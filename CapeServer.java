import com.sun.net.httpserver.HttpExchange;
import com.sun.net.httpserver.HttpServer;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.InetSocketAddress;
import java.net.URI;
import java.net.URLEncoder;
import java.net.http.HttpClient;
import java.net.http.HttpRequest;
import java.net.http.HttpResponse;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.time.Duration;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Properties;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.Executors;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Cape server for the cosmetics mod: remembers which cape every player wears so that all
 * clients with the mod can see each other's capes on any Minecraft server.
 *
 * Run:  java CapeServer.java [--port 8765] [--data capes.properties] [--no-auth]
 *       (or set the PORT / CAPE_DATA environment variables, as cloud hosts do)
 *
 * API
 *   GET  /capes?uuids=<uuid>,<uuid>,...   -> {"<uuid>":"<cosmeticId>", ...}   (players without a cape are left out)
 *   POST /capes  {"uuid":"..","name":"..","serverId":"..","cosmetic":".."}  -> 204, or 400/401
 *   GET  /health -> ok
 *
 * Authentication: before uploading, the client calls Mojang's joinServer with a random serverId
 * (exactly like joining a Minecraft server). This server then asks Mojang's hasJoined endpoint who
 * that was, so a player can only ever change their own cape. --no-auth skips this for local testing
 * with offline/dev accounts; never use it on a public server.
 */
public class CapeServer {
    private static final Pattern UUID_PATTERN = Pattern.compile("^[0-9a-f]{32}$");
    private static final Pattern COSMETIC_PATTERN = Pattern.compile("^[a-z0-9_]{0,64}$");
    private static final Pattern NAME_PATTERN = Pattern.compile("^[A-Za-z0-9_]{1,16}$");
    private static final int MAX_LOOKUP = 200;

    private static final Map<String, String> CAPES = new ConcurrentHashMap<>();
    private static final HttpClient HTTP = HttpClient.newBuilder().connectTimeout(Duration.ofSeconds(5)).build();
    private static Path dataFile;
    private static boolean requireAuth = true;

    public static void main(String[] args) throws IOException {
        // cloud hosts tell the app which port to use via $PORT
        int port = System.getenv("PORT") != null ? Integer.parseInt(System.getenv("PORT")) : 8765;
        dataFile = Path.of(System.getenv().getOrDefault("CAPE_DATA", "capes.properties"));
        for (int i = 0; i < args.length; i++) {
            switch (args[i]) {
                case "--port" -> port = Integer.parseInt(args[++i]);
                case "--data" -> dataFile = Path.of(args[++i]);
                case "--no-auth" -> requireAuth = false;
                default -> throw new IllegalArgumentException("Unknown argument " + args[i]);
            }
        }
        load();

        HttpServer server = HttpServer.create(new InetSocketAddress(port), 0);
        server.createContext("/capes", CapeServer::handleCapes);
        server.createContext("/health", ex -> respond(ex, 200, "ok", "text/plain"));
        server.setExecutor(Executors.newFixedThreadPool(8));
        server.start();
        System.out.println("Cape server listening on port " + port + " (" + CAPES.size() + " capes stored, auth "
                + (requireAuth ? "ON" : "OFF - testing only!") + ")");
    }

    private static void handleCapes(HttpExchange ex) throws IOException {
        try {
            switch (ex.getRequestMethod()) {
                case "GET" -> lookup(ex);
                case "POST" -> upload(ex);
                default -> respond(ex, 405, "method not allowed", "text/plain");
            }
        } catch (Exception e) {
            e.printStackTrace();
            respond(ex, 500, "error", "text/plain");
        }
    }

    private static void lookup(HttpExchange ex) throws IOException {
        String query = ex.getRequestURI().getRawQuery();
        String list = "";
        if (query != null)
            for (String part : query.split("&"))
                if (part.startsWith("uuids=")) list = part.substring(6);
        StringBuilder json = new StringBuilder("{");
        int count = 0;
        for (String raw : list.split(",")) {
            if (++count > MAX_LOOKUP) break;
            String uuid = normalizeUuid(raw);
            if (uuid == null) continue;
            String cape = CAPES.get(uuid);
            if (cape == null || cape.isEmpty()) continue;
            if (json.length() > 1) json.append(',');
            json.append('"').append(uuid).append("\":\"").append(cape).append('"');
        }
        respond(ex, 200, json.append('}').toString(), "application/json");
    }

    private static void upload(HttpExchange ex) throws IOException, InterruptedException {
        String lengthHeader = ex.getRequestHeaders().getFirst("Content-Length");
        int length;
        try {
            length = lengthHeader == null ? -1 : Integer.parseInt(lengthHeader.trim());
        } catch (NumberFormatException e) {
            length = -1;
        }
        if (length < 0 || length > 2048) {
            respond(ex, 400, "bad request", "text/plain");
            return;
        }
        String body;
        try (InputStream in = ex.getRequestBody()) {
            body = new String(in.readNBytes(length), StandardCharsets.UTF_8); // exactly the body, never waits for the connection to close
        }
        Map<String, String> json = parseFlatJson(body);
        String uuid = normalizeUuid(json.getOrDefault("uuid", ""));
        String name = json.getOrDefault("name", "");
        String serverId = json.getOrDefault("serverId", "");
        String cosmetic = json.getOrDefault("cosmetic", "");
        if (uuid == null || !NAME_PATTERN.matcher(name).matches() || !COSMETIC_PATTERN.matcher(cosmetic).matches()) {
            respond(ex, 400, "bad request", "text/plain");
            return;
        }
        if (requireAuth && !verifyWithMojang(name, serverId, uuid)) {
            respond(ex, 401, "not authenticated", "text/plain");
            return;
        }
        if (cosmetic.isEmpty()) CAPES.remove(uuid);
        else CAPES.put(uuid, cosmetic);
        save();
        System.out.println(name + " (" + uuid + ") -> " + (cosmetic.isEmpty() ? "no cape" : cosmetic));
        respond(ex, 204, "", "text/plain");
    }

    /** Asks Mojang whether this player really just called joinServer with this serverId. */
    private static boolean verifyWithMojang(String name, String serverId, String uuid) throws IOException, InterruptedException {
        if (serverId.isEmpty() || serverId.length() > 64) return false;
        URI uri = URI.create("https://sessionserver.mojang.com/session/minecraft/hasJoined?username="
                + URLEncoder.encode(name, StandardCharsets.UTF_8) + "&serverId=" + URLEncoder.encode(serverId, StandardCharsets.UTF_8));
        HttpResponse<String> res = HTTP.send(HttpRequest.newBuilder(uri).timeout(Duration.ofSeconds(10)).GET().build(),
                HttpResponse.BodyHandlers.ofString());
        if (res.statusCode() != 200) return false;
        String id = parseFlatJson(res.body()).get("id");
        return uuid.equals(normalizeUuid(id == null ? "" : id));
    }

    // ---------------------------------------------------------------------------------------

    private static String normalizeUuid(String s) {
        String u = s.trim().replace("-", "").toLowerCase();
        return UUID_PATTERN.matcher(u).matches() ? u : null;
    }

    /** Minimal parser for flat JSON objects with string values (all this API needs). */
    private static Map<String, String> parseFlatJson(String s) {
        Map<String, String> map = new LinkedHashMap<>();
        Matcher m = Pattern.compile("\"([A-Za-z0-9_]+)\"\\s*:\\s*\"((?:[^\"\\\\]|\\\\.)*)\"").matcher(s);
        while (m.find()) map.putIfAbsent(m.group(1), m.group(2));
        return map;
    }

    private static void respond(HttpExchange ex, int status, String body, String type) throws IOException {
        byte[] bytes = body.getBytes(StandardCharsets.UTF_8);
        ex.getResponseHeaders().set("Content-Type", type + "; charset=utf-8");
        ex.sendResponseHeaders(status, status == 204 ? -1 : bytes.length);
        if (status != 204) try (OutputStream out = ex.getResponseBody()) {
            out.write(bytes);
        }
        ex.close();
    }

    private static void load() throws IOException {
        if (!Files.exists(dataFile)) return;
        Properties p = new Properties();
        try (InputStream in = Files.newInputStream(dataFile)) {
            p.load(in);
        }
        p.forEach((k, v) -> CAPES.put((String) k, (String) v));
    }

    private static synchronized void save() throws IOException {
        Properties p = new Properties();
        p.putAll(CAPES);
        Path tmp = dataFile.resolveSibling(dataFile.getFileName() + ".tmp");
        try (OutputStream out = Files.newOutputStream(tmp)) {
            p.store(out, "uuid=cosmetic");
        }
        Files.move(tmp, dataFile, java.nio.file.StandardCopyOption.REPLACE_EXISTING, java.nio.file.StandardCopyOption.ATOMIC_MOVE);
    }
}
