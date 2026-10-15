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
 * Cape server for the cosmetics mod: remembers which cosmetics every player wears so that all
 * clients with the mod can see each other's capes, hats, wings and effects on any Minecraft server.
 *
 * Run:  java CapeServer.java [--port 8765] [--data capes.properties] [--images custom-capes] [--no-auth]
 *       (or set the PORT / CAPE_DATA / CAPE_IMAGES environment variables, as cloud hosts do)
 *
 * API
 *   GET  /capes?uuids=<uuid>,<uuid>,...   -> {"<uuid>":"<loadout>", ...}   (players wearing nothing are left out)
 *   POST /capes  {"uuid":"..","name":"..","serverId":"..","cosmetic":"<id>.<id>..."}  -> 204, or 400/401
 *   POST /custom?uuid=..&name=..&serverId=..   body: cape texture PNG  -> 200 "<hash>", or 400/401/413
 *   GET  /custom/<hash>.png  (or HEAD)  -> the PNG, or 404
 *   GET  /health -> ok
 *
 * Custom capes are pictures players made into capes. They are stored by the first 16 hex digits of
 * their SHA-256, which is also in the cape's id ("custom_<hash>_<frames>"), so clients can check that
 * what they download is what the player wears. Each player keeps one picture here; uploading a new one
 * deletes their old one (unless someone else uses it too).
 *
 * Authentication: before uploading, the client calls Mojang's joinServer with a random serverId
 * (exactly like joining a Minecraft server). This server then asks Mojang's hasJoined endpoint who
 * that was, so a player can only ever change their own cape. --no-auth skips this for local testing
 * with offline/dev accounts; never use it on a public server.
 */
public class CapeServer {
    private static final Pattern UUID_PATTERN = Pattern.compile("^[0-9a-f]{32}$");
    // a loadout: up to 256 chars of cosmetic ids joined with '.' (one id per slot: back, head, body, legs, effect)
    private static final Pattern COSMETIC_PATTERN = Pattern.compile("^(?=.{0,256}$)([a-z0-9_]{1,64}([.][a-z0-9_]{1,64})*)?$");
    private static final Pattern NAME_PATTERN = Pattern.compile("^[A-Za-z0-9_]{1,16}$");
    private static final int MAX_LOOKUP = 200;
    private static final Pattern IMAGE_PATH = Pattern.compile("^/custom/([0-9a-f]{16})\\.png$");
    // must match the mod (CustomCapes): textures up to 4 MB, 128/256/512 px wide, at most 128 frames
    private static final int MAX_IMAGE_BYTES = 4 << 20;
    private static final int MAX_FRAMES = 128;

    private static final Map<String, String> CAPES = new ConcurrentHashMap<>();
    /** uuid -> hash of that player's custom cape picture */
    private static final Map<String, String> OWNERS = new ConcurrentHashMap<>();
    private static final HttpClient HTTP = HttpClient.newBuilder().connectTimeout(Duration.ofSeconds(5)).build();
    private static Path dataFile;
    private static Path imageDir;
    private static boolean requireAuth = true;

    public static void main(String[] args) throws IOException {
        // cloud hosts tell the app which port to use via $PORT
        int port = System.getenv("PORT") != null ? Integer.parseInt(System.getenv("PORT")) : 8765;
        dataFile = Path.of(System.getenv().getOrDefault("CAPE_DATA", "capes.properties"));
        imageDir = Path.of(System.getenv().getOrDefault("CAPE_IMAGES", "custom-capes"));
        for (int i = 0; i < args.length; i++) {
            switch (args[i]) {
                case "--port" -> port = Integer.parseInt(args[++i]);
                case "--data" -> dataFile = Path.of(args[++i]);
                case "--images" -> imageDir = Path.of(args[++i]);
                case "--no-auth" -> requireAuth = false;
                default -> throw new IllegalArgumentException("Unknown argument " + args[i]);
            }
        }
        load();
        Files.createDirectories(imageDir);
        loadOwners();

        HttpServer server = HttpServer.create(new InetSocketAddress(port), 0);
        server.createContext("/capes", CapeServer::handleCapes);
        server.createContext("/custom", CapeServer::handleCustom);
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

    private static void handleCustom(HttpExchange ex) throws IOException {
        try {
            String method = ex.getRequestMethod();
            if (method.equals("GET") || method.equals("HEAD")) serveImage(ex, method.equals("HEAD"));
            else if (method.equals("POST") && ex.getRequestURI().getPath().equals("/custom")) uploadImage(ex);
            else respond(ex, 405, "method not allowed", "text/plain");
        } catch (Exception e) {
            e.printStackTrace();
            respond(ex, 500, "error", "text/plain");
        }
    }

    private static void serveImage(HttpExchange ex, boolean headOnly) throws IOException {
        Matcher m = IMAGE_PATH.matcher(ex.getRequestURI().getPath());
        Path file = m.matches() ? imageDir.resolve(m.group(1) + ".png") : null;
        if (file == null || !Files.isRegularFile(file)) {
            respond(ex, 404, "not found", "text/plain");
            return;
        }
        byte[] png = Files.readAllBytes(file);
        ex.getResponseHeaders().set("Content-Type", "image/png");
        ex.getResponseHeaders().set("X-Content-Type-Options", "nosniff");
        // a hash never names a different picture, so it can be cached forever
        ex.getResponseHeaders().set("Cache-Control", "public, max-age=31536000, immutable");
        if (headOnly) {
            ex.sendResponseHeaders(200, -1);
        } else {
            ex.sendResponseHeaders(200, png.length);
            try (OutputStream out = ex.getResponseBody()) {
                out.write(png);
            }
        }
        ex.close();
    }

    private static void uploadImage(HttpExchange ex) throws IOException, InterruptedException {
        Map<String, String> query = parseQuery(ex.getRequestURI().getRawQuery());
        String uuid = normalizeUuid(query.getOrDefault("uuid", ""));
        String name = query.getOrDefault("name", "");
        String serverId = query.getOrDefault("serverId", "");
        if (uuid == null || !NAME_PATTERN.matcher(name).matches()) {
            respond(ex, 400, "bad request", "text/plain");
            return;
        }
        String lengthHeader = ex.getRequestHeaders().getFirst("Content-Length");
        long length;
        try {
            length = lengthHeader == null ? -1 : Long.parseLong(lengthHeader.trim());
        } catch (NumberFormatException e) {
            length = -1;
        }
        if (length < 0 || length > MAX_IMAGE_BYTES) {
            respond(ex, length > MAX_IMAGE_BYTES ? 413 : 400, "bad request", "text/plain");
            return;
        }
        byte[] png;
        try (InputStream in = ex.getRequestBody()) {
            png = in.readNBytes((int) length);
        }
        if (png.length != length || !isCapeTexture(png)) {
            respond(ex, 400, "not a cape texture", "text/plain");
            return;
        }
        if (requireAuth && !verifyWithMojang(name, serverId, uuid)) {
            respond(ex, 401, "not authenticated", "text/plain");
            return;
        }
        String hash = sha256(png).substring(0, 16);
        Path file = imageDir.resolve(hash + ".png");
        if (!Files.exists(file)) {
            Path tmp = imageDir.resolve(hash + ".png.tmp");
            Files.write(tmp, png);
            Files.move(tmp, file, java.nio.file.StandardCopyOption.REPLACE_EXISTING, java.nio.file.StandardCopyOption.ATOMIC_MOVE);
        }
        synchronized (OWNERS) {
            String old = OWNERS.put(uuid, hash);
            if (old != null && !old.equals(hash) && !OWNERS.containsValue(old))
                Files.deleteIfExists(imageDir.resolve(old + ".png"));
            saveOwners();
        }
        System.out.println(name + " (" + uuid + ") -> custom cape picture " + hash + " (" + png.length / 1024 + " KB)");
        respond(ex, 200, hash, "text/plain");
    }

    /** Checks the PNG header: a cape texture is 128, 256 or 512 px wide with up to 128 frames of width/2 px stacked. */
    private static boolean isCapeTexture(byte[] png) {
        byte[] signature = {(byte) 0x89, 'P', 'N', 'G', '\r', '\n', 0x1A, '\n'};
        if (png.length < 24 || !java.util.Arrays.equals(png, 0, 8, signature, 0, 8)
                || !new String(png, 12, 4, StandardCharsets.US_ASCII).equals("IHDR"))
            return false;
        java.nio.ByteBuffer header = java.nio.ByteBuffer.wrap(png, 16, 8);
        int width = header.getInt(), height = header.getInt();
        if (width != 128 && width != 256 && width != 512) return false;
        int frameHeight = width / 2;
        return height > 0 && height % frameHeight == 0 && height / frameHeight <= MAX_FRAMES;
    }

    private static String sha256(byte[] data) {
        try {
            return java.util.HexFormat.of().formatHex(java.security.MessageDigest.getInstance("SHA-256").digest(data));
        } catch (java.security.NoSuchAlgorithmException e) {
            throw new IllegalStateException(e);
        }
    }

    private static Map<String, String> parseQuery(String query) {
        Map<String, String> map = new LinkedHashMap<>();
        if (query != null)
            for (String part : query.split("&")) {
                int eq = part.indexOf('=');
                if (eq > 0)
                    map.putIfAbsent(part.substring(0, eq), java.net.URLDecoder.decode(part.substring(eq + 1), StandardCharsets.UTF_8));
            }
        return map;
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

    private static void loadOwners() throws IOException {
        Path file = imageDir.resolve("owners.properties");
        if (!Files.exists(file)) return;
        Properties p = new Properties();
        try (InputStream in = Files.newInputStream(file)) {
            p.load(in);
        }
        p.forEach((k, v) -> OWNERS.put((String) k, (String) v));
    }

    private static void saveOwners() throws IOException {
        Properties p = new Properties();
        p.putAll(OWNERS);
        Path file = imageDir.resolve("owners.properties");
        Path tmp = imageDir.resolve("owners.properties.tmp");
        try (OutputStream out = Files.newOutputStream(tmp)) {
            p.store(out, "uuid=hash of their custom cape picture");
        }
        Files.move(tmp, file, java.nio.file.StandardCopyOption.REPLACE_EXISTING, java.nio.file.StandardCopyOption.ATOMIC_MOVE);
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
