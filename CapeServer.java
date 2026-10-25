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
 *   GET  /capes?uuids=<uuid>,...&names=<name>,...   -> {"<uuid>":"<loadout>", "<lowercase name>":"<loadout>", ...}
 *        (players wearing nothing are left out)
 *   POST /capes  {"uuid":"..","name":"..","serverId":"..","token":"..","cosmetic":"<id>.<id>..."}  -> 204, or 400/401
 *   POST /custom?uuid=..&name=..&serverId=..&token=..   body: cape texture PNG  -> 200 "<hash>", or 400/401/413
 *   GET  /custom/<hash>.png  (or HEAD)  -> the PNG, or 404
 *   GET  /markers?group=<64 hex>  -> [{"id":"..","dim":"..","x":..,"y":..,"z":..,"tx":..,"tz":..,"type":"..","owner":".."}, ...]
 *   POST /markers  {"uuid","name","serverId","token","group","action":"put|remove|clear",
 *                   "id","dim","x","y","z","tx","tz","type"}  -> 204, or 400/401/403  (tx/tz optional)
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
 *
 * Offline-mode ("cracked") servers give players offline UUIDs made from their name, so loadouts are also
 * stored by name, and clients look players up by name there. Players Mojang can't vouch for (cracked
 * launchers) can still upload, but only under their name: the first upload claims the name with the
 * client's secret token, and later uploads must bring the same token. Once a name's real (premium) owner
 * uploads with Mojang's check, the name is theirs and offline uploads for it are refused.
 *
 * Map markers: on Minecraft servers without the mod, players share world map markers with their scoreboard
 * team through here. A "group" is a hash the clients make from the server address and the team name, so this
 * server never learns either. Markers are kept in memory only, for MARKER_TTL_MS after their last upload; players
 * re-send theirs when they notice they are gone. Uploads are authenticated like capes, so the owner name shown to
 * the team is real, and only the owner can move or remove a marker.
 */
public class CapeServer {
    private static final Pattern UUID_PATTERN = Pattern.compile("^[0-9a-f]{32}$");
    // a loadout: up to 256 chars of cosmetic ids joined with '.' (one id per slot: back, head, body, legs, effect)
    private static final Pattern COSMETIC_PATTERN = Pattern.compile("^(?=.{0,256}$)([a-z0-9_]{1,64}([.][a-z0-9_]{1,64})*)?$");
    private static final Pattern NAME_PATTERN = Pattern.compile("^[A-Za-z0-9_]{1,16}$");
    private static final Pattern TOKEN_PATTERN = Pattern.compile("^[0-9a-f]{32,64}$");
    /** In NAME_TOKENS: the name's premium owner uploaded, so offline uploads can't use it. */
    private static final String PREMIUM = "premium";
    private static final int MAX_LOOKUP = 200;
    private static final Pattern IMAGE_PATH = Pattern.compile("^/custom/([0-9a-f]{16})\\.png$");
    // must match the mod (CustomCapes): textures up to 4 MB, 128/256/512 px wide, at most 128 frames
    private static final int MAX_IMAGE_BYTES = 4 << 20;
    private static final int MAX_FRAMES = 128;

    private static final Pattern GROUP_PATTERN = Pattern.compile("^[0-9a-f]{64}$");
    private static final Pattern DIM_PATTERN = Pattern.compile("^[a-z0-9_.-]{1,64}:[a-z0-9_./-]{1,63}$");
    private static final Pattern TYPE_PATTERN = Pattern.compile("^[a-z_]{1,16}$");
    private static final Pattern INT_PATTERN = Pattern.compile("^-?[0-9]{1,8}$");
    // must match the mod (MarkerServer): per team, and per player in a team
    private static final int MAX_MARKERS_PER_GROUP = 64;
    private static final int MAX_MARKERS_PER_OWNER = 16;
    private static final int MAX_GROUPS = 20_000;
    private static final long MARKER_TTL_MS = 12 * 60 * 60_000L;

    private static final Map<String, String> CAPES = new ConcurrentHashMap<>();
    /** group -> marker id -> marker, oldest first; guarded by itself */
    private static final Map<String, LinkedHashMap<String, StoredMarker>> MARKERS = new LinkedHashMap<>();

    /** (tx, tz): where an attack arrow points; the marker's own spot for other kinds */
    private record StoredMarker(String id, String dim, int x, int y, int z, int tx, int tz, String type, String owner, long time) {
        String toJson() {
            // every field was checked against a pattern, so nothing needs escaping
            return "{\"id\":\"" + id + "\",\"dim\":\"" + dim + "\",\"x\":" + x + ",\"y\":" + y + ",\"z\":" + z
                    + ",\"tx\":" + tx + ",\"tz\":" + tz + ",\"type\":\"" + type + "\",\"owner\":\"" + owner + "\"}";
        }
    }
    /** uuid (or lowercase name, for offline players) -> hash of that player's custom cape picture */
    private static final Map<String, String> OWNERS = new ConcurrentHashMap<>();
    /** lowercase name -> SHA-256 of the token that claimed it for offline uploads, or PREMIUM */
    private static final Map<String, String> NAME_TOKENS = new ConcurrentHashMap<>();
    private static final HttpClient HTTP = HttpClient.newBuilder().connectTimeout(Duration.ofSeconds(5)).build();
    private static Path dataFile;
    private static Path tokenFile;
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
        tokenFile = dataFile.resolveSibling("name-tokens.properties");
        load(dataFile, CAPES);
        load(tokenFile, NAME_TOKENS);
        Files.createDirectories(imageDir);
        loadOwners();

        HttpServer server = HttpServer.create(new InetSocketAddress(port), 0);
        server.createContext("/capes", CapeServer::handleCapes);
        server.createContext("/custom", CapeServer::handleCustom);
        server.createContext("/markers", CapeServer::handleMarkers);
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
        Map<String, String> query = parseQuery(ex.getRequestURI().getRawQuery());
        StringBuilder json = new StringBuilder("{");
        int count = 0;
        // uuids are 32 hex digits and names at most 16 characters, so the two kinds of keys never clash
        for (String raw : (query.getOrDefault("uuids", "") + "," + query.getOrDefault("names", "")).split(",")) {
            if (raw.isEmpty()) continue;
            if (++count > MAX_LOOKUP) break;
            String key = normalizeUuid(raw);
            if (key == null && NAME_PATTERN.matcher(raw).matches()) key = raw.toLowerCase();
            if (key == null) continue;
            String cape = CAPES.get(key);
            if (cape == null || cape.isEmpty()) continue;
            if (json.length() > 1) json.append(',');
            json.append('"').append(key).append("\":\"").append(cape).append('"');
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
        String token = json.getOrDefault("token", "");
        String cosmetic = json.getOrDefault("cosmetic", "");
        if (uuid == null || !NAME_PATTERN.matcher(name).matches() || !COSMETIC_PATTERN.matcher(cosmetic).matches()) {
            respond(ex, 400, "bad request", "text/plain");
            return;
        }
        Auth auth = authorize(name, serverId, uuid, token);
        if (auth == Auth.DENIED) {
            respond(ex, 401, "not authenticated", "text/plain");
            return;
        }
        // by name for offline-mode servers; by uuid only when Mojang confirmed it's really theirs
        String nameKey = name.toLowerCase();
        if (cosmetic.isEmpty()) CAPES.remove(nameKey);
        else CAPES.put(nameKey, cosmetic);
        if (auth == Auth.PREMIUM) {
            if (cosmetic.isEmpty()) CAPES.remove(uuid);
            else CAPES.put(uuid, cosmetic);
        }
        save();
        System.out.println(name + " (" + (auth == Auth.PREMIUM ? uuid : "offline") + ") -> " + (cosmetic.isEmpty() ? "no cape" : cosmetic));
        respond(ex, 204, "", "text/plain");
    }

    private static void handleMarkers(HttpExchange ex) throws IOException {
        try {
            switch (ex.getRequestMethod()) {
                case "GET" -> listMarkers(ex);
                case "POST" -> changeMarkers(ex);
                default -> respond(ex, 405, "method not allowed", "text/plain");
            }
        } catch (Exception e) {
            e.printStackTrace();
            respond(ex, 500, "error", "text/plain");
        }
    }

    private static void listMarkers(HttpExchange ex) throws IOException {
        String group = parseQuery(ex.getRequestURI().getRawQuery()).getOrDefault("group", "");
        if (!GROUP_PATTERN.matcher(group).matches()) {
            respond(ex, 400, "bad request", "text/plain");
            return;
        }
        StringBuilder json = new StringBuilder("[");
        synchronized (MARKERS) {
            expireMarkers();
            LinkedHashMap<String, StoredMarker> markers = MARKERS.get(group);
            if (markers != null)
                for (StoredMarker m : markers.values()) {
                    if (json.length() > 1) json.append(',');
                    json.append(m.toJson());
                }
        }
        respond(ex, 200, json.append(']').toString(), "application/json");
    }

    private static void changeMarkers(HttpExchange ex) throws IOException, InterruptedException {
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
            body = new String(in.readNBytes(length), StandardCharsets.UTF_8);
        }
        Map<String, String> json = parseFlatJson(body);
        String uuid = normalizeUuid(json.getOrDefault("uuid", ""));
        String name = json.getOrDefault("name", "");
        String group = json.getOrDefault("group", "");
        String action = json.getOrDefault("action", "");
        String id = json.getOrDefault("id", "");
        boolean idNeeded = !action.equals("clear");
        if (uuid == null || !NAME_PATTERN.matcher(name).matches() || !GROUP_PATTERN.matcher(group).matches()
                || idNeeded && !UUID_PATTERN.matcher(id).matches()
                || !action.equals("put") && !action.equals("remove") && !action.equals("clear")) {
            respond(ex, 400, "bad request", "text/plain");
            return;
        }
        StoredMarker marker = null;
        if (action.equals("put")) {
            String dim = json.getOrDefault("dim", ""), type = json.getOrDefault("type", "");
            String x = json.getOrDefault("x", ""), y = json.getOrDefault("y", ""), z = json.getOrDefault("z", "");
            // older mods send no target: the marker points at itself
            String tx = json.getOrDefault("tx", x), tz = json.getOrDefault("tz", z);
            if (!DIM_PATTERN.matcher(dim).matches() || !TYPE_PATTERN.matcher(type).matches()
                    || !INT_PATTERN.matcher(x).matches() || !INT_PATTERN.matcher(y).matches() || !INT_PATTERN.matcher(z).matches()
                    || !INT_PATTERN.matcher(tx).matches() || !INT_PATTERN.matcher(tz).matches()) {
                respond(ex, 400, "bad request", "text/plain");
                return;
            }
            marker = new StoredMarker(id, dim, Integer.parseInt(x), Integer.parseInt(y), Integer.parseInt(z),
                    Integer.parseInt(tx), Integer.parseInt(tz), type, name, System.currentTimeMillis());
        }
        if (authorize(name, json.getOrDefault("serverId", ""), uuid, json.getOrDefault("token", "")) == Auth.DENIED) {
            respond(ex, 401, "not authenticated", "text/plain");
            return;
        }
        synchronized (MARKERS) {
            expireMarkers();
            LinkedHashMap<String, StoredMarker> markers = MARKERS.get(group);
            if (markers == null) {
                if (marker == null) { // nothing to remove
                    respond(ex, 204, "", "text/plain");
                    return;
                }
                if (MARKERS.size() >= MAX_GROUPS) {
                    respond(ex, 503, "full", "text/plain");
                    return;
                }
                MARKERS.put(group, markers = new LinkedHashMap<>());
            }
            StoredMarker existing = idNeeded ? markers.get(id) : null;
            if (existing != null && !existing.owner().equalsIgnoreCase(name)) {
                respond(ex, 403, "not your marker", "text/plain");
                return;
            }
            switch (action) {
                case "clear" -> markers.values().removeIf(m -> m.owner().equalsIgnoreCase(name));
                case "remove" -> markers.remove(id);
                default -> {
                    markers.remove(id); // added again at the end: it is the newest now
                    trimMarkers(markers, name, MAX_MARKERS_PER_OWNER - 1);
                    trimMarkers(markers, null, MAX_MARKERS_PER_GROUP - 1);
                    markers.put(id, marker);
                }
            }
            if (markers.isEmpty()) MARKERS.remove(group);
        }
        respond(ex, 204, "", "text/plain");
    }

    /** Drops the oldest markers (of {@code owner}, or anyone's if null) until at most {@code keep} of them are left. */
    private static void trimMarkers(LinkedHashMap<String, StoredMarker> markers, String owner, int keep) {
        long count = markers.values().stream().filter(m -> owner == null || m.owner().equalsIgnoreCase(owner)).count();
        for (var it = markers.values().iterator(); count > keep && it.hasNext(); ) {
            StoredMarker m = it.next();
            if (owner == null || m.owner().equalsIgnoreCase(owner)) {
                it.remove();
                count--;
            }
        }
    }

    /** Forgets markers nobody re-sent for MARKER_TTL_MS. Call while holding MARKERS. */
    private static void expireMarkers() {
        long cutoff = System.currentTimeMillis() - MARKER_TTL_MS;
        MARKERS.values().removeIf(markers -> {
            markers.values().removeIf(m -> m.time() < cutoff);
            return markers.isEmpty();
        });
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
        Auth auth = authorize(name, serverId, uuid, query.getOrDefault("token", ""));
        if (auth == Auth.DENIED) {
            respond(ex, 401, "not authenticated", "text/plain");
            return;
        }
        String owner = auth == Auth.PREMIUM ? uuid : name.toLowerCase();
        String hash = sha256(png).substring(0, 16);
        Path file = imageDir.resolve(hash + ".png");
        if (!Files.exists(file)) {
            Path tmp = imageDir.resolve(hash + ".png.tmp");
            Files.write(tmp, png);
            Files.move(tmp, file, java.nio.file.StandardCopyOption.REPLACE_EXISTING, java.nio.file.StandardCopyOption.ATOMIC_MOVE);
        }
        synchronized (OWNERS) {
            String old = OWNERS.put(owner, hash);
            if (old != null && !old.equals(hash) && !OWNERS.containsValue(old))
                Files.deleteIfExists(imageDir.resolve(old + ".png"));
            saveOwners();
        }
        System.out.println(name + " (" + (auth == Auth.PREMIUM ? uuid : "offline") + ") -> custom cape picture " + hash + " (" + png.length / 1024 + " KB)");
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

    private enum Auth { PREMIUM, OFFLINE, DENIED }

    /**
     * PREMIUM: Mojang confirmed this is the account with this uuid (it then owns the name too).
     * OFFLINE: an unverified player who holds the name's token (or claims a free name with it); may only use the name.
     */
    private static Auth authorize(String name, String serverId, String uuid, String token) throws IOException, InterruptedException {
        if (!requireAuth) return Auth.PREMIUM;
        String nameKey = name.toLowerCase();
        if (verifyWithMojang(name, serverId, uuid)) {
            if (!PREMIUM.equals(NAME_TOKENS.put(nameKey, PREMIUM))) saveTokens();
            return Auth.PREMIUM;
        }
        if (!TOKEN_PATTERN.matcher(token).matches()) return Auth.DENIED;
        String tokenHash = sha256(token.getBytes(StandardCharsets.UTF_8));
        String claimed = NAME_TOKENS.putIfAbsent(nameKey, tokenHash);
        if (claimed == null) {
            saveTokens();
            System.out.println(name + " claimed their name for offline uploads");
            return Auth.OFFLINE;
        }
        return claimed.equals(tokenHash) ? Auth.OFFLINE : Auth.DENIED;
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

    private static void load(Path file, Map<String, String> into) throws IOException {
        if (!Files.exists(file)) return;
        Properties p = new Properties();
        try (InputStream in = Files.newInputStream(file)) {
            p.load(in);
        }
        p.forEach((k, v) -> into.put((String) k, (String) v));
    }

    private static synchronized void saveTokens() throws IOException {
        Properties p = new Properties();
        p.putAll(NAME_TOKENS);
        Path tmp = tokenFile.resolveSibling(tokenFile.getFileName() + ".tmp");
        try (OutputStream out = Files.newOutputStream(tmp)) {
            p.store(out, "lowercase name=sha256 of the token that may upload for it offline, or premium");
        }
        Files.move(tmp, tokenFile, java.nio.file.StandardCopyOption.REPLACE_EXISTING, java.nio.file.StandardCopyOption.ATOMIC_MOVE);
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
            p.store(out, "uuid or lowercase name=cosmetic");
        }
        Files.move(tmp, dataFile, java.nio.file.StandardCopyOption.REPLACE_EXISTING, java.nio.file.StandardCopyOption.ATOMIC_MOVE);
    }
}
