package org.bioontology.kobayashimarust.protege;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.AtomicMoveNotSupportedException;
import java.nio.file.FileAlreadyExistsException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardCopyOption;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.Locale;
import java.util.Properties;
import java.util.concurrent.ConcurrentHashMap;
import java.util.function.Function;

/**
 * Finds the native {@code km} executable that the plugin runs.
 *
 * <p>The plugin looks in this order:
 * <ol>
 *   <li>the Java system property {@code km.bin};</li>
 *   <li>the environment variable {@code KM_BIN};</li>
 *   <li>the executable bundled in the plugin jar for the running operating
 *       system and architecture, under {@code native/<os>-<arch>/km}
 *       ({@code km.exe} on Windows);</li>
 *   <li>{@code km} on {@code PATH}.</li>
 * </ol>
 *
 * <p>The jar lists the SHA-256 sum of every bundled executable in
 * {@code native/SHA256SUMS}, one {@code <sum>  <os>-<arch>/<name>} line per
 * platform. On first use the plugin unpacks the matching executable into a
 * per-user cache directory named after the plugin version and the sum. It
 * writes a temporary file, checks the sum, sets the executable bit and then
 * renames the file into place, so a half-written file is never run.
 */
public final class KMExecutable {

    /** Directory of the bundled executables inside the jar. */
    static final String NATIVE_ROOT = "native/";
    /** Manifest of SHA-256 sums inside the jar. */
    static final String MANIFEST = NATIVE_ROOT + "SHA256SUMS";
    /** Release platforms that a complete release jar bundles. */
    static final String[] RELEASE_PLATFORMS = {
        "linux-x86_64", "linux-aarch64", "macos-x86_64", "macos-aarch64", "windows-x86_64"
    };

    /** Reads a resource from the plugin jar; returns null when it is absent. */
    @FunctionalInterface
    interface Resources {
        InputStream open(String path) throws IOException;
    }

    /** Executables already unpacked and checked in this JVM, by cache path. */
    private static final ConcurrentHashMap<Path, Boolean> CHECKED = new ConcurrentHashMap<>();

    private final Function<String, String> properties;
    private final Function<String, String> environment;
    private final String osName;
    private final String osArch;
    private final Resources resources;
    private final Path cacheRoot;
    private final String pluginVersion;

    KMExecutable(
            Function<String, String> properties,
            Function<String, String> environment,
            String osName,
            String osArch,
            Resources resources,
            Path cacheRoot,
            String pluginVersion) {
        this.properties = properties;
        this.environment = environment;
        this.osName = osName;
        this.osArch = osArch;
        this.resources = resources;
        this.cacheRoot = cacheRoot;
        this.pluginVersion = pluginVersion;
    }

    /** Resolver for the running JVM, its environment and the plugin jar. */
    static KMExecutable forThisJvm() {
        Function<String, String> environment = System::getenv;
        String osName = System.getProperty("os.name", "");
        return new KMExecutable(
                System::getProperty,
                environment,
                osName,
                System.getProperty("os.arch", ""),
                path -> KMExecutable.class.getClassLoader().getResourceAsStream(path),
                defaultCacheRoot(osName, System::getProperty, environment),
                pluginVersion());
    }

    /**
     * Returns the absolute path or command name of the {@code km} executable
     * to run, unpacking the bundled one on first use.
     *
     * @throws IllegalStateException when no executable fits this platform
     */
    public static String resolve() {
        return forThisJvm().path();
    }

    /** Resolves the executable for this resolver's settings. */
    String path() {
        String configured = nonEmpty(properties.apply("km.bin"));
        if (configured != null) {
            return configured;
        }
        configured = nonEmpty(environment.apply("KM_BIN"));
        if (configured != null) {
            return configured;
        }
        String platform = platform(osName, osArch);
        String bundled = executableName(platform);
        String expected = bundledSum(bundled);
        if (expected != null) {
            return unpack(bundled, expected).toString();
        }
        String onPath = findOnPath(platform);
        if (onPath != null) {
            return onPath;
        }
        throw new IllegalStateException(
                "Kobayashi-MaRust has no bundled km executable for this platform ("
                + platform + ") and found none on PATH. Build or download km for "
                + platform + " and set the Java property -Dkm.bin=/absolute/path/to/"
                + (platform.startsWith("windows-") ? "km.exe" : "km")
                + " in the Protégé launcher configuration, or set the KM_BIN"
                + " environment variable.");
    }

    /** Names the platform as {@code <os>-<arch>}, for example {@code macos-aarch64}. */
    static String platform(String osName, String osArch) {
        String os = osName.toLowerCase(Locale.ROOT);
        if (os.startsWith("linux")) {
            os = "linux";
        } else if (os.startsWith("mac") || os.startsWith("darwin")) {
            os = "macos";
        } else if (os.startsWith("windows")) {
            os = "windows";
        } else {
            os = os.replaceAll("[^a-z0-9]+", "");
        }
        String arch = osArch.toLowerCase(Locale.ROOT);
        if (arch.equals("amd64") || arch.equals("x86_64") || arch.equals("x86-64")
                || arch.equals("x64")) {
            arch = "x86_64";
        } else if (arch.equals("aarch64") || arch.equals("arm64")) {
            arch = "aarch64";
        } else {
            arch = arch.replaceAll("[^a-z0-9_]+", "");
        }
        return os + "-" + arch;
    }

    /** Jar-relative path of the executable for a platform, below {@code native/}. */
    static String executableName(String platform) {
        return platform + "/" + (platform.startsWith("windows-") ? "km.exe" : "km");
    }

    /** Per-user cache root for unpacked executables. */
    static Path defaultCacheRoot(
            String osName,
            Function<String, String> properties,
            Function<String, String> environment) {
        String home = properties.apply("user.home");
        String os = platform(osName, "").replaceAll("-$", "");
        Path base;
        if (os.equals("windows")) {
            String local = nonEmpty(environment.apply("LOCALAPPDATA"));
            base = local != null
                    ? Paths.get(local)
                    : Paths.get(home, "AppData", "Local");
        } else if (os.equals("macos")) {
            base = Paths.get(home, "Library", "Caches");
        } else {
            String xdg = nonEmpty(environment.apply("XDG_CACHE_HOME"));
            base = xdg != null ? Paths.get(xdg) : Paths.get(home, ".cache");
        }
        return base.resolve("kobayashi-marust").resolve("protege");
    }

    /** The plugin version recorded at build time, or "dev" in an IDE build. */
    static String pluginVersion() {
        try (InputStream in = KMExecutable.class.getResourceAsStream("km-plugin.properties")) {
            if (in != null) {
                Properties properties = new Properties();
                properties.load(in);
                String version = nonEmpty(properties.getProperty("version"));
                if (version != null && !version.startsWith("${")) {
                    return version;
                }
            }
        } catch (IOException ignored) {
            // Fall through to the development version.
        }
        return "dev";
    }

    private String bundledSum(String name) {
        String manifest;
        try (InputStream in = resources.open(MANIFEST)) {
            if (in == null) {
                return null;
            }
            manifest = new String(in.readAllBytes(), StandardCharsets.UTF_8);
        } catch (IOException error) {
            throw new IllegalStateException(
                    "Kobayashi-MaRust cannot read the bundled " + MANIFEST, error);
        }
        for (String line : manifest.split("\\R")) {
            String[] fields = line.trim().split("\\s+");
            if (fields.length == 2) {
                String file = fields[1].startsWith("*") ? fields[1].substring(1) : fields[1];
                if (file.equals(name)) {
                    String sum = fields[0].toLowerCase(Locale.ROOT);
                    if (!sum.matches("[0-9a-f]{64}")) {
                        throw new IllegalStateException(
                                "Kobayashi-MaRust " + MANIFEST + " has a malformed sum for "
                                + name);
                    }
                    return sum;
                }
            }
        }
        return null;
    }

    private Path unpack(String name, String expected) {
        String file = name.substring(name.indexOf('/') + 1);
        Path directory = cacheRoot
                .resolve(pluginVersion + "-" + expected.substring(0, 16))
                .resolve(name.substring(0, name.indexOf('/')));
        Path target = directory.resolve(file);
        if (CHECKED.containsKey(target) && Files.isRegularFile(target)) {
            return target;
        }
        try {
            if (Files.isRegularFile(target)) {
                if (expected.equals(sha256(target))) {
                    makeExecutable(target);
                    CHECKED.put(target, Boolean.TRUE);
                    return target;
                }
                // A corrupt or truncated cache entry: replace it below.
                Files.delete(target);
            }
            Files.createDirectories(directory);
            Path temporary = Files.createTempFile(directory, file + ".", ".part");
            try {
                try (InputStream in = resources.open(NATIVE_ROOT + name)) {
                    if (in == null) {
                        throw new IllegalStateException(
                                "Kobayashi-MaRust lists " + name + " in " + MANIFEST
                                + " but the jar does not contain it");
                    }
                    try (OutputStream out = Files.newOutputStream(temporary)) {
                        in.transferTo(out);
                    }
                }
                String actual = sha256(temporary);
                if (!expected.equals(actual)) {
                    throw new IllegalStateException(
                            "Kobayashi-MaRust bundled executable " + name
                            + " failed its SHA-256 check (expected " + expected
                            + ", found " + actual + "). Reinstall the plugin, or set"
                            + " -Dkm.bin to a km executable.");
                }
                makeExecutable(temporary);
                try {
                    Files.move(temporary, target, StandardCopyOption.ATOMIC_MOVE);
                } catch (AtomicMoveNotSupportedException error) {
                    Files.move(temporary, target);
                } catch (FileAlreadyExistsException error) {
                    // Another Protégé process unpacked the same file first.
                    if (!expected.equals(sha256(target))) {
                        throw error;
                    }
                }
            } finally {
                Files.deleteIfExists(temporary);
            }
            CHECKED.put(target, Boolean.TRUE);
            return target;
        } catch (IOException error) {
            throw new IllegalStateException(
                    "Kobayashi-MaRust could not unpack its bundled km executable to "
                    + directory + ": " + error.getMessage()
                    + ". Set -Dkm.bin to a km executable instead.", error);
        }
    }

    private String findOnPath(String platform) {
        String path = nonEmpty(environment.apply("PATH"));
        if (path == null) {
            return null;
        }
        String name = platform.startsWith("windows-") ? "km.exe" : "km";
        for (String entry : path.split(File.pathSeparator)) {
            if (entry.isEmpty()) {
                continue;
            }
            Path candidate = Paths.get(entry, name);
            if (Files.isRegularFile(candidate) && Files.isExecutable(candidate)) {
                return candidate.toAbsolutePath().toString();
            }
        }
        return null;
    }

    private static void makeExecutable(Path file) throws IOException {
        File handle = file.toFile();
        if (!handle.canExecute() && !handle.setExecutable(true, false)) {
            throw new IOException("cannot set the executable bit on " + file);
        }
    }

    static String sha256(Path file) throws IOException {
        MessageDigest digest;
        try {
            digest = MessageDigest.getInstance("SHA-256");
        } catch (NoSuchAlgorithmException error) {
            throw new IllegalStateException(error);
        }
        byte[] buffer = new byte[1 << 16];
        try (InputStream in = Files.newInputStream(file)) {
            int read;
            while ((read = in.read(buffer)) > 0) {
                digest.update(buffer, 0, read);
            }
        }
        StringBuilder hex = new StringBuilder(64);
        for (byte b : digest.digest()) {
            hex.append(String.format("%02x", b));
        }
        return hex.toString();
    }

    private static String nonEmpty(String value) {
        return value == null || value.isEmpty() ? null : value;
    }
}
