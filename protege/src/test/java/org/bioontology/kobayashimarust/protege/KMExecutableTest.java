package org.bioontology.kobayashimarust.protege;

import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.ByteArrayInputStream;
import java.io.File;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.security.MessageDigest;
import java.util.HashMap;
import java.util.Map;
import java.util.concurrent.atomic.AtomicInteger;

import static org.junit.Assert.*;

/** Resolution order, unpacking, checksum and platform naming of the km executable. */
public class KMExecutableTest {

    @Rule
    public TemporaryFolder folder = new TemporaryFolder();

    private static final byte[] PAYLOAD = "#!/bin/sh\necho km\n".getBytes(StandardCharsets.UTF_8);

    private final Map<String, String> properties = new HashMap<>();
    private final Map<String, String> environment = new HashMap<>();
    private final Map<String, byte[]> jar = new HashMap<>();
    private final AtomicInteger opens = new AtomicInteger();

    private KMExecutable resolver(String os, String arch, Path cache) {
        return new KMExecutable(
                properties::get,
                environment::get,
                os,
                arch,
                path -> {
                    byte[] bytes = jar.get(path);
                    if (bytes == null) {
                        return null;
                    }
                    if (path.startsWith("native/") && !path.equals(KMExecutable.MANIFEST)) {
                        opens.incrementAndGet();
                    }
                    return new ByteArrayInputStream(bytes);
                },
                cache,
                "9.9.9-test");
    }

    private void bundle(String name, byte[] bytes, String listedSum) {
        jar.put("native/" + name, bytes);
        String manifest = new String(
                jar.getOrDefault(KMExecutable.MANIFEST, new byte[0]), StandardCharsets.UTF_8);
        manifest += listedSum + "  " + name + "\n";
        jar.put(KMExecutable.MANIFEST, manifest.getBytes(StandardCharsets.UTF_8));
    }

    private static String sha256(byte[] bytes) throws Exception {
        StringBuilder hex = new StringBuilder();
        for (byte b : MessageDigest.getInstance("SHA-256").digest(bytes)) {
            hex.append(String.format("%02x", b));
        }
        return hex.toString();
    }

    private Path pathDirWithKm(String name) throws Exception {
        File dir = folder.newFolder();
        Path km = dir.toPath().resolve(name);
        Files.write(km, PAYLOAD);
        assertTrue(km.toFile().setExecutable(true));
        environment.put("PATH", dir.getAbsolutePath());
        return km;
    }

    @Test
    public void platformNamesCoverTheReleaseTargets() {
        assertEquals("linux-x86_64", KMExecutable.platform("Linux", "amd64"));
        assertEquals("linux-aarch64", KMExecutable.platform("Linux", "aarch64"));
        assertEquals("macos-x86_64", KMExecutable.platform("Mac OS X", "x86_64"));
        assertEquals("macos-aarch64", KMExecutable.platform("Mac OS X", "aarch64"));
        assertEquals("windows-x86_64", KMExecutable.platform("Windows 11", "amd64"));
        assertEquals("freebsd-x86_64", KMExecutable.platform("FreeBSD", "amd64"));
        assertEquals("linux-ppc64le", KMExecutable.platform("Linux", "ppc64le"));
        assertEquals("windows-x86_64/km.exe", KMExecutable.executableName("windows-x86_64"));
        assertEquals("macos-aarch64/km", KMExecutable.executableName("macos-aarch64"));
    }

    @Test
    public void cacheRootFollowsEachPlatformConvention() {
        Map<String, String> props = new HashMap<>();
        props.put("user.home", "/home/u");
        Map<String, String> env = new HashMap<>();
        assertEquals("/home/u/.cache/kobayashi-marust/protege",
                KMExecutable.defaultCacheRoot("Linux", props::get, env::get).toString());
        env.put("XDG_CACHE_HOME", "/xdg");
        assertEquals("/xdg/kobayashi-marust/protege",
                KMExecutable.defaultCacheRoot("Linux", props::get, env::get).toString());
        assertEquals("/home/u/Library/Caches/kobayashi-marust/protege",
                KMExecutable.defaultCacheRoot("Mac OS X", props::get, env::get).toString());
        env.put("LOCALAPPDATA", "/appdata");
        assertEquals("/appdata/kobayashi-marust/protege",
                KMExecutable.defaultCacheRoot("Windows 10", props::get, env::get).toString());
    }

    @Test
    public void resolutionOrderIsPropertyEnvironmentBundledThenPath() throws Exception {
        Path cache = folder.newFolder("cache").toPath();
        Path onPath = pathDirWithKm("km");
        bundle("linux-x86_64/km", PAYLOAD, sha256(PAYLOAD));
        properties.put("km.bin", "/from/property");
        environment.put("KM_BIN", "/from/environment");

        assertEquals("/from/property", resolver("Linux", "amd64", cache).path());

        properties.remove("km.bin");
        assertEquals("/from/environment", resolver("Linux", "amd64", cache).path());

        environment.remove("KM_BIN");
        String bundled = resolver("Linux", "amd64", cache).path();
        assertTrue(bundled, bundled.startsWith(cache.toString()));
        assertTrue(bundled, bundled.endsWith("/linux-x86_64/km"));

        // No bundled executable for this platform: fall back to PATH.
        assertEquals(onPath.toAbsolutePath().toString(),
                resolver("Linux", "aarch64", cache).path());
    }

    @Test
    public void emptySettingsAreIgnored() throws Exception {
        Path onPath = pathDirWithKm("km");
        properties.put("km.bin", "");
        environment.put("KM_BIN", "");
        assertEquals(onPath.toAbsolutePath().toString(),
                resolver("Linux", "amd64", folder.newFolder().toPath()).path());
    }

    @Test
    public void bundledExecutableIsUnpackedOnceCheckedAndExecutable() throws Exception {
        Path cache = folder.newFolder("cache").toPath();
        String sum = sha256(PAYLOAD);
        bundle("linux-x86_64/km", PAYLOAD, sum);

        Path first = Path.of(resolver("Linux", "amd64", cache).path());
        assertArrayEquals(PAYLOAD, Files.readAllBytes(first));
        assertTrue(Files.isExecutable(first));
        assertEquals(cache.resolve("9.9.9-test-" + sum.substring(0, 16))
                .resolve("linux-x86_64").resolve("km"), first);
        try (var listing = Files.list(first.getParent())) {
            assertEquals("no temporary file is left behind", 1, listing.count());
        }

        Path second = Path.of(resolver("Linux", "amd64", cache).path());
        assertEquals(first, second);
        assertEquals("the second resolution reuses the cache", 1, opens.get());
    }

    @Test
    public void corruptCacheEntryIsReplaced() throws Exception {
        Path cache = folder.newFolder("cache").toPath();
        String sum = sha256(PAYLOAD);
        bundle("linux-x86_64/km", PAYLOAD, sum);
        Path target = cache.resolve("9.9.9-test-" + sum.substring(0, 16))
                .resolve("linux-x86_64").resolve("km");
        Files.createDirectories(target.getParent());
        Files.write(target, "truncated".getBytes(StandardCharsets.UTF_8));

        assertEquals(target.toString(), resolver("Linux", "amd64", cache).path());
        assertArrayEquals(PAYLOAD, Files.readAllBytes(target));
    }

    @Test
    public void checksumMismatchFailsAndLeavesNoExecutable() throws Exception {
        Path cache = folder.newFolder("cache").toPath();
        String wrong = sha256("something else".getBytes(StandardCharsets.UTF_8));
        bundle("windows-x86_64/km.exe", PAYLOAD, wrong);
        try {
            resolver("Windows 11", "amd64", cache).path();
            fail("a checksum mismatch must not resolve");
        } catch (IllegalStateException error) {
            assertTrue(error.getMessage(), error.getMessage().contains("SHA-256"));
            assertTrue(error.getMessage(), error.getMessage().contains("windows-x86_64/km.exe"));
        }
        Path directory = cache.resolve("9.9.9-test-" + wrong.substring(0, 16))
                .resolve("windows-x86_64");
        try (var listing = Files.list(directory)) {
            assertEquals("neither the executable nor a temporary file remains",
                    0, listing.count());
        }
    }

    @Test
    public void listedButMissingExecutableFails() throws Exception {
        jar.put(KMExecutable.MANIFEST,
                (sha256(PAYLOAD) + "  macos-aarch64/km\n").getBytes(StandardCharsets.UTF_8));
        try {
            resolver("Mac OS X", "aarch64", folder.newFolder().toPath()).path();
            fail("a listed but missing executable must not resolve");
        } catch (IllegalStateException error) {
            assertTrue(error.getMessage(), error.getMessage().contains("does not contain"));
        }
    }

    @Test
    public void unsupportedPlatformNamesItselfAndKmBin() throws Exception {
        bundle("linux-x86_64/km", PAYLOAD, sha256(PAYLOAD));
        environment.put("PATH", folder.newFolder("empty").getAbsolutePath());
        try {
            resolver("FreeBSD", "riscv64", folder.newFolder().toPath()).path();
            fail("no executable fits this platform");
        } catch (IllegalStateException error) {
            assertTrue(error.getMessage(), error.getMessage().contains("freebsd-riscv64"));
            assertTrue(error.getMessage(), error.getMessage().contains("-Dkm.bin="));
            assertTrue(error.getMessage(), error.getMessage().contains("KM_BIN"));
        }
    }

    @Test
    public void developerJarWithoutManifestUsesPath() throws Exception {
        Path onPath = pathDirWithKm("km");
        assertEquals(onPath.toAbsolutePath().toString(),
                resolver("Mac OS X", "aarch64", folder.newFolder().toPath()).path());
    }
}
