package org.bioontology.kobayashimarust.protege;

import java.io.IOException;
import java.nio.file.DirectoryStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

/**
 * The temporary files of the plugin. Every file lives in {@code java.io.tmpdir}
 * and is named {@code kmarust-<jvm pid>-<what>-<number><suffix>}. A query
 * deletes its files when it ends, on every path; a JVM shutdown (normal exit,
 * SIGTERM, SIGINT) deletes the ones still registered; and the first use in a
 * JVM deletes the files of JVMs that no longer run (a JVM killed with SIGKILL
 * runs no hook).
 */
final class TempFiles {

    static final String PREFIX = "kmarust-";
    private static final long PID = ProcessHandle.current().pid();
    private static final Set<Path> LIVE = ConcurrentHashMap.newKeySet();

    static {
        Runtime.getRuntime().addShutdownHook(new Thread(() -> {
            // Stop the native processes first: they may still write these files.
            NativeProcessTree.terminateAll();
            deleteAll();
        }, "km-temp-files-shutdown"));
        deleteOrphans();
    }

    private TempFiles() {
    }

    /** The temporary directory: {@code java.io.tmpdir}. */
    static Path directory() {
        return Paths.get(System.getProperty("java.io.tmpdir"));
    }

    /** A new registered file {@code kmarust-<pid>-<what>-<n><suffix>} in {@link #directory()}. */
    static Path create(String what, String suffix) throws IOException {
        Path file = Files.createTempFile(directory(), PREFIX + PID + "-" + what + "-", suffix);
        LIVE.add(file);
        return file;
    }

    /** Delete a file made by {@link #create}; never throws. */
    static void delete(Path file) {
        if (file == null) return;
        try {
            Files.deleteIfExists(file);
        } catch (IOException | SecurityException ignored) {
            // A file that cannot be deleted stays registered for the shutdown hook.
            return;
        }
        LIVE.remove(file);
    }

    static void deleteAll() {
        for (Path file : new ArrayList<>(LIVE)) delete(file);
    }

    /** Registered files that still exist (for tests). */
    static int liveCount() {
        LIVE.removeIf(file -> !Files.exists(file));
        return LIVE.size();
    }

    /** Delete the files of JVMs that no longer run. */
    private static void deleteOrphans() {
        try (DirectoryStream<Path> files = Files.newDirectoryStream(directory(), PREFIX + "*")) {
            for (Path file : files) {
                String name = file.getFileName().toString().substring(PREFIX.length());
                int dash = name.indexOf('-');
                if (dash <= 0) continue;
                long pid;
                try {
                    pid = Long.parseLong(name.substring(0, dash));
                } catch (NumberFormatException notOurs) {
                    continue;
                }
                if (pid != PID && !ProcessHandle.of(pid).isPresent()) {
                    try {
                        Files.deleteIfExists(file);
                    } catch (IOException | SecurityException ignored) {
                        // another user's file or a race: leave it
                    }
                }
            }
        } catch (IOException | SecurityException ignored) {
            // no readable temp directory: nothing to clean
        }
    }
}
