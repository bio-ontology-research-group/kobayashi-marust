package org.bioontology.kobayashimarust.protege;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.TimeUnit;
import java.util.stream.Collectors;

/** Owns termination and reaping of one native KM supervisor process tree. */
final class NativeProcessTree {

    /** Environment variable through which km workers watch their supervisor (km: cli.rs). */
    static final String SUPERVISOR_PID_ENV = "KM_SUPERVISOR_PID";

    /** Every native process tree started through {@link #start} that has not exited. */
    private static final Set<Process> LIVE = ConcurrentHashMap.newKeySet();

    static {
        // A JVM that exits normally or on SIGTERM / SIGINT takes every native
        // tree with it. (SIGKILL runs no hook; see start().)
        Runtime.getRuntime().addShutdownHook(new Thread(NativeProcessTree::terminateAll,
                "km-native-shutdown"));
    }

    private NativeProcessTree() {
    }

    /**
     * Start a native KM process owned by this JVM. The process is registered
     * until it exits, so a JVM shutdown terminates its whole tree. The JVM's
     * pid is exported as the supervisor of the tree: a km worker whose
     * supervisor is gone exits within 100 ms, so the workers of a
     * {@code km incremental-source} session (which does not export its own
     * pid) also die with a JVM that was killed without running its hooks.
     * {@code km classify} and {@code km explain} replace the variable with
     * their own pid for their workers.
     */
    static Process start(ProcessBuilder builder) throws java.io.IOException {
        builder.environment().put(SUPERVISOR_PID_ENV, Long.toString(ProcessHandle.current().pid()));
        Process process = builder.start();
        LIVE.add(process);
        process.onExit().thenRun(() -> LIVE.remove(process));
        return process;
    }

    /** Native process trees started through {@link #start} that are still alive (for tests). */
    static int liveCount() {
        LIVE.removeIf(process -> !process.isAlive());
        return LIVE.size();
    }

    /** Terminate every registered tree (JVM shutdown). */
    static void terminateAll() {
        for (Process process : new ArrayList<>(LIVE)) {
            terminateAndWait(process);
        }
    }

    /**
     * Stop a supervisor and every descendant visible before termination.
     * Descendants are signalled first so a route worker cannot become an
     * untracked orphan when its supervisor exits.
     */
    static void terminateAndWait(Process process) {
        if (process == null) {
            return;
        }
        LIVE.remove(process);
        List<ProcessHandle> descendants = new ArrayList<>(process.descendants()
                .collect(Collectors.toList()));
        Collections.reverse(descendants);
        // Preserve interruption without letting it skip ownership cleanup.
        boolean interrupted = Thread.interrupted();
        long deadline = System.nanoTime() + TimeUnit.SECONDS.toNanos(3);
        try {
            for (ProcessHandle descendant : descendants) {
                descendant.destroy();
            }
            // Keep the supervisor alive to reap its children. Killing it immediately
            // can orphan zombies under a subreaper; ProcessHandle still sees them alive.
            interrupted |= awaitDescendants(descendants, phaseDeadline(deadline, 500));
            for (ProcessHandle descendant : descendants) {
                if (descendant.isAlive()) {
                    descendant.destroyForcibly();
                }
            }
            interrupted |= awaitDescendants(descendants, phaseDeadline(deadline, 500));
            process.destroy();
            interrupted |= awaitProcess(process, phaseDeadline(deadline, 500));
            if (process.isAlive()) {
                process.destroyForcibly();
            }
            interrupted |= awaitProcess(process, deadline);
            interrupted |= awaitDescendants(descendants, deadline);
        } finally {
            if (interrupted) {
                Thread.currentThread().interrupt();
            }
        }
    }

    private static long phaseDeadline(long deadline, long millis) {
        return Math.min(deadline, System.nanoTime() + TimeUnit.MILLISECONDS.toNanos(millis));
    }

    private static boolean awaitDescendants(List<ProcessHandle> descendants, long deadline) {
        boolean interrupted = false;
        while (descendants.stream().anyMatch(ProcessHandle::isAlive)
                && System.nanoTime() < deadline) {
            try {
                TimeUnit.NANOSECONDS.sleep(Math.min(TimeUnit.MILLISECONDS.toNanos(10),
                        Math.max(0, deadline - System.nanoTime())));
            } catch (InterruptedException error) {
                interrupted = true;
            }
        }
        return interrupted;
    }

    private static boolean awaitProcess(Process process, long deadline) {
        boolean interrupted = false;
        while (process.isAlive() && System.nanoTime() < deadline) {
            try {
                process.waitFor(Math.max(0, deadline - System.nanoTime()), TimeUnit.NANOSECONDS);
            } catch (InterruptedException error) {
                interrupted = true;
            }
        }
        return interrupted;
    }
}
