package org.bioontology.kobayashimarust.protege;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.concurrent.TimeUnit;
import java.util.stream.Collectors;

/** Owns termination and reaping of one native KM supervisor process tree. */
final class NativeProcessTree {

    private NativeProcessTree() {
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
