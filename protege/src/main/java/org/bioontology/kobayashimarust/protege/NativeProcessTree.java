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
        for (ProcessHandle descendant : descendants) {
            descendant.destroy();
        }
        process.destroy();
        try {
            if (!process.waitFor(500, TimeUnit.MILLISECONDS)) {
                process.destroyForcibly();
                process.waitFor(5, TimeUnit.SECONDS);
            }
        } catch (InterruptedException error) {
            process.destroyForcibly();
            Thread.currentThread().interrupt();
        }
        for (ProcessHandle descendant : descendants) {
            if (descendant.isAlive()) {
                descendant.destroyForcibly();
            }
        }
        long deadline = System.nanoTime() + TimeUnit.SECONDS.toNanos(5);
        while (descendants.stream().anyMatch(ProcessHandle::isAlive)
                && System.nanoTime() < deadline) {
            try {
                Thread.sleep(10);
            } catch (InterruptedException error) {
                Thread.currentThread().interrupt();
                break;
            }
        }
    }
}
