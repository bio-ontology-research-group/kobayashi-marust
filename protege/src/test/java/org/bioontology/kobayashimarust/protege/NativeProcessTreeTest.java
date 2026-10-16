package org.bioontology.kobayashimarust.protege;

import static org.junit.Assert.*;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.concurrent.TimeUnit;
import org.junit.Test;

/** Process-only ownership regressions; no native reasoner is invoked. */
public class NativeProcessTreeTest {
    @Test
    public void supervisorReapsChildBeforeItIsTerminated() throws Exception {
        checkTermination(false, false);
    }

    @Test
    public void interruptedCancellationStillCleansUpAndPreservesInterrupt() throws Exception {
        checkTermination(false, true);
    }

    @Test
    public void stubbornChildIsForcedWhileSupervisorCanStillReap() throws Exception {
        checkTermination(true, false);
    }

    private static void checkTermination(boolean stubborn, boolean interrupt) throws Exception {
        Path directory = Files.createTempDirectory("km-process-tree-test-");
        Path pid = directory.resolve("child.pid");
        Path ready = directory.resolve("ready");
        Path reaped = directory.resolve("reaped");
        Path term = directory.resolve("term");
        // WNOWAIT deliberately leaves a dead child unreaped for 200ms. The
        // supervisor must survive this interval, rather than orphaning a zombie.
        String child = "import signal,time,pathlib,sys; "
                + (stubborn ? "signal.signal(signal.SIGTERM, lambda *_: pathlib.Path(sys.argv[2]).write_text('term')); " : "")
                + "pathlib.Path(sys.argv[1]).write_text('ready'); time.sleep(60)";
        String script = "import os,pathlib,subprocess,sys,time\n"
                + "child=subprocess.Popen([sys.executable, '-c', sys.argv[1], sys.argv[3], sys.argv[5]])\n"
                + "while not pathlib.Path(sys.argv[3]).exists(): time.sleep(.01)\n"
                + "pathlib.Path(sys.argv[2]).write_text(str(child.pid))\n"
                + "os.waitid(os.P_PID,child.pid,os.WEXITED|os.WNOWAIT)\n"
                + "time.sleep(.2)\nchild.wait()\n"
                + "pathlib.Path(sys.argv[4]).write_text('reaped')\n"
                + "time.sleep(60)\n";
        Process supervisor = new ProcessBuilder("/usr/bin/python3", "-c", script,
                child, pid.toString(), ready.toString(), reaped.toString(), term.toString())
                .redirectError(ProcessBuilder.Redirect.INHERIT).start();
        long childPid = -1;
        try {
            long startDeadline = System.nanoTime() + TimeUnit.SECONDS.toNanos(5);
            while ((!Files.exists(pid) || Files.size(pid) == 0) && supervisor.isAlive()
                    && System.nanoTime() < startDeadline) {
                Thread.sleep(10);
            }
            assertTrue("supervisor did not publish child", Files.exists(pid) && Files.size(pid) > 0);
            childPid = Long.parseLong(new String(Files.readAllBytes(pid), StandardCharsets.UTF_8));
            assertTrue(ProcessHandle.of(childPid).map(ProcessHandle::isAlive).orElse(false));
            long start = System.nanoTime();
            if (interrupt) Thread.currentThread().interrupt();
            NativeProcessTree.terminateAndWait(supervisor);
            boolean wasInterrupted = Thread.interrupted();
            assertEquals("interrupt status changed", interrupt, wasInterrupted);
            assertFalse("supervisor survived cancellation", supervisor.isAlive());
            assertFalse("child survived or remained an unreaped zombie",
                    ProcessHandle.of(childPid).map(ProcessHandle::isAlive).orElse(false));
            assertTrue("supervisor was killed before reaping child", Files.exists(reaped));
            if (stubborn) assertTrue("child never received graceful termination", Files.exists(term));
            assertTrue("cancellation exceeded its bounded budget",
                    System.nanoTime() - start < TimeUnit.SECONDS.toNanos(4));
        } finally {
            Thread.interrupted();
            if (supervisor.isAlive()) NativeProcessTree.terminateAndWait(supervisor);
            if (childPid > 0) ProcessHandle.of(childPid).ifPresent(ProcessHandle::destroyForcibly);
            for (Path path : new Path[] {pid, ready, reaped, term}) Files.deleteIfExists(path);
            Files.deleteIfExists(directory);
        }
    }
}
