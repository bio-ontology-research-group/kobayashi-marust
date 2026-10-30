//! Running a compiled Lean checker as a subprocess.
//!
//! A Lean executable starts its runtime threads before any Lean code runs:
//! the thread that runs `main` (stack `LEAN_STACK_SIZE_KB`, default 1 GiB in
//! v4.30) and a second runtime thread with a fixed 1 GiB stack. Under strict
//! commit accounting (`vm.overcommit_memory = 2`, the workstation `ws`) a
//! thread stack is charged in full when the thread starts, so when other
//! processes hold most of the commit limit the runtime throws
//! `lean::exception: failed to create thread` and the checker aborts
//! (SIGABRT, exit 134) without reading its input (finding of 2026-10-30:
//! the inert-sort unit tests failed this way while their documents check).
//! The checker's verdict never depended on the abort; only its start did.
//!
//! [`run`] gives the `main` thread a 256 MiB stack unless the caller set
//! `LEAN_STACK_SIZE_KB`, which halves the commit charge, and retries the
//! start-up failure, recognised by its message, with the pauses of
//! `bigstack`. Every other exit, including any other abort, is returned
//! unchanged, so a caller that requires success still fails closed.

use std::path::Path;
use std::process::{Command, Output};

/// Stack of the thread that runs the checker's `main`, in KiB.
const MAIN_STACK_KB: &str = "262144";

/// Pauses between retries of a checker whose runtime could not start a
/// thread (milliseconds), about 5 s in total.
const RETRY_PAUSES_MS: [u64; 9] = [10, 20, 40, 80, 160, 320, 640, 1280, 2560];

fn startup_thread_failure(output: &Output) -> bool {
    use std::os::unix::process::ExitStatusExt;
    output.status.signal() == Some(6)
        && String::from_utf8_lossy(&output.stderr).contains("failed to create thread")
}

/// Run `checker` on `document` and collect its output.
pub fn run(checker: &Path, document: &Path) -> std::io::Result<Output> {
    let mut attempt = 0;
    loop {
        let mut command = Command::new(checker);
        command.arg(document);
        if std::env::var_os("LEAN_STACK_SIZE_KB").is_none() {
            command.env("LEAN_STACK_SIZE_KB", MAIN_STACK_KB);
        }
        let output = command.output()?;
        if !startup_thread_failure(&output) || attempt == RETRY_PAUSES_MS.len() {
            return Ok(output);
        }
        std::thread::sleep(std::time::Duration::from_millis(RETRY_PAUSES_MS[attempt]));
        attempt += 1;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_start_up_thread_failure_is_recognised_and_other_aborts_are_not() {
        use std::os::unix::process::ExitStatusExt;
        let abort = |stderr: &str| Output {
            status: std::process::ExitStatus::from_raw(6),
            stdout: Vec::new(),
            stderr: stderr.as_bytes().to_vec(),
        };
        assert!(startup_thread_failure(&abort(
            "libc++abi: terminating due to uncaught exception of type lean::exception: failed to create thread"
        )));
        assert!(!startup_thread_failure(&abort("Stack overflow detected. Aborting.")));
        let rejected = Output {
            status: std::process::ExitStatus::from_raw(1 << 8),
            stdout: Vec::new(),
            stderr: b"failed to create thread".to_vec(),
        };
        assert!(!startup_thread_failure(&rejected));
    }
}
