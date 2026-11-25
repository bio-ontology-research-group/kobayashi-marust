//! The process-environment lock of the library tests.
//!
//! `cargo test` runs the tests of this crate on parallel threads of one
//! process, and the process environment is shared. Production code reads
//! `KM_*` switches at many places, so a test that sets or removes a variable
//! (directly, through `routing::EnvironmentGuard`, or through a route bundle
//! applied by the orchestrator) changes what every test running at the same
//! moment computes. Separate per-module locks did not exclude each other.
//!
//! Every library test takes this lock for its whole body: [`write`] when it
//! changes the environment or drives code that does, [`read`] otherwise.
//! Readers run in parallel with each other and never beside a writer. A
//! nested request on a thread that already holds the lock is granted without
//! blocking (helpers such as `frontend::lock_test_environment` call [`write`]
//! inside tests that hold it); a write request nested in a read is a bug in
//! the test's classification and panics instead of deadlocking.
//! [`EnvVar`] restores a variable on drop, also when the test panics.

use std::cell::{Cell, RefCell};
use std::ffi::OsString;
use std::sync::{RwLock, RwLockReadGuard, RwLockWriteGuard};

static LOCK: RwLock<()> = RwLock::new(());

enum Held {
    Read(#[allow(dead_code)] RwLockReadGuard<'static, ()>),
    Write(#[allow(dead_code)] RwLockWriteGuard<'static, ()>),
}

thread_local! {
    static HELD: RefCell<Option<Held>> = const { RefCell::new(None) };
    static DEPTH: Cell<usize> = const { Cell::new(0) };
}

/// Holds the environment lock until dropped.
#[must_use = "the environment lock is released when this guard is dropped"]
pub(crate) struct EnvGuard {
    _not_send: std::marker::PhantomData<*const ()>,
}

impl Drop for EnvGuard {
    fn drop(&mut self) {
        let depth = DEPTH.with(|d| {
            let next = d.get() - 1;
            d.set(next);
            next
        });
        if depth == 0 {
            HELD.with(|held| held.borrow_mut().take());
        }
    }
}

fn acquire(exclusive: bool) -> EnvGuard {
    let depth = DEPTH.with(Cell::get);
    if depth > 0 {
        let held_write = HELD.with(|held| matches!(*held.borrow(), Some(Held::Write(_))));
        assert!(
            held_write || !exclusive,
            "test_env: environment write requested inside a read-locked test; take test_env::write() at the start of the test"
        );
    } else {
        let held = if exclusive {
            Held::Write(LOCK.write().unwrap_or_else(|poisoned| poisoned.into_inner()))
        } else {
            Held::Read(LOCK.read().unwrap_or_else(|poisoned| poisoned.into_inner()))
        };
        HELD.with(|slot| *slot.borrow_mut() = Some(held));
    }
    DEPTH.with(|d| d.set(depth + 1));
    EnvGuard { _not_send: std::marker::PhantomData }
}

/// Exclusive: the test changes the process environment.
pub(crate) fn write() -> EnvGuard {
    acquire(true)
}

/// Shared: the test only reads the environment (through production code).
pub(crate) fn read() -> EnvGuard {
    acquire(false)
}

/// A variable set or removed for the scope of a test; restored on drop.
pub(crate) struct EnvVar {
    name: String,
    previous: Option<OsString>,
}

impl EnvVar {
    pub(crate) fn set(name: &str, value: impl AsRef<std::ffi::OsStr>) -> Self {
        let previous = std::env::var_os(name);
        std::env::set_var(name, value);
        EnvVar { name: name.to_string(), previous }
    }

    pub(crate) fn remove(name: &str) -> Self {
        let previous = std::env::var_os(name);
        std::env::remove_var(name);
        EnvVar { name: name.to_string(), previous }
    }
}

impl Drop for EnvVar {
    fn drop(&mut self) {
        match self.previous.take() {
            Some(value) => std::env::set_var(&self.name, value),
            None => std::env::remove_var(&self.name),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn nested_requests_reenter_and_release() {
        let _outer = write();
        {
            let _inner = write();
            let _reader = read();
        }
        let _again = read();
    }

    #[test]
    fn env_var_restores_the_previous_value() {
        let _env = write();
        let name = "KM_TEST_ENV_RESTORE_PROBE";
        std::env::remove_var(name);
        {
            let _set = EnvVar::set(name, "1");
            assert_eq!(std::env::var(name).as_deref(), Ok("1"));
        }
        assert!(std::env::var_os(name).is_none());
    }
}
