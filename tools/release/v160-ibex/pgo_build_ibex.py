#!/usr/bin/env python3
"""Exact-source PGO build of a KM v1.5.5 release candidate on ws.

Reproduces the v1.5.4 recipe (`.work/pgo-v154/run_pgo_pipeline.py` and the
glibc-wrapped `pgo-use-bfd` phase recorded in `pgo-use-bfd-build.json`):

1. `git archive` the given commit of a clean worktree, unpack it, and hash
   every file (source manifest); every build phase re-checks the hashes.
2. Instrumented build (`-Cprofile-generate`), LTO, one codegen unit,
   `--features mimalloc --bin km`, explicit `--target=x86_64-unknown-linux-gnu`.
3. Training: the frozen 22-input selection of the v1.5.0 PGO campaign
   (`training-selection.json` in `.work/worktrees/v1.4`), run through the
   ws harness `.work/v152-correctness-1920/run_1920_ws.py` with the v1.5.3
   release flags; every training input must be independently verified
   against the pinned references, otherwise the pipeline stops.
4. `llvm-profdata merge -sparse` of the raw profiles.
5. Profile-use build (`-Cprofile-use=... -Cllvm-args=-pgo-warn-missing-function`)
   linked through `cc-wrapper.sh` (`--defsym=pidfd_spawnp=0
   --defsym=pidfd_getpid=0`) so the binary needs no GLIBC_2.39 symbol and runs
   on Ibex (glibc 2.34). The audit of the build log rejects any profile
   mismatch or discarded non-zero count.

Differences from v1.5.4, all deliberate: the paths are arguments instead of
constants; only the wrapper-linked profile-use binary is built (v1.5.4 also
built a ws-only link `km-pgo-use` that needed GLIBC_2.39 and was not
released; the wrapper-linked binary runs on ws too); the result is copied to
`km-v<version>-rc-pgo` next to its `.sha256`.

Usage:
  pgo_build.py --worktree <clean KM worktree> --root <empty output dir> \
      [--version 1.5.5] [--cpus 32-39] [--train-cpus 32,33,34,35] [--jobs 8]
  pgo_build.py ... --clean   # afterwards: delete target dirs, training runs, raw profiles
"""
import argparse
from concurrent.futures import ProcessPoolExecutor, as_completed
import hashlib
import json
import multiprocessing
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

IBEX_ROOT = Path(os.environ["KM_IBEX_ROOT"])  # Ibex edition for v1.6.0: ws paths replaced by the staged copies
WORK = IBEX_ROOT
HARNESS_DIR = IBEX_ROOT / "harness"
TRAINING_SEL = HARNESS_DIR / "training-selection.json"
INPUTS_MANIFEST = HARNESS_DIR / "full-candidate-inputs-ibex.json"
TOOLCHAIN = Path.home() / ".rustup/toolchains/1.95.0-x86_64-unknown-linux-gnu"
RUSTC = str(TOOLCHAIN / "bin/rustc")
CARGO = str(TOOLCHAIN / "bin/cargo")
LLVM_PROFDATA = str(TOOLCHAIN / "lib/rustlib/x86_64-unknown-linux-gnu/bin/llvm-profdata")
WRAPPER = Path(__file__).resolve().parent / "cc-wrapper.sh"
WRAPPER_SHA256 = "18d4f2e700ce34f536dc98aee1a8b78f51847a98f283b5577b01de5787489191"  # v1.5.4 and v1.5.3
TRAINING_FLAGS = {
    "KM_HT_DDB": "1",
    "KM_HT_NATIVE_FULL": "1",
    "KM_CACHE_CONFORMANCE": "1",
    "KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE": "1",
    "KM_FAST_IRI_GRAMMAR": "1",
    "KM_JSON_GRAPH_EDGES": "1",
}

sys.path.insert(0, str(HARNESS_DIR))
import run_1920_ws  # noqa: E402


def digest(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as f:
        for block in iter(lambda: f.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


class Pipeline:
    def __init__(self, a):
        self.worktree = Path(a.worktree).resolve()
        self.root = Path(a.root).resolve()
        self.version = a.version
        self.cpus = a.cpus
        self.train_cpus = [int(x) for x in a.train_cpus.split(",")]
        self.jobs = str(a.jobs)
        self.timings = {}
        self.root.mkdir(parents=True, exist_ok=True)

    def log_time(self, step, seconds):
        self.timings[step] = round(seconds, 1)
        (self.root / "timings.json").write_text(json.dumps(self.timings, indent=2) + "\n")

    # ---- source
    def export_and_manifest(self):
        commit = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=self.worktree, text=True).strip()
        status = subprocess.check_output(["git", "status", "--porcelain", "--untracked-files=no"], cwd=self.worktree, text=True).strip()
        assert not status, f"worktree dirty: {status}"
        src = self.root / "source"
        if src.exists():
            shutil.rmtree(src)
        src.mkdir(parents=True)
        archive = self.root / "exact-source.tar.gz"
        subprocess.run(["git", "archive", "--format=tar.gz", "-o", str(archive), commit], cwd=self.worktree, check=True)
        subprocess.run(["tar", "-xzf", str(archive), "-C", str(src)], check=True)
        files = {str(p.relative_to(src)): digest(p) for p in sorted(src.rglob("*")) if p.is_file() and not p.is_symlink()}
        cargo_version = re.search(r'^version\s*=\s*"([^"]+)"', (src / "engine/Cargo.toml").read_text(), re.M).group(1)
        assert cargo_version == self.version, f"engine/Cargo.toml says {cargo_version}, expected {self.version}"
        manifest = {
            "schema": "km-pgo-exact-source-manifest-v1",
            "version": self.version,
            "git_commit": commit,
            "archive_sha256": digest(archive),
            "snapshot": str(src),
            "file_count": len(files),
            "files": files,
        }
        (self.root / "source-manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
        return commit, digest(self.root / "source-manifest.json")

    def check_source(self):
        mpath = self.root / "source-manifest.json"
        m = json.loads(mpath.read_text())
        snap = Path(m["snapshot"])
        for rel, expected in m["files"].items():
            assert digest(snap / rel) == expected, f"source file modified: {rel}"
        return digest(mpath)

    # ---- builds
    def build_phase(self, phase, rustflags, wrapper=False, binary_name=None):
        expected_mf = self.check_source()
        target_dir = self.root / f"target-{phase}"
        env = {k: v for k, v in os.environ.items()
               if k not in ["CARGO_ENCODED_RUSTFLAGS", "RUSTC_WRAPPER", "RUSTC_WORKSPACE_WRAPPER", "LLVM_PROFILE_FILE", "CARGO_TARGET_DIR"]}
        env.update(
            PATH=f"{TOOLCHAIN}/bin:{Path.home()}/.cargo/bin:" + env.get("PATH", ""),
            RUSTC=RUSTC,
            CARGO_HOME=str(Path.home() / ".cargo"),
            RUSTUP_HOME=str(Path.home() / ".rustup"),
            CARGO_TARGET_DIR=str(target_dir),
            CARGO_BUILD_JOBS=self.jobs,
            CARGO_PROFILE_RELEASE_LTO="true",
            CARGO_PROFILE_RELEASE_CODEGEN_UNITS="1",
            RUSTFLAGS=rustflags,
        )
        keys = ["CARGO_TARGET_DIR", "CARGO_PROFILE_RELEASE_LTO", "CARGO_PROFILE_RELEASE_CODEGEN_UNITS", "CARGO_BUILD_JOBS"]
        if wrapper:
            assert digest(WRAPPER) == WRAPPER_SHA256, "cc-wrapper.sh differs from the v1.5.4 wrapper"
            env["CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_LINKER"] = str(WRAPPER)
            keys.append("CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_LINKER")
        command = ["taskset", "-c", self.cpus, CARGO, "build", "--offline", "--locked", "--release",
                   "--target=x86_64-unknown-linux-gnu", "--features", "mimalloc", "--bin", "km"]
        receipt = {
            "phase": phase,
            "status": "running",
            "version": self.version,
            "command": command,
            "source_manifest_sha256": expected_mf,
            "rustflags": rustflags,
            "compiler": subprocess.check_output([RUSTC, "-Vv"], text=True),
            "production_environment": {k: env[k] for k in keys},
            "explicit_generic_target": True,
        }
        if wrapper:
            receipt.update(
                linker_wrapper=str(WRAPPER),
                linker_wrapper_sha256=digest(WRAPPER),
                linker_wrapper_purpose="-Wl,--defsym=pidfd_spawnp=0 -Wl,--defsym=pidfd_getpid=0 so the binary needs no GLIBC_2.39 symbol and runs on Ibex (glibc 2.34), as for v1.5.3 and v1.5.4",
            )
        rpath = self.root / f"{phase}-build.json"
        lpath = self.root / f"{phase}-build.log"
        rpath.write_text(json.dumps(receipt, indent=2) + "\n")
        start = time.monotonic()
        with lpath.open("wb") as log:
            proc = subprocess.run(command, cwd=self.root / "source/engine", env=env, stdout=log, stderr=subprocess.STDOUT)
        receipt.update(exit_code=proc.returncode, elapsed_s=time.monotonic() - start)
        assert self.check_source() == expected_mf
        receipt["sources_verified_after"] = True
        assert proc.returncode == 0, f"{phase} build failed (see {lpath})"
        built = target_dir / "x86_64-unknown-linux-gnu/release/km"
        dest = self.root / (binary_name or f"km-{phase}")
        if dest.exists():
            dest.chmod(0o755)
            dest.unlink()
        shutil.copy2(built, dest)
        dest.chmod(0o555)
        receipt.update(status="complete", binary_path=str(dest), binary_sha256=digest(dest))
        if wrapper:
            out = subprocess.run(["objdump", "-T", str(dest)], capture_output=True, text=True, check=True).stdout
            vers = sorted(set(re.findall(r"GLIBC_([0-9.]+)", out)), key=lambda v: [int(x) for x in v.split(".")])
            receipt["glibc_versions"] = vers
            assert all([int(x) for x in v.split(".")] <= [2, 34] for v in vers), f"binary needs glibc > 2.34: {vers}"
        rpath.write_text(json.dumps(receipt, indent=2) + "\n")
        self.log_time(f"build_{phase}", receipt["elapsed_s"])
        print(f"[{phase}] complete in {receipt['elapsed_s']:.1f}s: {receipt['binary_sha256']}", flush=True)
        return receipt

    # ---- training
    def run_training(self, inst):
        profiles = self.root / "profiles"
        train_out = self.root / "training"
        for d in (profiles, train_out):
            if d.exists():
                shutil.rmtree(d)
            d.mkdir(parents=True)
        selection = json.loads(TRAINING_SEL.read_text())
        all_inputs = {r["ontology"]: r for r in json.loads(INPUTS_MANIFEST.read_text())["inputs"]}
        rows = [all_inputs[item["ontology"]] for item in selection["inputs"]]
        assert len(rows) == 22 and selection["flags"] == TRAINING_FLAGS
        inv = {"flags": dict(TRAINING_FLAGS, LLVM_PROFILE_FILE=str(profiles / "%m-%p.profraw")),
               "artifacts": [{"id": "km", "path": inst["binary_path"], "sha256": inst["binary_sha256"]}]}
        inv_str = json.dumps(inv)
        manager = multiprocessing.Manager()
        q = manager.Queue()
        for c in self.train_cpus:
            q.put(c)
        by_r1 = {item["ontology"]: item["r1_wall_s"] for item in selection["inputs"]}
        rows_sorted = sorted(rows, key=lambda r: -by_r1[r["ontology"]])
        tasks = [(i, row, str(train_out / "runs"), inv_str) for i, row in enumerate(rows_sorted)]
        start = time.monotonic()
        records = []
        with ProcessPoolExecutor(max_workers=len(self.train_cpus), initializer=run_1920_ws._init_worker, initargs=(q,)) as ex:
            futs = {ex.submit(run_1920_ws.run_one_ontology, t): t[1]["ontology"] for t in tasks}
            for fut in as_completed(futs):
                _, res = fut.result()
                records.append(res)
                print(f"[train] {res['ontology']}: status={res['measurement_status']} verified={res['verified_solved']} wall={res['wall_s']:.2f}s", flush=True)
                assert res["measurement_status"] == "executed_unvalidated" and res["verified_solved"] is True, f"training verification failed on {res['ontology']}: {res}"
        profs = [{"path": str(p), "bytes": p.stat().st_size, "sha256": digest(p)} for p in sorted(profiles.glob("*.profraw"))]
        assert profs and all(p["bytes"] > 0 for p in profs), "no non-empty .profraw files"
        pm = {"profiles": profs, "source_manifest_sha256": self.check_source(), "instrumented_binary_sha256": inst["binary_sha256"]}
        (self.root / "profile-manifest.json").write_text(json.dumps(pm, indent=2) + "\n")
        tr = {"status": "complete", "elapsed_s": time.monotonic() - start, "outcomes_completed": len(records),
              "all_independently_verified": True, "raw_profile_count": len(profs),
              "training_selection": str(TRAINING_SEL), "training_selection_sha256": digest(TRAINING_SEL),
              "harness": str(HARNESS_DIR / "run_1920_ws.py"), "harness_sha256": digest(HARNESS_DIR / "run_1920_ws.py"),
              "training_wall_s": {r["ontology"]: r["wall_s"] for r in records},
              "profile_manifest_sha256": digest(self.root / "profile-manifest.json"),
              "source_manifest_sha256": self.check_source()}
        (self.root / "training-receipt.json").write_text(json.dumps(tr, indent=2) + "\n")
        self.log_time("training", tr["elapsed_s"])
        print(f"[train] complete in {tr['elapsed_s']:.1f}s ({len(profs)} raw profiles)", flush=True)
        return pm

    def merge_profiles(self, pm):
        dest = self.root / "merged.profdata"
        if dest.exists():
            dest.unlink()
        start = time.monotonic()
        r = subprocess.run([LLVM_PROFDATA, "merge", "-sparse", "-o", str(dest)] + [p["path"] for p in pm["profiles"]],
                           capture_output=True, text=True, check=True)
        (self.root / "merge.log").write_text(r.stdout + r.stderr)
        summ = subprocess.run([LLVM_PROFDATA, "show", "--detailed-summary", str(dest)], capture_output=True, text=True, check=True)
        (self.root / "profile-summary.txt").write_text(summ.stdout + summ.stderr)
        funcs = subprocess.run([LLVM_PROFDATA, "show", "--all-functions", str(dest)], capture_output=True, text=True, check=True)
        (self.root / "profile-functions.txt").write_text(funcs.stdout)
        for label in ["Total functions", "Maximum function count"]:
            m = re.search(re.escape(label) + r":\s*(\d+)", summ.stdout)
            assert m and int(m.group(1)) > 0, (label, summ.stdout)
        rec = {"status": "complete", "elapsed_s": time.monotonic() - start, "tool": LLVM_PROFDATA, "tool_sha256": digest(LLVM_PROFDATA),
               "raw_profile_count": len(pm["profiles"]), "merged_path": str(dest), "merged_sha256": digest(dest),
               "merged_bytes": dest.stat().st_size, "profile_summary_sha256": digest(self.root / "profile-summary.txt"),
               "profile_functions_sha256": digest(self.root / "profile-functions.txt"), "source_manifest_sha256": self.check_source()}
        (self.root / "merge-receipt.json").write_text(json.dumps(rec, indent=2) + "\n")
        self.log_time("merge", rec["elapsed_s"])
        print(f"[merge] {rec['merged_sha256']} ({rec['merged_bytes']} bytes)", flush=True)
        return rec

    def audit_pgo_build(self, phase):
        lpath = self.root / f"{phase}-build.log"
        lines = lpath.read_text(errors="replace").splitlines()
        missing = [re.search(r"no profile data available for function (.*?) Hash = (\d+) up to (\d+) count discarded", l)
                   for l in lines if "no profile data available for function" in l]
        assert all(missing)
        trained = {x.strip()[:-1] for x in (self.root / "profile-functions.txt").read_text().splitlines()
                   if x.startswith("  ") and not x.startswith("    ") and x.endswith(":")}
        names = {m[1] for m in missing}
        suspect = [x for x in lines if re.search(r"(hash mismatch|control flow change|profile.*mismatch|mismatched.*profile|profile data may be out of date|malformed.*profile)", x, re.I)]
        nonzero = [l for l in lines if (m := re.search(r"up to (\d+) count discarded", l)) and int(m[1]) > 0]
        audit = {"build_exit_code": 0, "full_build_log_sha256": digest(lpath), "missing_function_warning_count": len(missing),
                 "missing_function_unique": len(names), "zero_count_discarded_in_every_missing_warning": all(int(m[3]) == 0 for m in missing),
                 "trained_function_count": len(trained), "exact_trained_function_names_also_missing": sorted(names & trained),
                 "profile_mismatch_lines": suspect, "nonzero_discarded_warning_lines": nonzero,
                 "source_manifest_sha256": self.check_source(), "profile_functions_sha256": digest(self.root / "profile-functions.txt")}
        (self.root / "build-warning-audit.json").write_text(json.dumps(audit, indent=2) + "\n")
        assert not suspect and not nonzero and not (names & trained), f"PGO warning audit failed: {audit}"
        print(f"[audit] {len(trained)} trained functions, {len(missing)} zero-count cold functions, 0 mismatches", flush=True)
        return audit

    def run(self):
        t0 = time.monotonic()
        commit, mf = self.export_and_manifest()
        print(f"[init] commit={commit} source_manifest_sha256={mf}", flush=True)
        inst = self.build_phase("instrumented", f"-Cprofile-generate={self.root / 'profiles'}")
        pm = self.run_training(inst)
        merge = self.merge_profiles(pm)
        name = f"km-v{self.version}-rc-pgo"
        pgo = self.build_phase("pgo-use-bfd", f"-Cprofile-use={merge['merged_path']} -Cllvm-args=-pgo-warn-missing-function",
                               wrapper=True, binary_name=name)
        self.audit_pgo_build("pgo-use-bfd")
        smoke = subprocess.run([pgo["binary_path"], "routes"], capture_output=True, text=True)
        assert smoke.returncode == 0 and any(l.startswith("auto") for l in smoke.stdout.splitlines()), "km routes smoke failed"
        (self.root / f"{name}.sha256").write_text(f"{pgo['binary_sha256']}  {name}\n")
        receipt = {
            "schema": "km-v155-pgo-native-build-receipt-v1",
            "version": self.version,
            "source_commit": commit,
            "source_manifest_sha256": mf,
            "binary_path": pgo["binary_path"],
            "binary_sha256": pgo["binary_sha256"],
            "glibc_versions": pgo["glibc_versions"],
            "instrumented_binary_sha256": inst["binary_sha256"],
            "merged_profile_sha256": merge["merged_sha256"],
            "training_receipt_sha256": digest(self.root / "training-receipt.json"),
            "build_warning_audit_sha256": digest(self.root / "build-warning-audit.json"),
            "linker_wrapper_sha256": pgo["linker_wrapper_sha256"],
            "PGO": True,
            "rustc": pgo["compiler"].splitlines()[0],
            "compiler_full": pgo["compiler"],
            "pipeline": str(Path(__file__).resolve()),
            "pipeline_sha256": digest(__file__),
        }
        (self.root / "native-build-receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
        self.log_time("total", time.monotonic() - t0)
        print(json.dumps(receipt, indent=2), flush=True)

    def clean(self):
        for d in ["target-instrumented", "target-pgo-use-bfd", "training", "profiles", "source"]:
            p = self.root / d
            if p.exists():
                shutil.rmtree(p)
        print("[clean] removed target dirs, training runs, raw profiles and the unpacked source (the archive, manifests and receipts stay)")


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--worktree", required=True)
    ap.add_argument("--root", required=True)
    ap.add_argument("--version", default="1.5.5")
    ap.add_argument("--cpus", default="32-39")
    ap.add_argument("--train-cpus", default="32,33,34,35")
    ap.add_argument("--jobs", default=8, type=int)
    ap.add_argument("--clean", action="store_true")
    a = ap.parse_args()
    p = Pipeline(a)
    p.clean() if a.clean else p.run()
