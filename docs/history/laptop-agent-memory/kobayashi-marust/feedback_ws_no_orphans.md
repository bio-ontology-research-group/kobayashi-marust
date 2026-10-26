---
name: feedback_ws_no_orphans
description: "HARD RULE — never leave orphaned km processes on ws; run km under its own process group with group-kill on timeout, and bound threads"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: f75fe881-cb21-41f6-8110-ddbbedcc36b5
---

User HARD RULE (2026-06-25, after I spiked ws load to 144 on 56 cores with
~13 orphaned `km` processes): **never leave runaway/orphaned km processes on ws.**
Targeted ws evals are fine (see [[feedback_prefer_ibex]] / the targeted-ws vs
rare-unimatrix-full-sweep workflow), but they MUST clean up after themselves.

**Why it happens:** `km classify` is an ORCHESTRATOR — it spawns child
subprocesses (`km engine`, `km elc`, `km tableau` racers + parallel workers). A
plain `subprocess.run(..., timeout=N)` (or a dropped ssh session) kills only the
DIRECT child (`km`); the orchestrator's children ORPHAN and keep burning cores.
Across a multi-ont loop or repeated KM_DUMP_TIN runs, orphans accumulate ->
load explosion. Also `km classify` defaults KM_HT_PAR + KM_THREADS to ALL cores,
so each run is already aggressive on a shared box.

**How to apply (every ws km run):**
1. Run km in its OWN process group and kill the WHOLE group on timeout:
   Python `subprocess.Popen(argv, start_new_session=True)` + on TimeoutExpired
   `os.killpg(os.getpgid(p.pid), signal.SIGKILL)`. Shell: `setsid` + `kill -- -<pgid>`,
   or `timeout --signal=KILL --kill-after=5 <T> setsid <cmd>`. The existing
   `~/nomval/ore_runone.py` already does this (start_new_session + group kill) —
   prefer it, or the group-safe `~/nomval/clsval.py` (scp'd from scratchpad).
2. BOUND parallelism for validation: `KM_THREADS=1 KM_HT_PAR=1` (targeted evals
   don't need the cores; a stray child then burns <=1 core, not 56).
3. For fast-Ht-only checks prefer the STANDALONE `tableau_cli < tin.json`
   (single process, no orchestrator children) — killing it kills everything.
4. After ANY ws session: `ps -u <me> -o pid,etimes,args | grep -E
   "kobayashi|/km |tableau_cli|ofn|cargo|rustc"` and kill leftovers BY PID
   (not `pkill -f`, which self-matches the ssh — see [[CLAUDE.md]]).

Cleanup done 2026-06-25: killed 12 PIDs (km engine/classify/tableau/elc +
cargo/rustc), load 144 -> decaying, 0 km procs remaining.
