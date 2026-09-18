#!/usr/bin/env bash
# Kobayashi-MaRust v1.4.0 -- the first version that PUBLISHES a binary, so it is
# pinned by sha256 in reasoners.lock and fetched by ./setup.sh (linux-x64 only).
#
# CARRIED ALONGSIDE v1.3.0 DELIBERATELY. Every KM measurement recorded in docs/ used
# v1.3.0; v1.4.0 shipped 2026-09-16 and is a different reasoner. Running both is what
# tells you whether the recorded numbers still describe the current KM -- reading one
# version's results as if they were the other's is the mistake this arm exists to
# prevent.
#
# ROUTE = `auto`, NOT `production_all`. run-km-latest.sh uses production_all because
# on v0.2.32 KM's bare default DNF'd on ore_ont_10019 while production_all took
# 0.25 s. MEASURED ON v1.4.0 (2026-09-16): `auto` classifies ore_ont_10019 in 175 ms
# and production_all in 145 ms — the rationale is STALE. `auto` is KM's own shipped
# default ("learned source-profile decision tree (classify default)"), so using it
# measures KM as it ships rather than as we tuned it two minor versions ago.
#
# THE 20GB ulimit IS A NO-OP ON DARWIN and this wrapper runs on the Mac. v0.2.32
# reached 237 GB on pizza uncapped; v1.4.0 does NOT reproduce that (pizza completes
# in well under a second). The host has 128 GB. If a future run on a Linux host
# needs the cap, copy the `ulimit -v` guard from run-km-latest.sh.
#
# NOTE ON CONVENTIONS, load-bearing for any closure comparison:
#  - On an INCONSISTENT KB, KM reports `consistent: false` with EMPTY subsumptions
#    and EMPTY unsatisfiable. rustdl instead marks every class unsatisfiable. Do not
#    diff those two shapes directly.
#  - v0.2.32 emitted Tseitin definers (Q_N) in `subsumptions`; v1.4.0 emits none on
#    pizza. Filter defensively before any closure comparison.
# KM IS USER-SUPPLIED and NOT redistributed here. Look in vendor/ first (where
# setup.sh tells you to put it), then bin/, then honour KM_BIN_DIR.
#
# The binary is PLATFORM-SPECIFIC. A macOS build committed to this repo failed on
# Linux with "Exec format error" -- which is the general hazard with bin/: it holds
# binaries built for whichever machine produced them, and a clone on another
# platform cannot run them. Obtain or build KM for YOUR platform.
_d="$(cd "$(dirname "$0")/.." && pwd)"
if [ -n "${KM140_BIN:-}" ]; then B="$KM140_BIN"
elif [ -x "$_d/vendor/km" ]; then B="$_d/vendor/km"
else B="$_d/bin/km"; fi
[ -x "$B" ] || { echo "run-km-v130: KM binary not found/executable at $B -- see ./setup.sh --check" >&2; exit 2; }
if [ -n "${HARNESS_OUT_DIR:-}" ]; then
  mkdir -p "$HARNESS_OUT_DIR"
  exec bash -c "set -o pipefail; \"\$0\" classify --route auto \"\$1\" | tee \"\$2\"" \
       "$B" "$1" "$HARNESS_OUT_DIR/$(basename "${1%.*}").json"
fi
exec "$B" classify --route auto "$1"
