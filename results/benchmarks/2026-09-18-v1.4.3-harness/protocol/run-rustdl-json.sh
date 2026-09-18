#!/usr/bin/env bash
# rustdl leg for the RELEASE CORPUS REPORT: `classify --json`, output captured.
#
# WHY --json AND NOT THE TEXT SURFACE. The report needs three things per ontology
# that the human banner does not expose as machine-readable fields: the `consistent`
# verdict, the `incomplete` flag, and the unsatisfiable list. `# abox_check:` is a
# proxy for the first and a sound UNDER-approximation, not the verdict itself.
#
# The verdict field is the point. A 2026-08-15 sweep passed both pre-registered gate
# clauses (`ok -> dnf` = 0, dMISSED +0.78%) while flipping ore_ont_16372 from
# `consistent=false` to `consistent=true` on an ontology Konclude, HermiT and rustdl's
# own `consistent` all call inconsistent. Neither clause could see it: both arms
# completed, and the MISSED net excludes unsat classes on both sides.
#
#   MISSED_NET_RUSTDL       path to the pinned rustdl binary            (REQUIRED)
#   MISSED_NET_RUSTDL_ARGS  extra `classify` args                       (optional)
#   HARNESS_OUT_DIR         capture dir; <stem>.json gets stdout        (optional)
#
# stdout is REDIRECTED, not tee'd, for the reason run-rustdl.sh documents: a pipe
# makes the wrapper exit with tee's status, collapsing ErrCrash into Ok.
set -u
: "${MISSED_NET_RUSTDL:?set MISSED_NET_RUSTDL to the pinned rustdl binary}"
case "${1:-}" in
  --version | -V) exec "$MISSED_NET_RUSTDL" --version ;;
esac
# `ulimit -v` caps ADDRESS SPACE (RLIMIT_AS). Darwin has no RLIMIT_AS, so on macOS
# this call fails — and an unguarded failure here exits the wrapper BEFORE the
# reasoner runs, turning every case into `err_reject` in ~1ms. The release corpus
# report then read that as `0 classified / 424 DNF` and its confirmation pass
# relabelled the wreckage "CAP-BORDERLINE, gate PASSES" (2026-08-29). Apply the cap
# where the platform supports it; skip it where it does not.
ulimit -v $((24 * 1024 * 1024)) 2>/dev/null || true
if [ -n "${HARNESS_OUT_DIR:-}" ]; then
  mkdir -p "$HARNESS_OUT_DIR"
  out="$HARNESS_OUT_DIR/$(basename "${1%.*}").json"
else
  out=/dev/null
fi
# shellcheck disable=SC2086
exec "$MISSED_NET_RUSTDL" classify --json ${MISSED_NET_RUSTDL_ARGS:-} "$1" > "$out"
