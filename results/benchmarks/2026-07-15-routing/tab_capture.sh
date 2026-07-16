#!/bin/bash
# Diagnostic worker wrapper for the 9635 tableau-route gate.  It preserves the
# exact TInput handed to the legacy tableau worker and its otherwise-suppressed
# stderr, then delegates without changing the worker's exit status.
set -o pipefail
root=/ibex/scratch/hohndor/km/routing_20260715
/usr/bin/tee "$root/tab-9635-final2.tin.json" \
  | "$root/km-profiled-final2" tableau \
      2>"$root/tab-9635-final2.stderr"

