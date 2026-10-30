#!/bin/bash
# tee worker stdin to $CAP_DIR/input-$$.json, then run the given worker
bin=${CAP_BIN:?}
f=$CAP_DIR/input-$(date +%s%N).json
tee "$f" | "$bin" tableau "$@"
