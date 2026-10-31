#!/usr/bin/env bash
# Copy the chunk records of finished Ibex runs to a local data dir (run on ws).
#   fetch.sh <root-name> <local-data-dir> <label-job>...
#   e.g. fetch.sh v155-release-20261101 .work/v155-release-cert/data \
#          heldout-rc-5490xxxx heldout-v153-5490xxxx heldout-konclude-5490xxxx pool-rc-5490xxxx
# Also stores files.sha256 and a hash list of every record.json of each run,
# for build-completion.json. Refuses runs with a chunk that is not complete.
set -euo pipefail
name=${1:?root name}; dest=${2:?local data dir}; shift 2
ROOT=/ibex/scratch/projects/c2014/hohndor/km/$name
mkdir -p "$dest"
scp -q "ibex:$ROOT/files.sha256" "$dest/files.sha256"
for run in "$@"; do
  mkdir -p "$dest/$run"
  rsync -a --include='*.json' --exclude='*' "ibex:$ROOT/$run/chunks/" "$dest/$run/"
  ssh ibex "cd $ROOT/$run && find . -name record.json -print0 | sort -z | xargs -0 sha256sum" > "$dest/$run.record-files.sha256"
  python3 - "$dest/$run" <<'PY'
import json, os, sys
d = sys.argv[1]
bad = [f for f in os.listdir(d) if f.endswith('.json') and json.load(open(os.path.join(d, f))).get('status') != 'complete']
n = sum(len(json.load(open(os.path.join(d, f)))['outcomes']) for f in os.listdir(d) if f.endswith('.json'))
print(d, 'chunks', len(os.listdir(d)), 'outcomes', n, 'incomplete', bad)
sys.exit(1 if bad else 0)
PY
done
