#!/usr/bin/env bash
# Stage the v1.5.5 release measurement root on Ibex (run on ws).
#
#   stage.sh <root-name> <rc-binary> <rc-native-build-receipt.json>
#   e.g. stage.sh v155-release-20261031 \
#          .work/pgo-v155/km-v1.5.5-rc-pgo .work/pgo-v155/native-build-receipt.json
#
# Creates /ibex/scratch/projects/c2014/hohndor/km/<root-name>/ with
#   protocol/   byte-identical copies of the v1.5.4 G8 run's measurement and
#               audit modules (checked against that run's combined-files.sha256)
#   inputs/     held-out-inputs.json (585, sha 50b8b890...) and
#               full-candidate-inputs.json (1,920 rows, 1,708 admitted, sha 0309377d...)
#   binaries/   km-v1.5.5-rc-pgo-<sha>, km-v1.5.3-<sha> (release asset 2470b041...)
#   artifacts/  rc.json, v153.json, konclude.json (measurement inventories)
#   *.sbatch    with @ROOT@ filled in; run_release.py, run_konclude.py
#   files.sha256  checked by every task before it measures anything
# Only file copies and hashing run on the login node; nothing is measured there.
# Re-staging with a new RC replaces binaries/ entry, artifacts/rc.json and
# files.sha256; finished runs keep their own destination directories and
# record the inventory and binary hashes in every chunk.
set -euo pipefail
name=${1:?root name, e.g. v155-release-20261031}
rc=$(readlink -f "${2:?RC binary}")
receipt=$(readlink -f "${3:?RC native-build-receipt.json}")
here=$(cd "$(dirname "$0")" && pwd)
W=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work
V153_BIN=$W/v153-release-assets-b5abf83a/km-v1.5.3-linux-x86_64
V153_SHA=2470b0415f1a78533024e15b5c317f9e743a98916b597739db93b9452a8dd8d4
ROOT=/ibex/scratch/projects/c2014/hohndor/km/$name
G8=/ibex/scratch/projects/c2014/hohndor/km/v150-performance-20261005/g8-v154-80c8f82a
V153RUN=/ibex/scratch/projects/c2014/hohndor/km/v150-performance-20261005/recovery-v153-scoped-20261025
KONCLUDE=/ibex/scratch/hohndor/km/routing_20260715/konclude-oracle-builds/konclude-v0.7.0-1138-build-20260721-03/Konclude-build-a
KONCLUDE_SHA=e8dd5373d4606a1c9dbab0896b5939124ef7997781f15aea0d6f5fc6fd4cf0f4

rc_sha=$(sha256sum "$rc" | cut -d' ' -f1)
python3 - "$receipt" "$rc_sha" <<'PY'
import json, sys
r = json.load(open(sys.argv[1]))
assert r["binary_sha256"] == sys.argv[2], "RC binary is not the receipted PGO binary"
assert r.get("PGO") is True and all([int(x) for x in v.split(".")] <= [2, 34] for v in r["glibc_versions"])
PY
v153_sha=$(sha256sum "$V153_BIN" | cut -d' ' -f1)
[ "$v153_sha" = "$V153_SHA" ] || { echo "v1.5.3 release binary hash mismatch" >&2; exit 1; }
commit=$(python3 -c 'import json,sys;print(json.load(open(sys.argv[1]))["source_commit"])' "$receipt")
version=$(python3 -c 'import json,sys;print(json.load(open(sys.argv[1]))["version"])' "$receipt")

stage=$(mktemp -d "$W/agent-scratch/release-pipeline/stage.XXXXXX")
trap 'rm -rf "$stage"' EXIT
python3 - "$stage" "$ROOT" "$rc_sha" "$commit" "$version" "$receipt" "$KONCLUDE" "$KONCLUDE_SHA" <<'PY'
import json, sys
stage, root, rc_sha, commit, version, receipt, kpath, ksha = sys.argv[1:]
r = json.load(open(receipt))
flags = {"KM_HT_DDB": "1", "KM_HT_NATIVE_FULL": "1", "KM_CACHE_CONFORMANCE": "1",
         "KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE": "1", "KM_FAST_IRI_GRAMMAR": "1", "KM_JSON_GRAPH_EDGES": "1"}
json.dump({"artifacts": [{"id": "km", "version": f"v{version}-rc-pgo-{commit[:8]}",
                          "path": f"{root}/binaries/km-v{version}-rc-pgo-{rc_sha}", "sha256": rc_sha}],
           "flags": flags, "source_commit": commit, "source_manifest_sha256": r["source_manifest_sha256"],
           "profile_sha256": r["merged_profile_sha256"], "production_profile": True,
           "linker_wrapper": "cc-wrapper.sh (-Wl,--defsym=pidfd_spawnp=0 -Wl,--defsym=pidfd_getpid=0), as v1.5.3 and v1.5.4"},
          open(f"{stage}/rc.json", "w"), indent=2)
v153 = "2470b0415f1a78533024e15b5c317f9e743a98916b597739db93b9452a8dd8d4"
json.dump({"artifacts": [{"id": "km", "version": "1.5.3-pgo-3fd8d2be7810 (release asset km-v1.5.3-linux-x86_64)",
                          "path": f"{root}/binaries/km-v1.5.3-{v153}", "sha256": v153}],
           "flags": flags, "source_commit": "ecc4b1c57bc799bd8b2cf501fb5c2921607d9051",
           "source_manifest_sha256": "0b3eede3712ccad7db1bd9d042f91d2d9791708e57f4466967bb8522d76464f2",
           "profile_sha256": "63c8227e30b6008625bacce2e2ff2e6986a1c124e7bba702f993e4b9019f745b", "production_profile": True},
          open(f"{stage}/v153.json", "w"), indent=2)
json.dump({"artifacts": [{"id": "konclude", "version": "v0.7.0-1138 / source 0002e8063540; embedded banner 500e11d9",
                          "path": kpath, "sha256": ksha}],
           "flags": {}, "settings": "as classification-konclude-53201252 (2026-10-04): classification -w 1 -v, OWL/XML input, one core, 240 s, 20 GiB"},
          open(f"{stage}/konclude.json", "w"), indent=2)
PY
for f in "$here"/ibex/*.sbatch; do sed "s#@ROOT@#$ROOT#g" "$f" > "$stage/$(basename "$f")"; done

ssh ibex "mkdir -p $ROOT/protocol $ROOT/inputs $ROOT/artifacts $ROOT/binaries $ROOT/slurm $ROOT/tmp"
ssh ibex "test -f $ROOT/binaries/km-v1.5.3-$V153_SHA" || scp -q "$V153_BIN" "ibex:$ROOT/binaries/km-v1.5.3-$V153_SHA"
ssh ibex "test -f $ROOT/binaries/km-v$version-rc-pgo-$rc_sha" || scp -q "$rc" "ibex:$ROOT/binaries/km-v$version-rc-pgo-$rc_sha"
scp -q "$here/ibex/run_release.py" "$here/ibex/run_konclude.py" "$stage"/*.sbatch "ibex:$ROOT/"
scp -q "$here/ibex/smoke-inputs.txt" "ibex:$ROOT/inputs/"
scp -q "$stage/rc.json" "$stage/v153.json" "$stage/konclude.json" "ibex:$ROOT/artifacts/"
ssh ibex "bash -s" <<EOF
set -euo pipefail
cd $ROOT
chmod 555 binaries/*
for f in canonicalize.py taxonomy.py compare_taxonomies.py full_iri_fingerprint.py measure_classification.py tree_watchdog.py scoped_snapshot.py timing_support.py; do
  want=\$(grep "  \$f\$" $G8/combined-files.sha256 | cut -d' ' -f1)
  [ -n "\$want" ] || want=\$(sha256sum $G8/\$f | cut -d' ' -f1)   # tree_watchdog.py is not in that list
  cp $G8/\$f protocol/\$f
  [ "\$(sha256sum protocol/\$f | cut -d' ' -f1)" = "\$want" ] || { echo "protocol module \$f differs" >&2; exit 1; }
done
cp $G8/held-out-inputs.json inputs/
cp $V153RUN/full-candidate-inputs.json inputs/
echo "50b8b890aeeb4f1828edf5ec8c7cd2cd32b2a6861b9933f3590006b4abce328e  inputs/held-out-inputs.json" | sha256sum --quiet -c
echo "0309377d05dfd0cd81eb46050416272fbd52b16e77f21d9a37d732b352817fb4  inputs/full-candidate-inputs.json" | sha256sum --quiet -c
echo "$rc_sha  binaries/km-v$version-rc-pgo-$rc_sha" | sha256sum --quiet -c
echo "$V153_SHA  binaries/km-v1.5.3-$V153_SHA" | sha256sum --quiet -c
echo "$KONCLUDE_SHA  $KONCLUDE" | sha256sum --quiet -c
test -d $(dirname $KONCLUDE)/runtime-lib
sha256sum protocol/*.py run_release.py run_konclude.py *.sbatch inputs/*.json inputs/smoke-inputs.txt artifacts/*.json binaries/km-v1.5.3-$V153_SHA binaries/km-v$version-rc-pgo-$rc_sha $KONCLUDE > files.sha256
sha256sum --quiet -c files.sha256
echo "STAGED $ROOT rc=$rc_sha"
EOF
