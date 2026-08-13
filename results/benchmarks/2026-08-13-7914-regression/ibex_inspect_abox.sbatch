#!/bin/bash
#SBATCH --job-name=km-7914-abox-inspect
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --cpus-per-task=2
#SBATCH --mem=24G
#SBATCH --time=00:20:00
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/candidate-0289812-singleton-abox-20260813/inspect-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/candidate-0289812-singleton-abox-20260813
binary=$root/km
expected=$(cut -d' ' -f1 "$root/km.sha256")
[[ $(sha256sum "$binary" | cut -d' ' -f1) == "$expected" ]]
ont=/ibex/scratch/hohndor/km/corpus/ore_ont_7914.owl
tmp=${SLURM_TMPDIR:-$root}/7914.frontend.json
"$binary" ofn "$ont" > "$tmp"
/usr/bin/jq 'def kind: if type == "object" then (keys|sort|join("+")) else type end;
  .nominal_abox as $a |
  {complete:$a.complete,
   individuals:($a.individuals|length),
   same:($a.same|length), different:($a.different|length),
   roles:($a.role_assertions|length), negative_roles:($a.negative_role_assertions|length),
   unsupported:($a.unsupported|length),
   assertion_count_hist:([$a.individuals[].assertions|length]|group_by(.)|map({count:.[0],individuals:length})),
   assertion_kind_hist:([$a.individuals[].assertions[]|kind]|group_by(.)|map({kind:.[0],count:length})),
   marker_count_hist:([$a.individuals[].assertion_markers|length]|group_by(.)|map({count:.[0],individuals:length})),
   proxy_count_hist:([$a.individuals[].proxies|length]|group_by(.)|map({count:.[0],individuals:length})),
   samples:([$a.individuals[]|{individual,assertions,assertion_markers,proxies}][0:8]),
   clauses:(.clauses|length), concepts:(.named|length), source_axioms:(.source_axioms|length)}' "$tmp"
echo INSPECT_COMPLETE binary_sha256=$expected bytes=$(stat -c %s "$tmp")
