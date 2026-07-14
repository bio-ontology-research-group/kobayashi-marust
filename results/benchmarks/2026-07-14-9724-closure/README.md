# ore_ont_9724 closure and 592-ontology regression sweep

Status: complete. This directory records the KM/Konclude comparison, the
performance diagnosis, the exact intrusive-free-list port, the production
closure run, and the complete IBEX ORE regression sweep for `ore_ont_9724`.

The final binary was built on `ws` with Rust 1.85 in the Bullseye container.
Its SHA-256 is
`8071a4d0d7b35476f8c4d65a749e8fef71279e23dedd1ade4aba405f327078f9`.
The release suite passes 1,475 tests, with zero failures and 7 ignored tests.

## Production closure

The preceding 9663 binary returned a sound partial taxonomy with 3,325 missing
pairs. Extending the standalone saturation budget from 220 seconds to 1,200
seconds recovered only one pair and raised peak RSS above the ORE limit. The
problem was therefore not a small timeout margin.

| IBEX job | Binary/stage | Result | Missing | Wall | Peak RSS |
|---|---|---|---:|---:|---:|
| 48797888 | instrumented Konclude, one worker | reference | 0 | 10.46 s | 2,794,412 KB |
| 48797840 | preceding KM, standalone saturation | incomplete | 3,325 | 3:45.78 | 1,159,276 KB |
| 48797757 | preceding KM, 1,200-second saturation | incomplete | 3,324 | 20:05.75 | 24,555,236 KB |
| 48798030 | cursor/hash candidate | incomplete | 3,325 | 4:01.71 | 979,592 KB |
| 48798075 | final fix, exact normalized input | exact match | 0 | 32.15 s | 8,096,324 KB |
| 48798145 | final `km classify`, original OWL | exact match | 0 | 24.72 s | 8,091,788 KB |
| 48799766_350 | final full-sweep task | exact match | 0 | 23 s | 8,092,216 KB |

Production job 48798145 emitted 457,090 canonical non-self pairs, exactly the
457,090 pairs in the stored Konclude signature. The comparator reported zero
extra and zero missing pairs. Saturation itself took 20.39 seconds, answered
all 23,136 queried subjects, and left no completion residue.

## Precise diagnosis against Konclude

Instrumented Konclude with a single worker completed in 10.46 seconds, so
parallel scheduling was not the explanation. It built 33,422 saturation items
and performed 6,853,425 concept-add attempts. KM built a close 33,678 seeds,
but remained in the saturation outer queue after 220 seconds and after 1,200
seconds. This ruled out the original ATMOST/cardinality hypothesis for the
closure blocker and localized the problem to saturation implementation cost.

The first faithful alignment candidate removed three measurable differences:

1. `CImplicationReapplyConceptSaturationDescriptor` now holds a non-owning
   operand cursor, represented by an index, instead of cloning the remaining
   operand suffix into every descriptor. Initial implication application uses
   a stack-local cursor, matching Konclude's stack-local temporary descriptor.
2. Role-pointer hash buckets use the existing integer hasher, matching Qt's
   pointer-as-integer hash path, and backward-link installation mutates one
   bucket rather than repeatedly looking it up.
3. Local status-propagation stacks use tail-backed `push`/`pop`, preserving the
   intrusive newest-first LIFO order without front shifts.

That candidate reduced peak memory but still timed out with exactly 3,325
missing pairs. Four independent live stack samples at 30, 90, 160, and 220
seconds then caught the same worker stack:

```text
__memcpy_evex_unaligned_erms
release_role_saturation_process_linker
process_successor_functional_concepts_extensions
run_saturation_on
```

The repeated sample identified the decisive representation mismatch.
Konclude's `CProcessingDataBox.cpp:1849-1869` stores
`mRemRoleSatProcessLinker` as an intrusive free list. Release clears the
linker's next pointer and prepends it with `append(oldHead)`; acquire removes
the head and advances to `head->getNext()`. Both operations are constant time
and the reuse order is LIFO. KM had collapsed that list to a `Vec`, placed the
head at index zero, and implemented the same logical order with `insert(0, x)`
and `remove(0)`. Every release/acquire shifted the growing vector through
`memcpy`, making the hot functional-successor path quadratic.

## Exact targeted port

The collapsed `mRemaining*` allocation free lists now store their logical head
at the `Vec` tail. Konclude's prepend/head-pop pair becomes Rust `push`/`pop`,
which is constant time and retains the exact LIFO reuse order. Diagnostic
getters reverse the internal vector so their observable head-to-tail view also
matches C++. Ordinary live chains that are traversed remain in their original
head-to-tail representation.

The same representation invariant is applied to all adjacent saturation free
lists with the same Konclude constructor pattern: role saturation process
linkers, concept descriptors, concept saturation descriptors, individual
status-update linkers, and individual saturation-node linkers. A production
test releases two role linkers, verifies the Konclude head-to-tail order, then
verifies that acquire returns the second release followed by the first.

The fix changes allocation bookkeeping and enumeration cost, not rule
derivations or saturation order. The cursor, integer hash, consolidated bucket
access, and tail-backed LIFO stacks preserve the same keys, links, and
processing order. No CB-calculus rule changes, so Lean re-certification is not
required.

## Full 592-ontology IBEX regression gate

IBEX array job 48799766 ran every ORE pool ontology with the same final binary,
a 240-second reasoner cap, 20 GB memory, and the same production flags as the
preceding 9663 sweep. Every result row records the final binary SHA-256.

| Metric | 9663 baseline | 9724 closure |
|---|---:|---:|
| completed | 574 | 574 |
| timeout | 18 | 18 |
| exact Konclude match | 511 | 514 |
| incomplete | 48 | 45 |
| unsound | 5 | 5 |
| both-disagree | 1 | 1 |
| inconsistent | 6 | 6 |
| no gold | 3 | 3 |

No previously exact ontology regressed. Exactly three signatures changed, all
from sound incomplete results to exact matches:

- `ore_ont_1016.owl`: 2,510 missing to zero;
- `ore_ont_11623.owl`: 3,423 missing to zero;
- `ore_ont_9724.owl`: 3,325 missing to zero.

## Reproduction artifacts

- `ibex_9724_standalone_bridge.sbatch` and
  `ibex_9724_long_baseline.sbatch` reproduce the fixed-budget and 1,200-second
  baselines on the exact normalized input.
- `konclude-9724-seed-instrumentation.patch`,
  `ibex_9724_konclude_build.sbatch`, and
  `ibex_9724_konclude_one_worker.sbatch` reproduce the single-worker Konclude
  seed and saturation counts.
- `ibex_9724_callgrind.sbatch` and
  `ibex_9724_eustack_samples.sbatch` reproduce the profile and the decisive
  live stacks.
- `ibex_9724_cursor_candidate.sbatch` records the exact but insufficient first
  alignment candidate.
- `ibex_9724_freelist_candidate.sbatch` and
  `ibex_9724_production_gate.sbatch` prove the normalized-input and original-OWL
  closure.
- `ibex_9724_fullsweep.sbatch`, `compare_sweeps.py`, and
  `sweep-comparison.txt` reproduce and summarize the complete corpus gate.

The full causal account and C++ source correspondence are also recorded in
`docs/SOLVE-7914-9663-9724.md`.
