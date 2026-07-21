# Targeted validation status for ORE 4669 and 10621

This is an append-only audit of the two repair targets. A completed process is
not a solve claim. A solve requires a source-bound, twice-built executable, an
observed exact route, completion within 240 seconds and 20 GiB, and exact
full-IRI agreement with the independent reference.

Historical and superseded executables are provenance only. They cannot close
an ontology in the reproduced route ledger.

## Reproducible capsules

| Capsule | KM SHA-256 | Source archive SHA-256 | Source manifest SHA-256 | Receipt SHA-256 | Disposition |
|---|---|---|---|---|---|
| `km-final-20260721-01` | `799937b908a535f705123ed647e883c3d3dceb5be4be8e479fc9c68b7b3c5163` | `6f4d0b5f22ee2b5ffcce1e16fe8dc455ce0865a32b276a0b1221522670a1a032` | `455c226a605fdb3520b67b3c032a4fc70c8cd137ce9f6267813d97e63bc765cc` | `d57176ed43186df62ca6aedb2a4bded787bd3c81bceafbff778e0e0781f43673` | Superseded after its 10621 certificate declined. Retained as negative evidence only. |
| `km-final-20260721-02` | `791baa14c898b87ae9b9ecc7853bcdda1617aefcdcfc480071642a605c4f0411` | `74cb2cc53d83755d68d2232618ad2b9e3ab659ee1418787fb078da6117c47b00` | `0ba6d578a0af58c0b45e8980fb274d4c8cd5f12993f5526cbf21a924cb458e2b` | `1ebf980a961d65a0262b6e19d43164545849b816b2a74596d8fecdf378575529` | Superseded after its targeted 10621 certificate and direct trace both declined. Retained as negative evidence only. |
| `km-final-20260721-03` | `51443f579ebd1cf395efd9c4a412c557546619f512c00a2d1b84e5181986ff9c` | `88de74d06af57ecd0f9bf14345bb5837419b94af796526575c480f3ce347557a` | `9271d6362946ca3f4abf3c2b95183c63db4d9468f2667e2d9348a1c730c4bcfe` | Not promoted | Rejected during receipt review. The two binaries were byte-identical, but hashes of rustup dispatcher symlinks were mislabeled as the resolved compiler and Cargo hashes. No validation used this capsule. |
| `km-final-20260721-04` | `51443f579ebd1cf395efd9c4a412c557546619f512c00a2d1b84e5181986ff9c` | `88de74d06af57ecd0f9bf14345bb5837419b94af796526575c480f3ce347557a` | `9271d6362946ca3f4abf3c2b95183c63db4d9468f2667e2d9348a1c730c4bcfe` | `8e71143d381f4abcf5698bb06d8df71f9d60d50260781de82346ac1c55e16603` | Accepted provenance artifact for the first batching candidate, not a solve claim. Two offline builds are byte-identical; the corrected receipt records distinct resolved `rustc`, `cargo` and rustup dispatcher paths and hashes. The clean 20-file IBEX relay is `reproducible-current-20260721-04-core`, with full sorted file/hash-stream digest `9c5a6eadd1247831870a7a497d1c7ae565fbfc64af188262ee9f6a9a9e923222`. |
| `reproducible-current-20260721-05-core` | `7f5e39ac7e989ca7f029090d051f009a8b2f2da5d410aeccc376d9630143c0bf` | `91150f63f596e188ceae6a55f19acd0a5a9521f059cc86f0d3dc0dfee4c85f52` | `d5713b963d98f420939bf3843059e9edcbe06fd8c008536fee1e98202a7bf86e` | `841155050f7214e88d06b64f27258a66631eeaaf4ca0f6d3949ca10bb95dca0a` | Earlier accepted provenance artifact, not a solve claim. The two locked, offline builds are byte-identical. The 20-file core has sorted file/hash-stream digest `91cb83f716474e4c7c775f3eefa01f5c5fea5f3cce4cf65ef8faf659285af638`; its 4,234-file vendored build-input manifest has SHA-256 `5db9089f5663288b3b4ba1ca603e45fa7c144f2b885af1d455c7853b387aaea4`. |
| `reproducible-current-20260721-10-core` | `e8817734877911a45320830324cefdfb1002b411896f5b7982deab31673f6b30` | `369a6e975936caf75e664b528ce6c53f1d1480f4be20595498d1b2dfb6165349` | `4f52e2b8d587f729fb9f84354e8fe1cc5ebb372e6f27b6b109dfea1f8a737794` | `c1ee3dced72ad60757befb820b86f28419e04f9326f19a22193c9aa8635b5fda` | Current accepted capsule for route confirmation. Two clean, locked, offline builds are byte-identical. The complete 1,672-test suite passes, and the six-file IBEX runtime closure has manifest SHA-256 `ed5f9de424e1d4140197ade2bceaf0f7c9da2bb6399ce75522d091ba966695d5`. |

The reproducible capsules use the amd64 OCI manifest
`rust@sha256:646e8ceea789b00c5cfa339816a3ed44940dbf1651dc167b78f3c0aefcae0025`,
Rust 1.95.0 commit `59807616e1fa2540724bfbac14d7976d7e4a3860`,
locked vendored dependencies, four build jobs and disabled build networking.
The two validation scripts copied into the non-core `-04` directory after the
build are recorded separately in `CAPSULE-EXTRA-ARTIFACTS.tsv`; they are not
receipt-bound build inputs. Current validation starts from `-05-core` and stages
drivers outside the capsule root.

## ORE 10621

| Slurm job | Capsule | Exact request | Result | Wall | Peak RSS | Claim |
|---|---|---|---|---:|---:|---|
| `49203049` | `km-final-20260721-01` | `elc_cert`, 32 broad cover models | Exit 3, certificate declined | 113.03 s | 2,705,072 KiB | Open; no taxonomy emitted. |
| `49204617` | `km-final-20260721-02` | `elc_cert`, 2 broad models, 32 targeted models, 64 target restarts | Exit 3, certificate declined | 158.94 s | 2,705,776 KiB | Open; no taxonomy emitted. |
| `49204678` | `km-final-20260721-02` | Direct `km elc` trace of the same controls | Worker exit 3, trace job completed | 172.38 s | 2,706,780 KiB | Diagnostic only; `acceptance_evidence=false`. |
| `49207555` | `km-final-20260721-04` | `elc_cert`, 2 broad models, 32 targeted models, 64 target restarts | Exit 3, certificate declined | 162.93 s | 2,705,576 KiB | Open; provenance and Konclude-oracle gates passed, but no taxonomy was emitted. |
| `49207556` | `km-final-20260721-04` | Accidental duplicate of `49207555` | Cancelled by exact job ID after 20 s | 20.00 s | Not recorded | Not evidence. See `CANCELLED-RUNS.tsv`; `km.json` and `km.time` remained empty. |
| `49209225` | `km-final-20260721-04` | Direct `km elc` batching trace with the same search controls and `KM_ELC_DEBUG_ITEMS=0` | Worker exit 3; trace job completed | 180.78 s | 2,705,752 KiB | Diagnostic only; `acceptance_evidence=false`. |
| `49211457` | `reproducible-current-20260721-05-core` | Fresh same-job Konclude followed by `elc_cert`, 2 broad models, 32 targeted models, 64 target restarts | Launcher exit 1 before run-root creation | 1.00 s | 2,096 KiB | Rejected launcher; neither Konclude nor KM ran, so this is not route evidence. |
| `49211481` | `reproducible-current-20260721-05-core` | Fresh same-job Konclude followed by `elc_cert`, 2 broad models, 32 targeted models, 64 target restarts | Fresh Konclude exit 127 before KM | 4.00 s | 78,048 KiB | Rejected runtime launcher; all capsule, receipt and retained-oracle gates passed, but neither taxonomy nor KM result exists. |
| `49211607` | `reproducible-current-20260721-05-core` | Fresh same-job Konclude followed by `elc_cert`, 2 broad models, 32 targeted models, 64 target restarts | KM exit 3, certificate declined | 160.11 s KM; 182 s allocation | 2,706,452 KiB KM; 3,294,216 KiB batch | Decisive negative evidence. Every provenance, runtime and fresh-oracle gate passed, but KM emitted no taxonomy. ORE 10621 remains open. |
| `49212075` | `reproducible-current-20260721-05-core` | Direct `km elc` trace with certificate 2, 2 broad models, 32 targets, 64 target restarts, debug enabled and zero item dumps | Worker exit 3; trace job completed | 156.49 s ELC; 167 s allocation | 2,706,276 KiB ELC; 2,776,080 KiB batch | Diagnostic negative evidence. The local-dead tier enlarged only passes 1011 and 1012; the residue remained unchanged and no taxonomy was accepted. |
| `49212699` | `reproducible-current-20260721-05-core` | Isolated `ht_bridge` eligibility trace with TInput, bridge-progress and unsupported-fence diagnostics under a hard 30-second worker cap | Route exit 3 before worker spawn; 1 unsupported fence | 5.62 s route | 699,736 KiB | Diagnostic only; `acceptance_evidence=false`. The only pre-worker blocker was `85 nominal(s) together with inverse roles`; no taxonomy was emitted and ORE 10621 remains open. |
| `49245587_389` | `reproducible-current-20260721-10-core` | `KM_ROUTE=ht_bridge`, fresh source-built Konclude and full-IRI fingerprinting | Exact full-IRI taxonomy equality | 118.2149 s | 1096.54 MiB | **Closed.** Route trace was exactly `ht_bridge`; both taxonomies have 70,827 subsumptions and 33,433 unsatisfiable named classes, with taxonomy SHA-256 `066b41b5f3e845110eceb3607b050627da744968ccef1ceafed50e3c3ea4468e`. |

The final source-bound replay supersedes the earlier negative diagnostics. Its
record is
`/ibex/scratch/hohndor/km/routing_20260715/source-bound-selected-49245587/results/ore_ont_10621.owl.json`
with SHA-256
`9b650e32198269399fdfba3b83169fd95d39f03a4a6bd3978a7565a7eeabbe8e`.
It binds ontology SHA-256
`5d6abde6b2f6e9ebc5c7161c524178749fb165d1885babfb01ce13a997308167`,
route-specification SHA-256
`4fbbaad3552b2581bdf25aab067c2461710008d22160203e5ba8beb2913ac1be`,
the capsule source, build and runtime identities, one matching runtime trace,
the 240-second and 20-GiB limits, and a fresh source-built Konclude reference.
The earlier failures remain useful mechanism diagnostics, but they no longer
describe the final implementation.

Job `49211457` exposed a path-spelling defect in the immutable-driver gate.
Slurm reported `SLURM_SUBMIT_DIR` through `/ibex/user/hohndor/km/...`, while the
driver required the equivalent `/ibex/scratch/hohndor/km/...` spelling. The
driver with SHA-256
`17f118569c55b141f01e17a9e94f36a1ea2d85df812c3c31e0ef685f75e8af7a`
therefore stopped before creating a run root or reading either reasoner binary;
its Slurm output was empty, with SHA-256
`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
The replacement driver, SHA-256
`bdd7dbcdbba4126017db895b3a2e59cb0875d24c305b70ec87cf6065c0e0b778`,
canonicalizes both directory spellings with `readlink -f` before equality while
retaining the hash-named basename and exact script-hash gates. This launcher
failure is neither positive nor negative evidence about the route.

Job `49211481` confirmed that the canonical-path fix passed and that all pinned
capsule, receipt, core and retained-oracle gates succeeded. The fresh Konclude
process then returned 127 because its scrubbed environment could not locate
`libpcre.so.3`; stderr has SHA-256
`99d5016e42057bfad69568ac50edb2fd719a8177eba38127e3a56d9d3b0abf4f`.
The run stopped before KM, so it is also not route evidence. The replacement
driver, SHA-256
`677e97322c84d97f9f8cf70cbf7ee129589ad4bb31559f3ab10c73ebaabcca42`,
pins `/ibex/scratch/hohndor/km/libpcre.so.3` to SHA-256
`18a3afc32488c647144f659d1629604df7ff58482a5734626dac65bd35eba8bd`
and binds the sorted 12-library runtime hash stream to SHA-256
`a65425061780e34dff5f6a460681d4599d1098906dc5b03be0ef43699406e898`.
It supplies that exact library directory only to fresh Konclude; KM retains its
scrubbed environment without `LD_LIBRARY_PATH`.

Job `49211607` then exercised the complete decisive driver. Fresh Konclude
finished successfully and reproduced the retained canonical taxonomy with
70,827 subsumptions, 33,433 unsatisfiable named classes, 8,209 nonempty left
classes, 8,215 components and 41,647 declarations. Every source, capsule,
receipt, runtime-library and route-precondition gate passed. KM nevertheless
returned 3 after 160.11 seconds and 2,706,452 KiB peak RSS, emitted no taxonomy,
and reported that the ontology remained outside the selected EL completion
fragment. This is valid negative evidence for the local-dead batching tier;
10621 remains open.

For all 10621 reasoner or diagnostic executions through job `49209225`, the
ontology hash was
`5d6abde6b2f6e9ebc5c7161c524178749fb165d1885babfb01ce13a997308167`.
The fresh Konclude fingerprint and its original 240-second/20-GiB run record
passed every provenance check. `KM_ELC_DIAGNOSTIC_LOWER` was absent from every
decisive run. Job `49207555` additionally parsed and checked the complete
corrected build receipt before KM started.

The current mechanism remains fail-closed. Model-search choices can only find
candidate interpretations. Every admitted interpretation is re-closed under
the EL rules, checked against every residual clause, and required to keep top
non-bottom. The final certificate also requires a live witness for every
base-satisfiable named class and an empty intersection of extra named labels.
The acceptance failures mean that the bounded search has not met those
conditions; they do not support a 10621 solve claim.

The direct trace identifies the search failure precisely. Each of the first two
checked models kept 845 of 8,221 base-alive named witnesses, leaving 7,376
unwitnessed classes and 29 nonempty extra-label intersections. The first
target, `Part_of_peripheral_doublet_microtubule_of_axoneme_of_cilium`, is
satisfiable according to the pinned Konclude reference. Nevertheless, 64
target restarts banned only one different repair choice apiece and never
reached a model that kept this witness alive. This supports a search-scheduling
change, not relaxation of the certificate conditions.

Job `49209225` shows what the first batching change achieved and what remains.
The first 11 protected-target attempts returned causal multi-choice batches of
328, 177, 140, 64, 45, 42, 10, 11, 10, 5 and 6 choices, eliminating 838 choices
in those batches. The remaining 53 attempts each returned a different
singleton fallback, for 891 exclusions across all 64 attempts. No targeted
model was admitted, and the final residue stayed at 7,376 unwitnessed classes
and 29 intersections. This is non-acceptance diagnostic evidence. It motivates
the next search-only tier, which batches choices on locally newly-bottom nodes
inside the protected forward cone before using the singleton fallback. The
tier changes only bounded candidate search; complete model admission and the
fail-closed sandwich test remain unchanged. Its focused ws suite passed 28/28
tests. Job `49211607` then tested the tier decisively and still declined, so the
next diagnostic must measure which batching tiers fire before any further
search-only change.

Job `49212075` supplied that measurement. Relative to the exact capsule-04
baseline, passes 1000 through 1010 retained batch sizes 328, 177, 140, 64, 45,
42, 10, 11, 10, 5 and 6. Former singleton passes 1011 and 1012 became batches
of 166 and 99 choices, while passes 1013 through 1063 remained singleton-sized.
The two broad models still covered only 845 base-alive witnesses apiece, and the
final residue stayed at 7,376 unwitnessed classes and 29 undetermined pairs.
No targeted model was admitted. Repeated first-conflict node IDs were limited
to 121584 (three events) and 121600, 121612, 121734 and 17399 (two each), which
is only a proxy for canonical-witness sharing because the trace exposes the
first tuple rather than every choice in a batch. Direct ELC took 156.49 seconds
and 2,706,276 KiB peak RSS. The summary has SHA-256
`ddfcaae29d5a336a69ac9a1bfbfc1d02b6cb5343dfca5e23dc1f46ac1a3b4307`;
the Slurm stdout has SHA-256
`6b1091f731a032a544b31ef7ebe2b91c6f991a02597aaf555b83220616b9c24b`.
This confirms that the local-dead tier executes but does not address the
mechanism blocking target 3. ORE 10621 remains open.

Job `49212699` then tested whether the existing source-faithful hypertableau
bridge could provide a different exact route. The executed driver has SHA-256
`3a926938bdd67b789a24eeb8a7abded14a4152c6fbc3e0394a1bd1aae8766037`;
its run root is
`/ibex/scratch/hohndor/km/routing_20260715/10621-ht-bridge-05-49212699`.
All capsule, receipt, core, self-hash and ontology gates passed. The conversion
reported 247,721 clauses, 122,850 source axioms, 81,787 concepts, 41,647
queries, 56 role domains, 89 role ranges, inverse roles and number
restrictions. It recorded 120 fence entries: 119 were allowed by the existing
source-mode/inverse policy, while the single unsupported fence was
`nominal+inverse(SHOI/SHOIQ)`, with detail `85 nominal(s) together with inverse
roles`. The detailed source fences show that these are genuine TBox/RBox
nominals: several object-property ranges contain explicit `ObjectOneOf`
enumerations, including `AP_Position`, `Ion`, `Language`, `Rank_of_tissue`, and
`Term_status`. The older source-profile row reports zero `source.nominals`, but
that counter does not expose these role-domain/range-conditional nominals and
cannot be used as an ABox-origin certificate. The ABox independently contains
85 `ClassAssertion` axioms and one `DifferentIndividuals` axiom over the same
85 individuals. The final TInput reported zero dropped clauses and zero
admitted nominals because the converter clears the nominal IDs after recording
this conservative fence.

The route returned 3 before it spawned the bridge worker. Consequently there
are no bridge or source-classifier statistics and no taxonomy to compare. This
is precise non-acceptance diagnostic evidence, not a solve claim. A safe repair
must either implement the missing source-nominal-plus-inverse mechanism or
prove that every nominal-valued source range is irrelevant before pruning it;
globally allowing nominal-plus-inverse inputs would weaken a soundness fence.
ORE 10621 remains open.

Read-only follow-up audit job `49213221` parsed the saved TInput on one IBEX
compute core; it did not invoke KM or any reasoner and is not acceptance
evidence. It completed successfully in three seconds. The audit found that all
85 nominal proxy concepts correspond to 85 distinct `Nominal` values in the
normalized source TBox, with no name missing on either side. Those values occur
6,546 times across 6,480 source axioms, and 279 normalized clauses reference a
nominal proxy. The source nominals are therefore pervasive, not an ABox-only
artifact or a small removable range tail. The audit script has SHA-256
`d4d6eac7dfc418aab28348bf0c1b004f6a7008d8e8b0a5cf3b9a7291b96fc209`;
its JSON report has SHA-256
`5b0b0661b4a1f9ed1a73fc167a830569d7efe095228242f3a37fcfba93626433`.

## ORE 4669

| Slurm job | Validation route | Result | Resource observation | Disposition |
|---|---|---|---|---|
| `49201390` | First modal helper oracle with optional ELK planning | Cancelled before a decisive oracle | 87,903,940 KiB maximum RSS; an accidentally repeated diagnostic reached 11,739,349,401 bytes | Invalid validation implementation; artifacts retained only to explain the failure. |
| `49203175` | Normalized modal planner, 20,000-helper guard | Failed closed at 24,299 candidates | 4,400,420 KiB Slurm maximum RSS | Guard was too small; no KM run. |
| `49203303` | Preliminary count pass, 100,000-helper guard | Failed closed at 102,111 candidates | 1,847,616 KiB planner peak | Proved that a small materialized helper set was not complete. |
| `49203951` | True 64-bit count-only enumeration | Count completed | 1,349,337,472 helpers: 83,691,254 group plus 1,265,646,218 member; 3,643,584 KiB planner peak | Exhaustive helper materialization rejected as impractical; no KM run. |
| `49204676` | Complete positive-proxy oracle | Failed closed in HermiT hierarchy precomputation | Exit `124:0` after `01:30:07`; 30,068,520 KiB maximum RSS; no semantic oracle artifact | Monolithic hierarchy precomputation rejected; no Konclude, ELK, checker, or KM run. |

The count-only result prevents a misleading resource increase: the full helper
route is not a practical independent oracle. Job `49204676` tested the private
complement projection, but HermiT never returned from the explicit
`CLASS_HIERARCHY` precomputation before its 5,400-second command timeout. The
job produced no witness TSV, disjointness TSV or summary, positive taxonomy,
reconstructed taxonomy, or oracle report. Its projected ontology and mapping
are structural evidence only.

The replacement implementation keeps each actual filler fixed and directly
queries HermiT on anonymous filler/profile intersections using the certified
`part_of` role, without hierarchy precomputation. Its fail-closed
root-amalgamation certificate records the exposed role-closure cardinalities,
rejects a strict transitive exposed superproperty, independently scans every
successor-rule direction, and rejects generated aliases that collide with
source IRIs. The 2,109 may-states remain candidate compression only; no
semantic verdict transfers between fillers. Candidate covers must be
upward-closed before UNSAT propagation.

Java replays each fresh or resumed checkpoint. The separate Python finalizer
independently recomputes every query expression hash, propagation set,
accumulator, and total partition. It also verifies pinned Java/HermiT artifacts,
the exact command, `scontrol` allocation, GNU-time result, chain digest, six
source-disjointness controls, 64 known-SAT controls, and the retained bounded
HermiT/Konclude controls. The first 64-proxy array is a resource pilot; the
driver rejects full-oracle mode and cannot close 4669. No pilot has been staged
or submitted yet.

At the time of the original entry, both targets were open. The later
source-bound replay above closes 10621. ORE 4669 remains open.
