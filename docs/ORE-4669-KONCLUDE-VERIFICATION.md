# ORE 4669: Konclude verification and port gate

## Outcome

Konclude does not currently provide a verified solve route for
`ore_ont_4669.owl`. A reproducible source build of upstream Konclude timed out
under the standard 240-second, 20-GiB contract and again after 3,600 seconds
with a 90-GiB process limit. Neither run produced a taxonomy. The premise that
Konclude solves this ontology is therefore false for the tested upstream
release and command.

This result blocks a direct method-for-method port. KM must retain its
fail-closed inverse negative-existential mirror gate until a sound and complete
route has an authoritative full-IRI reference. Removing the gate would restore
an output already refuted by targeted HermiT checks.

## Exact source and build identity

The tested upstream source was Konclude tag `v0.7.0-1138`, Git commit
`0002e80635403960a7df5d93bd0e8f994d4952d0`.

| Artifact | SHA-256 |
|---|---|
| Source archive | `936b65796da3209eed83d90264614067bd7d8f03133d089a64dd8bea9618076f` |
| Source-file manifest | `a188a16ac440259e58c289ea766cd457a402e7c85ceb6c3e5b11a7ca08b116d2` |
| Build receipt | `e79b9ef8fe8b46122bb04e6749a876c4500da813f19795fbe888192ec1566651` |
| `Konclude-build-a` | `e8dd5373d4606a1c9dbab0896b5939124ef7997781f15aea0d6f5fc6fd4cf0f4` |
| `Konclude-build-b` | `e8dd5373d4606a1c9dbab0896b5939124ef7997781f15aea0d6f5fc6fd4cf0f4` |
| ORE ontology | `2b15dc9535ed50c4dc9eae05067df4e6525b69c7bf1913192715b79ad550b3eb` |

The two clean, sequential, offline source builds are byte-identical. The IBEX
build capsule is:

```text
/ibex/scratch/hohndor/km/routing_20260715/konclude-oracle-builds/
  konclude-v0.7.0-1138-build-20260721-03/
```

## Runtime verification

The standard invocation was:

```text
Konclude-build-a classification -w 16 -v \
  -i ore_ont_4669.owl -o taxonomy.owl
```

| Binary | Workers | Limit | Result | Wall | Reported peak MB | Taxonomy |
|---|---:|---:|---|---:|---:|---|
| Reproducible source build | 16 | 240 s / 20 GiB | timeout | 240.0123 s | 3,849.97 | none |
| Reproducible source build | 8 | 3,600 s / 90 GiB | timeout | 3,600.0517 s | 53,014.13 | none |
| Earlier official binary, corroboration only | 16 | 1,800 s / 60 GiB | timeout | 1,800.0173 s | 51,484.81 | none |

The standard result is the `konclude` row in run root
`/ibex/scratch/hohndor/km/full-panel-20260722/runs/49290191`, Slurm task
`49293176_157`. The extended source-built result is:

```text
/ibex/scratch/hohndor/km/routing_20260715/
  4669-source-konclude-49241765-3/PROBE.json
```

The corroborating official-binary record is:

```text
/ibex/scratch/hohndor/km/routing_20260715/4669-fix-20260718/
  results/konclude_long_4669/run.json
```

Since no Konclude run returned a taxonomy, there is no Konclude full-IRI result
to compare against KM or the retained satisfiability witnesses.

## What upstream Konclude actually does

The clean upstream source contains no specialized closure for the dominant
mirror pattern in this ontology. The source audit found 36,495 private classes
with definitions of the form:

```text
N_F ≡ ¬∃R.F
```

The relevant upstream path is:

1. `CConcreteOntologyUpdateBuilder.cpp` creates the named definition as a
   `CCEQ` concept. See `buildClassConcept`,
   `buildPermutableConceptEquivalentClass`, and
   `buildConceptEquivalentClass` near lines 1353, 1900, and 1926.
2. `CLexicalNormalisationPreProcess.cpp` lines 93-96 rewrites `CCSOME` to
   `CCALL`, sets mapping negation, and flips operand polarity. The mirror is
   represented as the positive universal definition `N_F ≡ ∀R.¬F`.
3. `CTriggeredImplicationBinaryAbsorberPreProcess.cpp` lines 173-215 tries full
   and partial equivalence absorption. Its triggerability tests accept positive
   `CCSOME` or negated `CCALL`, but not positive `CCALL`; see lines 3755-3769
   and 3925-3933. These mirror definitions consequently enter
   `mEquivConNonCandidateSet` rather than a mirror-specific trigger path.
4. `COptimizedKPSetClassSubsumptionClassifierThread.cpp` consumes that
   noncandidate set in
   `createObviousSubsumptionSatisfiableTestingOrderFromBuildData` near lines
   483-560. It schedules general class satisfiability jobs and possible
   subsumption jobs. `calculateSatisfiable` near line 1210 tests each unresolved
   class. `calculateSubsumption` near line 1298 tests
   `subsumed ⊓ ¬subsumer`, with pseudomodel pruning where possible.

Thus Konclude handles this family through its general KPSet classifier and
completion calculus. It does not compute the complement-contravariant mirror
hierarchy with a dedicated shortcut. The 3,600-second, 53-GB timeout is
consistent with that general path being too expensive on 36,495 retained
noncandidate equivalences.

KM already mirrors the same upstream preprocessing decision in
`engine/src/konclude_ht/bridge.rs`: non-triggerable equivalent definitions are
stored as equivalent noncandidates. Its larger Konclude port contains many
KPSet data structures and result-processing slices, but the full KPSet
scheduler and event integration remain explicitly deferred in
`engine/src/konclude_ht/STATUS.md`. Completing that literal port may reproduce
Konclude's algorithm, but upstream evidence shows that this algorithm does not
close 4669 within either tested limit.

## Soundness gate

The retained target set contains 67 historical KM UNSAT claims:

- 56 HT-only claims;
- 10 sampled production claims;
- one common control claim.

Targeted HermiT runs completed with a satisfiable witness for all 56 HT-only
claims, seven of the ten sampled production claims, and the common control.
That gives 64 confirmed satisfiable witnesses. The remaining three sampled
records did not return a usable result, so they are not counted as witnesses.
These checks refute the old KM taxonomy; they are not a complete taxonomy
oracle.

The source lists and the independent projection work are under
`results/benchmarks/2026-07-18-ore-solve-routes/evidence/`. In particular, see
[`4669-proxy-oracle.md`](../results/benchmarks/2026-07-18-ore-solve-routes/evidence/direct-validation/4669-proxy-oracle.md).
That projection is a possible independent algorithm based on fresh existential
proxies, complement contravariance, and complete disjointness queries. It is
not the method used by Konclude on the original ontology, so implementing it
would violate a strict "port Konclude, do not invent a new method" constraint.

## Decision

No engine change was made. The correct direct-port decision is to keep
`has_unhandled_inverse_negative_existential_mirror` and its early `None`
return. Closing 4669 now requires either:

1. a newly demonstrated Konclude configuration that returns a full taxonomy,
   followed by source tracing and a faithful port; or
2. explicit authorization to finish and validate the independent proxy and
   disjointness route against an authoritative full-IRI oracle.
