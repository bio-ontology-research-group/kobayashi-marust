# Practical-impact evidence for complete OWL 2 DL reasoning

This supplement asks what complete OWL 2 DL classification can establish that
an OWL 2 EL classifier cannot establish after unsupported axioms are omitted.
It separates executed results, failed executions, proposed experiments, and
work blocked on a restricted input. The binding claim boundary is
`ledger.tsv`; `evidence/results.tsv` summarizes every copied execution record.

## Demonstrated now

The impact jobs used post-v1.3 source commit
`301d37426cdf3dea249d9609037a2f1e47e89314` and binary SHA-256
`c8688f6b286db2b422f1ec1df0874eadbbce0cc9e2899f35dbe143ccad70639d`.
The crate still reports version 1.3.0, but this commit is 64 commits after the
v1.3.0 tag. These results therefore demonstrate capabilities of that exact
development artifact, not new measurements of the tagged v1.3.0 release.

Three controlled examples were executed with KM, ELK 0.6.0, and HermiT
1.4.5.519. The legacy `positive` suffix means that the adverse logical
consequence is present; `negative` means the repaired control. The clearer
publication labels are recorded in `case-map.tsv` without renaming immutable
evidence identifiers.

* In the merged biomedical-interoperability example, KM and HermiT find
  `IntegratedFinding` unsatisfiable while the ontology remains consistent.
  Changing only the existential filler makes the class satisfiable. ELK's two
  out-of-profile runs have the same consistency field and relation digest
  because the decisive universal restriction is outside OWL 2 EL.
* In the access-policy example, KM and HermiT find
  `PrivilegedContractor` unsatisfiable while the ontology remains consistent.
  Changing only the required filler makes the class satisfiable. ELK's two
  out-of-profile runs again have the same consistency field and relation
  digest.
* In the synthetic SNOMED-style example, the TBox requires left and right
  fillers, declares their types disjoint, and permits at most one laterality
  filler. Under OWL Direct Semantics those four axioms make
  `BilateralProcedure` unsatisfiable, so the TBox is incoherent but can still
  have a model. The executed file additionally asserts `exampleCase` as a
  `BilateralProcedure`, which makes the whole ontology inconsistent. KM and
  HermiT directly report that ABox inconsistency. The copied KM output does not
  separately enumerate the unsatisfiable class once the ontology is globally
  inconsistent, and no separate TBox-only classifier run is claimed. Removing
  the maximum-cardinality axiom is the executed consistent control. ELK's two
  out-of-profile runs report consistency and have the same relation digest.

For each adverse controlled case, KM returned one source-axiom support. The
supports are verified and subset-minimal relative to KM's automatic
classification oracle. Enumeration is not complete because the jobs requested
one justification; they are not independently checked proof objects.

The exact development artifact also classified the frozen ORE 2015 GALEN
input twice. Both executions report consistency, zero unsatisfiable named
classes, and 457,090 non-self subsumptions with identical taxonomy and relation
digests. This ORE input is distinct from the planned current BioPortal GALEN
hard case, which was not acquired because no BioPortal API key was available.

## Failed or blocked now

The frozen current Uberon input is OWL 2 DL but not OWL 2 EL. Its source
VersionIRI is 2026-06-19; the `uberon-2026-06-23` receipt stem is a legacy job
label, not the ontology version. Both automatic runs failed with exit code 1,
empty output, and `worker engine exited -1`: 11:40 at 17,724,884 KiB peak RSS
and 12:34 at 17,604,952 KiB. Two route diagnostics also failed: the
single-thread `production_all1` portfolio and `certified_nominals` portfolio
each timed out at 3,600 seconds without output, at 577,736 and 3,146,808 KiB
peak RSS respectively. None is a successful full-DL Uberon classification.
The historical v1.3 current-OBO matrix likewise contains no completing
expressive reasoner for this Uberon input; ELK and Whelk outputs are
out-of-profile observations only.

The first explanation array, job 51298402, failed before invoking KM because
the submitted batch script encountered a shell-array syntax error. The
corrected rerun, job 51298706, produced the three copied explanation records.
The failed attempt remains in `evidence/jobs.tsv` and is not counted as an
explanation result.

The synthetic SNOMED-style files contain no SNOMED CT content and establish no
finding about SNOMED CT. A licensed SNOMED CT experiment remains blocked until
an authorized release, exact checksum, pinned conversion where needed, and a
domain-reviewed perturbation are supplied. Product-configuration and
data-governance rows are experiment designs, not executed demonstrations.

## Enabled in principle versus established here

A complete OWL 2 DL reasoner can, when it terminates within the resource
contract, classify the ontology without deleting universal restrictions,
negation, disjunction, inverse roles, nominals, or number restrictions. It can
therefore test whether those axioms change named-class subsumption,
unsatisfiability, or consistency. It can also distinguish an incoherent TBox
from an inconsistent ontology after an individual instantiates an
unsatisfiable class, and it can provide bounded source-axiom supports for
review.

This artifact establishes those points only for the controlled cases and the
frozen ORE 2015 GALEN input. It does not establish full-DL classification of
current Uberon, current BioPortal GALEN, or SNOMED CT. It also does not
reproduce the full iterative UNMIREOT repair workflow. Logical findings locate
conflicting axioms; they do not determine which axiom, if any, is
scientifically wrong.

## Reproduction and validation

Large inputs were never parsed or classified on an IBEX login node. The Slurm
scripts under `../benchmark/impact/` cap arrays at four simultaneous tasks.
They bind source commit, binary, ontology, output, host, job, terminal status,
wall time, and peak RSS where applicable. The commands used for the retained
artifact are:

```bash
SOURCE_COMMIT=301d37426cdf3dea249d9609037a2f1e47e89314 \
IMPACT_ROOT=/ibex/scratch/hohndor/km/v1.4-paper-impact-20260903 \
  sbatch paper/benchmark/impact/ibex_build.sbatch

SOURCE_COMMIT=301d37426cdf3dea249d9609037a2f1e47e89314 \
IMPACT_ROOT=/ibex/scratch/hohndor/km/v1.4-paper-impact-20260903 \
PAPER_ROOT=/ibex/scratch/hohndor/km/v1.4-paper-impact-20260903/paper \
  sbatch paper/benchmark/impact/ibex_run.sbatch

IMPACT_ROOT=/ibex/scratch/hohndor/km/v1.4-paper-impact-20260903 \
PAPER_ROOT=/ibex/scratch/hohndor/km/v1.4-paper-impact-20260903/paper \
  sbatch paper/benchmark/impact/ibex_explain.sbatch
```

No rerun is needed to validate the compact bundle:

```bash
python3 paper/benchmark/impact/validate_evidence.py
```

The validator fails closed on missing or extra records, digest mismatches,
unexpected successful Uberon routes, changed controlled-case axioms, stale
ledger states, baseline outcome changes, or weakened explanation supports.
