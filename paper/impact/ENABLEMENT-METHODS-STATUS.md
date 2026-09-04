# KM practical-enablement methods and status

Status date: 2026-09-04. The machine-readable claim boundary is
[`enablement-ledger.tsv`](enablement-ledger.tsv). This document reports results,
not intended marketing claims.

## Answer to the impact question

The current evidence establishes that KM makes two kinds of full OWL 2 DL
workflow practical:

1. It classifies the frozen ORE 2015 GALEN artifact without deleting its
   non-EL axioms. A same-source differential now shows that those axioms matter:
   the full taxonomy has 457,090 subsumptions, while the independently verified
   OWL 2 EL axiom subset has 453,710. The 3,380 full-only relations are not an
   EL-profile warning alone; they are a measured semantic difference.
2. It detects and explains contradictions that depend on universals or number
   restrictions in controlled biomedical-merge, policy, terminology-design,
   and product-configuration examples. Their EL controls lose the decisive
   axioms and do not expose the conflict.

Neither result establishes that only KM can perform the task. Konclude agrees
with KM on full GALEN, and HermiT agrees on the controlled conflict cases. The
defensible result is that full-DL reasoning changes the answer and that KM can
execute the workflow. The retained artifact does not yet establish a natural
ontology task that KM completes while every tested complete reasoner fails.

KM also returns a hash-bound consistency verdict for current Uberon. That is a
consistency-only result, not classification. The full current-Uberon taxonomy
remains outside this impact artifact until the separate core investigation
publishes a terminal, validated result.

## Common experimental protocol

For every natural full-versus-EL case:

1. Start from an import-frozen ontology and verify its SHA-256.
2. Use OWLAPI's OWL 2 EL profile checker. Delete each whole source axiom tied to
   a violation, repeat until `OWL2EL=true`, and retain the removed-axiom digest.
   This is an axiom-deletion control, not an official project `basic`, `core`,
   or `lite` edition.
3. Classify the generated EL ontology with KM and ELK. Require exact agreement
   after canonicalizing identifiers and result semantics.
4. Compare the EL result with the full KM result over the same names. For a
   consistent ontology, every EL consequence must occur in the full result.
5. Use an independent complete reasoner for the full result or sampled
   consequences. Record failures rather than treating majority vote as gold.

The protocol follows the syntactic boundaries in the
[W3C OWL 2 Profiles Recommendation](https://www.w3.org/TR/owl2-profiles/).

## New completed evidence

### ORE GALEN full versus EL

- Input: `ore_ont_9724.owl`, SHA-256
  `00c80e07aa57578c168d15a1755b62fde41c53dd69a2f04cc5d88c888c8baf19`.
- Projection: 1,149 of 61,782 axioms removed in one round; output SHA-256
  `e4a1ef350907432a7af8b857c784f4a53ec7e7bbcfaad961dd4114baf1fc9a71`;
  OWLAPI reports `OWL2EL=true`.
- EL result: KM and ELK 0.6.0 agree exactly on consistency, zero
  named-unsatisfiable classes, and 453,710 subsumptions.
- Full result: the retained repeated KM classification has 457,090
  subsumptions and exactly matches the historical Konclude result.
- Difference: 3,380 full-only and zero projection-only subsumptions.
- Jobs: preparation `51326535`, KM `51326550`, ELK `51326551`, validation
  `51326594`.
- Limits: each classification task requested 4 CPU and 18 GiB, with at most two
  concurrent tasks and a 1,200-second command timeout. KM completed the EL view
  in 2.59 seconds at 215,948 KiB peak RSS; ELK completed in 7.88 seconds at
  1,166.89 MiB peak RSS. These are diagnostic measurements, not a controlled
  headline benchmark comparison.

Interpretation: the exact non-EL axiom set contributes named hierarchy
information at GALEN scale. This supports using full-DL classification for
downstream concept navigation, integration checks, and release comparisons
when an EL projection would silently omit those relations. It does not show
that each removed axiom contributes, and it does not identify which relations
matter clinically.

### Product-configuration control

- Inputs: conflict SHA-256
  `a92e020a6957504fc4ee1d206389288e65a8c8637d874d42aaacc31899e0fde6`;
  repaired control SHA-256
  `baad9238c8bcbf1519d3b006299334a52cf489a5f4b57292de32ffec69e0d2f3`.
- Intervention: the conflict adds one qualified maximum-cardinality axiom to a
  class that requires optical and thermal payload fillers whose types are
  disjoint.
- Full result: KM and HermiT report both ontologies consistent and only
  `DualSensorSurveyDrone` unsatisfiable in the conflict.
- EL result: the projection deletes the one maximum-cardinality axiom. The two
  projected ontologies have identical semantics, and KM and ELK agree exactly.
- Explanation: KM returns one verified, subset-minimal seven-axiom support that
  contains the two payload type axioms, disjointness, both existential
  requirements, the configuration superclass link, and maximum cardinality.
- Jobs: KM `51326538` and `51326539`; HermiT `51326543` and `51326545`;
  explanation array task `51326536_10`; validation `51326594`.

Interpretation: full DL can reject a logically impossible configuration that
the exact EL axiom subset accepts. This is a controlled mechanism test, not an
industrial product-line result.

## UNMIREOT extension

Slater, Gkoutos, and Hoehndorf used ELK in a merge, explanation, axiom-removal,
and reclassification loop and explicitly identified negation and universal
restriction as limitations of that oracle
([DOI 10.1186/s12911-020-01336-2](https://doi.org/10.1186/s12911-020-01336-2)).
KM can replace the oracle calls in that workflow, but only the controlled merge
mechanism has been executed here. The exact 2018 payloads have not been
reacquired, and the frozen 2026 snapshot would constitute a new-data study.
No corpus-scale repair or additional contradiction count is claimed.

## Current limitations and next evidence

- Current Uberon has a successful guarded consistency check but no retained
  full taxonomy in this artifact.
- FMA has a successful Konclude reference result but no current KM
  full-versus-EL differential.
- NCIt and ChEBI have strong full-base agreement but no differential. ChEBI is
  the important null control because one profile violation may have no named
  effect.
- No licensed SNOMED CT content was acquired or tested.
- The FIBO and data-governance experiments remain source-gated proposals.
- The first validation job, `51326537`, correctly failed because the validator
  compared KM default-prefixed identifiers with HermiT expanded IRIs. No
  ontology task failed. The corrected validator canonicalized those equivalent
  identifiers, and validation job `51326594` passed. Both records are retained.

The strongest next experiment is FMA full versus EL because Konclude supplies
an independent full-output oracle. After that, NCIt can test a broader
non-EL case and ChEBI can test the null hypothesis. A corpus-scale UNMIREOT
extension should begin only after a frozen core-set preregistration.

## Evidence locations

- Compact extension evidence:
  [`evidence/extension-20260904/`](evidence/extension-20260904/)
- Executable Slurm scripts:
  [`../benchmark/impact/`](../benchmark/impact/)
- Pre-existing controlled evidence and guarded Uberon result:
  [`evidence/`](evidence/)
- Detailed proposed-case manifest:
  [`../IMPACT-USE-CASE-MANIFEST.tsv`](../IMPACT-USE-CASE-MANIFEST.tsv)

