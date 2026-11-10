# v160-p3-rerun: STOPPED at Part 1 (forced/unforced difference found)

Part 1 fix 1 (class-only request) is committed. Fix 2 (unsatisfiable rows) could not be done as briefed:
production does not follow one rule, so no cell filter reproduces it. Part 2 (suite rerun) was not run,
as the brief requires a stop on any forced/unforced difference.

Fix 1: `try_reference_stage` (engine/src/orchestrate/mod.rs) now requests `meta.declared`, plus names of
`meta.named`/`meta.asserted_classes` that are declared, asserted or occur as a concept atom in the clause stream.
This removed the property `:s` row `SUB :s :C` from min_atleast0_gci and fixed min_copy_successor_insufficient.
After the fix forced == unforced on: min_atleast0_gci, min_copy_successor_insufficient, datatype_union_cover,
g633 (original), all fixtures/reference_stage EL and ALC fixtures that were passing.

Difference found (unsatisfiable classes), forced adds rows production omits (all entailed):
- el_property_unsat.ofn (new fixture): forced adds `SUB :U :V` (U, V unsat; production has V SUB U, not U SUB V).
- alc_property_unsat.ofn (new): forced adds B SUB A, B SUB U, U SUB B.
- g633.ofn with my transient strip-all-sups version matched, but strip-all breaks el_unsat_class.ofn (production
  EL route emits U SUB A,B,C there) and alc_property_unsat (production emits U SUB A, U SUB C, B SUB C).
Production's rows for unsat classes are route-internal (told/derived without using bottom), not a function of the
entailment matrix. Both tests are `#[ignore]`d with this reason.
Decision needed: either define digest equality modulo entailed rows of unsat classes, or make production emit them.
