# Source admission for retained module publication

The retained source session uses the existing `IncrementalModuleReuse`
publication theorems. The named-subclass certificate changes how the runtime
establishes admission of a source revision. It does not add a derivation rule,
infer consistency, alter locality formulas, or authorize a taxonomy answer.

`common_module_query`, `mixed_publication_exact`, and
`mixed_named_publication_exact` still require the same source/module binding.
Their semantic arguments do not validate OWL syntax or its global restrictions.
Parser and admission correspondence remain executable Rust obligations.

The implementation contract is:

- Mint an origin only from the exact successful `check_user_source` cache at
  the existing public validation boundary. Classification success or a caller
  flag cannot mint it. Capture must not repeat full validation just to mint.
- Keep the validated header and every fixed statement's exact bytes and
  multiplicity. Hashes are lookup keys; matching hashes still require matching
  bytes. Class operands must retain exact validated declaration spellings.
- Permit annotation-free named `SubClassOf` edits. Permit deletion and bounded
  restoration of exact origin named `DisjointClasses` statements, never novel
  disjointness. Validate novel named inclusions with the real compact source
  validator under the unchanged header. Unsupported forms use full validation.
- Check NEW outer gaps, the ontology-annotation phase, and the final close
  before non-byte-identical memo/deletion/module publication. Only vendor
  space, tab, CR, LF and line-comment gaps qualify. Unicode may remain inside
  validated spans and comments; unsupported token boundaries fall back safely.
- Carry immutable origin provenance through deletions without pretending each
  deletion ran a new validator. Check the exact NEW source at a common update.
  Do not transplant `SourceFacts`, profiles or a successful NEW validation-cache
  entry. A refused update must preserve the preceding public revision.

The first certificate implementation conservatively declines non-ASCII
documents. This restriction applies to the optimization, not the general
outer-grammar guard or public validator. Full validation preserves admission
for unsupported valid documents.

`run-routing-certification-gate.sh` runs `source_reuse_grammar::tests::`,
`named_subclass_validation::`, and all `source_module_reuse` public regressions.
The certificate's differential test re-executes one exact test in a separate
process and calls the actual public validator. Its successful-validation cache
cannot race other Rust unit tests. Tests cover valid and refused controls,
prefix aliases, punning, multiplicities, changed declarations/annotations,
malformed gaps and IRIs, origin restoration, and refusal rollback.

No new Lean axiom is introduced by this admission optimization. Final release
still requires all four production gates on the exact final source, with no
`sorryAx`, plus the independent Rust/Java/corpus validation requirements. Passing
the Lean surface alone must not be described as parser certification.
