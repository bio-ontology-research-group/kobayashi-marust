# Same-owner functional data clash

The admitted ground-data projection now detects two distinct canonical values attached to the same syntactic owner under a functional superproperty. This is an exact inconsistency certificate: every interpretation maps that owner to itself, and functionality requires the two values to coincide. Duplicate assertions and lexical aliases remain consistent. Different owner names do not imply inequality.

`GroundDataOwnerClash.same_owner_incompatible` proves the certificate against the existing functional model-extension contract. The frontend retains its whole-source admission and datatype decoding checks. This precheck does not certify the separate native ABox cardinality cache, for which a fresh/cache/classification regression has been added and remains under investigation.

Validation so far: six standalone tests of the production ground-data module pass; the new Lean lemma checks without axioms. Full binary integration and certification gates remain required before promotion.
