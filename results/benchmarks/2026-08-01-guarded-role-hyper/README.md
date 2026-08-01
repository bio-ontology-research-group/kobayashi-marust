# Guarded role Hyper index

Commit `1f2f46b` replaces the broad role posting for the normalized pattern
`C(y) ∧ R(x,y) -> D(x)` with a compact `(R,C)` join index. When Hyper is
triggered by `R(s,t)`, KM now probes only filler concepts actually available as
maximal `C(t)` premises in that context. The original ontology clauses still
enter the same Hyper rule in ascending clause order. This changes candidate
enumeration only, so the saturation fixpoint is unchanged and no Lean
re-certification is required.

The diagnosis used source-current ORE 1194 clauses. Its largest role postings
contained 144,131 and 144,132 clauses, almost all of the guarded two-body
shape. In a 45-second one-root profile before the index, KM processed 20,000
message-loop entries and reached 364 contexts. With the index, it processed
1.74 million entries and reached 1,951 contexts. A single root still did not
finish within 240 seconds, so this is not an ORE 1194 closure claim.

The full release suite passed at commit `1f2f46b`: 1,836 tests passed, zero
failed, and eight diagnostic tests were ignored, followed by every integration
and documentation target. The dedicated regression proves both that the
guarded clause leaves the broad role posting and that its entailment is still
derived through the indexed join.

IBEX validation is source-bound to `source-1f2f46b.tar.gz`, SHA-256
`cbdb06566ebf5c431e524b1ec47ab426f545d31f64c410288b00ef3434f889ea`.
The focused gate tests exact CB outputs on 9944 and 12141, both one- and
sixteen-worker scheduling for 9944, and the current automatic route on the two
residual ontologies 1194 and 4669. A full 592-ontology candidate sweep is
required before promotion.
