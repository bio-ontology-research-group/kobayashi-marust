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
IBEX build job `49729184` produced binary SHA-256
`e3ad3c996135b21c87e4d57fcfb48b44c5b2428e4df873690231084171782802`.
Focus array `49729185` recorded:

- ORE 9944, forced `cb_plain16`: exact match, 9.8543 seconds and 6,483.45 MiB.
  The historic exact route took 17.319 seconds and 6,558.71 MiB.
- ORE 9944, forced `cb_plain1`: exact match, 55.2924 seconds and 2,701.70 MiB.
  The historic exact route took 95.9574 seconds and 2,739.87 MiB.
- ORE 12141, forced `cb_plain16`: worker error after 190.1598 seconds. This was
  an unsuitable CB control because the established exact routes for 12141 are
  HT routes; it is not a default-route regression result.
- ORE 1194, automatic route: error at the 18 GiB adaptive memory guard after
  29.1408 seconds, with a 18,443.50 MiB observed peak. The faster CB expansion
  therefore exposes memory as the next limiting resource but does not close
  the ontology.
- ORE 4669, automatic route: timeout at 240.0228 seconds and 2,504.11 MiB.

The exact 9944 controls establish a 42–43% CB wall-time reduction with no
signature change. Neither residual ontology is recovered. A full
592-ontology candidate sweep is still required before promotion; it waits for
the in-flight `4703045` promotion sweep so the two result roots cannot compete
or be confused.

## Rejected Pred-arrival antichain

A follow-up diagnostic indexed received predecessor clauses by head and
discarded an arrival when an already-received clause strengthened it. The
criterion is fixpoint-preserving, but its index and subset checks were a net
loss on the measured 1194 bottleneck. In the same 60-second, one-root profile,
the gate processed 1.66 million messages and peaked at 2,302,476 KiB; the
retained implementation processed 2.12 million and peaked at 1,963,528 KiB.
The experiment was removed without a commit. No `KM_PRED_ARRIVAL_SUBSUME`
option exists in the retained source.
