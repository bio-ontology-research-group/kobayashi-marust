# Per-source existential witnesses: obligations and measured cost

The certificate model keeps one canonical node per skolem function, shared by
every source that reaches it. That sharing is what makes an at-most merge
contradict a `≥n` clause model-wide, and what makes an inverse bridge repair
mirror the whole role graph. Giving each source its own witness is the
construction that would localize both. This document states what such a
construction would have to discharge, isolates the smallest faithful version of
it, and measures what each would cost on ORE 1194.

## The construction being replaced

The EL completion builds the ELK canonical model: one element per concept name,
with the existential rule

```
R∃ :  C ⊑ D,  D ⊑ ∃R.E   ⟹   edge (C, R, E)
```

so every `C ⊑ D` gets an edge to the *same* element for `E`. For a skolem term
in the residual, `compile_residual` interns one dedicated node
`__cert_witness__f` per skolem function `f`, makes it an EL subclass of the NF3
filler, and rewrites that NF3 row to point at it. The witness is therefore
shared across every source element that reaches the axiom.

A per-source construction replaces each application of `R∃` at source `C` with a
fresh element carrying the filler's completed label. It is the unravelling of
the shared model.

## Why it is the semantically faithful one

The shared model is a quotient of the per-source model: the map sending every
copy of a witness to the single canonical node is a p-morphism. Concept
membership is invariant under bisimulation, so for EL the two models agree on
every label, which is exactly why the shared model is sound and complete there.

Bisimulation invariance fails for precisely the constructs in 1194's residual.

- **Qualified number restrictions.** The quotient collapses successors that the
  unravelling keeps apart, so it undercounts `R`-successors. A `≤n R.C` bound can
  hold in the quotient and fail in the unravelling; a `≥n R.C` bound can be
  satisfied in the unravelling by elements the quotient has identified.
- **Inverse roles.** An inverse edge out of a shared witness reaches every source
  that shares it. In the unravelling each copy has exactly one predecessor.

So the per-source model is the more faithful one, and the sharing is a genuine
approximation that the repair search currently has to work around. That is not a
defect of the repair; it is a property of the model it is repairing.

## Obligations

A per-source construction has to discharge all of the following before it can
carry the certificate.

1. **The upper bound must still be a model of the full ontology.** The
   certificate refutes `C ⊑ D` by finding `D` absent from the label of `C`'s
   element. The unravelled structure must satisfy every EL normal form and every
   residual clause, and must retain a distinguished root element for each named
   concept whose label is read. Unravelling copies labels downward, so
   `base ⊆ per-source` holds at the roots, and the existing acceptance test
   transfers unchanged.
2. **The lower bound is untouched.** The EL saturation supplies it and does not
   change.
3. **Finiteness.** This is the binding obligation. The unravelling of a cyclic
   EL model is infinite; witness sharing is exactly the device that closes those
   cycles. A per-source construction must reintroduce blocking, and with inverse
   roles present in the residual, subset blocking is unsound. It needs dynamic or
   double blocking, with a soundness proof for the residual constructs present.
4. **The per-subject intersection criterion** must be evaluated over the root
   elements only, not over copies, or unrelated copies would pollute the
   intersection.

Obligation 3 is where this stops being a small change. A per-source witness
model with inverse roles and double blocking is a hypertableau. This repository
already has one, `engine/src/tableau.rs`, and `AGENTS.md` records that it errors
or hangs on real ORE ontologies and must not be wired into the benchmark. So
the faithful construction is not a modification of the certificate; it is a
replacement of the certificate by a procedure already known not to scale here.

## Smallest faithful variant

The full unravelling is not the smallest change. The sharing only causes trouble
where a residual clause can observe it, and the clause that observes it is the
`≥n` witness-distinctness clause, which pins two specific witness nodes apart.
So the smallest faithful variant expands **only the pinned witnesses**, giving
each of their sources a private copy, and leaves every other witness shared.
That is enough to make a pinned pair distinct per source, which is what the
current search has to refuse a merge to avoid.

Its cost is measurable exactly: each pinned witness needs one copy per source
that reaches it, which is its in-degree in the saturated model.

## Measured cost on 1194

Reported by the certificate itself at startup (`per-source-witness-projection.log`):

```
KM_ELC_CERT per-source witness projection: 499902 alive node(s), 78367893
subsumption(s), 43891310 edge(s), avg label 156; full expansion = 43891310 new
node(s) / 6847044360 projected fact(s); selective expansion over 36 pinned
witness(es) = 148 new node(s) / 23088 projected fact(s)
```

| variant | new nodes | projected subsumption facts | verdict |
| --- | --- | --- | --- |
| full unravelling | 43,891,310 | 6,847,044,360 | over the cap by a wide margin |
| selective, pinned witnesses only | 148 | 23,088 | affordable |

The full unravelling needs one fresh node per existential edge, each carrying
its filler's completed label of about 156 supers. At 4 bytes per fact and no
container overhead that is already 27.4 GB against a 20 GiB cap, and the actual
`Vec<HashSet<u32>>` representation costs several times that. It is out of reach
by roughly two orders of magnitude, before the finiteness obligation is even
addressed.

The selective variant is the opposite: the 36 pinned witnesses have a combined
in-degree of 148, so expanding them per source costs 148 nodes and about 23,000
facts. It is essentially free.

## Verdict: not implemented

The full unravelling is out of reach on this ontology by about two orders of
magnitude, and it carries the finiteness obligation that turns it into a
hypertableau. That much was expected.

The selective variant is the interesting result, and it argues against itself.
It is affordable, but its own cost measurement is the evidence that it does not
address what stops 1194. The 36 pinned witnesses have a combined in-degree of
148. The sharing that the repair search has to work around is therefore a
148-instance phenomenon inside a model of 43,891,310 edges. If pinned-witness
sharing were the scale problem, those witnesses would have large in-degrees;
they average about four sources each.

Three reasons not to implement it:

1. **It solves an already-solved problem.** The identification-legality filter
   already refuses exactly the merges that shared pins make illegal, and reaches
   zero conflicts and zero restarts on 1194. Per-source copies would make some
   of those merges legal again at unguarded sources, which changes the search's
   options but not its outcome.
2. **It does not touch the binding constraint.** The gate is consumed by round
   23, the first of 14 inverse role bridges, which did not finish its repair in
   over 850 s. A bridge is violated once per edge, so per-source expansion moves
   that count in the wrong direction, by 148 edges here and by far more on any
   ontology where the pinned witnesses are heavily shared.
3. **It would change the residual checker, not just the search.** Skolem terms
   are checkable today because `compile_residual` pins the variable for `f(x)` to
   one fixed node before evaluation. Per-source copies make `f(x)` a function of
   the binding of `x`, so the join in `cert_round` would have to resolve it per
   binding through a `(function, source)` lookup. Every change landed in this
   branch so far leaves `cert_round`'s checking untouched and confines itself to
   choice order; this one would not, and it would need its own correctness
   argument for a payoff of zero on the gate.

The honest summary is that the shared-witness approximation is real, is
semantically weaker than the unravelling, and is not what stops ORE 1194. The
earlier suggestion in this evidence set that per-source witnesses were "what
would actually close it" was wrong, and this measurement is what corrects it.
