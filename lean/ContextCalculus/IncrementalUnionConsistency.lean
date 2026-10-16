import ContextCalculus.IncrementalModuleReuse

/-!
# Object-only union consistency from a retained empty core

A full-locality module of OLD ∪ NEW can establish union consistency when its
axioms all remain in the previously consistent OLD. The core need not remain
in NEW. In the executable path module extraction starts with an empty seed;
its fixpoint has a generally nonempty closed signature S0. The theorem uses
that closed signature, not the initial seed. Checking only added axioms
suffices to establish containment of the extracted module in OLD.

This boundary applies only to the concrete object `Axiom` semantics. Sources
with any data axioms or data assertions still require the complete NEW-source
consistency check. Source admission, exact header/text/hash membership, actual
full-index provenance and successful OLD consistency remain executable duties.

After deriving NEW consistency, classification of a NEW nominal-free TBox
module decides covered named queries and unsatisfiability. The `PlainAx`
premise is essential: an affected module containing a nominal cannot use this
path and must retain complete NEW-source classification. This file does not
claim that arbitrary TBox modules preserve consistency or nominal queries.

The closed signature S0 is the logical fixpoint before the executable module
API restores original individual occurrences for declaration emission. That
postprocessing does not run locality again; its expanded returned declaration
signature need not be the signature used in this IsModule certificate.
-/

namespace ContextCalculus.IncrementalUnionConsistency

open IncrementalModuleReuse

universe u v

/-- A module contained in a known consistent theory supplies a model of its
whole envelope. No containment of the module in NEW is needed. -/
theorem union_model_of_old_model {Ax Q Sym : Type u} {I : Type v}
    (sem : MaskedSemantics Ax Q I Sym) {OLD V M : Ax → Prop} {S : Sym → Prop}
    (hm : IsModule sem V M S) (hkeep : ∀ a, M a → OLD a)
    (hold : ∃ i, Models sem OLD i) : ∃ i, Models sem V i := by
  apply (module_has_model sem hm).mpr
  obtain ⟨i, hi⟩ := hold
  exact ⟨i, fun a ha => hi a (hkeep a ha)⟩

/-- Concrete production consistency certificate for the object-only full
module in the union index, over its closed extraction signature. -/
theorem object_union_consistent {OLD V M0 : Axiom → Prop} {S0 : Nat → Prop}
    (hm : IsModule sroiq V M0 S0)
    (hkeep : ∀ a, M0 a → OLD a)
    (hold : ∃ (W : Type) (i : Interp W), ∀ a, OLD a → sat i a) :
    ∃ (W : Type) (i : Interp W), ∀ a, V a → sat i a := by
  obtain ⟨W, i, hi⟩ := hold
  have oldModel : ∃ m, Models sroiq OLD m := ⟨⟨W, i⟩, hi⟩
  obtain ⟨m, hm⟩ := union_model_of_old_model sroiq hm hkeep oldModel
  exact ⟨m.1, m.2, hm⟩

/-- NEW inherits a model by being a subset of the certified union; deleted
empty-core axioms need not be restored. -/
theorem object_new_consistent {OLD NEW V M0 : Axiom → Prop} {S0 : Nat → Prop}
    (hm : IsModule sroiq V M0 S0)
    (hkeep : ∀ a, M0 a → OLD a) (hnew : ∀ a, NEW a → V a)
    (hold : ∃ (W : Type) (i : Interp W), ∀ a, OLD a → sat i a) :
    ∃ (W : Type) (i : Interp W), ∀ a, NEW a → sat i a := by
  obtain ⟨W, i, hi⟩ := object_union_consistent hm hkeep hold
  exact ⟨W, i, fun a ha => hi a (hnew a ha)⟩

/-- Build the NEW module contract using union-derived consistency and the
independent nominal-empty TBox analysis. `hplain` excludes nominal modules. -/
theorem object_affected_module_from_union {OLD NEW V M0 M : Axiom → Prop}
    {S0 S : Nat → Prop} (hm0 : IsModule sroiq V M0 S0)
    (hkeep0 : ∀ a, M0 a → OLD a) (hnew : ∀ a, NEW a → V a)
    (hold : ∃ (W : Type) (i : Interp W), ∀ a, OLD a → sat i a)
    (hkeep : ∀ a, M a → NEW a) (hplain : ∀ a, M a → PlainAx a)
    (hcov : ∀ a, M a → ∀ n, OccursA n a → S n)
    (hrest : ∀ a, NEW a → ¬ M a →
      AssertionAx a ∨ (TBoxAx a ∧ nonLocalN (bsig S) a = false)) :
    NominalModule NEW M S :=
  nominal_module_from_envelope (fun _ h => h) hkeep hplain hcov hrest
    (object_new_consistent hm0 hkeep0 hnew hold)

/-- Complete named rows of an affected, nominal-free NEW module are exact,
including named targets outside its signature. -/
theorem object_affected_named_query {OLD NEW V M0 M : Axiom → Prop}
    {S0 S : Nat → Prop} (hm0 : IsModule sroiq V M0 S0)
    (hkeep0 : ∀ a, M0 a → OLD a) (hnew : ∀ a, NEW a → V a)
    (hold : ∃ (W : Type) (i : Interp W), ∀ a, OLD a → sat i a)
    (hkeep : ∀ a, M a → NEW a) (hplain : ∀ a, M a → PlainAx a)
    (hcov : ∀ a, M a → ∀ n, OccursA n a → S n)
    (hrest : ∀ a, NEW a → ¬ M a →
      AssertionAx a ∨ (TBoxAx a ∧ nonLocalN (bsig S) a = false))
    {c : Concept} (hc : Plain c) (hs : ∀ n, OccursC n c → S n) (b : Nat) :
    EntailsC NEW (c, .atom b) ↔ EntailsC M (c, .atom b) :=
  nominal_module_named_query
    (object_affected_module_from_union hm0 hkeep0 hnew hold hkeep hplain hcov hrest)
    hc hs b

/-- Unsatisfiability uses the same certified NEW consistency and plain-module
contract, not a consistency guess from a restricted classifier answer. -/
theorem object_affected_unsat_query {OLD NEW V M0 M : Axiom → Prop}
    {S0 S : Nat → Prop} (hm0 : IsModule sroiq V M0 S0)
    (hkeep0 : ∀ a, M0 a → OLD a) (hnew : ∀ a, NEW a → V a)
    (hold : ∃ (W : Type) (i : Interp W), ∀ a, OLD a → sat i a)
    (hkeep : ∀ a, M a → NEW a) (hplain : ∀ a, M a → PlainAx a)
    (hcov : ∀ a, M a → ∀ n, OccursA n a → S n)
    (hrest : ∀ a, NEW a → ¬ M a →
      AssertionAx a ∨ (TBoxAx a ∧ nonLocalN (bsig S) a = false))
    {c : Concept} (hc : Plain c) (hs : ∀ n, OccursC n c → S n) :
    EntailsC NEW (c, .bot) ↔ EntailsC M (c, .bot) :=
  nominal_module_entails_iff
    (object_affected_module_from_union hm0 hkeep0 hnew hold hkeep hplain hcov hrest)
    (q := (c, .bot)) hc trivial hs (fun _ h => h.elim)

#print axioms union_model_of_old_model
#print axioms object_union_consistent
#print axioms object_new_consistent
#print axioms object_affected_module_from_union
#print axioms object_affected_named_query
#print axioms object_affected_unsat_query

end ContextCalculus.IncrementalUnionConsistency
