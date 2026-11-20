import ContextCalculus.SRIQN.Refute
import ContextCalculus.OWLFrontend.HintRoute

/-!
# The refutation route (`--procedure refute`, v1.7.0 task inc1)

`docs/V1.7.0-INCONSISTENCY-CERT.md`. The route reads an ontology as the hint
route does (datatype definitions unfolded, disjoint unions rewritten,
anonymous individuals renamed) and translates the SROIQ(D) knowledge base to
the `SRIQN` data ontology `dosnC` of the chain route (`sroiq_consistent`:
the ontology is consistent at the OWL 2 datatype map iff `dosnC` is
consistent in the OWL 2 data theory). It then checks a refutation of `dosnC`
with `SRIQN.Refute.refute`. Data clashes are decided on the cells of the
OWL 2 datatype map (`empOWL`), only when every data atom is supported.

The route checks no regularity, chain-elimination or C2a condition: it never
uses chain elimination, and a refutation is a proof, not a search.

* `refuteP_sound`: `refuteP O pf = true → ¬ ConsistentAt (owl2MapP pat) O`,
  for every reading `pat` of `xsd:pattern`.
-/

namespace ContextCalculus.OWLFrontend

open ContextCalculus.OWL ContextCalculus.OWL.Datatypes SHIQD SHOIQ

/-! ## The data oracle -/

/-- A conjunction of literals is empty: no cell under any reading of the
free datatypes satisfies it (and every atom is supported). -/
def empOWL {q : Nat} (spec : Fin q → DataRange) : List (Fin q × Bool) → Bool :=
  let sup := (List.finRange q).all fun p => drSupported (spec p)
  let cs := cellsOf (allBases spec)
  let gs := ContextCalculus.SRIQD.allG (allFrees spec).length
  let E := owlE spec
  fun L => sup && cs.all fun c => gs.all fun g => !(L.all fun l => E l.1 c g == l.2)

theorem empOWL_sound (pat : String → String → Prop) {q : Nat} (spec : Fin q → DataRange)
    (V : Type) (atom : Fin q → V → Prop) (hΘ : owlTheory pat spec V atom)
    (L : List (Fin q × Bool)) (h : empOWL spec L = true) (v : V) :
    ¬ ∀ l ∈ L, ContextCalculus.SRIQD.litSem atom l v := by
  intro hl
  simp only [empOWL, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
    at h
  obtain ⟨hsup, hc⟩ := h
  have hs : ∀ p, drSupported (spec p) = true := fun p => hsup p (List.mem_finRange p)
  obtain ⟨e, fr, hfr⟩ := (owlTheory_iff pat hs V atom).1 hΘ
  have h1 := hc _ (cellOf_mem (as := allBases spec) (e v)) (fun j => fr j (e v))
    (ContextCalculus.SRIQD.mem_allG _)
  rw [← Bool.not_eq_true, List.all_eq_true] at h1
  apply h1
  intro l hlL
  have := hl l hlL
  simp only [ContextCalculus.SRIQD.litSem, hfr] at this
  cases hb : l.2 <;> cases hE : owlE spec l.1 (cellOf (allBases spec) (e v))
      (fun j => fr j (e v)) <;> simp_all

theorem owlTheory_nonempty (pat : String → String → Prop) {q : Nat} (spec : Fin q → DataRange)
    (V : Type) (atom : Fin q → V → Prop) (hΘ : owlTheory pat spec V atom) : Nonempty V := by
  obtain ⟨e, -, -⟩ := hΘ
  exact ⟨e.symm (.bool true)⟩

/-! ## The route -/

/-- The ontology the route reads: datatype definitions unfolded (when there
are any), disjoint unions rewritten, anonymous individuals renamed. -/
def refutePrep (O : Ontology) : Option Ontology :=
  (if (splitDef O.axioms).isSome then dtLoop O.axioms.length O else some O).map
    fun O' => anonOff [] (duOff O')

theorem consistentAt_refutePrep (pat : String → String → Prop) {O X : Ontology}
    (h : refutePrep O = some X) (hk : X.noKey = true) :
    ConsistentAt (owl2MapP pat) O ↔ ConsistentAt (owl2MapP pat) X := by
  unfold refutePrep at h
  obtain ⟨O', hO', rfl⟩ := Option.map_eq_some_iff.1 h
  rw [consistentAt_anonOff (noKey_of_anonOffK hk), consistentAt_duOff]
  split_ifs at hO' with hs
  · exact consistentAt_dtLoop hO'
  · cases hO'; exact Iff.rfl

/-- The refutation checked on the chain-route translation of a prepared
ontology. -/
def refuteChain (X : Ontology) (pf : SRIQN.Refute.Proof) : Bool :=
  if X.isSROIQDKB then
    match translateSHOIQD (roleOff X) [] with
    | none => false
    | some T =>
      match roleCls T X with
      | none => false
      | some E => SRIQN.Refute.refute (dosnC T (nomNames (roleOff X) []) E) (empOWL (spec T.tab)) pf
  else false

theorem refuteChain_sound (pat : String → String → Prop) {X : Ontology} {pf : SRIQN.Refute.Proof}
    (h : refuteChain X pf = true) : X.noKey = true ∧ ¬ ConsistentAt (owl2MapP pat) X := by
  unfold refuteChain at h
  split_ifs at h with hX
  refine ⟨noKey_of_isSROIQDKB_O hX, ?_⟩
  split at h
  · cases h
  next T hT =>
    split at h
    · cases h
    next E hE =>
      rw [sroiq_consistent pat hX hT hE]
      exact SRIQN.Refute.refute_sound (owlTheory_nonempty pat _) (empOWL_sound pat _) h

/-- **The refutation route.** -/
def refuteP (O : Ontology) (pf : SRIQN.Refute.Proof) : Bool :=
  match refutePrep O with
  | some X => refuteChain X pf
  | none => false

/-- **Soundness of the refutation route**: a refutation the checker accepts
shows that the ontology has no model at the OWL 2 datatype map, for every
reading of `xsd:pattern`. -/
theorem refuteP_sound (pat : String → String → Prop) {O : Ontology} {pf : SRIQN.Refute.Proof}
    (h : refuteP O pf = true) : ¬ ConsistentAt (owl2MapP pat) O := by
  unfold refuteP at h
  split at h
  · next X hX =>
    obtain ⟨hk, hc⟩ := refuteChain_sound pat h
    rwa [consistentAt_refutePrep pat hX hk]
  · cases h

end ContextCalculus.OWLFrontend

#print axioms ContextCalculus.OWLFrontend.empOWL_sound
#print axioms ContextCalculus.OWLFrontend.refuteChain_sound
#print axioms ContextCalculus.OWLFrontend.refuteP_sound
