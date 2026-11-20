import ContextCalculus.SRIQN.Refute
import ContextCalculus.OWLFrontend.HintRoute

/-!
# The refutation route (`--procedure refute`, v1.7.0 task inc1)

`docs/V1.7.0-INCONSISTENCY-CERT.md`. The route reads an ontology as the hint
route does (datatype definitions unfolded, disjoint unions rewritten,
anonymous individuals renamed), but drops keys before the renaming and,
after it, every axiom outside the chain-route fragment (`refuteWeaken`): a
weaker ontology without a model shows that the input has none. It then
translates the SROIQ(D) knowledge base to
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

/-- The emptiness test on given cells, readings and atom evaluation. -/
def empWith {q k : Nat} (sup : Bool) (cs : List Cell) (gs : List (Fin k → Bool))
    (E : Fin q → Cell → (Fin k → Bool) → Bool) (L : List (Fin q × Bool)) : Bool :=
  sup && cs.all fun c => gs.all fun g => !(L.all fun l => E l.1 c g == l.2)

/-- Every atom of `spec` is supported. -/
def supAll {q : Nat} (spec : Fin q → DataRange) : Bool :=
  (List.finRange q).all fun p => drSupported (spec p)

/-- A conjunction of literals is empty: no cell under any reading of the
free datatypes satisfies it (and every atom is supported). -/
def empOWL {q : Nat} (spec : Fin q → DataRange) : List (Fin q × Bool) → Bool :=
  empWith (supAll spec) (cellsOf (allBases spec)) (ContextCalculus.SRIQD.allG (allFrees spec).length)
    (owlE spec)

theorem empOWL_sound (pat : String → String → Prop) {q : Nat} (spec : Fin q → DataRange)
    (V : Type) (atom : Fin q → V → Prop) (hΘ : owlTheory pat spec V atom)
    (L : List (Fin q × Bool)) (h : empOWL spec L = true) (v : V) :
    ¬ ∀ l ∈ L, ContextCalculus.SRIQD.litSem atom l v := by
  intro hl
  simp only [empOWL, empWith, supAll, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true] at h
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

/-- `owlE` is `owlEWith` on the free datatypes and the compiled data ranges.
The route binds both before the check: through `owlEF` the compiled code
recomputes them at every call. -/
theorem owlEWith_eq {q : Nat} (spec : Fin q → DataRange) :
    owlEWith (allFrees spec) (Array.ofFn fun p => compileDR (spec p)) q Array.size_ofFn =
      owlE spec := by
  rw [owlE_eq_F]; rfl

/-- `empOWL` from the precomputed parts. -/
theorem empC_sound (pat : String → String → Prop) {q : Nat} (spec : Fin q → DataRange)
    (V : Type) (atom : Fin q → V → Prop) (hΘ : owlTheory pat spec V atom)
    (L : List (Fin q × Bool))
    (h : empWith (supAll spec) (cellsOf (allBases spec))
      (ContextCalculus.SRIQD.allG (allFrees spec).length)
      (owlEWith (allFrees spec) (Array.ofFn fun p => compileDR (spec p)) q Array.size_ofFn) L
        = true)
    (v : V) : ¬ ∀ l ∈ L, ContextCalculus.SRIQD.litSem atom l v := by
  rw [owlEWith_eq] at h
  exact empOWL_sound pat spec V atom hΘ L h v

theorem owlTheory_nonempty (pat : String → String → Prop) {q : Nat} (spec : Fin q → DataRange)
    (V : Type) (atom : Fin q → V → Prop) (hΘ : owlTheory pat spec V atom) : Nonempty V := by
  obtain ⟨e, -, -⟩ := hΘ
  exact ⟨e.symm (.bool true)⟩

/-! ## The route -/

/-! ## Weakening

A refutation needs only one direction: if a weaker ontology (every model of
`O` is one of it) has no model, `O` has none. The route drops the axioms the
chain-route translation does not handle (`HasKey`, `DisjointObjectProperties`,
`AsymmetricObjectProperty`, self axioms, ...) and keeps the rest. -/

/-- The axioms the route keeps: those of the SROIQ(D) knowledge-base
fragment, disjoint unions and datatype definitions (both rewritten by
`refutePrep`); never a key. -/
def keepAx : Axiom → Bool
  | .hasKey .. => false
  | .disjointUnion .. => true
  | .datatypeDefinition .. => true
  | ax => ax.isSROIQDKB

/-- The kept axioms. -/
def refuteWeaken (O : Ontology) : Ontology := ⟨O.axioms.filter keepAx⟩

/-- The axioms without keys. -/
def dropKeys (O : Ontology) : Ontology := ⟨O.axioms.filter Axiom.noKey⟩

theorem noKey_dropKeys {O : Ontology} : (dropKeys O).noKey = true := by
  simp [dropKeys, Ontology.noKey]

theorem model_dropKeys {DM : DatatypeMap} {Dom : Type} {O : Ontology} {I : Interp DM Dom}
    (h : OWL.Model O I) : OWL.Model (dropKeys O) I := by
  intro ax hax
  obtain ⟨hmem, hk⟩ := List.mem_filter.1 hax
  have hs := h ax hmem
  cases ax with
  | hasKey => simp [Axiom.noKey] at hk
  | _ => exact hs

theorem consistentAt_dropKeys {DM : DatatypeMap} {O : Ontology}
    (h : ConsistentAt DM O) : ConsistentAt DM (dropKeys O) := by
  obtain ⟨Dom, hD, I, hI⟩ := h
  exact ⟨Dom, hD, I, model_dropKeys hI⟩

theorem model_refuteWeaken {DM : DatatypeMap} {Dom : Type} {O : Ontology} {I : Interp DM Dom}
    (h : OWL.Model O I) : OWL.Model (refuteWeaken O) I := by
  intro ax hax
  obtain ⟨hmem, hk⟩ := List.mem_filter.1 hax
  have hs := h ax hmem
  cases ax with
  | hasKey => simp [keepAx] at hk
  | _ => exact hs

theorem consistentAt_refuteWeaken {DM : DatatypeMap} {O : Ontology}
    (h : ConsistentAt DM O) : ConsistentAt DM (refuteWeaken O) := by
  obtain ⟨Dom, hD, I, hI⟩ := h
  exact ⟨Dom, hD, I, model_refuteWeaken hI⟩

/-- The ontology before the weakening: datatype definitions unfolded (when
there are any), disjoint unions rewritten, keys dropped, anonymous individuals
renamed. -/
def refuteStage (O : Ontology) : Option Ontology :=
  (if (splitDef O.axioms).isSome then dtLoop O.axioms.length O else some O).map
    fun O' => anonOff [] (dropKeys (duOff O'))

/-- The ontology the route reads: `refuteStage`, then the kept axioms. -/
def refutePrep (O : Ontology) : Option Ontology :=
  (refuteStage O).map refuteWeaken

theorem consistentAt_refutePrep (pat : String → String → Prop) {O X : Ontology}
    (h : refutePrep O = some X) (hc : ConsistentAt (owl2MapP pat) O) :
    ConsistentAt (owl2MapP pat) X := by
  unfold refutePrep refuteStage at h
  obtain ⟨Y, hY, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨O', hO', rfl⟩ := Option.map_eq_some_iff.1 hY
  have h1 : ConsistentAt (owl2MapP pat) O' := by
    split_ifs at hO' with hs
    · exact (consistentAt_dtLoop hO').1 hc
    · cases hO'; exact hc
  have h2 := consistentAt_dropKeys ((consistentAt_duOff O').2 h1)
  exact consistentAt_refuteWeaken ((consistentAt_anonOff (W := []) noKey_dropKeys).2 h2)

/-- The refutation checked on the chain-route translation of a prepared
ontology. -/
def refuteChain (X : Ontology) (pf : SRIQN.Refute.Proof) : Bool :=
  if X.isSROIQDKB then
    match translateSHOIQD (roleOff X) [] with
    | none => false
    | some T =>
      match roleCls T X with
      | none => false
      | some E =>
        -- the cells are computed once, before the checker runs
        let sp := spec T.tab
        let sup := supAll sp
        let cs := cellsOf (allBases sp)
        let fr := allFrees sp
        let gs := ContextCalculus.SRIQD.allG fr.length
        let arr : Array CExpr := Array.ofFn fun p => compileDR (sp p)
        let Ev := owlEWith fr arr _ Array.size_ofFn
        SRIQN.Refute.refute (dosnC T (nomNames (roleOff X) []) E) (empWith sup cs gs Ev) pf
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
      exact SRIQN.Refute.refute_sound (owlTheory_nonempty pat _) (empC_sound pat (spec T.tab)) h

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
    intro hO
    exact (refuteChain_sound pat h).2 (consistentAt_refutePrep pat hX hO)
  · cases h

end ContextCalculus.OWLFrontend

#print axioms ContextCalculus.OWLFrontend.empOWL_sound
#print axioms ContextCalculus.OWLFrontend.model_refuteWeaken
#print axioms ContextCalculus.OWLFrontend.refuteChain_sound
#print axioms ContextCalculus.OWLFrontend.refuteP_sound
