import ContextCalculus.OWLFrontend.DisjointUnion
import ContextCalculus.SRIQN.ZeroAtMost

/-!
# The chain route with at-most-zero restrictions as universals (stage C3d)

When `owlC3Consistent` declines, `owlC3ZConsistent` runs the chain route of
`SROIQDC2aReference.lean` with the at-most-zero clauses of the encoding
rewritten to universals (`SRIQN.encZeroD`), which leaves them out of the
C2a condition. Inputs that the previous routes accept keep their answer
and their hint indices.

* `sroiqZParts_iff`: the decision on the rewritten encoding, exact under
  the checks `sroiqZOK`.
* `owlC3ZConsistent_sound`, `owlC3ZConsistent_isSome_iff`, and the type row
  `owlC3ZTypeRow_sound`.
-/

namespace ContextCalculus.OWLFrontend

open ContextCalculus.OWL ContextCalculus.OWL.Datatypes SHIQD SHOIQ

/-- The encoding with the at-most-zero clauses rewritten. -/
abbrev encZ (T : SRIQDKBTranslation) (L : List IRI)
    (E : List (SRIQ.Clause (Fin T.obj.conceptCount) (Fin T.obj.roleCount))) :=
  SRIQN.encZeroD (encC T L E)

/-- **The checks**: regularity, chain elimination, C2a of the rewritten
encoding, supported data atoms. -/
def sroiqZOK (T : SRIQDKBTranslation) (L : List IRI)
    (E : List (SRIQ.Clause (Fin T.obj.conceptCount) (Fin T.obj.roleCount))) : Bool :=
  SROIQ.Proc.regularB (objC T L E) && SROIQ.Proc.condB (objC T L E) &&
    decide (SRIQN.IsC2aD (SRIQN.Proc.encTransDN (encZ T L E))) &&
    (List.finRange T.tab.length).all fun p => drSupported (spec T.tab p)

def sroiqZBound (T : SRIQDKBTranslation) (L : List IRI)
    (E : List (SRIQ.Clause (Fin T.obj.conceptCount) (Fin T.obj.roleCount))) : Nat :=
  ContextCalculus.SRIQD.dbnd (SRIQN.dbase (SRIQN.Proc.encTransDN (encZ T L E))) *
    (ContextCalculus.SRIQD.allG (allFrees (spec T.tab)).length).length

def sroiqZParts (T : SRIQDKBTranslation) (L : List IRI)
    (E : List (SRIQ.Clause (Fin T.obj.conceptCount) (Fin T.obj.roleCount)))
    (hint : Option RawHint) : Bool :=
  let sp := spec T.tab
  let as := allBases sp
  let cs := cellsOf as
  SRIQN.consistentPartsN (encZ T L E) cs (cellSize as)
    (ContextCalculus.SRIQD.splitCell cs (cellSize as) (sroiqZBound T L E) (owlE sp)) (owlE sp)
    (hint.bind fun h => h.toHintN _ _)

theorem sroiqZParts_iff (pat : String → String → Prop) {T : SRIQDKBTranslation} {L : List IRI}
    {E : List (SRIQ.Clause (Fin T.obj.conceptCount) (Fin T.obj.roleCount))}
    (hok : sroiqZOK T L E = true) (hint : Option RawHint) :
    sroiqZParts T L E hint = true ↔
      SRIQN.ConsistentDN (owlTheory pat (spec T.tab)) (dosnC T L E) := by
  simp only [sroiqZOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨-, h1⟩, h2⟩, h3⟩ := hok
  have hsup : ∀ p, drSupported (spec T.tab p) = true := fun p =>
    List.all_eq_true.1 h3 p (List.mem_finRange p)
  have heq : owlTheory pat (spec T.tab) = ContextCalculus.SRIQD.cellTheory
      (cellOf (allBases (spec T.tab))) (owlE (spec T.tab)) := by
    funext V atom
    exact propext (owlTheory_iff pat hsup V atom)
  have hA1 : SRIQ.IsALCHIQ (SRIQD.objPart (SRIQN.dbase (encC T L E))) := by
    rw [SROIQ.Proc.dbase_encChainDN, SROIQ.Proc.objPart_encChainQD]
    exact SROIQ.Proc.encChain_isALCHIQ _
  rw [heq, SROIQ.Proc.consistentDN_encChainDN (SROIQ.Proc.condC_of_condB h1),
    SRIQN.consistentDN_encZeroD]
  exact SRIQN.consistentPartsN_iff (cellSpec _) (le_refl (sroiqZBound T L E))
    ContextCalculus.SRIQD.splitCell_ok.1 ContextCalculus.SRIQD.splitCell_ok.2
    (isSHIQD_of_isALCHIQ (SRIQN.isALCHIQ_encZeroD _ hA1)) (le_refl _) h2 _

/-- The route on an ontology without anonymous individuals. -/
def owlZeroCore (O : OWL.Ontology) (hint : Option RawHint) : Option Bool :=
  if O.isSROIQDKB then
    match translateSHOIQD (roleOff O) [] with
    | none => none
    | some T =>
      match roleCls T O with
      | none => none
      | some E =>
        if sroiqZOK T (nomNames (roleOff O) []) E then
          some (sroiqZParts T (nomNames (roleOff O) []) E hint)
        else none
  else none

theorem owlZeroCore_sound (pat : String → String → Prop) {O : OWL.Ontology}
    {hint : Option RawHint} {v : Bool} (h : owlZeroCore O hint = some v) :
    v = true ↔ ConsistentAt (owl2MapP pat) O := by
  unfold owlZeroCore at h
  split_ifs at h with hO
  split at h
  · cases h
  next T hT =>
    split at h
    · cases h
    next E hE =>
      split_ifs at h with hok
      simp only [Option.some.injEq] at h
      subst h
      rw [sroiqZParts_iff pat hok, ← sroiq_consistent pat hO hT hE]

/-- The checks of the route on the translation. -/
def ZeroChecks (O : OWL.Ontology) : Prop :=
  ∀ T, translateSHOIQD (roleOff O) [] = some T →
    ∃ E, roleCls T O = some E ∧ sroiqZOK T (nomNames (roleOff O) []) E = true

theorem owlZeroCore_isSome_iff (O : OWL.Ontology) (hint : Option RawHint) :
    (owlZeroCore O hint).isSome = true ↔ O.isSROIQDKB = true ∧ ZeroChecks O := by
  constructor
  · intro h
    unfold owlZeroCore at h
    split_ifs at h with hO
    · refine ⟨hO, fun T' hT' => ?_⟩
      split at h
      · simp at h
      next T hT =>
        rw [hT] at hT'; cases hT'
        split at h
        · simp at h
        next E hE =>
          split_ifs at h with hok
          · exact ⟨E, hE, hok⟩
          · simp at h
    · simp at h
  · rintro ⟨hO, hc⟩
    obtain ⟨T, hT⟩ := Option.isSome_iff_exists.1
      (translateSHOIQD_isSome (roleOff_isSHOIQDKB hO) [])
    obtain ⟨E, hE, hok⟩ := hc T hT
    unfold owlZeroCore
    rw [if_pos hO, hT]
    dsimp only
    rw [hE]
    dsimp only
    rw [if_pos hok]
    rfl

/-- **Consistency** (stage C3d): `owlC3Consistent`, and when it declines,
the chain route with the at-most-zero clauses rewritten. -/
def owlC3ZConsistent (O : Ontology) (hint : Option RawHint) : Option Bool :=
  match owlC3Consistent O hint with
  | some v => some v
  | none => owlZeroCore (anonOff [] (duOff O)) hint

theorem owlC3ZConsistent_sound (pat : String → String → Prop) {O : Ontology}
    {hint : Option RawHint} {v : Bool} (h : owlC3ZConsistent O hint = some v) :
    v = true ↔ ConsistentAt (owl2MapP pat) O := by
  unfold owlC3ZConsistent at h
  split at h
  next v' hv =>
    simp only [Option.some.injEq] at h
    subst h
    exact owlC3Consistent_sound pat hv
  next =>
    have hk : (duOff O).noKey = true := noKey_of_anonOff
      ((owlZeroCore_isSome_iff _ hint).1 (by rw [h]; rfl)).1
    rw [owlZeroCore_sound pat h, consistentAt_anonOff hk, consistentAt_duOff]

theorem owlC3ZConsistent_isSome_iff (O : Ontology) (hint : Option RawHint) :
    (owlC3ZConsistent O hint).isSome = true ↔
      (owlC3Consistent O hint).isSome = true ∨
        ((anonOff [] (duOff O)).isSROIQDKB = true ∧ ZeroChecks (anonOff [] (duOff O))) := by
  rw [← owlZeroCore_isSome_iff _ hint]
  unfold owlC3ZConsistent
  cases owlC3Consistent O hint <;> simp

/-! ## The type row -/

/-- A row of the route: the negated consistency of the extension. -/
def rowZ (O : OWL.Ontology) (L : List Axiom) (hint : Option RawHint) : Option Bool :=
  (owlZeroCore (addAxs O L) hint).map (!·)

theorem rowZ_of {O : Ontology} {L : List Axiom} {hint : Option RawHint} {v : Bool}
    (pat : String → String → Prop) (h : rowZ O L hint = some v) :
    O.isSROIQDKB = true ∧ (∀ ax ∈ L, ax.isSROIQDKB = true) ∧
      (v = true ↔ ¬ ConsistentAt (owl2MapP pat) (addAxs O L)) := by
  obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.1 h
  have hk : (addAxs O L).isSROIQDKB = true :=
    ((owlZeroCore_isSome_iff (addAxs O L) hint).1 (by rw [hw]; rfl)).1
  rw [isSROIQDKB_addAxs, Bool.and_eq_true, List.all_eq_true] at hk
  refine ⟨hk.1, hk.2, ?_⟩
  rw [← owlZeroCore_sound pat hw]
  cases w <;> simp

/-- **Type row** (stage C3d). -/
def owlC3ZTypeRow (O : Ontology) (C a : IRI) (hint : Option RawHint) : Option Bool :=
  match owlC3TypeRow O C a hint with
  | some v => some v
  | none => rowZ (anonOff [a] (duOff O)) (typeAxs C a) hint

theorem owlC3ZTypeRow_sound (pat : String → String → Prop) {O : Ontology} {C a : IRI}
    {hint : Option RawHint} {v : Bool} (h : owlC3ZTypeRow O C a hint = some v) :
    v = true ↔ EntailsAt (owl2MapP pat) O (.classAssertion (.cls C) (.named a)) := by
  unfold owlC3ZTypeRow at h
  split at h
  next v' hv =>
    simp only [Option.some.injEq] at h; subst h
    exact owlC3TypeRow_sound pat hv
  next =>
    obtain ⟨hO, hL, hv⟩ := rowZ_of pat h
    have hk := noKey_of_anonOff hO
    rw [← entailsAt_duOff, ← entailsAt_anonOff (W := [a]) hk (by
      simp only [Axiom.mapI, ClassExpr.mapI, anonG_fix (List.mem_singleton_self a)]) rfl,
      hv, consistentAt_iff_not, not_not]
    constructor
    · intro hi Dom _ I hI
      by_contra hc
      refine hi Dom I ((model_addAxsS hO hL I).2 ⟨hI, ?_⟩)
      simpa [typeAxs, Interp.sat, Interp.ext] using hc
    · intro he Dom _ I hI
      obtain ⟨hI, hs⟩ := (model_addAxsS hO hL I).1 hI
      have := he Dom I hI
      simp only [typeAxs, List.mem_singleton, forall_eq, Interp.sat, Interp.ext] at hs this
      exact hs this

end ContextCalculus.OWLFrontend

#print axioms ContextCalculus.OWLFrontend.sroiqZParts_iff
#print axioms ContextCalculus.OWLFrontend.owlC3ZConsistent_sound
#print axioms ContextCalculus.OWLFrontend.owlC3ZConsistent_isSome_iff
#print axioms ContextCalculus.OWLFrontend.owlC3ZTypeRow_sound
