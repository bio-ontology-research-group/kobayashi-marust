import ContextCalculus.OWLFrontend.DatatypeDef
import ContextCalculus.SRIQN.HintCheck
import ContextCalculus.OWLFrontend.HintSparse

/-!
# The hint-only route (stage C5, `--procedure sroiq-hint`)

`docs/V1.7.0-PLAN.md`, sections 17 and 18. The proved reference route
`sroiq-c2a` checks the C2a condition because its exhaustive search is
complete only on C2a. A hint that the proved checker accepts gives a model
on every input the translation handles (`realisation_sound` has no C2a
condition), so for certifying km's negative answers the C2a check is not
needed. This file is the route that checks only a hint:

* the fragment: every input the translations of `sroiq-c2a` handle (the
  SROIQ(D) knowledge-base part with chains, reflexive and irreflexive
  properties, `ObjectHasSelf`, `DisjointUnion`, `DatatypeDefinition`,
  anonymous individuals), with the checks of chain elimination, the Self
  encoding and the data map, and **without** the C2a condition;
* the hint: a realisation in the text format of `RawHint.toHintN`
  (`SHOIQC2aReference.lean`). Core elements may carry no nominal name
  (anonymous shared elements): `blocks K` declares `K` core elements, and a
  core element whose `ty` lines contain no nominal index is anonymous. A
  core element with children must have them checked by a certificate
  (`rec` lines) or have no children; the elimination of the C2a route is
  not run. On the Self route a core element with a loop (`lab B B ...`)
  must carry a nominal name (`loopOKH`).

The answer is `some true` exactly when the route accepts the input and the
hint checks; it is never `some false`.

What is proved (for every reading `pat` of `xsd:pattern`, every hint):

* `owlHintConsistent_sound`: `owlHintConsistent O hint = some true →
  ConsistentAt (owl2MapP pat) O`;
* six negative rows: `hintNonType_sound` (`¬ EntailsAt … ClassAssertion(C a)`),
  `hintNonSame_sound`, `hintNonSub_sound` (`¬ EntailsSubAt … A B`),
  `hintNonDiff_sound`, `hintNonRole_sound`, `hintNonNRole_sound`;
* two batch rows: `hintNonSubs_sound` (one hint refutes `A ⊑ B` for every
  `B` of a list), `hintNonTypes_sound` (one hint refutes `C(a)` for every
  `C` of a list).

What is **not** claimed: no completeness (a hint that does not check, or
an input outside the fragment, says nothing), no positive rows (those come
from `kmSupervisor_sound` or from the complete route `sroiq-c2a`).
-/

namespace ContextCalculus.OWLFrontend

open ContextCalculus.OWL ContextCalculus.OWL.Datatypes SHIQD SHOIQ

/-! ## The chain route without C2a -/

/-- **The checks** of the chain route without C2a: regularity, the
conditions of chain elimination, supported data atoms. -/
def sroiqHOK (T : SRIQDKBTranslation) (L : List IRI)
    (E : List (SRIQ.Clause (Fin T.obj.conceptCount) (Fin T.obj.roleCount))) : Bool :=
  SROIQ.Proc.regularB (objC T L E) && SROIQ.Proc.condB (objC T L E) &&
    (List.finRange T.tab.length).all fun p => drSupported (spec T.tab p)

def sroiqHOKF (T : SRIQDKBTranslation) (L : List IRI)
    (E : List (SRIQ.Clause (Fin T.obj.conceptCount) (Fin T.obj.roleCount))) : Bool :=
  let B0 := objC T L E
  let spS := specS T.tab
  SROIQ.Proc.regularB B0 && SROIQ.Proc.condB B0 &&
    (List.finRange T.tab.length).all fun p => drSupported (spS.f p)

@[csimp] theorem sroiqHOK_eq_F : @sroiqHOK = @sroiqHOKF := by
  funext T L E
  simp [sroiqHOK, sroiqHOKF, specS_f]

/-- The data part the hint names accepts it, or, when it names none, some
part of the data theory does (stage H2: the hint is read as a sparse hint,
`HF.hintPartsP`; `HF.hintPartsP_imp` reduces it to `hintPartsN` on the
denoted hint). -/
def sroiqHParts (T : SRIQDKBTranslation) (L : List IRI)
    (E : List (SRIQ.Clause (Fin T.obj.conceptCount) (Fin T.obj.roleCount)))
    (hint : RawHint) : Bool :=
  let sp := spec T.tab
  let as := allBases sp
  let cs := cellsOf as
  (hint.toHintS _ _).any fun h => SRIQN.HF.hintPartsP (encC T L E) cs (cellSize as)
    (ContextCalculus.SRIQD.splitCell cs (cellSize as) (sroiqBound T L E) (owlE sp)) (owlE sp) h

def sroiqHPartsF (T : SRIQDKBTranslation) (L : List IRI)
    (E : List (SRIQ.Clause (Fin T.obj.conceptCount) (Fin T.obj.roleCount)))
    (hint : RawHint) : Bool :=
  let spS := specS T.tab
  let sp := spS.f
  let as := allBases sp
  let cs := cellsOf as
  let szS := cellSizeS as
  let sz := szS.f
  let eS := owlES sp
  let oe := eS.f
  let bnd := ContextCalculus.SRIQD.dbnd (SRIQN.dbase (SRIQN.Proc.encTransDN (encC T L E))) *
    (ContextCalculus.SRIQD.allG (allFrees sp).length).length
  let spT := SRIQN.HF.splitTab cs sz bnd oe
  (hint.toHintS _ _).any fun h => SRIQN.HF.hintPartsP (encC T L E) cs sz
    (SRIQN.HF.lookSplit spT (ContextCalculus.SRIQD.splitCell cs sz bnd oe)) oe h

@[csimp] theorem sroiqHParts_eq_F : @sroiqHParts = @sroiqHPartsF := by
  funext T L E hint
  unfold sroiqHPartsF sroiqHParts sroiqBound
  dsimp only
  rw [specS_f]
  simp only [cellSizeS_f, owlES_f, SRIQN.HF.lookSplit_eq]

theorem owlTheory_eq (pat : String → String → Prop) {T : SRIQDKBTranslation}
    (h : (List.finRange T.tab.length).all (fun p => drSupported (spec T.tab p)) = true) :
    owlTheory pat (spec T.tab) = ContextCalculus.SRIQD.cellTheory
      (cellOf (allBases (spec T.tab))) (owlE (spec T.tab)) := by
  have hsup : ∀ p, drSupported (spec T.tab p) = true := fun p =>
    List.all_eq_true.1 h p (List.mem_finRange p)
  funext V atom
  exact propext (owlTheory_iff pat hsup V atom)

theorem sroiqHParts_sound (pat : String → String → Prop) {T : SRIQDKBTranslation} {L : List IRI}
    {E : List (SRIQ.Clause (Fin T.obj.conceptCount) (Fin T.obj.roleCount))}
    (hok : sroiqHOK T L E = true) {hint : RawHint} (hh : sroiqHParts T L E hint = true) :
    SRIQN.ConsistentDN (owlTheory pat (spec T.tab)) (dosnC T L E) := by
  simp only [sroiqHOK, Bool.and_eq_true] at hok
  obtain ⟨⟨-, h1⟩, h3⟩ := hok
  rw [owlTheory_eq pat h3, SROIQ.Proc.consistentDN_encChainDN (SROIQ.Proc.condC_of_condB h1)]
  obtain ⟨h, -, hh⟩ := (Option.any_eq_true _ _).1 hh
  exact SRIQN.hintPartsN_sound (cellSpec _) (le_refl (sroiqBound T L E))
    ContextCalculus.SRIQD.splitCell_ok.1 ContextCalculus.SRIQD.splitCell_ok.2
    (SROIQ.Proc.isSHIQD_encChainDN _) (le_refl _) (SRIQN.HF.hintPartsP_imp _ _ _ _ _ h hh)

/-- The chain route on an ontology without anonymous individuals: `none`
outside the fragment, otherwise whether the hint checks. -/
def owlChainHint (O : OWL.Ontology) (hint : RawHint) : Option Bool :=
  if O.isSROIQDKB then
    match translateSHOIQD (roleOff O) [] with
    | none => none
    | some T =>
      match roleCls T O with
      | none => none
      | some E =>
        if sroiqHOK T (nomNames (roleOff O) []) E then
          some (sroiqHParts T (nomNames (roleOff O) []) E hint)
        else none
  else none

theorem noKey_of_isSROIQDKB_O {O : Ontology} (h : O.isSROIQDKB = true) : O.noKey = true := by
  simp only [Ontology.isSROIQDKB, List.all_eq_true] at h
  simp only [Ontology.noKey, List.all_eq_true]
  exact fun ax hax => noKey_of_isSROIQDKB (h ax hax)

theorem owlChainHint_sound (pat : String → String → Prop) {O : OWL.Ontology} {hint : RawHint}
    {b : Bool} (h : owlChainHint O hint = some b) :
    O.noKey = true ∧ (b = true → ConsistentAt (owl2MapP pat) O) := by
  unfold owlChainHint at h
  split_ifs at h with hO
  refine ⟨noKey_of_isSROIQDKB_O hO, fun hb => ?_⟩
  subst hb
  split at h
  · cases h
  next T hT =>
    split at h
    · cases h
    next E hE =>
      split_ifs at h with hok
      simp only [Option.some.injEq] at h
      exact (sroiq_consistent pat hO hT hE).2 (sroiqHParts_sound pat hok h)

/-! ## The Self route without C2a -/

/-- **The checks** of the Self route without C2a: regularity, chain
elimination, simple roles of the negative self clauses, the loop roles,
supported data atoms. -/
def sroiqSHOK (T : SRIQDKBTranslation) (L : List IRI)
    (E : List (SRIQ.Clause (Fin T.obj.conceptCount) (Fin T.obj.roleCount)))
    (SC : List (SRIQN.SClause (Fin T.obj.conceptCount) (Fin T.obj.roleCount))) : Bool :=
  SROIQ.Proc.regularB (objC T L E) && SROIQ.Proc.condB (objC T L E) &&
    SROIQ.Proc.selfSimpleB (objC T L E) SC &&
    SROIQ.Proc.lamOKB (SRIQD.objPart (SRIQN.dbase (chC T L E))) (scC T L E SC) (lamC T L E SC) (irrC T L E SC) &&
    (List.finRange T.tab.length).all fun p => drSupported (spec T.tab p)

/-- `sroiqSHOK` with the loop roles computed once. -/
def sroiqSHOKF (T : SRIQDKBTranslation) (L : List IRI)
    (E : List (SRIQ.Clause (Fin T.obj.conceptCount) (Fin T.obj.roleCount)))
    (SC : List (SRIQN.SClause (Fin T.obj.conceptCount) (Fin T.obj.roleCount))) : Bool :=
  let B0 := objC T L E
  let D1 := chC T L E
  let B1 := SRIQD.objPart (SRIQN.dbase D1)
  let sc1 := scC T L E SC
  let hm1 := Std.HashMap.ofList (SROIQ.Proc.mkTab B1)
  let le1 := SROIQ.Proc.leH hm1
  let lam := SROIQ.Proc.lamOfL le1 B1 sc1
  let irr := SROIQ.Proc.irrOfL le1 sc1
  let spS := specS T.tab
  SROIQ.Proc.regularB B0 && SROIQ.Proc.condB B0 && SROIQ.Proc.selfSimpleB B0 SC &&
    SROIQ.Proc.lamOKBL le1 B1 sc1 lam irr &&
    (List.finRange T.tab.length).all fun p => drSupported (spS.f p)

@[csimp] theorem sroiqSHOK_eq_F : @sroiqSHOK = @sroiqSHOKF := by
  funext T L E SC
  simp [sroiqSHOK, sroiqSHOKF, specS_f]
  rfl

/-- `sroiqHParts` with loops at nominal core elements. -/
def sroiqSHParts (T : SRIQDKBTranslation) (L : List IRI)
    (E : List (SRIQ.Clause (Fin T.obj.conceptCount) (Fin T.obj.roleCount)))
    (SC : List (SRIQN.SClause (Fin T.obj.conceptCount) (Fin T.obj.roleCount)))
    (hint : RawHint) : Bool :=
  let sp := spec T.tab
  let as := allBases sp
  let cs := cellsOf as
  (hint.toHintS _ _).any fun h => SRIQN.HF.hintPartsNLP (encS T L E SC) cs (cellSize as)
    (ContextCalculus.SRIQD.splitCell cs (cellSize as) (sroiqSBound T L E SC) (owlE sp)) (owlE sp) h

def sroiqSHPartsF (T : SRIQDKBTranslation) (L : List IRI)
    (E : List (SRIQ.Clause (Fin T.obj.conceptCount) (Fin T.obj.roleCount)))
    (SC : List (SRIQN.SClause (Fin T.obj.conceptCount) (Fin T.obj.roleCount)))
    (hint : RawHint) : Bool :=
  let spS := specS T.tab
  let sp := spS.f
  let as := allBases sp
  let cs := cellsOf as
  let szS := cellSizeS as
  let sz := szS.f
  let eS := owlES sp
  let oe := eS.f
  let bnd := ContextCalculus.SRIQD.dbnd (SRIQN.dbase (SRIQN.Proc.encTransDN (encS T L E SC))) *
    (ContextCalculus.SRIQD.allG (allFrees sp).length).length
  let spT := SRIQN.HF.splitTab cs sz bnd oe
  (hint.toHintS _ _).any fun h => SRIQN.HF.hintPartsNLP (encS T L E SC) cs sz
    (SRIQN.HF.lookSplit spT (ContextCalculus.SRIQD.splitCell cs sz bnd oe)) oe h

@[csimp] theorem sroiqSHParts_eq_F : @sroiqSHParts = @sroiqSHPartsF := by
  funext T L E SC hint
  unfold sroiqSHPartsF sroiqSHParts sroiqSBound
  dsimp only
  rw [specS_f]
  simp only [cellSizeS_f, owlES_f, SRIQN.HF.lookSplit_eq]

theorem sroiqSHParts_sound (pat : String → String → Prop) {T : SRIQDKBTranslation} {L : List IRI}
    {E : List (SRIQ.Clause (Fin T.obj.conceptCount) (Fin T.obj.roleCount))}
    {SC : List (SRIQN.SClause (Fin T.obj.conceptCount) (Fin T.obj.roleCount))}
    (hok : sroiqSHOK T L E SC = true) {hint : RawHint} (hh : sroiqSHParts T L E SC hint = true) :
    SRIQN.ConsistentDS (owlTheory pat (spec T.tab)) (dosnC T L E) SC := by
  simp only [sroiqSHOK, Bool.and_eq_true] at hok
  obtain ⟨⟨⟨⟨-, h1⟩, h2⟩, h3⟩, h6⟩ := hok
  have hA1 : SRIQ.IsALCHIQ (SRIQD.objPart (SRIQN.dbase (chC T L E))) := by
    rw [SROIQ.Proc.dbase_encChainDN, SROIQ.Proc.objPart_encChainQD]
    exact SROIQ.Proc.encChain_isALCHIQ _
  rw [owlTheory_eq pat h6,
    SROIQ.Proc.consistentDS_encChainDN (SROIQ.Proc.condC_of_condB h1) (selfSimple_of h2)]
  obtain ⟨h, -, hh⟩ := (Option.any_eq_true _ _).1 hh
  exact SRIQN.encSelf_down (SROIQ.Proc.lamOK_of_lamOKB h3) hA1
    (SRIQN.hintPartsNL_sound (cellSpec _) (le_refl (sroiqSBound T L E SC))
      ContextCalculus.SRIQD.splitCell_ok.1 ContextCalculus.SRIQD.splitCell_ok.2
      (SRIQN.isALCHIQ_encSelfD hA1) (le_refl _) (SRIQN.HF.hintPartsNLP_imp _ _ _ _ _ h hh))

/-- The Self route on an ontology without anonymous individuals. -/
def owlSelfHint (O : OWL.Ontology) (hint : RawHint) : Option Bool :=
  if O.isSROIQDSKB && !(selfAxs O).isEmpty then
    match translateSHOIQD (roleOff (selfOff O)) [] with
    | none => none
    | some T =>
      match roleCls T (selfOff O) with
      | none => none
      | some E =>
        match selfCls T O with
        | none => none
        | some SC =>
          if sroiqSHOK T (nomNames (roleOff (selfOff O)) []) E SC then
            some (sroiqSHParts T (nomNames (roleOff (selfOff O)) []) E SC hint)
          else none
  else none

theorem owlSelfHint_sound (pat : String → String → Prop) {O : OWL.Ontology} {hint : RawHint}
    {b : Bool} (h : owlSelfHint O hint = some b) :
    O.noKey = true ∧ (b = true → ConsistentAt (owl2MapP pat) O) := by
  unfold owlSelfHint at h
  split_ifs at h with hO'
  have hO : O.isSROIQDSKB = true := (Bool.and_eq_true _ _ ▸ hO').1
  refine ⟨noKey_of_isSROIQDSKB_O hO, fun hb => ?_⟩
  subst hb
  split at h
  · cases h
  next T hT =>
    split at h
    · cases h
    next E hE =>
      split at h
      · cases h
      next SC hS =>
        split_ifs at h with hok
        simp only [Option.some.injEq] at h
        exact (sroiqS_consistent pat hO hT hE hS).2 (sroiqSHParts_sound pat hok h)

/-! ## The route with `ObjectHasSelf` in class expressions, without C2a -/

/-- The route on a rewritten ontology `O` with pairs `P`. -/
def owlHSHintOn (O : Ontology) (P : List (IRI × ObjProp)) (hint : RawHint) : Option Bool :=
  if O.isSROIQDSKB && !P.isEmpty then
    match translateSHOIQD (roleOff (selfOff O)) (pairNames P) with
    | none => none
    | some T =>
      match roleCls T (selfOff O) with
      | none => none
      | some E =>
        match selfCls T O with
        | none => none
        | some SC =>
          match pairCls T P with
          | none => none
          | some PC =>
            if sroiqSHOK T (nomNames (roleOff (selfOff O)) (pairNames P)) E (SC ++ PC) then
              some (sroiqSHParts T (nomNames (roleOff (selfOff O)) (pairNames P)) E (SC ++ PC) hint)
            else none
  else none

theorem owlHSHintOn_sound (pat : String → String → Prop) {O : Ontology} {P : List (IRI × ObjProp)}
    {hint : RawHint} {b : Bool} (h : owlHSHintOn O P hint = some b) :
    O.noKey = true ∧ (b = true → ∃ (Dom : Type) (_ : Nonempty Dom) (I : Interp (owl2MapP pat) Dom),
      OWL.Model O I ∧ PairsHold P I) := by
  unfold owlHSHintOn at h
  split_ifs at h with hO'
  have hO : O.isSROIQDSKB = true := (Bool.and_eq_true _ _ ▸ hO').1
  refine ⟨noKey_of_isSROIQDSKB_O hO, fun hb => ?_⟩
  subst hb
  split at h
  · cases h
  next T hT =>
    split at h
    · cases h
    next E hE =>
      split at h
      · cases h
      next SC hS =>
        split at h
        · cases h
        next PC hP =>
          split_ifs at h with hok
          simp only [Option.some.injEq] at h
          exact (sroiqH_consistent pat hO hT hE hS hP).2 (sroiqSHParts_sound pat hok h)

/-- The route with `ObjectHasSelf`, on an ontology without anonymous
individuals. -/
def owlHSHint (O : Ontology) (hint : RawHint) : Option Bool :=
  owlHSHintOn (hsOff O) (selfPairs O) hint

theorem owlHSHint_sound (pat : String → String → Prop) {O : Ontology} {hint : RawHint}
    {b : Bool} (h : owlHSHint O hint = some b) :
    O.noKey = true ∧ (b = true → ConsistentAt (owl2MapP pat) O) := by
  obtain ⟨hk, hc⟩ := owlHSHintOn_sound pat h
  have hk' := noKey_hsOff hk
  exact ⟨hk', fun hb => (consistentAt_hsOff hk').2 (hc hb)⟩

/-! ## The route -/

/-- The core of the hint route on an ontology without anonymous
individuals: the route with `ObjectHasSelf` when the ontology uses it,
otherwise the chain route, and the Self route when the chain route
declines (irreflexive properties, or counting over a reflexive property). -/
def hintCore (O : Ontology) (hint : RawHint) : Option Bool :=
  if !(selfPairs O).isEmpty then owlHSHint O hint
  else
    match owlChainHint O hint with
    | some b => some b
    | none => owlSelfHint O hint

theorem hintCore_sound (pat : String → String → Prop) {O : Ontology} {hint : RawHint}
    {b : Bool} (h : hintCore O hint = some b) :
    O.noKey = true ∧ (b = true → ConsistentAt (owl2MapP pat) O) := by
  unfold hintCore at h
  split_ifs at h
  · exact owlHSHint_sound pat h
  · split at h
    next b' hb =>
      simp only [Option.some.injEq] at h
      subst h
      exact owlChainHint_sound pat hb
    next => exact owlSelfHint_sound pat h

/-- The hint route on an ontology without datatype definitions: disjoint
unions rewritten, anonymous individuals renamed. -/
def hintP0 (O : Ontology) (hint : RawHint) : Option Bool :=
  hintCore (anonOff [] (duOff O)) hint

theorem hintP0_sound (pat : String → String → Prop) {O : Ontology} {hint : RawHint}
    (h : hintP0 O hint = some true) : ConsistentAt (owl2MapP pat) O := by
  obtain ⟨hk, hc⟩ := hintCore_sound pat h
  rw [← consistentAt_duOff, ← consistentAt_anonOff (noKey_of_anonOffK hk)]
  exact hc rfl

/-- **The hint route**: datatype definitions unfolded (when there are any),
then `hintP0`. `none` outside the fragment; `some b` with `b` whether the
hint checks. -/
def hintP (O : Ontology) (hint : RawHint) : Option Bool :=
  if (splitDef O.axioms).isSome then
    match dtLoop O.axioms.length O with
    | some O' => hintP0 O' hint
    | none => none
  else hintP0 O hint

theorem hintP_sound (pat : String → String → Prop) {O : Ontology} {hint : RawHint}
    (h : hintP O hint = some true) : ConsistentAt (owl2MapP pat) O := by
  unfold hintP at h
  split_ifs at h
  · split at h
    next O' hO' => exact (consistentAt_dtLoop hO').2 (hintP0_sound pat h)
    next => cases h
  · exact hintP0_sound pat h

/-- **Consistency by a hint**: `some true` when the route accepts the input
and the hint checks, `none` otherwise (never `some false`). -/
def owlHintConsistent (O : Ontology) (hint : RawHint) : Option Bool :=
  match hintP O hint with
  | some true => some true
  | _ => none

/-- **Soundness of the hint route**, for every reading of `xsd:pattern` and
every hint, on every input (no C2a condition). -/
theorem owlHintConsistent_sound (pat : String → String → Prop) {O : Ontology} {hint : RawHint}
    (h : owlHintConsistent O hint = some true) : ConsistentAt (owl2MapP pat) O := by
  unfold owlHintConsistent at h
  split at h
  next hP => exact hintP_sound pat hP
  next => cases h

theorem owlHintConsistent_some {O : Ontology} {hint : RawHint} {b : Bool}
    (h : owlHintConsistent O hint = some b) : b = true := by
  unfold owlHintConsistent at h
  split at h
  · simp only [Option.some.injEq] at h; exact h.symm
  · cases h

/-! ## Negative rows -/

/-- A negative row: the extension of `O` by `L` is consistent by the hint. -/
def hintRow (O : Ontology) (L : List Axiom) (hint : RawHint) : Option Bool :=
  if (addAxs O L).noKey then owlHintConsistent (addAxs O L) hint else none

theorem hintRow_of {O : Ontology} {L : List Axiom} {hint : RawHint} (pat : String → String → Prop)
    (h : hintRow O L hint = some true) :
    O.noKey = true ∧ (∀ ax ∈ L, ax.noKey = true) ∧ ConsistentAt (owl2MapP pat) (addAxs O L) := by
  unfold hintRow at h
  split_ifs at h with hk
  rw [noKey_addAxs, Bool.and_eq_true, List.all_eq_true] at hk
  exact ⟨hk.1, hk.2, owlHintConsistent_sound pat h⟩

/-- A model of the extension, as a model of `O` that satisfies `L`. -/
theorem model_of_hintRow {O : Ontology} {L : List Axiom} {hint : RawHint}
    (pat : String → String → Prop) (h : hintRow O L hint = some true) :
    ∃ (Dom : Type) (_ : Nonempty Dom) (I : Interp (owl2MapP pat) Dom),
      OWL.Model O I ∧ ∀ ax ∈ L, I.sat [] ax := by
  obtain ⟨hO, hL, Dom, hD, I, hI⟩ := hintRow_of pat h
  exact ⟨Dom, hD, I, (model_addAxs_noKey hO hL I).1 hI⟩

def hintNonType (O : Ontology) (C a : IRI) (hint : RawHint) : Option Bool :=
  hintRow O (typeAxs C a) hint

def hintNonSame (O : Ontology) (a b : IRI) (hint : RawHint) : Option Bool :=
  hintRow O (sameAxs a b) hint

def hintNonSub (O : Ontology) (A B : IRI) (hint : RawHint) : Option Bool :=
  hintRow O (subAxs O A B) hint

def hintNonDiff (O : Ontology) (a b : IRI) (hint : RawHint) : Option Bool :=
  hintRow O (diffAxs a b) hint

def hintNonRole (O : Ontology) (r : ObjProp) (a b : IRI) (hint : RawHint) : Option Bool :=
  hintRow O (roleAxs r a b) hint

def hintNonNRole (O : Ontology) (r : ObjProp) (a b : IRI) (hint : RawHint) : Option Bool :=
  hintRow O (nroleAxs r a b) hint

/-- **Non-type row**: `O ⊭ ClassAssertion(C a)`. -/
theorem hintNonType_sound (pat : String → String → Prop) {O : Ontology} {C a : IRI}
    {hint : RawHint} (h : hintNonType O C a hint = some true) :
    ¬ EntailsAt (owl2MapP pat) O (.classAssertion (.cls C) (.named a)) := by
  obtain ⟨Dom, hD, I, hI, hs⟩ := model_of_hintRow pat h
  intro he
  have := he Dom I hI
  simp only [typeAxs, List.mem_singleton, forall_eq, Interp.sat, Interp.ext] at hs this
  exact hs this

/-- **Non-same row**: `O ⊭ SameIndividual(a b)`. -/
theorem hintNonSame_sound (pat : String → String → Prop) {O : Ontology} {a b : IRI}
    {hint : RawHint} (h : hintNonSame O a b hint = some true) :
    ¬ EntailsAt (owl2MapP pat) O (.sameIndividual [.named a, .named b]) := by
  obtain ⟨Dom, hD, I, hI, hs⟩ := model_of_hintRow pat h
  intro he
  have := (sat_same I _ a b).1 (he Dom I hI)
  simp only [sameAxs, List.mem_singleton, forall_eq] at hs
  exact (sat_diff I _ a b).1 hs this

/-- **Non-subsumption row**: `O ⊭ A ⊑ B`. -/
theorem hintNonSub_sound (pat : String → String → Prop) {O : Ontology} {A B : IRI}
    {hint : RawHint} (h : hintNonSub O A B hint = some true) :
    ¬ EntailsSubAt (owl2MapP pat) O A B := by
  obtain ⟨Dom, hD, I, hI, hs⟩ := model_of_hintRow pat h
  intro he
  simp only [subAxs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    Interp.sat, Interp.ext] at hs
  exact hs.2 (he Dom I hI _ hs.1)

/-- **Non-difference row**: `O ⊭ DifferentIndividuals(a b)`. -/
theorem hintNonDiff_sound (pat : String → String → Prop) {O : Ontology} {a b : IRI}
    {hint : RawHint} (h : hintNonDiff O a b hint = some true) :
    ¬ EntailsAt (owl2MapP pat) O (.differentIndividuals [.named a, .named b]) := by
  obtain ⟨Dom, hD, I, hI, hs⟩ := model_of_hintRow pat h
  intro he
  have hd : I.sat (Axiom.differentIndividuals [.named a, .named b]).namedIndividuals
      (.differentIndividuals [.named a, .named b]) ↔
      ¬ I.ind (.named a) = I.ind (.named b) := by simp [Interp.sat]
  simp only [diffAxs, List.mem_singleton, forall_eq] at hs
  exact hd.1 (he Dom I hI) ((sat_same I _ a b).1 hs)

/-- **Non-role row**: `O ⊭ ObjectPropertyAssertion(r a b)`. -/
theorem hintNonRole_sound (pat : String → String → Prop) {O : Ontology} {r : ObjProp} {a b : IRI}
    {hint : RawHint} (h : hintNonRole O r a b hint = some true) :
    ¬ EntailsAt (owl2MapP pat) O (.objectPropertyAssertion r (.named a) (.named b)) := by
  obtain ⟨Dom, hD, I, hI, hs⟩ := model_of_hintRow pat h
  intro he
  simp only [roleAxs, List.mem_singleton, forall_eq, Interp.sat] at hs
  exact hs (he Dom I hI)

/-- **Non-negative-role row**: `O ⊭ NegativeObjectPropertyAssertion(r a b)`. -/
theorem hintNonNRole_sound (pat : String → String → Prop) {O : Ontology} {r : ObjProp}
    {a b : IRI} {hint : RawHint} (h : hintNonNRole O r a b hint = some true) :
    ¬ EntailsAt (owl2MapP pat) O (.negativeObjectPropertyAssertion r (.named a) (.named b)) := by
  obtain ⟨Dom, hD, I, hI, hs⟩ := model_of_hintRow pat h
  intro he
  simp only [nroleAxs, List.mem_singleton, forall_eq, Interp.sat] at hs
  exact he Dom I hI hs

/-! ## Batch rows: one hint for many non-entailments -/

/-- The assertions of a batch non-subsumption row: a fresh individual in `A`
and in the complement of every `B` of `Bs`. -/
def nonSubsAxs (O : Ontology) (A : IRI) (Bs : List IRI) : List Axiom :=
  .classAssertion (.cls A) (.named (freshInd O)) ::
    Bs.map fun B => .classAssertion (.not (.cls B)) (.named (freshInd O))

/-- The assertions of a batch non-type row: `a` in the complement of every
`C` of `Cs`. -/
def nonTypesAxs (a : IRI) (Cs : List IRI) : List Axiom :=
  Cs.map fun C => .classAssertion (.not (.cls C)) (.named a)

def hintNonSubs (O : Ontology) (A : IRI) (Bs : List IRI) (hint : RawHint) : Option Bool :=
  hintRow O (nonSubsAxs O A Bs) hint

def hintNonTypes (O : Ontology) (a : IRI) (Cs : List IRI) (hint : RawHint) : Option Bool :=
  hintRow O (nonTypesAxs a Cs) hint

/-- **Batch non-subsumption row**: `O ⊭ A ⊑ B` for every `B` of `Bs`. -/
theorem hintNonSubs_sound (pat : String → String → Prop) {O : Ontology} {A : IRI}
    {Bs : List IRI} {hint : RawHint} (h : hintNonSubs O A Bs hint = some true) :
    ∀ B ∈ Bs, ¬ EntailsSubAt (owl2MapP pat) O A B := by
  obtain ⟨Dom, hD, I, hI, hs⟩ := model_of_hintRow pat h
  intro B hB he
  have h1 := hs _ (List.mem_cons_self ..)
  have h2 := hs _ (List.mem_cons_of_mem _ (List.mem_map_of_mem (f := fun B =>
    Axiom.classAssertion (.not (.cls B)) (.named (freshInd O))) hB))
  simp only [Interp.sat, Interp.ext] at h1 h2
  exact h2 (he Dom I hI _ h1)

/-- **Batch non-type row**: `O ⊭ ClassAssertion(C a)` for every `C` of `Cs`. -/
theorem hintNonTypes_sound (pat : String → String → Prop) {O : Ontology} {a : IRI}
    {Cs : List IRI} {hint : RawHint} (h : hintNonTypes O a Cs hint = some true) :
    ∀ C ∈ Cs, ¬ EntailsAt (owl2MapP pat) O (.classAssertion (.cls C) (.named a)) := by
  obtain ⟨Dom, hD, I, hI, hs⟩ := model_of_hintRow pat h
  intro C hC he
  have h2 := hs _ (List.mem_map_of_mem (f := fun C =>
    Axiom.classAssertion (.not (.cls C)) (.named a)) hC)
  have := he Dom I hI
  simp only [Interp.sat, Interp.ext] at h2 this
  exact h2 this

end ContextCalculus.OWLFrontend

#print axioms ContextCalculus.OWLFrontend.owlHintConsistent_sound
#print axioms ContextCalculus.OWLFrontend.sroiqHParts_sound
#print axioms ContextCalculus.OWLFrontend.sroiqSHParts_sound
#print axioms ContextCalculus.OWLFrontend.sroiqHOK_eq_F
#print axioms ContextCalculus.OWLFrontend.sroiqHParts_eq_F
#print axioms ContextCalculus.OWLFrontend.sroiqSHOK_eq_F
#print axioms ContextCalculus.OWLFrontend.sroiqSHParts_eq_F
#print axioms ContextCalculus.OWLFrontend.hintNonType_sound
#print axioms ContextCalculus.OWLFrontend.hintNonSame_sound
#print axioms ContextCalculus.OWLFrontend.hintNonSub_sound
#print axioms ContextCalculus.OWLFrontend.hintNonDiff_sound
#print axioms ContextCalculus.OWLFrontend.hintNonRole_sound
#print axioms ContextCalculus.OWLFrontend.hintNonNRole_sound
#print axioms ContextCalculus.OWLFrontend.hintNonSubs_sound
#print axioms ContextCalculus.OWLFrontend.hintNonTypes_sound
