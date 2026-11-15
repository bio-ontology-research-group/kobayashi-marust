import ContextCalculus.OWLFrontend.HintRoute

/-!
# Batch form of the hint route (stage C5, item 2)

The hint producer checks many hints per input. `hintPB O hs` checks a list
of hints against one ontology: the translation, the chain and Self
encodings, the transitivity encoding of the encoded ontology, its object
part and the data parts are computed once (bound as data values before the
loop over the hints), and each hint runs only `checkRedN` and the data-star
tests. `hintPB_eq` proves it equal to the per-hint route:

```
hintPB O hs = hs.map (hintP O)
```

so every result carries the soundness of `hintP` (`hintP_sound`) unchanged.

Rows (`HintRowSpec`): the consistency row and the negative rows of
`HintRoute.lean`. `hintRowsB O r hs = hs.map (hintRowAns O r)`
(`hintRowsB_eq`): the hints of one row share the translation of the
extended ontology. Rows with different added axioms have different
translations; sharing between them is not done.
-/

namespace ContextCalculus.SRIQN

open ContextCalculus.SRIQD (partsOf toPart partCard)

variable {Val K : Type} [DecidableEq K] {q s : Nat}
variable {n m p : Nat}

/-- `hintPartsN` over a list of hints, the encodings computed once. -/
def hintPartsNB (O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)) (cells : List K)
    (size : K → Option Nat) (sp : K → Bool) (E : Fin q → K → (Fin s → Bool) → Bool)
    (hs : List (Option (Proc.HintN (n + Proc.encKD O) m))) : List Bool :=
  let D := Proc.encTransDN O
  let Db := dbase D
  let A := SRIQD.objPart Db
  let N := dnoms D
  let xs := (partsOf size s (cells.filter sp)).map fun x => toPart s x
  hs.map fun h => h.any fun h =>
    let noKids := (List.finRange h.k).all (fun b => (h.kids b).isEmpty)
    (decide (0 < h.k ∧ Proc.coreOKN N h.ty h.lab ∧
        ∀ b, SRIQ.StarOK A (h.ty b) (SRIQ.Proc.nbrsL h.ty h.lab b ++ h.kids b)) &&
      (noKids || decide (Proc.CertOK A N h))) &&
    xs.any fun x =>
      let ok := SRIQD.Proc.dataSatB Db (partCard cells size sp E x)
      (List.finRange h.k).all (fun b => ok (h.ty b)) && (noKids || h.recs.all (fun e => ok e.1.1))

theorem hintPartsNB_eq (O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)) (cells : List K)
    (size : K → Option Nat) (sp : K → Bool) (E : Fin q → K → (Fin s → Bool) → Bool)
    (hs : List (Option (Proc.HintN (n + Proc.encKD O) m))) :
    hintPartsNB O cells size sp E hs = hs.map fun h => h.any (hintPartsN O cells size sp E) := by
  simp only [hintPartsNB, List.any_map, Function.comp_def, hintPartsN_eq_F]
  rfl

/-- `hintPartsNL` over a list of hints, the encodings computed once. -/
def hintPartsNLB (O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)) (cells : List K)
    (size : K → Option Nat) (sp : K → Bool) (E : Fin q → K → (Fin s → Bool) → Bool)
    (hs : List (Option (Proc.HintN (n + Proc.encKD O) m))) : List Bool :=
  let D := Proc.encTransDN O
  let Db := dbase D
  let A := SRIQD.objPart Db
  let N := dnoms D
  let xs := (partsOf size s (cells.filter sp)).map fun x => toPart s x
  hs.map fun h => h.any fun h =>
    let noKids := (List.finRange h.k).all (fun b => (h.kids b).isEmpty)
    Proc.loopOKH N h &&
    ((decide (0 < h.k ∧ Proc.coreOKN N h.ty h.lab ∧
        ∀ b, SRIQ.StarOK A (h.ty b) (SRIQ.Proc.nbrsL h.ty h.lab b ++ h.kids b)) &&
      (noKids || decide (Proc.CertOK A N h))) &&
    xs.any fun x =>
      let ok := SRIQD.Proc.dataSatB Db (partCard cells size sp E x)
      (List.finRange h.k).all (fun b => ok (h.ty b)) && (noKids || h.recs.all (fun e => ok e.1.1)))

theorem hintPartsNLB_eq (O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)) (cells : List K)
    (size : K → Option Nat) (sp : K → Bool) (E : Fin q → K → (Fin s → Bool) → Bool)
    (hs : List (Option (Proc.HintN (n + Proc.encKD O) m))) :
    hintPartsNLB O cells size sp E hs = hs.map fun h => h.any (hintPartsNL O cells size sp E) := by
  simp only [hintPartsNLB, List.any_map, Function.comp_def, hintPartsNL_eq_F]
  rfl

end ContextCalculus.SRIQN

namespace ContextCalculus.OWLFrontend

open ContextCalculus.OWL ContextCalculus.OWL.Datatypes SHIQD SHOIQ

/-! ## The cores over a list of hints -/

def sroiqHPartsB (T : SRIQDKBTranslation) (L : List IRI)
    (E : List (SRIQ.Clause (Fin T.obj.conceptCount) (Fin T.obj.roleCount)))
    (hs : List RawHint) : List Bool :=
  let sp := spec T.tab
  let as := allBases sp
  let cs := cellsOf as
  let D := encC T L E
  SRIQN.hintPartsNB D cs (cellSize as)
    (ContextCalculus.SRIQD.splitCell cs (cellSize as) (sroiqBound T L E) (owlE sp)) (owlE sp)
    (hs.map fun h => h.toHintN _ _)

theorem sroiqHPartsB_eq (T : SRIQDKBTranslation) (L : List IRI)
    (E : List (SRIQ.Clause (Fin T.obj.conceptCount) (Fin T.obj.roleCount))) (hs : List RawHint) :
    sroiqHPartsB T L E hs = hs.map (sroiqHParts T L E) := by
  simp only [sroiqHPartsB, SRIQN.hintPartsNB_eq, List.map_map, Function.comp_def]
  rfl

/-- `sroiqHPartsB` over the sparse forms of the hints (stage H2). -/
def sroiqHPartsBF (T : SRIQDKBTranslation) (L : List IRI)
    (E : List (SRIQ.Clause (Fin T.obj.conceptCount) (Fin T.obj.roleCount)))
    (hs : List RawHint) : List Bool :=
  let sp := spec T.tab
  let as := allBases sp
  let cs := cellsOf as
  let D := encC T L E
  SRIQN.HF.hintPartsSB D cs (cellSize as)
    (ContextCalculus.SRIQD.splitCell cs (cellSize as) (sroiqBound T L E) (owlE sp)) (owlE sp) false
    (hs.map fun h => h.toHintS _ _)

@[csimp] theorem sroiqHPartsB_eq_F : @sroiqHPartsB = @sroiqHPartsBF := by
  funext T L E hs
  rw [sroiqHPartsB_eq]
  unfold sroiqHPartsBF
  rw [(SRIQN.HF.hintPartsSB_eq _ _ _ _ _ _).1, List.map_map]
  refine List.map_congr_left fun h _ => ?_
  rw [sroiqHParts_eq_F]
  rfl

def sroiqSHPartsB (T : SRIQDKBTranslation) (L : List IRI)
    (E : List (SRIQ.Clause (Fin T.obj.conceptCount) (Fin T.obj.roleCount)))
    (SC : List (SRIQN.SClause (Fin T.obj.conceptCount) (Fin T.obj.roleCount)))
    (hs : List RawHint) : List Bool :=
  let sp := spec T.tab
  let as := allBases sp
  let cs := cellsOf as
  let D := encS T L E SC
  SRIQN.hintPartsNLB D cs (cellSize as)
    (ContextCalculus.SRIQD.splitCell cs (cellSize as) (sroiqSBound T L E SC) (owlE sp)) (owlE sp)
    (hs.map fun h => h.toHintN _ _)

theorem sroiqSHPartsB_eq (T : SRIQDKBTranslation) (L : List IRI)
    (E : List (SRIQ.Clause (Fin T.obj.conceptCount) (Fin T.obj.roleCount)))
    (SC : List (SRIQN.SClause (Fin T.obj.conceptCount) (Fin T.obj.roleCount)))
    (hs : List RawHint) :
    sroiqSHPartsB T L E SC hs = hs.map (sroiqSHParts T L E SC) := by
  simp only [sroiqSHPartsB, SRIQN.hintPartsNLB_eq, List.map_map, Function.comp_def]
  rfl

/-- `sroiqSHPartsB` over the sparse forms of the hints (stage H2). -/
def sroiqSHPartsBF (T : SRIQDKBTranslation) (L : List IRI)
    (E : List (SRIQ.Clause (Fin T.obj.conceptCount) (Fin T.obj.roleCount)))
    (SC : List (SRIQN.SClause (Fin T.obj.conceptCount) (Fin T.obj.roleCount)))
    (hs : List RawHint) : List Bool :=
  let sp := spec T.tab
  let as := allBases sp
  let cs := cellsOf as
  let D := encS T L E SC
  SRIQN.HF.hintPartsSB D cs (cellSize as)
    (ContextCalculus.SRIQD.splitCell cs (cellSize as) (sroiqSBound T L E SC) (owlE sp)) (owlE sp) true
    (hs.map fun h => h.toHintS _ _)

@[csimp] theorem sroiqSHPartsB_eq_F : @sroiqSHPartsB = @sroiqSHPartsBF := by
  funext T L E SC hs
  rw [sroiqSHPartsB_eq]
  unfold sroiqSHPartsBF
  rw [(SRIQN.HF.hintPartsSB_eq _ _ _ _ _ _).2, List.map_map]
  refine List.map_congr_left fun h _ => ?_
  rw [sroiqSHParts_eq_F]
  rfl

def owlChainHintB (O : OWL.Ontology) (hs : List RawHint) : List (Option Bool) :=
  if O.isSROIQDKB then
    match translateSHOIQD (roleOff O) [] with
    | none => hs.map fun _ => none
    | some T =>
      match roleCls T O with
      | none => hs.map fun _ => none
      | some E =>
        if sroiqHOK T (nomNames (roleOff O) []) E then
          (sroiqHPartsB T (nomNames (roleOff O) []) E hs).map some
        else hs.map fun _ => none
  else hs.map fun _ => none

theorem owlChainHintB_eq (O : OWL.Ontology) (hs : List RawHint) :
    owlChainHintB O hs = hs.map (owlChainHint O) := by
  unfold owlChainHintB owlChainHint
  by_cases hO : O.isSROIQDKB = true
  · simp only [hO, if_true]
    cases translateSHOIQD (roleOff O) [] with
    | none => simp
    | some T =>
      simp only
      cases roleCls T O with
      | none => simp
      | some E =>
        simp only
        by_cases hok : sroiqHOK T (nomNames (roleOff O) []) E = true
        · simp [hok, sroiqHPartsB_eq, List.map_map, Function.comp_def]
        · simp [hok]
  · simp [hO]

/-- Whether `owlChainHint` answers does not depend on the hint. -/
theorem owlChainHint_isSome (O : OWL.Ontology) (h h' : RawHint) :
    (owlChainHint O h).isSome = (owlChainHint O h').isSome := by
  unfold owlChainHint
  by_cases hO : O.isSROIQDKB = true
  · simp only [hO, if_true]
    cases translateSHOIQD (roleOff O) [] with
    | none => rfl
    | some T =>
      simp only
      cases roleCls T O with
      | none => rfl
      | some E =>
        simp only
        by_cases hok : sroiqHOK T (nomNames (roleOff O) []) E = true
        · simp [hok]
        · simp [hok]
  · simp only [hO]
    rfl

def owlSelfHintB (O : OWL.Ontology) (hs : List RawHint) : List (Option Bool) :=
  if O.isSROIQDSKB && !(selfAxs O).isEmpty then
    match translateSHOIQD (roleOff (selfOff O)) [] with
    | none => hs.map fun _ => none
    | some T =>
      match roleCls T (selfOff O) with
      | none => hs.map fun _ => none
      | some E =>
        match selfCls T O with
        | none => hs.map fun _ => none
        | some SC =>
          if sroiqSHOK T (nomNames (roleOff (selfOff O)) []) E SC then
            (sroiqSHPartsB T (nomNames (roleOff (selfOff O)) []) E SC hs).map some
          else hs.map fun _ => none
  else hs.map fun _ => none

theorem owlSelfHintB_eq (O : OWL.Ontology) (hs : List RawHint) :
    owlSelfHintB O hs = hs.map (owlSelfHint O) := by
  unfold owlSelfHintB owlSelfHint
  by_cases hO : (O.isSROIQDSKB && !(selfAxs O).isEmpty) = true
  · simp only [hO, if_true]
    cases translateSHOIQD (roleOff (selfOff O)) [] with
    | none => simp
    | some T =>
      simp only
      cases roleCls T (selfOff O) with
      | none => simp
      | some E =>
        simp only
        cases selfCls T O with
        | none => simp
        | some SC =>
          simp only
          by_cases hok : sroiqSHOK T (nomNames (roleOff (selfOff O)) []) E SC = true
          · simp [hok, sroiqSHPartsB_eq, List.map_map, Function.comp_def]
          · simp [hok]
  · simp only [hO]
    simp

/-- Whether `owlSelfHint` answers does not depend on the hint. -/
theorem owlSelfHint_isSome (O : OWL.Ontology) (h h' : RawHint) :
    (owlSelfHint O h).isSome = (owlSelfHint O h').isSome := by
  unfold owlSelfHint
  by_cases hO : (O.isSROIQDSKB && !(selfAxs O).isEmpty) = true
  · simp only [hO, if_true]
    cases translateSHOIQD (roleOff (selfOff O)) [] with
    | none => rfl
    | some T =>
      simp only
      cases roleCls T (selfOff O) with
      | none => rfl
      | some E =>
        simp only
        cases selfCls T O with
        | none => rfl
        | some SC =>
          simp only
          by_cases hok : sroiqSHOK T (nomNames (roleOff (selfOff O)) []) E SC = true
          · simp [hok]
          · simp [hok]
  · simp only [hO]
    rfl

def owlHSHintOnB (O : Ontology) (P : List (IRI × ObjProp)) (hs : List RawHint) :
    List (Option Bool) :=
  if O.isSROIQDSKB && !P.isEmpty then
    match translateSHOIQD (roleOff (selfOff O)) (pairNames P) with
    | none => hs.map fun _ => none
    | some T =>
      match roleCls T (selfOff O) with
      | none => hs.map fun _ => none
      | some E =>
        match selfCls T O with
        | none => hs.map fun _ => none
        | some SC =>
          match pairCls T P with
          | none => hs.map fun _ => none
          | some PC =>
            if sroiqSHOK T (nomNames (roleOff (selfOff O)) (pairNames P)) E (SC ++ PC) then
              (sroiqSHPartsB T (nomNames (roleOff (selfOff O)) (pairNames P)) E (SC ++ PC) hs).map some
            else hs.map fun _ => none
  else hs.map fun _ => none

theorem owlHSHintOnB_eq (O : Ontology) (P : List (IRI × ObjProp)) (hs : List RawHint) :
    owlHSHintOnB O P hs = hs.map (owlHSHintOn O P) := by
  unfold owlHSHintOnB owlHSHintOn
  by_cases hO : (O.isSROIQDSKB && !P.isEmpty) = true
  · simp only [hO, if_true]
    cases translateSHOIQD (roleOff (selfOff O)) (pairNames P) with
    | none => simp
    | some T =>
      simp only
      cases roleCls T (selfOff O) with
      | none => simp
      | some E =>
        simp only
        cases selfCls T O with
        | none => simp
        | some SC =>
          simp only
          cases pairCls T P with
          | none => simp
          | some PC =>
            simp only
            by_cases hok : sroiqSHOK T (nomNames (roleOff (selfOff O)) (pairNames P)) E (SC ++ PC) = true
            · simp [hok, sroiqSHPartsB_eq, List.map_map, Function.comp_def]
            · simp [hok]
  · simp only [hO]
    simp

/-! ## The route over a list of hints -/

def hintCoreB (O : Ontology) (hs : List RawHint) : List (Option Bool) :=
  if !(selfPairs O).isEmpty then owlHSHintOnB (hsOff O) (selfPairs O) hs
  else if (owlChainHint O {}).isSome then owlChainHintB O hs else owlSelfHintB O hs

theorem hintCoreB_eq (O : Ontology) (hs : List RawHint) :
    hintCoreB O hs = hs.map (hintCore O) := by
  unfold hintCoreB
  split_ifs with h1 h3
  · rw [owlHSHintOnB_eq]; simp [hintCore, h1, owlHSHint]
  · rw [owlChainHintB_eq]
    refine List.map_congr_left fun h _ => ?_
    have hs : (owlChainHint O h).isSome = true := by rw [owlChainHint_isSome O h {}]; exact h3
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hs
    simp [hintCore, h1, hb]
  · rw [owlSelfHintB_eq]
    refine List.map_congr_left fun h _ => ?_
    have hs : (owlChainHint O h).isSome = false := by
      rw [owlChainHint_isSome O h {}]; simpa using h3
    have hn : owlChainHint O h = none := Option.not_isSome_iff_eq_none.1 (by simp [hs])
    simp [hintCore, h1, hn]

def hintPB (O : Ontology) (hs : List RawHint) : List (Option Bool) :=
  if (splitDef O.axioms).isSome then
    match dtLoop O.axioms.length O with
    | some O' => hintCoreB (anonOff [] (duOff O')) hs
    | none => hs.map fun _ => none
  else hintCoreB (anonOff [] (duOff O)) hs

/-- **The batch route is the route**, hint by hint. -/
theorem hintPB_eq (O : Ontology) (hs : List RawHint) : hintPB O hs = hs.map (hintP O) := by
  unfold hintPB
  split_ifs with h1
  · split
    next O' hO' => rw [hintCoreB_eq]; simp [hintP, h1, hO', hintP0]
    next hO' =>
      refine List.map_congr_left fun h _ => ?_
      simp only [hintP, h1, if_true, hO']
  · rw [hintCoreB_eq]; simp [hintP, h1, hintP0]


/-! ## The fragment check without a hint -/

def owlChainFrag (O : OWL.Ontology) : Bool :=
  if O.isSROIQDKB then
    match translateSHOIQD (roleOff O) [] with
    | none => false
    | some T =>
      match roleCls T O with
      | none => false
      | some E => sroiqHOK T (nomNames (roleOff O) []) E
  else false

theorem owlChainFrag_eq (O : OWL.Ontology) (h : RawHint) :
    owlChainFrag O = (owlChainHint O h).isSome := by
  unfold owlChainFrag owlChainHint
  by_cases hO : O.isSROIQDKB = true
  · simp only [hO, if_true]
    cases translateSHOIQD (roleOff O) [] with
    | none => rfl
    | some T =>
      simp only
      cases roleCls T O with
      | none => rfl
      | some E =>
        simp only
        by_cases hok : sroiqHOK T (nomNames (roleOff O) []) E = true <;> simp [hok]
  · simp [hO]

def owlSelfFrag (O : OWL.Ontology) : Bool :=
  if O.isSROIQDSKB && !(selfAxs O).isEmpty then
    match translateSHOIQD (roleOff (selfOff O)) [] with
    | none => false
    | some T =>
      match roleCls T (selfOff O) with
      | none => false
      | some E =>
        match selfCls T O with
        | none => false
        | some SC => sroiqSHOK T (nomNames (roleOff (selfOff O)) []) E SC
  else false

theorem owlSelfFrag_eq (O : OWL.Ontology) (h : RawHint) :
    owlSelfFrag O = (owlSelfHint O h).isSome := by
  unfold owlSelfFrag owlSelfHint
  by_cases hO : (O.isSROIQDSKB && !(selfAxs O).isEmpty) = true
  · simp only [hO, if_true]
    cases translateSHOIQD (roleOff (selfOff O)) [] with
    | none => rfl
    | some T =>
      simp only
      cases roleCls T (selfOff O) with
      | none => rfl
      | some E =>
        simp only
        cases selfCls T O with
        | none => rfl
        | some SC =>
          simp only
          by_cases hok : sroiqSHOK T (nomNames (roleOff (selfOff O)) []) E SC = true <;> simp [hok]
  · simp only [hO]; simp

def owlHSFragOn (O : Ontology) (P : List (IRI × ObjProp)) : Bool :=
  if O.isSROIQDSKB && !P.isEmpty then
    match translateSHOIQD (roleOff (selfOff O)) (pairNames P) with
    | none => false
    | some T =>
      match roleCls T (selfOff O) with
      | none => false
      | some E =>
        match selfCls T O with
        | none => false
        | some SC =>
          match pairCls T P with
          | none => false
          | some PC => sroiqSHOK T (nomNames (roleOff (selfOff O)) (pairNames P)) E (SC ++ PC)
  else false

theorem owlHSFragOn_eq (O : Ontology) (P : List (IRI × ObjProp)) (h : RawHint) :
    owlHSFragOn O P = (owlHSHintOn O P h).isSome := by
  unfold owlHSFragOn owlHSHintOn
  by_cases hO : (O.isSROIQDSKB && !P.isEmpty) = true
  · simp only [hO, if_true]
    cases translateSHOIQD (roleOff (selfOff O)) (pairNames P) with
    | none => rfl
    | some T =>
      simp only
      cases roleCls T (selfOff O) with
      | none => rfl
      | some E =>
        simp only
        cases selfCls T O with
        | none => rfl
        | some SC =>
          simp only
          cases pairCls T P with
          | none => rfl
          | some PC =>
            simp only
            by_cases hok : sroiqSHOK T (nomNames (roleOff (selfOff O)) (pairNames P)) E (SC ++ PC) = true <;>
              simp [hok]
  · simp only [hO]; simp

def hintCoreFrag (O : Ontology) : Bool :=
  if !(selfPairs O).isEmpty then owlHSFragOn (hsOff O) (selfPairs O)
  else owlChainFrag O || owlSelfFrag O

theorem hintCoreFrag_eq (O : Ontology) (h : RawHint) : hintCoreFrag O = (hintCore O h).isSome := by
  unfold hintCoreFrag hintCore
  split_ifs
  · exact owlHSFragOn_eq _ _ h
  · rw [owlChainFrag_eq O h, owlSelfFrag_eq O h]
    cases owlChainHint O h <;> simp

/-- **The fragment of the hint route**, decided without a hint. -/
def hintPFrag (O : Ontology) : Bool :=
  if (splitDef O.axioms).isSome then
    match dtLoop O.axioms.length O with
    | some O' => hintCoreFrag (anonOff [] (duOff O'))
    | none => false
  else hintCoreFrag (anonOff [] (duOff O))

theorem hintPFrag_eq (O : Ontology) (h : RawHint) : hintPFrag O = (hintP O h).isSome := by
  unfold hintPFrag hintP hintP0
  split_ifs
  · cases dtLoop O.axioms.length O with
    | some O' => exact hintCoreFrag_eq _ h
    | none => rfl
  · exact hintCoreFrag_eq _ h

/-! ## Rows -/

/-- A row of the hint route. -/
inductive HintRowSpec where
  | consistent
  | nontype (C a : IRI)
  | nonsame (a b : IRI)
  | nonsub (A B : IRI)
  | nondiff (a b : IRI)
  | nonrole (r : ObjProp) (a b : IRI)
  | nonnrole (r : ObjProp) (a b : IRI)
  | nonsubs (A : IRI) (Bs : List IRI)
  | nontypes (a : IRI) (Cs : List IRI)
deriving DecidableEq, Repr, Inhabited

/-- The axioms a row adds (`none` for the consistency row). -/
def HintRowSpec.axs (O : Ontology) : HintRowSpec → Option (List Axiom)
  | .consistent => none
  | .nontype C a => some (typeAxs C a)
  | .nonsame a b => some (sameAxs a b)
  | .nonsub A B => some (subAxs O A B)
  | .nondiff a b => some (diffAxs a b)
  | .nonrole r a b => some (roleAxs r a b)
  | .nonnrole r a b => some (nroleAxs r a b)
  | .nonsubs A Bs => some (nonSubsAxs O A Bs)
  | .nontypes a Cs => some (nonTypesAxs a Cs)

/-- What a certified row means. -/
def HintRowSpec.Holds (pat : String → String → Prop) (O : Ontology) : HintRowSpec → Prop
  | .consistent => ConsistentAt (owl2MapP pat) O
  | .nontype C a => ¬ EntailsAt (owl2MapP pat) O (.classAssertion (.cls C) (.named a))
  | .nonsame a b => ¬ EntailsAt (owl2MapP pat) O (.sameIndividual [.named a, .named b])
  | .nonsub A B => ¬ EntailsSubAt (owl2MapP pat) O A B
  | .nondiff a b => ¬ EntailsAt (owl2MapP pat) O (.differentIndividuals [.named a, .named b])
  | .nonrole r a b => ¬ EntailsAt (owl2MapP pat) O (.objectPropertyAssertion r (.named a) (.named b))
  | .nonnrole r a b =>
    ¬ EntailsAt (owl2MapP pat) O (.negativeObjectPropertyAssertion r (.named a) (.named b))
  | .nonsubs A Bs => ∀ B ∈ Bs, ¬ EntailsSubAt (owl2MapP pat) O A B
  | .nontypes a Cs => ∀ C ∈ Cs, ¬ EntailsAt (owl2MapP pat) O (.classAssertion (.cls C) (.named a))

/-- The answer of a row on one hint. -/
def hintRowAns (O : Ontology) (r : HintRowSpec) (hint : RawHint) : Option Bool :=
  match r.axs O with
  | none => owlHintConsistent O hint
  | some L => hintRow O L hint

/-- **Every certified row holds**, for every reading of `xsd:pattern`. -/
theorem hintRowAns_sound (pat : String → String → Prop) {O : Ontology} {r : HintRowSpec}
    {hint : RawHint} (h : hintRowAns O r hint = some true) : r.Holds pat O := by
  cases r with
  | consistent => exact owlHintConsistent_sound pat h
  | nontype C a => exact hintNonType_sound pat h
  | nonsame a b => exact hintNonSame_sound pat h
  | nonsub A B => exact hintNonSub_sound pat h
  | nondiff a b => exact hintNonDiff_sound pat h
  | nonrole r a b => exact hintNonRole_sound pat h
  | nonnrole r a b => exact hintNonNRole_sound pat h
  | nonsubs A Bs => exact hintNonSubs_sound pat h
  | nontypes a Cs => exact hintNonTypes_sound pat h

/-- The answers of a row on a list of hints: the extended ontology is
translated once. -/
def hintRowsB (O : Ontology) (r : HintRowSpec) (hs : List RawHint) : List (Option Bool) :=
  let cert : Option Bool → Option Bool := fun
    | some true => some true
    | _ => none
  match r.axs O with
  | none => (hintPB O hs).map cert
  | some L =>
    if (addAxs O L).noKey then (hintPB (addAxs O L) hs).map cert else hs.map fun _ => none

/-- **The batch rows are the rows**, hint by hint. -/
theorem hintRowsB_eq (O : Ontology) (r : HintRowSpec) (hs : List RawHint) :
    hintRowsB O r hs = hs.map (hintRowAns O r) := by
  unfold hintRowsB hintRowAns
  split
  next hn => rw [hintPB_eq, List.map_map]; rfl
  next L hL =>
    split_ifs with hk
    · rw [hintPB_eq, List.map_map]
      refine List.map_congr_left fun h _ => ?_
      simp only [Function.comp_apply, hintRow, hk, if_true]
      rfl
    · refine List.map_congr_left fun h _ => ?_
      simp [hintRow, hk]

end ContextCalculus.OWLFrontend

#print axioms ContextCalculus.OWLFrontend.hintPB_eq
#print axioms ContextCalculus.OWLFrontend.hintPFrag_eq
#print axioms ContextCalculus.OWLFrontend.hintRowsB_eq
#print axioms ContextCalculus.OWLFrontend.hintRowAns_sound
