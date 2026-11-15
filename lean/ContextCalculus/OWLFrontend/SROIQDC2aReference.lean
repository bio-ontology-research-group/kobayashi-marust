import ContextCalculus.OWLFrontend.SROIQDNom

/-!
# The OWL route for SROIQ(D) knowledge bases in C2a (stage C3, design section 6)

`docs/V1.7.0-C3-ROLES-DESIGN.md`, sections 4 and 6. An ontology of the
SROIQ(D) knowledge-base part (`Ontology.isSROIQDKB`: the SHOIQ(D)
knowledge-base part with general role chains and reflexivity) is read as
the `SRIQN` data ontology `dosnC` (`SROIQDNom.lean`), the role chains are
eliminated (`SROIQ.Proc.encChainDN`), and the C2a procedure with the cell
parts of the OWL 2 datatype map decides consistency, as in the SHOIQ(D)
route.

The checks (`sroiqOK`): the OWL 2 regularity condition (`regularB`), closed
role automata and simple counting roles (`condB`, the conditions of chain
elimination), C2a of the encoding, and supported data ranges. The role
table lookups of `roleCls` are checked as well.

* `owlSROIQDC2aConsistent_sound`: every answer is consistency at
  `owl2MapP pat`, for every reading of `xsd:pattern` and every hint.
* `owlSROIQDC2aConsistent_isSome_iff`: the route answers exactly on the
  SROIQ(D) knowledge-base part with the checks passed.
* Six rows (type, same, subsumption, different, role, negative role), each
  the negated consistency of the ontology with added axioms.
-/

namespace ContextCalculus.SROIQ.Proc

open ContextCalculus.SRIQ (Clause Ontology)
open ContextCalculus.SROIQ (rules)

variable {n m : Nat}

/-- The conditions of chain elimination, computed. -/
def condB (O : Ontology (Fin n) (Fin m)) : Bool :=
  (allsQ O).all (fun q => closedB O (reachL O q.2.1)) &&
  O.all fun
    | .atLeast _ _ R _ | .atMost _ _ R _ => (rules O).all fun p => !leB O p.1 R
    | _ => true

theorem condC_of_condB {O : Ontology (Fin n) (Fin m)} (h : condB O = true) : CondC O := by
  simp only [condB, Bool.and_eq_true, List.all_eq_true] at h
  refine ⟨fun q hq => h.1 q hq, fun a k R b hcl T body hr hle => ?_⟩
  rcases hcl with hcl | hcl
  · have := h.2 _ hcl
    simp only [List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at this
    have h2 := this (T, body) hr
    rw [leB_iff.2 hle] at h2; cases h2
  · have := h.2 _ hcl
    simp only [List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at this
    have h2 := this (T, body) hr
    rw [leB_iff.2 hle] at h2; cases h2

/-- `condB` with the table of super-roles computed once. -/
def condBF (O : Ontology (Fin n) (Fin m)) : Bool :=
  let rs := rules O
  let le := leF (mkTab O)
  let sf := succsT rs le
  (allsQT rs le O).all (fun q => closedT sf (reachItT sf 4096 64 [[(q.2.1, false)]])) &&
  O.all fun
    | .atLeast _ _ R _ | .atMost _ _ R _ => rs.all fun p => !le p.1 R
    | _ => true

@[csimp] theorem condB_eq_F : @condB = @condBF := by
  funext n m O
  simp only [condBF, leF_mkTab, succsT_eq, condB, reachL, reachIt_eq, closedB_eq]
  rfl

end ContextCalculus.SROIQ.Proc

namespace ContextCalculus.OWLFrontend

open ContextCalculus.OWL ContextCalculus.OWL.Datatypes SHIQD SHOIQ

/-! ## The decision -/

/-- The encoded `SRIQN` data ontology. -/
abbrev encC (T : SRIQDKBTranslation) (L : List IRI)
    (E : List (SRIQ.Clause (Fin T.obj.conceptCount) (Fin T.obj.roleCount))) :=
  SROIQ.Proc.encChainDN (dosnC T L E)

/-- The object part before chain elimination. -/
abbrev objC (T : SRIQDKBTranslation) (L : List IRI)
    (E : List (SRIQ.Clause (Fin T.obj.conceptCount) (Fin T.obj.roleCount))) :=
  ContextCalculus.SRIQD.objPart (SRIQN.dbase (dosnC T L E))

instance {n m p q : Nat} (O : SRIQN.DOntology (Fin n) (Fin m) (Fin p) (Fin q)) :
    Decidable (SRIQN.IsC2aD O) := by
  unfold SRIQN.IsC2aD; infer_instance

/-- **The checks**: regularity, the conditions of chain elimination, C2a of
the encoding, and supported data atoms. -/
def sroiqOK (T : SRIQDKBTranslation) (L : List IRI)
    (E : List (SRIQ.Clause (Fin T.obj.conceptCount) (Fin T.obj.roleCount))) : Bool :=
  SROIQ.Proc.regularB (objC T L E) && SROIQ.Proc.condB (objC T L E) &&
    decide (SRIQN.IsC2aD (SRIQN.Proc.encTransDN (encC T L E))) &&
    (List.finRange T.tab.length).all fun p => drSupported (spec T.tab p)

/-- The small-cell threshold. -/
def sroiqBound (T : SRIQDKBTranslation) (L : List IRI)
    (E : List (SRIQ.Clause (Fin T.obj.conceptCount) (Fin T.obj.roleCount))) : Nat :=
  ContextCalculus.SRIQD.dbnd (SRIQN.dbase (SRIQN.Proc.encTransDN (encC T L E))) *
    (ContextCalculus.SRIQD.allG (allFrees (spec T.tab)).length).length

/-- Some part of the data theory accepts the encoded ontology. -/
def sroiqParts (T : SRIQDKBTranslation) (L : List IRI)
    (E : List (SRIQ.Clause (Fin T.obj.conceptCount) (Fin T.obj.roleCount)))
    (hint : Option RawHint) : Bool :=
  let sp := spec T.tab
  let as := allBases sp
  let cs := cellsOf as
  SRIQN.consistentPartsN (encC T L E) cs (cellSize as)
    (ContextCalculus.SRIQD.splitCell cs (cellSize as) (sroiqBound T L E) (owlE sp)) (owlE sp)
    (hint.bind fun h => h.toHintN _ _)

theorem sroiqParts_iff (pat : String → String → Prop) {T : SRIQDKBTranslation} {L : List IRI}
    {E : List (SRIQ.Clause (Fin T.obj.conceptCount) (Fin T.obj.roleCount))}
    (hok : sroiqOK T L E = true) (hint : Option RawHint) :
    sroiqParts T L E hint = true ↔
      SRIQN.ConsistentDN (owlTheory pat (spec T.tab)) (dosnC T L E) := by
  simp only [sroiqOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨-, h1⟩, h2⟩, h3⟩ := hok
  have hsup : ∀ p, drSupported (spec T.tab p) = true := fun p =>
    List.all_eq_true.1 h3 p (List.mem_finRange p)
  have heq : owlTheory pat (spec T.tab) = ContextCalculus.SRIQD.cellTheory
      (cellOf (allBases (spec T.tab))) (owlE (spec T.tab)) := by
    funext V atom
    exact propext (owlTheory_iff pat hsup V atom)
  rw [heq, SROIQ.Proc.consistentDN_encChainDN (SROIQ.Proc.condC_of_condB h1)]
  exact SRIQN.consistentPartsN_iff (cellSpec _) (le_refl (sroiqBound T L E))
    ContextCalculus.SRIQD.splitCell_ok.1 ContextCalculus.SRIQD.splitCell_ok.2
    (SROIQ.Proc.isSHIQD_encChainDN _) (le_refl _) h2 _

/-! ## The route -/

/-- **Consistency of a SROIQ(D) knowledge base in C2a** at the OWL 2
datatype map. -/
def owlSROIQDC2aConsistent (O : OWL.Ontology) (hint : Option RawHint) : Option Bool :=
  if O.isSROIQDKB then
    match translateSHOIQD (roleOff O) [] with
    | none => none
    | some T =>
      match roleCls T O with
      | none => none
      | some E =>
        if sroiqOK T (nomNames (roleOff O) []) E then
          some (sroiqParts T (nomNames (roleOff O) []) E hint)
        else none
  else none

/-- **Soundness.** Every answer is consistency at `owl2MapP pat`, for every
reading of `xsd:pattern` and every hint. -/
theorem owlSROIQDC2aConsistent_sound (pat : String → String → Prop) {O : OWL.Ontology}
    {hint : Option RawHint} {v : Bool} (h : owlSROIQDC2aConsistent O hint = some v) :
    v = true ↔ ConsistentAt (owl2MapP pat) O := by
  unfold owlSROIQDC2aConsistent at h
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
      rw [sroiqParts_iff pat hok, ← sroiq_consistent pat hO hT hE]

/-- The checks of the route on the translation. -/
def SROIQDC2aChecks (O : OWL.Ontology) : Prop :=
  ∀ T, translateSHOIQD (roleOff O) [] = some T →
    ∃ E, roleCls T O = some E ∧ sroiqOK T (nomNames (roleOff O) []) E = true

/-- **Completeness.** The route answers exactly on the SROIQ(D)
knowledge-base part with the checks passed, for every hint. -/
theorem owlSROIQDC2aConsistent_isSome_iff (O : OWL.Ontology) (hint : Option RawHint) :
    (owlSROIQDC2aConsistent O hint).isSome = true ↔ O.isSROIQDKB = true ∧ SROIQDC2aChecks O := by
  constructor
  · intro h
    unfold owlSROIQDC2aConsistent at h
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
    unfold owlSROIQDC2aConsistent
    rw [if_pos hO, hT]
    dsimp only
    rw [hE]
    dsimp only
    rw [if_pos hok]
    rfl

/-! ## Rows -/

variable {DM : DatatypeMap} {D : Type}

theorem isSROIQDKB_addAxs {O : Ontology} {L : List Axiom} :
    (addAxs O L).isSROIQDKB = (O.isSROIQDKB && L.all Axiom.isSROIQDKB) := by
  simp [addAxs, Ontology.isSROIQDKB, List.all_append]

theorem model_addAxsS {O : Ontology} {L : List Axiom} (hO : O.isSROIQDKB = true)
    (hL : ∀ ax ∈ L, ax.isSROIQDKB = true) (I : Interp DM D) :
    OWL.Model (addAxs O L) I ↔ OWL.Model O I ∧ ∀ ax ∈ L, I.sat [] ax := by
  have hO' : ∀ a ∈ O.axioms, a.isSROIQDKB = true := by
    simpa [Ontology.isSROIQDKB, List.all_eq_true] using hO
  simp only [OWL.Model, addAxs, List.mem_append]
  constructor
  · intro h
    exact ⟨fun a ha => (sat_N_sroiq (hO' a ha) _ _).1 (h a (Or.inl ha)),
      fun a ha => (sat_N_sroiq (hL a ha) _ _).1 (h a (Or.inr ha))⟩
  · rintro ⟨h1, h2⟩ a (ha | ha)
    · exact (sat_N_sroiq (hO' a ha) _ _).1 (h1 a ha)
    · exact (sat_N_sroiq (hL a ha) _ _).1 (h2 a ha)

theorem model_updS {O : Ontology} (hO : O.isSROIQDKB = true) {I : Interp DM D} {f : IRI}
    (hf : f ∉ O.namedIndividuals) (x : D) : OWL.Model O (updI I f x) ↔ OWL.Model O I := by
  have hO' : ∀ a ∈ O.axioms, a.isSROIQDKB = true := by
    simpa [Ontology.isSROIQDKB, List.all_eq_true] using hO
  have hfa : ∀ a ∈ O.axioms, f ∉ a.namedIndividuals := fun a ha hm =>
    hf (List.mem_flatMap.2 ⟨a, ha, hm⟩)
  simp only [OWL.Model]
  refine forall_congr' fun a => imp_congr_right fun ha => ?_
  by_cases hr : a.isRoleC3 = true
  · have hrole : (updI I f x).role = I.role := rfl
    cases a with
    | subObjectPropertyOf rs r =>
      simp only [Interp.sat, Interp.chain_congr hrole, Interp.prop_congr hrole]
    | reflexive r => simp only [Interp.sat, Interp.prop_congr hrole]
    | _ => simp [Axiom.isRoleC3] at hr
  · exact sat_updN (by simpa [Axiom.isSROIQDKB, hr] using hO' a ha) (hfa a ha) _

/-- A row: the negated consistency of the extension. -/
def rowS (O : OWL.Ontology) (L : List Axiom) (hint : Option RawHint) : Option Bool :=
  (owlSROIQDC2aConsistent (addAxs O L) hint).map (!·)

theorem rowS_of {O : Ontology} {L : List Axiom} {hint : Option RawHint} {v : Bool}
    (pat : String → String → Prop) (h : rowS O L hint = some v) :
    O.isSROIQDKB = true ∧ (∀ ax ∈ L, ax.isSROIQDKB = true) ∧
      (v = true ↔ ¬ ConsistentAt (owl2MapP pat) (addAxs O L)) := by
  obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.1 h
  have hk : (addAxs O L).isSROIQDKB = true :=
    ((owlSROIQDC2aConsistent_isSome_iff (addAxs O L) hint).1 (by rw [hw]; rfl)).1
  rw [isSROIQDKB_addAxs, Bool.and_eq_true, List.all_eq_true] at hk
  refine ⟨hk.1, hk.2, ?_⟩
  rw [← owlSROIQDC2aConsistent_sound pat hw]
  cases w <;> simp

theorem rowS_complete {O : Ontology} {L : List Axiom} (hO : O.isSROIQDKB = true)
    (hL : ∀ ax ∈ L, ax.isSROIQDKB = true) (hc : SROIQDC2aChecks (addAxs O L))
    (hint : Option RawHint) : (rowS O L hint).isSome = true := by
  unfold rowS
  rw [Option.isSome_map]
  exact (owlSROIQDC2aConsistent_isSome_iff _ hint).2
    ⟨by rw [isSROIQDKB_addAxs, hO, List.all_eq_true.2 hL]; rfl, hc⟩

/-- **Type row**: decides `O ⊨ ClassAssertion(C a)`. -/
def owlSROIQDTypeRow (O : OWL.Ontology) (C a : IRI) (hint : Option RawHint) : Option Bool :=
  rowS O (typeAxs C a) hint

/-- **Same row**: decides `O ⊨ SameIndividual(a b)`. -/
def owlSROIQDSameRow (O : OWL.Ontology) (a b : IRI) (hint : Option RawHint) : Option Bool :=
  rowS O (sameAxs a b) hint

/-- **Subsumption row**: decides `O ⊨ SubClassOf(A B)`. -/
def owlSROIQDSubRow (O : OWL.Ontology) (A B : IRI) (hint : Option RawHint) : Option Bool :=
  rowS O (subAxs O A B) hint

/-- **Different row**: decides `O ⊨ DifferentIndividuals(a b)`. -/
def owlSROIQDDiffRow (O : OWL.Ontology) (a b : IRI) (hint : Option RawHint) : Option Bool :=
  rowS O (diffAxs a b) hint

/-- **Role row**: decides `O ⊨ ObjectPropertyAssertion(r a b)` for a basic `r`. -/
def owlSROIQDRoleRow (O : OWL.Ontology) (r : ObjProp) (a b : IRI) (hint : Option RawHint) :
    Option Bool :=
  if r.isBasic then rowS O (roleAxs r a b) hint else none

/-- **Negative role row**: decides `O ⊨ NegativeObjectPropertyAssertion(r a b)`. -/
def owlSROIQDNRoleRow (O : OWL.Ontology) (r : ObjProp) (a b : IRI) (hint : Option RawHint) :
    Option Bool :=
  if r.isBasic then rowS O (nroleAxs r a b) hint else none

theorem owlSROIQDTypeRow_sound (pat : String → String → Prop) {O : OWL.Ontology} {C a : IRI}
    {hint : Option RawHint} {v : Bool} (h : owlSROIQDTypeRow O C a hint = some v) :
    v = true ↔ EntailsAt (owl2MapP pat) O (.classAssertion (.cls C) (.named a)) := by
  obtain ⟨hO, hL, hv⟩ := rowS_of pat h
  rw [hv, consistentAt_iff_not, not_not]
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

theorem owlSROIQDSameRow_sound (pat : String → String → Prop) {O : OWL.Ontology} {a b : IRI}
    {hint : Option RawHint} {v : Bool} (h : owlSROIQDSameRow O a b hint = some v) :
    v = true ↔ EntailsAt (owl2MapP pat) O (.sameIndividual [.named a, .named b]) := by
  obtain ⟨hO, hL, hv⟩ := rowS_of pat h
  rw [hv, consistentAt_iff_not, not_not]
  constructor
  · intro hi Dom _ I hI
    rw [sat_same]
    by_contra hc
    refine hi Dom I ((model_addAxsS hO hL I).2 ⟨hI, ?_⟩)
    simp only [sameAxs, List.mem_singleton, forall_eq]
    exact (sat_diff I _ a b).2 hc
  · intro he Dom _ I hI
    obtain ⟨hI, hs⟩ := (model_addAxsS hO hL I).1 hI
    have := (sat_same I _ a b).1 (he Dom I hI)
    simp only [sameAxs, List.mem_singleton, forall_eq] at hs
    exact (sat_diff I _ a b).1 hs this

theorem owlSROIQDSubRow_sound (pat : String → String → Prop) {O : OWL.Ontology} {A B : IRI}
    {hint : Option RawHint} {v : Bool} (h : owlSROIQDSubRow O A B hint = some v) :
    v = true ↔ EntailsSubAt (owl2MapP pat) O A B := by
  obtain ⟨hO, hL, hv⟩ := rowS_of pat h
  rw [hv, consistentAt_iff_not, not_not]
  constructor
  · intro hi Dom _ I hI x hA
    by_contra hB
    have hU := (model_updS hO (freshInd_not_mem O) x).2 hI
    refine hi Dom (updI I (freshInd O) x) ((model_addAxsS hO hL _).2 ⟨hU, ?_⟩)
    simp only [subAxs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      Interp.sat, Interp.ext, updI, Function.update_self]
    exact ⟨hA, hB⟩
  · intro he Dom _ I hI
    obtain ⟨hI, hs⟩ := (model_addAxsS hO hL I).1 hI
    simp only [subAxs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      Interp.sat, Interp.ext] at hs
    exact hs.2 (he Dom I hI _ hs.1)

theorem owlSROIQDDiffRow_sound (pat : String → String → Prop) {O : OWL.Ontology} {a b : IRI}
    {hint : Option RawHint} {v : Bool} (h : owlSROIQDDiffRow O a b hint = some v) :
    v = true ↔ EntailsAt (owl2MapP pat) O (.differentIndividuals [.named a, .named b]) := by
  obtain ⟨hO, hL, hv⟩ := rowS_of pat h
  rw [hv, consistentAt_iff_not, not_not]
  have hd : ∀ {Dom : Type} (I : Interp (owl2MapP pat) Dom) (N : List IRI),
      I.sat N (.differentIndividuals [.named a, .named b]) ↔ ¬ I.ind (.named a) = I.ind (.named b) := by
    intro Dom I N
    simp [Interp.sat]
  constructor
  · intro hi Dom _ I hI
    rw [hd]
    intro hc
    refine hi Dom I ((model_addAxsS hO hL I).2 ⟨hI, ?_⟩)
    simp only [diffAxs, List.mem_singleton, forall_eq]
    exact (sat_same I _ a b).2 hc
  · intro he Dom _ I hI
    obtain ⟨hI, hs⟩ := (model_addAxsS hO hL I).1 hI
    simp only [diffAxs, List.mem_singleton, forall_eq] at hs
    exact (hd I _).1 (he Dom I hI) ((sat_same I _ a b).1 hs)

theorem owlSROIQDRoleRow_sound (pat : String → String → Prop) {O : OWL.Ontology} {r : ObjProp}
    {a b : IRI} {hint : Option RawHint} {v : Bool} (h : owlSROIQDRoleRow O r a b hint = some v) :
    v = true ↔ EntailsAt (owl2MapP pat) O (.objectPropertyAssertion r (.named a) (.named b)) := by
  unfold owlSROIQDRoleRow at h
  split at h
  swap
  · cases h
  obtain ⟨hO, hL, hv⟩ := rowS_of pat h
  rw [hv, consistentAt_iff_not, not_not]
  constructor
  · intro hi Dom _ I hI
    by_contra hc
    refine hi Dom I ((model_addAxsS hO hL I).2 ⟨hI, ?_⟩)
    simpa [roleAxs, Interp.sat] using hc
  · intro he Dom _ I hI
    obtain ⟨hI, hs⟩ := (model_addAxsS hO hL I).1 hI
    simp only [roleAxs, List.mem_singleton, forall_eq, Interp.sat] at hs
    exact hs (he Dom I hI)

theorem owlSROIQDNRoleRow_sound (pat : String → String → Prop) {O : OWL.Ontology} {r : ObjProp}
    {a b : IRI} {hint : Option RawHint} {v : Bool} (h : owlSROIQDNRoleRow O r a b hint = some v) :
    v = true ↔
      EntailsAt (owl2MapP pat) O (.negativeObjectPropertyAssertion r (.named a) (.named b)) := by
  unfold owlSROIQDNRoleRow at h
  split at h
  swap
  · cases h
  obtain ⟨hO, hL, hv⟩ := rowS_of pat h
  rw [hv, consistentAt_iff_not, not_not]
  constructor
  · intro hi Dom _ I hI hc
    exact hi Dom I ((model_addAxsS hO hL I).2 ⟨hI, by simpa [nroleAxs, Interp.sat] using hc⟩)
  · intro he Dom _ I hI
    obtain ⟨hI, hs⟩ := (model_addAxsS hO hL I).1 hI
    simp only [nroleAxs, List.mem_singleton, forall_eq, Interp.sat] at hs
    exact he Dom I hI hs

theorem typeAxs_okS (C a : IRI) : ∀ ax ∈ typeAxs C a, ax.isSROIQDKB = true :=
  fun ax hax => Axiom.isSROIQDKB_of_isSHOIQDKB (typeAxs_okN C a ax hax)

theorem sameAxs_okS (a b : IRI) : ∀ ax ∈ sameAxs a b, ax.isSROIQDKB = true :=
  fun ax hax => Axiom.isSROIQDKB_of_isSHOIQDKB (sameAxs_okN a b ax hax)

theorem subAxs_okS (O : Ontology) (A B : IRI) : ∀ ax ∈ subAxs O A B, ax.isSROIQDKB = true :=
  fun ax hax => Axiom.isSROIQDKB_of_isSHOIQDKB (subAxs_okN O A B ax hax)

theorem diffAxs_okS (a b : IRI) : ∀ ax ∈ diffAxs a b, ax.isSROIQDKB = true :=
  fun ax hax => Axiom.isSROIQDKB_of_isSHOIQDKB (diffAxs_ok a b ax hax)

theorem owlSROIQDTypeRow_complete {O : OWL.Ontology} (C a : IRI) (hO : O.isSROIQDKB = true)
    (hc : SROIQDC2aChecks (addAxs O (typeAxs C a))) (hint : Option RawHint) :
    (owlSROIQDTypeRow O C a hint).isSome = true :=
  rowS_complete hO (typeAxs_okS C a) hc hint

theorem owlSROIQDSameRow_complete {O : OWL.Ontology} (a b : IRI) (hO : O.isSROIQDKB = true)
    (hc : SROIQDC2aChecks (addAxs O (sameAxs a b))) (hint : Option RawHint) :
    (owlSROIQDSameRow O a b hint).isSome = true :=
  rowS_complete hO (sameAxs_okS a b) hc hint

theorem owlSROIQDSubRow_complete {O : OWL.Ontology} (A B : IRI) (hO : O.isSROIQDKB = true)
    (hc : SROIQDC2aChecks (addAxs O (subAxs O A B))) (hint : Option RawHint) :
    (owlSROIQDSubRow O A B hint).isSome = true :=
  rowS_complete hO (subAxs_okS O A B) hc hint

theorem owlSROIQDDiffRow_complete {O : OWL.Ontology} (a b : IRI) (hO : O.isSROIQDKB = true)
    (hc : SROIQDC2aChecks (addAxs O (diffAxs a b))) (hint : Option RawHint) :
    (owlSROIQDDiffRow O a b hint).isSome = true :=
  rowS_complete hO (diffAxs_okS a b) hc hint

theorem owlSROIQDRoleRow_complete {O : OWL.Ontology} {r : ObjProp} (hr : r.isBasic = true)
    (a b : IRI) (hO : O.isSROIQDKB = true) (hc : SROIQDC2aChecks (addAxs O (roleAxs r a b)))
    (hint : Option RawHint) : (owlSROIQDRoleRow O r a b hint).isSome = true := by
  unfold owlSROIQDRoleRow
  rw [if_pos hr]
  exact rowS_complete hO (fun ax hax => Axiom.isSROIQDKB_of_isSHOIQDKB (roleAxs_ok hr a b ax hax))
    hc hint

theorem owlSROIQDNRoleRow_complete {O : OWL.Ontology} {r : ObjProp} (hr : r.isBasic = true)
    (a b : IRI) (hO : O.isSROIQDKB = true) (hc : SROIQDC2aChecks (addAxs O (nroleAxs r a b)))
    (hint : Option RawHint) : (owlSROIQDNRoleRow O r a b hint).isSome = true := by
  unfold owlSROIQDNRoleRow
  rw [if_pos hr]
  exact rowS_complete hO (fun ax hax => Axiom.isSROIQDKB_of_isSHOIQDKB (nroleAxs_ok hr a b ax hax))
    hc hint

/-- The route extends the SHOIQ(D) knowledge-base part. -/
theorem isSROIQDKB_of_isSHOIQDKB' {O : Ontology} (h : O.isSHOIQDKB = true) : O.isSROIQDKB = true :=
  Ontology.isSROIQDKB_of_isSHOIQDKB h

end ContextCalculus.OWLFrontend

#print axioms ContextCalculus.SROIQ.Proc.condC_of_condB
#print axioms ContextCalculus.OWLFrontend.sroiqParts_iff
#print axioms ContextCalculus.OWLFrontend.owlSROIQDC2aConsistent_sound
#print axioms ContextCalculus.OWLFrontend.owlSROIQDC2aConsistent_isSome_iff
#print axioms ContextCalculus.OWLFrontend.owlSROIQDTypeRow_sound
#print axioms ContextCalculus.OWLFrontend.owlSROIQDSameRow_sound
#print axioms ContextCalculus.OWLFrontend.owlSROIQDSubRow_sound
#print axioms ContextCalculus.OWLFrontend.owlSROIQDDiffRow_sound
#print axioms ContextCalculus.OWLFrontend.owlSROIQDRoleRow_sound
#print axioms ContextCalculus.OWLFrontend.owlSROIQDNRoleRow_sound
#print axioms ContextCalculus.OWLFrontend.owlSROIQDTypeRow_complete
#print axioms ContextCalculus.OWLFrontend.owlSROIQDSameRow_complete
#print axioms ContextCalculus.OWLFrontend.owlSROIQDSubRow_complete
#print axioms ContextCalculus.OWLFrontend.owlSROIQDDiffRow_complete
#print axioms ContextCalculus.OWLFrontend.owlSROIQDRoleRow_complete
#print axioms ContextCalculus.OWLFrontend.owlSROIQDNRoleRow_complete
