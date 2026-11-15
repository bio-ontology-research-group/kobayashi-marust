import ContextCalculus.OWLFrontend.SROIQDSelf

/-!
# Rows of the route with irreflexive and reflexive properties (stage C3c)

The six rows of `SROIQDC2aReference.lean` (type, same, subsumption,
different, role, negative role) over `owlSelfCore`, each the negated
consistency of the ontology with added axioms, and their versions with
anonymous individuals that try the previous route first
(`owlSROIQDSTypeRow` and the others).
-/

namespace ContextCalculus.OWLFrontend

open ContextCalculus.OWL ContextCalculus.OWL.Datatypes SHIQD SHOIQ

theorem isSROIQDSKB_ax_of_isSHOIQDKB {ax : Axiom} (h : ax.isSHOIQDKB = true) :
    ax.isSROIQDSKB = true := by
  simp [Axiom.isSROIQDSKB, Axiom.isSROIQDKB_of_isSHOIQDKB h]

/-! ## Rows -/

variable {DM : DatatypeMap} {D : Type}

theorem isSROIQDSKB_addAxs {O : Ontology} {L : List Axiom} :
    (addAxs O L).isSROIQDSKB = (O.isSROIQDSKB && L.all Axiom.isSROIQDSKB) := by
  simp [addAxs, Ontology.isSROIQDSKB, List.all_append]

theorem model_addAxsSS {O : Ontology} {L : List Axiom} (hO : O.isSROIQDSKB = true)
    (hL : ∀ ax ∈ L, ax.isSROIQDSKB = true) (I : Interp DM D) :
    OWL.Model (addAxs O L) I ↔ OWL.Model O I ∧ ∀ ax ∈ L, I.sat [] ax := by
  have hO' : ∀ a ∈ O.axioms, a.isSROIQDSKB = true := by
    simpa [Ontology.isSROIQDSKB, List.all_eq_true] using hO
  simp only [OWL.Model, addAxs, List.mem_append]
  constructor
  · intro h
    exact ⟨fun a ha => (sat_N_sroiqS (hO' a ha) _ _).1 (h a (Or.inl ha)),
      fun a ha => (sat_N_sroiqS (hL a ha) _ _).1 (h a (Or.inr ha))⟩
  · rintro ⟨h1, h2⟩ a (ha | ha)
    · exact (sat_N_sroiqS (hO' a ha) _ _).1 (h1 a ha)
    · exact (sat_N_sroiqS (hL a ha) _ _).1 (h2 a ha)

theorem model_updSS {O : Ontology} (hO : O.isSROIQDSKB = true) {I : Interp DM D} {f : IRI}
    (hf : f ∉ O.namedIndividuals) (x : D) : OWL.Model O (updI I f x) ↔ OWL.Model O I := by
  have hO' : ∀ a ∈ O.axioms, a.isSROIQDSKB = true := by
    simpa [Ontology.isSROIQDSKB, List.all_eq_true] using hO
  have hfa : ∀ a ∈ O.axioms, f ∉ a.namedIndividuals := fun a ha hm =>
    hf (List.mem_flatMap.2 ⟨a, ha, hm⟩)
  simp only [OWL.Model]
  refine forall_congr' fun a => imp_congr_right fun ha => ?_
  by_cases hs : a.isSelfAx = true
  · have hrole : (updI I f x).role = I.role := rfl
    cases a with
    | irreflexive r => simp only [Interp.sat, Interp.prop_congr hrole]
    | reflexive r => simp only [Interp.sat, Interp.prop_congr hrole]
    | _ => simp [Axiom.isSelfAx] at hs
  have hk : a.isSROIQDKB = true := by simpa [Axiom.isSROIQDSKB, hs] using hO' a ha
  by_cases hr : a.isRoleC3 = true
  · have hrole : (updI I f x).role = I.role := rfl
    cases a with
    | subObjectPropertyOf rs r =>
      simp only [Interp.sat, Interp.chain_congr hrole, Interp.prop_congr hrole]
    | reflexive r => simp only [Interp.sat, Interp.prop_congr hrole]
    | subDataPropertyOf p q => rfl
    | _ => simp [Axiom.isRoleC3] at hr
  · exact sat_updN (by simpa [Axiom.isSROIQDKB, hr] using hk) (hfa a ha) _

/-- A row: the negated consistency of the extension. -/
def rowSS (O : OWL.Ontology) (L : List Axiom) (hint : Option RawHint) : Option Bool :=
  (owlSelfCore (addAxs O L) hint).map (!·)

theorem rowSS_of {O : Ontology} {L : List Axiom} {hint : Option RawHint} {v : Bool}
    (pat : String → String → Prop) (h : rowSS O L hint = some v) :
    O.isSROIQDSKB = true ∧ (∀ ax ∈ L, ax.isSROIQDSKB = true) ∧
      (v = true ↔ ¬ ConsistentAt (owl2MapP pat) (addAxs O L)) := by
  obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.1 h
  have hk : (addAxs O L).isSROIQDSKB = true :=
    (Bool.and_eq_true _ _ ▸ ((owlSelfCore_isSome_iff (addAxs O L) hint).1 (by rw [hw]; rfl)).1).1
  rw [isSROIQDSKB_addAxs, Bool.and_eq_true, List.all_eq_true] at hk
  refine ⟨hk.1, hk.2, ?_⟩
  rw [← owlSelfCore_sound pat hw]
  cases w <;> simp

theorem rowSS_complete {O : Ontology} {L : List Axiom} (hO : O.isSROIQDSKB = true)
    (hL : ∀ ax ∈ L, ax.isSROIQDSKB = true) (hS : (selfAxs (addAxs O L)).isEmpty = false)
    (hc : SelfChecks (addAxs O L))
    (hint : Option RawHint) : (rowSS O L hint).isSome = true := by
  unfold rowSS
  rw [Option.isSome_map]
  exact (owlSelfCore_isSome_iff _ hint).2
    ⟨by rw [isSROIQDSKB_addAxs, hO, List.all_eq_true.2 hL, hS]; rfl, hc⟩

/-- **Type row**: decides `O ⊨ ClassAssertion(C a)`. -/
def owlSelfTypeRow (O : OWL.Ontology) (C a : IRI) (hint : Option RawHint) : Option Bool :=
  rowSS O (typeAxs C a) hint

/-- **Same row**: decides `O ⊨ SameIndividual(a b)`. -/
def owlSelfSameRow (O : OWL.Ontology) (a b : IRI) (hint : Option RawHint) : Option Bool :=
  rowSS O (sameAxs a b) hint

/-- **Subsumption row**: decides `O ⊨ SubClassOf(A B)`. -/
def owlSelfSubRow (O : OWL.Ontology) (A B : IRI) (hint : Option RawHint) : Option Bool :=
  rowSS O (subAxs O A B) hint

/-- **Different row**: decides `O ⊨ DifferentIndividuals(a b)`. -/
def owlSelfDiffRow (O : OWL.Ontology) (a b : IRI) (hint : Option RawHint) : Option Bool :=
  rowSS O (diffAxs a b) hint

/-- **Role row**: decides `O ⊨ ObjectPropertyAssertion(r a b)` for a basic `r`. -/
def owlSelfRoleRow (O : OWL.Ontology) (r : ObjProp) (a b : IRI) (hint : Option RawHint) :
    Option Bool :=
  if r.isBasic then rowSS O (roleAxs r a b) hint else none

/-- **Negative role row**: decides `O ⊨ NegativeObjectPropertyAssertion(r a b)`. -/
def owlSelfNRoleRow (O : OWL.Ontology) (r : ObjProp) (a b : IRI) (hint : Option RawHint) :
    Option Bool :=
  if r.isBasic then rowSS O (nroleAxs r a b) hint else none

theorem owlSelfTypeRow_sound (pat : String → String → Prop) {O : OWL.Ontology} {C a : IRI}
    {hint : Option RawHint} {v : Bool} (h : owlSelfTypeRow O C a hint = some v) :
    v = true ↔ EntailsAt (owl2MapP pat) O (.classAssertion (.cls C) (.named a)) := by
  obtain ⟨hO, hL, hv⟩ := rowSS_of pat h
  rw [hv, consistentAt_iff_not, not_not]
  constructor
  · intro hi Dom _ I hI
    by_contra hc
    refine hi Dom I ((model_addAxsSS hO hL I).2 ⟨hI, ?_⟩)
    simpa [typeAxs, Interp.sat, Interp.ext] using hc
  · intro he Dom _ I hI
    obtain ⟨hI, hs⟩ := (model_addAxsSS hO hL I).1 hI
    have := he Dom I hI
    simp only [typeAxs, List.mem_singleton, forall_eq, Interp.sat, Interp.ext] at hs this
    exact hs this

theorem owlSelfSameRow_sound (pat : String → String → Prop) {O : OWL.Ontology} {a b : IRI}
    {hint : Option RawHint} {v : Bool} (h : owlSelfSameRow O a b hint = some v) :
    v = true ↔ EntailsAt (owl2MapP pat) O (.sameIndividual [.named a, .named b]) := by
  obtain ⟨hO, hL, hv⟩ := rowSS_of pat h
  rw [hv, consistentAt_iff_not, not_not]
  constructor
  · intro hi Dom _ I hI
    rw [sat_same]
    by_contra hc
    refine hi Dom I ((model_addAxsSS hO hL I).2 ⟨hI, ?_⟩)
    simp only [sameAxs, List.mem_singleton, forall_eq]
    exact (sat_diff I _ a b).2 hc
  · intro he Dom _ I hI
    obtain ⟨hI, hs⟩ := (model_addAxsSS hO hL I).1 hI
    have := (sat_same I _ a b).1 (he Dom I hI)
    simp only [sameAxs, List.mem_singleton, forall_eq] at hs
    exact (sat_diff I _ a b).1 hs this

theorem owlSelfSubRow_sound (pat : String → String → Prop) {O : OWL.Ontology} {A B : IRI}
    {hint : Option RawHint} {v : Bool} (h : owlSelfSubRow O A B hint = some v) :
    v = true ↔ EntailsSubAt (owl2MapP pat) O A B := by
  obtain ⟨hO, hL, hv⟩ := rowSS_of pat h
  rw [hv, consistentAt_iff_not, not_not]
  constructor
  · intro hi Dom _ I hI x hA
    by_contra hB
    have hU := (model_updSS hO (freshInd_not_mem O) x).2 hI
    refine hi Dom (updI I (freshInd O) x) ((model_addAxsSS hO hL _).2 ⟨hU, ?_⟩)
    simp only [subAxs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      Interp.sat, Interp.ext, updI, Function.update_self]
    exact ⟨hA, hB⟩
  · intro he Dom _ I hI
    obtain ⟨hI, hs⟩ := (model_addAxsSS hO hL I).1 hI
    simp only [subAxs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      Interp.sat, Interp.ext] at hs
    exact hs.2 (he Dom I hI _ hs.1)

theorem owlSelfDiffRow_sound (pat : String → String → Prop) {O : OWL.Ontology} {a b : IRI}
    {hint : Option RawHint} {v : Bool} (h : owlSelfDiffRow O a b hint = some v) :
    v = true ↔ EntailsAt (owl2MapP pat) O (.differentIndividuals [.named a, .named b]) := by
  obtain ⟨hO, hL, hv⟩ := rowSS_of pat h
  rw [hv, consistentAt_iff_not, not_not]
  have hd : ∀ {Dom : Type} (I : Interp (owl2MapP pat) Dom) (N : List IRI),
      I.sat N (.differentIndividuals [.named a, .named b]) ↔ ¬ I.ind (.named a) = I.ind (.named b) := by
    intro Dom I N
    simp [Interp.sat]
  constructor
  · intro hi Dom _ I hI
    rw [hd]
    intro hc
    refine hi Dom I ((model_addAxsSS hO hL I).2 ⟨hI, ?_⟩)
    simp only [diffAxs, List.mem_singleton, forall_eq]
    exact (sat_same I _ a b).2 hc
  · intro he Dom _ I hI
    obtain ⟨hI, hs⟩ := (model_addAxsSS hO hL I).1 hI
    simp only [diffAxs, List.mem_singleton, forall_eq] at hs
    exact (hd I _).1 (he Dom I hI) ((sat_same I _ a b).1 hs)

theorem owlSelfRoleRow_sound (pat : String → String → Prop) {O : OWL.Ontology} {r : ObjProp}
    {a b : IRI} {hint : Option RawHint} {v : Bool} (h : owlSelfRoleRow O r a b hint = some v) :
    v = true ↔ EntailsAt (owl2MapP pat) O (.objectPropertyAssertion r (.named a) (.named b)) := by
  unfold owlSelfRoleRow at h
  split at h
  swap
  · cases h
  obtain ⟨hO, hL, hv⟩ := rowSS_of pat h
  rw [hv, consistentAt_iff_not, not_not]
  constructor
  · intro hi Dom _ I hI
    by_contra hc
    refine hi Dom I ((model_addAxsSS hO hL I).2 ⟨hI, ?_⟩)
    simpa [roleAxs, Interp.sat] using hc
  · intro he Dom _ I hI
    obtain ⟨hI, hs⟩ := (model_addAxsSS hO hL I).1 hI
    simp only [roleAxs, List.mem_singleton, forall_eq, Interp.sat] at hs
    exact hs (he Dom I hI)

theorem owlSelfNRoleRow_sound (pat : String → String → Prop) {O : OWL.Ontology} {r : ObjProp}
    {a b : IRI} {hint : Option RawHint} {v : Bool} (h : owlSelfNRoleRow O r a b hint = some v) :
    v = true ↔
      EntailsAt (owl2MapP pat) O (.negativeObjectPropertyAssertion r (.named a) (.named b)) := by
  unfold owlSelfNRoleRow at h
  split at h
  swap
  · cases h
  obtain ⟨hO, hL, hv⟩ := rowSS_of pat h
  rw [hv, consistentAt_iff_not, not_not]
  constructor
  · intro hi Dom _ I hI hc
    exact hi Dom I ((model_addAxsSS hO hL I).2 ⟨hI, by simpa [nroleAxs, Interp.sat] using hc⟩)
  · intro he Dom _ I hI
    obtain ⟨hI, hs⟩ := (model_addAxsSS hO hL I).1 hI
    simp only [nroleAxs, List.mem_singleton, forall_eq, Interp.sat] at hs
    exact he Dom I hI hs

theorem typeAxs_okSS (C a : IRI) : ∀ ax ∈ typeAxs C a, ax.isSROIQDSKB = true :=
  fun ax hax => isSROIQDSKB_ax_of_isSHOIQDKB (typeAxs_okN C a ax hax)

theorem sameAxs_okSS (a b : IRI) : ∀ ax ∈ sameAxs a b, ax.isSROIQDSKB = true :=
  fun ax hax => isSROIQDSKB_ax_of_isSHOIQDKB (sameAxs_okN a b ax hax)

theorem subAxs_okSS (O : Ontology) (A B : IRI) : ∀ ax ∈ subAxs O A B, ax.isSROIQDSKB = true :=
  fun ax hax => isSROIQDSKB_ax_of_isSHOIQDKB (subAxs_okN O A B ax hax)

theorem diffAxs_okSS (a b : IRI) : ∀ ax ∈ diffAxs a b, ax.isSROIQDSKB = true :=
  fun ax hax => isSROIQDSKB_ax_of_isSHOIQDKB (diffAxs_ok a b ax hax)

theorem owlSelfTypeRow_complete {O : OWL.Ontology} (C a : IRI) (hO : O.isSROIQDSKB = true)
    (hS : (selfAxs (addAxs O (typeAxs C a))).isEmpty = false)
    (hc : SelfChecks (addAxs O (typeAxs C a))) (hint : Option RawHint) :
    (owlSelfTypeRow O C a hint).isSome = true :=
  rowSS_complete hO (typeAxs_okSS C a) hS hc hint

theorem owlSelfSameRow_complete {O : OWL.Ontology} (a b : IRI) (hO : O.isSROIQDSKB = true)
    (hS : (selfAxs (addAxs O (sameAxs a b))).isEmpty = false)
    (hc : SelfChecks (addAxs O (sameAxs a b))) (hint : Option RawHint) :
    (owlSelfSameRow O a b hint).isSome = true :=
  rowSS_complete hO (sameAxs_okSS a b) hS hc hint

theorem owlSelfSubRow_complete {O : OWL.Ontology} (A B : IRI) (hO : O.isSROIQDSKB = true)
    (hS : (selfAxs (addAxs O (subAxs O A B))).isEmpty = false)
    (hc : SelfChecks (addAxs O (subAxs O A B))) (hint : Option RawHint) :
    (owlSelfSubRow O A B hint).isSome = true :=
  rowSS_complete hO (subAxs_okSS O A B) hS hc hint

theorem owlSelfDiffRow_complete {O : OWL.Ontology} (a b : IRI) (hO : O.isSROIQDSKB = true)
    (hS : (selfAxs (addAxs O (diffAxs a b))).isEmpty = false)
    (hc : SelfChecks (addAxs O (diffAxs a b))) (hint : Option RawHint) :
    (owlSelfDiffRow O a b hint).isSome = true :=
  rowSS_complete hO (diffAxs_okSS a b) hS hc hint

theorem owlSelfRoleRow_complete {O : OWL.Ontology} {r : ObjProp} (hr : r.isBasic = true)
    (a b : IRI) (hO : O.isSROIQDSKB = true) (hS : (selfAxs (addAxs O (roleAxs r a b))).isEmpty = false)
    (hc : SelfChecks (addAxs O (roleAxs r a b)))
    (hint : Option RawHint) : (owlSelfRoleRow O r a b hint).isSome = true := by
  unfold owlSelfRoleRow
  rw [if_pos hr]
  exact rowSS_complete hO (fun ax hax => isSROIQDSKB_ax_of_isSHOIQDKB (roleAxs_ok hr a b ax hax))
    hS hc hint

theorem owlSelfNRoleRow_complete {O : OWL.Ontology} {r : ObjProp} (hr : r.isBasic = true)
    (a b : IRI) (hO : O.isSROIQDSKB = true) (hS : (selfAxs (addAxs O (nroleAxs r a b))).isEmpty = false)
    (hc : SelfChecks (addAxs O (nroleAxs r a b)))
    (hint : Option RawHint) : (owlSelfNRoleRow O r a b hint).isSome = true := by
  unfold owlSelfNRoleRow
  rw [if_pos hr]
  exact rowSS_complete hO (fun ax hax => isSROIQDSKB_ax_of_isSHOIQDKB (nroleAxs_ok hr a b ax hax))
    hS hc hint


/-! ## With anonymous individuals, the previous route first -/

/-- **Type row**. -/
def owlSROIQDSTypeRow (O : Ontology) (C a : IRI) (hint : Option RawHint) : Option Bool :=
  match owlSROIQDATypeRow O C a hint with
  | some v => some v
  | none => owlSelfTypeRow (anonOff [a] O) C a hint

/-- **Same row**. -/
def owlSROIQDSSameRow (O : Ontology) (a b : IRI) (hint : Option RawHint) : Option Bool :=
  match owlSROIQDASameRow O a b hint with
  | some v => some v
  | none => owlSelfSameRow (anonOff [a, b] O) a b hint

/-- **Subsumption row**. -/
def owlSROIQDSSubRow (O : Ontology) (A B : IRI) (hint : Option RawHint) : Option Bool :=
  match owlSROIQDASubRow O A B hint with
  | some v => some v
  | none => owlSelfSubRow (anonOff [] O) A B hint

/-- **Different row**. -/
def owlSROIQDSDiffRow (O : Ontology) (a b : IRI) (hint : Option RawHint) : Option Bool :=
  match owlSROIQDADiffRow O a b hint with
  | some v => some v
  | none => owlSelfDiffRow (anonOff [a, b] O) a b hint

/-- **Role row**. -/
def owlSROIQDSRoleRow (O : Ontology) (r : ObjProp) (a b : IRI) (hint : Option RawHint) :
    Option Bool :=
  match owlSROIQDARoleRow O r a b hint with
  | some v => some v
  | none => owlSelfRoleRow (anonOff [a, b] O) r a b hint

/-- **Negative role row**. -/
def owlSROIQDSNRoleRow (O : Ontology) (r : ObjProp) (a b : IRI) (hint : Option RawHint) :
    Option Bool :=
  match owlSROIQDANRoleRow O r a b hint with
  | some v => some v
  | none => owlSelfNRoleRow (anonOff [a, b] O) r a b hint

theorem rowSS_isSome {O : Ontology} {L : List Axiom} {hint : Option RawHint} {v : Bool}
    (h : rowSS O L hint = some v) : O.isSROIQDSKB = true := by
  obtain ⟨w, hw, -⟩ := Option.map_eq_some_iff.1 h
  have hk := (Bool.and_eq_true _ _ ▸ ((owlSelfCore_isSome_iff (addAxs O L) hint).1
    (by rw [hw]; rfl)).1).1
  rw [isSROIQDSKB_addAxs, Bool.and_eq_true] at hk
  exact hk.1

theorem owlSROIQDSTypeRow_sound (pat : String → String → Prop) {O : Ontology} {C a : IRI}
    {hint : Option RawHint} {v : Bool} (h : owlSROIQDSTypeRow O C a hint = some v) :
    v = true ↔ EntailsAt (owl2MapP pat) O (.classAssertion (.cls C) (.named a)) := by
  unfold owlSROIQDSTypeRow at h
  split at h
  next v' hv =>
    simp only [Option.some.injEq] at h; subst h
    exact owlSROIQDATypeRow_sound pat hv
  next =>
    have hk := noKey_of_anonOffS (rowSS_isSome h)
    rw [owlSelfTypeRow_sound pat h, entailsAt_anonOff hk (by
      simp only [Axiom.mapI, ClassExpr.mapI, anonG_fix (List.mem_singleton_self a)]) rfl]

theorem owlSROIQDSSameRow_sound (pat : String → String → Prop) {O : Ontology} {a b : IRI}
    {hint : Option RawHint} {v : Bool} (h : owlSROIQDSSameRow O a b hint = some v) :
    v = true ↔ EntailsAt (owl2MapP pat) O (.sameIndividual [.named a, .named b]) := by
  unfold owlSROIQDSSameRow at h
  split at h
  next v' hv =>
    simp only [Option.some.injEq] at h; subst h
    exact owlSROIQDASameRow_sound pat hv
  next =>
    have hk := noKey_of_anonOffS (rowSS_isSome h)
    rw [owlSelfSameRow_sound pat h, entailsAt_anonOff hk (by
      simp [Axiom.mapI, anonG_fix (W := [a, b]) (O := O) (a := a) (by simp),
        anonG_fix (W := [a, b]) (O := O) (a := b) (by simp)]) rfl]

theorem owlSROIQDSSubRow_sound (pat : String → String → Prop) {O : Ontology} {A B : IRI}
    {hint : Option RawHint} {v : Bool} (h : owlSROIQDSSubRow O A B hint = some v) :
    v = true ↔ EntailsSubAt (owl2MapP pat) O A B := by
  unfold owlSROIQDSSubRow at h
  split at h
  next v' hv =>
    simp only [Option.some.injEq] at h; subst h
    exact owlSROIQDASubRow_sound pat hv
  next =>
    have hk := noKey_of_anonOffS (rowSS_isSome h)
    rw [owlSelfSubRow_sound pat h, entailsSubAt_anonOff hk]

theorem owlSROIQDSDiffRow_sound (pat : String → String → Prop) {O : Ontology} {a b : IRI}
    {hint : Option RawHint} {v : Bool} (h : owlSROIQDSDiffRow O a b hint = some v) :
    v = true ↔ EntailsAt (owl2MapP pat) O (.differentIndividuals [.named a, .named b]) := by
  unfold owlSROIQDSDiffRow at h
  split at h
  next v' hv =>
    simp only [Option.some.injEq] at h; subst h
    exact owlSROIQDADiffRow_sound pat hv
  next =>
    have hk := noKey_of_anonOffS (rowSS_isSome h)
    rw [owlSelfDiffRow_sound pat h, entailsAt_anonOff hk (by
      simp [Axiom.mapI, anonG_fix (W := [a, b]) (O := O) (a := a) (by simp),
        anonG_fix (W := [a, b]) (O := O) (a := b) (by simp)]) rfl]

theorem owlSROIQDSRoleRow_sound (pat : String → String → Prop) {O : Ontology} {r : ObjProp}
    {a b : IRI} {hint : Option RawHint} {v : Bool} (h : owlSROIQDSRoleRow O r a b hint = some v) :
    v = true ↔ EntailsAt (owl2MapP pat) O (.objectPropertyAssertion r (.named a) (.named b)) := by
  unfold owlSROIQDSRoleRow at h
  split at h
  next v' hv =>
    simp only [Option.some.injEq] at h; subst h
    exact owlSROIQDARoleRow_sound pat hv
  next =>
    have h' := h
    unfold owlSelfRoleRow at h'
    split at h'
    swap
    · cases h'
    have hk := noKey_of_anonOffS (rowSS_isSome h')
    rw [owlSelfRoleRow_sound pat h, entailsAt_anonOff hk (by
      simp [Axiom.mapI, anonG_fix (W := [a, b]) (O := O) (a := a) (by simp),
        anonG_fix (W := [a, b]) (O := O) (a := b) (by simp)]) rfl]

theorem owlSROIQDSNRoleRow_sound (pat : String → String → Prop) {O : Ontology} {r : ObjProp}
    {a b : IRI} {hint : Option RawHint} {v : Bool} (h : owlSROIQDSNRoleRow O r a b hint = some v) :
    v = true ↔
      EntailsAt (owl2MapP pat) O (.negativeObjectPropertyAssertion r (.named a) (.named b)) := by
  unfold owlSROIQDSNRoleRow at h
  split at h
  next v' hv =>
    simp only [Option.some.injEq] at h; subst h
    exact owlSROIQDANRoleRow_sound pat hv
  next =>
    have h' := h
    unfold owlSelfNRoleRow at h'
    split at h'
    swap
    · cases h'
    have hk := noKey_of_anonOffS (rowSS_isSome h')
    rw [owlSelfNRoleRow_sound pat h, entailsAt_anonOff hk (by
      simp [Axiom.mapI, anonG_fix (W := [a, b]) (O := O) (a := a) (by simp),
        anonG_fix (W := [a, b]) (O := O) (a := b) (by simp)]) rfl]

/-- The type row answers when the previous route or this one does. -/
theorem owlSROIQDSTypeRow_complete {O : Ontology} (C a : IRI)
    (hO : (anonOff [a] O).isSROIQDSKB = true)
    (hS : (selfAxs (addAxs (anonOff [a] O) (typeAxs C a))).isEmpty = false)
    (hc : SelfChecks (addAxs (anonOff [a] O) (typeAxs C a))) (hint : Option RawHint) :
    (owlSROIQDSTypeRow O C a hint).isSome = true := by
  unfold owlSROIQDSTypeRow
  split
  · rfl
  · exact owlSelfTypeRow_complete C a hO hS hc hint

end ContextCalculus.OWLFrontend

#print axioms ContextCalculus.OWLFrontend.owlSelfTypeRow_sound
#print axioms ContextCalculus.OWLFrontend.owlSelfSubRow_sound
#print axioms ContextCalculus.OWLFrontend.owlSelfRoleRow_sound
#print axioms ContextCalculus.OWLFrontend.owlSROIQDSTypeRow_sound
#print axioms ContextCalculus.OWLFrontend.owlSROIQDSSameRow_sound
#print axioms ContextCalculus.OWLFrontend.owlSROIQDSSubRow_sound
#print axioms ContextCalculus.OWLFrontend.owlSROIQDSDiffRow_sound
#print axioms ContextCalculus.OWLFrontend.owlSROIQDSRoleRow_sound
#print axioms ContextCalculus.OWLFrontend.owlSROIQDSNRoleRow_sound
#print axioms ContextCalculus.OWLFrontend.owlSROIQDSTypeRow_complete
