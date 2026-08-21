import ContextCalculus.HypertableauCardinalityCertificate
import Mathlib.Data.List.FinRange

/-!
# Source-clause projection for first-class cardinality definitions

The frontend clausifies `Q ⊑ ≤ n r.C` as one universally quantified
pigeonhole clause.  Production may replace that clause with a first-class
`CardinalityDef`.  This module proves the two representations have exactly the
same models.  Minimum-cardinality Skolem bundles and recognition-marker
exactness are composed separately.
-/

namespace ContextCalculus.Hypertableau

abbrev MaximumVariable (n : Nat) := Option (Fin (n + 1))

def maximumSource : MaximumVariable n := none

def maximumWitness (index : Fin (n + 1)) : MaximumVariable n := some index

def maximumBody (marker filler : Concept) (role : Role) (n : Nat) :
    List (Atom (MaximumVariable n) Concept Role) :=
  .concept (.pos marker) maximumSource ::
    (List.finRange (n + 1)).flatMap fun index =>
      [.role role maximumSource (maximumWitness index),
        .concept (.pos filler) (maximumWitness index)]

def maximumHead (n : Nat) :
    List (Atom (MaximumVariable n) Concept Role) :=
  (List.finRange (n + 1)).flatMap fun left =>
    (List.finRange (n + 1)).flatMap fun right =>
      if left < right then [.eq (maximumWitness left) (maximumWitness right)] else []

def maximumProjectionClause (definition : CardinalityDef Concept Role) :
    Clause (MaximumVariable definition.bound) Concept Role := {
  body := maximumBody definition.marker definition.filler definition.role definition.bound
  head := maximumHead definition.bound
}

theorem mem_maximumBody {atom : Atom (MaximumVariable n) Concept Role} :
    atom ∈ maximumBody marker filler role n ↔
      atom = .concept (.pos marker) maximumSource ∨
      ∃ index, atom = .role role maximumSource (maximumWitness index) ∨
        atom = .concept (.pos filler) (maximumWitness index) := by
  simp only [maximumBody, List.mem_cons, List.mem_flatMap, List.mem_finRange,
    true_and]
  aesop

theorem mem_maximumHead {atom : Atom (MaximumVariable n) Concept Role} :
    atom ∈ maximumHead n ↔
      ∃ left right, left < right ∧
        atom = .eq (maximumWitness left) (maximumWitness right) := by
  simp only [maximumHead, List.mem_flatMap, List.mem_finRange, true_and]
  constructor
  · rintro ⟨left, right, hmem⟩
    by_cases hlt : left < right
    · simp only [hlt, if_true, List.mem_singleton] at hmem
      exact ⟨left, right, hlt, hmem⟩
    · simp only [hlt, if_false, List.not_mem_nil] at hmem
  · rintro ⟨left, right, hlt, rfl⟩
    exact ⟨left, right, by simp [hlt]⟩

theorem not_injective_iff_equal_pair
    (values : Fin count → Domain) :
    ¬_root_.Function.Injective values ↔
      ∃ left right, left < right ∧ values left = values right := by
  constructor
  · intro hnot
    rcases Function.not_injective_iff.mp hnot with ⟨left, right, hequal, hne⟩
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact ⟨left, right, hlt, hequal⟩
    · exact ⟨right, left, hgt, hequal.symm⟩
  · rintro ⟨left, right, hlt, hequal⟩ hinjective
    exact (ne_of_lt hlt) (hinjective hequal)

theorem models_maximumProjectionClause_iff
    (I : Interp Domain Concept Role)
    (definition : CardinalityDef Concept Role)
    (hkind : definition.kind = .maximum) :
    I.modelsClause (maximumProjectionClause definition) ↔
      I.modelsCardinalityDef definition := by
  constructor
  · intro hclause source hmarker
    have hmaximum : HasAtMost definition.bound
        (I.cardinalitySuccessor definition source) := by
      intro hatLeast
      rcases hatLeast with ⟨witnesses, hinjective, hsuccessors⟩
      let assignment : MaximumVariable definition.bound → Domain
        | none => source
        | some index => witnesses index
      have hbody : ∀ atom ∈ (maximumProjectionClause definition).body,
          I.satAtom assignment atom := by
        intro atom hatom
        change atom ∈ maximumBody definition.marker definition.filler
          definition.role definition.bound at hatom
        rw [mem_maximumBody] at hatom
        rcases hatom with rfl | ⟨index, rfl | rfl⟩
        · exact hmarker
        · exact (hsuccessors index).1
        · exact (hsuccessors index).2
      rcases hclause assignment hbody with ⟨atom, hatom, hsat⟩
      change atom ∈ maximumHead definition.bound at hatom
      rw [mem_maximumHead] at hatom
      rcases hatom with ⟨left, right, hlt, rfl⟩
      exact (ne_of_lt hlt) (hinjective hsat)
    simpa [Interp.modelsCardinalityDef, hkind] using hmaximum
  · intro hdefinition assignment hbody
    have hmarker := hbody (.concept (.pos definition.marker) maximumSource)
      (by simp [maximumProjectionClause, maximumBody])
    have hmaximum : HasAtMost definition.bound
        (I.cardinalitySuccessor definition (assignment maximumSource)) := by
      simpa [Interp.modelsCardinalityDef, hkind] using
        hdefinition (assignment maximumSource) hmarker
    let witnesses : Fin (definition.bound + 1) → Domain :=
      fun index => assignment (maximumWitness index)
    have hsuccessors : ∀ index,
        I.cardinalitySuccessor definition (assignment maximumSource)
          (witnesses index) := by
      intro index
      constructor
      · exact hbody (.role definition.role maximumSource (maximumWitness index))
          (by
            change _ ∈ maximumBody definition.marker definition.filler
              definition.role definition.bound
            rw [mem_maximumBody]
            exact Or.inr ⟨index, Or.inl rfl⟩)
      · exact hbody (.concept (.pos definition.filler) (maximumWitness index))
          (by
            change _ ∈ maximumBody definition.marker definition.filler
              definition.role definition.bound
            rw [mem_maximumBody]
            exact Or.inr ⟨index, Or.inr rfl⟩)
    have hnotInjective : ¬_root_.Function.Injective witnesses :=
      not_injective_of_hasAtMost hmaximum witnesses hsuccessors
    rcases (not_injective_iff_equal_pair witnesses).1 hnotInjective with
      ⟨left, right, hlt, hequal⟩
    refine ⟨.eq (maximumWitness left) (maximumWitness right), ?_, ?_⟩
    · change _ ∈ maximumHead definition.bound
      rw [mem_maximumHead]
      exact ⟨left, right, hlt, rfl⟩
    · exact hequal

abbrev MinimumSkolemInterp (Domain : Type*) (bound : Nat) :=
  Fin bound → Domain → Domain

def ModelsMinimumExpansion
    (I : Interp Domain Concept Role)
    (definition : CardinalityDef Concept Role)
    (functions : MinimumSkolemInterp Domain definition.bound) : Prop :=
  ∀ source, I.concept definition.marker source →
    (∀ index, I.role definition.role source (functions index source) ∧
      I.concept definition.filler (functions index source)) ∧
    _root_.Function.Injective (fun index => functions index source)

theorem minimumExpansion_implies_definition
    (I : Interp Domain Concept Role)
    (definition : CardinalityDef Concept Role)
    (hkind : definition.kind = .minimum)
    (functions : MinimumSkolemInterp Domain definition.bound)
    (hexpansion : ModelsMinimumExpansion I definition functions) :
    I.modelsCardinalityDef definition := by
  intro source hmarker
  have hexpansionAt := hexpansion source hmarker
  have hatLeast : HasAtLeast definition.bound
      (I.cardinalitySuccessor definition source) := by
    refine ⟨fun index => functions index source, hexpansionAt.2, ?_⟩
    intro index
    exact hexpansionAt.1 index
  simpa [Interp.modelsCardinalityDef, hkind] using hatLeast

noncomputable def minimumExpansionFunctions
    (I : Interp Domain Concept Role)
    (definition : CardinalityDef Concept Role)
    (hkind : definition.kind = .minimum)
    (hdefinition : I.modelsCardinalityDef definition) :
    MinimumSkolemInterp Domain definition.bound := by
  classical
  exact fun index source =>
    if hmarker : I.concept definition.marker source then
      (Classical.choose (by
        have := hdefinition source hmarker
        simpa [Interp.modelsCardinalityDef, hkind] using this) :
          Fin definition.bound → Domain) index
    else source

theorem minimumExpansionFunctions_models
    (I : Interp Domain Concept Role)
    (definition : CardinalityDef Concept Role)
    (hkind : definition.kind = .minimum)
    (hdefinition : I.modelsCardinalityDef definition) :
    ModelsMinimumExpansion I definition
      (minimumExpansionFunctions I definition hkind hdefinition) := by
  intro source hmarker
  have hatLeast : HasAtLeast definition.bound
      (I.cardinalitySuccessor definition source) := by
    have := hdefinition source hmarker
    simpa [Interp.modelsCardinalityDef, hkind] using this
  have hchosen := Classical.choose_spec hatLeast
  constructor
  · intro index
    simpa [minimumExpansionFunctions, hmarker] using hchosen.2 index
  · intro left right hequal
    apply hchosen.1
    simpa [minimumExpansionFunctions, hmarker] using hequal

theorem exists_minimumExpansion_iff
    (I : Interp Domain Concept Role)
    (definition : CardinalityDef Concept Role)
    (hkind : definition.kind = .minimum) :
    (∃ functions : MinimumSkolemInterp Domain definition.bound,
      ModelsMinimumExpansion I definition functions) ↔
      I.modelsCardinalityDef definition := by
  constructor
  · rintro ⟨functions, hexpansion⟩
    exact minimumExpansion_implies_definition I definition hkind functions hexpansion
  · intro hdefinition
    exact ⟨minimumExpansionFunctions I definition hkind hdefinition,
      minimumExpansionFunctions_models I definition hkind hdefinition⟩

def Interp.cardinalityCondition
    (I : Interp Domain Concept Role)
    (definition : CardinalityDef Concept Role) (source : Domain) : Prop :=
  match definition.kind with
  | .minimum => HasAtLeast definition.bound (I.cardinalitySuccessor definition source)
  | .maximum => HasAtMost definition.bound (I.cardinalitySuccessor definition source)

def Interp.modelsCardinalityRecognition
    (I : Interp Domain Concept Role)
    (definition : CardinalityDef Concept Role) : Prop :=
  ∀ source, I.cardinalityCondition definition source →
    I.concept definition.marker source

def Interp.modelsCardinalityDefExact
    (I : Interp Domain Concept Role)
    (definition : CardinalityDef Concept Role) : Prop :=
  ∀ source, I.concept definition.marker source ↔
    I.cardinalityCondition definition source

structure ComplementaryCardinalityPair
    (maximum minimum : CardinalityDef Concept Role) : Prop where
  maximum_kind : maximum.kind = .maximum
  minimum_kind : minimum.kind = .minimum
  minimum_bound : minimum.bound = maximum.bound + 1
  same_role : minimum.role = maximum.role
  same_filler : minimum.filler = maximum.filler

def Interp.modelsCardinalitySplit
    (I : Interp Domain Concept Role)
    (maximum minimum : CardinalityDef Concept Role) : Prop :=
  ∀ source,
    (I.concept maximum.marker source ∨ I.concept minimum.marker source) ∧
    ¬(I.concept maximum.marker source ∧ I.concept minimum.marker source)

def cardinalitySplitClause
    (maximum minimum : CardinalityDef Concept Role) : Clause Unit Concept Role := {
  body := []
  head := [.concept (.pos maximum.marker) (), .concept (.pos minimum.marker) ()]
}

def cardinalityClashClause
    (maximum minimum : CardinalityDef Concept Role) : Clause Unit Concept Role := {
  body := [.concept (.pos maximum.marker) (), .concept (.pos minimum.marker) ()]
  head := []
}

def cardinalitySplitTheory
    (maximum minimum : CardinalityDef Concept Role) : List (Clause Unit Concept Role) :=
  [cardinalitySplitClause maximum minimum,
    cardinalityClashClause maximum minimum]

theorem models_cardinalitySplitClause_iff
    (I : Interp Domain Concept Role) :
    I.modelsClause (cardinalitySplitClause maximum minimum) ↔
      ∀ source, I.concept maximum.marker source ∨
        I.concept minimum.marker source := by
  constructor
  · intro hmodels source
    rcases hmodels (fun _ => source) (by
      intro atom hmem
      simp [cardinalitySplitClause] at hmem) with ⟨atom, hmem, hsat⟩
    simp [cardinalitySplitClause] at hmem
    rcases hmem with rfl | rfl
    · exact Or.inl hsat
    · exact Or.inr hsat
  · intro hmodels assignment _
    rcases hmodels (assignment ()) with hmaximum | hminimum
    · exact ⟨.concept (.pos maximum.marker) (), by simp [cardinalitySplitClause], hmaximum⟩
    · exact ⟨.concept (.pos minimum.marker) (), by simp [cardinalitySplitClause], hminimum⟩

theorem models_cardinalityClashClause_iff
    (I : Interp Domain Concept Role) :
    I.modelsClause (cardinalityClashClause maximum minimum) ↔
      ∀ source, ¬(I.concept maximum.marker source ∧
        I.concept minimum.marker source) := by
  constructor
  · intro hmodels source hboth
    rcases hmodels (fun _ => source) (by
      intro atom hmem
      simp [cardinalityClashClause] at hmem
      rcases hmem with rfl | rfl
      · exact hboth.1
      · exact hboth.2) with ⟨atom, hmem, _⟩
    simp [cardinalityClashClause] at hmem
  · intro hmodels assignment hbody
    exfalso
    apply hmodels (assignment ())
    constructor
    · exact hbody (.concept (.pos maximum.marker) ()) (by
        simp [cardinalityClashClause])
    · exact hbody (.concept (.pos minimum.marker) ()) (by
        simp [cardinalityClashClause])

theorem models_cardinalitySplitTheory_iff
    (I : Interp Domain Concept Role) :
    I.models (cardinalitySplitTheory maximum minimum) ↔
      I.modelsCardinalitySplit maximum minimum := by
  rw [Interp.models, Interp.modelsCardinalitySplit]
  simp only [cardinalitySplitTheory]
  constructor
  · intro hmodels source
    constructor
    · exact (models_cardinalitySplitClause_iff I).mp
        (hmodels _ (by simp)) source
    · exact (models_cardinalityClashClause_iff I).mp
        (hmodels _ (by simp)) source
  · intro hmodels clause hmem
    simp at hmem
    rcases hmem with rfl | rfl
    · exact (models_cardinalitySplitClause_iff I).mpr fun source => (hmodels source).1
    · exact (models_cardinalityClashClause_iff I).mpr fun source => (hmodels source).2

theorem ComplementaryCardinalityPair.minimumSuccessor_eq
    (maximum minimum : CardinalityDef Concept Role)
    (pair : ComplementaryCardinalityPair maximum minimum)
    (I : Interp Domain Concept Role) (source : Domain) :
    I.cardinalitySuccessor minimum source =
      I.cardinalitySuccessor maximum source := by
  funext target
  simp [Interp.cardinalitySuccessor, pair.same_role, pair.same_filler]

theorem complementary_models_and_split_iff_exact
    (I : Interp Domain Concept Role)
    (maximum minimum : CardinalityDef Concept Role)
    (pair : ComplementaryCardinalityPair maximum minimum) :
    (I.modelsCardinalityDef maximum ∧
        I.modelsCardinalityDef minimum ∧
        I.modelsCardinalitySplit maximum minimum) ↔
      (I.modelsCardinalityDefExact maximum ∧
        I.modelsCardinalityDefExact minimum) := by
  have hsuccessor : ∀ source,
      I.cardinalitySuccessor minimum source =
        I.cardinalitySuccessor maximum source :=
    ComplementaryCardinalityPair.minimumSuccessor_eq maximum minimum pair I
  constructor
  · rintro ⟨hmaximum, hminimum, hsplit⟩
    constructor
    · intro source
      constructor
      · intro hmarker
        simpa [Interp.cardinalityCondition, pair.maximum_kind] using
          hmaximum source hmarker
      · intro hatMost
        have hatMostMaximum : HasAtMost maximum.bound
            (I.cardinalitySuccessor maximum source) := by
          simpa [Interp.cardinalityCondition, pair.maximum_kind] using hatMost
        rcases (hsplit source).1 with hmarker | hminimumMarker
        · exact hmarker
        · have hatLeast := hminimum source hminimumMarker
          have hatLeastMaximum : HasAtLeast (maximum.bound + 1)
              (I.cardinalitySuccessor maximum source) := by
            simpa [Interp.modelsCardinalityDef, pair.minimum_kind,
              pair.minimum_bound, hsuccessor source] using hatLeast
          exact False.elim (hatMostMaximum hatLeastMaximum)
    · intro source
      constructor
      · intro hmarker
        have hatLeast := hminimum source hmarker
        simpa [Interp.cardinalityCondition, pair.minimum_kind,
          pair.minimum_bound, hsuccessor source] using hatLeast
      · intro hatLeast
        rcases (hsplit source).1 with hmaximumMarker | hmarker
        · have hatMost := hmaximum source hmaximumMarker
          have hatMostMaximum : HasAtMost maximum.bound
              (I.cardinalitySuccessor maximum source) := by
            simpa [Interp.modelsCardinalityDef, pair.maximum_kind] using hatMost
          have hatLeastMaximum : HasAtLeast (maximum.bound + 1)
              (I.cardinalitySuccessor maximum source) := by
            simpa [Interp.cardinalityCondition, pair.minimum_kind,
              pair.minimum_bound, hsuccessor source] using hatLeast
          exact False.elim (hatMostMaximum hatLeastMaximum)
        · exact hmarker
  · rintro ⟨hmaximum, hminimum⟩
    have hmaximumDef : I.modelsCardinalityDef maximum := by
      intro source hmarker
      simpa [Interp.cardinalityCondition, Interp.modelsCardinalityDef] using
        (hmaximum source).mp hmarker
    have hminimumDef : I.modelsCardinalityDef minimum := by
      intro source hmarker
      simpa [Interp.cardinalityCondition, Interp.modelsCardinalityDef] using
        (hminimum source).mp hmarker
    refine ⟨hmaximumDef, hminimumDef, ?_⟩
    intro source
    have hmaximumCondition := hmaximum source
    have hminimumCondition := hminimum source
    constructor
    · by_cases hatMost : HasAtMost maximum.bound
          (I.cardinalitySuccessor maximum source)
      · exact Or.inl (hmaximumCondition.mpr (by
          simpa [Interp.cardinalityCondition, pair.maximum_kind] using hatMost))
      · right
        apply hminimumCondition.mpr
        simpa [Interp.cardinalityCondition, pair.minimum_kind,
          pair.minimum_bound, hsuccessor source, HasAtMost] using hatMost
    · rintro ⟨hmaximumMarker, hminimumMarker⟩
      have hatMost := hmaximumCondition.mp hmaximumMarker
      have hatLeast := hminimumCondition.mp hminimumMarker
      have hatMostMaximum : HasAtMost maximum.bound
          (I.cardinalitySuccessor maximum source) := by
        simpa [Interp.cardinalityCondition, pair.maximum_kind] using hatMost
      have hatLeastMaximum : HasAtLeast (maximum.bound + 1)
          (I.cardinalitySuccessor maximum source) := by
        simpa [Interp.cardinalityCondition, pair.minimum_kind,
          pair.minimum_bound, hsuccessor source] using hatLeast
      exact hatMostMaximum hatLeastMaximum

theorem complementary_sourceTheory_iff_exact
    (I : Interp Domain Concept Role)
    (maximum minimum : CardinalityDef Concept Role)
    (pair : ComplementaryCardinalityPair maximum minimum) :
    (I.modelsCardinalityDef maximum ∧
        I.modelsCardinalityDef minimum ∧
        I.models (cardinalitySplitTheory maximum minimum)) ↔
      (I.modelsCardinalityDefExact maximum ∧
        I.modelsCardinalityDefExact minimum) := by
  rw [models_cardinalitySplitTheory_iff]
  exact complementary_models_and_split_iff_exact I maximum minimum pair

/-- Complete semantic contract for the exact frontend cardinality family:
the maximum pigeonhole clause, the minimum Skolem expansion, and the
excluded-middle/clash pair can be replaced by two exact first-class
definitions, and conversely. -/
theorem frontendCardinalityFamily_sat_iff_exact
    (I : Interp Domain Concept Role)
    (maximum minimum : CardinalityDef Concept Role)
    (pair : ComplementaryCardinalityPair maximum minimum) :
    (I.modelsClause (maximumProjectionClause maximum) ∧
        (∃ functions : MinimumSkolemInterp Domain minimum.bound,
          ModelsMinimumExpansion I minimum functions) ∧
        I.models (cardinalitySplitTheory maximum minimum)) ↔
      (I.modelsCardinalityDefExact maximum ∧
        I.modelsCardinalityDefExact minimum) := by
  rw [models_maximumProjectionClause_iff I maximum pair.maximum_kind,
    exists_minimumExpansion_iff I minimum pair.minimum_kind,
    models_cardinalitySplitTheory_iff]
  exact complementary_models_and_split_iff_exact I maximum minimum pair

theorem modelsCardinalityDef_and_recognition_iff_exact
    (I : Interp Domain Concept Role)
    (definition : CardinalityDef Concept Role) :
    I.modelsCardinalityDef definition ∧
        I.modelsCardinalityRecognition definition ↔
      I.modelsCardinalityDefExact definition := by
  constructor
  · rintro ⟨hdefinition, hrecognition⟩ source
    constructor
    · intro hmarker
      simpa [Interp.cardinalityCondition, Interp.modelsCardinalityDef] using
        hdefinition source hmarker
    · exact hrecognition source
  · intro hexact
    constructor
    · intro source hmarker
      simpa [Interp.cardinalityCondition, Interp.modelsCardinalityDef] using
        (hexact source).1 hmarker
    · intro source hcondition
      exact (hexact source).2 hcondition

theorem modelsCardinalityDefExact_models
    (I : Interp Domain Concept Role)
    (definition : CardinalityDef Concept Role)
    (hexact : I.modelsCardinalityDefExact definition) :
    I.modelsCardinalityDef definition :=
  (modelsCardinalityDef_and_recognition_iff_exact I definition).2 hexact |>.1

def FiniteEqCertificate.checkMaximumRecognition
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (definition : CardinalityDef (Fin conceptCount) (Fin roleCount)) : Bool :=
  match definition.kind with
  | .minimum => true
  | .maximum =>
      (List.finRange nodeCount).all fun source =>
        certificate.quotientPositiveB source definition.marker ||
          (allAssignments nodeCount (definition.bound + 1)).any fun witnesses =>
            certificate.quotientInjectiveB witnesses &&
              (List.finRange (definition.bound + 1)).all fun index =>
              certificate.cardinalitySuccessorB definition source (witnesses index)

def FiniteEqCertificate.checkMinimumRecognition
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (definition : CardinalityDef (Fin conceptCount) (Fin roleCount)) : Bool :=
  match definition.kind with
  | .maximum => true
  | .minimum =>
      (List.finRange nodeCount).all fun source =>
        certificate.quotientPositiveB source definition.marker ||
          (allAssignments nodeCount definition.bound).all fun witnesses =>
            !certificate.quotientInjectiveB witnesses ||
              !(List.finRange definition.bound).all fun index =>
                certificate.cardinalitySuccessorB definition source (witnesses index)

def FiniteEqCertificate.checkCardinalityRecognition
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (definition : CardinalityDef (Fin conceptCount) (Fin roleCount)) : Bool :=
  match definition.kind with
  | .maximum => certificate.checkMaximumRecognition definition
  | .minimum => certificate.checkMinimumRecognition definition

theorem FiniteEqCertificate.checkMaximumRecognition_sound
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (hvalid : certificate.equalityClosureValidB = true)
    (definition : CardinalityDef (Fin conceptCount) (Fin roleCount))
    (hkind : definition.kind = .maximum)
    (hcheck : certificate.checkMaximumRecognition definition = true) :
    certificate.state.quotientCanonical.modelsCardinalityRecognition definition := by
  intro semanticSource hcondition
  rcases Quotient.exists_rep semanticSource with ⟨source, rfl⟩
  simp only [FiniteEqCertificate.checkMaximumRecognition, hkind,
    List.all_eq_true] at hcheck
  have hsource := hcheck source (List.mem_finRange source)
  cases hmarkerB : certificate.quotientPositiveB source definition.marker with
  | true =>
      exact (certificate.quotientPositiveB_eq_true hvalid source definition.marker).mp hmarkerB
  | false =>
      simp only [hmarkerB, Bool.false_or, List.any_eq_true, Bool.and_eq_true] at hsource
      rcases hsource with ⟨witnesses, _hwitnesses, hinjectiveB, hsuccessorsB⟩
      have hinjective : Function.Injective (fun index =>
          Quotient.mk certificate.state.nodeSetoid (witnesses index)) :=
        (certificate.quotientInjectiveB_eq_true hvalid witnesses).mp hinjectiveB
      have hsuccessors : ∀ index,
          certificate.state.quotientCanonical.cardinalitySuccessor definition
            (Quotient.mk certificate.state.nodeSetoid source)
            (Quotient.mk certificate.state.nodeSetoid (witnesses index)) := by
        intro index
        apply (certificate.cardinalitySuccessorB_eq_true hvalid definition source
          (witnesses index)).mp
        exact (List.all_eq_true.mp hsuccessorsB) index (List.mem_finRange index)
      have hmaximum : HasAtMost definition.bound
          (certificate.state.quotientCanonical.cardinalitySuccessor definition
            (Quotient.mk certificate.state.nodeSetoid source)) := by
        simpa [Interp.cardinalityCondition, hkind] using hcondition
      exact False.elim (hmaximum ⟨_, hinjective, hsuccessors⟩)

theorem FiniteEqCertificate.checkMaximumRecognition_complete
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (hvalid : certificate.equalityClosureValidB = true)
    (definition : CardinalityDef (Fin conceptCount) (Fin roleCount))
    (hkind : definition.kind = .maximum)
    (hrecognition :
      certificate.state.quotientCanonical.modelsCardinalityRecognition definition) :
    certificate.checkMaximumRecognition definition = true := by
  simp only [FiniteEqCertificate.checkMaximumRecognition, hkind, List.all_eq_true]
  intro source _
  cases hmarkerB : certificate.quotientPositiveB source definition.marker with
  | true => simp
  | false =>
      simp only [Bool.false_or, List.any_eq_true, Bool.and_eq_true]
      have hnotMarker : ¬certificate.state.quotientCanonical.concept definition.marker
          (Quotient.mk certificate.state.nodeSetoid source) := by
        intro hmarker
        have := (certificate.quotientPositiveB_eq_true hvalid source
          definition.marker).mpr hmarker
        simp [hmarkerB] at this
      have hnotMaximum : ¬HasAtMost definition.bound
          (certificate.state.quotientCanonical.cardinalitySuccessor definition
            (Quotient.mk certificate.state.nodeSetoid source)) := by
        intro hmaximum
        apply hnotMarker
        apply hrecognition
        simpa [Interp.cardinalityCondition, hkind] using hmaximum
      have hatLeast : HasAtLeast (definition.bound + 1)
          (certificate.state.quotientCanonical.cardinalitySuccessor definition
            (Quotient.mk certificate.state.nodeSetoid source)) := by
        simpa [HasAtMost] using hnotMaximum
      rcases hatLeast with ⟨semanticWitnesses, hinjective, hsuccessors⟩
      have representatives : ∀ index, ∃ node,
          Quotient.mk certificate.state.nodeSetoid node = semanticWitnesses index :=
        fun index => Quotient.exists_rep (semanticWitnesses index)
      choose witnesses hwitnesses using representatives
      refine ⟨witnesses, mem_allAssignments nodeCount (definition.bound + 1) witnesses,
        ?_, ?_⟩
      · apply (certificate.quotientInjectiveB_eq_true hvalid witnesses).mpr
        intro left right hequal
        apply hinjective
        simpa only [hwitnesses] using hequal
      · rw [List.all_eq_true]
        intro index _
        apply (certificate.cardinalitySuccessorB_eq_true hvalid definition source
          (witnesses index)).mpr
        simpa only [hwitnesses] using hsuccessors index

theorem FiniteEqCertificate.checkMaximumRecognition_eq_true_iff
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (hvalid : certificate.equalityClosureValidB = true)
    (definition : CardinalityDef (Fin conceptCount) (Fin roleCount))
    (hkind : definition.kind = .maximum) :
    certificate.checkMaximumRecognition definition = true ↔
      certificate.state.quotientCanonical.modelsCardinalityRecognition definition := by
  constructor
  · exact certificate.checkMaximumRecognition_sound hvalid definition hkind
  · exact certificate.checkMaximumRecognition_complete hvalid definition hkind

theorem FiniteEqCertificate.checkMinimumRecognition_sound
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (hvalid : certificate.equalityClosureValidB = true)
    (definition : CardinalityDef (Fin conceptCount) (Fin roleCount))
    (hkind : definition.kind = .minimum)
    (hcheck : certificate.checkMinimumRecognition definition = true) :
    certificate.state.quotientCanonical.modelsCardinalityRecognition definition := by
  intro semanticSource hcondition
  rcases Quotient.exists_rep semanticSource with ⟨source, rfl⟩
  simp only [FiniteEqCertificate.checkMinimumRecognition, hkind,
    List.all_eq_true] at hcheck
  have hsource := hcheck source (List.mem_finRange source)
  cases hmarkerB : certificate.quotientPositiveB source definition.marker with
  | true =>
      exact (certificate.quotientPositiveB_eq_true hvalid source definition.marker).mp hmarkerB
  | false =>
      simp only [hmarkerB, Bool.false_or] at hsource
      have hatLeast : HasAtLeast definition.bound
          (certificate.state.quotientCanonical.cardinalitySuccessor definition
            (Quotient.mk certificate.state.nodeSetoid source)) := by
        simpa [Interp.cardinalityCondition, hkind] using hcondition
      rcases hatLeast with ⟨semanticWitnesses, hinjective, hsuccessors⟩
      have representatives : ∀ index, ∃ node,
          Quotient.mk certificate.state.nodeSetoid node = semanticWitnesses index :=
        fun index => Quotient.exists_rep (semanticWitnesses index)
      choose witnesses hwitnesses using representatives
      have hcandidate := (List.all_eq_true.mp hsource) witnesses
        (mem_allAssignments nodeCount definition.bound witnesses)
      have hinjectiveB : certificate.quotientInjectiveB witnesses = true :=
        (certificate.quotientInjectiveB_eq_true hvalid witnesses).mpr (by
          intro left right hequal
          apply hinjective
          simpa only [hwitnesses] using hequal)
      have hsuccessorsB : (List.finRange definition.bound).all (fun index =>
          certificate.cardinalitySuccessorB definition source (witnesses index)) = true := by
        rw [List.all_eq_true]
        intro index _
        apply (certificate.cardinalitySuccessorB_eq_true hvalid definition source
          (witnesses index)).mpr
        simpa only [hwitnesses] using hsuccessors index
      simp [hinjectiveB, hsuccessorsB] at hcandidate

theorem FiniteEqCertificate.checkMinimumRecognition_complete
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (hvalid : certificate.equalityClosureValidB = true)
    (definition : CardinalityDef (Fin conceptCount) (Fin roleCount))
    (hkind : definition.kind = .minimum)
    (hrecognition :
      certificate.state.quotientCanonical.modelsCardinalityRecognition definition) :
    certificate.checkMinimumRecognition definition = true := by
  simp only [FiniteEqCertificate.checkMinimumRecognition, hkind, List.all_eq_true]
  intro source _
  cases hmarkerB : certificate.quotientPositiveB source definition.marker with
  | true => simp
  | false =>
      simp only [Bool.false_or]
      rw [List.all_eq_true]
      intro witnesses _
      cases hinjectiveB : certificate.quotientInjectiveB witnesses with
      | false => simp
      | true =>
          simp only [Bool.not_true, Bool.false_or]
          cases hsuccessorsB : (List.finRange definition.bound).all (fun index =>
              certificate.cardinalitySuccessorB definition source (witnesses index)) with
          | false => simp
          | true =>
              have hatLeast : HasAtLeast definition.bound
                  (certificate.state.quotientCanonical.cardinalitySuccessor definition
                    (Quotient.mk certificate.state.nodeSetoid source)) := by
                refine ⟨fun index => Quotient.mk certificate.state.nodeSetoid
                  (witnesses index),
                  (certificate.quotientInjectiveB_eq_true hvalid witnesses).mp hinjectiveB, ?_⟩
                intro index
                apply (certificate.cardinalitySuccessorB_eq_true hvalid definition source
                  (witnesses index)).mp
                exact (List.all_eq_true.mp hsuccessorsB) index (List.mem_finRange index)
              have hmarker := hrecognition
                (Quotient.mk certificate.state.nodeSetoid source) (by
                  simpa [Interp.cardinalityCondition, hkind] using hatLeast)
              have := (certificate.quotientPositiveB_eq_true hvalid source
                definition.marker).mpr hmarker
              simp [hmarkerB] at this

theorem FiniteEqCertificate.checkCardinalityRecognition_eq_true_iff
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (hvalid : certificate.equalityClosureValidB = true)
    (definition : CardinalityDef (Fin conceptCount) (Fin roleCount)) :
    certificate.checkCardinalityRecognition definition = true ↔
      certificate.state.quotientCanonical.modelsCardinalityRecognition definition := by
  cases hkind : definition.kind with
  | minimum =>
      simp only [FiniteEqCertificate.checkCardinalityRecognition, hkind]
      exact ⟨certificate.checkMinimumRecognition_sound hvalid definition hkind,
        certificate.checkMinimumRecognition_complete hvalid definition hkind⟩
  | maximum =>
      simp only [FiniteEqCertificate.checkCardinalityRecognition, hkind]
      exact certificate.checkMaximumRecognition_eq_true_iff hvalid definition hkind

def FiniteEqCertificate.checkMaximumDefExact
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (definition : CardinalityDef (Fin conceptCount) (Fin roleCount)) : Bool :=
  certificate.checkCardinalityDef definition &&
    certificate.checkMaximumRecognition definition

def FiniteEqCertificate.checkCardinalityDefExact
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (definition : CardinalityDef (Fin conceptCount) (Fin roleCount)) : Bool :=
  certificate.checkCardinalityDef definition &&
    certificate.checkCardinalityRecognition definition

def FiniteEqCertificate.checkMaximumDefsExact
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount))) : Bool :=
  definitions.all certificate.checkMaximumDefExact

def FiniteEqCertificate.checkCardinalityDefsExact
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount))) : Bool :=
  definitions.all certificate.checkCardinalityDefExact

def Interp.modelsCardinalityDefsExact
    (I : Interp Domain Concept Role)
    (definitions : List (CardinalityDef Concept Role)) : Prop :=
  ∀ definition ∈ definitions, I.modelsCardinalityDefExact definition

theorem FiniteEqCertificate.checkMaximumDefExact_eq_true_iff
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (hvalid : certificate.equalityClosureValidB = true)
    (definition : CardinalityDef (Fin conceptCount) (Fin roleCount))
    (hkind : definition.kind = .maximum) :
    certificate.checkMaximumDefExact definition = true ↔
      certificate.state.quotientCanonical.modelsCardinalityDefExact definition := by
  rw [FiniteEqCertificate.checkMaximumDefExact, Bool.and_eq_true,
    certificate.checkCardinalityDef_eq_true_iff_models hvalid,
    certificate.checkMaximumRecognition_eq_true_iff hvalid definition hkind,
    modelsCardinalityDef_and_recognition_iff_exact]

theorem FiniteEqCertificate.checkCardinalityDefExact_eq_true_iff
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (hvalid : certificate.equalityClosureValidB = true)
    (definition : CardinalityDef (Fin conceptCount) (Fin roleCount)) :
    certificate.checkCardinalityDefExact definition = true ↔
      certificate.state.quotientCanonical.modelsCardinalityDefExact definition := by
  rw [FiniteEqCertificate.checkCardinalityDefExact, Bool.and_eq_true,
    certificate.checkCardinalityDef_eq_true_iff_models hvalid,
    certificate.checkCardinalityRecognition_eq_true_iff hvalid,
    modelsCardinalityDef_and_recognition_iff_exact]

theorem FiniteEqCertificate.checkMaximumDefsExact_sound
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (hvalid : certificate.equalityClosureValidB = true)
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (hmaximum : ∀ definition ∈ definitions, definition.kind = .maximum)
    (hcheck : certificate.checkMaximumDefsExact definitions = true) :
    certificate.state.quotientCanonical.modelsCardinalityDefsExact definitions := by
  intro definition hmem
  have hdefinition := (List.all_eq_true.mp hcheck) definition hmem
  exact (certificate.checkMaximumDefExact_eq_true_iff hvalid definition
    (hmaximum definition hmem)).mp hdefinition

theorem FiniteEqCertificate.checkCardinalityDefsExact_sound
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (hvalid : certificate.equalityClosureValidB = true)
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (hcheck : certificate.checkCardinalityDefsExact definitions = true) :
    certificate.state.quotientCanonical.modelsCardinalityDefsExact definitions := by
  intro definition hmem
  have hdefinition := (List.all_eq_true.mp hcheck) definition hmem
  exact (certificate.checkCardinalityDefExact_eq_true_iff hvalid definition).mp hdefinition

#print axioms mem_maximumBody
#print axioms mem_maximumHead
#print axioms not_injective_iff_equal_pair
#print axioms models_maximumProjectionClause_iff
#print axioms minimumExpansion_implies_definition
#print axioms minimumExpansionFunctions_models
#print axioms exists_minimumExpansion_iff
#print axioms ComplementaryCardinalityPair.minimumSuccessor_eq
#print axioms models_cardinalitySplitClause_iff
#print axioms models_cardinalityClashClause_iff
#print axioms models_cardinalitySplitTheory_iff
#print axioms complementary_models_and_split_iff_exact
#print axioms complementary_sourceTheory_iff_exact
#print axioms frontendCardinalityFamily_sat_iff_exact
#print axioms modelsCardinalityDef_and_recognition_iff_exact
#print axioms modelsCardinalityDefExact_models
#print axioms FiniteEqCertificate.checkMaximumRecognition_sound
#print axioms FiniteEqCertificate.checkMaximumRecognition_complete
#print axioms FiniteEqCertificate.checkMaximumRecognition_eq_true_iff
#print axioms FiniteEqCertificate.checkMinimumRecognition_sound
#print axioms FiniteEqCertificate.checkMinimumRecognition_complete
#print axioms FiniteEqCertificate.checkCardinalityRecognition_eq_true_iff
#print axioms FiniteEqCertificate.checkMaximumDefExact_eq_true_iff
#print axioms FiniteEqCertificate.checkCardinalityDefExact_eq_true_iff
#print axioms FiniteEqCertificate.checkMaximumDefsExact_sound
#print axioms FiniteEqCertificate.checkCardinalityDefsExact_sound

end ContextCalculus.Hypertableau
