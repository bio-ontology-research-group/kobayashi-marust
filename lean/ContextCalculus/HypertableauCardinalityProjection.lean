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

def FiniteEqCertificate.checkMaximumDefExact
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (definition : CardinalityDef (Fin conceptCount) (Fin roleCount)) : Bool :=
  certificate.checkCardinalityDef definition &&
    certificate.checkMaximumRecognition definition

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

#print axioms mem_maximumBody
#print axioms mem_maximumHead
#print axioms not_injective_iff_equal_pair
#print axioms models_maximumProjectionClause_iff
#print axioms minimumExpansion_implies_definition
#print axioms minimumExpansionFunctions_models
#print axioms exists_minimumExpansion_iff
#print axioms modelsCardinalityDef_and_recognition_iff_exact
#print axioms modelsCardinalityDefExact_models
#print axioms FiniteEqCertificate.checkMaximumRecognition_sound
#print axioms FiniteEqCertificate.checkMaximumRecognition_complete
#print axioms FiniteEqCertificate.checkMaximumRecognition_eq_true_iff
#print axioms FiniteEqCertificate.checkMaximumDefExact_eq_true_iff

end ContextCalculus.Hypertableau
