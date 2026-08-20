import ContextCalculus.HypertableauCardinality
import ContextCalculus.HypertableauEqualityCertificate

/-!
# Executable cardinality checks for equality quotient models

The checker enumerates raw finite nodes but compares their supplied, validated
equality representatives.  The proofs below connect those computations to
cardinality in the canonical quotient model, so merged nodes are never counted
as distinct witnesses.
-/

namespace ContextCalculus.Hypertableau

def FiniteEqCertificate.quotientPositiveB
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (node : Fin nodeCount) (concept : Fin conceptCount) : Bool :=
  (List.finRange nodeCount).any fun source =>
    certificate.closedRelatedB source node &&
      decide ((source, .pos concept) ∈ certificate.base.labels)

theorem FiniteEqCertificate.quotientPositiveB_eq_true
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (hvalid : certificate.equalityClosureValidB = true)
    (node : Fin nodeCount) (concept : Fin conceptCount) :
    certificate.quotientPositiveB node concept = true ↔
      certificate.state.quotientCanonical.concept concept
        (Quotient.mk certificate.state.nodeSetoid node) := by
  simp only [FiniteEqCertificate.quotientPositiveB, List.any_eq_true,
    Bool.and_eq_true, decide_eq_true_eq, EqState.quotientCanonical]
  constructor
  · rintro ⟨source, _, hrelated, hlabel⟩
    exact ⟨source,
      Quotient.sound ((certificate.closedRelatedB_eq_true hvalid source node).mp hrelated),
      hlabel⟩
  · rintro ⟨source, heq, hlabel⟩
    exact ⟨source, List.mem_finRange source,
      (certificate.closedRelatedB_eq_true hvalid source node).mpr
        (Quotient.exact heq), hlabel⟩

def FiniteEqCertificate.quotientRoleB
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (role : Fin roleCount) (source target : Fin nodeCount) : Bool :=
  (List.finRange nodeCount).any fun edgeSource =>
    (List.finRange nodeCount).any fun edgeTarget =>
      (certificate.closedRelatedB edgeSource source &&
        certificate.closedRelatedB edgeTarget target) &&
        decide ((role, edgeSource, edgeTarget) ∈ certificate.base.edges)

theorem FiniteEqCertificate.quotientRoleB_eq_true
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (hvalid : certificate.equalityClosureValidB = true)
    (role : Fin roleCount) (source target : Fin nodeCount) :
    certificate.quotientRoleB role source target = true ↔
      certificate.state.quotientCanonical.role role
        (Quotient.mk certificate.state.nodeSetoid source)
        (Quotient.mk certificate.state.nodeSetoid target) := by
  simp only [FiniteEqCertificate.quotientRoleB, List.any_eq_true,
    Bool.and_eq_true, decide_eq_true_eq, EqState.quotientCanonical]
  constructor
  · rintro ⟨edgeSource, _, edgeTarget, _, ⟨hsource, htarget⟩, hedge⟩
    exact ⟨edgeSource, edgeTarget,
      Quotient.sound ((certificate.closedRelatedB_eq_true hvalid edgeSource source).mp hsource),
      Quotient.sound ((certificate.closedRelatedB_eq_true hvalid edgeTarget target).mp htarget),
      hedge⟩
  · rintro ⟨edgeSource, edgeTarget, hsource, htarget, hedge⟩
    exact ⟨edgeSource, List.mem_finRange edgeSource,
      edgeTarget, List.mem_finRange edgeTarget,
      ⟨(certificate.closedRelatedB_eq_true hvalid edgeSource source).mpr
          (Quotient.exact hsource),
        (certificate.closedRelatedB_eq_true hvalid edgeTarget target).mpr
          (Quotient.exact htarget)⟩, hedge⟩

def FiniteEqCertificate.cardinalitySuccessorB
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (definition : CardinalityDef (Fin conceptCount) (Fin roleCount))
    (source target : Fin nodeCount) : Bool :=
  certificate.quotientRoleB definition.role source target &&
    certificate.quotientPositiveB target definition.filler

theorem FiniteEqCertificate.cardinalitySuccessorB_eq_true
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (hvalid : certificate.equalityClosureValidB = true)
    (definition : CardinalityDef (Fin conceptCount) (Fin roleCount))
    (source target : Fin nodeCount) :
    certificate.cardinalitySuccessorB definition source target = true ↔
      certificate.state.quotientCanonical.cardinalitySuccessor definition
        (Quotient.mk certificate.state.nodeSetoid source)
        (Quotient.mk certificate.state.nodeSetoid target) := by
  simp only [FiniteEqCertificate.cardinalitySuccessorB, Bool.and_eq_true,
    Interp.cardinalitySuccessor]
  rw [certificate.quotientRoleB_eq_true hvalid,
    certificate.quotientPositiveB_eq_true hvalid]

def FiniteEqCertificate.quotientInjectiveB
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (witnesses : Fin arity → Fin nodeCount) : Bool :=
  (List.finRange arity).all fun left =>
    (List.finRange arity).all fun right =>
      decide (left = right) ||
        decide (certificate.representative (witnesses left) ≠
          certificate.representative (witnesses right))

theorem FiniteEqCertificate.quotientInjectiveB_representative
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (witnesses : Fin arity → Fin nodeCount) :
    certificate.quotientInjectiveB witnesses = true ↔
      Function.Injective (fun index => certificate.representative (witnesses index)) := by
  simp only [FiniteEqCertificate.quotientInjectiveB, List.all_eq_true,
    Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · intro h left right hequal
    rcases h left (List.mem_finRange left) right (List.mem_finRange right) with
      hsame | hdifferent
    · exact hsame
    · exact False.elim (hdifferent hequal)
  · intro hinjective left _ right _
    by_cases hsame : left = right
    · exact Or.inl hsame
    · exact Or.inr fun hequal => hsame (hinjective hequal)

theorem FiniteEqCertificate.quotientInjectiveB_eq_true
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (hvalid : certificate.equalityClosureValidB = true)
    (witnesses : Fin arity → Fin nodeCount) :
    certificate.quotientInjectiveB witnesses = true ↔
      Function.Injective (fun index =>
        Quotient.mk certificate.state.nodeSetoid (witnesses index)) := by
  rw [certificate.quotientInjectiveB_representative]
  constructor
  · intro hinjective left right heq
    apply hinjective
    exact (certificate.equalityClosureValidB_sound hvalid _ _).mp
      (Quotient.exact heq)
  · intro hinjective left right heq
    apply hinjective
    exact Quotient.sound
      ((certificate.equalityClosureValidB_sound hvalid _ _).mpr heq)

def FiniteEqCertificate.checkCardinalityDef
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (definition : CardinalityDef (Fin conceptCount) (Fin roleCount)) : Bool :=
  (List.finRange nodeCount).all fun source =>
    !certificate.quotientPositiveB source definition.marker ||
      match definition.kind with
      | .minimum =>
          (allAssignments nodeCount definition.bound).any fun witnesses =>
            certificate.quotientInjectiveB witnesses &&
              (List.finRange definition.bound).all fun index =>
                certificate.cardinalitySuccessorB definition source (witnesses index)
      | .maximum =>
          (allAssignments nodeCount (definition.bound + 1)).all fun witnesses =>
            !((List.finRange (definition.bound + 1)).all fun index =>
                certificate.cardinalitySuccessorB definition source (witnesses index)) ||
              !certificate.quotientInjectiveB witnesses

def FiniteEqCertificate.checkCardinalityDefs
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount))) : Bool :=
  certificate.equalityClosureValidB &&
    definitions.all certificate.checkCardinalityDef

theorem FiniteEqCertificate.checkCardinalityDef_sound
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (hvalid : certificate.equalityClosureValidB = true)
    (definition : CardinalityDef (Fin conceptCount) (Fin roleCount))
    (hcheck : certificate.checkCardinalityDef definition = true) :
    certificate.state.quotientCanonical.modelsCardinalityDef definition := by
  intro semanticSource hmarker
  rcases Quotient.exists_rep semanticSource with ⟨source, rfl⟩
  have hmarkerB : certificate.quotientPositiveB source definition.marker = true :=
    (certificate.quotientPositiveB_eq_true hvalid source definition.marker).mpr hmarker
  have hsource := (List.all_eq_true.mp hcheck) source (List.mem_finRange source)
  rw [hmarkerB] at hsource
  simp only [Bool.not_true, Bool.false_or] at hsource
  cases hkind : definition.kind with
    | minimum =>
        simp only [hkind] at hsource ⊢
        rw [List.any_eq_true] at hsource
        rcases hsource with ⟨witnesses, _, hwitness⟩
        simp only [Bool.and_eq_true] at hwitness
        rcases hwitness with ⟨hinjectiveB, hsuccessorsB⟩
        refine ⟨fun index => Quotient.mk certificate.state.nodeSetoid (witnesses index),
          (certificate.quotientInjectiveB_eq_true hvalid witnesses).mp hinjectiveB, ?_⟩
        intro index
        have hsuccessorB := (List.all_eq_true.mp hsuccessorsB) index
          (List.mem_finRange index)
        exact (certificate.cardinalitySuccessorB_eq_true hvalid definition source
          (witnesses index)).mp hsuccessorB
    | maximum =>
        simp only [hkind] at hsource ⊢
        intro hatLeast
        rcases hatLeast with ⟨semanticWitnesses, hinjective, hsuccessors⟩
        have representatives : ∀ index, ∃ node,
            Quotient.mk certificate.state.nodeSetoid node = semanticWitnesses index :=
          fun index => Quotient.exists_rep (semanticWitnesses index)
        choose witnesses hwitnesses using representatives
        have hwitnessesMem : witnesses ∈
            allAssignments nodeCount (definition.bound + 1) :=
          mem_allAssignments nodeCount (definition.bound + 1) witnesses
        have hassignment := (List.all_eq_true.mp hsource) witnesses hwitnessesMem
        have hsuccessorsB :
            (List.finRange (definition.bound + 1)).all (fun index =>
              certificate.cardinalitySuccessorB definition source (witnesses index)) = true := by
          rw [List.all_eq_true]
          intro index _
          apply (certificate.cardinalitySuccessorB_eq_true hvalid definition source
            (witnesses index)).mpr
          simpa only [hwitnesses] using hsuccessors index
        have hinjectiveRaw : Function.Injective (fun index =>
            Quotient.mk certificate.state.nodeSetoid (witnesses index)) := by
          intro left right heq
          apply hinjective
          simpa only [hwitnesses] using heq
        have hinjectiveB : certificate.quotientInjectiveB witnesses = true :=
          (certificate.quotientInjectiveB_eq_true hvalid witnesses).mpr hinjectiveRaw
        simp [hsuccessorsB, hinjectiveB] at hassignment

theorem FiniteEqCertificate.checkCardinalityDef_complete
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (hvalid : certificate.equalityClosureValidB = true)
    (definition : CardinalityDef (Fin conceptCount) (Fin roleCount))
    (hmodels : certificate.state.quotientCanonical.modelsCardinalityDef definition) :
    certificate.checkCardinalityDef definition = true := by
  rw [FiniteEqCertificate.checkCardinalityDef, List.all_eq_true]
  intro source _
  cases hmarkerB : certificate.quotientPositiveB source definition.marker with
  | false => simp
  | true =>
      have hmarker := (certificate.quotientPositiveB_eq_true hvalid source
        definition.marker).mp hmarkerB
      have hsource := hmodels
        (Quotient.mk certificate.state.nodeSetoid source) hmarker
      simp only [Bool.not_true, Bool.false_or]
      cases hkind : definition.kind with
      | minimum =>
          simp only [hkind] at hsource ⊢
          rcases hsource with ⟨semanticWitnesses, hinjective, hsuccessors⟩
          have representatives : ∀ index, ∃ node,
              Quotient.mk certificate.state.nodeSetoid node = semanticWitnesses index :=
            fun index => Quotient.exists_rep (semanticWitnesses index)
          choose witnesses hwitnesses using representatives
          rw [List.any_eq_true]
          refine ⟨witnesses, mem_allAssignments nodeCount definition.bound witnesses, ?_⟩
          rw [Bool.and_eq_true, certificate.quotientInjectiveB_eq_true hvalid,
            List.all_eq_true]
          refine ⟨?_, ?_⟩
          · intro left right heq
            apply hinjective
            simpa only [hwitnesses] using heq
          · intro index _
            apply (certificate.cardinalitySuccessorB_eq_true hvalid definition source
              (witnesses index)).mpr
            simpa only [hwitnesses] using hsuccessors index
      | maximum =>
          simp only [hkind] at hsource ⊢
          rw [List.all_eq_true]
          intro witnesses _
          by_cases hsuccessorsB :
              (List.finRange (definition.bound + 1)).all (fun index =>
                certificate.cardinalitySuccessorB definition source
                  (witnesses index)) = true
          · have hsuccessors : ∀ index,
                certificate.state.quotientCanonical.cardinalitySuccessor definition
                  (Quotient.mk certificate.state.nodeSetoid source)
                  (Quotient.mk certificate.state.nodeSetoid (witnesses index)) := by
              intro index
              apply (certificate.cardinalitySuccessorB_eq_true hvalid definition source
                (witnesses index)).mp
              exact (List.all_eq_true.mp hsuccessorsB) index
                (List.mem_finRange index)
            have hnotInjective : ¬Function.Injective (fun index =>
                Quotient.mk certificate.state.nodeSetoid (witnesses index)) :=
              not_injective_of_hasAtMost hsource
                (fun index => Quotient.mk certificate.state.nodeSetoid
                  (witnesses index)) hsuccessors
            have hinjectiveB : certificate.quotientInjectiveB witnesses = false := by
              cases hcheck : certificate.quotientInjectiveB witnesses with
              | false => rfl
              | true =>
                  exact False.elim (hnotInjective
                    ((certificate.quotientInjectiveB_eq_true hvalid witnesses).mp hcheck))
            simp [hsuccessorsB, hinjectiveB]
          · have hsuccessorsFalse :
                (List.finRange (definition.bound + 1)).all (fun index =>
                  certificate.cardinalitySuccessorB definition source
                    (witnesses index)) = false := by
              cases hcheck : (List.finRange (definition.bound + 1)).all (fun index =>
                  certificate.cardinalitySuccessorB definition source
                    (witnesses index)) with
              | false => rfl
              | true => exact False.elim (hsuccessorsB hcheck)
            simp [hsuccessorsFalse]

theorem FiniteEqCertificate.checkCardinalityDef_eq_true_iff_models
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (hvalid : certificate.equalityClosureValidB = true)
    (definition : CardinalityDef (Fin conceptCount) (Fin roleCount)) :
    certificate.checkCardinalityDef definition = true ↔
      certificate.state.quotientCanonical.modelsCardinalityDef definition := by
  constructor
  · exact certificate.checkCardinalityDef_sound hvalid definition
  · exact certificate.checkCardinalityDef_complete hvalid definition

theorem FiniteEqCertificate.checkCardinalityDefs_sound
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (hcheck : certificate.checkCardinalityDefs definitions = true) :
    certificate.state.quotientCanonical.modelsCardinalityDefs definitions := by
  simp only [FiniteEqCertificate.checkCardinalityDefs, Bool.and_eq_true,
    List.all_eq_true] at hcheck
  intro definition hdefinition
  exact certificate.checkCardinalityDef_sound hcheck.1 definition
    (hcheck.2 definition hdefinition)

theorem FiniteEqCertificate.checkCardinalityDefs_complete
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (hvalid : certificate.equalityClosureValidB = true)
    (hmodels : certificate.state.quotientCanonical.modelsCardinalityDefs definitions) :
    certificate.checkCardinalityDefs definitions = true := by
  simp only [FiniteEqCertificate.checkCardinalityDefs, Bool.and_eq_true,
    List.all_eq_true]
  exact ⟨hvalid, fun definition hdefinition =>
    certificate.checkCardinalityDef_complete hvalid definition
      (hmodels definition hdefinition)⟩

theorem FiniteEqCertificate.checkCardinalityDefs_eq_true_iff_models
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (hvalid : certificate.equalityClosureValidB = true) :
    certificate.checkCardinalityDefs definitions = true ↔
      certificate.state.quotientCanonical.modelsCardinalityDefs definitions := by
  constructor
  · exact certificate.checkCardinalityDefs_sound definitions
  · exact certificate.checkCardinalityDefs_complete definitions hvalid

def FiniteEqCertificate.checkEqSatWithCardinality
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount))) : Bool :=
  certificate.checkEqSat && certificate.checkCardinalityDefs definitions

theorem FiniteEqCertificate.checkEqSatWithCardinality_models
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (hcheck : certificate.checkEqSatWithCardinality definitions = true) :
    certificate.state.quotientCanonical.models certificate.base.ontology ∧
      certificate.state.quotientCanonical.modelsCardinalityDefs definitions := by
  simp only [FiniteEqCertificate.checkEqSatWithCardinality, Bool.and_eq_true] at hcheck
  exact ⟨certificate.checkEqSat_models hcheck.1,
    certificate.checkCardinalityDefs_sound definitions hcheck.2⟩

theorem FiniteEqCertificate.checkEqSatWithCardinality_eq_true_iff
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount))) :
    certificate.checkEqSatWithCardinality definitions = true ↔
      certificate.Valid ∧
        certificate.state.quotientCanonical.modelsCardinalityDefs definitions := by
  simp only [FiniteEqCertificate.checkEqSatWithCardinality, Bool.and_eq_true,
    certificate.checkEqSat_eq_true_iff_valid]
  constructor
  · rintro ⟨hvalid, hcardinality⟩
    exact ⟨hvalid,
      certificate.checkCardinalityDefs_sound definitions hcardinality⟩
  · rintro ⟨hvalid, hcardinality⟩
    exact ⟨hvalid, certificate.checkCardinalityDefs_complete definitions hvalid.1
      hcardinality⟩

theorem FiniteEqCertificate.checkEqSatWithCardinality_not_entailsSub
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (root : Fin nodeCount) (sub sup : Fin conceptCount)
    (hsub : (root, .pos sub) ∈ certificate.base.labels)
    (hnotSup : (root, .negated sup) ∈ certificate.base.labels)
    (hcheck : certificate.checkEqSatWithCardinality definitions = true) :
    ¬EntailsSubWithCardinality certificate.base.ontology definitions sub sup := by
  intro hentails
  have hparts := hcheck
  simp only [FiniteEqCertificate.checkEqSatWithCardinality, Bool.and_eq_true] at hparts
  have hmodels := certificate.checkEqSat_models hparts.1
  have hcards := certificate.checkCardinalityDefs_sound definitions hparts.2
  have hsatParts := hparts.1
  simp only [FiniteEqCertificate.checkEqSat, Bool.and_eq_true] at hsatParts
  have hvalid : certificate.equalityClosureValidB = true := hsatParts.1.1.1.1
  have hclashFalse : certificate.closedClashB = false := by
    simpa using hsatParts.1.1.2
  have hclash := certificate.not_closedClashB_closedClashFree hvalid hclashFalse
  let value : certificate.state.QuotientDomain :=
    Quotient.mk certificate.state.nodeSetoid root
  have hsubModel : certificate.state.quotientCanonical.concept sub value :=
    ⟨root, rfl, hsub⟩
  have hsupModel := hentails _ certificate.state.quotientCanonical hmodels hcards
    value hsubModel
  have hnegative := certificate.state.quotientCanonical_sat_closedLabel hclash
    root (.negated sup) ⟨root, certificate.state.equiv_equivalence.1 root, hnotSup⟩
  exact hnegative hsupModel

theorem FiniteEqCertificate.checkEqSatWithCardinality_not_unsatisfiableConcept
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (root : Fin nodeCount) (concept : Fin conceptCount)
    (hconcept : (root, .pos concept) ∈ certificate.base.labels)
    (hcheck : certificate.checkEqSatWithCardinality definitions = true) :
    ¬UnsatisfiableConceptWithCardinality certificate.base.ontology definitions concept := by
  intro hunsatisfiable
  have hmodels := certificate.checkEqSatWithCardinality_models definitions hcheck
  let value : certificate.state.QuotientDomain :=
    Quotient.mk certificate.state.nodeSetoid root
  exact hunsatisfiable _ certificate.state.quotientCanonical hmodels.1 hmodels.2 value
    ⟨root, rfl, hconcept⟩

namespace CardinalityCertificateTests

private def unmerged : FiniteEqCertificate 3 2 1 0 where
  base := {
    ontology := []
    labels := [(0, .pos 0), (1, .pos 1), (2, .pos 1)]
    edges := [(0, 0, 1), (0, 0, 2)]
    obligations := []
  }
  equalities := []
  representative := id
  representativePath := fun _ => []

private def merged : FiniteEqCertificate 3 2 1 0 where
  base := unmerged.base
  equalities := [(2, 1)]
  representative := fun node => if node = 2 then 1 else node
  representativePath := fun node => if node = 2 then [1] else []

private def minimumTwo : CardinalityDef (Fin 2) (Fin 1) where
  marker := 0
  kind := .minimum
  bound := 2
  role := 0
  filler := 1

private def maximumOne : CardinalityDef (Fin 2) (Fin 1) where
  marker := 0
  kind := .maximum
  bound := 1
  role := 0
  filler := 1

example : unmerged.checkCardinalityDefs [minimumTwo] = true := by native_decide
example : unmerged.checkCardinalityDefs [maximumOne] = false := by native_decide
example : merged.checkCardinalityDefs [minimumTwo] = false := by native_decide
example : merged.checkCardinalityDefs [maximumOne] = true := by native_decide
example : merged.checkEqSatWithCardinality [maximumOne] = true := by native_decide

end CardinalityCertificateTests

#print axioms FiniteEqCertificate.quotientInjectiveB_eq_true
#print axioms FiniteEqCertificate.checkCardinalityDef_sound
#print axioms FiniteEqCertificate.checkCardinalityDef_complete
#print axioms FiniteEqCertificate.checkCardinalityDef_eq_true_iff_models
#print axioms FiniteEqCertificate.checkCardinalityDefs_sound
#print axioms FiniteEqCertificate.checkCardinalityDefs_complete
#print axioms FiniteEqCertificate.checkCardinalityDefs_eq_true_iff_models
#print axioms FiniteEqCertificate.checkEqSatWithCardinality_models
#print axioms FiniteEqCertificate.checkEqSatWithCardinality_eq_true_iff
#print axioms FiniteEqCertificate.checkEqSatWithCardinality_not_entailsSub
#print axioms FiniteEqCertificate.checkEqSatWithCardinality_not_unsatisfiableConcept

end ContextCalculus.Hypertableau
