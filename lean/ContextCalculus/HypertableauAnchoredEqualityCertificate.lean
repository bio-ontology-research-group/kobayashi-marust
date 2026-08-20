import ContextCalculus.HypertableauAnchoredCertificate
import ContextCalculus.HypertableauEqualityCertificate

/-! # Dense equality quotients for anchored HT certificates -/

namespace ContextCalculus.Hypertableau
namespace AnchoredForestDomain

structure FiniteAnchoredEqCertificate
    (eqNodeCount regularNodeCount conceptCount roleCount variableCount : Nat) where
  equality : FiniteEqCertificate eqNodeCount conceptCount roleCount variableCount
  regular : FiniteRegularCertificate regularNodeCount conceptCount roleCount variableCount
  classMap : Fin eqNodeCount → Fin regularNodeCount
  nominalRoot : Fin conceptCount → Option (Fin regularNodeCount)

def FiniteAnchoredEqCertificate.ClassQuotient
    (certificate : FiniteAnchoredEqCertificate
      eqNodeCount regularNodeCount conceptCount roleCount variableCount) : Prop :=
  (∀ left right, certificate.equality.state.equiv left right ↔
    certificate.classMap left = certificate.classMap right) ∧
  Function.Surjective certificate.classMap

def FiniteAnchoredEqCertificate.classQuotientB
    (certificate : FiniteAnchoredEqCertificate
      eqNodeCount regularNodeCount conceptCount roleCount variableCount) : Bool :=
  ((List.finRange eqNodeCount).all fun left =>
    (List.finRange eqNodeCount).all fun right =>
      decide ((certificate.equality.representative left =
        certificate.equality.representative right) =
        (certificate.classMap left = certificate.classMap right))) &&
  ((List.finRange regularNodeCount).all fun target =>
    (List.finRange eqNodeCount).any fun source =>
      decide (certificate.classMap source = target))

theorem FiniteAnchoredEqCertificate.classQuotientB_sound
    (certificate : FiniteAnchoredEqCertificate
      eqNodeCount regularNodeCount conceptCount roleCount variableCount)
    (hequality : certificate.equality.equalityClosureValidB = true)
    (hcheck : certificate.classQuotientB = true) :
    certificate.ClassQuotient := by
  simp only [FiniteAnchoredEqCertificate.classQuotientB, Bool.and_eq_true,
    List.all_eq_true, List.any_eq_true, decide_eq_true_eq] at hcheck
  refine ⟨?_, ?_⟩
  · intro left right
    rw [certificate.equality.equalityClosureValidB_sound hequality]
    exact eq_iff_iff.mp
      (hcheck.1 left (List.mem_finRange left) right (List.mem_finRange right))
  · intro target
    rcases hcheck.2 target (List.mem_finRange target) with ⟨source, _, hsource⟩
    exact ⟨source, hsource⟩

def FiniteAnchoredEqCertificate.ExactImage
    (certificate : FiniteAnchoredEqCertificate
      eqNodeCount regularNodeCount conceptCount roleCount variableCount) : Prop :=
  (∀ node lit, certificate.regular.state.label node lit ↔
    ∃ source ∈ List.finRange eqNodeCount, certificate.classMap source = node ∧
      certificate.equality.base.state.label source lit) ∧
  (∀ role source target, certificate.regular.state.edge role source target ↔
    ∃ edgeSource ∈ List.finRange eqNodeCount,
      ∃ edgeTarget ∈ List.finRange eqNodeCount,
      (certificate.classMap edgeSource = source ∧
      certificate.classMap edgeTarget = target) ∧
      certificate.equality.base.state.edge role edgeSource edgeTarget) ∧
  (∀ role filler node, certificate.regular.state.obligation role filler node ↔
    ∃ source ∈ List.finRange eqNodeCount, certificate.classMap source = node ∧
      certificate.equality.base.state.obligation role filler source)

def FiniteAnchoredEqCertificate.exactImageB
    (certificate : FiniteAnchoredEqCertificate
      eqNodeCount regularNodeCount conceptCount roleCount variableCount) : Bool :=
  (List.finRange regularNodeCount).all fun node =>
    ((List.finRange conceptCount).all fun concept =>
      decide (((node, Lit.pos concept) ∈ certificate.regular.labels) =
        ((List.finRange eqNodeCount).any fun source =>
          decide (certificate.classMap source = node) &&
          decide ((source, Lit.pos concept) ∈ certificate.equality.base.labels))) &&
      decide (((node, Lit.negated concept) ∈ certificate.regular.labels) =
        ((List.finRange eqNodeCount).any fun source =>
          decide (certificate.classMap source = node) &&
          decide ((source, Lit.negated concept) ∈ certificate.equality.base.labels)))) &&
    ((List.finRange roleCount).all fun role =>
      (List.finRange regularNodeCount).all fun target =>
        decide (((role, node, target) ∈ certificate.regular.edges) =
          ((List.finRange eqNodeCount).any fun edgeSource =>
            (List.finRange eqNodeCount).any fun edgeTarget =>
              decide (certificate.classMap edgeSource = node) &&
              decide (certificate.classMap edgeTarget = target) &&
              decide ((role, edgeSource, edgeTarget) ∈ certificate.equality.base.edges)))) &&
    ((List.finRange roleCount).all fun role =>
      (List.finRange conceptCount).all fun concept =>
        decide (((role, Lit.pos concept, node) ∈ certificate.regular.obligations) =
          ((List.finRange eqNodeCount).any fun source =>
            decide (certificate.classMap source = node) &&
            decide ((role, Lit.pos concept, source) ∈ certificate.equality.base.obligations))) &&
        decide (((role, Lit.negated concept, node) ∈ certificate.regular.obligations) =
          ((List.finRange eqNodeCount).any fun source =>
            decide (certificate.classMap source = node) &&
            decide ((role, Lit.negated concept, source) ∈ certificate.equality.base.obligations))))

theorem FiniteAnchoredEqCertificate.exactImageB_sound
    (certificate : FiniteAnchoredEqCertificate
      eqNodeCount regularNodeCount conceptCount roleCount variableCount)
    (hcheck : certificate.exactImageB = true) : certificate.ExactImage := by
  simp only [FiniteAnchoredEqCertificate.exactImageB, List.all_eq_true,
    List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  refine ⟨?_, ?_, ?_⟩
  · intro node lit
    have hnode := hcheck node (List.mem_finRange node)
    rcases lit with ⟨concept, neg⟩
    cases neg with
    | false =>
        change ((node, Lit.pos concept) ∈ certificate.regular.labels) ↔ _
        exact eq_iff_iff.mp (hnode.1.1 concept (List.mem_finRange concept)).1
    | true =>
        change ((node, Lit.negated concept) ∈ certificate.regular.labels) ↔ _
        exact eq_iff_iff.mp (hnode.1.1 concept (List.mem_finRange concept)).2
  · intro role source target
    have hnode := hcheck source (List.mem_finRange source)
    change ((role, source, target) ∈ certificate.regular.edges) ↔ _
    exact eq_iff_iff.mp
      (hnode.1.2 role (List.mem_finRange role) target (List.mem_finRange target))
  · intro role filler node
    have hnode := hcheck node (List.mem_finRange node)
    rcases filler with ⟨concept, neg⟩
    cases neg with
    | false =>
        change ((role, Lit.pos concept, node) ∈ certificate.regular.obligations) ↔ _
        exact eq_iff_iff.mp
          (hnode.2 role (List.mem_finRange role) concept
            (List.mem_finRange concept)).1
    | true =>
        change ((role, Lit.negated concept, node) ∈ certificate.regular.obligations) ↔ _
        exact eq_iff_iff.mp
          (hnode.2 role (List.mem_finRange role) concept
            (List.mem_finRange concept)).2

def FiniteAnchoredEqCertificate.check
    (certificate : FiniteAnchoredEqCertificate
      eqNodeCount regularNodeCount conceptCount roleCount variableCount) : Bool :=
  certificate.equality.equalityClosureValidB &&
  decide (certificate.regular.ontology = certificate.equality.base.ontology) &&
  certificate.classQuotientB && certificate.exactImageB &&
  anchoredCheck certificate.regular certificate.nominalRoot

theorem FiniteAnchoredEqCertificate.check_sound
    (certificate : FiniteAnchoredEqCertificate
      eqNodeCount regularNodeCount conceptCount roleCount variableCount)
    (hcheck : certificate.check = true) :
    certificate.regular.ontology = certificate.equality.base.ontology ∧
    certificate.ClassQuotient ∧ certificate.ExactImage ∧
    anchoredCheck certificate.regular certificate.nominalRoot = true := by
  simp only [FiniteAnchoredEqCertificate.check, Bool.and_eq_true,
    decide_eq_true_eq] at hcheck
  rcases hcheck with ⟨⟨⟨⟨hequality, hontology⟩, hquotient⟩, himage⟩, hanchored⟩
  exact ⟨hontology, certificate.classQuotientB_sound hequality hquotient,
    certificate.exactImageB_sound himage, hanchored⟩

theorem FiniteAnchoredEqCertificate.check_models
    [NeZero regularNodeCount]
    (certificate : FiniteAnchoredEqCertificate
      eqNodeCount regularNodeCount conceptCount roleCount variableCount)
    (hcheck : certificate.check = true) :
    (interpretation certificate.regular.state certificate.regular.redirect
      (fun _ _ _ _ => True) (NominalAnchor certificate.nominalRoot)
      certificate.regular.rules certificate.nominalRoot).models
      certificate.equality.base.ontology := by
  have hsound := certificate.check_sound hcheck
  rw [← hsound.1]
  exact anchoredCheck_models certificate.regular certificate.nominalRoot hsound.2.2.2

theorem FiniteAnchoredEqCertificate.check_sat_source_label
    [NeZero regularNodeCount]
    (certificate : FiniteAnchoredEqCertificate
      eqNodeCount regularNodeCount conceptCount roleCount variableCount)
    (hcheck : certificate.check = true) (source : Fin eqNodeCount)
    (lit : Lit (Fin conceptCount))
    (hlabel : certificate.equality.base.state.label source lit) :
    let value := AnchoredForestDomain.root certificate.regular.state
      certificate.regular.redirect (fun _ _ _ _ => True)
      (NominalAnchor certificate.nominalRoot) (certificate.classMap source)
    (interpretation certificate.regular.state certificate.regular.redirect
      (fun _ _ _ _ => True) (NominalAnchor certificate.nominalRoot)
      certificate.regular.rules certificate.nominalRoot).satLit lit value := by
  have hsound := certificate.check_sound hcheck
  have himage := hsound.2.2.1
  have hregularLabel : certificate.regular.state.label
      (certificate.classMap source) lit :=
    (himage.1 (certificate.classMap source) lit).2
      ⟨source, List.mem_finRange source, rfl, hlabel⟩
  have hanchored := hsound.2.2.2
  simp only [anchoredCheck, Bool.and_eq_true] at hanchored
  have hpremises := finitePremisesB_sound
    (regularSatCertificate certificate.regular) certificate.regular.redirect
    certificate.nominalRoot hanchored.2
  rw [regularSatCertificate_state] at hpremises
  exact interpretation_sat_label certificate.regular.state
    certificate.regular.redirect (fun _ _ _ _ => True)
    (NominalAnchor certificate.nominalRoot) certificate.regular.rules
    certificate.nominalRoot hpremises.1 hpremises.2.1
    (AnchoredForestDomain.root certificate.regular.state
      certificate.regular.redirect (fun _ _ _ _ => True)
      (NominalAnchor certificate.nominalRoot) (certificate.classMap source))
    lit hregularLabel

#print axioms FiniteAnchoredEqCertificate.classQuotientB_sound
#print axioms FiniteAnchoredEqCertificate.exactImageB_sound
#print axioms FiniteAnchoredEqCertificate.check_models
#print axioms FiniteAnchoredEqCertificate.check_sat_source_label

end AnchoredForestDomain
end ContextCalculus.Hypertableau
