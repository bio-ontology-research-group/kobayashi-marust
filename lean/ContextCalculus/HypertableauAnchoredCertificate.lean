import ContextCalculus.HypertableauAnchoredUnravelling
import ContextCalculus.HypertableauCertificate

/-!
# Executable finite premises for anchored HT models

This checker layer derives the finite semantic premises of the anchored
canonical-model theorem from bounded certificate vectors. The later wire layer
only decodes natural-number identifiers into these finite objects.
-/

namespace ContextCalculus.Hypertableau

namespace AnchoredForestDomain

def NominalAnchor
    (nominalRoot : Fin conceptCount → Option (Fin nodeCount))
    (node : Fin nodeCount) : Prop :=
  ∃ name, nominalRoot name = some node

def nominalLabelCoherentB
    (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount)
    (nominalRoot : Fin conceptCount → Option (Fin nodeCount)) : Bool :=
  (List.finRange conceptCount).all fun name =>
    match nominalRoot name with
    | none => true
    | some root =>
        (List.finRange nodeCount).all fun node =>
          decide (((node, Lit.pos name) ∈ certificate.labels) ↔ node = root) &&
          decide ((node, Lit.negated name) ∈ certificate.labels → node ≠ root)

theorem nominalLabelCoherentB_sound
    (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount)
    (nominalRoot : Fin conceptCount → Option (Fin nodeCount))
    (hcheck : nominalLabelCoherentB certificate nominalRoot = true) :
    NominalLabelCoherent certificate.state (NominalAnchor nominalRoot) nominalRoot := by
  simp only [nominalLabelCoherentB, List.all_eq_true] at hcheck
  intro name root hroot
  have hname := hcheck name (List.mem_finRange name)
  rw [hroot] at hname
  simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hname
  refine ⟨⟨name, hroot⟩, ?_, ?_⟩
  · intro node
    exact (hname node (List.mem_finRange node)).1
  · intro node hnegative
    exact (hname node (List.mem_finRange node)).2 hnegative

def clashFreeB
    (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount) : Bool :=
  certificate.labels.all fun entry =>
    decide ((entry.1, entry.2.complement) ∉ certificate.labels)

theorem clashFreeB_sound
    (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount)
    (hcheck : clashFreeB certificate = true) : certificate.state.ClashFree := by
  simp only [clashFreeB, List.all_eq_true, decide_eq_true_eq] at hcheck
  intro node concept hboth
  have hnot := hcheck (node, Lit.pos concept) hboth.1
  simp only [Lit.complement, Lit.pos, Bool.not_false] at hnot
  exact hnot hboth.2

def redirectWitnessCompleteB
    (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount)
    (redirect : Fin nodeCount → Fin nodeCount) : Bool :=
  certificate.obligations.all fun obligation =>
    (List.finRange nodeCount).any fun target =>
      decide ((obligation.1, redirect obligation.2.2, target) ∈ certificate.edges) &&
      decide ((target, obligation.2.1) ∈ certificate.labels)

theorem redirectWitnessCompleteB_sound
    (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount)
    (redirect : Fin nodeCount → Fin nodeCount)
    (hcheck : redirectWitnessCompleteB certificate redirect = true) :
    RedirectWitnessComplete certificate.state redirect := by
  simp only [redirectWitnessCompleteB, List.all_eq_true] at hcheck
  intro node role filler hobligation
  have hentry : (role, filler, node) ∈ certificate.obligations := hobligation
  have h := hcheck (role, filler, node) hentry
  simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨target, _, hedge, hlabel⟩
  exact ⟨target, hedge, hlabel⟩

def finitePremisesB
    (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount)
    (redirect : Fin nodeCount → Fin nodeCount)
    (nominalRoot : Fin conceptCount → Option (Fin nodeCount)) : Bool :=
  clashFreeB certificate &&
    nominalLabelCoherentB certificate nominalRoot &&
    redirectWitnessCompleteB certificate redirect

theorem finitePremisesB_sound
    (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount)
    (redirect : Fin nodeCount → Fin nodeCount)
    (nominalRoot : Fin conceptCount → Option (Fin nodeCount))
    (hcheck : finitePremisesB certificate redirect nominalRoot = true) :
    certificate.state.ClashFree ∧
      NominalLabelCoherent certificate.state (NominalAnchor nominalRoot) nominalRoot ∧
      RedirectWitnessComplete certificate.state redirect := by
  simp only [finitePremisesB, Bool.and_eq_true] at hcheck
  exact ⟨clashFreeB_sound certificate hcheck.1.1,
    nominalLabelCoherentB_sound certificate nominalRoot hcheck.1.2,
    redirectWitnessCompleteB_sound certificate redirect hcheck.2⟩

#print axioms nominalLabelCoherentB_sound
#print axioms clashFreeB_sound
#print axioms redirectWitnessCompleteB_sound
#print axioms finitePremisesB_sound

end AnchoredForestDomain

end ContextCalculus.Hypertableau
