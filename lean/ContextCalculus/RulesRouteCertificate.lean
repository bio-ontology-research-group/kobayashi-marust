import ContextCalculus.RulesRouteModel
import ContextCalculus.RulesRouteRefutation
import ContextCalculus.HypertableauWire

/-!
# Rule-route answer certificates

One certificate covers one published answer of the rule worker: the
consistency verdict (`KM_RULES_CONSISTENCY`) or a taxonomy over `queries`
(`KM_RULES_CLASSIFY`). It carries the worker clause list, the guard concept
`O` and the nominals, the published answer, closed-tableau proofs for the
entailments, finite models for the non-entailments, and premises: entailments
the worker took as given (`KM_RULES_CLASSIFY_KNOWN`, the CB taxonomy of the
rule-free part).

`Certificate.check_sound`: if the checker accepts and every premise is
entailed, the published answer is exact for the decoded DL-safe knowledge
base: the consistency flag, unsatisfiability of each query, and subsumption
between every two distinct queries whose subsumee is satisfiable.
-/

namespace ContextCalculus.RulesRoute

open ContextCalculus.Hypertableau

inductive Claim where
  | inconsistent
  | unsat (concept : Nat)
  | sub (sub sup : Nat)
deriving DecidableEq, Repr

def Claim.root : Claim → List RLit
  | .inconsistent => []
  | .unsat c => [⟨c, false⟩]
  | .sub a b => [⟨a, false⟩, ⟨b, true⟩]

structure RefutationCert where
  claim : Claim
  proof : Proof

structure ModelCert where
  model : FModel
  /-- `(concept, node)`: the node carries the concept. -/
  witnesses : List (Nat × Nat)

structure Certificate where
  oguard : Nat
  nominals : List Nat
  ontology : List RClause
  queries : List Nat
  consistent : Bool
  unsatisfiable : List Nat
  subsumptions : List (Nat × Nat)
  premiseSubsumptions : List (Nat × Nat)
  premiseUnsatisfiable : List Nat
  refutations : List RefutationCert
  models : List ModelCert

namespace Certificate

variable (C : Certificate)

def kb : KB := decode C.oguard C.nominals C.ontology

def refOK (r : RefutationCert) : Bool :=
  checkProof C.ontology C.nominals (initState r.claim.root C.nominals) r.proof

def proved : List Claim := (C.refutations.filter C.refOK).map (·.claim)

def okModels : List ModelCert := C.models.filter (fun m => m.model.check C.nominals C.ontology)

/-- Label lists of checked model elements that carry `a`. -/
def witnessLabels (a : Nat) : List (List Nat) :=
  C.okModels.flatMap fun m =>
    m.witnesses.filterMap fun w =>
      if w.1 = a ∧ w.2 < m.model.n ∧ m.model.lab w.2 a = true then
        some (m.model.labels.getD w.2 [])
      else none

def inconsistentProved : Bool := C.proved.contains .inconsistent

def unsatOK (a : Nat) : Bool :=
  a != C.oguard &&
    (C.inconsistentProved || C.premiseUnsatisfiable.contains a || C.proved.contains (.unsat a))

def subOK (p : Nat × Nat) : Bool :=
  p.1 != C.oguard && p.2 != C.oguard &&
    (C.inconsistentProved || C.premiseSubsumptions.contains p ||
      C.proved.contains (.unsat p.1) || C.proved.contains (.sub p.1 p.2))

def check : Bool :=
  encodingOK C.oguard C.nominals C.ontology &&
  (if C.consistent then !C.okModels.isEmpty
   else C.inconsistentProved && C.queries.all C.unsatisfiable.contains) &&
  C.unsatisfiable.all C.unsatOK &&
  C.subsumptions.all C.subOK &&
  C.queries.all (fun a => C.unsatisfiable.contains a || !(C.witnessLabels a).isEmpty) &&
  C.queries.all (fun a => C.unsatisfiable.contains a ||
    C.queries.all (fun b => b == a || C.subsumptions.contains (a, b) ||
      (C.witnessLabels a).any (fun L => !L.contains b)))

/-- The published answer is exact for the DL-safe knowledge base. -/
def Exact : Prop :=
  (C.consistent = true ↔ Consistent C.kb) ∧
  (∀ a ∈ C.queries, a ∈ C.unsatisfiable ↔ UnsatConcept C.kb a) ∧
  (∀ a ∈ C.queries, ∀ b ∈ C.queries, a ∉ C.unsatisfiable → a ≠ b →
    ((a, b) ∈ C.subsumptions ↔ EntailsSub C.kb a b))

/-! ## Soundness -/

theorem proved_sound {cl : Claim}
    (h : C.proved.contains cl = true) :
    ∃ p, checkProof C.ontology C.nominals (initState cl.root C.nominals) p = true := by
  have hmem := List.contains_iff_mem.mp h
  simp only [proved, List.mem_map, List.mem_filter] at hmem
  obtain ⟨r, ⟨_, hok⟩, rfl⟩ := hmem
  exact ⟨r.proof, hok⟩

theorem not_consistent_of_proved (henc : encodingOK C.oguard C.nominals C.ontology = true)
    (h : C.inconsistentProved = true) : ¬Consistent C.kb := by
  obtain ⟨p, hp⟩ := C.proved_sound h
  exact refutation_inconsistent henc hp

theorem unsat_of_not_consistent (h : ¬Consistent C.kb) (a : Nat) : UnsatConcept C.kb a :=
  fun D I hm d _ => h ⟨D, ⟨d⟩, I, hm⟩

theorem sub_of_not_consistent (h : ¬Consistent C.kb) (a b : Nat) : EntailsSub C.kb a b :=
  fun D I hm d _ => absurd ⟨D, ⟨d⟩, I, hm⟩ h

theorem consistent_of_okModels (henc : encodingOK C.oguard C.nominals C.ontology = true)
    (h : C.okModels.isEmpty = false) : Consistent C.kb := by
  obtain ⟨m, hm⟩ := List.exists_mem_of_ne_nil _ (by simpa using h)
  simp only [okModels, List.mem_filter] at hm
  obtain ⟨hn, hcm⟩ := m.model.check_sound hm.2
  haveI : Nonempty (Fin m.model.n) := ⟨⟨0, hn⟩⟩
  exact consistent_of_clauseModel henc m.model.interp hcm

theorem witnessLabels_sound {a : Nat} {L : List Nat} (h : L ∈ C.witnessLabels a) :
    ∃ (m : FModel) (d : Fin m.n), ClauseModel m.interp C.nominals C.ontology ∧
      m.interp.concept a d ∧ ∀ b, L.contains b = false → ¬m.interp.concept b d := by
  simp only [witnessLabels, List.mem_flatMap, List.mem_filterMap] at h
  obtain ⟨mc, hmc, w, _, hw⟩ := h
  split at hw
  · rename_i hcond
    simp only [Option.some.injEq] at hw
    subst hw
    obtain ⟨_, hn, hlab⟩ := hcond
    simp only [okModels, List.mem_filter] at hmc
    obtain ⟨_, hcm⟩ := mc.model.check_sound hmc.2
    refine ⟨mc.model, ⟨w.2, hn⟩, hcm, hlab, ?_⟩
    intro b hb hc
    simp only [FModel.interp, FModel.lab] at hc
    simp_all
  · exact absurd hw (by simp)

theorem check_sound (h : C.check = true)
    (hpremSub : ∀ p ∈ C.premiseSubsumptions, EntailsSub C.kb p.1 p.2)
    (hpremUnsat : ∀ a ∈ C.premiseUnsatisfiable, UnsatConcept C.kb a) : C.Exact := by
  simp only [check, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨henc, hcons⟩, hunsat⟩, hsubs⟩, hsat⟩, hnonsub⟩ := h
  have hunsat_sound : ∀ a ∈ C.unsatisfiable, UnsatConcept C.kb a := by
    intro a ha
    have hok := hunsat a ha
    simp only [unsatOK, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true] at hok
    obtain ⟨hne, (hinc | hprem) | hp⟩ := hok
    · exact C.unsat_of_not_consistent (C.not_consistent_of_proved henc hinc) a
    · exact hpremUnsat a (List.contains_iff_mem.mp hprem)
    · obtain ⟨p, hp⟩ := C.proved_sound hp
      exact refutation_unsat henc hne hp
  have hsub_sound : ∀ p ∈ C.subsumptions, EntailsSub C.kb p.1 p.2 := by
    intro p hpmem
    have hok := hsubs p hpmem
    simp only [subOK, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true] at hok
    obtain ⟨⟨hne1, hne2⟩, ((hinc | hprem) | hu) | hs⟩ := hok
    · exact C.sub_of_not_consistent (C.not_consistent_of_proved henc hinc) _ _
    · exact hpremSub p (List.contains_iff_mem.mp hprem)
    · obtain ⟨q, hq⟩ := C.proved_sound hu
      have := refutation_unsat henc hne1 hq
      exact fun D I hm d hd => absurd hd (this D I hm d)
    · obtain ⟨q, hq⟩ := C.proved_sound hs
      exact refutation_sub henc hne1 hne2 hq
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro htrue
      rw [htrue, if_pos rfl] at hcons
      exact C.consistent_of_okModels henc (by simpa using hcons)
    · intro hc
      by_contra hfalse
      have hf : C.consistent = false := by simpa using hfalse
      rw [hf] at hcons
      simp only [Bool.false_eq_true, if_false, Bool.and_eq_true] at hcons
      exact C.not_consistent_of_proved henc hcons.1 hc
  · intro a ha
    constructor
    · exact hunsat_sound a
    · intro hu
      by_contra hnot
      have hs := hsat a ha
      simp only [Bool.or_eq_true, Bool.not_eq_true'] at hs
      rcases hs with hs | hs
      · exact hnot (List.contains_iff_mem.mp hs)
      · obtain ⟨L, hL⟩ := List.exists_mem_of_ne_nil _ (by simpa using hs)
        obtain ⟨m, d, hcm, hd, _⟩ := C.witnessLabels_sound hL
        exact hu _ m.interp (dlSafeModel_of_clauseModel henc _ hcm) d hd
  · intro a ha b hb hau hab
    constructor
    · exact hsub_sound (a, b)
    · intro hent
      by_contra hnot
      have hn := hnonsub a ha
      simp only [Bool.or_eq_true, List.all_eq_true] at hn
      rcases hn with hn | hn
      · exact hau (List.contains_iff_mem.mp hn)
      · have := hn b hb
        simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, Bool.not_eq_true'] at this
        rcases this with (heq | hcontains) | ⟨L, hL, hlack⟩
        · exact hab heq.symm
        · exact hnot (List.contains_iff_mem.mp hcontains)
        · obtain ⟨m, d, hcm, hd, hnb⟩ := C.witnessLabels_sound hL
          exact hnb b hlack (hent _ m.interp (dlSafeModel_of_clauseModel henc _ hcm) d hd)

end Certificate

/-! ## Wire format -/

open Lean

inductive WireStep where
  | horn (clause : Nat) (assignment : List Nat)
  | witness (node role : Nat) (filler : WireLit)
  | nominal (concept left right : Nat)
deriving FromJson, ToJson, Repr

inductive WireProof where
  | clash (steps : List WireStep) (node concept : Nat)
  | bottom (steps : List WireStep) (clause : Nat) (assignment : List Nat)
  | split (steps : List WireStep) (clause : Nat) (assignment : List Nat)
      (children : List WireProof)
deriving FromJson, ToJson, Repr

inductive WireClaim where
  | inconsistent
  | unsat (concept : Nat)
  | sub (sub sup : Nat)
deriving FromJson, ToJson, Repr

structure WireRefutation where
  claim : WireClaim
  proof : WireProof
deriving FromJson, ToJson, Repr

structure WireModel where
  node_count : Nat
  labels : Array (List Nat)
  succ : Array (List (Nat × Nat))
  pred : Array (List (Nat × Nat))
  witnesses : List (Nat × Nat)
deriving FromJson, ToJson, Repr

structure WireRulesCertificate where
  version : Nat
  oguard : Nat
  nominals : List Nat
  ontology : List WireClause
  queries : List Nat
  consistent : Bool
  unsatisfiable : List Nat
  subsumptions : List (Nat × Nat)
  premise_subsumptions : List (Nat × Nat)
  premise_unsatisfiable : List Nat
  refutations : List WireRefutation
  models : List WireModel
deriving FromJson, ToJson, Repr

def toLit (l : WireLit) : RLit := ⟨l.concept, l.neg⟩

def WireAtom.toAtom : WireAtom → RAtom
  | .concept l v => .concept (toLit l) v
  | .role r s t => .role r s t
  | .exists_ r l v => .exists_ r (toLit l) v
  | .eq l r => .eq l r

def WireClause.toClause (c : WireClause) : RClause :=
  { body := c.body.map WireAtom.toAtom, head := c.head.map WireAtom.toAtom }

def WireStep.toStep : WireStep → Step
  | .horn c a => .horn c a
  | .witness n r l => .witness n r l.concept l.neg
  | .nominal c a b => .nominal c a b

def WireProof.toProof : WireProof → Proof
  | .clash steps n c => .clash (steps.map WireStep.toStep) n c
  | .bottom steps c a => .bottom (steps.map WireStep.toStep) c a
  | .split steps c a children =>
      .split (steps.map WireStep.toStep) c a (children.attach.map fun ⟨p, _⟩ => p.toProof)

def WireClaim.toClaim : WireClaim → Claim
  | .inconsistent => .inconsistent
  | .unsat c => .unsat c
  | .sub a b => .sub a b

def WireModel.toModelCert (m : WireModel) : ModelCert :=
  { model := { n := m.node_count, labels := m.labels, succ := m.succ, pred := m.pred },
    witnesses := m.witnesses }

def WireRulesCertificate.toCertificate (w : WireRulesCertificate) : Certificate where
  oguard := w.oguard
  nominals := w.nominals
  ontology := w.ontology.map WireClause.toClause
  queries := w.queries
  consistent := w.consistent
  unsatisfiable := w.unsatisfiable
  subsumptions := w.subsumptions
  premiseSubsumptions := w.premise_subsumptions
  premiseUnsatisfiable := w.premise_unsatisfiable
  refutations := w.refutations.map fun r => { claim := r.claim.toClaim, proof := r.proof.toProof }
  models := w.models.map WireModel.toModelCert

/-- The executable check of a decoded document; acceptance means
`Certificate.check_sound` applies to `w.toCertificate`. -/
def WireRulesCertificate.check (w : WireRulesCertificate) : Bool :=
  w.version == 1 && w.toCertificate.check

theorem WireRulesCertificate.check_sound (w : WireRulesCertificate) (h : w.check = true)
    (hpremSub : ∀ p ∈ w.premise_subsumptions, EntailsSub w.toCertificate.kb p.1 p.2)
    (hpremUnsat : ∀ a ∈ w.premise_unsatisfiable, UnsatConcept w.toCertificate.kb a) :
    w.toCertificate.Exact := by
  simp only [WireRulesCertificate.check, Bool.and_eq_true] at h
  exact w.toCertificate.check_sound h.2 hpremSub hpremUnsat

#print axioms clauseModel_of_dlSafeModel
#print axioms dlSafeModel_of_clauseModel
#print axioms FModel.check_sound
#print axioms checkProof_sound
#print axioms refutation_inconsistent
#print axioms refutation_unsat
#print axioms refutation_sub
#print axioms Certificate.check_sound
#print axioms WireRulesCertificate.check_sound

end ContextCalculus.RulesRoute
