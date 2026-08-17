import ContextCalculus.ELCompletionCertificate
import Lean

/-!
# JSON wire format for executable ELC certificates

The Rust worker emits this schema. All symbol ids are checked against the
declared finite signature before they can enter the semantic checker. Parsing,
bound validation, proof-trace validation, and closure validation therefore fail
closed.
-/

namespace ContextCalculus.ELCompletion

open Lean

inductive WireClause where
  | nf1 (sub sup : Nat)
  | nf2 (left right sup : Nat)
  | nf3 (sub role filler : Nat)
  | nf4 (role filler sup : Nat)
  | nf5 (sub : Nat)
  | nf6 (sub sup : Nat)
  | nf7 (first second sup : Nat)
  | reflexive (role : Nat)
deriving FromJson, ToJson

inductive WireStep where
  | refl (a : Nat)
  | top (a : Nat)
  | nf1 (a sub sup : Nat)
  | nf2 (a left right sup : Nat)
  | nf5 (a sub : Nat)
  | nf4 (a target filler sup role : Nat)
  | bottom_edge (a target role : Nat)
  | nf3 (a sub filler role : Nat)
  | nf6 (a target sub sup : Nat)
  | nf7 (a middle target first second sup : Nat)
  | reflexive (a role : Nat)
deriving FromJson, ToJson

structure WireSubFact where
  sub : Nat
  sup : Nat
deriving FromJson, ToJson

structure WireEdgeFact where
  source : Nat
  role : Nat
  target : Nat
deriving FromJson, ToJson

structure WireCertificate where
  version : Nat
  symbol_count : Nat
  top : Nat
  bottom : Nat
  ontology : List WireClause
  trace : List WireStep
  active_concepts : List Nat
  rust_subsumptions : List WireSubFact
  rust_edges : List WireEdgeFact
  public_subsumptions : List WireSubFact
deriving FromJson, ToJson

def checkedFin (n value : Nat) : Except String (Fin n) :=
  if h : value < n then .ok ⟨value, h⟩
  else .error s!"symbol id {value} is outside [0,{n})"

def WireClause.decode (n : Nat) : WireClause → Except String (Clause (Fin n) (Fin n))
  | .nf1 sub sup => return .nf1 (← checkedFin n sub) (← checkedFin n sup)
  | .nf2 left right sup =>
      return .nf2 (← checkedFin n left) (← checkedFin n right) (← checkedFin n sup)
  | .nf3 sub role filler =>
      return .nf3 (← checkedFin n sub) (← checkedFin n role) (← checkedFin n filler)
  | .nf4 role filler sup =>
      return .nf4 (← checkedFin n role) (← checkedFin n filler) (← checkedFin n sup)
  | .nf5 sub => return .nf5 (← checkedFin n sub)
  | .nf6 sub sup => return .nf6 (← checkedFin n sub) (← checkedFin n sup)
  | .nf7 first second sup =>
      return .nf7 (← checkedFin n first) (← checkedFin n second) (← checkedFin n sup)
  | .reflexive role => return .reflexive (← checkedFin n role)

def WireStep.decode (n : Nat) : WireStep → Except String (Step (Fin n) (Fin n))
  | .refl a => return .refl (← checkedFin n a)
  | .top a => return .top (← checkedFin n a)
  | .nf1 a sub sup => return .nf1 (← checkedFin n a) (← checkedFin n sub) (← checkedFin n sup)
  | .nf2 a left right sup =>
      return .nf2 (← checkedFin n a) (← checkedFin n left) (← checkedFin n right)
        (← checkedFin n sup)
  | .nf5 a sub => return .nf5 (← checkedFin n a) (← checkedFin n sub)
  | .nf4 a target filler sup role =>
      return .nf4 (← checkedFin n a) (← checkedFin n target) (← checkedFin n filler)
        (← checkedFin n sup) (← checkedFin n role)
  | .bottom_edge a target role =>
      return .bottomEdge (← checkedFin n a) (← checkedFin n target) (← checkedFin n role)
  | .nf3 a sub filler role =>
      return .nf3 (← checkedFin n a) (← checkedFin n sub) (← checkedFin n filler)
        (← checkedFin n role)
  | .nf6 a target sub sup =>
      return .nf6 (← checkedFin n a) (← checkedFin n target) (← checkedFin n sub)
        (← checkedFin n sup)
  | .nf7 a middle target first second sup =>
      return .nf7 (← checkedFin n a) (← checkedFin n middle) (← checkedFin n target)
        (← checkedFin n first) (← checkedFin n second) (← checkedFin n sup)
  | .reflexive a role => return .reflexive (← checkedFin n a) (← checkedFin n role)

structure DecodedCertificate (n : Nat) where
  top : Fin n
  bottom : Fin n
  ontology : Ontology (Fin n) (Fin n)
  trace : List (Step (Fin n) (Fin n))
  active_concepts : List (Fin n)
  rust_facts : List (Fact (Fin n) (Fin n))
  public_subsumptions : List (Fin n × Fin n)

def WireSubFact.decode (n : Nat) (fact : WireSubFact) :
    Except String (Fact (Fin n) (Fin n)) :=
  return .sub (← checkedFin n fact.sub) (← checkedFin n fact.sup)

def WireEdgeFact.decode (n : Nat) (fact : WireEdgeFact) :
    Except String (Fact (Fin n) (Fin n)) :=
  return .edge (← checkedFin n fact.source) (← checkedFin n fact.role)
    (← checkedFin n fact.target)

def WireCertificate.decode (doc : WireCertificate) :
    Except String (DecodedCertificate doc.symbol_count) := do
  if doc.version != 1 then
    throw s!"unsupported ELC certificate version {doc.version}"
  return {
    top := ← checkedFin doc.symbol_count doc.top
    bottom := ← checkedFin doc.symbol_count doc.bottom
    ontology := ← doc.ontology.mapM (WireClause.decode doc.symbol_count)
    trace := ← doc.trace.mapM (WireStep.decode doc.symbol_count)
    active_concepts := ← doc.active_concepts.mapM (checkedFin doc.symbol_count)
    rust_facts :=
      (← doc.rust_subsumptions.mapM (WireSubFact.decode doc.symbol_count)) ++
      (← doc.rust_edges.mapM (WireEdgeFact.decode doc.symbol_count))
    public_subsumptions := ← doc.public_subsumptions.mapM fun fact =>
      return (← checkedFin doc.symbol_count fact.sub, ← checkedFin doc.symbol_count fact.sup)
  }

def Fact.source {Concept Role : Type} : Fact Concept Role → Concept
  | .sub a _ => a
  | .edge a _ _ => a

def DecodedCertificate.checkStateAgreement {n : Nat} (doc : DecodedCertificate n) : Bool :=
  let formal := doc.trace.map (Step.conclusion doc.top doc.bottom)
  doc.rust_facts.all (fun fact =>
    decide (fact ∈ formal ∧ fact.source ∈ doc.active_concepts)) &&
  formal.all (fun fact =>
    if fact.source ∈ doc.active_concepts then decide (fact ∈ doc.rust_facts) else true)

def DecodedCertificate.expectedPublicOutput {n : Nat} (doc : DecodedCertificate n) :=
  doc.rust_facts.filterMap fun
    | .sub sub sup =>
        if sub != doc.top && sub != doc.bottom && sup != sub && sup != doc.top then
          some (sub, sup)
        else none
    | .edge _ _ _ => none

def DecodedCertificate.checkPublicOutput {n : Nat} (doc : DecodedCertificate n) : Bool :=
  doc.public_subsumptions.all (fun fact => decide (fact ∈ doc.expectedPublicOutput)) &&
    doc.expectedPublicOutput.all (fun fact => decide (fact ∈ doc.public_subsumptions))

def DecodedCertificate.check {n : Nat} (doc : DecodedCertificate n) : Bool :=
  checkTrace doc.top doc.bottom doc.ontology doc.trace &&
    checkClosedTrace doc.top doc.bottom doc.ontology doc.trace &&
    doc.checkStateAgreement && doc.checkPublicOutput

theorem DecodedCertificate.rustFact_iff {n : Nat} (doc : DecodedCertificate n)
    (hagree : doc.checkStateAgreement = true) {fact : Fact (Fin n) (Fin n)}
    (hactive : fact.source ∈ doc.active_concepts) :
    fact ∈ doc.rust_facts ↔
      fact ∈ doc.trace.map (Step.conclusion doc.top doc.bottom) := by
  simp only [DecodedCertificate.checkStateAgreement, Bool.and_eq_true,
    List.all_eq_true, decide_eq_true_eq] at hagree
  constructor
  · intro hrust
    exact (hagree.1 fact hrust).1
  · intro hformal
    have h := hagree.2 fact hformal
    simp only [hactive, if_true, decide_eq_true_eq] at h
    exact h

theorem DecodedCertificate.check_exact {n : Nat} (doc : DecodedCertificate n)
    (hcheck : doc.check = true) :
    (∀ a b, EntailsSub (top := doc.top) (bottom := doc.bottom) doc.ontology a b ↔
      (traceMaterialization doc.top doc.bottom doc.trace).sub a doc.bottom ∨
        (traceMaterialization doc.top doc.bottom doc.trace).sub a b) ∧
    (Unsatisfiable (top := doc.top) (bottom := doc.bottom) doc.ontology ↔
      (traceMaterialization doc.top doc.bottom doc.trace).sub doc.top doc.bottom) := by
  simp only [DecodedCertificate.check, Bool.and_eq_true] at hcheck
  exact checkedTrace_exact hcheck.1.1.1 hcheck.1.1.2

theorem DecodedCertificate.active_subsumption_exact {n : Nat}
    (doc : DecodedCertificate n) (hcheck : doc.check = true)
    {a b : Fin n} (hactive : a ∈ doc.active_concepts) :
    EntailsSub (top := doc.top) (bottom := doc.bottom) doc.ontology a b ↔
      Fact.sub a doc.bottom ∈ doc.rust_facts ∨ Fact.sub a b ∈ doc.rust_facts := by
  have exact := doc.check_exact hcheck
  simp only [DecodedCertificate.check, Bool.and_eq_true] at hcheck
  rw [exact.1 a b]
  constructor
  · intro h
    rcases h with hbottom | hsub
    · exact Or.inl ((doc.rustFact_iff hcheck.1.2
        (fact := Fact.sub a doc.bottom) hactive).2 hbottom)
    · exact Or.inr ((doc.rustFact_iff hcheck.1.2
        (fact := Fact.sub a b) hactive).2 hsub)
  · intro h
    rcases h with hbottom | hsub
    · exact Or.inl ((doc.rustFact_iff hcheck.1.2
        (fact := Fact.sub a doc.bottom) hactive).1 hbottom)
    · exact Or.inr ((doc.rustFact_iff hcheck.1.2
        (fact := Fact.sub a b) hactive).1 hsub)

theorem DecodedCertificate.publicSub_iff_expected {n : Nat}
    (doc : DecodedCertificate n) (hcheck : doc.check = true) {a b : Fin n} :
    (a, b) ∈ doc.public_subsumptions ↔ (a, b) ∈ doc.expectedPublicOutput := by
  simp only [DecodedCertificate.check, Bool.and_eq_true,
    DecodedCertificate.checkPublicOutput, List.all_eq_true, decide_eq_true_eq] at hcheck
  exact ⟨hcheck.2.1 (a, b), hcheck.2.2 (a, b)⟩

theorem DecodedCertificate.public_subsumption_sound {n : Nat}
    (doc : DecodedCertificate n) (hcheck : doc.check = true) {a b : Fin n}
    (hpublic : (a, b) ∈ doc.public_subsumptions) :
    EntailsSub (top := doc.top) (bottom := doc.bottom) doc.ontology a b := by
  have hcert := hcheck
  have hexpected := (doc.publicSub_iff_expected hcheck).1 hpublic
  simp only [DecodedCertificate.expectedPublicOutput, List.mem_filterMap] at hexpected
  rcases hexpected with ⟨fact, hfact, hdecoded⟩
  cases fact with
  | edge source role target => simp at hdecoded
  | sub sub sup =>
      simp only at hdecoded
      split at hdecoded
      · simp only [Option.some.injEq, Prod.mk.injEq] at hdecoded
        obtain ⟨hsub, hsup⟩ := hdecoded
        subst sub
        subst sup
        simp only [DecodedCertificate.check, Bool.and_eq_true,
          DecodedCertificate.checkStateAgreement, List.all_eq_true,
          decide_eq_true_eq] at hcheck
        have hactive := (hcheck.1.2.1 (Fact.sub a b) hfact).2
        change a ∈ doc.active_concepts at hactive
        rw [doc.active_subsumption_exact hcert hactive]
        exact Or.inr hfact
      · simp at hdecoded

def WireCertificate.check (doc : WireCertificate) : Except String Bool := do
  return (← doc.decode).check

namespace WireExamples

def empty : WireCertificate where
  version := 1
  symbol_count := 2
  top := 0
  bottom := 1
  ontology := []
  trace := [.refl 0, .top 0, .refl 1, .top 1]
  active_concepts := [0]
  rust_subsumptions := [{ sub := 0, sup := 0 }]
  rust_edges := []
  public_subsumptions := []

example : empty.check = .ok true := by rfl

example : { empty with top := 2 }.check = .error "symbol id 2 is outside [0,2)" := by
  rfl

end WireExamples

end ContextCalculus.ELCompletion
