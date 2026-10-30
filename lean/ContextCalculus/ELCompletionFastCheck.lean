import ContextCalculus.ELCompletionWire
import Std.Data.HashSet.Lemmas
import Std.Data.HashMap.Lemmas

/-!
# Hash-indexed executable ELC certificate check

`DecodedCertificate.checkV5` states every membership test as a `List`
membership, so its running time is quadratic (and the NF7 closure test cubic)
in the size of the certificate. This module defines `checkV5Fast`, which runs
the same tests against hash sets and hash-indexed clause tables, and proves
`checkV5Fast = true → checkV5 = true`. Every theorem about an accepted
`checkV5` certificate therefore holds for an accepted `checkV5Fast`
certificate; acceptance proves exactly what it proved before.
-/

namespace ContextCalculus.ELCompletion

open Std

deriving instance Hashable for Fact
deriving instance Hashable for Clause
deriving instance Hashable for Step
deriving instance Hashable for RawTerm
deriving instance Hashable for RawResidualAtom
deriving instance Hashable for RawResidualClause

/-! ## Hash-set membership agrees with list membership -/

section Membership

instance instHashableSum {α β : Type} [Hashable α] [Hashable β] : Hashable (Sum α β) where
  hash
    | .inl a => mixHash 11 (hash a)
    | .inr b => mixHash 13 (hash b)

theorem hashSet_contains_ofList {α : Type} [BEq α] [LawfulBEq α] [Hashable α]
    (l : List α) (x : α) [inst : Decidable (x ∈ l)] :
    (HashSet.ofList l).contains x = @decide (x ∈ l) inst := by
  rw [HashSet.contains_ofList]
  by_cases h : x ∈ l
  · simp [h]
  · simp [h]

variable {α : Type} [DecidableEq α] [Hashable α]

/-- `listSetEq` with both sides indexed once. -/
def listSetEqFast (left right : List α) : Bool :=
  let leftSet := HashSet.ofList left
  let rightSet := HashSet.ofList right
  left.all (fun value => rightSet.contains value) &&
    right.all (fun value => leftSet.contains value)

theorem listSetEqFast_eq (left right : List α) :
    listSetEqFast left right = listSetEq left right := by
  simp only [listSetEqFast, listSetEq, hashSet_contains_ofList]

end Membership

/-! ## Trace soundness -/

section Trace

variable {Concept Role : Type} [DecidableEq Concept] [DecidableEq Role]
  [Hashable Concept] [Hashable Role]

def validStepFast (_top bottom : Concept) (O : HashSet (Clause Concept Role))
    (available : HashSet (Fact Concept Role)) : Step Concept Role → Bool
  | .refl _ | .top _ => true
  | .nf1 a sub sup =>
      available.contains (.sub a sub) && O.contains (.nf1 sub sup)
  | .nf2 a left right sup =>
      available.contains (.sub a left) && available.contains (.sub a right) &&
        O.contains (.nf2 left right sup)
  | .nf5 a sub => available.contains (.sub a sub) && O.contains (.nf5 sub)
  | .nf4 a target filler sup role =>
      available.contains (.edge a role target) &&
        available.contains (.sub target filler) && O.contains (.nf4 role filler sup)
  | .bottomEdge a target role =>
      available.contains (.edge a role target) && available.contains (.sub target bottom)
  | .nf3 a sub filler role =>
      available.contains (.sub a sub) && O.contains (.nf3 sub role filler)
  | .nf6 a target sub sup =>
      available.contains (.edge a sub target) && O.contains (.nf6 sub sup)
  | .nf7 a middle target first second sup =>
      available.contains (.edge a first middle) &&
        available.contains (.edge middle second target) &&
        O.contains (.nf7 first second sup)
  | .reflexive _ role => O.contains (.reflexive role)

theorem validStepFast_eq (top bottom : Concept) (O : Ontology Concept Role)
    (OS : HashSet (Clause Concept Role))
    (hO : ∀ clause, OS.contains clause = decide (clause ∈ O))
    (available : List (Fact Concept Role)) (S : HashSet (Fact Concept Role))
    (hS : ∀ fact, S.contains fact = decide (fact ∈ available))
    (step : Step Concept Role) :
    validStepFast top bottom OS S step =
      decide (ValidStep top bottom O available step) := by
  cases step <;> simp [validStepFast, ValidStep, hO, hS, Bool.and_assoc]

/-- Process the trace from its end, so that the available facts of a step are
exactly the conclusions of the steps after it. Returns the verdict and the set
of all conclusions. -/
def checkTraceFastAux (top bottom : Concept) (O : HashSet (Clause Concept Role))
    (trace : List (Step Concept Role)) : Bool × HashSet (Fact Concept Role) :=
  trace.foldr (fun step state =>
    (validStepFast top bottom O state.2 step && state.1,
      state.2.insert (step.conclusion top bottom))) (true, ∅)

theorem checkTraceFastAux_spec (top bottom : Concept) (O : Ontology Concept Role)
    (OS : HashSet (Clause Concept Role))
    (hO : ∀ clause, OS.contains clause = decide (clause ∈ O))
    (trace : List (Step Concept Role)) :
    (checkTraceFastAux top bottom OS trace).1 = checkTrace top bottom O trace ∧
      ∀ fact, (checkTraceFastAux top bottom OS trace).2.contains fact =
        decide (fact ∈ trace.map (Step.conclusion top bottom)) := by
  induction trace with
  | nil => simp [checkTraceFastAux, checkTrace]
  | cons step tail ih =>
      obtain ⟨hverdict, hfacts⟩ := ih
      have hunfold : checkTraceFastAux top bottom OS (step :: tail) =
          (validStepFast top bottom OS (checkTraceFastAux top bottom OS tail).2 step &&
              (checkTraceFastAux top bottom OS tail).1,
            (checkTraceFastAux top bottom OS tail).2.insert
              (step.conclusion top bottom)) := by
        simp [checkTraceFastAux, List.foldr_cons]
      rw [hunfold]
      refine ⟨?_, ?_⟩
      · simp only [checkTrace]
        rw [validStepFast_eq top bottom O OS hO _ _ hfacts, hverdict]
      · intro fact
        rw [HashSet.contains_insert, hfacts]
        by_cases h : step.conclusion top bottom = fact
        · simp [h]
        · have h' : ¬fact = step.conclusion top bottom := fun e => h e.symm
          simp [h, h']

/-- `checkTrace` with hash-set premises. -/
def checkTraceFast (top bottom : Concept) (O : Ontology Concept Role)
    (trace : List (Step Concept Role)) : Bool :=
  (checkTraceFastAux top bottom (HashSet.ofList O) trace).1

theorem checkTraceFast_eq (top bottom : Concept) (O : Ontology Concept Role)
    (trace : List (Step Concept Role)) :
    checkTraceFast top bottom O trace = checkTrace top bottom O trace :=
  (checkTraceFastAux_spec top bottom O (HashSet.ofList O)
    (fun clause => hashSet_contains_ofList O clause) trace).1

end Trace

/-! ## Hash-indexed tables -/

section Index

variable {α κ : Type} [BEq κ] [Hashable κ] [LawfulBEq κ]

/-- Group the entries of `l` by `key`; entries without a key are dropped. -/
def indexBy (key : α → Option κ) (l : List α) : HashMap κ (List α) :=
  l.foldl (fun table x => match key x with
    | some k => table.alter k (fun old => some (x :: old.getD []))
    | none => table) ∅

theorem mem_indexBy_aux (key : α → Option κ) (l : List α) :
    ∀ (table : HashMap κ (List α)) (k : κ) (y : α),
      (y ∈ table.getD k [] ∨ (y ∈ l ∧ key y = some k)) →
        y ∈ (l.foldl (fun table x => match key x with
          | some k => table.alter k (fun old => some (x :: old.getD []))
          | none => table) table).getD k [] := by
  induction l with
  | nil =>
      intro table k y h
      rcases h with h | ⟨h, _⟩
      · exact h
      · simp at h
  | cons x xs ih =>
      intro table k y h
      simp only [List.foldl_cons]
      apply ih
      rcases h with h | ⟨hmem, hkey⟩
      · left
        cases hx : key x with
        | none => simpa using h
        | some k' =>
            simp only []
            rw [HashMap.getD_alter]
            by_cases hk : k' = k
            · subst hk
              simp [HashMap.getD_eq_getD_getElem?] at h ⊢
              exact Or.inr h
            · simp [hk, h]
      · rcases List.mem_cons.mp hmem with rfl | hxs
        · left
          rw [hkey]
          simp [HashMap.getD_alter_self]
        · right
          exact ⟨hxs, hkey⟩

theorem mem_indexBy (key : α → Option κ) {l : List α} {y : α} {k : κ}
    (hy : y ∈ l) (hkey : key y = some k) : y ∈ (indexBy key l).getD k [] :=
  mem_indexBy_aux key l ∅ k y (Or.inr ⟨hy, hkey⟩)

end Index

/-! ## Fixpoint closure -/

section Closure

variable {n : Nat}

/-- Clauses whose first premise is a subsumption `a ⊑ C`, keyed by `C`. -/
def subPremiseKey : Clause (Fin n) (Fin n) → Option (Fin n)
  | .nf1 sub _ => some sub
  | .nf2 left _ _ => some left
  | .nf3 sub _ _ => some sub
  | .nf5 sub => some sub
  | _ => none

/-- Clauses whose first premise is an edge with role `R`, keyed by `R`. -/
def edgePremiseKey : Clause (Fin n) (Fin n) → Option (Fin n)
  | .nf6 sub _ => some sub
  | .nf7 first _ _ => some first
  | _ => none

/-- NF4 clauses keyed by role and filler. -/
def nf4Key : Clause (Fin n) (Fin n) → Option (Fin n × Fin n)
  | .nf4 role filler _ => some (role, filler)
  | _ => none

/-- Subsumption facts keyed by their subject. -/
def subSourceKey : Fact (Fin n) (Fin n) → Option (Fin n)
  | .sub a _ => some a
  | _ => none

/-- Edge facts keyed by their source. -/
def edgeSourceKey : Fact (Fin n) (Fin n) → Option (Fin n)
  | .edge a _ _ => some a
  | _ => none

def reflexiveRoles (O : Ontology (Fin n) (Fin n)) : List (Fin n) :=
  O.filterMap fun
    | .reflexive role => some role
    | _ => none

/-- Closure obligations triggered by the fact `a ⊑ known`. -/
def subFactClosed (S : HashSet (Fact (Fin n) (Fin n))) (bottom a : Fin n) :
    Clause (Fin n) (Fin n) → Bool
  | .nf1 _ sup => S.contains (.sub a sup)
  | .nf2 _ right sup => !S.contains (.sub a right) || S.contains (.sub a sup)
  | .nf3 _ role filler => S.contains (.edge a role filler)
  | .nf5 _ => S.contains (.sub a bottom)
  | _ => true

/-- Closure obligations triggered by the edge `a -role-> target`. -/
def edgeFactClosed (S : HashSet (Fact (Fin n) (Fin n)))
    (outgoing : HashMap (Fin n) (List (Fact (Fin n) (Fin n))))
    (a target : Fin n) : Clause (Fin n) (Fin n) → Bool
  | .nf6 _ sup => S.contains (.edge a sup target)
  | .nf7 _ second sup => (outgoing.getD target []).all fun
      | .edge _ role last => !(role == second) || S.contains (.edge a sup last)
      | _ => true
  | _ => true

/-- NF4 obligations of the edge `a -role-> target`, one lookup per known
superconcept of `target`. -/
def nf4Closed (S : HashSet (Fact (Fin n) (Fin n)))
    (byNf4 : HashMap (Fin n × Fin n) (List (Clause (Fin n) (Fin n))))
    (subsOf : HashMap (Fin n) (List (Fact (Fin n) (Fin n))))
    (a role target : Fin n) : Bool :=
  (subsOf.getD target []).all fun
    | .sub _ filler => (byNf4.getD (role, filler) []).all fun
        | .nf4 _ _ sup => S.contains (.sub a sup)
        | _ => true
    | _ => true

def factClosed (S : HashSet (Fact (Fin n) (Fin n)))
    (bySub byEdge : HashMap (Fin n) (List (Clause (Fin n) (Fin n))))
    (byNf4 : HashMap (Fin n × Fin n) (List (Clause (Fin n) (Fin n))))
    (subsOf outgoing : HashMap (Fin n) (List (Fact (Fin n) (Fin n))))
    (bottom : Fin n) : Fact (Fin n) (Fin n) → Bool
  | .sub a known => (bySub.getD known []).all (subFactClosed S bottom a)
  | .edge a role target =>
      (!S.contains (.sub target bottom) || S.contains (.sub a bottom)) &&
        (byEdge.getD role []).all (edgeFactClosed S outgoing a target) &&
        nf4Closed S byNf4 subsOf a role target

/-- `checkClosedTrace` with hash-set lookups and premise-indexed clauses. -/
def checkClosedTraceFast (top bottom : Fin n) (O : Ontology (Fin n) (Fin n))
    (trace : List (Step (Fin n) (Fin n))) : Bool :=
  let facts := trace.map (Step.conclusion top bottom)
  let S := HashSet.ofList facts
  let bySub := indexBy subPremiseKey O
  let byEdge := indexBy edgePremiseKey O
  let byNf4 := indexBy nf4Key O
  let subsOf := indexBy subSourceKey facts
  let outgoing := indexBy edgeSourceKey facts
  let reflexive := reflexiveRoles O
  (List.finRange n).all (fun a =>
      S.contains (.sub a a) && S.contains (.sub a top) &&
        reflexive.all fun role => S.contains (.edge a role a)) &&
    facts.all (factClosed S bySub byEdge byNf4 subsOf outgoing bottom)

theorem checkClosedTraceFast_closed {top bottom : Fin n}
    {O : Ontology (Fin n) (Fin n)} {trace : List (Step (Fin n) (Fin n))}
    (hcheck : checkClosedTraceFast top bottom O trace = true) :
    ClosedState (traceMaterialization top bottom trace) top bottom O := by
  simp only [checkClosedTraceFast, Bool.and_eq_true, List.all_eq_true] at hcheck
  obtain ⟨hall, hfacts⟩ := hcheck
  have hS : ∀ fact, (HashSet.ofList (trace.map (Step.conclusion top bottom))).contains fact =
      true ↔ fact ∈ trace.map (Step.conclusion top bottom) := by
    intro fact
    rw [hashSet_contains_ofList]
    simp
  have hpoint := fun a => hall a (List.mem_finRange a)
  have hsubFact := fun a known (h : Fact.sub a known ∈ trace.map (Step.conclusion top bottom)) =>
    hfacts _ h
  have hedgeFact := fun a role target
      (h : Fact.edge a role target ∈ trace.map (Step.conclusion top bottom)) =>
    hfacts _ h
  refine {
    initRefl := fun a => (hS _).mp (hpoint a).1.1
    initTop := fun a => (hS _).mp (hpoint a).1.2
    closeNf1 := ?_, closeNf2 := ?_, closeNf5 := ?_, closeNf4 := ?_
    closeBottomEdge := ?_, closeNf3 := ?_, closeNf6 := ?_, closeNf7 := ?_
    closeReflexive := ?_ }
  · intro a sub sup hsub hcl
    have h := hsubFact a sub hsub
    simp only [factClosed, List.all_eq_true] at h
    have := h _ (mem_indexBy subPremiseKey hcl rfl)
    exact (hS _).mp (by simpa only [subFactClosed] using this)
  · intro a left right sup hleft hright hcl
    have h := hsubFact a left hleft
    simp only [factClosed, List.all_eq_true] at h
    have := h _ (mem_indexBy subPremiseKey hcl rfl)
    simp only [subFactClosed, Bool.or_eq_true, Bool.not_eq_true'] at this
    rcases this with hnot | hsup
    · have : (HashSet.ofList (trace.map (Step.conclusion top bottom))).contains
          (Fact.sub a right) = true := (hS _).mpr hright
      rw [this] at hnot
      contradiction
    · exact (hS _).mp hsup
  · intro a sub hsub hcl
    have h := hsubFact a sub hsub
    simp only [factClosed, List.all_eq_true] at h
    have := h _ (mem_indexBy subPremiseKey hcl rfl)
    exact (hS _).mp (by simpa only [subFactClosed] using this)
  · intro a target filler sup role hedge hfiller hcl
    have h := hedgeFact a role target hedge
    simp only [factClosed, Bool.and_eq_true] at h
    have h4 := h.2
    simp only [nf4Closed, List.all_eq_true] at h4
    have hsubs := h4 _ (mem_indexBy subSourceKey hfiller rfl)
    simp only [List.all_eq_true] at hsubs
    have := hsubs _ (mem_indexBy nf4Key hcl rfl)
    exact (hS _).mp this
  · intro a target role hedge hbottom
    have h := hedgeFact a role target hedge
    simp only [factClosed, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
    rcases h.1.1 with hnot | hsup
    · have : (HashSet.ofList (trace.map (Step.conclusion top bottom))).contains
          (Fact.sub target bottom) = true := (hS _).mpr hbottom
      rw [this] at hnot
      contradiction
    · exact (hS _).mp hsup
  · intro a sub filler role hsub hcl
    have h := hsubFact a sub hsub
    simp only [factClosed, List.all_eq_true] at h
    have := h _ (mem_indexBy subPremiseKey hcl rfl)
    exact (hS _).mp (by simpa only [subFactClosed] using this)
  · intro a target sub sup hedge hcl
    have h := hedgeFact a sub target hedge
    simp only [factClosed, Bool.and_eq_true, List.all_eq_true] at h
    have := h.1.2 _ (mem_indexBy edgePremiseKey hcl rfl)
    exact (hS _).mp (by simpa only [edgeFactClosed] using this)
  · intro a middle target first second sup hfirst hsecond hcl
    have h := hedgeFact a first middle hfirst
    simp only [factClosed, Bool.and_eq_true, List.all_eq_true] at h
    have := h.1.2 _ (mem_indexBy edgePremiseKey hcl rfl)
    simp only [edgeFactClosed, List.all_eq_true] at this
    have hout := this _ (mem_indexBy edgeSourceKey hsecond rfl)
    simp only [Bool.or_eq_true, Bool.not_eq_true', beq_self_eq_true] at hout
    rcases hout with hnot | hsup
    · simp at hnot
    · exact (hS _).mp hsup
  · intro a role hcl
    have h := (hpoint a).2
    have hrole : role ∈ reflexiveRoles O := by
      simp only [reflexiveRoles, List.mem_filterMap]
      exact ⟨_, hcl, rfl⟩
    exact (hS _).mp (h role hrole)

/-- `checkClosedTrace` is complete for closed materializations, so the fast
check also establishes the original executable closure check. -/
theorem checkClosedTrace_of_closed {top bottom : Fin n}
    {O : Ontology (Fin n) (Fin n)} {trace : List (Step (Fin n) (Fin n))}
    (closed : ClosedState (traceMaterialization top bottom trace) top bottom O) :
    checkClosedTrace top bottom O trace = true := by
  simp only [checkClosedTrace, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨closed.initRefl, closed.initTop⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩,
    ?_⟩, ?_⟩, ?_⟩
  · intro a clause _
    cases clause <;> simp only [checkNf1Rule, decide_eq_true_eq]
    intro h; exact closed.closeNf1 h ‹_›
  · intro a clause hcl
    cases clause <;> simp only [checkNf2Rule, decide_eq_true_eq]
    intro h1 h2; exact closed.closeNf2 h1 h2 hcl
  · intro a clause hcl
    cases clause <;> simp only [checkNf5Rule, decide_eq_true_eq]
    intro h; exact closed.closeNf5 h hcl
  · intro fact hfact clause hcl
    cases fact <;> cases clause <;> simp only [checkNf4Rule, decide_eq_true_eq]
    intro hrole hfiller; subst hrole; exact closed.closeNf4 hfact hfiller hcl
  · intro fact hfact
    cases fact <;> simp only [checkBottomEdgeRule, decide_eq_true_eq]
    intro hbottom; exact closed.closeBottomEdge hfact hbottom
  · intro a clause hcl
    cases clause <;> simp only [checkNf3Rule, decide_eq_true_eq]
    intro h; exact closed.closeNf3 h hcl
  · intro fact hfact clause hcl
    cases fact <;> cases clause <;> simp only [checkNf6Rule, decide_eq_true_eq]
    intro hrole; subst hrole; exact closed.closeNf6 hfact hcl
  · intro first hfirst second hsecond clause hcl
    cases first <;> cases second <;> cases clause <;>
      simp only [checkNf7Rule, decide_eq_true_eq]
    intro h1 h2 h3; subst h1; subst h2; subst h3
    exact closed.closeNf7 hfirst hsecond hcl
  · intro a clause hcl
    cases clause <;> simp only [checkReflexiveRule, decide_eq_true_eq]
    exact closed.closeReflexive a hcl

theorem checkClosedTraceFast_sound {top bottom : Fin n}
    {O : Ontology (Fin n) (Fin n)} {trace : List (Step (Fin n) (Fin n))}
    (hcheck : checkClosedTraceFast top bottom O trace = true) :
    checkClosedTrace top bottom O trace = true :=
  checkClosedTrace_of_closed (checkClosedTraceFast_closed hcheck)

end Closure

/-! ## The decoded certificate -/

section Decoded

variable {n : Nat}

theorem decide_mem_eq_contains {α : Type} [DecidableEq α] [Hashable α]
    (l : List α) (x : α) : decide (x ∈ l) = (HashSet.ofList l).contains x :=
  (hashSet_contains_ofList l x).symm

def DecodedCertificate.facts (doc : DecodedCertificate n) :=
  doc.trace.map (Step.conclusion doc.top doc.bottom)

def DecodedCertificate.checkFactAgreementFast (doc : DecodedCertificate n) : Bool :=
  let formal := HashSet.ofList doc.facts
  let active := HashSet.ofList doc.active_concepts
  let rust := HashSet.ofList doc.rust_facts
  doc.rust_facts.all (fun fact => formal.contains fact && active.contains fact.source) &&
    doc.facts.all (fun fact => !active.contains fact.source || rust.contains fact)

theorem DecodedCertificate.checkFactAgreementFast_eq (doc : DecodedCertificate n) :
    doc.checkFactAgreementFast = doc.checkFactAgreement := by
  simp only [DecodedCertificate.checkFactAgreementFast, DecodedCertificate.checkFactAgreement,
    DecodedCertificate.facts, hashSet_contains_ofList]
  congr 1
  · simp [Bool.decide_and]
  · congr 1
    funext fact
    by_cases h : fact.source ∈ doc.active_concepts <;> simp [h]

def DecodedCertificate.checkActiveConceptsFast (doc : DecodedCertificate n) : Bool :=
  let expected := doc.expectedActiveConcepts
  let expectedSet := HashSet.ofList expected
  let active := HashSet.ofList doc.active_concepts
  doc.active_concepts.all (fun id => expectedSet.contains id) &&
    expected.all (fun id => active.contains id)

theorem DecodedCertificate.checkActiveConceptsFast_eq (doc : DecodedCertificate n) :
    doc.checkActiveConceptsFast = doc.checkActiveConcepts := by
  simp only [DecodedCertificate.checkActiveConceptsFast,
    DecodedCertificate.checkActiveConcepts, hashSet_contains_ofList]

def DecodedCertificate.checkPublicOutputFast (doc : DecodedCertificate n) : Bool :=
  let expected := doc.expectedPublicOutput
  let expectedSet := HashSet.ofList expected
  let published := HashSet.ofList doc.public_subsumptions
  doc.public_subsumptions.all (fun fact => expectedSet.contains fact) &&
    expected.all (fun fact => published.contains fact)

theorem DecodedCertificate.checkPublicOutputFast_eq (doc : DecodedCertificate n) :
    doc.checkPublicOutputFast = doc.checkPublicOutput := by
  simp only [DecodedCertificate.checkPublicOutputFast,
    DecodedCertificate.checkPublicOutput, hashSet_contains_ofList]

def DecodedCertificate.checkNamedOutputFast (doc : DecodedCertificate n) : Bool :=
  let expected := doc.expectedNamedOutput
  let expectedSet := HashSet.ofList expected
  let published := HashSet.ofList doc.public_named_subsumptions
  doc.public_named_subsumptions.all (fun fact => expectedSet.contains fact) &&
    expected.all (fun fact => published.contains fact) &&
    decide (doc.public_inconsistent = decide (Fact.sub doc.top doc.bottom ∈ doc.rust_facts))

theorem DecodedCertificate.checkNamedOutputFast_eq (doc : DecodedCertificate n) :
    doc.checkNamedOutputFast = doc.checkNamedOutput := by
  simp only [DecodedCertificate.checkNamedOutputFast,
    DecodedCertificate.checkNamedOutput, hashSet_contains_ofList]

def DecodedCertificate.checkFast (doc : DecodedCertificate n) : Bool :=
  checkTraceFast doc.top doc.bottom doc.ontology doc.trace &&
    checkClosedTraceFast doc.top doc.bottom doc.ontology doc.trace &&
    (doc.checkFactAgreementFast && doc.checkActiveConceptsFast) &&
    doc.checkPublicOutputFast && doc.checkNamedOutputFast

theorem DecodedCertificate.checkFast_sound (doc : DecodedCertificate n)
    (h : doc.checkFast = true) : doc.check = true := by
  simp only [DecodedCertificate.checkFast, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨htrace, hclosed⟩, hfacts, hactive⟩, hpublic⟩, hnamed⟩ := h
  simp only [DecodedCertificate.check, DecodedCertificate.checkStateAgreement,
    Bool.and_eq_true]
  rw [checkTraceFast_eq] at htrace
  rw [DecodedCertificate.checkFactAgreementFast_eq] at hfacts
  rw [DecodedCertificate.checkActiveConceptsFast_eq] at hactive
  rw [DecodedCertificate.checkPublicOutputFast_eq] at hpublic
  rw [DecodedCertificate.checkNamedOutputFast_eq] at hnamed
  exact ⟨⟨⟨⟨htrace, checkClosedTraceFast_sound hclosed⟩, hfacts, hactive⟩, hpublic⟩, hnamed⟩

def DecodedCertificate.checkSignatureClosedFast (doc : DecodedCertificate n) : Bool :=
  let active := HashSet.ofList doc.active_concepts
  active.contains doc.top &&
    doc.ontology.all fun clause =>
      clause.concepts.all fun concept => concept == doc.bottom || active.contains concept

theorem DecodedCertificate.checkSignatureClosedFast_eq (doc : DecodedCertificate n) :
    doc.checkSignatureClosedFast = doc.checkSignatureClosed := by
  simp only [DecodedCertificate.checkSignatureClosedFast,
    DecodedCertificate.checkSignatureClosed, hashSet_contains_ofList]

def DecodedCertificate.checkOriginOntologyFast (doc : DecodedCertificate n) : Bool :=
  listSetEqFast doc.normal_ontology (mapOntologyConcept doc.conceptOrigin doc.ontology)

theorem DecodedCertificate.checkOriginOntologyFast_eq (doc : DecodedCertificate n) :
    doc.checkOriginOntologyFast = doc.checkOriginOntology := by
  simp only [DecodedCertificate.checkOriginOntologyFast,
    DecodedCertificate.checkOriginOntology, listSetEqFast_eq]

def DecodedCertificate.checkSourcePartitionFast (doc : DecodedCertificate n) : Bool :=
  listSetEqFast doc.source_ontology doc.partitionedSourceOntology

theorem DecodedCertificate.checkSourcePartitionFast_eq (doc : DecodedCertificate n) :
    doc.checkSourcePartitionFast = doc.checkSourcePartition := by
  simp only [DecodedCertificate.checkSourcePartitionFast,
    DecodedCertificate.checkSourcePartition, listSetEqFast_eq]

theorem DecodedCertificate.originArray_getElem? (doc : DecodedCertificate n)
    (concept : Fin n) :
    doc.concept_origins.toArray[concept.val]? = some (doc.conceptOrigin concept) := by
  have hlt : concept.val < doc.concept_origins.length := by
    rw [doc.concept_origins_length]; exact concept.isLt
  simp [DecodedCertificate.conceptOrigin, List.getElem?_eq_getElem hlt]

def DecodedCertificate.checkPartitionedNormalizationFast (doc : DecodedCertificate n) :
    Bool :=
  let origins := doc.concept_origins.toArray
  let sourceConcepts := doc.source_ontology.flatMap RawResidualClause.conceptIds
  let witnessConcepts := doc.witness_records.flatMap fun record =>
    [record.sub, record.filler, record.witness]
  let sourceOrigins := (sourceConcepts ++ witnessConcepts).all fun concept =>
    decide (origins[concept.val]? = some (.inl concept))
  match certifyRawDirectToNormal doc.top doc.bottom doc.raw_ontology with
  | none => false
  | some certificate =>
      sourceOrigins && listSetEqFast doc.normal_ontology
        (certificate.normal.normal ++ doc.witnessNormalOntology)

theorem DecodedCertificate.checkPartitionedNormalizationFast_eq
    (doc : DecodedCertificate n) :
    doc.checkPartitionedNormalizationFast = doc.checkPartitionedNormalization := by
  simp only [DecodedCertificate.checkPartitionedNormalizationFast,
    DecodedCertificate.checkPartitionedNormalization, listSetEqFast_eq,
    DecodedCertificate.originArray_getElem?, Option.some.injEq]
  split
  · rename_i h; rw [h]
  · rename_i h; rw [h]

end Decoded

/-! ## Finite residual check -/

section Residual

variable {n : Nat}

def DecodedCertificate.residualValueAliveFast (doc : DecodedCertificate n)
    (active : HashSet (Fin n)) (facts : HashSet (Fact (Fin n) (Fin n)))
    (value : Fin n) : Bool :=
  active.contains value && !facts.contains (.sub value doc.bottom)

theorem DecodedCertificate.residualValueAliveFast_eq (doc : DecodedCertificate n)
    (value : Fin n) :
    doc.residualValueAliveFast (HashSet.ofList doc.active_concepts)
        (HashSet.ofList doc.facts) value = doc.residualValueAlive value := by
  simp only [DecodedCertificate.residualValueAliveFast,
    DecodedCertificate.residualValueAlive, hashSet_contains_ofList]
  simp only [DecodedCertificate.facts, DecodedCertificate.materialization,
    traceMaterialization]
  congr 1
  by_cases h : Fact.sub value doc.bottom ∈ doc.trace.map (Step.conclusion doc.top doc.bottom)
  · simp [h]
  · simp [h]

def DecodedCertificate.checkFunctionBindingsFast (doc : DecodedCertificate n)
    (active : HashSet (Fin n)) (facts : HashSet (Fact (Fin n) (Fin n))) : Bool :=
  let bindings := doc.functionBindings
  let table := indexBy (fun binding : Nat × Fin n => some binding.1) bindings
  bindings.all fun binding =>
    doc.residualValueAliveFast active facts binding.2 &&
      (table.getD binding.1 []).all fun other => decide (other.2 = binding.2)

theorem DecodedCertificate.checkFunctionBindingsFast_sound (doc : DecodedCertificate n)
    (h : doc.checkFunctionBindingsFast (HashSet.ofList doc.active_concepts)
      (HashSet.ofList doc.facts) = true) :
    doc.checkFunctionBindings = true := by
  rw [DecodedCertificate.checkFunctionBindings_iff]
  simp only [DecodedCertificate.checkFunctionBindingsFast, List.all_eq_true,
    Bool.and_eq_true, decide_eq_true_eq] at h
  intro binding hbinding
  obtain ⟨halive, hconsistent⟩ := h binding hbinding
  rw [DecodedCertificate.residualValueAliveFast_eq] at halive
  simp only [DecodedCertificate.residualValueAlive, Bool.and_eq_true,
    decide_eq_true_eq] at halive
  refine ⟨halive, ?_⟩
  intro other hother hkey
  have hmem : other ∈ (indexBy (fun binding : Nat × Fin n => some binding.1)
      doc.functionBindings).getD binding.1 [] :=
    mem_indexBy _ hother (by rw [hkey])
  exact (hconsistent other hmem).symm

def DecodedCertificate.checkWitnessRecordsFast (doc : DecodedCertificate n)
    (active : HashSet (Fin n)) (facts : HashSet (Fact (Fin n) (Fin n)))
    (ontology : HashSet (Clause (Fin n) (Fin n))) : Bool :=
  doc.witness_records.all fun record =>
    doc.residualValueAliveFast active facts record.witness &&
      ontology.contains (.nf3 record.sub record.role record.witness) &&
      ontology.contains (.nf1 record.witness record.filler)

theorem DecodedCertificate.checkWitnessRecordsFast_eq (doc : DecodedCertificate n) :
    doc.checkWitnessRecordsFast (HashSet.ofList doc.active_concepts)
        (HashSet.ofList doc.facts) (HashSet.ofList doc.ontology) =
      doc.checkWitnessRecords := by
  simp only [DecodedCertificate.checkWitnessRecordsFast,
    DecodedCertificate.checkWitnessRecords, DecodedCertificate.residualValueAliveFast_eq,
    hashSet_contains_ofList]

/-- `checkFiniteResiduals` with the fast closure, binding and witness checks.
The residual clauses themselves are evaluated exactly as before. -/
def DecodedCertificate.checkFiniteResidualsFast {n : Nat}
    (doc : DecodedCertificate n) : Bool :=
  letI : ∀ a b, Decidable (doc.materialization.sub a b) := fun _ _ => by
    dsimp [DecodedCertificate.materialization, traceMaterialization]
    infer_instance
  letI : DecidablePred (fun concept : Fin n =>
      concept ∈ doc.active_concepts ∧
        ¬doc.materialization.sub concept doc.bottom) := fun _ => inferInstance
  if hfast : checkClosedTraceFast doc.top doc.bottom doc.ontology doc.trace = true then
    have hclosed := checkClosedTraceFast_sound hfast
    if htopActive : doc.top ∈ doc.active_concepts then
      if htopBottom : doc.materialization.sub doc.top doc.bottom then
        true
      else
        let closed := checkClosedTrace_closed hclosed
        let map := doc.residualDomainValue htopActive htopBottom
        let model := doc.residualModel
        have htop : ∀ value, model.concept doc.top value = true := by
          intro value
          simpa [model, DecodedCertificate.residualModel] using
            closed.initTop value.1
        have hbottom : ∀ value, model.concept doc.bottom value = false := by
          intro value
          simpa [model, DecodedCertificate.residualModel] using value.2.2
        let active := HashSet.ofList doc.active_concepts
        let facts := HashSet.ofList doc.facts
        doc.checkFunctionBindingsFast active facts &&
          doc.checkWitnessRecordsFast active facts (HashSet.ofList doc.ontology) &&
          doc.residual_compilations.all fun residual =>
            doc.residualWitnessesAlive residual.decoded &&
            checkResidualCompilationEvidence
              (residual.decoded.mappedOrigin map) residual.decoded.raw
              (residual.decoded.mappedCompiled map) &&
            checkCompiledResidualClause model doc.top doc.bottom htop hbottom
              (residual.decoded.mappedCompiled map)
    else false
  else false

theorem DecodedCertificate.checkFiniteResidualsFast_sound (doc : DecodedCertificate n)
    (h : doc.checkFiniteResidualsFast = true) : doc.checkFiniteResiduals = true := by
  unfold DecodedCertificate.checkFiniteResidualsFast at h
  split at h
  · rename_i hfast
    have hclosed := checkClosedTraceFast_sound hfast
    unfold DecodedCertificate.checkFiniteResiduals
    rw [dif_pos hclosed]
    split at h
    · rename_i htopActive
      rw [dif_pos htopActive]
      split at h
      · rename_i htopBottom
        rw [dif_pos htopBottom]
      · rename_i htopBottom
        rw [dif_neg htopBottom]
        simp only [Bool.and_eq_true] at h ⊢
        obtain ⟨⟨hbindings, hwitness⟩, hresiduals⟩ := h
        refine ⟨⟨doc.checkFunctionBindingsFast_sound hbindings, ?_⟩, hresiduals⟩
        rw [← doc.checkWitnessRecordsFast_eq]
        exact hwitness
    · contradiction
  · contradiction

end Residual

/-! ## The complete fast check -/

section Complete

variable {n : Nat}

def DecodedCertificate.checkV5Fast (doc : DecodedCertificate n) : Bool :=
  doc.checkCanonicalOrigins && doc.checkOriginOntologyFast &&
    doc.checkSourcePartitionFast && doc.checkPartitionedNormalizationFast &&
    doc.residual_compilations.all (fun residual => residual.check) &&
    doc.checkFiniteResidualsFast && doc.checkSignatureClosedFast && doc.checkFast

theorem DecodedCertificate.checkV5Fast_sound (doc : DecodedCertificate n)
    (h : doc.checkV5Fast = true) : doc.checkV5 = true := by
  simp only [DecodedCertificate.checkV5Fast, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hcanonical, horigin⟩, hpartition⟩, hnormal⟩, hresiduals⟩, hfinite⟩,
    hsignature⟩, hcheck⟩ := h
  rw [DecodedCertificate.checkOriginOntologyFast_eq] at horigin
  rw [DecodedCertificate.checkSourcePartitionFast_eq] at hpartition
  rw [DecodedCertificate.checkPartitionedNormalizationFast_eq] at hnormal
  rw [DecodedCertificate.checkSignatureClosedFast_eq] at hsignature
  simp only [DecodedCertificate.checkV5, DecodedCertificate.checkNormalizationV5,
    Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨hcanonical, horigin⟩, hpartition⟩, hnormal⟩, hresiduals⟩,
    doc.checkFiniteResidualsFast_sound hfinite⟩, hsignature⟩, doc.checkFast_sound hcheck⟩

/-- The executable wire check run by `elc-cert-check`. -/
def WireCertificate.checkFast (doc : WireCertificate) : Except String Bool := do
  return (← doc.decode).checkV5Fast

theorem WireCertificate.checkFast_sound (wire : WireCertificate)
    (h : wire.checkFast = .ok true) : wire.check = .ok true := by
  unfold WireCertificate.checkFast at h
  unfold WireCertificate.check
  cases hdecode : wire.decode with
  | error error => simp [hdecode] at h
  | ok decoded =>
      simp only [hdecode] at h ⊢
      have hfast : decoded.checkV5Fast = true := by simpa using h
      simp [decoded.checkV5Fast_sound hfast]

end Complete

#print axioms ContextCalculus.ELCompletion.checkTraceFast_eq
#print axioms ContextCalculus.ELCompletion.checkClosedTraceFast_sound
#print axioms ContextCalculus.ELCompletion.DecodedCertificate.checkV5Fast_sound
#print axioms ContextCalculus.ELCompletion.WireCertificate.checkFast_sound

end ContextCalculus.ELCompletion
