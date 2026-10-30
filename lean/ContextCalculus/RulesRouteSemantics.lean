import ContextCalculus.Hypertableau

/-!
# DL-safe rules in the rule-route clause language

The rule-consistency worker (`KM_RULES_CONSISTENCY`, `KM_RULES_CLASSIFY`,
engine `tableau.rs`) receives one flat list of hypertableau clauses over the
atoms of `ContextCalculus.Hypertableau` (concept literals, roles, existential
obligations, equality). Three kinds of clause share that list:

* ordinary clauses of the ontology (TBox, ABox as nominal facts, role-chain
  clauses);
* *introduction clauses* `{a}(x) → O(x)`, one per nominal `{a}` of a named
  individual, that mark the named elements with the reserved guard concept
  `O` (`__O__` in `cb_to_ht.rs`);
* *rule clauses*: a DL-safe rule whose body carries a guard atom `O(v)` for
  every variable `v` of the clause.

This module states the DL-safe semantics of such a clause list without `O`
(rules range over the elements that interpret named individuals, Motik, Sattler
and Studer 2005) and proves that the guarded clause list has a model iff the
decoded knowledge base has a DL-safe model (`clauseModel_of_dlSafeModel`,
`dlSafeModel_of_clauseModel`). Entailment and non-entailment therefore
transfer in both directions (`entailsSub_of_clausal`, ...).

The syntactic conditions are checked by `encodingOK`: `O` is not a nominal,
occurs only positively in rule bodies and in introduction-clause heads, every
nominal has an introduction clause, and each rule clause guards each of its
variables.
-/

namespace ContextCalculus.RulesRoute

open ContextCalculus.Hypertableau

abbrev RLit := Lit Nat
abbrev RAtom := Atom Nat Nat Nat
abbrev RClause := Clause Nat Nat Nat

/-! ## Syntax -/

def atomVars : RAtom → List Nat
  | .concept _ v => [v]
  | .role _ s t => [s, t]
  | .exists_ _ _ v => [v]
  | .eq l r => [l, r]

def clauseVars (cl : RClause) : List Nat := (cl.body ++ cl.head).flatMap atomVars

def atomMentions (o : Nat) : RAtom → Bool
  | .concept lit _ => lit.concept == o
  | .exists_ _ filler _ => filler.concept == o
  | _ => false

def isGuard (o : Nat) : RAtom → Bool
  | .concept lit _ => lit.concept == o && !lit.neg
  | _ => false

def guardAtom (o v : Nat) : RAtom := .concept ⟨o, false⟩ v

/-- The nominal of an introduction clause `{n}(x) → O(x)`. -/
def introNominal? (o : Nat) (cl : RClause) : Option Nat :=
  match cl.body, cl.head with
  | [.concept l x], [.concept l' y] =>
      if !l.neg && !l'.neg && l'.concept == o && x == y && l.concept != o then
        some l.concept
      else none
  | _, _ => none

def isIntro (o : Nat) (cl : RClause) : Bool := (introNominal? o cl).isSome

def isRule (o : Nat) (cl : RClause) : Bool := !isIntro o cl && cl.body.any (isGuard o)

def isDL (o : Nat) (cl : RClause) : Bool := !isIntro o cl && !cl.body.any (isGuard o)

def ruleOK (o : Nat) (cl : RClause) : Bool :=
  cl.head.all (fun a => !atomMentions o a) &&
  cl.body.all (fun a => isGuard o a || !atomMentions o a) &&
  (clauseVars cl).all (fun v => cl.body.contains (guardAtom o v))

def dlOK (o : Nat) (cl : RClause) : Bool :=
  cl.body.all (fun a => !atomMentions o a) && cl.head.all (fun a => !atomMentions o a)

def clauseOK (o : Nat) (nominals : List Nat) (cl : RClause) : Bool :=
  match introNominal? o cl with
  | some n => nominals.contains n
  | none => if cl.body.any (isGuard o) then ruleOK o cl else dlOK o cl

/-- The decidable side conditions of the guarded encoding. -/
def encodingOK (o : Nat) (nominals : List Nat) (ontology : List RClause) : Bool :=
  !nominals.contains o &&
  ontology.all (clauseOK o nominals) &&
  nominals.all (fun n => ontology.any (fun cl => introNominal? o cl == some n))

def strip (o : Nat) (cl : RClause) : RClause :=
  { body := cl.body.filter (fun a => !isGuard o a), head := cl.head }

/-- A knowledge base with DL-safe rules: ordinary clauses, rules (without
guards) and the nominal concepts `{a}` of the named individuals. -/
structure KB where
  dl : List RClause
  rules : List RClause
  nominals : List Nat

def decode (o : Nat) (nominals : List Nat) (ontology : List RClause) : KB where
  dl := ontology.filter (isDL o)
  rules := (ontology.filter (isRule o)).map (strip o)
  nominals := nominals

/-! ## Semantics -/

section Semantics

variable {D : Type}

/-- `d` interprets a named individual. -/
def Named (I : Interp D Nat Nat) (nominals : List Nat) (d : D) : Prop :=
  ∃ n ∈ nominals, I.concept n d

/-- Every nominal concept `{a}` denotes exactly one element. -/
def Singletons (I : Interp D Nat Nat) (nominals : List Nat) : Prop :=
  ∀ n ∈ nominals, ∃ d, ∀ x, I.concept n x ↔ x = d

/-- DL-safe reading of a rule: it applies to assignments of named elements only. -/
def RuleHolds (I : Interp D Nat Nat) (nominals : List Nat) (rule : RClause) : Prop :=
  ∀ σ : Nat → D, (∀ v, Named I nominals (σ v)) →
    (∀ a ∈ rule.body, I.satAtom σ a) → ∃ a ∈ rule.head, I.satAtom σ a

def DLSafeModel (I : Interp D Nat Nat) (kb : KB) : Prop :=
  Singletons I kb.nominals ∧ (∀ cl ∈ kb.dl, I.modelsClause cl) ∧
    ∀ rule ∈ kb.rules, RuleHolds I kb.nominals rule

/-- First-order reading of the worker clause list: nominal singletons and all
clauses, with `O` an ordinary concept. -/
def ClauseModel (I : Interp D Nat Nat) (nominals : List Nat) (ontology : List RClause) : Prop :=
  Singletons I nominals ∧ I.models ontology

end Semantics

/-- The knowledge base has a DL-safe model with a non-empty domain. -/
def Consistent (kb : KB) : Prop :=
  ∃ (D : Type) (_ : Nonempty D) (I : Interp D Nat Nat), DLSafeModel I kb

def EntailsSub (kb : KB) (sub sup : Nat) : Prop :=
  ∀ (D : Type) (I : Interp D Nat Nat), DLSafeModel I kb →
    ∀ d, I.concept sub d → I.concept sup d

def UnsatConcept (kb : KB) (concept : Nat) : Prop :=
  ∀ (D : Type) (I : Interp D Nat Nat), DLSafeModel I kb → ∀ d, ¬I.concept concept d

/-! ## Basic lemmas -/

section Lemmas

variable {D : Type}

theorem satAtom_congr (I : Interp D Nat Nat) {σ τ : Nat → D} (a : RAtom)
    (h : ∀ w ∈ atomVars a, σ w = τ w) : (I.satAtom σ a ↔ I.satAtom τ a) := by
  cases a with
  | concept lit v =>
      simp only [atomVars, List.mem_singleton, forall_eq] at h
      simp [Interp.satAtom, h]
  | role r s t =>
      simp only [atomVars, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at h
      simp [Interp.satAtom, h.1, h.2]
  | exists_ r fil v =>
      simp only [atomVars, List.mem_singleton, forall_eq] at h
      simp [Interp.satAtom, h]
  | eq l r =>
      simp only [atomVars, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at h
      simp [Interp.satAtom, h.1, h.2]

/-- Override the interpretation of one concept. -/
def withConcept (I : Interp D Nat Nat) (o : Nat) (P : D → Prop) : Interp D Nat Nat where
  concept c d := if c = o then P d else I.concept c d
  role := I.role

theorem satAtom_withConcept (I : Interp D Nat Nat) (o : Nat) (P : D → Prop)
    (σ : Nat → D) (a : RAtom) (h : atomMentions o a = false) :
    (withConcept I o P).satAtom σ a ↔ I.satAtom σ a := by
  cases a with
  | concept lit v =>
      have hne : lit.concept ≠ o := by simpa [atomMentions] using h
      simp [Interp.satAtom, Interp.satLit, withConcept, hne]
  | role r s t => simp [Interp.satAtom, withConcept]
  | exists_ r fil v =>
      have hne : fil.concept ≠ o := by simpa [atomMentions] using h
      simp [Interp.satAtom, Interp.satLit, withConcept, hne]
  | eq l r => simp [Interp.satAtom]

theorem introNominal?_spec {o : Nat} {cl : RClause} {n : Nat}
    (h : introNominal? o cl = some n) :
    ∃ x, cl.body = [.concept ⟨n, false⟩ x] ∧ cl.head = [.concept ⟨o, false⟩ x] ∧ n ≠ o := by
  rcases cl with ⟨body, head⟩
  match body, head, h with
  | [.concept ⟨c, neg⟩ x], [.concept ⟨c', neg'⟩ y], h =>
      simp only [introNominal?] at h
      split at h
      · rename_i hcond
        simp only [Option.some.injEq] at h
        subst h
        simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, bne_iff_ne, ne_eq] at hcond
        rcases hcond with ⟨⟨⟨⟨hl, hl'⟩, ho⟩, hxy⟩, hno⟩
        subst hl hl' ho hxy
        exact ⟨x, rfl, rfl, hno⟩
      · exact absurd h (by simp)

theorem named_withConcept (I : Interp D Nat Nat) (o : Nat) (P : D → Prop)
    (nominals : List Nat) (ho : o ∉ nominals) (d : D) :
    Named (withConcept I o P) nominals d ↔ Named I nominals d := by
  unfold Named
  constructor
  · rintro ⟨n, hn, hc⟩
    have hne : n ≠ o := fun h => ho (h ▸ hn)
    exact ⟨n, hn, by simpa [withConcept, hne] using hc⟩
  · rintro ⟨n, hn, hc⟩
    have hne : n ≠ o := fun h => ho (h ▸ hn)
    exact ⟨n, hn, by simpa [withConcept, hne] using hc⟩

theorem mem_clauseVars_of_body {cl : RClause} {a : RAtom} (ha : a ∈ cl.body)
    {w : Nat} (hw : w ∈ atomVars a) : w ∈ clauseVars cl := by
  unfold clauseVars
  exact List.mem_flatMap.mpr ⟨a, List.mem_append.mpr (Or.inl ha), hw⟩

theorem mem_clauseVars_of_head {cl : RClause} {a : RAtom} (ha : a ∈ cl.head)
    {w : Nat} (hw : w ∈ atomVars a) : w ∈ clauseVars cl := by
  unfold clauseVars
  exact List.mem_flatMap.mpr ⟨a, List.mem_append.mpr (Or.inr ha), hw⟩

theorem isGuard_eq {o : Nat} {a : RAtom} (h : isGuard o a = true) :
    ∃ v, a = guardAtom o v := by
  cases a with
  | concept lit v =>
      rcases lit with ⟨c, neg⟩
      simp only [isGuard, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
      rcases h with ⟨rfl, rfl⟩
      exact ⟨v, rfl⟩
  | _ => simp [isGuard] at h

end Lemmas

/-! ## The bridge between the clause reading and the DL-safe reading -/

section Bridge

variable {D : Type}

theorem encodingOK_parts {o : Nat} {nominals : List Nat} {ontology : List RClause}
    (h : encodingOK o nominals ontology = true) :
    o ∉ nominals ∧ (∀ cl ∈ ontology, clauseOK o nominals cl = true) ∧
      (∀ n ∈ nominals, ∃ cl ∈ ontology, introNominal? o cl = some n) := by
  simp only [encodingOK, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true,
    List.any_eq_true, beq_iff_eq] at h
  rcases h with ⟨⟨hno, hcl⟩, hintro⟩
  refine ⟨?_, hcl, hintro⟩
  intro hmem
  have : nominals.contains o = true := List.contains_iff_mem.mpr hmem
  simp_all

/-- A DL-safe model, with `O` interpreted as the named elements, is a model of
the guarded clause list. -/
theorem clauseModel_of_dlSafeModel {o : Nat} {nominals : List Nat}
    {ontology : List RClause} (henc : encodingOK o nominals ontology = true)
    (I : Interp D Nat Nat) (hm : DLSafeModel I (decode o nominals ontology)) :
    ClauseModel (withConcept I o (Named I nominals)) nominals ontology := by
  obtain ⟨ho, hcl, _⟩ := encodingOK_parts henc
  obtain ⟨hsing, hdl, hrules⟩ := hm
  refine ⟨?_, ?_⟩
  · intro n hn
    have hne : n ≠ o := fun h => ho (h ▸ hn)
    obtain ⟨d, hd⟩ := hsing n hn
    exact ⟨d, fun x => by simpa [withConcept, hne] using hd x⟩
  · intro cl hcl_mem σ hbody
    have hok := hcl cl hcl_mem
    unfold clauseOK at hok
    cases hintro : introNominal? o cl with
    | some n =>
        rw [hintro] at hok
        have hn : n ∈ nominals := List.contains_iff_mem.mp hok
        obtain ⟨x, hb, hh, hne⟩ := introNominal?_spec hintro
        refine ⟨.concept ⟨o, false⟩ x, by simp [hh], ?_⟩
        have hx := hbody (.concept ⟨n, false⟩ x) (by simp [hb])
        simp only [Interp.satAtom, Interp.satLit, withConcept, hne, if_false] at hx
        simp only [Interp.satAtom, Interp.satLit, withConcept, if_true]
        exact ⟨n, hn, by simpa using hx⟩
    | none =>
        rw [hintro] at hok
        have hnotintro : isIntro o cl = false := by simp [isIntro, hintro]
        by_cases hguard : cl.body.any (isGuard o) = true
        · rw [if_pos hguard] at hok
          simp only [ruleOK, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true',
            Bool.or_eq_true] at hok
          rcases hok with ⟨⟨hhead, hbodyok⟩, hvars⟩
          have hrule_mem : strip o cl ∈ (decode o nominals ontology).rules := by
            simp only [decode]
            exact List.mem_map.mpr ⟨cl, List.mem_filter.mpr ⟨hcl_mem, by
              simp [isRule, hnotintro, hguard]⟩, rfl⟩
          -- every clause variable is named under σ
          have hnamed : ∀ v ∈ clauseVars cl, Named I nominals (σ v) := by
            intro v hv
            have hg := hbody (guardAtom o v) (List.contains_iff_mem.mp (hvars v hv))
            simpa [guardAtom, Interp.satAtom, Interp.satLit, withConcept] using hg
          obtain ⟨g, hgmem, hgg⟩ := List.any_eq_true.mp hguard
          obtain ⟨v0, rfl⟩ := isGuard_eq hgg
          have hv0 : v0 ∈ clauseVars cl :=
            mem_clauseVars_of_body hgmem (by simp [atomVars, guardAtom])
          let σ' : Nat → D := fun v => if v ∈ clauseVars cl then σ v else σ v0
          have hσ'named : ∀ v, Named I nominals (σ' v) := by
            intro v
            by_cases hv : v ∈ clauseVars cl
            · simp only [σ', if_pos hv]; exact hnamed v hv
            · simp only [σ', if_neg hv]; exact hnamed v0 hv0
          have hagree : ∀ a, (∀ w ∈ atomVars a, w ∈ clauseVars cl) →
              ∀ w ∈ atomVars a, σ w = σ' w := by
            intro a ha w hw
            simp [σ', ha w hw]
          have hstripbody : ∀ a ∈ (strip o cl).body, I.satAtom σ' a := by
            intro a ha
            simp only [strip, List.mem_filter, Bool.not_eq_true'] at ha
            rcases ha with ⟨ha, hng⟩
            have hm : atomMentions o a = false := by
              rcases hbodyok a ha with h | h
              · simp_all
              · exact h
            have h1 := hbody a ha
            rw [satAtom_withConcept I o _ σ a hm] at h1
            exact (satAtom_congr I a (hagree a (fun w hw =>
              mem_clauseVars_of_body ha hw))).mp h1
          obtain ⟨a, ha, hsat⟩ := hrules _ hrule_mem σ' hσ'named hstripbody
          refine ⟨a, ha, ?_⟩
          have ha' : a ∈ cl.head := ha
          rw [satAtom_withConcept I o _ σ a (hhead a ha')]
          exact (satAtom_congr I a (hagree a (fun w hw =>
            mem_clauseVars_of_head ha' hw))).mpr hsat
        · rw [if_neg hguard] at hok
          simp only [dlOK, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hok
          have hdl_mem : cl ∈ (decode o nominals ontology).dl := by
            simp only [decode]
            exact List.mem_filter.mpr ⟨hcl_mem, by simp [isDL, hnotintro, hguard]⟩
          have hbody' : ∀ a ∈ cl.body, I.satAtom σ a := by
            intro a ha
            exact (satAtom_withConcept I o _ σ a (hok.1 a ha)).mp (hbody a ha)
          obtain ⟨a, ha, hsat⟩ := hdl cl hdl_mem σ hbody'
          exact ⟨a, ha, (satAtom_withConcept I o _ σ a (hok.2 a ha)).mpr hsat⟩

/-- A model of the guarded clause list is a DL-safe model of the decoded
knowledge base. -/
theorem dlSafeModel_of_clauseModel {o : Nat} {nominals : List Nat}
    {ontology : List RClause} (henc : encodingOK o nominals ontology = true)
    (I : Interp D Nat Nat) (hm : ClauseModel I nominals ontology) :
    DLSafeModel I (decode o nominals ontology) := by
  obtain ⟨_, hcl, hintro⟩ := encodingOK_parts henc
  obtain ⟨hsing, hmodels⟩ := hm
  refine ⟨hsing, ?_, ?_⟩
  · intro cl hcl_mem
    simp only [decode, List.mem_filter] at hcl_mem
    exact hmodels cl hcl_mem.1
  · intro rule hrule σ hnamed hbody
    simp only [decode, List.mem_map, List.mem_filter] at hrule
    obtain ⟨cl, ⟨hcl_mem, _⟩, rfl⟩ := hrule
    apply hmodels cl hcl_mem σ
    intro a ha
    by_cases hg : isGuard o a = true
    · obtain ⟨v, rfl⟩ := isGuard_eq hg
      obtain ⟨n, hn, hc⟩ := hnamed v
      obtain ⟨icl, hicl, hin⟩ := hintro n hn
      obtain ⟨x, hb, hh, _⟩ := introNominal?_spec hin
      have := hmodels icl hicl (fun _ => σ v) (by
        intro b hbmem
        rw [hb] at hbmem
        simp only [List.mem_singleton] at hbmem
        subst hbmem
        simpa [Interp.satAtom, Interp.satLit] using hc)
      obtain ⟨b, hbmem, hbsat⟩ := this
      rw [hh] at hbmem
      simp only [List.mem_singleton] at hbmem
      subst hbmem
      simpa [guardAtom, Interp.satAtom, Interp.satLit] using hbsat
    · exact hbody a (by simp [strip, ha, hg])

/-! ## Transfer of answers -/

theorem consistent_of_clauseModel {o : Nat} {nominals : List Nat} {ontology : List RClause}
    (henc : encodingOK o nominals ontology = true) {D : Type} [Nonempty D]
    (I : Interp D Nat Nat) (hm : ClauseModel I nominals ontology) :
    Consistent (decode o nominals ontology) :=
  ⟨D, inferInstance, I, dlSafeModel_of_clauseModel henc I hm⟩

theorem not_consistent_of_clausal {o : Nat} {nominals : List Nat} {ontology : List RClause}
    (henc : encodingOK o nominals ontology = true)
    (h : ∀ (D : Type) [Nonempty D] (I : Interp D Nat Nat), ¬ClauseModel I nominals ontology) :
    ¬Consistent (decode o nominals ontology) := by
  rintro ⟨D, hne, I, hm⟩
  exact h D (withConcept I o (Named I nominals)) (clauseModel_of_dlSafeModel henc I hm)

theorem entailsSub_of_clausal {o : Nat} {nominals : List Nat} {ontology : List RClause}
    (henc : encodingOK o nominals ontology = true) {sub sup : Nat}
    (hsub : sub ≠ o) (hsup : sup ≠ o)
    (h : ∀ (D : Type) (I : Interp D Nat Nat), ClauseModel I nominals ontology →
      ∀ d, I.concept sub d → I.concept sup d) :
    EntailsSub (decode o nominals ontology) sub sup := by
  intro D I hm d hd
  have h' := h D _ (clauseModel_of_dlSafeModel henc I hm) d
    (by simpa [withConcept, hsub] using hd)
  simpa [withConcept, hsup] using h'

theorem unsatConcept_of_clausal {o : Nat} {nominals : List Nat} {ontology : List RClause}
    (henc : encodingOK o nominals ontology = true) {concept : Nat} (hc : concept ≠ o)
    (h : ∀ (D : Type) (I : Interp D Nat Nat), ClauseModel I nominals ontology →
      ∀ d, ¬I.concept concept d) :
    UnsatConcept (decode o nominals ontology) concept := by
  intro D I hm d hd
  exact h D _ (clauseModel_of_dlSafeModel henc I hm) d (by simpa [withConcept, hc] using hd)

theorem not_entailsSub_of_clauseModel {o : Nat} {nominals : List Nat} {ontology : List RClause}
    (henc : encodingOK o nominals ontology = true) {D : Type} (I : Interp D Nat Nat)
    (hm : ClauseModel I nominals ontology) {sub sup : Nat} (d : D)
    (hsub : I.concept sub d) (hsup : ¬I.concept sup d) :
    ¬EntailsSub (decode o nominals ontology) sub sup :=
  fun h => hsup (h D I (dlSafeModel_of_clauseModel henc I hm) d hsub)

theorem not_unsatConcept_of_clauseModel {o : Nat} {nominals : List Nat}
    {ontology : List RClause} (henc : encodingOK o nominals ontology = true) {D : Type}
    (I : Interp D Nat Nat) (hm : ClauseModel I nominals ontology) {concept : Nat} (d : D)
    (hc : I.concept concept d) : ¬UnsatConcept (decode o nominals ontology) concept :=
  fun h => h D I (dlSafeModel_of_clauseModel henc I hm) d hc

end Bridge

end ContextCalculus.RulesRoute
