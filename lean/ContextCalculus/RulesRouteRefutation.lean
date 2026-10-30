import ContextCalculus.RulesRouteSemantics
import Std.Data.HashSet
import Std.Data.HashMap

/-!
# Closed-tableau certificates for the rule route

A certificate is the closed search tree of the rule tableau
(`tableau.rs`, careful expansion). A branch state is a finite set of facts over
node numbers: concept literals, role edges and existential obligations. The
initial state of a test with root label `L` has node `0` carrying `L` and node
`k + 1` carrying the `k`-th nominal, as in `Tableau::find_model`. A proof node
runs a list of deterministic steps and then closes the branch:

* `horn c σ`: clause `c` has one head atom and its body holds under `σ`; the
  head is added (an equality head merges the two nodes);
* `witness s r C`: an obligation `∃r.C` at `s` gets a fresh successor;
* `nominal a b c`: two nodes carrying the nominal `c` are merged;
* the branch closes on a clash `C, ¬C`, on a clause with an empty head whose
  body holds, or splits on a clause body that holds into one sub-proof per
  head atom.

A merge copies every fact of the removed node onto the surviving one; the
removed node keeps its facts (they stay true). The per-node fact index used to
find them is untrusted: soundness never depends on it.

`checkProof_sound` proves that a checked proof has no realization in a model
of the clause list. With `RulesRouteSemantics` this gives the DL-safe
entailments of `refutation_*`.
-/

namespace ContextCalculus.RulesRoute

open ContextCalculus.Hypertableau

inductive RFact where
  | lab (node concept : Nat) (neg : Bool)
  | edge (role source target : Nat)
  | obl (role concept : Nat) (neg : Bool) (node : Nat)
deriving DecidableEq, Hashable, Repr

namespace RFact

def nodes : RFact → List Nat
  | lab n _ _ => [n]
  | edge _ s t => [s, t]
  | obl _ _ _ n => [n]

def holds {D : Type} (I : Interp D Nat Nat) (val : Nat → D) : RFact → Prop
  | lab n c neg => I.satLit ⟨c, neg⟩ (val n)
  | edge r s t => I.role r (val s) (val t)
  | obl r c neg n => ∃ w, I.role r (val n) w ∧ I.satLit ⟨c, neg⟩ w

def ren (gone keep n : Nat) : Nat := if n = gone then keep else n

def rename (gone keep : Nat) : RFact → RFact
  | lab n c neg => lab (ren gone keep n) c neg
  | edge r s t => edge r (ren gone keep s) (ren gone keep t)
  | obl r c neg n => obl r c neg (ren gone keep n)

theorem holds_congr {D : Type} (I : Interp D Nat Nat) {val val' : Nat → D} (f : RFact)
    (h : ∀ n ∈ f.nodes, val n = val' n) : f.holds I val ↔ f.holds I val' := by
  cases f <;> simp_all [nodes, holds]

theorem holds_rename {D : Type} (I : Interp D Nat Nat) {val : Nat → D} {gone keep : Nat}
    (heq : val gone = val keep) (f : RFact) (h : f.holds I val) :
    (f.rename gone keep).holds I val := by
  have hv : ∀ n, val (ren gone keep n) = val n := by
    intro n
    unfold ren
    split
    · rename_i h; rw [h, heq]
    · rfl
  cases f <;> simp_all [rename, holds]

theorem nodes_rename {gone keep : Nat} (f : RFact) {n : Nat}
    (h : n ∈ (f.rename gone keep).nodes) : n ∈ f.nodes ∨ n = keep := by
  have hr : ∀ m, n = ren gone keep m → n = m ∨ n = keep := by
    intro m hm
    unfold ren at hm
    split at hm
    · exact Or.inr hm
    · exact Or.inl hm
  cases f with
  | lab m c neg =>
      simp only [rename, nodes, List.mem_singleton] at h
      rcases hr m h with h | h
      · exact Or.inl (by simp [nodes, h])
      · exact Or.inr h
  | edge r s t =>
      simp only [rename, nodes, List.mem_cons, List.mem_singleton, List.not_mem_nil,
        or_false] at h
      rcases h with h | h
      · rcases hr s h with h | h
        · exact Or.inl (by simp [nodes, h])
        · exact Or.inr h
      · rcases hr t h with h | h
        · exact Or.inl (by simp [nodes, h])
        · exact Or.inr h
  | obl r c neg m =>
      simp only [rename, nodes, List.mem_singleton] at h
      rcases hr m h with h | h
      · exact Or.inl (by simp [nodes, h])
      · exact Or.inr h

end RFact

open RFact

structure RState where
  facts : Std.HashSet RFact
  index : Std.HashMap Nat (List RFact)
  next : Nat

namespace RState

def has (S : RState) (f : RFact) : Bool := S.facts.contains f

def add (S : RState) (f : RFact) : RState where
  facts := S.facts.insert f
  index := f.nodes.foldl (fun m n => m.insert n (f :: m.getD n [])) S.index
  next := S.next

theorem has_add (S : RState) (f g : RFact) : (S.add f).has g = (f == g || S.has g) := by
  simp [has, add, Std.HashSet.contains_insert]

@[simp] theorem next_add (S : RState) (f : RFact) : (S.add f).next = S.next := rfl

def Realized {D : Type} (I : Interp D Nat Nat) (val : Nat → D) (S : RState) : Prop :=
  ∀ f, S.has f = true → f.holds I val ∧ ∀ n ∈ f.nodes, n < S.next

variable {D : Type} (I : Interp D Nat Nat)

theorem realized_add {val : Nat → D} {S : RState} (hS : Realized I val S) {f : RFact}
    (hf : f.holds I val) (hn : ∀ n ∈ f.nodes, n < S.next) : Realized I val (S.add f) := by
  intro g hg
  rw [has_add] at hg
  rcases Bool.or_eq_true _ _ ▸ hg with h | h
  · have : f = g := by simpa using h
    subst this
    exact ⟨hf, hn⟩
  · exact hS g h

def mergeInto (S : RState) (gone keep : Nat) : RState :=
  (S.index.getD gone []).foldl
    (fun T f => if T.has f then T.add (f.rename gone keep) else T) S

def merge (S : RState) (x y : Nat) : RState :=
  if x = y then S else S.mergeInto (max x y) (min x y)

theorem foldl_merge_realized {val : Nat → D} {gone keep : Nat} (heq : val gone = val keep)
    (hkeep : ∀ T : RState, keep < T.next ∨ True → True) :
    ∀ (L : List RFact) (T : RState), Realized I val T → keep < T.next →
      Realized I val (L.foldl (fun T f => if T.has f then T.add (f.rename gone keep) else T) T) ∧
      (L.foldl (fun T f => if T.has f then T.add (f.rename gone keep) else T) T).next = T.next := by
  intro L
  induction L with
  | nil => intro T hT _; exact ⟨hT, rfl⟩
  | cons f rest ih =>
      intro T hT hk
      simp only [List.foldl_cons]
      split
      · rename_i hf
        obtain ⟨hholds, hnodes⟩ := hT f hf
        have hT' := realized_add I hT (holds_rename I heq f hholds) (by
          intro n hn
          rcases nodes_rename f hn with h | h
          · exact hnodes n h
          · exact h ▸ hk)
        obtain ⟨h1, h2⟩ := ih (T.add (f.rename gone keep)) hT' (by simpa using hk)
        exact ⟨h1, by simpa using h2⟩
      · exact ih T hT hk

theorem merge_realized {val : Nat → D} {S : RState} (hS : Realized I val S) {x y : Nat}
    (heq : val x = val y) (hx : x < S.next) (hy : y < S.next) :
    Realized I val (S.merge x y) ∧ (S.merge x y).next = S.next := by
  unfold merge
  split
  · exact ⟨hS, rfl⟩
  · have heq' : val (max x y) = val (min x y) := by
      rcases Nat.le_total x y with h | h
      · rw [Nat.max_eq_right h, Nat.min_eq_left h, heq]
      · rw [Nat.max_eq_left h, Nat.min_eq_right h, heq]
    have hk : min x y < S.next := Nat.lt_of_le_of_lt (Nat.min_le_left x y) hx
    exact foldl_merge_realized I heq' (fun _ _ => trivial) _ S hS hk

def atomB (S : RState) (σ : Nat → Nat) : RAtom → Bool
  | .concept lit v => S.has (.lab (σ v) lit.concept lit.neg)
  | .role r s t => S.has (.edge r (σ s) (σ t))
  | .exists_ r fil v => S.has (.obl r fil.concept fil.neg (σ v))
  | .eq l r => σ l == σ r

theorem atomB_sound {val : Nat → D} {S : RState} (hS : Realized I val S) (σ : Nat → Nat)
    (a : RAtom) (h : S.atomB σ a = true) : I.satAtom (val ∘ σ) a := by
  cases a with
  | concept lit v =>
      have := (hS _ h).1
      simpa [RFact.holds, Interp.satAtom] using this
  | role r s t => simpa [RFact.holds, Interp.satAtom] using (hS _ h).1
  | exists_ r fil v => simpa [RFact.holds, Interp.satAtom] using (hS _ h).1
  | eq l r =>
      have : σ l = σ r := by simpa [atomB] using h
      simp [Interp.satAtom, this]

def addHead (S : RState) (σ : Nat → Nat) : RAtom → RState
  | .concept lit v => S.add (.lab (σ v) lit.concept lit.neg)
  | .role r s t => S.add (.edge r (σ s) (σ t))
  | .exists_ r fil v => S.add (.obl r fil.concept fil.neg (σ v))
  | .eq l r => S.merge (σ l) (σ r)

theorem addHead_realized {val : Nat → D} {S : RState} (hS : Realized I val S)
    (σ : Nat → Nat) (a : RAtom) (hvars : ∀ w ∈ atomVars a, σ w < S.next)
    (hsat : I.satAtom (val ∘ σ) a) :
    Realized I val (S.addHead σ a) ∧ (S.addHead σ a).next = S.next := by
  cases a with
  | concept lit v =>
      refine ⟨realized_add I hS (by simpa [RFact.holds, Interp.satAtom] using hsat) ?_, rfl⟩
      intro n hn
      simp only [RFact.nodes, List.mem_singleton] at hn
      exact hn ▸ hvars v (by simp [atomVars])
  | role r s t =>
      refine ⟨realized_add I hS (by simpa [RFact.holds, Interp.satAtom] using hsat) ?_, rfl⟩
      intro n hn
      simp only [RFact.nodes, List.mem_cons, List.mem_singleton, List.not_mem_nil,
        or_false] at hn
      rcases hn with rfl | rfl
      · exact hvars s (by simp [atomVars])
      · exact hvars t (by simp [atomVars])
  | exists_ r fil v =>
      refine ⟨realized_add I hS (by simpa [RFact.holds, Interp.satAtom] using hsat) ?_, rfl⟩
      intro n hn
      simp only [RFact.nodes, List.mem_singleton] at hn
      exact hn ▸ hvars v (by simp [atomVars])
  | eq l r =>
      exact merge_realized I hS (by simpa [Interp.satAtom] using hsat)
        (hvars l (by simp [atomVars])) (hvars r (by simp [atomVars]))

end RState

open RState

/-! ## Steps and proofs -/

inductive Step where
  | horn (clause : Nat) (assignment : List Nat)
  | witness (node role concept : Nat) (neg : Bool)
  | nominal (concept left right : Nat)
deriving Repr

inductive Proof where
  | clash (steps : List Step) (node concept : Nat)
  | bottom (steps : List Step) (clause : Nat) (assignment : List Nat)
  | split (steps : List Step) (clause : Nat) (assignment : List Nat) (children : List Proof)
deriving Repr

def asg (l : List Nat) : Nat → Nat := fun v => l.getD v 0

def varsBelow (cl : RClause) (σ : Nat → Nat) (next : Nat) : Bool :=
  (clauseVars cl).all (fun w => decide (σ w < next))

def witnessState (S : RState) (s r c : Nat) (neg : Bool) : RState :=
  (({ S with next := S.next + 1 } : RState).add (.edge r s S.next)).add (.lab S.next c neg)

def stepCheck (ontology : List RClause) (nominals : List Nat) (S : RState) : Step → Option RState
  | .horn ci a =>
      match ontology[ci]? with
      | some cl =>
          match cl.head with
          | [h] =>
              if varsBelow cl (asg a) S.next && cl.body.all (S.atomB (asg a)) then
                some (S.addHead (asg a) h)
              else none
          | _ => none
      | none => none
  | .witness s r c neg =>
      if S.has (.obl r c neg s) then some (witnessState S s r c neg) else none
  | .nominal c a b =>
      if nominals.contains c && S.has (.lab a c false) && S.has (.lab b c false) then
        some (S.merge a b)
      else none

def runSteps (ontology : List RClause) (nominals : List Nat) : RState → List Step → Option RState
  | S, [] => some S
  | S, st :: rest =>
      match stepCheck ontology nominals S st with
      | some T => runSteps ontology nominals T rest
      | none => none

mutual
def checkProof (ontology : List RClause) (nominals : List Nat) : RState → Proof → Bool
  | S, .clash steps n c =>
      match runSteps ontology nominals S steps with
      | some T => T.has (.lab n c false) && T.has (.lab n c true)
      | none => false
  | S, .bottom steps ci a =>
      match runSteps ontology nominals S steps with
      | some T =>
          match ontology[ci]? with
          | some cl => cl.head.isEmpty && cl.body.all (T.atomB (asg a))
          | none => false
      | none => false
  | S, .split steps ci a children =>
      match runSteps ontology nominals S steps with
      | some T =>
          match ontology[ci]? with
          | some cl =>
              varsBelow cl (asg a) T.next && cl.body.all (T.atomB (asg a)) &&
                checkChildren ontology nominals T (asg a) cl.head children
          | none => false
      | none => false
def checkChildren (ontology : List RClause) (nominals : List Nat) (T : RState)
    (σ : Nat → Nat) : List RAtom → List Proof → Bool
  | [], [] => true
  | a :: as, p :: ps =>
      checkProof ontology nominals (T.addHead σ a) p && checkChildren ontology nominals T σ as ps
  | _, _ => false
end

/-! ## Soundness -/

section Soundness

variable {D : Type} (I : Interp D Nat Nat) {nominals : List Nat} {ontology : List RClause}

theorem witnessState_realized {val : Nat → D} {S : RState} (hS : Realized I val S)
    {s r c : Nat} {neg : Bool} (h : S.has (.obl r c neg s) = true) :
    ∃ val', Realized I val' (witnessState S s r c neg) := by
  obtain ⟨⟨w, hrole, hlit⟩, hnodes⟩ := hS _ h
  have hs : s < S.next := hnodes s (by simp [RFact.nodes])
  let val' : Nat → D := fun n => if n = S.next then w else val n
  have hagree : ∀ f, S.has f = true → f.holds I val' := by
    intro f hf
    obtain ⟨hholds, hn⟩ := hS f hf
    refine (holds_congr I f ?_).mp hholds
    intro n hnmem
    have : n ≠ S.next := Nat.ne_of_lt (hn n hnmem)
    simp [val', this]
  refine ⟨val', ?_⟩
  have hS1 : Realized I val' ({ S with next := S.next + 1 } : RState) := by
    intro f hf
    exact ⟨hagree f hf, fun n hn => Nat.lt_succ_of_lt ((hS f hf).2 n hn)⟩
  have hS2 := realized_add I hS1 (f := .edge r s S.next)
    (by simp [RFact.holds, val', Nat.ne_of_lt hs, hrole])
    (by
      intro n hn
      simp only [RFact.nodes, List.mem_cons, List.mem_singleton, List.not_mem_nil,
        or_false] at hn
      rcases hn with rfl | rfl
      · exact Nat.lt_succ_of_lt hs
      · exact Nat.lt_succ_self _)
  exact realized_add I hS2 (f := .lab S.next c neg)
    (by simpa [RFact.holds, val'] using hlit)
    (by
      intro n hn
      simp only [RFact.nodes, List.mem_singleton] at hn
      subst hn
      exact Nat.lt_succ_self _)

theorem stepCheck_sound (hm : ClauseModel I nominals ontology) {val : Nat → D} {S T : RState}
    (hS : Realized I val S) (st : Step) (h : stepCheck ontology nominals S st = some T) :
    ∃ val', Realized I val' T := by
  cases st with
  | horn ci a =>
      simp only [stepCheck] at h
      split at h
      · rename_i cl hcl
        split at h
        · rename_i hd hhead
          split at h
          · rename_i hcond
            simp only [Option.some.injEq] at h
            subst h
            simp only [Bool.and_eq_true, List.all_eq_true] at hcond
            obtain ⟨hvars, hbody⟩ := hcond
            have hmem : cl ∈ ontology := List.mem_of_getElem? hcl
            obtain ⟨b, hb, hsat⟩ := hm.2 cl hmem (val ∘ asg a)
              (fun b hb => atomB_sound I hS (asg a) b (hbody b hb))
            rw [hhead] at hb
            simp only [List.mem_singleton] at hb
            subst hb
            refine ⟨val, (addHead_realized I hS (asg a) b ?_ hsat).1⟩
            intro w hw
            simp only [varsBelow, List.all_eq_true, decide_eq_true_eq] at hvars
            exact hvars w (mem_clauseVars_of_head (by rw [hhead]; simp) hw)
          · exact absurd h (by simp)
        · exact absurd h (by simp)
      · exact absurd h (by simp)
  | witness s r c neg =>
      simp only [stepCheck] at h
      split at h
      · rename_i hobl
        simp only [Option.some.injEq] at h
        subst h
        exact witnessState_realized I hS hobl
      · exact absurd h (by simp)
  | nominal c a b =>
      simp only [stepCheck] at h
      split at h
      · rename_i hcond
        simp only [Option.some.injEq] at h
        subst h
        simp only [Bool.and_eq_true] at hcond
        obtain ⟨⟨hc, ha⟩, hb⟩ := hcond
        obtain ⟨hla, hna⟩ := hS _ ha
        obtain ⟨hlb, hnb⟩ := hS _ hb
        obtain ⟨d, hd⟩ := hm.1 c (List.contains_iff_mem.mp hc)
        have hva : val a = d := (hd (val a)).mp (by simpa [RFact.holds, Interp.satLit] using hla)
        have hvb : val b = d := (hd (val b)).mp (by simpa [RFact.holds, Interp.satLit] using hlb)
        exact ⟨val, (merge_realized I hS (hva.trans hvb.symm)
          (hna a (by simp [RFact.nodes])) (hnb b (by simp [RFact.nodes]))).1⟩
      · exact absurd h (by simp)

theorem runSteps_sound (hm : ClauseModel I nominals ontology) :
    ∀ (steps : List Step) (S T : RState) (val : Nat → D), Realized I val S →
      runSteps ontology nominals S steps = some T → ∃ val', Realized I val' T := by
  intro steps
  induction steps with
  | nil =>
      intro S T val hS h
      simp only [runSteps, Option.some.injEq] at h
      exact ⟨val, h ▸ hS⟩
  | cons st rest ih =>
      intro S T val hS h
      simp only [runSteps] at h
      split at h
      · rename_i T' hT'
        obtain ⟨val', hval'⟩ := stepCheck_sound I hm hS st hT'
        exact ih T' T val' hval' h
      · exact absurd h (by simp)

mutual
theorem checkProof_sound (hm : ClauseModel I nominals ontology) :
    ∀ (p : Proof) (S : RState) (val : Nat → D),
      checkProof ontology nominals S p = true → Realized I val S → False
  | .clash steps n c, S, val, h, hS => by
      simp only [checkProof] at h
      split at h
      · rename_i T hT
        obtain ⟨val', hval'⟩ := runSteps_sound I hm steps S T val hS hT
        simp only [Bool.and_eq_true] at h
        have hpos := (hval' _ h.1).1
        have hneg := (hval' _ h.2).1
        simp [RFact.holds, Interp.satLit] at hpos hneg
        exact hneg hpos
      · exact absurd h (by simp)
  | .bottom steps ci a, S, val, h, hS => by
      simp only [checkProof] at h
      split at h
      · rename_i T hT
        obtain ⟨val', hval'⟩ := runSteps_sound I hm steps S T val hS hT
        split at h
        · rename_i cl hcl
          simp only [Bool.and_eq_true, List.isEmpty_iff, List.all_eq_true] at h
          obtain ⟨hempty, hbody⟩ := h
          obtain ⟨b, hb, _⟩ := hm.2 cl (List.mem_of_getElem? hcl) (val' ∘ asg a)
            (fun b hb => atomB_sound I hval' (asg a) b (hbody b hb))
          rw [hempty] at hb
          simp at hb
        · exact absurd h (by simp)
      · exact absurd h (by simp)
  | .split steps ci a children, S, val, h, hS => by
      simp only [checkProof] at h
      split at h
      · rename_i T hT
        obtain ⟨val', hval'⟩ := runSteps_sound I hm steps S T val hS hT
        split at h
        · rename_i cl hcl
          simp only [Bool.and_eq_true, List.all_eq_true] at h
          obtain ⟨⟨hvars, hbody⟩, hchildren⟩ := h
          have hsat := hm.2 cl (List.mem_of_getElem? hcl) (val' ∘ asg a)
            (fun b hb => atomB_sound I hval' (asg a) b (hbody b hb))
          refine checkChildren_sound hm cl.head children T (asg a) val' hchildren hval' ?_ hsat
          intro b hb w hw
          simp only [varsBelow, List.all_eq_true, decide_eq_true_eq] at hvars
          exact hvars w (mem_clauseVars_of_head hb hw)
        · exact absurd h (by simp)
      · exact absurd h (by simp)
theorem checkChildren_sound (hm : ClauseModel I nominals ontology) :
    ∀ (as : List RAtom) (ps : List Proof) (T : RState) (σ : Nat → Nat) (val : Nat → D),
      checkChildren ontology nominals T σ as ps = true → Realized I val T →
      (∀ a ∈ as, ∀ w ∈ atomVars a, σ w < T.next) →
      (∃ a ∈ as, I.satAtom (val ∘ σ) a) → False
  | [], [], _, _, _, _, _, _, hsat => by simp at hsat
  | a :: as, p :: ps, T, σ, val, h, hT, hvars, hsat => by
      simp only [checkChildren, Bool.and_eq_true] at h
      rcases hsat with ⟨b, hb, hbsat⟩
      rcases List.mem_cons.mp hb with rfl | hb'
      · exact checkProof_sound hm p (T.addHead σ b) val h.1
          (addHead_realized I hT σ b (hvars b (List.mem_cons_self ..)) hbsat).1
      · exact checkChildren_sound hm as ps T σ val h.2 hT
          (fun c hc => hvars c (List.mem_cons_of_mem _ hc)) ⟨b, hb', hbsat⟩
  | [], _ :: _, _, _, _, h, _, _, _ => by simp [checkChildren] at h
  | _ :: _, [], _, _, _, h, _, _, _ => by simp [checkChildren] at h
end

end Soundness

/-! ## Initial states -/

def nominalFacts : List Nat → Nat → List RFact
  | [], _ => []
  | c :: rest, i => .lab i c false :: nominalFacts rest (i + 1)

def addAll (S : RState) (facts : List RFact) : RState := facts.foldl RState.add S

def initState (root : List RLit) (nominals : List Nat) : RState :=
  addAll { facts := ∅, index := ∅, next := nominals.length + 1 }
    (root.map (fun l => .lab 0 l.concept l.neg) ++ nominalFacts nominals 1)

theorem mem_nominalFacts : ∀ (l : List Nat) (i : Nat) (f : RFact), f ∈ nominalFacts l i →
    ∃ k, ∃ h : k < l.length, f = .lab (i + k) l[k] false
  | [], _, _, h => by simp [nominalFacts] at h
  | c :: rest, i, f, h => by
      simp only [nominalFacts, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨0, by simp, by simp⟩
      · obtain ⟨k, hk, rfl⟩ := mem_nominalFacts rest (i + 1) f h
        exact ⟨k + 1, by simp [hk], by simp [Nat.add_assoc, Nat.add_comm 1 k]⟩

section Init

variable {D : Type} (I : Interp D Nat Nat)

theorem addAll_realized {val : Nat → D} :
    ∀ (facts : List RFact) (S : RState), Realized I val S →
      (∀ f ∈ facts, f.holds I val ∧ ∀ n ∈ f.nodes, n < S.next) →
      Realized I val (addAll S facts)
  | [], S, hS, _ => hS
  | f :: rest, S, hS, hf => by
      have h1 := realized_add I hS (hf f (List.mem_cons_self ..)).1 (hf f (List.mem_cons_self ..)).2
      exact addAll_realized rest (S.add f) h1 (fun g hg => by
        simpa using hf g (List.mem_cons_of_mem _ hg))

open Classical in
/-- The values of the initial nodes: the tested element and the nominal elements. -/
noncomputable def initVal (nominals : List Nat) (hs : Singletons I nominals) (d : D) : Nat → D
  | 0 => d
  | k + 1 =>
      if h : k < nominals.length then
        Classical.choose (hs nominals[k] (List.getElem_mem h))
      else d

theorem initState_realized {nominals : List Nat} (hs : Singletons I nominals)
    (root : List RLit) (d : D) (hroot : ∀ l ∈ root, I.satLit l d) :
    Realized I (initVal I nominals hs d) (initState root nominals) := by
  unfold initState
  apply addAll_realized
  · intro f hf
    simp [RState.has] at hf
  · intro f hf
    rcases List.mem_append.mp hf with hf | hf
    · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hf
      refine ⟨?_, ?_⟩
      · simpa [RFact.holds, initVal] using hroot l hl
      · simp [RFact.nodes]
    · obtain ⟨k, hk, rfl⟩ := mem_nominalFacts nominals 1 f hf
      refine ⟨?_, ?_⟩
      · have hspec := Classical.choose_spec (hs nominals[k] (List.getElem_mem hk))
        simp only [RFact.holds, Interp.satLit, Bool.false_eq_true, if_false]
        rw [Nat.add_comm 1 k]
        simp only [initVal, dif_pos hk]
        exact (hspec _).mpr rfl
      · simp only [RFact.nodes, List.mem_singleton]
        intro n hn
        omega

end Init

/-! ## Entailments established by a checked proof -/

theorem refutes_root {nominals : List Nat} {ontology : List RClause} {root : List RLit}
    {p : Proof} (h : checkProof ontology nominals (initState root nominals) p = true)
    {D : Type} (I : Interp D Nat Nat) (hm : ClauseModel I nominals ontology) (d : D)
    (hroot : ∀ l ∈ root, I.satLit l d) : False :=
  checkProof_sound I hm p _ _ h (initState_realized I hm.1 root d hroot)

theorem refutation_inconsistent {o : Nat} {nominals : List Nat} {ontology : List RClause}
    (henc : encodingOK o nominals ontology = true) {p : Proof}
    (h : checkProof ontology nominals (initState [] nominals) p = true) :
    ¬Consistent (decode o nominals ontology) := by
  apply not_consistent_of_clausal henc
  intro D hne I hm
  obtain ⟨d⟩ := hne
  exact refutes_root h I hm d (by simp)

theorem refutation_unsat {o : Nat} {nominals : List Nat} {ontology : List RClause}
    (henc : encodingOK o nominals ontology = true) {concept : Nat} (hc : concept ≠ o)
    {p : Proof} (h : checkProof ontology nominals (initState [⟨concept, false⟩] nominals) p = true) :
    UnsatConcept (decode o nominals ontology) concept := by
  apply unsatConcept_of_clausal henc hc
  intro D I hm d hd
  exact refutes_root h I hm d (by simpa [Interp.satLit] using hd)

theorem refutation_sub {o : Nat} {nominals : List Nat} {ontology : List RClause}
    (henc : encodingOK o nominals ontology = true) {sub sup : Nat} (hsub : sub ≠ o)
    (hsup : sup ≠ o) {p : Proof}
    (h : checkProof ontology nominals
      (initState [⟨sub, false⟩, ⟨sup, true⟩] nominals) p = true) :
    EntailsSub (decode o nominals ontology) sub sup := by
  apply entailsSub_of_clausal henc hsub hsup
  intro D I hm d hd
  by_contra hnot
  exact refutes_root h I hm d (by
    intro l hl
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · simpa [Interp.satLit] using hd
    · simpa [Interp.satLit] using hnot)

end ContextCalculus.RulesRoute
