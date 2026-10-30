import ContextCalculus.RulesRouteSemantics

/-!
# Finite model certificates for the rule route

A certificate is a finite interpretation: `n` elements, the positive concept
labels of each element and its outgoing role edges. Concepts are interpreted by
the positive labels (a negative literal holds where the positive label is
absent), roles by the edges. `FModel.check` evaluates every clause of the
worker input under every assignment and checks that every nominal concept
denotes exactly one element. The enumeration binds the clause variables one at
a time, stops as soon as a body atom over bound variables fails or a head atom
over bound variables holds, and draws the values of a variable that is the
target (source) of a body role atom with a bound source (target) from the
recorded successors (predecessors). `FModel.check_sound` proves that
acceptance yields a model of the clause list (`ClauseModel`), so by
`RulesRouteSemantics` a DL-safe model of the decoded knowledge base.
-/

namespace ContextCalculus.RulesRoute

open ContextCalculus.Hypertableau

structure FModel where
  n : Nat
  labels : Array (List Nat)
  succ : Array (List (Nat × Nat))
  pred : Array (List (Nat × Nat))
  /-- Elements carrying each concept (untrusted; `extComplete` checks it). -/
  ext : Array (List Nat)

namespace FModel

variable (M : FModel)

def lab (d c : Nat) : Bool := (M.labels.getD d []).contains c

def rel (r a b : Nat) : Bool := (M.succ.getD a []).contains (r, b)

def interp : Interp (Fin M.n) Nat Nat where
  concept c d := M.lab d.val c = true
  role r a b := M.rel r a.val b.val = true

def litB (lit : RLit) (d : Nat) : Bool :=
  if lit.neg then !M.lab d lit.concept else M.lab d lit.concept

def holdsB (σ : Nat → Fin M.n) : RAtom → Bool
  | .concept lit v => M.litB lit (σ v).val
  | .role r s t => M.rel r (σ s).val (σ t).val
  | .exists_ r fil v =>
      (M.succ.getD (σ v).val []).any (fun p => p.1 == r && decide (p.2 < M.n) && M.litB fil p.2)
  | .eq l r => decide (σ l = σ r)

theorem litB_iff (lit : RLit) (d : Fin M.n) :
    M.litB lit d.val = true ↔ M.interp.satLit lit d := by
  rcases lit with ⟨c, neg⟩
  cases neg <;> simp [litB, interp, Interp.satLit]

theorem holdsB_iff (σ : Nat → Fin M.n) (a : RAtom) :
    M.holdsB σ a = true ↔ M.interp.satAtom σ a := by
  cases a with
  | concept lit v => exact M.litB_iff lit (σ v)
  | role r s t => simp [holdsB, interp, Interp.satAtom]
  | exists_ r fil v =>
      simp only [holdsB, Interp.satAtom, List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
        decide_eq_true_eq]
      constructor
      · rintro ⟨⟨r', t⟩, hmem, ⟨rfl, ht⟩, hlit⟩
        refine ⟨⟨t, ht⟩, ?_, (M.litB_iff fil ⟨t, ht⟩).mp hlit⟩
        simp only [interp, rel]
        exact List.contains_iff_mem.mpr hmem
      · rintro ⟨w, hrel, hlit⟩
        refine ⟨(r, w.val), ?_, ⟨rfl, w.isLt⟩, (M.litB_iff fil w).mpr hlit⟩
        simp only [interp, rel] at hrel
        exact List.contains_iff_mem.mp hrel
  | eq l r => simp [holdsB, Interp.satAtom]

theorem holdsB_congr {σ τ : Nat → Fin M.n} (a : RAtom)
    (h : ∀ w ∈ atomVars a, τ w = σ w) : M.holdsB τ a = M.holdsB σ a := by
  cases a with
  | concept lit v => simp [holdsB, h v (by simp [atomVars])]
  | role r s t => simp [holdsB, h s (by simp [atomVars]), h t (by simp [atomVars])]
  | exists_ r fil v => simp [holdsB, h v (by simp [atomVars])]
  | eq l r => simp [holdsB, h l (by simp [atomVars]), h r (by simp [atomVars])]

/-! ## Candidate values -/

def succTargets (r a : Nat) : List (Fin M.n) :=
  (M.succ.getD a []).filterMap fun p =>
    if p.1 = r then (if h : p.2 < M.n then some ⟨p.2, h⟩ else none) else none

def predSources (r b : Nat) : List (Fin M.n) :=
  (M.pred.getD b []).filterMap fun p =>
    if p.1 = r then (if h : p.2 < M.n then some ⟨p.2, h⟩ else none) else none

/-- Every recorded edge `r(a, b)` is recorded among the predecessors of `b`. -/
def predComplete : Bool :=
  (List.range M.n).all fun a =>
    (M.succ.getD a []).all fun p => !decide (p.2 < M.n) || (M.pred.getD p.2 []).contains (p.1, a)

def extElems (c : Nat) : List (Fin M.n) :=
  (M.ext.getD c []).filterMap fun d => if h : d < M.n then some ⟨d, h⟩ else none

/-- Every element is recorded in the extension of each of its labels. -/
def extComplete : Bool :=
  (List.range M.n).all fun d => (M.labels.getD d []).all fun c => (M.ext.getD c []).contains d

theorem mem_extElems (hec : M.extComplete = true) {c : Nat} {d : Fin M.n}
    (h : M.lab d.val c = true) : d ∈ M.extElems c := by
  simp only [extComplete, List.all_eq_true, List.mem_range] at hec
  have hmem : c ∈ M.labels.getD d.val [] := List.contains_iff_mem.mp h
  have hd := List.contains_iff_mem.mp (hec d.val d.isLt c hmem)
  simp only [extElems, List.mem_filterMap]
  exact ⟨d.val, hd, by simp [d.isLt]⟩

def atomCands (done : List Nat) (σ : Nat → Fin M.n) (v : Nat) : RAtom → Option (List (Fin M.n))
  | .role r s t =>
      if t = v ∧ s ≠ v ∧ s ∈ done then some (M.succTargets r (σ s).val)
      else if s = v ∧ t ≠ v ∧ t ∈ done then some (M.predSources r (σ t).val)
      else none
  | .concept lit w => if w = v ∧ lit.neg = false then some (M.extElems lit.concept) else none
  | _ => none

def cands (cl : RClause) (done : List Nat) (σ : Nat → Fin M.n) (v : Nat) : List (Fin M.n) :=
  match cl.body.findSome? (M.atomCands done σ v) with
  | some l => l
  | none => List.finRange M.n

theorem mem_succTargets {r a : Nat} {b : Fin M.n} (h : M.rel r a b.val = true) :
    b ∈ M.succTargets r a := by
  simp only [succTargets, List.mem_filterMap]
  refine ⟨(r, b.val), List.contains_iff_mem.mp h, ?_⟩
  simp [b.isLt]

theorem mem_predSources (hpc : M.predComplete = true) {r a : Nat} {b : Fin M.n}
    (ha : a < M.n) (h : M.rel r a b.val = true) : ⟨a, ha⟩ ∈ M.predSources r b.val := by
  simp only [predComplete, List.all_eq_true, List.mem_range, Bool.or_eq_true] at hpc
  have hmem : (r, b.val) ∈ M.succ.getD a [] := List.contains_iff_mem.mp h
  have hp := hpc a ha (r, b.val) hmem
  have hpred : (r, a) ∈ M.pred.getD b.val [] := by
    rcases hp with hp | hp
    · simp [b.isLt] at hp
    · exact List.contains_iff_mem.mp hp
  simp only [predSources, List.mem_filterMap]
  exact ⟨(r, a), hpred, by simp [ha]⟩

theorem cands_complete (hpc : M.predComplete = true) (hec : M.extComplete = true) (cl : RClause) (done : List Nat)
    (σ τ : Nat → Fin M.n) (v : Nat) (hagree : ∀ w ∈ done, τ w = σ w)
    (hnot : τ v ∉ M.cands cl done σ v) : ∃ a ∈ cl.body, M.holdsB τ a = false := by
  unfold cands at hnot
  split at hnot
  · rename_i l hfind
    obtain ⟨a, ha, hc⟩ := List.exists_of_findSome?_eq_some hfind
    refine ⟨a, ha, ?_⟩
    cases a with
    | role r s t =>
        simp only [atomCands] at hc
        split at hc
        · rename_i hcond
          obtain ⟨rfl, _, hs⟩ := hcond
          simp only [Option.some.injEq] at hc
          subst hc
          rw [Bool.eq_false_iff]
          intro hrel
          simp only [holdsB] at hrel
          rw [hagree s hs] at hrel
          exact hnot (M.mem_succTargets hrel)
        · split at hc
          · rename_i _ hcond
            obtain ⟨rfl, _, ht⟩ := hcond
            simp only [Option.some.injEq] at hc
            subst hc
            rw [Bool.eq_false_iff]
            intro hrel
            simp only [holdsB] at hrel
            rw [hagree t ht] at hrel
            exact hnot (M.mem_predSources hpc (τ s).isLt hrel)
          · exact absurd hc (by simp)
    | concept lit w =>
        simp only [atomCands] at hc
        split at hc
        · rename_i hcond
          obtain ⟨rfl, hneg⟩ := hcond
          simp only [Option.some.injEq] at hc
          subst hc
          rw [Bool.eq_false_iff]
          intro hlab
          rcases lit with ⟨c, neg⟩
          simp only at hneg
          subst hneg
          simp only [holdsB, litB, Bool.false_eq_true, if_false] at hlab
          exact hnot (M.mem_extElems hec hlab)
        · exact absurd hc (by simp)
    | exists_ => simp [atomCands] at hc
    | eq => simp [atomCands] at hc
  · exact absurd (List.mem_finRange _) hnot

/-! ## Clause evaluation -/

/-- The atom mentions the variable bound last (only such atoms can have become
ready). A pruning filter only: soundness does not depend on it. -/
def _root_.ContextCalculus.RulesRoute.fresh (done : List Nat) (a : RAtom) : Bool :=
  match done with
  | [] => true
  | w :: _ => (atomVars a).contains w

def _root_.ContextCalculus.RulesRoute.ready (done : List Nat) (a : RAtom) : Bool := (atomVars a).all (fun w => decide (w ∈ done))

def upd (σ : Nat → Fin M.n) (v : Nat) (d : Fin M.n) : Nat → Fin M.n :=
  fun w => if w = v then d else σ w

def checkFrom (cl : RClause) : List Nat → List Nat → (Nat → Fin M.n) → Bool
  | [], _, σ => !(cl.body.all (M.holdsB σ)) || cl.head.any (M.holdsB σ)
  | v :: rest, done, σ =>
      if v ∈ done then checkFrom cl rest done σ
      else
        cl.body.any (fun a => fresh done a && ready done a && !M.holdsB σ a) ||
        cl.head.any (fun a => fresh done a && ready done a && M.holdsB σ a) ||
        (M.cands cl done σ v).all (fun d => checkFrom cl rest (v :: done) (M.upd σ v d))

omit M in
theorem ready_agree {n : Nat} {done : List Nat} {a : RAtom} (h : ready done a = true)
    {σ τ : Nat → Fin n} (hagree : ∀ w ∈ done, τ w = σ w) :
    ∀ w ∈ atomVars a, τ w = σ w := by
  intro w hw
  simp only [ready, List.all_eq_true, decide_eq_true_eq] at h
  exact hagree w (h w hw)

theorem checkFrom_sound (hpc : M.predComplete = true) (hec : M.extComplete = true) (cl : RClause) :
    ∀ (todo done : List Nat) (σ : Nat → Fin M.n),
      M.checkFrom cl todo done σ = true →
      (∀ a ∈ cl.body ++ cl.head, ∀ w ∈ atomVars a, w ∈ todo ∨ w ∈ done) →
      ∀ τ : Nat → Fin M.n, (∀ w ∈ done, τ w = σ w) →
        (∀ a ∈ cl.body, M.holdsB τ a = true) → ∃ a ∈ cl.head, M.holdsB τ a = true := by
  intro todo
  induction todo with
  | nil =>
      intro done σ hcheck hcover τ hagree hbody
      have hall : ∀ a ∈ cl.body ++ cl.head, M.holdsB τ a = M.holdsB σ a := by
        intro a ha
        apply M.holdsB_congr a
        intro w hw
        rcases hcover a ha w hw with h | h
        · simp at h
        · exact hagree w h
      simp only [checkFrom, Bool.or_eq_true, Bool.not_eq_true', List.all_eq_false,
        List.any_eq_true] at hcheck
      rcases hcheck with ⟨a, ha, hfalse⟩ | ⟨a, ha, htrue⟩
      · have := hbody a ha
        rw [hall a (List.mem_append_left _ ha)] at this
        simp_all
      · refine ⟨a, ha, ?_⟩
        rw [hall a (List.mem_append_right _ ha)]
        exact htrue
  | cons v rest ih =>
      intro done σ hcheck hcover τ hagree hbody
      simp only [checkFrom] at hcheck
      split at hcheck
      · rename_i hv
        apply ih done σ hcheck _ τ hagree hbody
        intro a ha w hw
        rcases hcover a ha w hw with h | h
        · rcases List.mem_cons.mp h with h | h
          · exact Or.inr (h ▸ hv)
          · exact Or.inl h
        · exact Or.inr h
      · simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, Bool.not_eq_true',
          List.all_eq_true] at hcheck
        rcases hcheck with (⟨a, ha, ⟨_, hready⟩, hfalse⟩ | ⟨a, ha, ⟨_, hready⟩, htrue⟩) | hcands
        · have := hbody a ha
          rw [M.holdsB_congr a (ready_agree hready hagree)] at this
          simp_all
        · exact ⟨a, ha, by rw [M.holdsB_congr a (ready_agree hready hagree)]; exact htrue⟩
        · by_cases hmem : τ v ∈ M.cands cl done σ v
          · apply ih (v :: done) (M.upd σ v (τ v)) (hcands _ hmem) _ τ _ hbody
            · intro a ha w hw
              rcases hcover a ha w hw with h | h
              · rcases List.mem_cons.mp h with h | h
                · exact Or.inr (List.mem_cons.mpr (Or.inl h))
                · exact Or.inl h
              · exact Or.inr (List.mem_cons_of_mem _ h)
            · intro w hw
              simp only [upd]
              split
              · rename_i h; rw [h]
              · rcases List.mem_cons.mp hw with h | h
                · contradiction
                · exact hagree w h
          · obtain ⟨a, ha, hfalse⟩ := M.cands_complete hpc hec cl done σ τ v hagree hmem
            have := hbody a ha
            simp_all

/-- A variable joined by a body role atom to a variable in `done`. -/
def joinedVar? (cl : RClause) (done : List Nat) : Option Nat :=
  cl.body.findSome? fun
    | .role _ s t =>
        if s ∈ done ∧ t ∉ done then some t else if t ∈ done ∧ s ∉ done then some s else none
    | _ => none

/-- Enumeration order: follow body role atoms from bound variables, else take
the next unbound clause variable. Any order is sound (`checkFrom_sound`); this
one keeps joins along role edges. -/
def varOrder (cl : RClause) : Nat → List Nat → List Nat
  | 0, done => done.reverse
  | fuel + 1, done =>
      match joinedVar? cl done with
      | some v => varOrder cl fuel (v :: done)
      | none =>
          match (clauseVars cl).find? (fun v => v ∉ done) with
          | some v => varOrder cl fuel (v :: done)
          | none => done.reverse

def checkClause (cl : RClause) : Bool :=
  if h : 0 < M.n then
    M.checkFrom cl (varOrder cl (clauseVars cl).length [] ++ clauseVars cl) [] (fun _ => ⟨0, h⟩)
  else false

theorem checkClause_sound (hpc : M.predComplete = true) (hec : M.extComplete = true) (cl : RClause)
    (h : M.checkClause cl = true) : M.interp.modelsClause cl := by
  unfold checkClause at h
  split at h
  · intro τ hbody
    obtain ⟨a, ha, hsat⟩ := M.checkFrom_sound hpc hec cl _ [] _ h
      (by
        intro a ha w hw
        left
        apply List.mem_append_right
        rcases List.mem_append.mp ha with ha | ha
        · exact mem_clauseVars_of_body ha hw
        · exact mem_clauseVars_of_head ha hw)
      τ (by simp) (fun a ha => (M.holdsB_iff τ a).mpr (hbody a ha))
    exact ⟨a, ha, (M.holdsB_iff τ a).mp hsat⟩
  · exact absurd h (by simp)

/-! ## The model check -/

def singletonB (c : Nat) : Bool :=
  ((List.finRange M.n).filter (fun d => M.lab d.val c)).length == 1

def check (nominals : List Nat) (ontology : List RClause) : Bool :=
  decide (0 < M.n) && M.predComplete && M.extComplete && nominals.all M.singletonB &&
    ontology.all M.checkClause

theorem singletonB_sound {c : Nat} (h : M.singletonB c = true) :
    ∃ d, ∀ x, M.interp.concept c x ↔ x = d := by
  simp only [singletonB, beq_iff_eq] at h
  obtain ⟨d, hd⟩ := List.length_eq_one_iff.mp h
  refine ⟨d, fun x => ?_⟩
  have hx : x ∈ (List.finRange M.n).filter (fun d => M.lab d.val c) ↔ x = d := by
    rw [hd]; simp
  rw [← hx]
  simp [interp]

theorem check_sound {nominals : List Nat} {ontology : List RClause}
    (h : M.check nominals ontology = true) :
    0 < M.n ∧ ClauseModel M.interp nominals ontology := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hn, hpc⟩, hec⟩, hsing⟩, hcl⟩ := h
  exact ⟨hn, fun c hc => M.singletonB_sound (hsing c hc),
    fun cl hcl' => M.checkClause_sound hpc hec cl (hcl cl hcl')⟩

end FModel

end ContextCalculus.RulesRoute
