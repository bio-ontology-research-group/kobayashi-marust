import ContextCalculus.SROIQ.ChainFast

/-!
# The automaton of a role over a finite graph (stage H4, item 1)

`docs/V1.7.0-C5-HINT-ROUTE.md`, section 12. A role `R` holds between two
elements of a model of the chain route when some path between them spells
a word of `R`'s language (`Gen`, `downC_rt`). Over the core of a hint the
paths are the paths of the label graph (`LPath`). The product of the label
graph with the role's automaton (`Move`, `acc_iff_gen`) decides it: the
states are pairs of a core element and a stack, a silent move keeps the
element, a letter move `R` goes along an edge whose label holds `R`.

* `bfsP`: a depth-first listing of the product states reachable from a
  start state (fuel-bounded; the flag says whether the frontier emptied).
* `closedP`: every successor of a listed state is listed.
* `succOf sc adj fuel R x`: the core elements `y` whose state `(y, [])` is
  listed from `(x, [(R, false)])`, and a flag (`true` when the listing
  finished and is closed).
* `succOf_sound`: every listed `y` is reached along a word of `R`.
* `succOf_complete`: with the flag, every `y` reached along a word of `R`
  is listed.

The theorems hold for any successor function `sc` exact for `Move` and any
adjacency `adj` exact for the labels.
-/

namespace ContextCalculus.SROIQ.Proc

open ContextCalculus.SRI (RoleT)
open ContextCalculus.SRIQ (Ontology)
open ContextCalculus.SROIQ (Item Stack Move Run Acc Gen acc_iff_gen rules)

variable {n m k : Nat}

/-- Paths in the label graph of a core. -/
def LPath (lab : Fin k → Fin k → Finset (RT m)) : List (RT m) → Fin k → Fin k → Prop
  | [], x, y => x = y
  | R :: w, x, y => ∃ z, R ∈ lab x z ∧ LPath lab w z y

theorem lpath_append_single (lab : Fin k → Fin k → Finset (RT m)) :
    ∀ (w : List (RT m)) (R : RT m) (x z : Fin k),
      LPath lab (w ++ [R]) x z ↔ ∃ y, LPath lab w x y ∧ R ∈ lab y z
  | [], R, x, z => by
    simp only [List.nil_append, LPath]
    constructor
    · rintro ⟨u, hu, rfl⟩; exact ⟨x, rfl, hu⟩
    · rintro ⟨y, rfl, hR⟩; exact ⟨z, hR, rfl⟩
  | S :: w, R, x, z => by
    simp only [List.cons_append, LPath]
    constructor
    · rintro ⟨u, hu, hp⟩
      obtain ⟨y, hy, hR⟩ := (lpath_append_single lab w R u z).1 hp
      exact ⟨y, ⟨u, hu, hy⟩, hR⟩
    · rintro ⟨y, ⟨u, hu, hy⟩, hR⟩
      exact ⟨u, hu, (lpath_append_single lab w R u z).2 ⟨y, hy, hR⟩⟩

/-- A state of the product: a core element and a stack. -/
abbrev PSt (m k : Nat) := Fin k × Stack (Fin m)

section Step

variable (sc : Stack (Fin m) → List (Option (RT m) × Stack (Fin m)))
  (adj : Fin k → List (Fin k × Finset (RT m)))

/-- The successors of a product state. -/
def pstep (s : PSt m k) : List (PSt m k) :=
  (sc s.2).flatMap fun p => match p.1 with
    | none => [(s.1, p.2)]
    | some R => (adj s.1).filterMap fun e => if R ∈ e.2 then some (e.1, p.2) else none

/-- Add the unseen states of a list to the seen set and the frontier. -/
def pushAll (l : List (PSt m k)) (acc : Std.HashSet (PSt m k) × List (PSt m k)) :
    Std.HashSet (PSt m k) × List (PSt m k) :=
  l.foldl (fun a y => if a.1.contains y then a else (a.1.insert y, y :: a.2)) acc

/-- The listing: the seen states and whether the frontier emptied. -/
def bfsP : Nat → Std.HashSet (PSt m k) → List (PSt m k) → Std.HashSet (PSt m k) × Bool
  | 0, seen, fr => (seen, fr.isEmpty)
  | _ + 1, seen, [] => (seen, true)
  | fuel + 1, seen, x :: rest =>
    let a := pushAll (pstep sc adj x) (seen, rest)
    bfsP fuel a.1 a.2

/-- Every successor of a listed state is listed. -/
def closedP (S : Std.HashSet (PSt m k)) : Bool :=
  S.toList.all fun x => (pstep sc adj x).all fun y => S.contains y

/-- The listing from the start state of `R` at `x`, with its flag. -/
def reachP (fuel : Nat) (R : RT m) (x : Fin k) : Std.HashSet (PSt m k) × Bool :=
  let s0 : PSt m k := (x, [(R, false)])
  let r := bfsP sc adj fuel (({} : Std.HashSet (PSt m k)).insert s0) [s0]
  (r.1, r.2 && closedP sc adj r.1)

/-- **The `R`-successors of `x` in the core**, and whether the list is
exact. -/
def succOf (fuel : Nat) (R : RT m) (x : Fin k) : List (Fin k) × Bool :=
  let r := reachP sc adj fuel R x
  ((List.finRange k).filter fun y => r.1.contains (y, []), r.2)

end Step

section Proofs

variable {O : Ontology (Fin n) (Fin m)} {sc : Stack (Fin m) → List (Option (RT m) × Stack (Fin m))}
  {adj : Fin k → List (Fin k × Finset (RT m))} {lab : Fin k → Fin k → Finset (RT m)}

/-- A product state reached from `s0`. -/
def Good (O : Ontology (Fin n) (Fin m)) (lab : Fin k → Fin k → Finset (RT m)) (s0 s : PSt m k) :
    Prop :=
  ∃ w, Run O s0.2 w s.2 ∧ LPath lab w s0.1 s.1

theorem good_start (s0 : PSt m k) : Good O lab s0 s0 := ⟨[], .nil, rfl⟩

theorem pstep_good (hsc : ∀ st l st', (l, st') ∈ sc st → Move O st l st')
    (hadj : ∀ x e, e ∈ adj x → ∀ R ∈ e.2, R ∈ lab x e.1) {s0 x y : PSt m k}
    (hx : Good O lab s0 x) (hy : y ∈ pstep sc adj x) : Good O lab s0 y := by
  obtain ⟨w, hr, hp⟩ := hx
  obtain ⟨⟨l, st'⟩, hl, hy⟩ := List.mem_flatMap.1 hy
  have hm := hsc _ _ _ hl
  cases l with
  | none =>
    simp only [List.mem_singleton] at hy
    subst hy
    refine ⟨w, ?_, hp⟩
    simpa using hr.append (Run.single_eps hm)
  | some R =>
    obtain ⟨e, he, hy⟩ := List.mem_filterMap.1 hy
    split_ifs at hy with hR
    cases hy
    refine ⟨w ++ [R], hr.append (.read hm .nil), ?_⟩
    exact (lpath_append_single lab w R s0.1 e.1).2 ⟨x.1, hp, hadj _ _ he R hR⟩

theorem pushAll_good {P : PSt m k → Prop} :
    ∀ (l : List (PSt m k)) (acc : Std.HashSet (PSt m k) × List (PSt m k)),
      (∀ y ∈ l, P y) → (∀ y ∈ acc.1, P y) → (∀ y ∈ acc.2, P y) →
      (∀ y ∈ (pushAll l acc).1, P y) ∧ ∀ y ∈ (pushAll l acc).2, P y
  | [], acc, _, h1, h2 => ⟨h1, h2⟩
  | z :: l, acc, hl, h1, h2 => by
    unfold pushAll
    rw [List.foldl_cons]
    refine pushAll_good l _ (fun y hy => hl y (List.mem_cons_of_mem _ hy)) ?_ ?_
    · split_ifs
      · exact h1
      · intro y hy
        rcases Std.HashSet.mem_insert.1 hy with h | h
        · rw [← beq_iff_eq.1 h]; exact hl z List.mem_cons_self
        · exact h1 y h
    · split_ifs
      · exact h2
      · intro y hy
        rcases List.mem_cons.1 hy with rfl | h
        · exact hl y List.mem_cons_self
        · exact h2 y h

theorem bfsP_good (hsc : ∀ st l st', (l, st') ∈ sc st → Move O st l st')
    (hadj : ∀ x e, e ∈ adj x → ∀ R ∈ e.2, R ∈ lab x e.1) (s0 : PSt m k) :
    ∀ (fuel : Nat) (seen : Std.HashSet (PSt m k)) (fr : List (PSt m k)),
      (∀ y ∈ seen, Good O lab s0 y) → (∀ y ∈ fr, Good O lab s0 y) →
      ∀ y ∈ (bfsP sc adj fuel seen fr).1, Good O lab s0 y
  | 0, seen, fr, h1, _ => h1
  | _ + 1, seen, [], h1, _ => h1
  | fuel + 1, seen, x :: rest, h1, h2 => by
    simp only [bfsP]
    have hx := h2 x List.mem_cons_self
    obtain ⟨g1, g2⟩ := pushAll_good (P := Good O lab s0) (pstep sc adj x) (seen, rest)
      (fun y hy => pstep_good hsc hadj hx hy) h1 (fun y hy => h2 y (List.mem_cons_of_mem _ hy))
    exact bfsP_good hsc hadj s0 fuel _ _ g1 g2

theorem closedP_mem {S : Std.HashSet (PSt m k)} (h : closedP sc adj S = true) {x y : PSt m k}
    (hx : x ∈ S) (hy : y ∈ pstep sc adj x) : y ∈ S := by
  unfold closedP at h
  have := List.all_eq_true.1 (List.all_eq_true.1 h x (Std.HashSet.mem_toList.2 hx)) y hy
  exact Std.HashSet.contains_iff_mem.1 this

theorem closedP_run (hsc : ∀ st l st', Move O st l st' → (l, st') ∈ sc st)
    (hadj : ∀ x z R, R ∈ lab x z → ∃ e ∈ adj x, e.1 = z ∧ R ∈ e.2)
    {S : Std.HashSet (PSt m k)} (h : closedP sc adj S = true) {st st' : Stack (Fin m)}
    {w : List (RT m)} (hr : Run O st w st') : ∀ x y, (x, st) ∈ S → LPath lab w x y → (y, st') ∈ S := by
  induction hr with
  | nil =>
    intro x y hx hp
    cases hp; exact hx
  | @eps st1 st2 st3 w hm _ ih =>
    intro x y hx hp
    refine ih x y (closedP_mem h hx ?_) hp
    exact List.mem_flatMap.2 ⟨(none, st2), hsc _ _ _ hm, List.mem_singleton_self _⟩
  | @read st1 st2 st3 R w hm _ ih =>
    intro x y hx hp
    obtain ⟨z, hz, hp⟩ := hp
    obtain ⟨e, he, rfl, hR⟩ := hadj _ _ _ hz
    refine ih e.1 y (closedP_mem h hx ?_) hp
    refine List.mem_flatMap.2 ⟨(some R, st2), hsc _ _ _ hm, ?_⟩
    exact List.mem_filterMap.2 ⟨e, he, by simp [hR]⟩

/-- **Soundness of the listing**: a listed `y` is reached from `x` along a
word of `R`. -/
theorem succOf_sound (hsc : ∀ st l st', (l, st') ∈ sc st → Move O st l st')
    (hadj : ∀ x e, e ∈ adj x → ∀ R ∈ e.2, R ∈ lab x e.1) {fuel : Nat} {R : RT m} {x y : Fin k}
    (hy : y ∈ (succOf sc adj fuel R x).1) : ∃ w, Gen O w R ∧ LPath lab w x y := by
  simp only [succOf, reachP, List.mem_filter] at hy
  have hm := Std.HashSet.contains_iff_mem.1 hy.2
  have := bfsP_good hsc hadj (x, [(R, false)]) fuel _ _ (fun z hz => by
    rcases Std.HashSet.mem_insert.1 hz with h | h
    · rw [← beq_iff_eq.1 h]; exact good_start _
    · exact absurd h (Std.HashSet.not_mem_empty))
    (fun z hz => by rw [List.mem_singleton.1 hz]; exact good_start _) _ hm
  obtain ⟨w, hr, hp⟩ := this
  exact ⟨w, acc_iff_gen.1 hr, hp⟩


theorem pushAll_mono : ∀ (l : List (PSt m k)) (acc : Std.HashSet (PSt m k) × List (PSt m k))
    (y : PSt m k), y ∈ acc.1 → y ∈ (pushAll l acc).1
  | [], _, _, h => h
  | z :: l, acc, y, h => by
    unfold pushAll
    rw [List.foldl_cons]
    refine pushAll_mono l _ y ?_
    split_ifs
    · exact h
    · exact Std.HashSet.mem_insert.2 (Or.inr h)

variable (sc adj) in
theorem bfsP_mem_start : ∀ (fuel : Nat) (seen : Std.HashSet (PSt m k)) (fr : List (PSt m k))
    (y : PSt m k), y ∈ seen → y ∈ (bfsP sc adj fuel seen fr).1
  | 0, _, _, _, h => h
  | _ + 1, _, [], _, h => h
  | fuel + 1, seen, x :: rest, y, h => by
    simp only [bfsP]
    exact bfsP_mem_start fuel _ _ y (pushAll_mono _ (seen, rest) y h)

/-- **Completeness of the listing**: when the flag is set, every `y`
reached from `x` along a word of `R` is listed. -/
theorem succOf_complete (hsc : ∀ st l st', Move O st l st' → (l, st') ∈ sc st)
    (hadj : ∀ x z R, R ∈ lab x z → ∃ e ∈ adj x, e.1 = z ∧ R ∈ e.2) {fuel : Nat} {R : RT m}
    {x y : Fin k} (hf : (succOf sc adj fuel R x).2 = true) {w : List (RT m)} (hg : Gen O w R)
    (hp : LPath lab w x y) : y ∈ (succOf sc adj fuel R x).1 := by
  simp only [succOf, reachP, Bool.and_eq_true] at hf ⊢
  obtain ⟨-, hc⟩ := hf
  refine List.mem_filter.2 ⟨List.mem_finRange _, Std.HashSet.contains_iff_mem.2 ?_⟩
  have hst := bfsP_mem_start sc adj fuel (({} : Std.HashSet (PSt m k)).insert (x, [(R, false)]))
    [(x, [(R, false)])] (x, [(R, false)]) (Std.HashSet.mem_insert_self)
  exact closedP_run hsc hadj hc (acc_iff_gen.2 hg) x y hst hp

end Proofs

end ContextCalculus.SROIQ.Proc

#print axioms ContextCalculus.SROIQ.Proc.succOf_sound
#print axioms ContextCalculus.SROIQ.Proc.succOf_complete
