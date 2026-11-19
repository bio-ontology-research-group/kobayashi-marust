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

theorem pushAll_sub_snd : ∀ (l : List (PSt m k)) (acc : Std.HashSet (PSt m k) × List (PSt m k))
    (u : PSt m k), u ∈ acc.2 → u ∈ (pushAll l acc).2
  | [], _, _, h => h
  | z :: l, acc, u, h => by
    unfold pushAll
    rw [List.foldl_cons]
    refine pushAll_sub_snd l _ u ?_
    split_ifs
    · exact h
    · exact List.mem_cons_of_mem _ h

theorem pushAll_mem_or : ∀ (l : List (PSt m k)) (acc : Std.HashSet (PSt m k) × List (PSt m k))
    (x : PSt m k), x ∈ (pushAll l acc).1 → x ∈ acc.1 ∨ x ∈ (pushAll l acc).2
  | [], _, _, h => Or.inl h
  | z :: l, acc, x, h => by
    unfold pushAll at h ⊢
    rw [List.foldl_cons] at h ⊢
    split_ifs at h ⊢
    · exact pushAll_mem_or l acc x h
    · rcases pushAll_mem_or l (acc.1.insert z, z :: acc.2) x h with h1 | h2
      · rcases Std.HashSet.mem_insert.1 h1 with hxz | h1
        · rw [← beq_iff_eq.1 hxz]
          exact Or.inr (pushAll_sub_snd l (acc.1.insert z, z :: acc.2) z List.mem_cons_self)
        · exact Or.inl h1
      · exact Or.inr h2

theorem pushAll_mem_fst : ∀ (l : List (PSt m k)) (acc : Std.HashSet (PSt m k) × List (PSt m k))
    (y : PSt m k), y ∈ l → y ∈ (pushAll l acc).1
  | [], _, _, h => by cases h
  | z :: l, acc, y, h => by
    unfold pushAll
    rw [List.foldl_cons]
    rcases List.mem_cons.1 h with rfl | h
    · refine pushAll_mono l _ y ?_
      split_ifs with hc
      · exact Std.HashSet.contains_iff_mem.1 hc
      · exact Std.HashSet.mem_insert_self
    · exact pushAll_mem_fst l _ y h

variable (sc adj) in
theorem bfsP_closed_aux : ∀ (fuel : Nat) (seen : Std.HashSet (PSt m k)) (fr : List (PSt m k)),
    (∀ x ∈ seen, x ∈ fr ∨ ∀ y ∈ pstep sc adj x, y ∈ seen) →
    (bfsP sc adj fuel seen fr).2 = true →
    closedP sc adj (bfsP sc adj fuel seen fr).1 = true
  | 0, seen, fr, hinv, h2 => by
    simp only [bfsP, List.isEmpty_iff] at h2 ⊢
    subst h2
    unfold closedP
    refine List.all_eq_true.2 fun x hx => List.all_eq_true.2 fun y hy => Std.HashSet.contains_iff_mem.2 ?_
    exact (hinv x (Std.HashSet.mem_toList.1 hx)).resolve_left List.not_mem_nil y hy
  | _ + 1, seen, [], hinv, _ => by
    simp only [bfsP]
    unfold closedP
    refine List.all_eq_true.2 fun x hx => List.all_eq_true.2 fun y hy => Std.HashSet.contains_iff_mem.2 ?_
    exact (hinv x (Std.HashSet.mem_toList.1 hx)).resolve_left List.not_mem_nil y hy
  | fuel + 1, seen, z :: rest, hinv, h2 => by
    simp only [bfsP] at h2 ⊢
    refine bfsP_closed_aux fuel _ _ (fun x hx => ?_) h2
    rcases pushAll_mem_or (pstep sc adj z) (seen, rest) x hx with hs | hfr
    · rcases hinv x hs with hzf | hp
      · rcases List.mem_cons.1 hzf with rfl | hr
        · exact Or.inr fun y hy => pushAll_mem_fst (pstep sc adj x) (seen, rest) y hy
        · exact Or.inl (pushAll_sub_snd (pstep sc adj z) (seen, rest) x hr)
      · exact Or.inr fun y hy => pushAll_mono (pstep sc adj z) (seen, rest) y (hp y hy)
    · exact Or.inl hfr

variable (sc adj) in
theorem reachP_eq_bfsP (fuel : Nat) (R : RT m) (x : Fin k) :
    let s0 : PSt m k := (x, [(R, false)])
    reachP sc adj fuel R x = bfsP sc adj fuel (({} : Std.HashSet (PSt m k)).insert s0) [s0] := by
  dsimp only
  unfold reachP
  set s0 : PSt m k := (x, [(R, false)])
  set r := bfsP sc adj fuel (({} : Std.HashSet (PSt m k)).insert s0) [s0]
  refine Prod.ext rfl ?_
  dsimp only
  cases hr : r.2
  · simp
  · rw [Bool.true_and]
    refine bfsP_closed_aux sc adj fuel _ _ (fun u hu => Or.inl ?_) hr
    rcases Std.HashSet.mem_insert.1 hu with h | h
    · rw [← beq_iff_eq.1 h]; exact List.mem_singleton_self _
    · exact absurd h Std.HashSet.not_mem_empty

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

/-- `succOf` avoiding the `Fin k` scan when no accepting state is reached. -/
def succOfF (sc : Stack (Fin m) → List (Option (RT m) × Stack (Fin m)))
    (adj : Fin k → List (Fin k × Finset (RT m))) (fuel : Nat) (R : RT m) (x : Fin k) :
    List (Fin k) × Bool :=
  let s0 : PSt m k := (x, [(R, false)])
  let r := bfsP sc adj fuel (({} : Std.HashSet (PSt m k)).insert s0) [s0]
  (if r.1.toList.any (fun s => s.2.isEmpty) then
    (List.finRange k).filter fun y => r.1.contains (y, [])
   else [], r.2)

@[csimp] theorem succOf_eq_F : @succOf = @succOfF := by
  funext m k sc adj fuel R x
  simp only [succOf, succOfF, ← reachP_eq_bfsP, Prod.mk.injEq, and_true]
  split_ifs with h
  · rfl
  · rw [List.filter_eq_nil_iff]
    intro y _
    rw [Bool.not_eq_true, Bool.eq_false_iff]
    intro hc
    apply h
    exact List.any_eq_true.2 ⟨(y, []), Std.HashSet.mem_toList.2 (Std.HashSet.contains_iff_mem.1 hc), rfl⟩

/-- Integer code of a role term. -/
def rtEnc (R : RT m) : Nat := match R with
  | .pos r => 2 * r.val
  | .inv r => 2 * r.val + 1

/-- Role term from its integer code. -/
def rtDec (m : Nat) (c : Nat) : Option (RT m) :=
  if h : c / 2 < m then
    if c % 2 = 0 then some (.pos ⟨c / 2, h⟩) else some (.inv ⟨c / 2, h⟩)
  else none

theorem rtDec_rtEnc (R : RT m) : rtDec m (rtEnc R) = some R := by
  cases R with
  | pos r =>
    unfold rtEnc rtDec
    have h1 : 2 * r.val / 2 = r.val := Nat.mul_div_right r.val (by decide)
    have h2 : 2 * r.val % 2 = 0 := Nat.mul_mod_right 2 r.val
    simp [h1, h2, r.isLt]
  | inv r =>
    unfold rtEnc rtDec
    have h1 : (2 * r.val + 1) / 2 = r.val := by omega
    have h2 : (2 * r.val + 1) % 2 = 1 := by omega
    simp [h1, h2, r.isLt]

theorem rtEnc_of_rtDec {c : Nat} {R : RT m} (h : rtDec m c = some R) : rtEnc R = c := by
  unfold rtDec at h
  split_ifs at h with h1 h2
  · cases h; unfold rtEnc; dsimp only; omega
  · cases h; unfold rtEnc; dsimp only; omega

/-- The members of a role-term finite set as a duplicate-free list. -/
def toLRT (L : Finset (RT m)) : List (RT m) :=
  ((L.image rtEnc).sort (· ≤ ·)).filterMap (rtDec m)

theorem mem_toLRT (L : Finset (RT m)) (R : RT m) : R ∈ toLRT L ↔ R ∈ L := by
  unfold toLRT
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨c, hc, hdec⟩
    rw [Finset.mem_sort, Finset.mem_image] at hc
    obtain ⟨S, hS, hSc⟩ := hc
    rw [← hSc, rtDec_rtEnc] at hdec
    cases hdec
    exact hS
  · intro hR
    refine ⟨rtEnc R, ?_, rtDec_rtEnc R⟩
    rw [Finset.mem_sort, Finset.mem_image]
    exact ⟨R, hR, rfl⟩

theorem nodup_toLRT (L : Finset (RT m)) : (toLRT L).Nodup := by
  unfold toLRT
  refine (Finset.sort_nodup (L.image rtEnc) (· ≤ ·)).filterMap ?_
  intro a b R ha hb
  rw [← rtEnc_of_rtDec ha, ← rtEnc_of_rtDec hb]

/-- The `R`-targets of `x` in `adj`. -/
def byRole (adj : Fin k → List (Fin k × Finset (RT m))) (x : Fin k) (R : RT m) : List (Fin k) :=
  (adj x).filterMap fun e => if R ∈ e.2 then some e.1 else none

/-- Insert target `y` under each role in `l`. -/
def insAdjEdge (y : Fin k) (mp : Std.HashMap (RT m) (List (Fin k))) (l : List (RT m)) :
    Std.HashMap (RT m) (List (Fin k)) :=
  l.foldl (fun mp R => mp.insert R (y :: mp.getD R [])) mp

theorem insAdjEdge_getD (y : Fin k) (R : RT m) :
    ∀ (l : List (RT m)) (_ : l.Nodup) (mp : Std.HashMap (RT m) (List (Fin k))),
      (insAdjEdge y mp l).getD R [] = if R ∈ l then y :: mp.getD R [] else mp.getD R []
  | [], _, mp => by simp [insAdjEdge]
  | S :: l, hl, mp => by
    obtain ⟨hS, hnd⟩ := List.nodup_cons.1 hl
    rw [insAdjEdge, List.foldl_cons, ← insAdjEdge, insAdjEdge_getD y R l hnd]
    by_cases hRS : R = S
    · subst hRS
      simp [hS]
    · have hne : (S == R) = false := beq_false_of_ne (Ne.symm hRS)
      simp [hRS, Std.HashMap.getD_insert, hne]

/-- The outgoing edges of a node indexed by role term. -/
def adjMapOf (es : List (Fin k × Finset (RT m))) : Std.HashMap (RT m) (List (Fin k)) :=
  es.reverse.foldl (fun mp e => insAdjEdge e.1 mp (toLRT e.2)) ∅

theorem foldr_insAdjEdge_getD (R : RT m) :
    ∀ (es : List (Fin k × Finset (RT m))),
      (es.foldr (fun e mp => insAdjEdge e.1 mp (toLRT e.2)) ∅).getD R [] =
        es.filterMap fun e => if R ∈ e.2 then some e.1 else none
  | [] => by simp
  | e :: es => by
    rw [List.foldr_cons, insAdjEdge_getD e.1 R (toLRT e.2) (nodup_toLRT e.2),
      foldr_insAdjEdge_getD R es, List.filterMap_cons]
    by_cases h : R ∈ e.2
    · have h' : R ∈ toLRT e.2 := (mem_toLRT e.2 R).2 h
      simp [h, h']
    · have h' : R ∉ toLRT e.2 := fun hc => h ((mem_toLRT e.2 R).1 hc)
      simp [h, h']

theorem adjMapOf_getD (es : List (Fin k × Finset (RT m))) (R : RT m) :
    (adjMapOf es).getD R [] = es.filterMap fun e => if R ∈ e.2 then some e.1 else none := by
  unfold adjMapOf
  rw [← List.foldr_eq_foldl_reverse]
  exact foldr_insAdjEdge_getD R es

/-- Wrapper so the per-node role map array is computed once per graph. -/
structure ByRoleS (m k : Nat) where
  f : Fin k → RT m → List (Fin k)

def byRoleS (adj : Fin k → List (Fin k × Finset (RT m))) : ByRoleS m k :=
  ⟨byRole adj⟩

/-- `byRoleS` backed by a precomputed per-node hash map array. -/
@[noinline] def byRoleFS (adj : Fin k → List (Fin k × Finset (RT m))) : ByRoleS m k :=
  let arr : Array (Std.HashMap (RT m) (List (Fin k))) := Array.ofFn fun x => adjMapOf (adj x)
  ⟨fun x R => match arr[x.val]? with
    | some mp => mp.getD R []
    | none => byRole adj x R⟩

@[csimp] theorem byRoleS_eq_F : @byRoleS = @byRoleFS := by
  funext m k adj
  simp only [byRoleS, byRoleFS, ByRoleS.mk.injEq]
  funext x R
  unfold byRole
  rw [Array.getElem?_ofFn]
  simp [x.isLt, adjMapOf_getD]

/-- The successors of a product state using role-indexed adjacency `br`. -/
def pstepR (sc : Stack (Fin m) → List (Option (RT m) × Stack (Fin m)))
    (br : Fin k → RT m → List (Fin k)) (s : PSt m k) : List (PSt m k) :=
  (sc s.2).flatMap fun p => match p.1 with
    | none => [(s.1, p.2)]
    | some R => (br s.1 R).map fun y => (y, p.2)

variable (sc adj) in
theorem pstepR_byRole (s : PSt m k) : pstepR sc (byRole adj) s = pstep sc adj s := by
  unfold pstepR pstep byRole
  congr 1
  funext p
  cases p.1 with
  | none => rfl
  | some R =>
    dsimp only
    rw [List.map_filterMap]
    congr 1
    funext e
    split_ifs <;> rfl

/-- Depth-first listing over role-indexed adjacency `br`. -/
def bfsPR (sc : Stack (Fin m) → List (Option (RT m) × Stack (Fin m)))
    (br : Fin k → RT m → List (Fin k)) :
    Nat → Std.HashSet (PSt m k) → List (PSt m k) → Std.HashSet (PSt m k) × Bool
  | 0, seen, fr => (seen, fr.isEmpty)
  | _ + 1, seen, [] => (seen, true)
  | fuel + 1, seen, x :: rest =>
    let a := pushAll (pstepR sc br x) (seen, rest)
    bfsPR sc br fuel a.1 a.2

variable (sc adj) in
theorem bfsPR_byRole : ∀ (fuel : Nat) (seen : Std.HashSet (PSt m k)) (fr : List (PSt m k)),
    bfsPR sc (byRole adj) fuel seen fr = bfsP sc adj fuel seen fr
  | 0, _, _ => rfl
  | _ + 1, _, [] => rfl
  | fuel + 1, seen, x :: rest => by
    simp only [bfsPR, bfsP, pstepR_byRole, bfsPR_byRole fuel]

/-- `succOf` over a precomputed role-indexed adjacency function `br`. -/
def succOfR (sc : Stack (Fin m) → List (Option (RT m) × Stack (Fin m)))
    (br : Fin k → RT m → List (Fin k)) (fuel : Nat) (R : RT m) (x : Fin k) :
    List (Fin k) × Bool :=
  let s0 : PSt m k := (x, [(R, false)])
  let r := bfsPR sc br fuel (({} : Std.HashSet (PSt m k)).insert s0) [s0]
  (if r.1.toList.any (fun s => s.2.isEmpty) then
    (List.finRange k).filter fun y => r.1.contains (y, [])
   else [], r.2)

variable (sc adj) in
theorem succOfR_byRole (fuel : Nat) (R : RT m) (x : Fin k) :
    succOfR sc (byRole adj) fuel R x = succOf sc adj fuel R x := by
  rw [succOf_eq_F]
  unfold succOfR succOfF
  dsimp only
  rw [bfsPR_byRole]

end Proofs

end ContextCalculus.SROIQ.Proc

#print axioms ContextCalculus.SROIQ.Proc.succOf_sound
#print axioms ContextCalculus.SROIQ.Proc.succOf_complete
#print axioms ContextCalculus.SROIQ.Proc.succOf_eq_F
