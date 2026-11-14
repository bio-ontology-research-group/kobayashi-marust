import ContextCalculus.SROIQ.Automaton

/-!
# The automaton of a role, computed (stage C3, design section 3.3)

Over `Fin m` roles: the successors of a stack (`succs`, exact for `Move`
by `mem_succs`), a breadth-first listing of stacks (`reachL`), the closure
check (`closedB`) and `run_mem`: in a closed list, every run from a listed
stack stays in the list.
-/

namespace ContextCalculus.SROIQ.Proc

open ContextCalculus.SRI (RoleT)
open ContextCalculus.SRIQ (Clause Ontology RoleLe)
open ContextCalculus.SROIQ (Item Stack ini shapeOf Shape Move Run Acc Eqv rules)

variable {n m : Nat}

/-- Every role term. -/
def allRT (m : Nat) : List (RT m) := (List.finRange m).flatMap fun r => [.pos r, .inv r]

theorem mem_allRT (R : RT m) : R ∈ allRT m := by
  cases R <;> simp [allRT]

section Defs

variable (O : Ontology (Fin n) (Fin m))

def eqvB (T S : RT m) : Bool := leB O T S && leB O S T

/-- The moves from an initial item. -/
def succsI (S : RT m) (rest : Stack (Fin m)) : List (Option (RT m) × Stack (Fin m)) :=
  (allRT m).filterMap (fun R => if leB O R S then some (some R, (S, true) :: rest) else none) ++
  (rules O).filterMap (fun p => if leB O p.1 S && !leB O S p.1 then
      some (none, (p.1, false) :: (S, true) :: rest) else none) ++
  (rules O).filterMap (fun p => match shapeOf p.1 p.2 with
    | .refl => if leB O p.1 S then some (none, (S, true) :: rest) else none
    | .ord => if eqvB O p.1 S then some (none, ini p.2 ++ (S, true) :: rest) else none
    | .right => if eqvB O p.1 S then some (none, ini p.2.dropLast ++ (S, false) :: rest) else none
    | _ => none)

/-- The moves from a final item. -/
def succsF (S : RT m) (rest : Stack (Fin m)) : List (Option (RT m) × Stack (Fin m)) :=
  (none, rest) ::
  (rules O).filterMap (fun p => match shapeOf p.1 p.2 with
    | .left => if eqvB O p.1 S then some (none, ini p.2.tail ++ (S, true) :: rest) else none
    | .trans => if eqvB O p.1 S then some (none, (S, false) :: rest) else none
    | _ => none)

/-- The moves of a stack. -/
def succs : Stack (Fin m) → List (Option (RT m) × Stack (Fin m))
  | [] => []
  | (S, false) :: rest => succsI O S rest
  | (S, true) :: rest => succsF O S rest

end Defs

variable {O : Ontology (Fin n) (Fin m)}

theorem eqvB_iff {T S : RT m} : eqvB O T S = true ↔ Eqv O T S := by
  simp [eqvB, Eqv, leB_iff]

/-- **The successors are the moves.** -/
theorem mem_succs {st st' : Stack (Fin m)} {l : Option (RT m)} :
    (l, st') ∈ succs O st ↔ Move O st l st' := by
  constructor
  · intro h
    match st, h with
    | (S, false) :: rest, h =>
      simp only [succs, succsI, List.mem_append, List.mem_filterMap] at h
      rcases h with (⟨R, -, hR⟩ | ⟨⟨T, B⟩, hr, hT⟩) | ⟨⟨T, B⟩, hr, hT⟩
      · split_ifs at hR with hle
        simp only [Option.some.injEq, Prod.mk.injEq] at hR
        obtain ⟨rfl, rfl⟩ := hR
        exact .letter (leB_iff.1 hle)
      · split_ifs at hT with hle
        simp only [Option.some.injEq, Prod.mk.injEq] at hT
        obtain ⟨rfl, rfl⟩ := hT
        simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hle
        exact .call hr (leB_iff.1 hle.1) (fun h' => by rw [leB_iff.2 h'] at hle; simp at hle)
      · dsimp only at hT
        split at hT <;> first | cases hT | skip
        all_goals split_ifs at hT with hle
        all_goals simp only [Option.some.injEq, Prod.mk.injEq] at hT
        all_goals obtain ⟨rfl, rfl⟩ := hT
        · exact .refl hr ‹_› (leB_iff.1 hle)
        · exact .ord hr ‹_› (eqvB_iff.1 hle)
        · exact .right hr ‹_› (eqvB_iff.1 hle)
    | (S, true) :: rest, h =>
      simp only [succs, succsF, List.mem_cons, List.mem_filterMap, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨⟨T, B⟩, hr, hT⟩
      · exact .pop
      · dsimp only at hT
        split at hT <;> first | cases hT | skip
        all_goals split_ifs at hT with hle
        all_goals simp only [Option.some.injEq, Prod.mk.injEq] at hT
        all_goals obtain ⟨rfl, rfl⟩ := hT
        · exact .left hr ‹_› (eqvB_iff.1 hle)
        · exact .trans hr ‹_› (eqvB_iff.1 hle)
  · intro h
    cases h with
    | @letter R S rest hle =>
      simp only [succs, succsI, List.mem_append, List.mem_filterMap]
      exact Or.inl (Or.inl ⟨R, mem_allRT R, by simp [leB_iff.2 hle]⟩)
    | @call R S B rest hr hle hn =>
      simp only [succs, succsI, List.mem_append, List.mem_filterMap]
      refine Or.inl (Or.inr ⟨(R, B), hr, ?_⟩)
      have : leB O S R = false := by
        cases h' : leB O S R
        · rfl
        · exact absurd (leB_iff.1 h') hn
      simp [leB_iff.2 hle, this]
    | @refl T S B rest hr hs hle =>
      simp only [succs, succsI, List.mem_append, List.mem_filterMap]
      exact Or.inr ⟨(T, B), hr, by simp [hs, leB_iff.2 hle]⟩
    | @ord T S B rest hr hs he =>
      simp only [succs, succsI, List.mem_append, List.mem_filterMap]
      exact Or.inr ⟨(T, B), hr, by simp [hs, eqvB_iff.2 he]⟩
    | @right T S B rest hr hs he =>
      simp only [succs, succsI, List.mem_append, List.mem_filterMap]
      exact Or.inr ⟨(T, B), hr, by simp [hs, eqvB_iff.2 he]⟩
    | @left T S B rest hr hs he =>
      simp only [succs, succsF, List.mem_cons, List.mem_filterMap]
      exact Or.inr ⟨(T, B), hr, by simp [hs, eqvB_iff.2 he]⟩
    | @trans T S B rest hr hs he =>
      simp only [succs, succsF, List.mem_cons, List.mem_filterMap]
      exact Or.inr ⟨(T, B), hr, by simp [hs, eqvB_iff.2 he]⟩
    | pop => simp [succs, succsF]

/-! ## Listing and closure -/

section Listing

variable (O)

/-- One round of the listing. -/
def expandL (L : List (Stack (Fin m))) : List (Stack (Fin m)) :=
  (L ++ L.flatMap fun st => (succs O st).map Prod.snd).dedup

/-- The listing: at most `fuel` rounds, stopping when a round adds nothing
or the list exceeds `cap` stacks. -/
def reachIt (cap : Nat) : Nat → List (Stack (Fin m)) → List (Stack (Fin m))
  | 0, L => L
  | k + 1, L =>
    if cap < L.length then L
    else
      let L' := expandL O L
      if L'.length = L.length then L else reachIt cap k L'

/-- The listed stacks of the automaton of `S`. -/
def reachL (S : RT m) : List (Stack (Fin m)) := reachIt O 4096 64 [[(S, false)]]

/-- Every successor of a listed stack is listed. -/
def closedB (L : List (Stack (Fin m))) : Bool :=
  L.all fun st => (succs O st).all fun p => decide (p.2 ∈ L)

end Listing

theorem mem_expandL {L : List (Stack (Fin m))} {st : Stack (Fin m)} (h : st ∈ L) :
    st ∈ expandL O L := by
  unfold expandL; rw [List.mem_dedup]; exact List.mem_append_left _ h

theorem mem_reachIt {cap : Nat} : ∀ (k : Nat) {L : List (Stack (Fin m))} {st : Stack (Fin m)},
    st ∈ L → st ∈ reachIt O cap k L
  | 0, _, _, h => h
  | k + 1, L, st, h => by
    unfold reachIt
    dsimp only
    split_ifs
    · exact h
    · exact h
    · exact mem_reachIt k (mem_expandL h)

theorem init_mem_reachL (S : RT m) : [(S, false)] ∈ reachL O S :=
  mem_reachIt _ (List.mem_singleton_self _)

theorem closedB_move {L : List (Stack (Fin m))} (h : closedB O L = true) {st st' : Stack (Fin m)}
    {l : Option (RT m)} (hst : st ∈ L) (hm : Move O st l st') : st' ∈ L := by
  unfold closedB at h
  rw [List.all_eq_true] at h
  have := List.all_eq_true.1 (h st hst) (l, st') (mem_succs.2 hm)
  exact of_decide_eq_true this

/-- **Runs stay in a closed list.** -/
theorem run_mem {L : List (Stack (Fin m))} (h : closedB O L = true) {st st' : Stack (Fin m)}
    {w : List (RT m)} (hst : st ∈ L) (hr : Run O st w st') : st' ∈ L := by
  induction hr with
  | nil => exact hst
  | eps hm _ ih => exact ih (closedB_move h hst hm)
  | read hm _ ih => exact ih (closedB_move h hst hm)

end ContextCalculus.SROIQ.Proc

#print axioms ContextCalculus.SROIQ.Proc.mem_succs
#print axioms ContextCalculus.SROIQ.Proc.run_mem
