import ContextCalculus.SROIQ.ChainFast
import ContextCalculus.SRIQN.Procedure

/-!
# A fast decision of the C2a condition (stage C3, check speed)

`SRIQN.Proc` decides `IsC2a` by recomputing the nominal-only test (a pass
over the ontology) for every lower clause and the super-roles (a fixpoint
over the ontology) for every pair of a lower and an at-most clause.
`c2aB` computes the names with a bad positive occurrence once (`badPos`),
the super-role table once (`mkTab`, from the chain clauses only), and is
equal to the condition (`c2aB_iff`). `fastDecC2a` is the decision
instance the C3 route uses.
-/

namespace ContextCalculus.SROIQ.Proc

open ContextCalculus.SRI (RoleT)
open ContextCalculus.SRIQ (Clause lowerL upperL RoleLe)
open ContextCalculus.SRIQN (basePart noms NomOnly PosOK IsC2a)

variable {n m : Nat}

/-- The names whose positive occurrence in `cl` is not an exempt
`[a] ⊑ [X]` with `a` a nominal name. -/
def badPos (N : List (Fin n)) : Clause (Fin n) (Fin m) → List (Fin n)
  | .gci body head =>
    match body, head with
    | [a], [_] => if a ∈ N then [] else head
    | _, _ => head
  | .exRight _ _ b | .allRight _ _ b | .atLeast _ _ _ b => [b]
  | _ => []

theorem posOK_iff (N : List (Fin n)) (X : Fin n) (cl : Clause (Fin n) (Fin m)) :
    PosOK N X cl ↔ X ∉ badPos N cl := by
  cases cl with
  | gci body head =>
    simp only [PosOK]
    match body, head with
    | [a], [Y] =>
      simp only [badPos]
      split_ifs with ha
      · simp only [List.not_mem_nil, not_false_eq_true, iff_true]
        intro hX
        rw [List.mem_singleton] at hX
        subst hX
        exact ⟨a, ha, rfl, rfl⟩
      · constructor
        · rintro h hX
          obtain ⟨a', ha', h1, -⟩ := h hX
          simp only [List.cons.injEq, and_true] at h1
          exact ha (h1 ▸ ha')
        · intro h hX; exact absurd hX h
    | [], head =>
      simp only [badPos]
      constructor
      · rintro h hX; obtain ⟨a, -, h1, -⟩ := h hX; simp at h1
      · intro h hX; exact absurd hX h
    | a :: b :: body, head =>
      simp only [badPos]
      constructor
      · rintro h hX; obtain ⟨a', -, h1, -⟩ := h hX; simp at h1
      · intro h hX; exact absurd hX h
    | [a], [] =>
      simp [badPos]
    | [a], Y :: Z :: head =>
      simp only [badPos]
      constructor
      · rintro h hX; obtain ⟨a', -, -, h1⟩ := h hX; simp at h1
      · intro h hX; exact absurd hX h
  | exRight a R b => simp [PosOK, badPos, eq_comm]
  | allRight a R b => simp [PosOK, badPos, eq_comm]
  | atLeast a k R b => simp [PosOK, badPos, eq_comm]
  | atMost a k R b => simp [PosOK, badPos]
  | chain body S => simp [PosOK, badPos]

theorem lookup_map_gen {β : Type} (f : RT m → β) :
    ∀ (l : List (RT m)) (R : RT m), R ∈ l → (l.map fun x => (x, f x)).lookup R = some (f R)
  | [], _, h => by simp at h
  | x :: l, R, h => by
    simp only [List.map_cons, List.lookup_cons]
    by_cases hx : R = x
    · subst hx; simp
    · have : (R == x) = false := by simp [hx]
      rw [this]
      exact lookup_map_gen f l R ((List.mem_cons.1 h).resolve_left hx)

theorem contains_ofList_fin (l : List (Fin n)) (a : Fin n) :
    (Std.HashSet.ofList l).contains a = decide (a ∈ l) := by
  rw [Std.HashSet.contains_ofList]
  simp

/-- `badPos` with the nominal test as a function. -/
def badPosB (mem : Fin n → Bool) : Clause (Fin n) (Fin m) → List (Fin n)
  | .gci body head =>
    match body, head with
    | [a], [_] => if mem a then [] else head
    | _, _ => head
  | .exRight _ _ b | .allRight _ _ b | .atLeast _ _ _ b => [b]
  | _ => []

theorem badPosB_eq (N : List (Fin n)) : badPosB (m := m) (fun a => decide (a ∈ N)) = badPos N := by
  funext cl
  cases cl with
  | gci body head =>
    match body, head with
    | [a], [_] => simp [badPosB, badPos]
    | [], _ => simp [badPosB, badPos]
    | _ :: _ :: _, _ => simp [badPosB, badPos]
    | [a], [] => simp [badPosB, badPos]
    | [a], _ :: _ :: _ => simp [badPosB, badPos]
  | _ => rfl

/-- **The C2a condition, computed with shared tables**: hash sets for the
nominal names and the names with a bad positive occurrence, and the
super-role test answered once per role term. -/
def c2aB (O : SRIQN.Ontology (Fin n) (Fin m)) : Bool :=
  let B := basePart O
  let N := noms O
  let Ns := Std.HashSet.ofList N
  let badS := Std.HashSet.ofList (B.flatMap (badPosB fun a => Ns.contains a))
  let tab := mkTab B
  let le := leF tab
  let invs := (upperL B).map fun q' => q'.2.2.1.flip
  let okT := (allRT m).map fun R => (R, invs.all fun R' => !le R R')
  (lowerL B).all fun q =>
    Ns.contains q.1 || !badS.contains q.1 || (okT.lookup q.2.2.1).getD false

theorem c2aB_eq (O : SRIQN.Ontology (Fin n) (Fin m)) : c2aB O =
    (lowerL (basePart O)).all fun q =>
      decide (q.1 ∈ noms O) || decide (q.1 ∉ (basePart O).flatMap (badPos (noms O))) ||
        ((upperL (basePart O)).map fun q' => q'.2.2.1.flip).all fun R' =>
          !leB (basePart O) q.2.2.1 R' := by
  unfold c2aB
  simp only [contains_ofList_fin, badPosB_eq, leF_mkTab]
  congr 1
  funext q
  rw [lookup_map_gen _ _ _ (mem_allRT _), Option.getD_some]
  have : (!decide (∃ a ∈ basePart O, q.1 ∈ badPos (noms O) a)) =
      decide (∀ x ∈ basePart O, q.1 ∉ badPos (noms O) x) := by
    by_cases h : ∃ a ∈ basePart O, q.1 ∈ badPos (noms O) a
    · obtain ⟨a, ha, hq⟩ := h
      rw [decide_eq_true ⟨a, ha, hq⟩, decide_eq_false (fun h' => h' a ha hq)]; rfl
    · rw [decide_eq_false h]
      exact (decide_eq_true (p := ∀ x ∈ basePart O, q.1 ∉ badPos (noms O) x)
        (fun x hx hq => h ⟨x, hx, hq⟩)).symm
  simp [this]

theorem c2aB_iff (O : SRIQN.Ontology (Fin n) (Fin m)) : c2aB O = true ↔ IsC2a O := by
  have hno : ∀ X, X ∉ noms O → (NomOnly O X ↔ X ∉ (basePart O).flatMap (badPos (noms O))) := by
    intro X hX
    simp only [NomOnly, hX, not_false_eq_true, true_and, List.mem_flatMap, not_exists, not_and,
      posOK_iff]
  rw [c2aB_eq]
  unfold IsC2a
  simp only [List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.mem_map,
    Bool.not_eq_eq_eq_not, Bool.not_true, forall_exists_index, and_imp]
  refine forall_congr' fun q => imp_congr_right fun _ => ?_
  constructor
  · intro h hn hno' q' hq' hle
    rcases h with (h | h) | h
    · exact hn h
    · exact hno' ((hno q.1 hn).2 h)
    · have := h _ q' hq' rfl
      rw [leB_iff.2 hle] at this; cases this
  · intro h
    by_cases hn : q.1 ∈ noms O
    · exact Or.inl (Or.inl hn)
    by_cases hb : q.1 ∉ (basePart O).flatMap (badPos (noms O))
    · exact Or.inl (Or.inr hb)
    refine Or.inr fun R' q' hq' hR' => ?_
    subst hR'
    cases hl : leB (basePart O) q.2.2.1 q'.2.2.1.flip
    · rfl
    · exact absurd (leB_iff.1 hl) (h hn (fun h' => hb ((hno q.1 hn).1 h')) q' hq')

/-- The fast decision of C2a. -/
def fastDecC2a (O : SRIQN.Ontology (Fin n) (Fin m)) : Decidable (IsC2a O) :=
  decidable_of_iff _ (c2aB_iff O)

end ContextCalculus.SROIQ.Proc

#print axioms ContextCalculus.SROIQ.Proc.c2aB_iff
