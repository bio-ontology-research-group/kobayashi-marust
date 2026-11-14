import ContextCalculus.SRIQ.Stars
import ContextCalculus.SRI.Procedure
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod

/-!
# An executable elimination procedure for ALCHIQ (stage C1, design section 4)

Concepts are `Fin n`, roles `Fin m`; records then form a finite type.
The procedure starts from all records whose own type is closed and whose
parent entry is a valid edge (`init`; a record outside it has no star),
and removes every record that has no supporting children list inside the
current set, until nothing changes (`alive`). Good records are exactly
the alive ones (`good_iff_mem_alive`), so `classifyQ` reads the
subsumers off the alive root records (`classifyQ_spec`).

Deciding whether a children list exists needs a bound on its length:
`support_bound` shows that a supporting list can be pruned to a sublist
of length at most `bnd O` (the sum of the numbers of the at-least
clauses, one per existential), whose entries all count for some
at-least or existential clause at the centre. Removing children keeps
the at-most clauses and the edge conditions. The search then runs over
all lists up to that length over the candidate children.

The procedure is exponential on purpose: it is the reference that a
demand-driven version must match later.
-/

namespace ContextCalculus.SRIQ

open ContextCalculus.SRI (RoleT Interp)

/-! ## Clause lists and the length bound (any names) -/

section Lists

variable {CName Role : Type} (O : Ontology CName Role)

/-- The existential and at-least clauses as `(a, k, R, b)`, an existential
counting as at least one. -/
def lowerL : List (CName × Nat × RoleT Role × CName) :=
  O.filterMap fun
    | .exRight a R b => some (a, 1, R, b)
    | .atLeast a k R b => some (a, k, R, b)
    | _ => none

/-- The at-most clauses as `(a, k, R, b)`. -/
def upperL : List (CName × Nat × RoleT Role × CName) :=
  O.filterMap fun
    | .atMost a k R b => some (a, k, R, b)
    | _ => none

/-- The length bound: the sum of the numbers of `lowerL`. -/
def bnd : Nat := ((lowerL O).map fun q => q.2.1).sum

variable {O}

theorem mem_lowerL {q : CName × Nat × RoleT Role × CName} :
    q ∈ lowerL O ↔ (q.2.1 = 1 ∧ Clause.exRight q.1 q.2.2.1 q.2.2.2 ∈ O) ∨
      Clause.atLeast q.1 q.2.1 q.2.2.1 q.2.2.2 ∈ O := by
  obtain ⟨a, k, R, b⟩ := q
  simp only [lowerL, List.mem_filterMap]
  constructor
  · rintro ⟨cl, hcl, he⟩
    cases cl <;> simp at he
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := he
      exact Or.inl ⟨rfl, hcl⟩
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := he
      exact Or.inr hcl
  · rintro (⟨rfl, h⟩ | h)
    · exact ⟨_, h, rfl⟩
    · exact ⟨_, h, rfl⟩

theorem mem_upperL {q : CName × Nat × RoleT Role × CName} :
    q ∈ upperL O ↔ Clause.atMost q.1 q.2.1 q.2.2.1 q.2.2.2 ∈ O := by
  obtain ⟨a, k, R, b⟩ := q
  simp only [upperL, List.mem_filterMap]
  constructor
  · rintro ⟨cl, hcl, he⟩
    cases cl <;> simp at he
    obtain ⟨rfl, rfl, rfl, rfl⟩ := he
    exact hcl
  · intro h
    exact ⟨_, h, rfl⟩

variable [DecidableEq CName] [DecidableEq Role]

/-- The existential and at-least parts of `StarOK`, as one list. -/
theorem lower_iff {t : Finset CName} {N : List (Nbr CName Role)} :
    ((∀ a R b, Clause.exRight a R b ∈ O → a ∈ t → 1 ≤ cnt N R b) ∧
      (∀ a k R b, Clause.atLeast a k R b ∈ O → a ∈ t → k ≤ cnt N R b)) ↔
    ∀ q ∈ lowerL O, q.1 ∈ t → q.2.1 ≤ cnt N q.2.2.1 q.2.2.2 := by
  constructor
  · rintro ⟨h1, h2⟩ q hq ha
    rcases mem_lowerL.1 hq with ⟨hk, hcl⟩ | hcl
    · rw [hk]; exact h1 _ _ _ hcl ha
    · exact h2 _ _ _ _ hcl ha
  · intro h
    refine ⟨fun a R b hcl ha => ?_, fun a k R b hcl ha => ?_⟩
    · exact h (a, 1, R, b) (mem_lowerL.2 (Or.inl ⟨rfl, hcl⟩)) ha
    · exact h (a, k, R, b) (mem_lowerL.2 (Or.inr hcl)) ha

theorem starOK_lower {t : Finset CName} {N : List (Nbr CName Role)} (h : StarOK O t N) :
    ∀ q ∈ lowerL O, q.1 ∈ t → q.2.1 ≤ cnt N q.2.2.1 q.2.2.2 :=
  lower_iff.1 ⟨h.ex, h.atLeast⟩

/-- An entry counts for some existential or at-least clause at the centre. -/
def contribB (t : Finset CName) (e : Nbr CName Role) : Bool :=
  (lowerL O).any fun q => decide (q.1 ∈ t ∧ q.2.2.1 ∈ e.1 ∧ q.2.2.2 ∈ e.2)

/-- A sublist of the children keeps `StarOK` when it keeps the lower bounds. -/
theorem starOK_sublist {t : Finset CName} {P C C' : List (Nbr CName Role)} (hs : C'.Sublist C)
    (h : StarOK O t (P ++ C))
    (hlow : ∀ q ∈ lowerL O, q.1 ∈ t → q.2.1 ≤ cnt (P ++ C') q.2.2.1 q.2.2.2) :
    StarOK O t (P ++ C') := by
  have hs' : (P ++ C').Sublist (P ++ C) := hs.append_left P
  obtain ⟨h1, h2⟩ := lower_iff.2 hlow
  exact ⟨h.closed, fun e he => h.edge e (hs'.subset he), h1, h2,
    fun a k R b hcl ha => le_trans hs'.countP_le (h.atMost a k R b hcl ha)⟩

/-- Dropping the entries that count for no clause keeps `StarOK`. -/
theorem starOK_filter {t : Finset CName} {P C : List (Nbr CName Role)}
    (h : StarOK O t (P ++ C)) : StarOK O t (P ++ C.filter (contribB (O := O) t)) := by
  refine starOK_sublist List.filter_sublist h fun q hq ht => ?_
  have heq : cnt (P ++ C.filter (contribB (O := O) t)) q.2.2.1 q.2.2.2 = cnt (P ++ C) q.2.2.1 q.2.2.2 := by
    unfold cnt
    rw [List.countP_append, List.countP_append, List.countP_filter]
    congr 1
    refine List.countP_congr fun e _ => ?_
    simp only [Bool.and_eq_true, decide_eq_true_eq, and_iff_left_iff_imp]
    intro hp
    exact List.any_eq_true.2 ⟨q, hq, decide_eq_true ⟨ht, hp⟩⟩
  rw [heq]
  exact starOK_lower h q hq ht

theorem le_sum_map_of_mem {β : Type} (g : β → Nat) {x : β} :
    ∀ Q : List β, x ∈ Q → g x ≤ (Q.map g).sum
  | [], h => by simp at h
  | q :: Q, h => by
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := le_sum_map_of_mem g Q h
      omega

theorem length_le_sum {α β : Type} (f : β → α → Bool) (Q : List β) :
    ∀ C : List α, (∀ e ∈ C, ∃ q ∈ Q, f q e = true) →
      C.length ≤ (Q.map fun q => C.countP (f q)).sum
  | [], _ => by simp
  | e :: C, h => by
    have ih := length_le_sum f Q C fun e' he' => h e' (List.mem_cons_of_mem _ he')
    obtain ⟨q, hq, hfq⟩ := h e List.mem_cons_self
    have h1 : (Q.map fun q => (e :: C).countP (f q)).sum =
        (Q.map fun q => C.countP (f q)).sum + (Q.map fun q => if f q e = true then 1 else 0).sum := by
      rw [← List.sum_map_add]
      congr 1
      refine List.map_congr_left fun q _ => ?_
      rw [List.countP_cons]
    have h2 : 1 ≤ (Q.map fun q => if f q e = true then 1 else 0).sum := by
      have := le_sum_map_of_mem (fun q => if f q e = true then 1 else 0) Q hq
      simpa [hfq] using this
    simp only [List.length_cons]
    omega

theorem sum_map_le {β : Type} {f g : β → Nat} :
    ∀ Q : List β, (∀ q ∈ Q, f q ≤ g q) → (Q.map f).sum ≤ (Q.map g).sum
  | [], _ => by simp
  | q :: Q, h => by
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h q List.mem_cons_self)
      (sum_map_le Q fun q' hq' => h q' (List.mem_cons_of_mem _ hq'))

theorem sum_filter_le {β : Type} (p : β → Bool) (f : β → Nat) :
    ∀ Q : List β, ((Q.filter p).map f).sum ≤ (Q.map f).sum
  | [] => by simp
  | q :: Q => by
    have := sum_filter_le p f Q
    rw [List.filter_cons]
    split <;> simp only [List.map_cons, List.sum_cons] <;> omega

theorem cnt_remove (P l1 l2 : List (Nbr CName Role)) (e : Nbr CName Role) (R : RoleT Role)
    (b : CName) : cnt (P ++ (l1 ++ e :: l2)) R b =
      cnt (P ++ (l1 ++ l2)) R b + if decide (R ∈ e.1 ∧ b ∈ e.2) = true then 1 else 0 := by
  simp only [cnt, List.countP_append, List.countP_cons]
  omega

/-- If the children list is longer than the bound, one child can go. -/
theorem exists_remove {t : Finset CName} {P C : List (Nbr CName Role)}
    (h : StarOK O t (P ++ C)) (hlen : bnd O < C.length) :
    ∃ C', C'.Sublist C ∧ C'.length + 1 = C.length ∧ StarOK O t (P ++ C') := by
  classical
  by_contra hno
  let crit := (lowerL O).filter fun q =>
    decide (q.1 ∈ t ∧ cnt (P ++ C) q.2.2.1 q.2.2.2 ≤ q.2.1)
  let f : CName × Nat × RoleT Role × CName → Nbr CName Role → Bool :=
    fun q e => decide (q.2.2.1 ∈ e.1 ∧ q.2.2.2 ∈ e.2)
  have hall : ∀ e ∈ C, ∃ q ∈ crit, f q e = true := by
    intro e he
    by_contra hne
    obtain ⟨l1, l2, rfl⟩ := List.append_of_mem he
    apply hno
    refine ⟨l1 ++ l2, ?_, by simp; omega, ?_⟩
    · exact (List.sublist_cons_self e l2).append_left l1
    · refine starOK_sublist ((List.sublist_cons_self e l2).append_left l1) h fun q hq ht => ?_
      have hl := starOK_lower h q hq ht
      rw [cnt_remove] at hl
      by_cases hp : decide (q.2.2.1 ∈ e.1 ∧ q.2.2.2 ∈ e.2) = true
      · by_contra hlt
        apply hne
        refine ⟨q, List.mem_filter.2 ⟨hq, decide_eq_true ⟨ht, ?_⟩⟩, hp⟩
        rw [cnt_remove, if_pos hp]
        omega
      · rw [if_neg hp] at hl
        omega
  have h1 := length_le_sum f crit C hall
  have h2 : (crit.map fun q => C.countP (f q)).sum ≤ (crit.map fun q => q.2.1).sum := by
    refine sum_map_le crit fun q hq => ?_
    obtain ⟨-, hq⟩ := List.mem_filter.1 hq
    have hq := of_decide_eq_true hq
    refine le_trans ?_ hq.2
    unfold cnt
    rw [List.countP_append]
    exact Nat.le_add_left _ _
  have h3 : (crit.map fun q => q.2.1).sum ≤ ((lowerL O).map fun q => q.2.1).sum :=
    sum_filter_le _ _ _
  unfold bnd at hlen
  omega

/-- **List-length bound.** A supporting children list can be pruned to a
sublist of length at most `bnd O` whose entries all count. -/
theorem support_bound {t : Finset CName} {P : List (Nbr CName Role)} :
    ∀ C : List (Nbr CName Role), StarOK O t (P ++ C) →
      ∃ C', C'.Sublist C ∧ C'.length ≤ bnd O ∧ (∀ e ∈ C', contribB (O := O) t e = true) ∧
        StarOK O t (P ++ C') := by
  -- first the pruning to `bnd O`, for lists of counting entries
  have key : ∀ k, ∀ C : List (Nbr CName Role), C.length = k →
      (∀ e ∈ C, contribB (O := O) t e = true) → StarOK O t (P ++ C) →
      ∃ C', C'.Sublist C ∧ C'.length ≤ bnd O ∧ (∀ e ∈ C', contribB (O := O) t e = true) ∧
        StarOK O t (P ++ C') := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro C hk hc h
      by_cases hle : C.length ≤ bnd O
      · exact ⟨C, List.Sublist.refl _, hle, hc, h⟩
      · obtain ⟨C', hs, hl, h'⟩ := exists_remove h (by omega)
        obtain ⟨C'', hs', hl', hc', h''⟩ :=
          ih C'.length (by omega) C' rfl (fun e he => hc e (hs.subset he)) h'
        exact ⟨C'', hs'.trans hs, hl', hc', h''⟩
  intro C h
  obtain ⟨C', hs, hl, hc, h'⟩ := key _ (C.filter (contribB (O := O) t)) rfl
    (fun e he => (List.mem_filter.1 he).2) (starOK_filter h)
  exact ⟨C', hs.trans List.filter_sublist, hl, hc, h'⟩

end Lists

/-! ## The procedure over `Fin n` and `Fin m` -/

namespace Proc

variable {n m : Nat}

abbrev QRec (n m : Nat) := Rec (Fin n) (Fin m)
abbrev QNbr (n m : Nat) := Nbr (Fin n) (Fin m)

section Decide

variable (O : Ontology (Fin n) (Fin m))

theorem closed_iff_gcis (t : Finset (Fin n)) :
    Closed O t ↔ ∀ q ∈ SRI.Proc.gcis (sriPart O), (∀ a ∈ q.1, a ∈ t) → ∃ b ∈ q.2, b ∈ t := by
  constructor
  · intro h q hq
    exact h q.1 q.2 (SRI.Proc.mem_gcis.1 hq)
  · intro h body head hcl
    exact h (body, head) (SRI.Proc.mem_gcis.2 hcl)

instance (t : Finset (Fin n)) : Decidable (Closed O t) :=
  decidable_of_iff _ (closed_iff_gcis O t).symm

theorem upClosed_iff (L : Finset (RoleT (Fin m))) :
    UpClosed O L ↔ ∀ R ∈ L, ∀ S ∈ SRI.Proc.roleUp (sriPart O) R, S ∈ L := by
  unfold UpClosed RoleLe
  simp only [SRI.Proc.mem_roleUp]

instance (L : Finset (RoleT (Fin m))) : Decidable (UpClosed O L) :=
  decidable_of_iff _ (upClosed_iff O L).symm

theorem edgeOK_iff (t : Finset (Fin n)) (e : QNbr n m) :
    EdgeOK O t e ↔ ∀ q ∈ SRI.Proc.alls (sriPart O),
      (q.2.1 ∈ e.1 → q.1 ∈ t → q.2.2 ∈ e.2) ∧ (q.2.1.flip ∈ e.1 → q.1 ∈ e.2 → q.2.2 ∈ t) := by
  constructor
  · intro h q hq
    exact h q.1 q.2.1 q.2.2 (mem_sriPart.1 (SRI.Proc.mem_alls.1 hq))
  · intro h a S c hcl
    exact h (a, S, c) (SRI.Proc.mem_alls.2 (mem_sriPart.2 hcl))

instance (t : Finset (Fin n)) (e : QNbr n m) : Decidable (EdgeOK O t e) :=
  decidable_of_iff _ (edgeOK_iff O t e).symm

theorem starOK_iff (t : Finset (Fin n)) (N : List (QNbr n m)) :
    StarOK O t N ↔ Closed O t ∧ (∀ e ∈ N, UpClosed O e.1 ∧ EdgeOK O t e) ∧
      (∀ q ∈ lowerL O, q.1 ∈ t → q.2.1 ≤ cnt N q.2.2.1 q.2.2.2) ∧
      (∀ q ∈ upperL O, q.1 ∈ t → cnt N q.2.2.1 q.2.2.2 ≤ q.2.1) := by
  constructor
  · intro h
    exact ⟨h.closed, h.edge, starOK_lower h,
      fun q hq ht => h.atMost _ _ _ _ (mem_upperL.1 hq) ht⟩
  · rintro ⟨h1, h2, h3, h4⟩
    obtain ⟨h5, h6⟩ := lower_iff.2 h3
    exact ⟨h1, h2, h5, h6, fun a k R b hcl ha => h4 (a, k, R, b) (mem_upperL.2 hcl) ha⟩

instance (t : Finset (Fin n)) (N : List (QNbr n m)) : Decidable (StarOK O t N) :=
  decidable_of_iff _ (starOK_iff O t N).symm

end Decide

section Defs

variable (O : Ontology (Fin n) (Fin m))

/-- The conditions a record checks on itself: a closed type and a valid
parent edge. -/
def localOK (ρ : QRec n m) : Prop :=
  Closed O ρ.1 ∧ ∀ e ∈ ρ.2.toList, UpClosed O e.1 ∧ EdgeOK O ρ.1 e

instance (ρ : QRec n m) : Decidable (localOK O ρ) := by
  unfold localOK; infer_instance

/-- A possible child entry of a node of type `t`. -/
def candOK (t : Finset (Fin n)) (e : QNbr n m) : Prop :=
  UpClosed O e.1 ∧ EdgeOK O t e ∧ contribB (O := O) t e = true

instance (t : Finset (Fin n)) (e : QNbr n m) : Decidable (candOK O t e) := by
  unfold candOK; infer_instance

/-- The child entries of a node of type `t` whose records are in `G`. -/
def cands (G : Finset (QRec n m)) (t : Finset (Fin n)) : Multiset (QNbr n m) :=
  (G.val.bind fun ρ => match ρ.2 with
    | some p => if p.2 = t then {(flipL p.1, ρ.1)} else 0
    | none => 0).filter (candOK O t)

/-- All lists of length at most `k` over `s`. -/
def listsUpTo {α : Type} : Nat → Multiset α → Multiset (List α)
  | 0, _ => {[]}
  | k + 1, s => [] ::ₘ s.bind fun e => (listsUpTo k s).map (e :: ·)

/-- `ρ` has a children list in `G` of length at most `bnd O`. -/
def supB (G : Finset (QRec n m)) (ρ : QRec n m) : Prop :=
  ∃ C ∈ listsUpTo (bnd O) (cands O G ρ.1), StarOK O ρ.1 (ρ.2.toList ++ C)

instance (G : Finset (QRec n m)) (ρ : QRec n m) : Decidable (supB O G ρ) := by
  unfold supB; exact Multiset.decidableExistsMultiset

def prune (G : Finset (QRec n m)) : Finset (QRec n m) :=
  G.filter (supB O G)

/-- Remove unsupported records until stable. -/
def eliminate (G : Finset (QRec n m)) : Finset (QRec n m) :=
  let G' := prune O G
  if h : G' = G then G else eliminate G'
termination_by G.card
decreasing_by
  exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨Finset.filter_subset _ _, h⟩)

/-- The starting set: every record that passes its own checks. -/
def init : Finset (QRec n m) :=
  Finset.univ.filter (localOK O)

def alive : Finset (QRec n m) :=
  eliminate O (init O)

/-- The procedure's verdict on `a ⊑ b`. -/
def entailsQ (a b : Fin n) : Bool :=
  decide (∀ ρ ∈ alive O, ρ.2 = none → a ∈ ρ.1 → b ∈ ρ.1)

/-- The procedure's verdict on the satisfiability of `a`. -/
def satQ (a : Fin n) : Bool :=
  decide (∃ ρ ∈ alive O, ρ.2 = none ∧ a ∈ ρ.1)

/-- Every requested name with its subsumers. -/
def classifyQ (req : List (Fin n)) : List (Fin n × List (Fin n)) :=
  req.map fun a => (a, (List.finRange n).filter fun b => entailsQ O a b)

end Defs

section Facts

variable {O : Ontology (Fin n) (Fin m)}

theorem mem_listsUpTo {α : Type} {s : Multiset α} :
    ∀ (k : Nat) (l : List α), l ∈ listsUpTo k s ↔ l.length ≤ k ∧ ∀ e ∈ l, e ∈ s
  | 0, l => by
    cases l <;> simp [listsUpTo]
  | k + 1, l => by
    cases l with
    | nil => simp [listsUpTo]
    | cons e l =>
      simp only [listsUpTo, Multiset.mem_cons, reduceCtorEq, false_or, Multiset.mem_bind,
        Multiset.mem_map, List.cons.injEq, List.length_cons, List.mem_cons, forall_eq_or_imp]
      constructor
      · rintro ⟨e', he', l', hl', rfl, rfl⟩
        obtain ⟨h1, h2⟩ := (mem_listsUpTo k l').1 hl'
        exact ⟨by omega, he', h2⟩
      · rintro ⟨hlen, he, hl⟩
        exact ⟨e, he, l, (mem_listsUpTo k l).2 ⟨by omega, hl⟩, rfl, rfl⟩

theorem flipL_flipL (L : Finset (RoleT (Fin m))) : flipL (flipL L) = L := by
  ext S
  rw [mem_flipL, mem_flipL, RoleT.flip_flip]

theorem mem_cands {G : Finset (QRec n m)} {t : Finset (Fin n)} {e : QNbr n m} :
    e ∈ cands O G t ↔ childRec t e ∈ G ∧ candOK O t e := by
  unfold cands
  rw [Multiset.mem_filter, Multiset.mem_bind]
  refine and_congr_left fun _ => ⟨?_, ?_⟩
  · rintro ⟨⟨s, par⟩, hρ, he⟩
    cases par with
    | none => simp at he
    | some p =>
      simp only at he
      by_cases hp : p.2 = t
      swap
      · rw [if_neg hp] at he
        simp at he
      rw [if_pos hp, Multiset.mem_singleton] at he
      subst he
      obtain ⟨L, s'⟩ := p
      simp only at hp
      subst hp
      simpa [childRec, flipL_flipL] using hρ
  · intro h
    refine ⟨childRec t e, h, ?_⟩
    simp [childRec, flipL_flipL]

theorem supB_mono {S G : Finset (QRec n m)} (hSG : S ⊆ G) {ρ : QRec n m} (h : supB O S ρ) :
    supB O G ρ := by
  obtain ⟨C, hC, hok⟩ := h
  refine ⟨C, ?_, hok⟩
  rw [mem_listsUpTo] at hC ⊢
  refine ⟨hC.1, fun e he => ?_⟩
  obtain ⟨h1, h2⟩ := mem_cands.1 (hC.2 e he)
  exact mem_cands.2 ⟨hSG h1, h2⟩

theorem supports_of_supB {G : Finset (QRec n m)} {ρ : QRec n m} (h : supB O G ρ) :
    ∃ C, Supports O (↑G : Set (QRec n m)) ρ C := by
  obtain ⟨C, hC, hok⟩ := h
  refine ⟨C, hok, fun e he => ?_⟩
  exact Finset.mem_coe.2 (mem_cands.1 ((mem_listsUpTo _ _).1 hC |>.2 e he)).1

theorem supB_of_supports {S : Set (QRec n m)} {G : Finset (QRec n m)} (hSG : ∀ x ∈ S, x ∈ G)
    {ρ : QRec n m} {C : List (QNbr n m)} (h : Supports O S ρ C) : supB O G ρ := by
  obtain ⟨C', hs, hl, hc, hok⟩ := support_bound C h.1
  refine ⟨C', (mem_listsUpTo _ _).2 ⟨hl, fun e he => mem_cands.2 ⟨hSG _ (h.2 e (hs.subset he)), ?_⟩⟩,
    hok⟩
  have hedge := h.1.edge e (List.mem_append_right _ (hs.subset he))
  exact ⟨hedge.1, hedge.2, hc e he⟩

theorem eliminate_spec : ∀ G : Finset (QRec n m),
    eliminate O G ⊆ G ∧ prune O (eliminate O G) = eliminate O G ∧
    ∀ S ⊆ G, (∀ ρ ∈ S, supB O S ρ) → S ⊆ eliminate O G := by
  intro G
  induction h : G.card using Nat.strong_induction_on generalizing G with
  | _ k ih =>
    rw [eliminate]
    split_ifs with hp
    · exact ⟨Finset.Subset.refl _, hp, fun S hS _ => hS⟩
    · have hlt : (prune O G).card < k := h ▸
        Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨Finset.filter_subset _ _, hp⟩)
      obtain ⟨h1, h2, h3⟩ := ih _ hlt _ rfl
      refine ⟨h1.trans (Finset.filter_subset _ _), h2, fun S hS hw => h3 S ?_ hw⟩
      intro ρ hρ
      exact Finset.mem_filter.2 ⟨hS hρ, supB_mono hS (hw ρ hρ)⟩

theorem alive_supB {ρ : QRec n m} (hρ : ρ ∈ alive O) : supB O (alive O) ρ := by
  have h := (eliminate_spec (O := O) (init O)).2.1
  unfold alive at hρ ⊢
  rw [← h] at hρ
  exact (Finset.mem_filter.1 hρ).2

theorem alive_selfSupp : SelfSupp O (↑(alive O) : Set (QRec n m)) :=
  fun _ hρ => supports_of_supB (alive_supB (Finset.mem_coe.1 hρ))

/-- **Exactness of elimination.** The alive records are exactly the good ones. -/
theorem good_iff_mem_alive (ρ : QRec n m) : Good O ρ ↔ ρ ∈ alive O := by
  classical
  constructor
  · rintro ⟨G, hρ, hG⟩
    let S : Finset (QRec n m) := Finset.univ.filter (· ∈ G)
    have hS : ∀ x ∈ G, x ∈ S := fun x hx => Finset.mem_filter.2 ⟨Finset.mem_univ _, hx⟩
    have hSG : ∀ x ∈ S, x ∈ G := fun x hx => (Finset.mem_filter.1 hx).2
    have hsub : S ⊆ init O := by
      intro x hx
      obtain ⟨C, hok, -⟩ := hG x (hSG x hx)
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, hok.closed, fun e he => ?_⟩
      exact hok.edge e (List.mem_append_left _ he)
    have hsupp : ∀ x ∈ S, supB O S x := by
      intro x hx
      obtain ⟨C, hC⟩ := hG x (hSG x hx)
      exact supB_of_supports hS hC
    exact (eliminate_spec (O := O) (init O)).2.2 S hsub hsupp (hS ρ hρ)
  · intro h
    exact ⟨_, Finset.mem_coe.2 h, alive_selfSupp⟩

theorem entailsQ_iff (hA : IsALCHIQ O) (a b : Fin n) :
    entailsQ O a b = true ↔ EntailsSub O a b := by
  rw [entailsSub_iff_star O hA, entailsQ, decide_eq_true_iff]
  constructor
  · intro h t ht hat
    exact h _ ((good_iff_mem_alive _).1 ht) rfl hat
  · intro h ρ hρ hn hat
    obtain ⟨t, par⟩ := ρ
    simp only at hn hat ⊢
    subst hn
    exact h t ((good_iff_mem_alive _).2 hρ) hat

theorem satQ_iff (hA : IsALCHIQ O) (a : Fin n) :
    satQ O a = false ↔
      ∀ (D : Type) [Nonempty D] (I : Interp D (Fin n) (Fin m)), models I O → ∀ x, ¬ I.c a x := by
  rw [unsat_iff_no_star O hA, satQ, decide_eq_false_iff_not]
  constructor
  · intro h t ht hat
    exact h ⟨_, (good_iff_mem_alive _).1 ht, rfl, hat⟩
  · rintro h ⟨⟨t, par⟩, hρ, hn, hat⟩
    simp only at hn hat
    subst hn
    exact h t ((good_iff_mem_alive _).2 hρ) hat

/-- **Classification.** Each requested name comes with exactly its
subsumers. -/
theorem classifyQ_spec (hA : IsALCHIQ O) {req : List (Fin n)} :
    ∀ p ∈ classifyQ O req, p.1 ∈ req ∧ ∀ b, b ∈ p.2 ↔ EntailsSub O p.1 b := by
  intro p hp
  simp only [classifyQ, List.mem_map] at hp
  obtain ⟨a, ha, rfl⟩ := hp
  refine ⟨ha, fun b => ?_⟩
  simp only [List.mem_filter, List.mem_finRange, true_and]
  exact entailsQ_iff hA a b

end Facts

end Proc

end ContextCalculus.SRIQ

#print axioms ContextCalculus.SRIQ.support_bound
#print axioms ContextCalculus.SRIQ.Proc.good_iff_mem_alive
#print axioms ContextCalculus.SRIQ.Proc.entailsQ_iff
#print axioms ContextCalculus.SRIQ.Proc.satQ_iff
#print axioms ContextCalculus.SRIQ.Proc.classifyQ_spec
