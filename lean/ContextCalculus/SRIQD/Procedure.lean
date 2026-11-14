import ContextCalculus.SRIQD.Stars
import ContextCalculus.SRIQ.Procedure

/-!
# An executable elimination procedure with a datatype oracle (stage C4, step 3)

`docs/V1.7.0-C4-DATATYPES-DESIGN.md`, sections 4 and 7. Concepts are
`Fin n`, roles `Fin m`, data properties `Fin p`, data atoms `Fin q`; the
oracle `card` is any computable function, and the statements hold for
every data theory for which it satisfies `OracleSpec`.

A data star depends on the centre type only, so the procedure decides
for each type whether it has one (`dataSatB`), starts the `SRIQ`
elimination of the object part from the records whose own checks pass
and whose type has a data star (`initD`), and runs it (`aliveD`). Good
records are exactly the alive ones (`good_iff_mem_aliveD`), and
`classifyQD` reads the subsumers off the alive root records
(`classifyQD_spec`).

Deciding `dataSatB` needs a bound on the length of a data star:
`dsupport_bound` prunes a data star to a sublist of length at most
`dbnd O`, the sum of the numbers of the data existential (one each) and
at-least clauses, whose entries all count for an active one. The bound
for the children lists of the object part is `SRIQ.bnd` of the object
part, unchanged. The pruning is the argument of `SRIQ.support_bound`
for any lower bounds over counts (`prune_bound`).
-/

namespace ContextCalculus.SRIQD

open ContextCalculus.SRI (RoleT Interp)
open ContextCalculus.SRIQ (Rec Nbr childRec)

/-! ## Pruning under lower bounds (any types) -/

section Prune

variable {α β : Type}

theorem countP_remove (f : α → Bool) (l1 l2 : List α) (e : α) :
    (l1 ++ e :: l2).countP f = (l1 ++ l2).countP f + if f e = true then 1 else 0 := by
  simp only [List.countP_append, List.countP_cons]
  omega

/-- A list longer than the sum of the lower bounds has an entry whose
removal keeps every lower bound. -/
theorem exists_remove_lower (Q : List β) (k : β → Nat) (f : β → α → Bool) {L : List α}
    (hlow : ∀ q ∈ Q, k q ≤ L.countP (f q)) (hc : ∀ e ∈ L, ∃ q ∈ Q, f q e = true)
    (hlen : (Q.map k).sum < L.length) :
    ∃ L' : List α, L'.Sublist L ∧ L'.length + 1 = L.length ∧ ∀ q ∈ Q, k q ≤ L'.countP (f q) := by
  classical
  by_contra hno
  let crit := Q.filter fun q => decide (L.countP (f q) ≤ k q)
  have hall : ∀ e ∈ L, ∃ q ∈ crit, f q e = true := by
    intro e he
    by_contra hne
    obtain ⟨l1, l2, rfl⟩ := List.append_of_mem he
    apply hno
    refine ⟨l1 ++ l2, (List.sublist_cons_self e l2).append_left l1, by simp; omega,
      fun q hq => ?_⟩
    have hl := hlow q hq
    rw [countP_remove] at hl
    by_cases hp : f q e = true
    · by_contra hlt
      apply hne
      refine ⟨q, List.mem_filter.2 ⟨hq, decide_eq_true ?_⟩, hp⟩
      rw [countP_remove, if_pos hp]
      omega
    · rw [if_neg hp] at hl
      omega
  have h1 := SRIQ.length_le_sum f crit L hall
  have h2 : (crit.map fun q => L.countP (f q)).sum ≤ (crit.map k).sum :=
    SRIQ.sum_map_le crit fun q hq => of_decide_eq_true (List.mem_filter.1 hq).2
  have h3 : (crit.map k).sum ≤ (Q.map k).sum := SRIQ.sum_filter_le _ _ _
  omega

/-- **Pruning.** A list that meets lower bounds on counts and has a
property closed under sublists has a sublist with both whose length is
at most the sum of the bounds and whose entries all count. -/
theorem prune_bound (Q : List β) (k : β → Nat) (f : β → α → Bool) (P : List α → Prop)
    (hP : ∀ L L', L'.Sublist L → P L → P L') :
    ∀ L : List α, P L → (∀ q ∈ Q, k q ≤ L.countP (f q)) →
      ∃ L', L'.Sublist L ∧ L'.length ≤ (Q.map k).sum ∧ (∀ e ∈ L', ∃ q ∈ Q, f q e = true) ∧
        P L' ∧ ∀ q ∈ Q, k q ≤ L'.countP (f q) := by
  have key : ∀ j, ∀ L : List α, L.length = j → (∀ e ∈ L, ∃ q ∈ Q, f q e = true) → P L →
      (∀ q ∈ Q, k q ≤ L.countP (f q)) →
      ∃ L', L'.Sublist L ∧ L'.length ≤ (Q.map k).sum ∧ (∀ e ∈ L', ∃ q ∈ Q, f q e = true) ∧
        P L' ∧ ∀ q ∈ Q, k q ≤ L'.countP (f q) := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro L hj hc hPL hlow
      by_cases hle : L.length ≤ (Q.map k).sum
      · exact ⟨L, List.Sublist.refl _, hle, hc, hPL, hlow⟩
      · obtain ⟨L', hs, hl, hlow'⟩ := exists_remove_lower Q k f hlow hc (by omega)
        obtain ⟨L'', hs', hl', hc', hP'', hlow''⟩ := ih L'.length (by omega) L' rfl
          (fun e he => hc e (hs.subset he)) (hP L L' hs hPL) hlow'
        exact ⟨L'', hs'.trans hs, hl', hc', hP'', hlow''⟩
  intro L hPL hlow
  let g : α → Bool := fun e => Q.any fun q => f q e
  have hcnt : ∀ q ∈ Q, (L.filter g).countP (f q) = L.countP (f q) := by
    intro q hq
    rw [List.countP_filter]
    refine List.countP_congr fun e _ => ?_
    simp only [Bool.and_eq_true, and_iff_left_iff_imp]
    intro hf
    exact List.any_eq_true.2 ⟨q, hq, hf⟩
  obtain ⟨L', hs, hl, hc, hP', hlow'⟩ := key _ (L.filter g) rfl
    (fun e he => List.any_eq_true.1 (List.mem_filter.1 he).2)
    (hP L _ List.filter_sublist hPL) (fun q hq => (hcnt q hq).symm ▸ hlow q hq)
  exact ⟨L', hs.trans List.filter_sublist, hl, hc, hP', hlow'⟩

end Prune

/-! ## Clause lists, the data bound and the decision of data stars -/

section Lists

set_option linter.unusedSectionVars false

variable {CName Role DProp DAtom : Type} (O : Ontology CName Role DProp DAtom)

/-- The data existential and at-least clauses as `(a, k, u, pos, neg)`, an
existential counting as at least one. -/
def dLowerL : List (CName × Nat × DProp × List DAtom × List DAtom) :=
  O.filterMap fun
    | .dEx a u pos neg => some (a, 1, u, pos, neg)
    | .dAtLeast a k u pos neg => some (a, k, u, pos, neg)
    | _ => none

/-- The data at-most clauses as `(a, k, u, pos, neg)`. -/
def dUpperL : List (CName × Nat × DProp × List DAtom × List DAtom) :=
  O.filterMap fun
    | .dAtMost a k u pos neg => some (a, k, u, pos, neg)
    | _ => none

/-- The data universal clauses as `(a, u, head)`. -/
def dAllL : List (CName × DProp × List (DAtom × Bool)) :=
  O.filterMap fun
    | .dAll a u head => some (a, u, head)
    | _ => none

/-- The data property inclusions. -/
def dSubL : List (DProp × DProp) :=
  O.filterMap fun
    | .dSub u w => some (u, w)
    | _ => none

/-- **The data bound**: the sum of the numbers of `dLowerL`. -/
def dbnd : Nat := ((dLowerL O).map fun q => q.2.1).sum

variable {O}

theorem mem_dLowerL {q : CName × Nat × DProp × List DAtom × List DAtom} :
    q ∈ dLowerL O ↔ (q.2.1 = 1 ∧ Clause.dEx q.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 ∈ O) ∨
      Clause.dAtLeast q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 ∈ O := by
  obtain ⟨a, k, u, pos, neg⟩ := q
  simp only [dLowerL, List.mem_filterMap]
  constructor
  · rintro ⟨cl, hcl, he⟩
    cases cl <;> simp at he
    · obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := he
      exact Or.inl ⟨rfl, hcl⟩
    · obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := he
      exact Or.inr hcl
  · rintro (⟨rfl, h⟩ | h)
    · exact ⟨_, h, rfl⟩
    · exact ⟨_, h, rfl⟩

theorem mem_dUpperL {q : CName × Nat × DProp × List DAtom × List DAtom} :
    q ∈ dUpperL O ↔ Clause.dAtMost q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 ∈ O := by
  obtain ⟨a, k, u, pos, neg⟩ := q
  simp only [dUpperL, List.mem_filterMap]
  constructor
  · rintro ⟨cl, hcl, he⟩
    cases cl <;> simp at he
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := he
    exact hcl
  · intro h
    exact ⟨_, h, rfl⟩

theorem mem_dAllL {q : CName × DProp × List (DAtom × Bool)} :
    q ∈ dAllL O ↔ Clause.dAll q.1 q.2.1 q.2.2 ∈ O := by
  obtain ⟨a, u, head⟩ := q
  simp only [dAllL, List.mem_filterMap]
  constructor
  · rintro ⟨cl, hcl, he⟩
    cases cl <;> simp at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact hcl
  · intro h
    exact ⟨_, h, rfl⟩

theorem mem_dSubL {q : DProp × DProp} : q ∈ dSubL O ↔ Clause.dSub q.1 q.2 ∈ O := by
  obtain ⟨u, w⟩ := q
  simp only [dSubL, List.mem_filterMap]
  constructor
  · rintro ⟨cl, hcl, he⟩
    cases cl <;> simp at he
    obtain ⟨rfl, rfl⟩ := he
    exact hcl
  · intro h
    exact ⟨_, h, rfl⟩

variable [DecidableEq CName] [DecidableEq DProp] [DecidableEq DAtom]
variable (O) (card : Finset DAtom → Option Nat)

/-- The cardinality condition for the value type `τ`. -/
def cardOK (Dn : List (DNbr DProp DAtom)) (τ : Finset DAtom) : Bool :=
  match card τ with
  | some k => decide (tcnt Dn τ ≤ k)
  | none => true

/-- The conditions of a data star that hold for every sublist. -/
def DDown (t : Finset CName) (Dn : List (DNbr DProp DAtom)) : Prop :=
  (∀ e ∈ Dn, ∀ q ∈ dSubL O, q.1 ∈ e.1 → q.2 ∈ e.1) ∧
  (∀ e ∈ Dn, cardOK card Dn e.2 = true) ∧
  (∀ q ∈ dAllL O, q.1 ∈ t → ∀ e ∈ Dn, q.2.1 ∈ e.1 → ∃ l ∈ q.2.2, litOK l e.2) ∧
  (∀ q ∈ dUpperL O, q.1 ∈ t → dcnt Dn q.2.2.1 q.2.2.2.1 q.2.2.2.2 ≤ q.2.1)

instance (t : Finset CName) (Dn : List (DNbr DProp DAtom)) : Decidable (DDown O card t Dn) := by
  unfold DDown; infer_instance

/-- The lower bounds of a data star. -/
def DLower (t : Finset CName) (Dn : List (DNbr DProp DAtom)) : Prop :=
  ∀ q ∈ dLowerL O, q.1 ∈ t → q.2.1 ≤ dcnt Dn q.2.2.1 q.2.2.2.1 q.2.2.2.2

instance (t : Finset CName) (Dn : List (DNbr DProp DAtom)) : Decidable (DLower O t Dn) := by
  unfold DLower; infer_instance

variable {O card}

theorem dok_iff {t : Finset CName} {Dn : List (DNbr DProp DAtom)} :
    DOK O card t Dn ↔ DDown O card t Dn ∧ DLower O t Dn := by
  constructor
  · intro h
    refine ⟨⟨fun e he q hq hu => h.up e he q.1 q.2 (mem_dSubL.1 hq) hu, fun e he => ?_,
      fun q hq ht e he hu => h.all _ _ _ (mem_dAllL.1 hq) ht e he hu,
      fun q hq ht => h.atMost _ _ _ _ _ (mem_dUpperL.1 hq) ht⟩, fun q hq ht => ?_⟩
    · unfold cardOK
      split
      · rename_i k hk
        exact decide_eq_true (h.card _ k hk)
      · rfl
    · rcases mem_dLowerL.1 hq with ⟨hk, hcl⟩ | hcl
      · rw [hk]; exact h.ex _ _ _ _ hcl ht
      · exact h.atLeast _ _ _ _ _ hcl ht
  · rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩
    refine ⟨fun e he u w hcl hu => h1 e he (u, w) (mem_dSubL.2 hcl) hu, fun τ k hk => ?_,
      fun a u head hcl ht e he hu => h3 (a, u, head) (mem_dAllL.2 hcl) ht e he hu,
      fun a u pos neg hcl ht => h5 (a, 1, u, pos, neg) (mem_dLowerL.2 (Or.inl ⟨rfl, hcl⟩)) ht,
      fun a k u pos neg hcl ht => h5 (a, k, u, pos, neg) (mem_dLowerL.2 (Or.inr hcl)) ht,
      fun a k u pos neg hcl ht => h4 (a, k, u, pos, neg) (mem_dUpperL.2 hcl) ht⟩
    by_cases h0 : tcnt Dn τ = 0
    · omega
    · obtain ⟨e, he, hτ⟩ := List.countP_pos_iff.1 (Nat.pos_of_ne_zero h0)
      have hτ : e.2 = τ := of_decide_eq_true hτ
      have := h2 e he
      rw [hτ] at this
      unfold cardOK at this
      rw [hk] at this
      exact of_decide_eq_true this

instance (t : Finset CName) (Dn : List (DNbr DProp DAtom)) : Decidable (DOK O card t Dn) :=
  decidable_of_iff _ dok_iff.symm

theorem dDown_sublist {t : Finset CName} {Dn Dn' : List (DNbr DProp DAtom)}
    (hs : Dn'.Sublist Dn) (h : DDown O card t Dn) : DDown O card t Dn' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun e he => h1 e (hs.subset he), fun e he => ?_,
    fun q hq ht e he => h3 q hq ht e (hs.subset he),
    fun q hq ht => le_trans hs.countP_le (h4 q hq ht)⟩
  have := h2 e (hs.subset he)
  unfold cardOK at this ⊢
  split
  · rename_i k hk
    rw [hk] at this
    exact decide_eq_true (le_trans hs.countP_le (of_decide_eq_true this))
  · rfl

variable (O) in
/-- An entry counts for some data existential or at-least clause at `t`. -/
def dcontrib (t : Finset CName) (e : DNbr DProp DAtom) : Bool :=
  (dLowerL O).any fun q => decide (q.1 ∈ t ∧ q.2.2.1 ∈ e.1 ∧ rngOK q.2.2.2.1 q.2.2.2.2 e.2)

/-- **Data bound.** A data star can be pruned to a sublist of length at
most `dbnd O` whose entries all count. -/
theorem dsupport_bound {t : Finset CName} {Dn : List (DNbr DProp DAtom)} (h : DOK O card t Dn) :
    ∃ Dn', Dn'.Sublist Dn ∧ Dn'.length ≤ dbnd O ∧ (∀ e ∈ Dn', dcontrib O t e = true) ∧
      DOK O card t Dn' := by
  classical
  obtain ⟨hd, hl⟩ := dok_iff.1 h
  let Q := (dLowerL O).filter fun q => decide (q.1 ∈ t)
  let f : CName × Nat × DProp × List DAtom × List DAtom → DNbr DProp DAtom → Bool :=
    fun q e => decide (q.2.2.1 ∈ e.1 ∧ rngOK q.2.2.2.1 q.2.2.2.2 e.2)
  obtain ⟨Dn', hs, hlen, hc, hd', hl'⟩ := prune_bound Q (fun q => q.2.1) f (DDown O card t)
    (fun L L' hs h => dDown_sublist hs h) Dn hd
    (fun q hq => hl q (List.mem_filter.1 hq).1 (of_decide_eq_true (List.mem_filter.1 hq).2))
  refine ⟨Dn', hs, le_trans hlen (SRIQ.sum_filter_le _ _ _), fun e he => ?_,
    dok_iff.2 ⟨hd', fun q hq ht => hl' q (List.mem_filter.2 ⟨hq, decide_eq_true ht⟩)⟩⟩
  obtain ⟨q, hq, hf⟩ := hc e he
  obtain ⟨hq, ht⟩ := List.mem_filter.1 hq
  exact List.any_eq_true.2 ⟨q, hq, decide_eq_true ⟨of_decide_eq_true ht, of_decide_eq_true hf⟩⟩

end Lists

/-! ## The procedure over finite names -/

namespace Proc

open ContextCalculus.SRIQ.Proc (QRec QNbr listsUpTo mem_listsUpTo eliminate eliminate_spec init
  localOK supB prune supports_of_supB supB_of_supports)

variable {n m p q : Nat}

section Defs

variable (O : Ontology (Fin n) (Fin m) (Fin p) (Fin q)) (card : Finset (Fin q) → Option Nat)

/-- A possible entry of a data star of `t`. -/
def dcandOK (t : Finset (Fin n)) (e : DNbr (Fin p) (Fin q)) : Prop :=
  DDown O card t [e] ∧ dcontrib O t e = true

instance (t : Finset (Fin n)) (e : DNbr (Fin p) (Fin q)) : Decidable (dcandOK O card t e) := by
  unfold dcandOK; infer_instance

/-- The possible entries of a data star of `t`. -/
def dcands (t : Finset (Fin n)) : Finset (DNbr (Fin p) (Fin q)) :=
  Finset.univ.filter (dcandOK O card t)

/-- A data star of `t` of length at most `dbnd O` over the possible
entries. -/
def DataSatS (t : Finset (Fin n)) : Prop :=
  ∃ Dn ∈ listsUpTo (dbnd O) (dcands O card t).val, DOK O card t Dn

instance (t : Finset (Fin n)) : Decidable (DataSatS O card t) := by
  unfold DataSatS; exact Multiset.decidableExistsMultiset

/-- **Data stars, decided.** -/
def dataSatB (t : Finset (Fin n)) : Bool :=
  decide (DataSatS O card t)

/-- The types with a data star. -/
def okTypes : Finset (Finset (Fin n)) :=
  Finset.univ.filter fun t => dataSatB O card t = true

/-- The starting set: every record that passes its own checks and whose
type has a data star. -/
def initD : Finset (QRec n m) :=
  (init (objPart O)).filter fun ρ => ρ.1 ∈ okTypes O card

/-- **Elimination with the oracle.** -/
def aliveD : Finset (QRec n m) :=
  eliminate (objPart O) (initD O card)

/-- The procedure's verdict on `a ⊑ b`. -/
def entailsQD (a b : Fin n) : Bool :=
  let G := aliveD O card
  decide (∀ ρ ∈ G, ρ.2 = none → a ∈ ρ.1 → b ∈ ρ.1)

/-- The procedure's verdict on the satisfiability of `a`. -/
def satQD (a : Fin n) : Bool :=
  let G := aliveD O card
  decide (∃ ρ ∈ G, ρ.2 = none ∧ a ∈ ρ.1)

/-- Every requested name with its subsumers. The alive records are
computed once. -/
def classifyQD (req : List (Fin n)) : List (Fin n × List (Fin n)) :=
  let G := aliveD O card
  req.map fun a => (a, (List.finRange n).filter fun b =>
    decide (∀ ρ ∈ G, ρ.2 = none → a ∈ ρ.1 → b ∈ ρ.1))

end Defs

section Facts

variable {O : Ontology (Fin n) (Fin m) (Fin p) (Fin q)} {card : Finset (Fin q) → Option Nat}

theorem dataSatB_iff (t : Finset (Fin n)) : dataSatB O card t = true ↔ DataSat O card t := by
  unfold dataSatB
  rw [decide_eq_true_iff]
  unfold DataSatS
  constructor
  · rintro ⟨Dn, -, h⟩
    exact ⟨Dn, h⟩
  · rintro ⟨Dn, h⟩
    obtain ⟨Dn', hs, hl, hc, h'⟩ := dsupport_bound h
    refine ⟨Dn', (mem_listsUpTo _ _).2 ⟨hl, fun e he => ?_⟩, h'⟩
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, hc e he⟩
    exact dDown_sublist (List.singleton_sublist.2 he) (dok_iff.1 h').1

theorem mem_okTypes {t : Finset (Fin n)} : t ∈ okTypes O card ↔ DataSat O card t := by
  rw [okTypes, Finset.mem_filter, dataSatB_iff]
  exact and_iff_right (Finset.mem_univ _)

theorem aliveD_spec :
    SRIQ.SelfSupp (objPart O) (↑(aliveD O card) : Set (QRec n m)) ∧
      ∀ ρ ∈ aliveD O card, DataSat O card ρ.1 := by
  obtain ⟨hsub, hfix, -⟩ := eliminate_spec (O := objPart O) (initD O card)
  refine ⟨fun ρ hρ => supports_of_supB ?_, fun ρ hρ => ?_⟩
  · have hρ' : ρ ∈ prune (objPart O) (aliveD O card) := by
      unfold aliveD
      rw [hfix]
      exact Finset.mem_coe.1 hρ
    exact (Finset.mem_filter.1 hρ').2
  · exact mem_okTypes.1 (Finset.mem_filter.1 (hsub hρ)).2

/-- **Exactness of elimination.** The alive records are exactly the good
ones. -/
theorem good_iff_mem_aliveD (ρ : QRec n m) : DGood O card ρ ↔ ρ ∈ aliveD O card := by
  classical
  constructor
  · rintro ⟨G, hρ, hG⟩
    obtain ⟨hS, hds⟩ := dselfSupp_iff.1 hG
    let S : Finset (QRec n m) := Finset.univ.filter (· ∈ G)
    have hSm : ∀ x ∈ G, x ∈ S := fun x hx => Finset.mem_filter.2 ⟨Finset.mem_univ _, hx⟩
    have hSG : ∀ x ∈ S, x ∈ G := fun x hx => (Finset.mem_filter.1 hx).2
    have hsub : S ⊆ initD O card := by
      intro x hx
      obtain ⟨C, hok, -⟩ := hS x (hSG x hx)
      refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, hok.closed,
        fun e he => hok.edge e (List.mem_append_left _ he)⟩, mem_okTypes.2 (hds x (hSG x hx))⟩
    have hsupp : ∀ x ∈ S, supB (objPart O) S x := by
      intro x hx
      obtain ⟨C, hC⟩ := hS x (hSG x hx)
      exact supB_of_supports hSm hC
    exact (eliminate_spec (O := objPart O) (initD O card)).2.2 S hsub hsupp (hSm ρ hρ)
  · intro h
    exact ⟨_, Finset.mem_coe.2 h, dselfSupp_iff.2 ⟨aliveD_spec.1, fun σ hσ =>
      aliveD_spec.2 σ (Finset.mem_coe.1 hσ)⟩⟩

variable {Θ : DataTheory (Fin q)}

theorem entailsQD_iff (hspec : OracleSpec Θ card) (hA : IsALCHIQ O) (a b : Fin n) :
    entailsQD O card a b = true ↔ EntailsSub Θ O a b := by
  rw [entailsSub_iff_dstar hspec O hA, entailsQD, decide_eq_true_iff]
  constructor
  · intro h t ht hat
    exact h _ ((good_iff_mem_aliveD _).1 ht) rfl hat
  · intro h ρ hρ hn hat
    obtain ⟨t, par⟩ := ρ
    simp only at hn hat ⊢
    subst hn
    exact h t ((good_iff_mem_aliveD _).2 hρ) hat

theorem satQD_iff (hspec : OracleSpec Θ card) (hA : IsALCHIQ O) (a : Fin n) :
    satQD O card a = false ↔ Unsat Θ O a := by
  rw [unsat_iff_no_dstar hspec O hA, satQD, decide_eq_false_iff_not]
  constructor
  · intro h t ht hat
    exact h ⟨_, (good_iff_mem_aliveD _).1 ht, rfl, hat⟩
  · rintro h ⟨⟨t, par⟩, hρ, hn, hat⟩
    simp only at hn hat
    subst hn
    exact h t ((good_iff_mem_aliveD _).2 hρ) hat

/-- **Classification with data.** For every data theory for which `card`
satisfies `OracleSpec`, each requested name comes with exactly its
subsumers. -/
theorem classifyQD_spec (hspec : OracleSpec Θ card) (hA : IsALCHIQ O) {req : List (Fin n)} :
    ∀ r ∈ classifyQD O card req, r.1 ∈ req ∧ ∀ b, b ∈ r.2 ↔ EntailsSub Θ O r.1 b := by
  intro r hr
  simp only [classifyQD, List.mem_map] at hr
  obtain ⟨a, ha, rfl⟩ := hr
  refine ⟨ha, fun b => ?_⟩
  simp only [List.mem_filter, List.mem_finRange, true_and]
  exact entailsQD_iff hspec hA a b

end Facts

end Proc

end ContextCalculus.SRIQD

#print axioms ContextCalculus.SRIQD.prune_bound
#print axioms ContextCalculus.SRIQD.dsupport_bound
#print axioms ContextCalculus.SRIQD.Proc.dataSatB_iff
#print axioms ContextCalculus.SRIQD.Proc.good_iff_mem_aliveD
#print axioms ContextCalculus.SRIQD.Proc.entailsQD_iff
#print axioms ContextCalculus.SRIQD.Proc.satQD_iff
#print axioms ContextCalculus.SRIQD.Proc.classifyQD_spec
