import ContextCalculus.SRIQN.C2a
import ContextCalculus.SRIQ.ABoxProcedure
import Mathlib.Data.Fintype.Pi

/-!
# Procedures for nominals (stage C2, design section 4)

`docs/V1.7.0-C2-NOMINALS-DESIGN.md`. Concepts `Fin n`, roles `Fin m`, a
core `Fin k` with types `ty`. Records relative to the core form a finite
type; `aliveN` eliminates unsupported records as `SRIQ.Proc.alive` does,
where a support now also picks core entries (any function from the core to
labels; the anchor gets none and no entry may count at its core element).
`good_iff_mem_aliveN`: the alive records are exactly the good ones.

* `checkRealisationN`: a hint is a core with explicit core children.
  Sound for every hint (`checkRealisationN_sound`), and every realisation
  gives a hint that checks (`checkRealisationN_complete`).
* `searchN`: every core with at most `max 1 |Nom|` elements, its types and
  labels, and children lists up to `bnd`. Exact on C2a ontologies
  (`searchN_iff`).
* `consistentN`: the hint first, else the search; exact on C2a for every
  hint (`consistentN_iff`).
-/

namespace ContextCalculus.SRIQN.Proc

open ContextCalculus.SRI (RoleT Interp)
open ContextCalculus.SRIQ (Nbr StarOK UpClosed EdgeOK cnt flipL nbrs RoleLe Closed mem_flipL
  lowerL upperL mem_upperL bnd contribB support_bound)
open ContextCalculus.SRIQ.Proc (QNbr listsUpTo mem_listsUpTo candOK mkLab mkLab_half mkLab_symm
  nbrsL nbrs_perm_nbrsL)

variable {n m k : Nat}

/-- Records relative to a core `Fin k`. -/
abbrev NRec (n m k : Nat) := RecN (Fin n) (Fin m) (Fin k)

section Decide

variable (B : SRIQ.Ontology (Fin n) (Fin m))

theorem counted_iff (u : Finset (Fin n)) (L : Finset (RoleT (Fin m))) (t : Finset (Fin n)) :
    Counted B u L t ↔ ∃ q ∈ upperL B, q.1 ∈ u ∧ q.2.2.1 ∈ L ∧ q.2.2.2 ∈ t := by
  constructor
  · rintro ⟨a, j, R, b, hcl, h1, h2, h3⟩
    exact ⟨(a, j, R, b), mem_upperL.2 hcl, h1, h2, h3⟩
  · rintro ⟨⟨a, j, R, b⟩, hq, h1, h2, h3⟩
    exact ⟨a, j, R, b, mem_upperL.1 hq, h1, h2, h3⟩

instance (u : Finset (Fin n)) (L : Finset (RoleT (Fin m))) (t : Finset (Fin n)) :
    Decidable (Counted B u L t) :=
  decidable_of_iff _ (counted_iff B u L t).symm

theorem nomOK_iff (N : List (Fin n)) (ty : Fin k → Finset (Fin n)) :
    NomOK N ty ↔ ∀ a ∈ N, (Finset.univ.filter fun c => a ∈ ty c).card = 1 := by
  refine forall_congr' fun a => forall_congr' fun _ => ?_
  rw [Finset.card_eq_one]
  constructor
  · rintro ⟨c, hc, hu⟩
    refine ⟨c, Finset.ext fun d => ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨hu d, fun h => h ▸ hc⟩
  · rintro ⟨c, hc⟩
    have hmem : ∀ d, a ∈ ty d ↔ d = c := fun d => by
      have := congrArg (d ∈ ·) hc
      simpa using this
    exact ⟨c, (hmem c).2 rfl, fun d hd => (hmem d).1 hd⟩

instance (N : List (Fin n)) (ty : Fin k → Finset (Fin n)) : Decidable (NomOK N ty) :=
  decidable_of_iff _ (nomOK_iff N ty).symm

instance (N : List (Fin n)) (X : Fin n) (cl : SRIQ.Clause (Fin n) (Fin m)) :
    Decidable (PosOK N X cl) := by
  cases cl <;> unfold PosOK <;> infer_instance

instance (O : Ontology (Fin n) (Fin m)) (X : Fin n) : Decidable (NomOnly O X) := by
  unfold NomOnly; infer_instance

theorem isC2a_iff (O : Ontology (Fin n) (Fin m)) :
    IsC2a O ↔ ∀ q ∈ lowerL (basePart O), q.1 ∉ noms O → ¬ NomOnly O q.1 →
      ∀ q' ∈ upperL (basePart O),
        q'.2.2.1.flip ∉ SRI.Proc.roleUp (SRIQ.sriPart (basePart O)) q.2.2.1 := by
  unfold IsC2a
  simp only [SRI.Proc.mem_roleUp]
  rfl

/-- `IsC2a` is decidable over `Fin n`, `Fin m`. -/
instance (O : Ontology (Fin n) (Fin m)) : Decidable (IsC2a O) :=
  decidable_of_iff _ (isC2a_iff O).symm

/-- A chain has length one. -/
def chainOneB : SRIQ.Clause (Fin n) (Fin m) → Bool
  | .chain body _ => body.length == 1
  | _ => true

theorem isALCHOIQ_iff (O : Ontology (Fin n) (Fin m)) :
    IsALCHOIQ O ↔ ∀ cl ∈ basePart O, chainOneB cl = true := by
  constructor
  · intro h cl hcl
    cases cl <;> simp only [chainOneB]
    simpa using h _ _ hcl
  · intro h body S hcl
    simpa [chainOneB] using h _ hcl

instance (O : Ontology (Fin n) (Fin m)) : Decidable (IsALCHOIQ O) := by
  refine decidable_of_iff _ (isALCHOIQ_iff O).symm

end Decide

/-! ## Elimination relative to a core -/

section Defs

variable (B : SRIQ.Ontology (Fin n) (Fin m)) (N : List (Fin n)) (ty : Fin k → Finset (Fin n))

/-- The core entries over `Fin k`, in the order of `finRange`. -/
def cEntriesL (ce : Fin k → Finset (RoleT (Fin m))) : List (QNbr n m) :=
  ((List.finRange k).filter fun d => decide (ce d ≠ ∅)).map fun d => (ce d, ty d)

/-- The conditions a record checks on itself. -/
def localOKN (ρ : NRec n m k) : Prop :=
  Closed B ρ.1 ∧ (∀ a ∈ N, a ∉ ρ.1) ∧ UpClosed B (parentE ty ρ.2).1 ∧
    EdgeOK B ρ.1 (parentE ty ρ.2)

instance (ρ : NRec n m k) : Decidable (localOKN B N ty ρ) := by
  unfold localOKN; infer_instance

/-- The conditions on the core entries. -/
def ceOK (ρ : NRec n m k) (ce : Fin k → Finset (RoleT (Fin m))) : Prop :=
  (∀ c, (∃ L, ρ.2 = .inr (c, L)) → ce c = ∅) ∧ ∀ d, ¬ Counted B (ty d) (flipL (ce d)) ρ.1

instance (ρ : NRec n m k) (ce : Fin k → Finset (RoleT (Fin m))) : Decidable (ceOK B ty ρ ce) := by
  unfold ceOK
  refine @instDecidableAnd _ _ ?_ inferInstance
  refine @Fintype.decidableForallFintype _ _ (fun c => ?_) _
  refine @instDecidableForall _ _ ?_ inferInstance
  rcases ρ with ⟨t, _ | ⟨c', L⟩⟩
  · exact isFalse (by simp)
  · exact decidable_of_iff (c' = c) (by simp)

/-- The tree child entries of a node of type `t` whose records are in `G`. -/
def candsN (G : Finset (NRec n m k)) (t : Finset (Fin n)) : Multiset (QNbr n m) :=
  (G.val.bind fun ρ => match ρ.2 with
    | .inl p => if p.2 = t then {(flipL p.1, ρ.1)} else 0
    | .inr _ => 0).filter (candOK B t)

/-- `ρ` has a support in `G` with children up to `bnd`. -/
def supBN (G : Finset (NRec n m k)) (ρ : NRec n m k) : Prop :=
  ∃ ce : Fin k → Finset (RoleT (Fin m)), ceOK B ty ρ ce ∧
    ∃ C ∈ listsUpTo (bnd B) (candsN B G ρ.1),
      StarOK B ρ.1 ((parentE ty ρ.2 :: cEntriesL ty ce) ++ C)

instance (G : Finset (NRec n m k)) (ρ : NRec n m k) : Decidable (supBN B ty G ρ) := by
  unfold supBN
  refine @Fintype.decidableExistsFintype _ _ (fun ce => ?_) _
  refine @instDecidableAnd _ _ inferInstance ?_
  exact Multiset.decidableExistsMultiset

def pruneN (G : Finset (NRec n m k)) : Finset (NRec n m k) :=
  G.filter (supBN B ty G)

/-- Remove unsupported records until stable. -/
def eliminateN (G : Finset (NRec n m k)) : Finset (NRec n m k) :=
  let G' := pruneN B ty G
  if h : G' = G then G else eliminateN G'
termination_by G.card
decreasing_by
  exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨Finset.filter_subset _ _, h⟩)

def initN : Finset (NRec n m k) := Finset.univ.filter (localOKN B N ty)

/-- The alive records relative to the core types `ty`. -/
def aliveN : Finset (NRec n m k) := eliminateN B ty (initN B N ty)

end Defs

section Facts

variable {B : SRIQ.Ontology (Fin n) (Fin m)} {N : List (Fin n)} {ty : Fin k → Finset (Fin n)}

theorem cEntries_perm (ce : Fin k → Finset (RoleT (Fin m))) :
    (cEntries ty ce).Perm (cEntriesL ty ce) := by
  unfold cEntries cEntriesL
  refine List.Perm.map _ (SRIQ.Proc.perm_of_nodup_mem (Finset.nodup_toList _)
    ((List.nodup_finRange _).filter _) fun c => ?_)
  simp

theorem mem_candsN {G : Finset (NRec n m k)} {t : Finset (Fin n)} {e : QNbr n m} :
    e ∈ candsN B G t ↔ childRecN t e ∈ G ∧ candOK B t e := by
  unfold candsN
  rw [Multiset.mem_filter, Multiset.mem_bind]
  refine and_congr_left fun _ => ⟨?_, ?_⟩
  · rintro ⟨⟨s, par⟩, hρ, he⟩
    cases par with
    | inr _ => simp at he
    | inl p =>
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
      simpa [childRecN, flipL_flipL] using hρ
  · intro h
    refine ⟨childRecN t e, h, ?_⟩
    simp [childRecN, flipL_flipL]

theorem supBN_mono {S G : Finset (NRec n m k)} (hSG : S ⊆ G) {ρ : NRec n m k}
    (h : supBN B ty S ρ) : supBN B ty G ρ := by
  obtain ⟨ce, hce, C, hC, hok⟩ := h
  refine ⟨ce, hce, C, ?_, hok⟩
  rw [mem_listsUpTo] at hC ⊢
  refine ⟨hC.1, fun e he => ?_⟩
  obtain ⟨h1, h2⟩ := mem_candsN.1 (hC.2 e he)
  exact mem_candsN.2 ⟨hSG h1, h2⟩

theorem supports_of_supBN {G : Finset (NRec n m k)} {ρ : NRec n m k} (hloc : ∀ a ∈ N, a ∉ ρ.1)
    (h : supBN B ty G ρ) :
    ∃ p : (Fin k → Finset (RoleT (Fin m))) × List (QNbr n m),
      SupportsN B N ty (↑G : Set (NRec n m k)) ρ p.1 p.2 := by
  obtain ⟨ce, ⟨hanc, hunc⟩, C, hC, hok⟩ := h
  refine ⟨(ce, C), hloc, fun c L h => hanc c ⟨L, h⟩, hunc, ?_, fun e he => ?_⟩
  · exact starOK_perm' (((cEntries_perm ce).symm.cons _).append_right C) hok
  · exact Finset.mem_coe.2 (mem_candsN.1 ((mem_listsUpTo _ _).1 hC |>.2 e he)).1

theorem supBN_of_supports {S : Set (NRec n m k)} {G : Finset (NRec n m k)}
    (hSG : ∀ x ∈ S, x ∈ G) {ρ : NRec n m k} {ce : Fin k → Finset (RoleT (Fin m))}
    {C : List (QNbr n m)} (h : SupportsN B N ty S ρ ce C) : supBN B ty G ρ := by
  have hok := starOK_perm' (((cEntries_perm ce).cons _).append_right C) h.star
  obtain ⟨C', hs, hl, hc, hok'⟩ := support_bound C hok
  refine ⟨ce, ⟨fun c ⟨L, hL⟩ => h.anchor c L hL, h.unc⟩, C',
    (mem_listsUpTo _ _).2 ⟨hl, fun e he => mem_candsN.2 ⟨hSG _ (h.kids e (hs.subset he)), ?_⟩⟩,
    hok'⟩
  have hedge := hok.edge e (List.mem_append_right _ (hs.subset he))
  exact ⟨hedge.1, hedge.2, hc e he⟩

theorem eliminateN_spec : ∀ G : Finset (NRec n m k),
    eliminateN B ty G ⊆ G ∧ pruneN B ty (eliminateN B ty G) = eliminateN B ty G ∧
    ∀ S ⊆ G, (∀ ρ ∈ S, supBN B ty S ρ) → S ⊆ eliminateN B ty G := by
  intro G
  induction h : G.card using Nat.strong_induction_on generalizing G with
  | _ j ih =>
    rw [eliminateN]
    split_ifs with hp
    · exact ⟨Finset.Subset.refl _, hp, fun S hS _ => hS⟩
    · have hlt : (pruneN B ty G).card < j := h ▸
        Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨Finset.filter_subset _ _, hp⟩)
      obtain ⟨h1, h2, h3⟩ := ih _ hlt _ rfl
      refine ⟨h1.trans (Finset.filter_subset _ _), h2, fun S hS hw => h3 S ?_ hw⟩
      intro ρ hρ
      exact Finset.mem_filter.2 ⟨hS hρ, supBN_mono hS (hw ρ hρ)⟩

theorem aliveN_supBN {ρ : NRec n m k} (hρ : ρ ∈ aliveN B N ty) : supBN B ty (aliveN B N ty) ρ := by
  have h := (eliminateN_spec (B := B) (ty := ty) (initN B N ty)).2.1
  unfold aliveN at hρ ⊢
  rw [← h] at hρ
  exact (Finset.mem_filter.1 hρ).2

theorem aliveN_init {ρ : NRec n m k} (hρ : ρ ∈ aliveN B N ty) : ρ ∈ initN B N ty :=
  (eliminateN_spec (B := B) (ty := ty) (initN B N ty)).1 hρ

theorem aliveN_selfSupp : SelfSuppN B N ty (↑(aliveN B N ty) : Set (NRec n m k)) := by
  intro ρ hρ
  have hρ' := Finset.mem_coe.1 hρ
  exact supports_of_supBN (Finset.mem_filter.1 (aliveN_init hρ')).2.2.1 (aliveN_supBN hρ')

/-- **Exactness of elimination.** The alive records are exactly the good
ones. -/
theorem good_iff_mem_aliveN (ρ : NRec n m k) : GoodN B N ty ρ ↔ ρ ∈ aliveN B N ty := by
  classical
  constructor
  · rintro ⟨G, hρ, hG⟩
    let S : Finset (NRec n m k) := Finset.univ.filter (· ∈ G)
    have hS : ∀ x ∈ G, x ∈ S := fun x hx => Finset.mem_filter.2 ⟨Finset.mem_univ _, hx⟩
    have hSG : ∀ x ∈ S, x ∈ G := fun x hx => (Finset.mem_filter.1 hx).2
    have hsub : S ⊆ initN B N ty := by
      intro x hx
      obtain ⟨p, hp⟩ := hG x (hSG x hx)
      have he := hp.star.edge _ (List.mem_append_left _ List.mem_cons_self)
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hp.star.closed, hp.noNom, he.1, he.2⟩
    have hsupp : ∀ x ∈ S, supBN B ty S x := by
      intro x hx
      obtain ⟨p, hp⟩ := hG x (hSG x hx)
      exact supBN_of_supports hS hp
    exact (eliminateN_spec (B := B) (ty := ty) (initN B N ty)).2.2 S hsub hsupp (hS ρ hρ)
  · intro h
    exact ⟨_, Finset.mem_coe.2 h, aliveN_selfSupp⟩

end Facts

/-! ## Hints and the search -/

section Check

variable (B : SRIQ.Ontology (Fin n) (Fin m)) (N : List (Fin n))

/-- A hint: a core over `Fin k` with types, labels and explicit children. -/
structure HintN (n m : Nat) where
  k : Nat
  ty : Fin k → Finset (Fin n)
  lab : Fin k → Fin k → Finset (RoleT (Fin m))
  kids : Fin k → List (QNbr n m)

/-- The core conditions other than the children. -/
def coreOKN (ty : Fin k → Finset (Fin n)) (lab : Fin k → Fin k → Finset (RoleT (Fin m))) : Prop :=
  (∀ b c, lab c b = flipL (lab b c)) ∧ NomOK N ty

instance (ty : Fin k → Finset (Fin n)) (lab : Fin k → Fin k → Finset (RoleT (Fin m))) :
    Decidable (coreOKN N ty lab) := by
  unfold coreOKN; infer_instance

/-- The explicit children of a core element check against `G`. -/
def kidsOKN (G : Finset (NRec n m k)) (ty : Fin k → Finset (Fin n))
    (lab : Fin k → Fin k → Finset (RoleT (Fin m))) (b : Fin k) (C : List (QNbr n m)) : Prop :=
  StarOK B (ty b) (nbrsL ty lab b ++ C) ∧ ∀ e ∈ C, anchorRec b e ∈ G

instance (G : Finset (NRec n m k)) (ty : Fin k → Finset (Fin n))
    (lab : Fin k → Fin k → Finset (RoleT (Fin m))) (b : Fin k) (C : List (QNbr n m)) :
    Decidable (kidsOKN B G ty lab b C) := by
  unfold kidsOKN; infer_instance

/-- **Hint check.** -/
def checkRealisationN (h : HintN n m) : Bool :=
  let G := aliveN B N h.ty
  decide (0 < h.k ∧ coreOKN N h.ty h.lab ∧ ∀ b, kidsOKN B G h.ty h.lab b (h.kids b))

/-- The anchor child entries of core element `b` of type `t` with records
in `G`. -/
def candsA (G : Finset (NRec n m k)) (b : Fin k) (t : Finset (Fin n)) : Multiset (QNbr n m) :=
  (G.val.bind fun ρ => match ρ.2 with
    | .inl _ => 0
    | .inr (c, L) => if c = b then {(flipL L, ρ.1)} else 0).filter (candOK B t)

/-- A core element has children up to `bnd` over the candidates in `G`. -/
def supBlkN (G : Finset (NRec n m k)) (ty : Fin k → Finset (Fin n))
    (lab : Fin k → Fin k → Finset (RoleT (Fin m))) (b : Fin k) : Prop :=
  ∃ C ∈ listsUpTo (bnd B) (candsA B G b (ty b)), StarOK B (ty b) (nbrsL ty lab b ++ C)

instance (G : Finset (NRec n m k)) (ty : Fin k → Finset (Fin n))
    (lab : Fin k → Fin k → Finset (RoleT (Fin m))) (b : Fin k) :
    Decidable (supBlkN B G ty lab b) := by
  unfold supBlkN; exact Multiset.decidableExistsMultiset

/-- All sets of names. -/
def allTypesN (n : Nat) : List (Finset (Fin n)) :=
  (List.finRange n).sublists.map List.toFinset

/-- All functions from `Fin k` into the members of `L`. -/
def funsL {α : Type} (L : List α) : (k : Nat) → List (Fin k → α)
  | 0 => [Fin.elim0]
  | k + 1 => (funsL L k).flatMap fun f => L.map fun x => Fin.cons x f

/-- The labels of the search for fixed core types and alive records `G`. -/
def LabProp {k : Nat} (G : Finset (NRec n m (k + 1))) (ty : Fin (k + 1) → Finset (Fin n)) : Prop :=
  ∃ half : {p : Fin (k + 1) × Fin (k + 1) // p.1 ≤ p.2} → Finset (RoleT (Fin m)),
    (∀ b, mkLab half b b = flipL (mkLab half b b)) ∧ ∀ b, supBlkN B G ty (mkLab half) b

set_option synthInstance.maxHeartbeats 200000 in
set_option synthInstance.maxSize 1024 in
instance {k : Nat} (G : Finset (NRec n m (k + 1))) (ty : Fin (k + 1) → Finset (Fin n)) :
    Decidable (LabProp B G ty) := by
  unfold LabProp; infer_instance

/-- The checks for fixed core types; the alive records are computed once. -/
def tyCheck {k : Nat} (ty : Fin (k + 1) → Finset (Fin n)) : Bool :=
  decide (NomOK N ty) && (let G := aliveN B N ty; decide (LabProp B G ty))

/-- The search space of C2a: at most `max 1 |Nom|` core elements, closed
types with each nominal name in exactly one, labels on the pairs `b ≤ c`. -/
def SearchPropN : Prop :=
  ∃ j ∈ List.range (max 1 N.toFinset.card),
    ∃ ty ∈ funsL ((allTypesN n).filter fun t => decide (Closed B t)) (j + 1),
      tyCheck B N ty = true

instance : Decidable (SearchPropN B N) := by
  unfold SearchPropN; infer_instance

/-- **Exhaustive search (C2a).** -/
def searchN : Bool := decide (SearchPropN B N)

/-- **Consistency with a hint.** -/
def consistentN (hint : Option (HintN n m)) : Bool :=
  hint.any (checkRealisationN B N) || searchN B N

end Check

section CheckFacts

variable {B : SRIQ.Ontology (Fin n) (Fin m)} {N : List (Fin n)}

theorem mem_candsA {G : Finset (NRec n m k)} {b : Fin k} {t : Finset (Fin n)} {e : QNbr n m} :
    e ∈ candsA B G b t ↔ anchorRec b e ∈ G ∧ candOK B t e := by
  unfold candsA
  rw [Multiset.mem_filter, Multiset.mem_bind]
  refine and_congr_left fun _ => ⟨?_, ?_⟩
  · rintro ⟨⟨s, par⟩, hρ, he⟩
    cases par with
    | inl _ => simp at he
    | inr p =>
      obtain ⟨c, L⟩ := p
      simp only at he
      by_cases hc : c = b
      swap
      · rw [if_neg hc] at he
        simp at he
      rw [if_pos hc, Multiset.mem_singleton] at he
      subst he hc
      simpa [anchorRec, flipL_flipL] using hρ
  · intro h
    refine ⟨anchorRec b e, h, ?_⟩
    simp [anchorRec, flipL_flipL]

/-- A realisation over `Fin k` from the core conditions and children with
good anchor records. -/
def realOfCoreN {ty : Fin k → Finset (Fin n)} {lab : Fin k → Fin k → Finset (RoleT (Fin m))}
    (hc : coreOKN N ty lab)
    (hk : ∀ b, ∃ C, StarOK B (ty b) (nbrsL ty lab b ++ C) ∧ ∀ e ∈ C, GoodN B N ty (anchorRec b e)) :
    RealisationN B N (Fin k) where
  ty := ty
  lab := lab
  symm := hc.1
  nom := hc.2
  kids b := by
    obtain ⟨C, hok, hC⟩ := hk b
    exact ⟨C, starOK_perm' ((nbrs_perm_nbrsL ty lab b).symm.append_right C) hok, hC⟩

/-- **Soundness of the hint check**, for every hint. -/
theorem checkRealisationN_sound {O : Ontology (Fin n) (Fin m)} (hA : IsALCHOIQ O) (h : HintN n m)
    (hc : checkRealisationN (basePart O) (noms O) h = true) : ConsistentN O := by
  obtain ⟨hpos, hcore, hkids⟩ := of_decide_eq_true hc
  haveI : Nonempty (Fin h.k) := ⟨⟨0, hpos⟩⟩
  refine realisation_sound hA (realOfCoreN hcore fun b => ⟨h.kids b, (hkids b).1, fun e he => ?_⟩)
  exact (good_iff_mem_aliveN _).2 ((hkids b).2 e he)

/-- **Completeness of the hint check.** Every realisation over a nonempty
`Fin k` gives a hint that checks. -/
theorem checkRealisationN_complete {k : Nat} (hk : 0 < k) (r : RealisationN B N (Fin k)) :
    ∃ h : HintN n m, checkRealisationN B N h = true := by
  classical
  let C : Fin k → List (QNbr n m) := fun b => (r.kids b).choose
  refine ⟨⟨k, r.ty, r.lab, C⟩, decide_eq_true ⟨hk, ⟨r.symm, r.nom⟩, fun b => ?_⟩⟩
  obtain ⟨hok, hgood⟩ := (r.kids b).choose_spec
  exact ⟨starOK_perm' ((nbrs_perm_nbrsL r.ty r.lab b).append_right _) hok,
    fun e he => (good_iff_mem_aliveN _).1 (hgood e he)⟩

theorem supBlkN_of_real {k : Nat} (r : RealisationN B N (Fin k)) (b : Fin k) :
    supBlkN B (aliveN B N r.ty) r.ty r.lab b := by
  obtain ⟨C, hok, hC⟩ := r.kids b
  have hok' := starOK_perm' ((nbrs_perm_nbrsL r.ty r.lab b).append_right C) hok
  obtain ⟨C', hs, hl, hcb, hok''⟩ := support_bound C hok'
  refine ⟨C', (mem_listsUpTo _ _).2 ⟨hl, fun e he => mem_candsA.2 ⟨?_, ?_⟩⟩, hok''⟩
  · exact (good_iff_mem_aliveN _).1 (hC e (hs.subset he))
  · have hedge := hok'.edge e (List.mem_append_right _ (hs.subset he))
    exact ⟨hedge.1, hedge.2, hcb e he⟩

/-- **Exactness of the search on C2a.** -/
theorem mem_allTypesN (t : Finset (Fin n)) : t ∈ allTypesN n := by
  refine List.mem_map.2 ⟨(List.finRange n).filter (· ∈ t), List.mem_sublists.2 List.filter_sublist,
    ?_⟩
  ext a
  simp

theorem mem_funsL {α : Type} {L : List α} : ∀ {k : Nat} (f : Fin k → α), (∀ i, f i ∈ L) →
    f ∈ funsL L k
  | 0, f, _ => by
    have : f = Fin.elim0 := funext fun i => i.elim0
    simp [funsL, this]
  | k + 1, f, hf => by
    refine List.mem_flatMap.2 ⟨Fin.tail f, mem_funsL _ fun i => hf _, ?_⟩
    exact List.mem_map.2 ⟨f 0, hf 0, Fin.cons_self_tail f⟩

theorem searchN_iff {O : Ontology (Fin n) (Fin m)} (hA : IsALCHOIQ O) (hC : IsC2a O) :
    searchN (basePart O) (noms O) = true ↔ ConsistentN O := by
  unfold searchN
  rw [decide_eq_true_iff]
  constructor
  · rintro ⟨j, -, ty, -, hchk⟩
    simp only [tyCheck, Bool.and_eq_true, decide_eq_true_eq] at hchk
    obtain ⟨hnom, half, hd, hs⟩ := hchk
    have hc : coreOKN (noms O) ty (mkLab half) := ⟨mkLab_symm hd, hnom⟩
    haveI : Nonempty (Fin (j + 1)) := ⟨0⟩
    refine realisation_sound hA (realOfCoreN hc fun b => ?_)
    obtain ⟨C, hCm, hok⟩ := hs b
    refine ⟨C, hok, fun e he => (good_iff_mem_aliveN _).2 ?_⟩
    exact (mem_candsA.1 ((mem_listsUpTo _ _).1 hCm |>.2 e he)).1
  · intro hc
    obtain ⟨k, hk, hle, r, -⟩ := c2a_complete hC hc
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    refine ⟨j, List.mem_range.2 (by omega), r.ty, mem_funsL _ fun b => List.mem_filter.2
      ⟨mem_allTypesN _, decide_eq_true (r.kids b).choose_spec.1.closed⟩, ?_⟩
    simp only [tyCheck, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨r.nom, fun p => r.lab p.1.1 p.1.2, ?_, ?_⟩
    · intro b
      rw [mkLab_half r.symm]
      exact r.symm b b
    · intro b
      rw [mkLab_half r.symm]
      exact supBlkN_of_real r b

/-- **Consistency with a hint is exact on C2a, for every hint.** -/
theorem consistentN_iff {O : Ontology (Fin n) (Fin m)} (hA : IsALCHOIQ O) (hC : IsC2a O)
    (hint : Option (HintN n m)) :
    consistentN (basePart O) (noms O) hint = true ↔ ConsistentN O := by
  unfold consistentN
  rw [Bool.or_eq_true, searchN_iff hA hC]
  constructor
  · rintro (h | h)
    · cases hint with
      | none => simp at h
      | some h' => exact checkRealisationN_sound hA h' (by simpa using h)
    · exact h
  · exact Or.inr

end CheckFacts

end ContextCalculus.SRIQN.Proc

#print axioms ContextCalculus.SRIQN.Proc.good_iff_mem_aliveN
#print axioms ContextCalculus.SRIQN.Proc.checkRealisationN_sound
#print axioms ContextCalculus.SRIQN.Proc.checkRealisationN_complete
#print axioms ContextCalculus.SRIQN.Proc.searchN_iff
#print axioms ContextCalculus.SRIQN.Proc.consistentN_iff
