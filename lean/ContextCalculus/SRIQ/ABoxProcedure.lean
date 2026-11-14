import ContextCalculus.SRIQ.ABox
import ContextCalculus.SRIQ.Procedure
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Option

/-!
# A procedure for ALCHIQ knowledge bases with a hint (stage C1b, design section 5)

`docs/V1.7.0-C1B-ABOX-DESIGN.md`. Concepts are `Fin n`, roles `Fin m`,
individuals `Fin k`. A hint is a concrete realisation over the blocks
`Fin nb`: block map, types, labels and explicit children lists.

* `checkRealisation` checks a hint, using `alive` for the goodness of the
  children records. Sound: `true` implies `ConsistentKB`
  (`checkRealisation_sound`).
* `searchKB` searches every realisation with at most `k + 1` blocks,
  with children lists up to the bound of `support_bound` over the alive
  candidates. Exact (`searchKB_iff`), and far too slow for real inputs.
* `consistentKB` answers `true` if the hint checks, else runs
  `searchKB`; it equals `ConsistentKB` for every hint
  (`consistentKB_iff`).
* `classifyKB` gives the `classifyQ` rows for a consistent knowledge base
  and every name as a subsumer of each requested name otherwise
  (`classifyKB_spec`, against `EntailsSubKB`).
* `consistentKBQ` and `consistentKBQ_iff`: the same for SHIQ knowledge
  bases, after `encTransQ`.
-/

namespace ContextCalculus.SRIQ.Proc

open ContextCalculus.SRI (RoleT Interp)
open ContextCalculus.SRIQ

variable {n m k : Nat}

/-! ## Stars up to permutation -/

theorem starOK_perm {O : Ontology (Fin n) (Fin m)} {t : Finset (Fin n)} {N N' : List (QNbr n m)}
    (hp : N.Perm N') (h : StarOK O t N) : StarOK O t N' := by
  have hc : ∀ R b, cnt N' R b = cnt N R b := fun R b => (hp.countP_eq _).symm
  exact ⟨h.closed, fun e he => h.edge e (hp.symm.subset he),
    fun a R b hcl ha => (hc R b).symm ▸ h.ex a R b hcl ha,
    fun a j R b hcl ha => (hc R b).symm ▸ h.atLeast a j R b hcl ha,
    fun a j R b hcl ha => (hc R b).symm ▸ h.atMost a j R b hcl ha⟩

/-- Two duplicate-free lists with the same members are permutations. -/
theorem perm_of_nodup_mem {α : Type} {l l' : List α} (h : l.Nodup) (h' : l'.Nodup)
    (hm : ∀ x, x ∈ l ↔ x ∈ l') : l.Perm l' :=
  (List.perm_ext_iff_of_nodup h h').2 hm

/-- `nbrs` changes only up to permutation along an equivalence of blocks. -/
theorem nbrs_equiv {B B' : Type} [Fintype B] [Fintype B'] (e : B ≃ B')
    (ty : B → Finset (Fin n)) (lab : B → B → Finset (RoleT (Fin m))) (b : B') :
    (nbrs (fun c => ty (e.symm c)) (fun c d => lab (e.symm c) (e.symm d)) b).Perm
      (nbrs ty lab (e.symm b)) := by
  classical
  unfold nbrs
  have hp : ((Finset.univ.filter fun c => lab (e.symm b) (e.symm c) ≠ ∅).toList).Perm
      (((Finset.univ.filter fun c => lab (e.symm b) c ≠ ∅).toList).map e) := by
    refine perm_of_nodup_mem (Finset.nodup_toList _) ((Finset.nodup_toList _).map e.injective)
      fun c => ?_
    simp only [Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and, List.mem_map]
    constructor
    · intro h
      exact ⟨e.symm c, h, e.apply_symm_apply c⟩
    · rintro ⟨d, hd, rfl⟩
      simpa using hd
  refine (hp.map _).trans ?_
  rw [List.map_map]
  refine List.Perm.of_eq (List.map_congr_left fun c _ => ?_)
  simp

/-- A realisation moves along an equivalence of blocks. -/
def _root_.ContextCalculus.SRIQ.Realisation.equiv {Ind : Type} {O : Ontology (Fin n) (Fin m)}
    {A : ABox (Fin n) (Fin m) Ind} {B B' : Type} [Fintype B] [Fintype B']
    (ρ : Realisation O A B) (e : B ≃ B') : Realisation O A B' where
  blk a := e (ρ.blk a)
  ty c := ρ.ty (e.symm c)
  lab c d := ρ.lab (e.symm c) (e.symm d)
  up c d := ρ.up _ _
  symm c d := ρ.symm _ _
  cls a X h := by simpa using ρ.cls a X h
  role a R b h := by simpa using ρ.role a R b h
  nrole a R b h := by simpa using ρ.nrole a R b h
  same a b h := by rw [ρ.same a b h]
  diff a b h he := ρ.diff a b h (e.injective he)
  kids b := by
    obtain ⟨C, hok, hC⟩ := ρ.kids (e.symm b)
    exact ⟨C, starOK_perm ((nbrs_equiv e ρ.ty ρ.lab b).symm.append_right C) hok, hC⟩

/-! ## Checking a realisation over `Fin nb` -/

section Defs

variable (O : Ontology (Fin n) (Fin m)) (A : ABox (Fin n) (Fin m) (Fin k))

/-- A hint: a realisation over the blocks `Fin nb` with explicit children. -/
structure Hint (n m k : Nat) where
  nb : Nat
  blk : Fin k → Fin nb
  ty : Fin nb → Finset (Fin n)
  lab : Fin nb → Fin nb → Finset (RoleT (Fin m))
  kids : Fin nb → List (QNbr n m)

/-- The named neighbours over `Fin nb`, in the order of `finRange`. -/
def nbrsL {nb : Nat} (ty : Fin nb → Finset (Fin n)) (lab : Fin nb → Fin nb → Finset (RoleT (Fin m)))
    (b : Fin nb) : List (QNbr n m) :=
  ((List.finRange nb).filter fun c => decide (lab b c ≠ ∅)).map fun c => (lab b c, ty c)

/-- An assertion holds in the blocks. -/
def assertOK {nb : Nat} (blk : Fin k → Fin nb) (ty : Fin nb → Finset (Fin n))
    (lab : Fin nb → Fin nb → Finset (RoleT (Fin m))) : Assertion (Fin n) (Fin m) (Fin k) → Prop
  | .cls a X => X ∈ ty (blk a)
  | .role a R b => R ∈ lab (blk a) (blk b)
  | .nrole a R b => R ∉ lab (blk a) (blk b)
  | .same a b => blk a = blk b
  | .diff a b => blk a ≠ blk b

instance {nb : Nat} (blk : Fin k → Fin nb) (ty : Fin nb → Finset (Fin n))
    (lab : Fin nb → Fin nb → Finset (RoleT (Fin m))) (as : Assertion (Fin n) (Fin m) (Fin k)) :
    Decidable (assertOK blk ty lab as) := by
  cases as <;> unfold assertOK <;> infer_instance

/-- The conditions of a realisation other than the children. -/
def coreOK {nb : Nat} (blk : Fin k → Fin nb) (ty : Fin nb → Finset (Fin n))
    (lab : Fin nb → Fin nb → Finset (RoleT (Fin m))) : Prop :=
  (∀ b c, UpClosed O (lab b c)) ∧ (∀ b c, lab c b = flipL (lab b c)) ∧
    ∀ as ∈ A, assertOK blk ty lab as

instance {nb : Nat} (blk : Fin k → Fin nb) (ty : Fin nb → Finset (Fin n))
    (lab : Fin nb → Fin nb → Finset (RoleT (Fin m))) : Decidable (coreOK O A blk ty lab) := by
  unfold coreOK; infer_instance

/-- The explicit children of a block check, with `G` for the alive records. -/
def kidsOK (G : Finset (QRec n m)) {nb : Nat} (ty : Fin nb → Finset (Fin n))
    (lab : Fin nb → Fin nb → Finset (RoleT (Fin m))) (b : Fin nb) (C : List (QNbr n m)) : Prop :=
  StarOK O (ty b) (nbrsL ty lab b ++ C) ∧ ∀ e ∈ C, childRec (ty b) e ∈ G

instance (G : Finset (QRec n m)) {nb : Nat} (ty : Fin nb → Finset (Fin n))
    (lab : Fin nb → Fin nb → Finset (RoleT (Fin m))) (b : Fin nb) (C : List (QNbr n m)) :
    Decidable (kidsOK O G ty lab b C) := by
  unfold kidsOK; infer_instance

/-- **Hint check.** The alive records are computed once. -/
def checkRealisation (h : Hint n m k) : Bool :=
  let G := alive O
  decide (0 < h.nb ∧ coreOK O A h.blk h.ty h.lab ∧ ∀ b, kidsOK O G h.ty h.lab b (h.kids b))

/-- A block has a children list of length at most `bnd O` over the
candidates in `G`. -/
def supBlk (G : Finset (QRec n m)) {nb : Nat} (ty : Fin nb → Finset (Fin n))
    (lab : Fin nb → Fin nb → Finset (RoleT (Fin m))) (b : Fin nb) : Prop :=
  ∃ C ∈ listsUpTo (bnd O) (cands O G (ty b)), StarOK O (ty b) (nbrsL ty lab b ++ C)

instance (G : Finset (QRec n m)) {nb : Nat} (ty : Fin nb → Finset (Fin n))
    (lab : Fin nb → Fin nb → Finset (RoleT (Fin m))) (b : Fin nb) :
    Decidable (supBlk O G ty lab b) := by
  unfold supBlk; exact Multiset.decidableExistsMultiset

/-- The equality and inequality assertions hold in the block map. -/
def idOK {nb : Nat} (blk : Fin k → Fin nb) : Assertion (Fin n) (Fin m) (Fin k) → Prop
  | .same a b => blk a = blk b
  | .diff a b => blk a ≠ blk b
  | _ => True

instance {nb : Nat} (blk : Fin k → Fin nb) (as : Assertion (Fin n) (Fin m) (Fin k)) :
    Decidable (idOK blk as) := by
  cases as <;> unfold idOK <;> infer_instance

/-- The class assertions hold in the types. -/
def clsOK {nb : Nat} (blk : Fin k → Fin nb) (ty : Fin nb → Finset (Fin n)) :
    Assertion (Fin n) (Fin m) (Fin k) → Prop
  | .cls a X => X ∈ ty (blk a)
  | _ => True

instance {nb : Nat} (blk : Fin k → Fin nb) (ty : Fin nb → Finset (Fin n))
    (as : Assertion (Fin n) (Fin m) (Fin k)) : Decidable (clsOK blk ty as) := by
  cases as <;> unfold clsOK <;> infer_instance

/-- A label function from its values on the pairs `b ≤ c`. -/
def mkLab {nb : Nat} (half : {p : Fin nb × Fin nb // p.1 ≤ p.2} → Finset (RoleT (Fin m)))
    (b c : Fin nb) : Finset (RoleT (Fin m)) :=
  if h : b ≤ c then half ⟨(b, c), h⟩ else flipL (half ⟨(c, b), (not_le.1 h).le⟩)

/-- The search space: `j + 1 ≤ max 1 k` blocks, block maps onto the blocks
(when there are individuals), closed types, and labels given on the
pairs `b ≤ c`. The cheap conditions come first. -/
def SearchProp (G : Finset (QRec n m)) : Prop :=
  ∃ j : Fin (max 1 k), ∃ blk : Fin k → Fin (j.val + 1),
    (k = 0 ∨ Function.Surjective blk) ∧ (∀ as ∈ A, idOK blk as) ∧
    ∃ ty : Fin (j.val + 1) → Finset (Fin n), (∀ b, Closed O (ty b)) ∧ (∀ as ∈ A, clsOK blk ty as) ∧
      ∃ half : {p : Fin (j.val + 1) × Fin (j.val + 1) // p.1 ≤ p.2} → Finset (RoleT (Fin m)),
        coreOK O A blk ty (mkLab half) ∧ ∀ b, supBlk O G ty (mkLab half) b

instance (G : Finset (QRec n m)) : Decidable (SearchProp O A G) := by
  unfold SearchProp; infer_instance

/-- **Exhaustive search.** The alive records are computed once. -/
def searchKB : Bool :=
  let G := alive O
  decide (SearchProp O A G)

/-- **Consistency with a hint.** `true` if the hint checks, else the search. -/
def consistentKB (hint : Option (Hint n m k)) : Bool :=
  hint.any (checkRealisation O A) || searchKB O A

/-- **Classification with an ABox.** -/
def classifyKB (hint : Option (Hint n m k)) (req : List (Fin n)) :
    List (Fin n × List (Fin n)) :=
  if consistentKB O A hint then classifyQ O req else req.map fun a => (a, List.finRange n)

end Defs

/-! ## Correctness -/

section Facts

variable {O : Ontology (Fin n) (Fin m)} {A : ABox (Fin n) (Fin m) (Fin k)}

theorem nbrs_perm_nbrsL {nb : Nat} (ty : Fin nb → Finset (Fin n))
    (lab : Fin nb → Fin nb → Finset (RoleT (Fin m))) (b : Fin nb) :
    (nbrs ty lab b).Perm (nbrsL ty lab b) := by
  unfold nbrs nbrsL
  refine List.Perm.map _ (perm_of_nodup_mem (Finset.nodup_toList _)
    ((List.nodup_finRange _).filter _) fun c => ?_)
  simp

/-- A realisation over `Fin nb` from the core conditions and children with
good records. -/
def realOfCore {nb : Nat} {blk : Fin k → Fin nb} {ty : Fin nb → Finset (Fin n)}
    {lab : Fin nb → Fin nb → Finset (RoleT (Fin m))} (hc : coreOK O A blk ty lab)
    (hk : ∀ b, ∃ C, StarOK O (ty b) (nbrsL ty lab b ++ C) ∧ ∀ e ∈ C, Good O (childRec (ty b) e)) :
    Realisation O A (Fin nb) where
  blk := blk
  ty := ty
  lab := lab
  up := hc.1
  symm := hc.2.1
  cls a X h := hc.2.2 _ h
  role a R b h := hc.2.2 _ h
  nrole a R b h := hc.2.2 _ h
  same a b h := hc.2.2 _ h
  diff a b h := hc.2.2 _ h
  kids b := by
    obtain ⟨C, hok, hC⟩ := hk b
    exact ⟨C, starOK_perm ((nbrs_perm_nbrsL ty lab b).symm.append_right C) hok, hC⟩

theorem core_of_real {nb : Nat} (ρ : Realisation O A (Fin nb)) :
    coreOK O A ρ.blk ρ.ty ρ.lab ∧ ∀ b, supBlk O (alive O) ρ.ty ρ.lab b := by
  refine ⟨⟨ρ.up, ρ.symm, fun as has => ?_⟩, fun b => ?_⟩
  · cases as with
    | cls a X => exact ρ.cls a X has
    | role a R b => exact ρ.role a R b has
    | nrole a R b => exact ρ.nrole a R b has
    | same a b => exact ρ.same a b has
    | diff a b => exact ρ.diff a b has
  · obtain ⟨C, hok, hC⟩ := ρ.kids b
    have hok' := starOK_perm ((nbrs_perm_nbrsL ρ.ty ρ.lab b).append_right C) hok
    obtain ⟨C', hs, hl, hcb, hok''⟩ := support_bound C hok'
    refine ⟨C', (mem_listsUpTo _ _).2 ⟨hl, fun e he => mem_cands.2 ⟨?_, ?_⟩⟩, hok''⟩
    · exact (good_iff_mem_alive _).1 (hC e (hs.subset he))
    · have hedge := hok'.edge e (List.mem_append_right _ (hs.subset he))
      exact ⟨hedge.1, hedge.2, hcb e he⟩

/-- **Soundness of the hint check.** -/
theorem checkRealisation_sound (hA : IsALCHIQ O) (h : Hint n m k)
    (hc : checkRealisation O A h = true) : ConsistentKB O A := by
  obtain ⟨hpos, hcore, hkids⟩ := of_decide_eq_true (p := 0 < h.nb ∧ coreOK O A h.blk h.ty h.lab ∧
    ∀ b, kidsOK O (alive O) h.ty h.lab b (h.kids b)) hc
  refine (consistentKB_iff_realisation O hA A).2 ⟨Fin h.nb, inferInstance, ⟨⟨0, hpos⟩⟩,
    ⟨realOfCore hcore fun b => ⟨h.kids b, (hkids b).1, fun e he => ?_⟩⟩⟩
  exact (good_iff_mem_alive _).2 ((hkids b).2 e he)

theorem card_blockSet_le {Ind D : Type} [Fintype Ind] (ind : Ind → D) (x0 : D)
    [Fintype (blockSet ind x0)] : Fintype.card (blockSet ind x0) ≤ Fintype.card Ind + 1 := by
  have hsurj : Function.Surjective fun o : Option Ind =>
      (match o with
       | none => ⟨x0, Or.inl rfl⟩
       | some a => ⟨ind a, Or.inr ⟨a, rfl⟩⟩ : blockSet ind x0) := by
    rintro ⟨x, rfl | ⟨a, rfl⟩⟩
    · exact ⟨none, rfl⟩
    · exact ⟨some a, rfl⟩
  have hle := Fintype.card_le_of_surjective _ hsurj
  rwa [Fintype.card_option] at hle

/-- A model gives a realisation over `Fin (j + 1)` with `j + 1 ≤ max 1 k`,
whose block map is onto when there are individuals. -/
theorem exists_small_realisation (hc : ConsistentKB O A) :
    ∃ j : Fin (max 1 k), ∃ ρ : Realisation O A (Fin (j.val + 1)),
      k = 0 ∨ Function.Surjective ρ.blk := by
  classical
  obtain ⟨D, ⟨x1⟩, I, ind, hI, hAs⟩ := hc
  -- with individuals, the extra block is the first individual
  let x0 : D := if hk : 0 < k then ind ⟨0, hk⟩ else x1
  haveI : Finite (blockSet ind x0) := (blockSet_finite ind x0).to_subtype
  letI : Fintype (blockSet ind x0) := Fintype.ofFinite _
  have hpos : 0 < Fintype.card (blockSet ind x0) :=
    Fintype.card_pos_iff.2 ⟨⟨x0, Or.inl rfl⟩⟩
  have hsurj : 0 < k → Function.Surjective (realOfModel I ind x0 hI hAs).blk := by
    intro hk
    rintro ⟨x, rfl | ⟨a, rfl⟩⟩
    · refine ⟨⟨0, hk⟩, ?_⟩
      show (⟨ind ⟨0, hk⟩, _⟩ : blockSet ind x0) = ⟨x0, _⟩
      simp only [x0, dif_pos hk]
    · exact ⟨a, rfl⟩
  have hle : Fintype.card (blockSet ind x0) ≤ max 1 k := by
    by_cases hk : 0 < k
    · have := Fintype.card_le_of_surjective _ (hsurj hk)
      rw [Fintype.card_fin] at this
      omega
    · have := card_blockSet_le ind x0
      rw [Fintype.card_fin] at this
      omega
  let e := Fintype.equivFinOfCardEq (α := blockSet ind x0)
    (n := Fintype.card (blockSet ind x0) - 1 + 1) (by omega)
  refine ⟨⟨Fintype.card (blockSet ind x0) - 1, by omega⟩, (realOfModel I ind x0 hI hAs).equiv e, ?_⟩
  by_cases hk : 0 < k
  · exact Or.inr (e.surjective.comp (hsurj hk))
  · exact Or.inl (by omega)

theorem mkLab_half {nb : Nat} {lab : Fin nb → Fin nb → Finset (RoleT (Fin m))}
    (hs : ∀ b c, lab c b = flipL (lab b c)) :
    mkLab (fun p => lab p.1.1 p.1.2) = lab := by
  funext b c
  unfold mkLab
  split_ifs with h
  · rfl
  · exact (hs c b).symm

/-- **Exactness of the search.** -/
theorem searchKB_iff (hA : IsALCHIQ O) : searchKB O A = true ↔ ConsistentKB O A := by
  show decide (SearchProp O A (alive O)) = true ↔ _
  rw [decide_eq_true_iff]
  constructor
  · rintro ⟨j, blk, -, -, ty, -, -, half, hc, hs⟩
    refine (consistentKB_iff_realisation O hA A).2 ⟨Fin (j.val + 1), inferInstance, ⟨0⟩,
      ⟨realOfCore hc fun b => ?_⟩⟩
    obtain ⟨C, hC, hok⟩ := hs b
    refine ⟨C, hok, fun e he => (good_iff_mem_alive _).2 ?_⟩
    exact (mem_cands.1 ((mem_listsUpTo _ _).1 hC |>.2 e he)).1
  · intro hc
    obtain ⟨j, ρ, hsurj⟩ := exists_small_realisation hc
    obtain ⟨hcore, hsup⟩ := core_of_real ρ
    refine ⟨j, ρ.blk, hsurj, fun as has => ?_, ρ.ty, fun b => ?_, fun as has => ?_,
      fun p => ρ.lab p.1.1 p.1.2, ?_⟩
    · cases as with
      | same a b => exact ρ.same a b has
      | diff a b => exact ρ.diff a b has
      | _ => trivial
    · obtain ⟨C, hok, -⟩ := ρ.kids b
      exact hok.closed
    · cases as with
      | cls a X => exact ρ.cls a X has
      | _ => trivial
    · rw [mkLab_half ρ.symm]
      exact ⟨hcore, hsup⟩

/-- **Consistency with a hint is exact for every hint.** -/
theorem consistentKB_iff (hA : IsALCHIQ O) (hint : Option (Hint n m k)) :
    consistentKB O A hint = true ↔ ConsistentKB O A := by
  unfold consistentKB
  rw [Bool.or_eq_true, searchKB_iff hA]
  constructor
  · rintro (h | h)
    · cases hint with
      | none => simp at h
      | some h' => exact checkRealisation_sound hA h' (by simpa using h)
    · exact h
  · exact Or.inr

/-- **Classification with an ABox.** Each requested name comes with
exactly its subsumers under the knowledge base. -/
theorem classifyKB_spec (hA : IsALCHIQ O) (hint : Option (Hint n m k)) {req : List (Fin n)} :
    ∀ p ∈ classifyKB O A hint req, p.1 ∈ req ∧ ∀ b, b ∈ p.2 ↔ EntailsSubKB O A p.1 b := by
  intro p hp
  unfold classifyKB at hp
  split_ifs at hp with hc
  · obtain ⟨hreq, hb⟩ := classifyQ_spec hA p hp
    refine ⟨hreq, fun b => ?_⟩
    rw [hb, entailsSubKB_iff]
    have : ConsistentKB O A := (consistentKB_iff hA hint).1 hc
    simp [this]
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hp
    refine ⟨ha, fun b => ?_⟩
    have : ¬ ConsistentKB O A := fun h => hc ((consistentKB_iff hA hint).2 h)
    simp only [List.mem_finRange, true_iff]
    exact (entailsSubKB_iff O A a b).2 (Or.inl this)

end Facts

/-! ## SHIQ knowledge bases -/

/-- Consistency of a SHIQ knowledge base: the procedure on the encoding,
with a hint over the names of the encoding. -/
def consistentKBQ (O : Ontology (Fin n) (Fin m)) (A : ABox (Fin n) (Fin m) (Fin k))
    (hint : Option (Hint (n + (encTransQ O).1) m k)) : Bool :=
  consistentKB (encTransQ O).2 (encABox O A) hint

theorem consistentKBQ_iff {O : Ontology (Fin n) (Fin m)} {A : ABox (Fin n) (Fin m) (Fin k)}
    (h : IsSHIQKB O A) (hint : Option (Hint (n + (encTransQ O).1) m k)) :
    consistentKBQ O A hint = true ↔ ConsistentKB O A := by
  rw [consistentKBQ, consistentKB_iff (encTransQ_isALCHIQ O), consistentKB_encTransQ h]

end ContextCalculus.SRIQ.Proc

#print axioms ContextCalculus.SRIQ.Proc.checkRealisation_sound
#print axioms ContextCalculus.SRIQ.Proc.searchKB_iff
#print axioms ContextCalculus.SRIQ.Proc.consistentKB_iff
#print axioms ContextCalculus.SRIQ.Proc.classifyKB_spec
#print axioms ContextCalculus.SRIQ.Proc.consistentKBQ_iff
