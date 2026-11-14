import ContextCalculus.SRIQN.Core

/-!
# Soundness: realisation to model (stage C2, design section 3.2)

`docs/V1.7.0-C2-NOMINALS-DESIGN.md`. From a realisation we build the
forest: the core elements, and below each core element the unravelling of
the good records of its children. A tree node is `(c, i, p)`: the child
`i` of core element `c`, then the path `p` of child indices (last step
first). Besides tree edges, a tree node has an edge to every core element
of its core entries (`rawRT`, the second disjuncts). Those back edges are
uncounted at the core element, so the core element's star stays its core
neighbours plus its children (`models_of_starLists'`).

`realisation_sound` holds for every realisation, with any core, and is the
soundness half of the full C2 stage.
-/

namespace ContextCalculus.SRIQN

open ContextCalculus.SRI (RoleT Interp)
open ContextCalculus.SRIQ (Nbr StarOK UpClosed EdgeOK cnt flipL nbrs RoleLe Closed mem_flipL FR)

variable {CName Role : Type}

section Forest

set_option linter.unusedSectionVars false

variable [DecidableEq CName] [DecidableEq Role] {B : SRIQ.Ontology CName Role} {N : List CName}
  {K : Type} [Fintype K] (r : RealisationN B N K)

/-- The support chosen for each good record. -/
noncomputable def supN (ρ : RecN CName Role K) :
    (K → Finset (RoleT Role)) × List (Nbr CName Role) := by
  classical
  exact if h : ρ ∈ goodSetN B N r.ty then (gSN (B := B) (N := N) (ty := r.ty) ρ h).choose
    else (fun _ => ∅, [])

theorem supN_spec {ρ : RecN CName Role K} (h : ρ ∈ goodSetN B N r.ty) :
    SupportsN B N r.ty (goodSetN B N r.ty) ρ (supN r ρ).1 (supN r ρ).2 := by
  unfold supN
  rw [dif_pos h]
  exact (gSN (B := B) (N := N) (ty := r.ty) ρ h).choose_spec

/-- The chosen children. -/
noncomputable def chN (ρ : RecN CName Role K) : List (Nbr CName Role) := (supN r ρ).2

/-- The chosen core entries. -/
noncomputable def ceN (ρ : RecN CName Role K) : K → Finset (RoleT Role) := (supN r ρ).1

/-- The record at a path below a start record. -/
noncomputable def recOfN (ρ0 : RecN CName Role K) : List Nat → Option (RecN CName Role K)
  | [] => some ρ0
  | i :: q => (recOfN ρ0 q).bind fun ρ => (chN r ρ)[i]?.map (childRecN ρ.1)

/-- The chosen tree children of each core element. -/
noncomputable def bkidsN (c : K) : List (Nbr CName Role) := (r.kids c).choose

theorem bkidsN_spec (c : K) : StarOK B (r.ty c) (nbrs r.ty r.lab c ++ bkidsN r c) ∧
    ∀ e ∈ bkidsN r c, GoodN B N r.ty (anchorRec c e) :=
  (r.kids c).choose_spec

/-- The record of the tree node `(c, i, p)`. -/
noncomputable def recT (c : K) (i : Nat) (p : List Nat) : Option (RecN CName Role K) :=
  ((bkidsN r c)[i]?).bind fun e => recOfN r (anchorRec c e) p

theorem recT_nil {c : K} {i : Nat} {ρ : RecN CName Role K} :
    recT r c i [] = some ρ ↔ ∃ e, (bkidsN r c)[i]? = some e ∧ ρ = anchorRec c e := by
  simp only [recT, recOfN, Option.bind_eq_some_iff, Option.some.injEq]
  constructor
  · rintro ⟨e, he, rfl⟩
    exact ⟨e, he, rfl⟩
  · rintro ⟨e, he, rfl⟩
    exact ⟨e, he, rfl⟩

theorem recT_cons {c : K} {i j : Nat} {q : List Nat} {ρ' : RecN CName Role K} :
    recT r c i (j :: q) = some ρ' ↔
      ∃ ρ e, recT r c i q = some ρ ∧ (chN r ρ)[j]? = some e ∧ ρ' = childRecN ρ.1 e := by
  simp only [recT, recOfN, Option.bind_eq_some_iff, Option.map_eq_some_iff]
  constructor
  · rintro ⟨e0, h0, ρ, h1, e, h2, rfl⟩
    exact ⟨ρ, e, ⟨e0, h0, h1⟩, h2, rfl⟩
  · rintro ⟨ρ, e, ⟨e0, h0, h1⟩, h2, rfl⟩
    exact ⟨e0, h0, ρ, h1, e, h2, rfl⟩

theorem recT_mem : ∀ {c : K} {i : Nat} {p : List Nat} {ρ : RecN CName Role K},
    recT r c i p = some ρ → ρ ∈ goodSetN B N r.ty
  | c, i, [], ρ, h => by
    obtain ⟨e, he, rfl⟩ := (recT_nil r).1 h
    exact (bkidsN_spec r c).2 e (List.mem_of_getElem? he)
  | c, i, j :: q, ρ, h => by
    obtain ⟨σ, e, h1, h2, rfl⟩ := (recT_cons r).1 h
    exact (supN_spec r (recT_mem h1)).kids e (List.mem_of_getElem? h2)

/-- The core entries of an anchor record leave out its anchor. -/
theorem ceN_anchor {c : K} {i : Nat} {ρ : RecN CName Role K} (h : recT r c i [] = some ρ) :
    ceN r ρ c = ∅ := by
  obtain ⟨e, -, rfl⟩ := (recT_nil r).1 h
  exact (supN_spec r (recT_mem r h)).anchor c _ rfl

/-- Tree edges below the child `i` of `c`. -/
def TAdj (c : K) (i : Nat) (R : RoleT Role) (p q : List Nat) : Prop :=
  (∃ j ρ e, q = j :: p ∧ recT r c i p = some ρ ∧ (chN r ρ)[j]? = some e ∧ R ∈ e.1) ∨
  (∃ j ρ e, p = j :: q ∧ recT r c i q = some ρ ∧ (chN r ρ)[j]? = some e ∧ R.flip ∈ e.1)

/-- Roles in the raw forest. -/
def rawRT (R : RoleT Role) : FR K → FR K → Prop
  | .inl b, .inl c => R ∈ r.lab b c
  | .inl b, .inr (c, i, p) => (c = b ∧ p = [] ∧ ∃ e, (bkidsN r b)[i]? = some e ∧ R ∈ e.1) ∨
      ∃ ρ, recT r c i p = some ρ ∧ R.flip ∈ ceN r ρ b
  | .inr (c, i, p), .inl b => (c = b ∧ p = [] ∧ ∃ e, (bkidsN r b)[i]? = some e ∧ R.flip ∈ e.1) ∨
      ∃ ρ, recT r c i p = some ρ ∧ R ∈ ceN r ρ b
  | .inr (b, i, p), .inr (c, j, q) => b = c ∧ i = j ∧ TAdj r b i R p q

/-- Types in the raw forest. -/
noncomputable def typN : FR K → Finset CName
  | .inl b => r.ty b
  | .inr (b, i, p) => ((recT r b i p).map Prod.fst).getD ∅

/-- The nodes of the forest. -/
def validN : FR K → Prop
  | .inl _ => True
  | .inr (b, i, p) => ∃ ρ, recT r b i p = some ρ

/-- **The forest interpretation.** -/
def forestN : Interp {x : FR K // validN r x} CName Role where
  c a x := a ∈ typN r x.1
  r s x y := rawRT r (.pos s) x.1 y.1

theorem tadj_flip (c : K) (i : Nat) (R : RoleT Role) (p q : List Nat) :
    TAdj r c i R.flip p q ↔ TAdj r c i R q p := by
  unfold TAdj
  simp only [RoleT.flip_flip]
  exact Or.comm

theorem rawRT_flip (R : RoleT Role) (x y : FR K) : rawRT r R.flip x y ↔ rawRT r R y x := by
  rcases x with b | ⟨b, i, p⟩ <;> rcases y with c | ⟨c, j, q⟩
  · simp only [rawRT]
    rw [r.symm c b, mem_flipL, RoleT.flip_flip]
  · simp only [rawRT, RoleT.flip_flip]
  · simp only [rawRT, RoleT.flip_flip]
  · simp only [rawRT, tadj_flip]
    constructor
    · rintro ⟨rfl, rfl, h⟩
      exact ⟨rfl, rfl, h⟩
    · rintro ⟨rfl, rfl, h⟩
      exact ⟨rfl, rfl, h⟩

theorem forestN_rt (R : RoleT Role) (x y : {x : FR K // validN r x}) :
    (forestN r).rt R x y ↔ rawRT r R x.1 y.1 := by
  cases R with
  | pos s => exact Iff.rfl
  | inv s =>
    show rawRT r (.pos s) y.1 x.1 ↔ _
    exact (rawRT_flip r (.pos s) x.1 y.1).symm

variable [Fintype Role]

/-- Labels in the raw forest. -/
noncomputable def labN (x y : FR K) : Finset (RoleT Role) := by
  classical
  exact Finset.univ.filter fun R => rawRT r R x y

theorem mem_labN {x y : FR K} {R : RoleT Role} : R ∈ labN r x y ↔ rawRT r R x y := by
  classical
  simp [labN]

/-- The parent of a tree node. -/
def parN (c : K) (i : Nat) : List Nat → List (FR K)
  | [] => [.inl c]
  | _ :: q => [.inr (c, i, q)]

/-- The neighbours of a raw node. -/
noncomputable def nbN : FR K → List (FR K)
  | .inl b => ((Finset.univ.filter fun c => r.lab b c ≠ ∅).toList.map Sum.inl) ++
      (List.finRange (bkidsN r b).length).map fun i => Sum.inr (b, i.val, [])
  | .inr (c, i, p) => match recT r c i p with
      | some ρ => parN c i p ++ (((Finset.univ.filter fun d => ceN r ρ d ≠ ∅).toList.map Sum.inl) ++
          (List.finRange (chN r ρ).length).map fun j => Sum.inr (c, i, j.val :: p))
      | none => []

/-- The facts the star lemma needs at one valid node. -/
structure NodeOKN (x : FR K) : Prop where
  nodup : (nbN r x).Nodup
  valid : ∀ y ∈ nbN r x, validN r y
  comp : ∀ R y, rawRT r R x y → y ∉ nbN r x →
    UpClosed B (labN r x y) ∧ EdgeOK B (typN r x) (labN r x y, typN r y) ∧
      ¬ Counted B (typN r x) (labN r x y) (typN r y)
  star : StarOK B (typN r x) ((nbN r x).map fun y => (labN r x y, typN r y))

theorem labN_core_child {b : K} {i : Nat} (hi : i < (bkidsN r b).length) :
    labN r (.inl b) (.inr (b, i, [])) = ((bkidsN r b)[i]).1 := by
  have h0 : recT r b i [] = some (anchorRec b (bkidsN r b)[i]) :=
    (recT_nil r).2 ⟨_, List.getElem?_eq_getElem hi, rfl⟩
  have hce := ceN_anchor r h0
  ext R
  rw [mem_labN]
  simp only [rawRT, true_and, List.getElem?_eq_getElem hi, Option.some.injEq, exists_eq_left', h0,
    hce, Finset.notMem_empty, or_false]

theorem labN_core_back {b c : K} {i : Nat} {p : List Nat} {ρ : RecN CName Role K}
    (hρ : recT r c i p = some ρ) (hn : ¬ (c = b ∧ p = [])) :
    labN r (.inl b) (.inr (c, i, p)) = flipL (ceN r ρ b) := by
  ext R
  rw [mem_labN, mem_flipL]
  simp only [rawRT, hρ, Option.some.injEq, exists_eq_left']
  constructor
  · rintro (⟨rfl, rfl, -⟩ | h)
    · exact absurd ⟨rfl, rfl⟩ hn
    · exact h
  · exact Or.inr

theorem labN_tree_core {c d : K} {i : Nat} {p : List Nat} {ρ : RecN CName Role K}
    (hρ : recT r c i p = some ρ) (hn : ¬ (d = c ∧ p = [])) :
    labN r (.inr (c, i, p)) (.inl d) = ceN r ρ d := by
  ext R
  rw [mem_labN]
  simp only [rawRT, hρ, Option.some.injEq, exists_eq_left']
  constructor
  · rintro (⟨rfl, rfl, -⟩ | h)
    · exact absurd ⟨rfl, rfl⟩ hn
    · exact h
  · exact Or.inr

theorem tadj_child {c : K} {i : Nat} {R : RoleT Role} {p : List Nat} {ρ : RecN CName Role K}
    (hp : recT r c i p = some ρ) {j : Nat} (hj : j < (chN r ρ).length) :
    TAdj r c i R p (j :: p) ↔ R ∈ ((chN r ρ)[j]).1 := by
  constructor
  · rintro (⟨j', ρ', e, he, hρ', hj', hR⟩ | ⟨j', ρ', e, he, -, -, -⟩)
    · obtain ⟨rfl, -⟩ := List.cons.inj he
      rw [hp, Option.some.injEq] at hρ'
      subst hρ'
      rw [List.getElem?_eq_getElem hj, Option.some.injEq] at hj'
      exact hj' ▸ hR
    · exact absurd he (SRIQ.ne_cons_cons _ _ _)
  · intro hR
    exact Or.inl ⟨j, ρ, _, rfl, hp, List.getElem?_eq_getElem hj, hR⟩

theorem tadj_parent {c : K} {i : Nat} {R : RoleT Role} {q : List Nat} {σ : RecN CName Role K}
    (hq : recT r c i q = some σ) {j : Nat} {e : Nbr CName Role} (he : (chN r σ)[j]? = some e) :
    TAdj r c i R (j :: q) q ↔ R.flip ∈ e.1 := by
  constructor
  · rintro (⟨j', ρ', e', h', -, -, -⟩ | ⟨j', ρ', e', h', hρ', hj, hR⟩)
    · exact absurd h' (SRIQ.ne_cons_cons _ _ _)
    · obtain ⟨rfl, -⟩ := List.cons.inj h'
      rw [hq, Option.some.injEq] at hρ'
      subst hρ'
      rw [he, Option.some.injEq] at hj
      exact hj ▸ hR
  · intro hR
    exact Or.inr ⟨j, σ, e, rfl, hq, he, hR⟩

theorem nodeOKN_block (b : K) : NodeOKN r (.inl b) := by
  have hroot : ∀ i (h : i < (bkidsN r b).length),
      recT r b i [] = some (anchorRec b (bkidsN r b)[i]) := fun i h =>
    (recT_nil r).2 ⟨_, List.getElem?_eq_getElem h, rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [nbN]
    rw [List.nodup_append]
    refine ⟨(Finset.nodup_toList _).map Sum.inl_injective, ?_, ?_⟩
    · refine (List.nodup_finRange _).map fun i j h => ?_
      simp only [Sum.inr.injEq, Prod.mk.injEq, and_true, true_and] at h
      exact Fin.ext h
    · intro u hu v hv huv
      subst huv
      obtain ⟨c, -, rfl⟩ := List.mem_map.1 hu
      obtain ⟨i, -, h⟩ := List.mem_map.1 hv
      exact Sum.inr_ne_inl h
  · intro y hy
    simp only [nbN] at hy
    rcases List.mem_append.1 hy with hy | hy
    · obtain ⟨c, -, rfl⟩ := List.mem_map.1 hy
      trivial
    · obtain ⟨i, -, rfl⟩ := List.mem_map.1 hy
      exact ⟨_, hroot i.val i.2⟩
  · rintro R (c | ⟨c, i, p⟩) h hny
    · exfalso
      simp only [rawRT] at h
      refine hny (List.mem_append_left _ (List.mem_map.2 ⟨c, ?_, rfl⟩))
      rw [Finset.mem_toList, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, fun h0 => ?_⟩
      rw [h0] at h
      exact absurd h (Finset.notMem_empty _)
    · simp only [rawRT] at h
      rcases h with ⟨rfl, rfl, e, he, -⟩ | ⟨ρ, hρ, hR⟩
      · exfalso
        have hlt : i < (bkidsN r c).length := (List.getElem?_eq_some_iff.1 he).1
        exact hny (List.mem_append_right _ (List.mem_map.2 ⟨⟨i, hlt⟩, List.mem_finRange _, rfl⟩))
      · have hn : ¬ (c = b ∧ p = []) := by
          rintro ⟨rfl, rfl⟩
          rw [ceN_anchor r hρ] at hR
          exact Finset.notMem_empty _ hR
        have hne : ceN r ρ b ≠ ∅ := fun h0 => by
          rw [h0] at hR
          exact Finset.notMem_empty _ hR
        have sp := supN_spec r (recT_mem r hρ)
        have hmem : (ceN r ρ b, r.ty b) ∈ (parentE r.ty ρ.2 :: cEntries r.ty (ceN r ρ)) ++
            chN r ρ := by
          refine List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_map.2 ⟨b, ?_, rfl⟩))
          rw [Finset.mem_toList, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, hne⟩
        obtain ⟨hup, hedge⟩ := sp.star.edge _ hmem
        have htyp : typN r (.inr (c, i, p)) = ρ.1 := by
          simp only [typN, hρ, Option.map_some, Option.getD_some]
        rw [labN_core_back r hρ hn, htyp]
        exact ⟨upClosed_flipL hup, edgeOK_flip hedge, sp.unc b⟩
  · have heq : (nbN r (.inl b)).map (fun y => (labN r (.inl b) y, typN r y)) =
        nbrs r.ty r.lab b ++ bkidsN r b := by
      simp only [nbN, List.map_append, List.map_map, nbrs]
      congr 1
      · refine List.map_congr_left fun c _ => ?_
        simp only [Function.comp_apply, typN, Prod.mk.injEq, and_true]
        ext R
        rw [mem_labN]
        rfl
      · conv_rhs => rw [← List.map_getElem_finRange (bkidsN r b)]
        refine List.map_congr_left fun i _ => ?_
        simp only [Function.comp_apply, typN, hroot i.val i.2, Option.map_some,
          Option.getD_some, anchorRec, labN_core_child r i.2]
    rw [heq]
    exact (bkidsN_spec r b).1

theorem nodeOKN_tree {c : K} {i : Nat} {p : List Nat} {ρ : RecN CName Role K}
    (hr : recT r c i p = some ρ) : NodeOKN r (.inr (c, i, p)) := by
  have sp := supN_spec r (recT_mem r hr)
  set cores := (Finset.univ.filter fun d => ceN r ρ d ≠ ∅).toList with hcores
  set kids := (List.finRange (chN r ρ).length).map fun j => (Sum.inr (c, i, j.val :: p) : FR K)
    with hkids
  have hnb : nbN r (.inr (c, i, p)) = parN c i p ++ (cores.map Sum.inl ++ kids) := by
    simp only [nbN, hr, hcores, hkids]
  have hrecj : ∀ j (hj : j < (chN r ρ).length),
      recT r c i (j :: p) = some (childRecN ρ.1 (chN r ρ)[j]) := fun j hj =>
    (recT_cons r).2 ⟨ρ, _, hr, List.getElem?_eq_getElem hj, rfl⟩
  -- the anchor is not a core entry
  have hanc : p = [] → ceN r ρ c = ∅ := by
    rintro rfl
    exact ceN_anchor r hr
  have hmemcores : ∀ d, d ∈ cores ↔ ceN r ρ d ≠ ∅ := by
    intro d
    rw [hcores, Finset.mem_toList, Finset.mem_filter]
    simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hnb, List.nodup_append, List.nodup_append]
    refine ⟨?_, ⟨(Finset.nodup_toList _).map Sum.inl_injective,
      (List.nodup_finRange _).map fun j j' h => ?_, ?_⟩, ?_⟩
    · cases p <;> simp [parN]
    · simp only [Sum.inr.injEq, Prod.mk.injEq, List.cons.injEq, and_true, true_and] at h
      exact Fin.ext h
    · intro u hu v hv huv
      subst huv
      obtain ⟨d, -, rfl⟩ := List.mem_map.1 hu
      obtain ⟨j, -, h⟩ := List.mem_map.1 hv
      exact Sum.inr_ne_inl h
    · intro u hu v hv huv
      subst huv
      cases p with
      | nil =>
        simp only [parN, List.mem_singleton] at hu
        subst hu
        rcases List.mem_append.1 hv with hv | hv
        · obtain ⟨d, hd, hdc⟩ := List.mem_map.1 hv
          obtain rfl := Sum.inl_injective hdc
          exact (hmemcores d).1 hd (hanc rfl)
        · obtain ⟨j, -, h⟩ := List.mem_map.1 hv
          exact Sum.inr_ne_inl h
      | cons j q =>
        simp only [parN, List.mem_singleton] at hu
        subst hu
        rcases List.mem_append.1 hv with hv | hv
        · obtain ⟨d, -, h⟩ := List.mem_map.1 hv
          exact Sum.inl_ne_inr h
        · obtain ⟨j', -, h⟩ := List.mem_map.1 hv
          simp only [Sum.inr.injEq, Prod.mk.injEq, true_and] at h
          exact SRIQ.ne_cons_cons _ _ _ h.symm
  · intro y hy
    rw [hnb] at hy
    rcases List.mem_append.1 hy with hy | hy
    · cases p with
      | nil =>
        simp only [parN, List.mem_singleton] at hy
        subst hy
        trivial
      | cons j q =>
        simp only [parN, List.mem_singleton] at hy
        subst hy
        obtain ⟨σ, e, h1, -, -⟩ := (recT_cons r).1 hr
        exact ⟨σ, h1⟩
    · rcases List.mem_append.1 hy with hy | hy
      · obtain ⟨d, -, rfl⟩ := List.mem_map.1 hy
        trivial
      · obtain ⟨j, -, rfl⟩ := List.mem_map.1 hy
        exact ⟨_, hrecj j.val j.2⟩
  · intro R y h hny
    exfalso
    apply hny
    rw [hnb]
    rcases y with d | ⟨c', j, q⟩
    · simp only [rawRT] at h
      rcases h with ⟨rfl, rfl, -⟩ | ⟨ρ', hρ', hR⟩
      · exact List.mem_append_left _ (by simp [parN])
      · rw [hr, Option.some.injEq] at hρ'
        subst hρ'
        refine List.mem_append_right _ (List.mem_append_left _ (List.mem_map.2 ⟨d, ?_, rfl⟩))
        rw [hmemcores]
        intro h0
        rw [h0] at hR
        exact Finset.notMem_empty _ hR
    · simp only [rawRT] at h
      obtain ⟨rfl, rfl, h⟩ := h
      rcases h with ⟨j', ρ', e, rfl, hρ', he, -⟩ | ⟨j', ρ', e, rfl, -, -, -⟩
      · rw [hr, Option.some.injEq] at hρ'
        subst hρ'
        have hlt : j' < (chN r ρ).length := (List.getElem?_eq_some_iff.1 he).1
        exact List.mem_append_right _ (List.mem_append_right _
          (List.mem_map.2 ⟨⟨j', hlt⟩, List.mem_finRange _, rfl⟩))
      · exact List.mem_append_left _ (by simp [parN])
  · have htyp : typN r (.inr (c, i, p)) = ρ.1 := by
      simp only [typN, hr, Option.map_some, Option.getD_some]
    have hpar : (parN c i p).map (fun y => (labN r (.inr (c, i, p)) y, typN r y)) =
        [parentE r.ty ρ.2] := by
      cases p with
      | nil =>
        obtain ⟨e, he, rfl⟩ := (recT_nil r).1 hr
        simp only [parN, List.map_cons, List.map_nil, anchorRec, parentE, typN, List.cons.injEq,
          Prod.mk.injEq, and_true]
        ext R
        rw [mem_labN, mem_flipL]
        simp only [rawRT, true_and, he, Option.some.injEq, exists_eq_left', hr,
          ceN_anchor r hr, Finset.notMem_empty, or_false]
      | cons j q =>
        obtain ⟨σ, e, h1, h2, rfl⟩ := (recT_cons r).1 hr
        simp only [parN, List.map_cons, List.map_nil, childRecN, parentE, typN, h1,
          Option.map_some, Option.getD_some, List.cons.injEq, Prod.mk.injEq, and_true]
        ext R
        rw [mem_labN, mem_flipL]
        simp only [rawRT, true_and]
        exact tadj_parent r h1 h2
    have hcore : (cores.map Sum.inl).map (fun y => (labN r (.inr (c, i, p)) y, typN r y)) =
        cEntries r.ty (ceN r ρ) := by
      rw [List.map_map, cEntries, ← hcores]
      refine List.map_congr_left fun d hd => ?_
      simp only [Function.comp_apply, typN, Prod.mk.injEq, and_true]
      refine labN_tree_core r hr ?_
      rintro ⟨rfl, rfl⟩
      exact (hmemcores d).1 hd (hanc rfl)
    have hch : kids.map (fun y => (labN r (.inr (c, i, p)) y, typN r y)) = chN r ρ := by
      rw [hkids, List.map_map]
      conv_rhs => rw [← List.map_getElem_finRange (chN r ρ)]
      refine List.map_congr_left fun j _ => ?_
      simp only [Function.comp_apply, typN, hrecj j.val j.2, Option.map_some, Option.getD_some,
        childRecN]
      refine Prod.ext ?_ rfl
      ext R
      rw [mem_labN]
      simp only [rawRT, true_and]
      exact tadj_child r hr j.2
    rw [hnb, List.map_append, List.map_append, hpar, hcore, hch, htyp]
    exact sp.star

theorem nodeOKN (x : {x : FR K // validN r x}) : NodeOKN r x.1 := by
  obtain ⟨x | ⟨b, i, p⟩, hx⟩ := x
  · exact nodeOKN_block r x
  · obtain ⟨ρ, hρ⟩ := hx
    exact nodeOKN_tree r hρ

theorem forestN_models_base (hA : SRIQ.IsALCHIQ B) : SRIQ.models (forestN r) B := by
  refine models_of_starLists' hA (forestN r) (fun x => typN r x.1) (fun _ _ => Iff.rfl)
    (fun x y => labN r x.1 y.1) (fun R x y => by rw [mem_labN, forestN_rt])
    (fun x => (nbN r x.1).pmap Subtype.mk (nodeOKN r x).valid)
    (fun x => (nodeOKN r x).nodup.pmap fun _ _ _ _ h => congrArg Subtype.val h)
    (fun R x y h hy => ?_) (fun x => ?_)
  · refine (nodeOKN r x).comp R y.1 ((forestN_rt r R x y).1 h) fun hy' => hy ?_
    rw [List.mem_pmap]
    exact ⟨y.1, hy', rfl⟩
  · simp only [List.map_pmap, List.pmap_eq_map]
    exact (nodeOKN r x).star

theorem forestN_nom {a : CName} (ha : a ∈ N) : NomAt (forestN r) a := by
  obtain ⟨c, hc, huniq⟩ := r.nom a ha
  refine ⟨⟨.inl c, trivial⟩, fun y => ?_⟩
  obtain ⟨y | ⟨b, i, p⟩, hy⟩ := y
  · show a ∈ r.ty y ↔ _
    constructor
    · intro h
      rw [huniq y h]
    · intro h
      cases h
      exact hc
  · obtain ⟨ρ, hρ⟩ := hy
    show a ∈ typN r (.inr (b, i, p)) ↔ _
    simp only [typN, hρ, Option.map_some, Option.getD_some]
    constructor
    · intro h
      exact absurd h (good_noNom (recT_mem r hρ) a ha)
    · intro h
      exact absurd (congrArg Subtype.val h) Sum.inr_ne_inl

end Forest

/-- **Soundness of realisations** (design section 3.2). A realisation over
a nonempty core gives a model. -/
theorem realisation_sound [DecidableEq CName] [DecidableEq Role] [Fintype Role]
    {O : Ontology CName Role} (h : IsALCHOIQ O) {K : Type} [Fintype K] [Nonempty K]
    (r : RealisationN (basePart O) (noms O) K) : ConsistentN O := by
  obtain ⟨c⟩ := (inferInstance : Nonempty K)
  refine ⟨_, ⟨⟨.inl c, trivial⟩⟩, forestN r, models_iff.2 ⟨forestN_models_base r h, ?_⟩⟩
  intro a ha
  exact forestN_nom r ha

end ContextCalculus.SRIQN

#print axioms ContextCalculus.SRIQN.realisation_sound
