import ContextCalculus.ELCompletionRelativeRefinement
import Mathlib.Data.List.Dedup
import Std.Data.TreeSet
import Std.Data.TreeSet.Lemmas
import Std.Data.TreeMap
import Std.Data.TreeMap.Lemmas

/-!
# Executable reference saturation for the pure ELC calculus

This module is the reference procedure of the v1.6.0 completeness proof for
the EL fragment (`docs/V1.6.0-COMPLETENESS-PLAN.md`, section 4.1).  It
computes the closure of `ELCompletion.Sub`/`Edge` over a finite universe and
proves the result closed on that universe and sound.  Combined with
`entails_iff_materialized_on`, the readout `referenceBit` is exact for every
requested named concept.
-/

namespace ContextCalculus.ELReference

open ContextCalculus.ELCompletion
open Std

local instance [Ord α] [Ord β] : Ord (α × β) := lexOrd

abbrev Ontology := ELCompletion.Ontology Nat Nat

/-- Concept names of one normal-form clause. -/
def clauseConcepts : ELCompletion.Clause Nat Nat → List Nat
  | .nf1 sub sup => [sub, sup]
  | .nf2 left right sup => [left, right, sup]
  | .nf3 sub _ filler => [sub, filler]
  | .nf4 _ filler sup => [filler, sup]
  | .nf5 sub => [sub]
  | .nf6 _ _ => []
  | .nf7 _ _ _ => []
  | .reflexive _ => []

/-- Role names of one normal-form clause. -/
def clauseRoles : ELCompletion.Clause Nat Nat → List Nat
  | .nf1 _ _ => []
  | .nf2 _ _ _ => []
  | .nf3 _ role _ => [role]
  | .nf4 role _ _ => [role]
  | .nf5 _ => []
  | .nf6 sub sup => [sub, sup]
  | .nf7 first second sup => [first, second, sup]
  | .reflexive role => [role]

/-- The finite context universe: distinguished concepts, requested names and
every concept of the ontology. -/
def contextUniverse (top bottom : Nat) (named : List Nat) (O : Ontology) : List Nat :=
  (top :: bottom :: named ++ O.flatMap clauseConcepts).dedup

def roleUniverse (O : Ontology) : List Nat :=
  (O.flatMap clauseRoles).dedup

/-- Every concept occurring in an ontology clause belongs to the context universe. -/
theorem mem_universe_of_concept {top bottom : Nat} {named : List Nat}
    {O : Ontology} {clause : ELCompletion.Clause Nat Nat} {concept : Nat}
    (hclause : clause ∈ O) (hconcept : concept ∈ clauseConcepts clause) :
    concept ∈ contextUniverse top bottom named O :=
  List.mem_dedup.mpr (List.mem_append_right _
    (List.mem_flatMap.mpr ⟨clause, hclause, hconcept⟩))

/-- The distinguished `top` concept belongs to the context universe. -/
theorem top_mem_contextUniverse (top bottom : Nat) (named : List Nat) (O : Ontology) :
    top ∈ contextUniverse top bottom named O := by
  simp [contextUniverse]

/-- The distinguished `bottom` concept belongs to the context universe. -/
theorem bottom_mem_contextUniverse (top bottom : Nat) (named : List Nat) (O : Ontology) :
    bottom ∈ contextUniverse top bottom named O := by
  simp [contextUniverse]

/-- Every requested named concept belongs to the context universe. -/
theorem mem_universe_of_named {top bottom : Nat} {named : List Nat}
    {O : Ontology} {concept : Nat} (hnamed : concept ∈ named) :
    concept ∈ contextUniverse top bottom named O := by
  simp [contextUniverse, hnamed]

private theorem mem_roleUniverse_of_role {O : Ontology}
    {clause : ELCompletion.Clause Nat Nat} {role : Nat}
    (hclause : clause ∈ O) (hrole : role ∈ clauseRoles clause) :
    role ∈ roleUniverse O :=
  List.mem_dedup.mpr (List.mem_flatMap.mpr ⟨clause, hclause, hrole⟩)

/-- Label facts `(context, member)` and edge facts `(context, (role, target))`. -/
structure State where
  subs : List (Nat × Nat)
  edges : List (Nat × (Nat × Nat))
  subSet : TreeSet (Nat × Nat) := ∅
  edgeSet : TreeSet (Nat × (Nat × Nat)) := ∅

def State.hasSub (s : State) (a b : Nat) : Bool := s.subSet.contains (a, b)

def State.hasEdge (s : State) (a role b : Nat) : Bool :=
  s.edgeSet.contains (a, (role, b))

def State.hasSubSlow (s : State) (a b : Nat) : Bool := decide ((a, b) ∈ s.subs)

def State.hasEdgeSlow (s : State) (a role b : Nat) : Bool :=
  decide ((a, (role, b)) ∈ s.edges)

def State.size (s : State) : Nat := s.subs.length + s.edges.length

/-- The abstract view used by the refinement contract. -/
def State.toMaterialization (s : State) : Materialization Nat Nat where
  sub a b := (a, b) ∈ s.subs
  edge a role b := (a, (role, b)) ∈ s.edges

/-- Tree-set indices agree with list membership. -/
structure WellFormedState (s : State) : Prop where
  sub_iff : ∀ p, s.subSet.contains p = true ↔ p ∈ s.subs
  edge_iff : ∀ e, s.edgeSet.contains e = true ↔ e ∈ s.edges

/-- Rust's initialisation: every context is in its own label and in `top`'s. -/
def initial (top : Nat) (U : List Nat) : State where
  subs := U.flatMap fun a => [(a, a), (a, top)]
  edges := []

/-- Every label consequence of one round (possibly already present). -/
def subConsequences (bottom : Nat) (O : Ontology) (U : List Nat) (s : State) :
    List (Nat × Nat) :=
  U.flatMap fun a =>
    (O.flatMap fun clause =>
      match clause with
      | .nf1 sub sup => if s.hasSubSlow a sub then [(a, sup)] else []
      | .nf2 left right sup =>
          if s.hasSubSlow a left && s.hasSubSlow a right then [(a, sup)] else []
      | .nf5 sub => if s.hasSubSlow a sub then [(a, bottom)] else []
      | .nf4 role filler sup =>
          (s.edges.filter fun edge => edge.1 == a && edge.2.1 == role).flatMap
            fun edge => if s.hasSubSlow edge.2.2 filler then [(a, sup)] else []
      | _ => []) ++
    ((s.edges.filter fun edge => edge.1 == a).flatMap
      fun edge => if s.hasSubSlow edge.2.2 bottom then [(a, bottom)] else [])

/-- Every edge consequence of one round (possibly already present). -/
def edgeConsequences (O : Ontology) (U : List Nat) (s : State) :
    List (Nat × (Nat × Nat)) :=
  U.flatMap fun a =>
    O.flatMap fun clause =>
      match clause with
      | .nf3 sub role filler => if s.hasSubSlow a sub then [(a, (role, filler))] else []
      | .nf6 sub sup =>
          (s.edges.filter fun edge => edge.1 == a && edge.2.1 == sub).map
            fun edge => (a, (sup, edge.2.2))
      | .nf7 first second sup =>
          (s.edges.filter fun edge => edge.1 == a && edge.2.1 == first).flatMap
            fun edge =>
              (s.edges.filter fun next =>
                  next.1 == edge.2.2 && next.2.1 == second).map
                fun next => (a, (sup, next.2.2))
      | .reflexive role => [(a, (role, a))]
      | _ => []

/-- One round: append the new consequences, keeping the lists duplicate-free. -/
def step (bottom : Nat) (O : Ontology) (U : List Nat) (s : State) : State :=
  let newSubs :=
    ((subConsequences bottom O U s).filter fun fact => decide (fact ∉ s.subs)).dedup
  let newEdges :=
    ((edgeConsequences O U s).filter fun fact => decide (fact ∉ s.edges)).dedup
  { subs := s.subs ++ newSubs, edges := s.edges ++ newEdges }

/-- Iterate `step` until a round adds nothing. -/
def saturate (bottom : Nat) (O : Ontology) (U : List Nat) :
    Nat → State → State
  | 0, s => s
  | fuel + 1, s =>
      let next := step bottom O U s
      if next.size = s.size then s else saturate bottom O U fuel next

/-- Upper bound on the number of distinct facts over the universe. -/
def factBound (U roles : List Nat) : Nat :=
  U.length * U.length + U.length * (roles.length * U.length)

/-- Populate the tree-set indices from the fact lists. -/
def State.withSets (s : State) : State :=
  { s with
    subSet := TreeSet.ofList s.subs
    edgeSet := TreeSet.ofList s.edges }

/-- Slow specification closure used as the verified fallback. -/
def slowClosure (top bottom : Nat) (named : List Nat) (O : Ontology) : State :=
  let U := contextUniverse top bottom named O
  (saturate bottom O U (factBound U (roleUniverse O) + 1) (initial top U)).withSets

/-!
## Obligations

The two theorems below are the proof obligations of the reference procedure.
Proof plan (see the plan document):

* Invariants of `step`, preserved from `initial`: `subs ⊆ U × U` and
  `edges ⊆ U × roleUniverse O × U` (every consequence has its context in
  `U`, its role in the ontology and its target an nf3 filler, the context,
  or an earlier target); both lists are `Nodup`; `step` only appends; each
  stored fact has a derivation (`SoundState`), by `Sub`/`Edge` constructors
  applied to the derivations of the facts it was computed from.
* A fixpoint (`(step s).size = s.size`) contains every consequence, which
  is exactly `ClosedStateOn (· ∈ U)` with `fillerIn` from
  `mem_universe_of_concept`.
* Pigeonhole: a `Nodup` list of pairs over `U × U` has length at most
  `U.length * U.length` (and likewise for edges), so `size ≤ factBound`;
  every non-fixpoint step raises `size` by at least one, so `saturate`
  with fuel `factBound + 1` returns a fixpoint.
-/

private theorem hasSub_iff {s : State} {a b : Nat} :
    s.hasSubSlow a b = true ↔ (a, b) ∈ s.subs := by
  simp [State.hasSubSlow]

private theorem hasEdge_iff {s : State} {a role b : Nat} :
    s.hasEdgeSlow a role b = true ↔ (a, (role, b)) ∈ s.edges := by
  simp [State.hasEdgeSlow]

private theorem mem_ite_singleton {α : Type} {P : Prop} [Decidable P] {x y : α} :
    x ∈ (if P then [y] else []) ↔ P ∧ x = y := by
  split <;> simp [*]

private theorem initial_sound (top bottom : Nat) (O : Ontology) (U : List Nat) :
    SoundState (initial top U).toMaterialization top bottom O where
  subSound {a b} hmem := by
    simp only [State.toMaterialization, initial, List.mem_flatMap, List.mem_cons,
      List.not_mem_nil, or_false] at hmem
    rcases hmem with ⟨x, _, hEq | hEq⟩
    · cases hEq
      exact Sub.refl a
    · cases hEq
      exact Sub.top a
  edgeSound hmem := by
    simp [State.toMaterialization, initial] at hmem

private theorem subConsequences_sound {top bottom : Nat} {O : Ontology} {U : List Nat}
    {s : State} (hs : SoundState s.toMaterialization top bottom O)
    {a b : Nat} (hmem : (a, b) ∈ subConsequences bottom O U s) :
    Sub top bottom O a b := by
  simp only [subConsequences, List.mem_flatMap, List.mem_append] at hmem
  rcases hmem with ⟨x, _, hclause | hedge⟩
  · rcases hclause with ⟨clause, hcl, hbranch⟩
    cases clause with
    | nf1 sub sup =>
        simp only [mem_ite_singleton, Prod.mk.injEq, hasSub_iff] at hbranch
        rcases hbranch with ⟨hsub, h1, h2⟩
        rw [h1, h2]
        exact Sub.nf1 (hs.subSound hsub) hcl
    | nf2 left right sup =>
        simp only [mem_ite_singleton, Prod.mk.injEq, Bool.and_eq_true, hasSub_iff] at hbranch
        rcases hbranch with ⟨⟨hl, hr⟩, h1, h2⟩
        rw [h1, h2]
        exact Sub.nf2 (hs.subSound hl) (hs.subSound hr) hcl
    | nf5 sub =>
        simp only [mem_ite_singleton, Prod.mk.injEq, hasSub_iff] at hbranch
        rcases hbranch with ⟨hsub, h1, h2⟩
        rw [h1, h2]
        exact Sub.nf5 (hs.subSound hsub) hcl
    | nf4 role filler sup =>
        simp only [List.mem_flatMap, List.mem_filter, mem_ite_singleton,
          Prod.mk.injEq, Bool.and_eq_true, beq_iff_eq, hasSub_iff] at hbranch
        rcases hbranch with ⟨⟨e1, r, t⟩, ⟨he_mem, he1, her⟩, hsub, h1, h2⟩
        dsimp only at he1 her hsub
        rw [h1, h2]
        rw [he1, her] at he_mem
        exact Sub.nf4 (hs.edgeSound he_mem) (hs.subSound hsub) hcl
    | nf3 _ _ _ => simp at hbranch
    | nf6 _ _ => simp at hbranch
    | nf7 _ _ _ => simp at hbranch
    | reflexive _ => simp at hbranch
  · rcases hedge with ⟨⟨e1, r, t⟩, he_filter, hif⟩
    simp only [List.mem_filter, beq_iff_eq] at he_filter
    rcases he_filter with ⟨he_mem, he1⟩
    simp only [mem_ite_singleton, Prod.mk.injEq, hasSub_iff] at hif
    rcases hif with ⟨hsub, h1, h2⟩
    rw [h1, h2]
    rw [he1] at he_mem
    exact Sub.bottomEdge (hs.edgeSound he_mem) (hs.subSound hsub)

private theorem edgeConsequences_sound {top bottom : Nat} {O : Ontology} {U : List Nat}
    {s : State} (hs : SoundState s.toMaterialization top bottom O)
    {a role b : Nat} (hmem : (a, (role, b)) ∈ edgeConsequences O U s) :
    Edge top bottom O a role b := by
  simp only [edgeConsequences, List.mem_flatMap] at hmem
  rcases hmem with ⟨x, _, clause, hcl, hbranch⟩
  cases clause with
  | nf3 sub r filler =>
      simp only [mem_ite_singleton, Prod.mk.injEq, hasSub_iff] at hbranch
      rcases hbranch with ⟨hsub, h1, h2, h3⟩
      rw [h1, h2, h3]
      exact Edge.nf3 (hs.subSound hsub) hcl
  | nf6 sub sup =>
      simp only [List.mem_map, List.mem_filter, Bool.and_eq_true, beq_iff_eq,
        Prod.mk.injEq] at hbranch
      rcases hbranch with ⟨⟨e1, r, t⟩, ⟨he_mem, he1, her⟩, h1, h2, h3⟩
      dsimp only at he1 her h3
      rw [← h1, ← h2, ← h3]
      rw [he1, her] at he_mem
      exact Edge.nf6 (hs.edgeSound he_mem) hcl
  | nf7 first second sup =>
      simp only [List.mem_flatMap, List.mem_map, List.mem_filter, Bool.and_eq_true,
        beq_iff_eq, Prod.mk.injEq] at hbranch
      rcases hbranch with ⟨⟨e1, r1, mid⟩, ⟨he1_mem, he1_1, he1_r⟩,
        ⟨e2, r2, t⟩, ⟨he2_mem, he2_1, he2_r⟩, h1, h2, h3⟩
      dsimp only at he1_1 he1_r he2_1 he2_r h3
      rw [← h1, ← h2, ← h3]
      rw [he1_1, he1_r] at he1_mem
      rw [he2_1, he2_r] at he2_mem
      exact Edge.nf7 (hs.edgeSound he1_mem) (hs.edgeSound he2_mem) hcl
  | reflexive r =>
      simp only [List.mem_singleton, Prod.mk.injEq] at hbranch
      rcases hbranch with ⟨h1, h2, h3⟩
      rw [h1, h2, h3]
      exact Edge.reflexive x hcl
  | nf1 _ _ => simp at hbranch
  | nf2 _ _ _ => simp at hbranch
  | nf4 _ _ _ => simp at hbranch
  | nf5 _ => simp at hbranch

private theorem step_sound {top bottom : Nat} {O : Ontology} {U : List Nat}
    {s : State} (hs : SoundState s.toMaterialization top bottom O) :
    SoundState (step bottom O U s).toMaterialization top bottom O where
  subSound hmem := by
    simp only [State.toMaterialization, step, List.mem_append, List.mem_dedup,
      List.mem_filter] at hmem
    rcases hmem with hmem | ⟨hmem, _⟩
    · exact hs.subSound hmem
    · exact subConsequences_sound hs hmem
  edgeSound hmem := by
    simp only [State.toMaterialization, step, List.mem_append, List.mem_dedup,
      List.mem_filter] at hmem
    rcases hmem with hmem | ⟨hmem, _⟩
    · exact hs.edgeSound hmem
    · exact edgeConsequences_sound hs hmem

private theorem saturate_sound {top bottom : Nat} {O : Ontology} {U : List Nat} :
    ∀ (fuel : Nat) {s : State},
      SoundState s.toMaterialization top bottom O →
      SoundState (saturate bottom O U fuel s).toMaterialization top bottom O
  | 0, _, hs => hs
  | fuel + 1, s, hs => by
      dsimp only [saturate]
      split
      · exact hs
      · exact saturate_sound fuel (step_sound hs)

private theorem mem_subs_step {bottom : Nat} {O : Ontology} {U : List Nat}
    {s : State} {fact : Nat × Nat} (hmem : fact ∈ s.subs) :
    fact ∈ (step bottom O U s).subs := by
  simp [step, hmem]

private theorem mem_subs_saturate {bottom : Nat} {O : Ontology} {U : List Nat} :
    ∀ (fuel : Nat) {s : State} {fact : Nat × Nat},
      fact ∈ s.subs → fact ∈ (saturate bottom O U fuel s).subs
  | 0, _, _, hmem => hmem
  | fuel + 1, s, _, hmem => by
      dsimp only [saturate]
      split
      · exact hmem
      · exact mem_subs_saturate fuel (mem_subs_step hmem)

private theorem mem_initial_refl {top : Nat} {U : List Nat} {a : Nat} (ha : a ∈ U) :
    (a, a) ∈ (initial top U).subs := by
  simp only [initial, List.mem_flatMap]
  exact ⟨a, ha, by simp⟩

private theorem mem_initial_top {top : Nat} {U : List Nat} {a : Nat} (ha : a ∈ U) :
    (a, top) ∈ (initial top U).subs := by
  simp only [initial, List.mem_flatMap]
  exact ⟨a, ha, by simp⟩

private theorem mem_subs_of_fixpoint {bottom : Nat} {O : Ontology} {U : List Nat}
    {s : State} (hfix : (step bottom O U s).size = s.size)
    {fact : Nat × Nat} (hcons : fact ∈ subConsequences bottom O U s) :
    fact ∈ s.subs := by
  by_contra hnot
  have hmem_new :
      fact ∈ ((subConsequences bottom O U s).filter fun f => decide (f ∉ s.subs)).dedup := by
    rw [List.mem_dedup, List.mem_filter]
    exact ⟨hcons, decide_eq_true hnot⟩
  have hpos := List.length_pos_of_mem hmem_new
  simp only [step, State.size, List.length_append] at hfix
  omega

private theorem mem_edges_of_fixpoint {bottom : Nat} {O : Ontology} {U : List Nat}
    {s : State} (hfix : (step bottom O U s).size = s.size)
    {fact : Nat × (Nat × Nat)} (hcons : fact ∈ edgeConsequences O U s) :
    fact ∈ s.edges := by
  by_contra hnot
  have hmem_new :
      fact ∈ ((edgeConsequences O U s).filter fun f => decide (f ∉ s.edges)).dedup := by
    rw [List.mem_dedup, List.mem_filter]
    exact ⟨hcons, decide_eq_true hnot⟩
  have hpos := List.length_pos_of_mem hmem_new
  simp only [step, State.size, List.length_append] at hfix
  omega

private theorem nf1_mem_subConsequences {bottom : Nat} {O : Ontology} {U : List Nat}
    {s : State} {a sub sup : Nat} (ha : a ∈ U)
    (hsub : (a, sub) ∈ s.subs) (hcl : .nf1 sub sup ∈ O) :
    (a, sup) ∈ subConsequences bottom O U s := by
  simp only [subConsequences, List.mem_flatMap, List.mem_append]
  exact ⟨a, ha, Or.inl ⟨.nf1 sub sup, hcl, by simp [State.hasSubSlow, hsub]⟩⟩

private theorem nf2_mem_subConsequences {bottom : Nat} {O : Ontology} {U : List Nat}
    {s : State} {a left right sup : Nat} (ha : a ∈ U)
    (hl : (a, left) ∈ s.subs) (hr : (a, right) ∈ s.subs)
    (hcl : .nf2 left right sup ∈ O) :
    (a, sup) ∈ subConsequences bottom O U s := by
  simp only [subConsequences, List.mem_flatMap, List.mem_append]
  exact ⟨a, ha, Or.inl ⟨.nf2 left right sup, hcl, by simp [State.hasSubSlow, hl, hr]⟩⟩

private theorem nf5_mem_subConsequences {bottom : Nat} {O : Ontology} {U : List Nat}
    {s : State} {a sub : Nat} (ha : a ∈ U)
    (hsub : (a, sub) ∈ s.subs) (hcl : .nf5 sub ∈ O) :
    (a, bottom) ∈ subConsequences bottom O U s := by
  simp only [subConsequences, List.mem_flatMap, List.mem_append]
  exact ⟨a, ha, Or.inl ⟨.nf5 sub, hcl, by simp [State.hasSubSlow, hsub]⟩⟩

private theorem nf4_mem_subConsequences {bottom : Nat} {O : Ontology} {U : List Nat}
    {s : State} {a target filler sup role : Nat} (ha : a ∈ U)
    (hedge : (a, (role, target)) ∈ s.edges) (hsub : (target, filler) ∈ s.subs)
    (hcl : .nf4 role filler sup ∈ O) :
    (a, sup) ∈ subConsequences bottom O U s := by
  simp only [subConsequences, List.mem_flatMap, List.mem_append]
  refine ⟨a, ha, Or.inl ⟨.nf4 role filler sup, hcl, ?_⟩⟩
  simp only [List.mem_flatMap, List.mem_filter]
  exact ⟨(a, (role, target)), ⟨hedge, by simp⟩, by simp [State.hasSubSlow, hsub]⟩

private theorem bottomEdge_mem_subConsequences {bottom : Nat} {O : Ontology} {U : List Nat}
    {s : State} {a target role : Nat} (ha : a ∈ U)
    (hedge : (a, (role, target)) ∈ s.edges) (hsub : (target, bottom) ∈ s.subs) :
    (a, bottom) ∈ subConsequences bottom O U s := by
  simp only [subConsequences, List.mem_flatMap, List.mem_append, List.mem_filter]
  refine ⟨a, ha, Or.inr ⟨(a, (role, target)), ⟨hedge, by simp⟩, ?_⟩⟩
  simp [State.hasSubSlow, hsub]

private theorem nf3_mem_edgeConsequences {O : Ontology} {U : List Nat}
    {s : State} {a sub filler role : Nat} (ha : a ∈ U)
    (hsub : (a, sub) ∈ s.subs) (hcl : .nf3 sub role filler ∈ O) :
    (a, (role, filler)) ∈ edgeConsequences O U s := by
  simp only [edgeConsequences, List.mem_flatMap]
  exact ⟨a, ha, .nf3 sub role filler, hcl, by simp [State.hasSubSlow, hsub]⟩

private theorem nf6_mem_edgeConsequences {O : Ontology} {U : List Nat}
    {s : State} {a target sub sup : Nat} (ha : a ∈ U)
    (hedge : (a, (sub, target)) ∈ s.edges) (hcl : .nf6 sub sup ∈ O) :
    (a, (sup, target)) ∈ edgeConsequences O U s := by
  simp only [edgeConsequences, List.mem_flatMap]
  refine ⟨a, ha, .nf6 sub sup, hcl, ?_⟩
  simp only [List.mem_map, List.mem_filter]
  exact ⟨(a, (sub, target)), ⟨hedge, by simp⟩, rfl⟩

private theorem nf7_mem_edgeConsequences {O : Ontology} {U : List Nat}
    {s : State} {a middle target first second sup : Nat} (ha : a ∈ U)
    (hfirst : (a, (first, middle)) ∈ s.edges)
    (hsecond : (middle, (second, target)) ∈ s.edges)
    (hcl : .nf7 first second sup ∈ O) :
    (a, (sup, target)) ∈ edgeConsequences O U s := by
  simp only [edgeConsequences, List.mem_flatMap]
  refine ⟨a, ha, .nf7 first second sup, hcl, ?_⟩
  simp only [List.mem_flatMap, List.mem_map, List.mem_filter]
  exact ⟨(a, (first, middle)), ⟨hfirst, by simp⟩,
    (middle, (second, target)), ⟨hsecond, by simp⟩, rfl⟩

private theorem reflexive_mem_edgeConsequences {O : Ontology} {U : List Nat}
    {s : State} {a role : Nat} (ha : a ∈ U) (hcl : .reflexive role ∈ O) :
    (a, (role, a)) ∈ edgeConsequences O U s := by
  simp only [edgeConsequences, List.mem_flatMap]
  exact ⟨a, ha, .reflexive role, hcl, by simp⟩

private theorem fixpoint_closedOn {top bottom : Nat} {named : List Nat} {O : Ontology}
    {s : State}
    (hinit : ∀ fact ∈ (initial top (contextUniverse top bottom named O)).subs,
      fact ∈ s.subs)
    (hfix : (step bottom O (contextUniverse top bottom named O) s).size = s.size) :
    ClosedStateOn (fun a => a ∈ contextUniverse top bottom named O)
      s.toMaterialization top bottom O where
  fillerIn hcl := mem_universe_of_concept hcl (by simp [clauseConcepts])
  initRefl _ ha := hinit _ (mem_initial_refl ha)
  initTop _ ha := hinit _ (mem_initial_top ha)
  closeNf1 ha hsub hcl :=
    mem_subs_of_fixpoint hfix (nf1_mem_subConsequences ha hsub hcl)
  closeNf2 ha hl hr hcl :=
    mem_subs_of_fixpoint hfix (nf2_mem_subConsequences ha hl hr hcl)
  closeNf5 ha hsub hcl :=
    mem_subs_of_fixpoint hfix (nf5_mem_subConsequences ha hsub hcl)
  closeNf4 ha _ hedge hsub hcl :=
    mem_subs_of_fixpoint hfix (nf4_mem_subConsequences ha hedge hsub hcl)
  closeBottomEdge ha _ hedge hsub :=
    mem_subs_of_fixpoint hfix (bottomEdge_mem_subConsequences ha hedge hsub)
  closeNf3 ha hsub hcl :=
    mem_edges_of_fixpoint hfix (nf3_mem_edgeConsequences ha hsub hcl)
  closeNf6 ha hedge hcl :=
    mem_edges_of_fixpoint hfix (nf6_mem_edgeConsequences ha hedge hcl)
  closeNf7 ha _ hfirst hsecond hcl :=
    mem_edges_of_fixpoint hfix (nf7_mem_edgeConsequences ha hfirst hsecond hcl)
  closeReflexive := by
    intro a role ha hcl
    exact mem_edges_of_fixpoint hfix (reflexive_mem_edgeConsequences ha hcl)

/-- Cartesian product of two lists. -/
private def prodList {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=
  xs.flatMap fun x => ys.map fun y => (x, y)

private theorem mem_prodList {α β : Type} {xs : List α} {ys : List β} {p : α × β} :
    p ∈ prodList xs ys ↔ p.1 ∈ xs ∧ p.2 ∈ ys := by
  rcases p with ⟨a, b⟩
  simp [prodList]

private theorem length_prodList {α β : Type} (xs : List α) (ys : List β) :
    (prodList xs ys).length = xs.length * ys.length := by
  induction xs with
  | nil => simp [prodList]
  | cons x xs ih =>
      simp only [prodList, List.flatMap_cons, List.length_append, List.length_map,
        List.length_cons] at ih ⊢
      rw [ih, Nat.add_mul, Nat.one_mul, Nat.add_comm]

private theorem nodup_length_le_of_subset {α : Type} [DecidableEq α] :
    ∀ {l u : List α}, l.Nodup → (∀ x ∈ l, x ∈ u) → l.length ≤ u.length
  | [], _, _, _ => Nat.zero_le _
  | a :: as, u, hl, hsub => by
      rcases List.nodup_cons.mp hl with ⟨ha_not_mem, has_nodup⟩
      have ha_u : a ∈ u := hsub a List.mem_cons_self
      have hsub_erase : ∀ x ∈ as, x ∈ u.erase a := by
        intro x hx
        have hne : x ≠ a := fun hEq => ha_not_mem (hEq ▸ hx)
        exact (List.mem_erase_of_ne hne).mpr (hsub x (List.mem_cons_of_mem a hx))
      have ih := nodup_length_le_of_subset has_nodup hsub_erase
      have hlen_erase := List.length_erase_of_mem ha_u
      have hpos := List.length_pos_of_mem ha_u
      simp only [List.length_cons]
      omega

private theorem length_dedup_append_le {α : Type} [DecidableEq α]
    {l n : List α} (hn : n.Nodup) (hdisj : ∀ x ∈ n, x ∉ l) :
    l.dedup.length + n.length ≤ (l ++ n).dedup.length := by
  have hnodup : (l.dedup ++ n).Nodup := by
    refine List.nodup_append.mpr ⟨List.nodup_dedup l, hn, ?_⟩
    intro x hx y hy hEq
    subst hEq
    exact hdisj x hy (List.mem_dedup.mp hx)
  have hsub : ∀ x ∈ l.dedup ++ n, x ∈ (l ++ n).dedup := by
    intro x hx
    rw [List.mem_dedup, List.mem_append]
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact Or.inl (List.mem_dedup.mp hx)
    · exact Or.inr hx
  have hle := nodup_length_le_of_subset hnodup hsub
  simpa only [List.length_append] using hle

/-- Number of distinct facts in a state. -/
private def State.uniqSize (s : State) : Nat :=
  s.subs.dedup.length + s.edges.dedup.length

private theorem uniqSize_step_gt {bottom : Nat} {O : Ontology} {U : List Nat}
    {s : State} (hne : (step bottom O U s).size ≠ s.size) :
    s.uniqSize < (step bottom O U s).uniqSize := by
  let newSubs :=
    ((subConsequences bottom O U s).filter fun fact => decide (fact ∉ s.subs)).dedup
  let newEdges :=
    ((edgeConsequences O U s).filter fun fact => decide (fact ∉ s.edges)).dedup
  have hsub_le : s.subs.dedup.length + newSubs.length ≤ (s.subs ++ newSubs).dedup.length := by
    apply length_dedup_append_le (List.nodup_dedup _)
    intro x hx
    rw [List.mem_dedup, List.mem_filter, decide_eq_true_eq] at hx
    exact hx.2
  have hedge_le : s.edges.dedup.length + newEdges.length ≤ (s.edges ++ newEdges).dedup.length := by
    apply length_dedup_append_le (List.nodup_dedup _)
    intro x hx
    rw [List.mem_dedup, List.mem_filter, decide_eq_true_eq] at hx
    exact hx.2
  have hsize : (step bottom O U s).size =
      (s.subs.length + newSubs.length) + (s.edges.length + newEdges.length) := by
    simp [step, State.size, newSubs, newEdges]
  have huniq : (step bottom O U s).uniqSize =
      (s.subs ++ newSubs).dedup.length + (s.edges ++ newEdges).dedup.length := rfl
  have horig : s.size = s.subs.length + s.edges.length := rfl
  have horig_u : s.uniqSize = s.subs.dedup.length + s.edges.dedup.length := rfl
  omega

/-- Universe membership invariant for a state during saturation. -/
private structure ScopedState (top bottom : Nat) (named : List Nat) (O : Ontology)
    (s : State) : Prop where
  subsIn : ∀ p ∈ s.subs,
    p.1 ∈ contextUniverse top bottom named O ∧
    p.2 ∈ contextUniverse top bottom named O
  edgesIn : ∀ e ∈ s.edges,
    e.1 ∈ contextUniverse top bottom named O ∧
    e.2.1 ∈ roleUniverse O ∧
    e.2.2 ∈ contextUniverse top bottom named O

private theorem ScopedState.uniqSize_le_factBound {top bottom : Nat} {named : List Nat}
    {O : Ontology} {s : State} (hs : ScopedState top bottom named O s) :
    s.uniqSize ≤ factBound (contextUniverse top bottom named O) (roleUniverse O) := by
  have hsub_le :
      s.subs.dedup.length ≤
        (contextUniverse top bottom named O).length *
          (contextUniverse top bottom named O).length := by
    rw [← length_prodList]
    apply nodup_length_le_of_subset (List.nodup_dedup _)
    intro p hp
    rw [mem_prodList]
    exact hs.subsIn p (List.mem_dedup.mp hp)
  have hedge_le :
      s.edges.dedup.length ≤
        (contextUniverse top bottom named O).length *
          ((roleUniverse O).length * (contextUniverse top bottom named O).length) := by
    rw [← length_prodList (roleUniverse O) (contextUniverse top bottom named O),
      ← length_prodList (contextUniverse top bottom named O)]
    apply nodup_length_le_of_subset (List.nodup_dedup _)
    intro e he
    rw [mem_prodList, mem_prodList]
    exact hs.edgesIn e (List.mem_dedup.mp he)
  unfold State.uniqSize factBound
  omega

private theorem initial_scoped (top bottom : Nat) (named : List Nat) (O : Ontology) :
    ScopedState top bottom named O
      (initial top (contextUniverse top bottom named O)) where
  subsIn p hp := by
    simp only [initial, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with ⟨a, ha, rfl | rfl⟩
    · exact ⟨ha, ha⟩
    · exact ⟨ha, top_mem_contextUniverse top bottom named O⟩
  edgesIn _ he := by
    simp [initial] at he

private theorem subConsequences_scoped {top bottom : Nat} {named : List Nat} {O : Ontology}
    {s : State} {p : Nat × Nat}
    (hp : p ∈ subConsequences bottom O (contextUniverse top bottom named O) s) :
    p.1 ∈ contextUniverse top bottom named O ∧
    p.2 ∈ contextUniverse top bottom named O := by
  rcases p with ⟨a, b⟩
  simp only [subConsequences, List.mem_flatMap, List.mem_append] at hp
  rcases hp with ⟨x, hx, hclause | hedge⟩
  · rcases hclause with ⟨clause, hcl, hbranch⟩
    cases clause with
    | nf1 sub sup =>
        simp only [mem_ite_singleton, Prod.mk.injEq] at hbranch
        rcases hbranch with ⟨_, h1, h2⟩
        rw [h1, h2]
        exact ⟨hx, mem_universe_of_concept hcl (by simp [clauseConcepts])⟩
    | nf2 left right sup =>
        simp only [mem_ite_singleton, Prod.mk.injEq] at hbranch
        rcases hbranch with ⟨_, h1, h2⟩
        rw [h1, h2]
        exact ⟨hx, mem_universe_of_concept hcl (by simp [clauseConcepts])⟩
    | nf5 sub =>
        simp only [mem_ite_singleton, Prod.mk.injEq] at hbranch
        rcases hbranch with ⟨_, h1, h2⟩
        rw [h1, h2]
        exact ⟨hx, bottom_mem_contextUniverse top bottom named O⟩
    | nf4 role filler sup =>
        simp only [List.mem_flatMap, List.mem_filter, mem_ite_singleton,
          Prod.mk.injEq] at hbranch
        rcases hbranch with ⟨_, _, _, h1, h2⟩
        rw [h1, h2]
        exact ⟨hx, mem_universe_of_concept hcl (by simp [clauseConcepts])⟩
    | nf3 _ _ _ => simp at hbranch
    | nf6 _ _ => simp at hbranch
    | nf7 _ _ _ => simp at hbranch
    | reflexive _ => simp at hbranch
  · rcases hedge with ⟨_, _, hif⟩
    simp only [mem_ite_singleton, Prod.mk.injEq] at hif
    rcases hif with ⟨_, h1, h2⟩
    rw [h1, h2]
    exact ⟨hx, bottom_mem_contextUniverse top bottom named O⟩

private theorem edgeConsequences_scoped {top bottom : Nat} {named : List Nat} {O : Ontology}
    {s : State} (hs : ScopedState top bottom named O s)
    {e : Nat × (Nat × Nat)}
    (he : e ∈ edgeConsequences O (contextUniverse top bottom named O) s) :
    e.1 ∈ contextUniverse top bottom named O ∧
    e.2.1 ∈ roleUniverse O ∧
    e.2.2 ∈ contextUniverse top bottom named O := by
  rcases e with ⟨a, role, b⟩
  simp only [edgeConsequences, List.mem_flatMap] at he
  rcases he with ⟨x, hx, clause, hcl, hbranch⟩
  cases clause with
  | nf3 sub r filler =>
      simp only [mem_ite_singleton, Prod.mk.injEq] at hbranch
      rcases hbranch with ⟨_, h1, h2, h3⟩
      rw [h1, h2, h3]
      exact ⟨hx,
        mem_roleUniverse_of_role hcl (by simp [clauseRoles]),
        mem_universe_of_concept hcl (by simp [clauseConcepts])⟩
  | nf6 sub sup =>
      simp only [List.mem_map, List.mem_filter, Prod.mk.injEq] at hbranch
      rcases hbranch with ⟨edge, ⟨he_mem, _⟩, h1, h2, h3⟩
      rw [← h1, ← h2, ← h3]
      exact ⟨hx,
        mem_roleUniverse_of_role hcl (by simp [clauseRoles]),
        (hs.edgesIn edge he_mem).2.2⟩
  | nf7 first second sup =>
      simp only [List.mem_flatMap, List.mem_map, List.mem_filter, Prod.mk.injEq] at hbranch
      rcases hbranch with ⟨_, _, next, ⟨he2_mem, _⟩, h1, h2, h3⟩
      rw [← h1, ← h2, ← h3]
      exact ⟨hx,
        mem_roleUniverse_of_role hcl (by simp [clauseRoles]),
        (hs.edgesIn next he2_mem).2.2⟩
  | reflexive r =>
      simp only [List.mem_singleton, Prod.mk.injEq] at hbranch
      rcases hbranch with ⟨h1, h2, h3⟩
      rw [h1, h2, h3]
      exact ⟨hx, mem_roleUniverse_of_role hcl (by simp [clauseRoles]), hx⟩
  | nf1 _ _ => simp at hbranch
  | nf2 _ _ _ => simp at hbranch
  | nf4 _ _ _ => simp at hbranch
  | nf5 _ => simp at hbranch

private theorem ScopedState.step {top bottom : Nat} {named : List Nat} {O : Ontology}
    {s : State} (hs : ScopedState top bottom named O s) :
    ScopedState top bottom named O
      (ELReference.step bottom O (contextUniverse top bottom named O) s) where
  subsIn p hp := by
    simp only [ELReference.step, List.mem_append, List.mem_dedup, List.mem_filter] at hp
    rcases hp with hp | ⟨hp, _⟩
    · exact hs.subsIn p hp
    · exact subConsequences_scoped hp
  edgesIn e he := by
    simp only [ELReference.step, List.mem_append, List.mem_dedup, List.mem_filter] at he
    rcases he with he | ⟨he, _⟩
    · exact hs.edgesIn e he
    · exact edgeConsequences_scoped hs he

private theorem saturate_fixpoint {top bottom : Nat} {named : List Nat} {O : Ontology} :
    ∀ (fuel : Nat) {s : State},
      ScopedState top bottom named O s →
      factBound (contextUniverse top bottom named O) (roleUniverse O) <
        s.uniqSize + fuel →
      let U := contextUniverse top bottom named O
      (step bottom O U (saturate bottom O U fuel s)).size =
        (saturate bottom O U fuel s).size
  | 0, s, hscope, hfuel => by
      have hbound := hscope.uniqSize_le_factBound
      omega
  | fuel + 1, s, hscope, hfuel => by
      dsimp only [saturate]
      split
      · next hfix => exact hfix
      · next hne =>
          have hgt := uniqSize_step_gt hne
          exact saturate_fixpoint fuel hscope.step (by omega)

private theorem withSets_wf (s : State) : WellFormedState s.withSets where
  sub_iff p := by simp [State.withSets]
  edge_iff e := by simp [State.withSets]

private theorem toMaterialization_withSets (s : State) :
    s.withSets.toMaterialization = s.toMaterialization := rfl

private theorem slowClosure_wf (top bottom : Nat) (named : List Nat) (O : Ontology) :
    WellFormedState (slowClosure top bottom named O) :=
  withSets_wf _

private theorem slowClosure_closedOn (top bottom : Nat) (named : List Nat) (O : Ontology) :
    ClosedStateOn (fun a => a ∈ contextUniverse top bottom named O)
      (slowClosure top bottom named O).toMaterialization top bottom O := by
  unfold slowClosure
  rw [toMaterialization_withSets]
  apply fixpoint_closedOn
  · intro fact hmem
    exact mem_subs_saturate _ hmem
  · exact saturate_fixpoint
      (factBound (contextUniverse top bottom named O) (roleUniverse O) + 1)
      (initial_scoped top bottom named O)
      (by omega)

private theorem slowClosure_sound (top bottom : Nat) (named : List Nat) (O : Ontology) :
    SoundState (slowClosure top bottom named O).toMaterialization top bottom O := by
  unfold slowClosure
  rw [toMaterialization_withSets]
  exact saturate_sound _ (initial_sound top bottom O _)

/-!
## Fast indexed worklist saturation and closure check
-/

def fastUniverse (top bottom : Nat) (named : List Nat) (O : Ontology) : List Nat :=
  (TreeSet.ofList (top :: bottom :: named ++ O.flatMap clauseConcepts)).toList

private theorem mem_fastUniverse_iff {top bottom : Nat} {named : List Nat}
    {O : Ontology} {a : Nat} :
    a ∈ fastUniverse top bottom named O ↔ a ∈ contextUniverse top bottom named O := by
  simp [fastUniverse, contextUniverse]

def clauseKey : ELCompletion.Clause Nat Nat → Nat × (Nat × (Nat × Nat))
  | .nf1 sub sup => (0, (sub, (sup, 0)))
  | .nf2 left right sup => (1, (left, (right, sup)))
  | .nf3 sub role filler => (2, (sub, (role, filler)))
  | .nf4 role filler sup => (3, (role, (filler, sup)))
  | .nf5 sub => (4, (sub, (0, 0)))
  | .nf6 sub sup => (5, (sub, (sup, 0)))
  | .nf7 first second sup => (6, (first, (second, sup)))
  | .reflexive role => (7, (role, (0, 0)))

private theorem clauseKey_inj {c1 c2 : ELCompletion.Clause Nat Nat} :
    clauseKey c1 = clauseKey c2 ↔ c1 = c2 := by
  cases c1 <;> cases c2 <;> simp [clauseKey]

def hasClause (Oset : TreeSet (Nat × (Nat × (Nat × Nat))))
    (cl : ELCompletion.Clause Nat Nat) : Bool :=
  Oset.contains (clauseKey cl)

private theorem hasClause_ofList (O : Ontology) (cl : ELCompletion.Clause Nat Nat) :
    hasClause (TreeSet.ofList (O.map clauseKey)) cl = true ↔ cl ∈ O := by
  simp [hasClause, clauseKey_inj]

inductive SubRule where
  | refl (a : Nat)
  | top (a : Nat)
  | nf1 (a sub sup : Nat)
  | nf2 (a left right sup : Nat)
  | nf5 (a sub : Nat)
  | nf4 (a role target filler sup : Nat)
  | bottomEdge (a role target : Nat)

def SubRule.conclusion (top bottom : Nat) : SubRule → Nat × Nat
  | .refl a => (a, a)
  | .top a => (a, top)
  | .nf1 a _ sup => (a, sup)
  | .nf2 a _ _ sup => (a, sup)
  | .nf5 a _ => (a, bottom)
  | .nf4 a _ _ _ sup => (a, sup)
  | .bottomEdge a _ _ => (a, bottom)

def SubRule.valid (Oset : TreeSet (Nat × (Nat × (Nat × Nat))))
    (bottom : Nat) (s : State) : SubRule → Bool
  | .refl _ => true
  | .top _ => true
  | .nf1 a sub sup => s.hasSub a sub && hasClause Oset (.nf1 sub sup)
  | .nf2 a left right sup =>
      s.hasSub a left && s.hasSub a right && hasClause Oset (.nf2 left right sup)
  | .nf5 a sub => s.hasSub a sub && hasClause Oset (.nf5 sub)
  | .nf4 a role target filler sup =>
      s.hasEdge a role target && s.hasSub target filler &&
        hasClause Oset (.nf4 role filler sup)
  | .bottomEdge a role target => s.hasEdge a role target && s.hasSub target bottom

def State.tryAddSub (top bottom : Nat)
    (Oset : TreeSet (Nat × (Nat × (Nat × Nat))))
    (r : SubRule) (s : State) : State × Bool :=
  let p := r.conclusion top bottom
  if !s.subSet.contains p && r.valid Oset bottom s then
    ({ s with subs := p :: s.subs, subSet := s.subSet.insert p }, true)
  else
    (s, false)

inductive EdgeRule where
  | nf3 (a sub role filler : Nat)
  | nf6 (a sub sup target : Nat)
  | nf7 (a first middle second target sup : Nat)
  | reflexive (a role : Nat)

def EdgeRule.conclusion : EdgeRule → Nat × (Nat × Nat)
  | .nf3 a _ role filler => (a, (role, filler))
  | .nf6 a _ sup target => (a, (sup, target))
  | .nf7 a _ _ _ target sup => (a, (sup, target))
  | .reflexive a role => (a, (role, a))

def EdgeRule.valid (Oset : TreeSet (Nat × (Nat × (Nat × Nat))))
    (s : State) : EdgeRule → Bool
  | .nf3 a sub role filler => s.hasSub a sub && hasClause Oset (.nf3 sub role filler)
  | .nf6 a sub sup target => s.hasEdge a sub target && hasClause Oset (.nf6 sub sup)
  | .nf7 a first middle second target sup =>
      s.hasEdge a first middle && s.hasEdge middle second target &&
        hasClause Oset (.nf7 first second sup)
  | .reflexive _ role => hasClause Oset (.reflexive role)

def State.tryAddEdge (Oset : TreeSet (Nat × (Nat × (Nat × Nat))))
    (r : EdgeRule) (s : State) : State × Bool :=
  let e := r.conclusion
  if !s.edgeSet.contains e && r.valid Oset s then
    ({ s with edges := e :: s.edges, edgeSet := s.edgeSet.insert e }, true)
  else
    (s, false)

private structure GoodState (top bottom : Nat) (O : Ontology) (s : State) : Prop where
  wf : WellFormedState s
  sound : SoundState s.toMaterialization top bottom O

private theorem SubRule.valid_sound {top bottom : Nat} {O : Ontology}
    {Oset : TreeSet (Nat × (Nat × (Nat × Nat)))}
    (hO : ∀ cl, hasClause Oset cl = true ↔ cl ∈ O)
    {s : State} (hwf : WellFormedState s)
    (hs : SoundState s.toMaterialization top bottom O)
    {r : SubRule} (hval : r.valid Oset bottom s = true) :
    Sub top bottom O (r.conclusion top bottom).1 (r.conclusion top bottom).2 := by
  cases r with
  | refl a => exact Sub.refl a
  | top a => exact Sub.top a
  | nf1 a sub sup =>
      simp only [SubRule.valid, Bool.and_eq_true, State.hasSub, hwf.sub_iff, hO] at hval
      exact Sub.nf1 (hs.subSound hval.1) hval.2
  | nf2 a left right sup =>
      simp only [SubRule.valid, Bool.and_eq_true, State.hasSub, hwf.sub_iff, hO] at hval
      exact Sub.nf2 (hs.subSound hval.1.1) (hs.subSound hval.1.2) hval.2
  | nf5 a sub =>
      simp only [SubRule.valid, Bool.and_eq_true, State.hasSub, hwf.sub_iff, hO] at hval
      exact Sub.nf5 (hs.subSound hval.1) hval.2
  | nf4 a role target filler sup =>
      simp only [SubRule.valid, Bool.and_eq_true, State.hasEdge, State.hasSub,
        hwf.edge_iff, hwf.sub_iff, hO] at hval
      exact Sub.nf4 (hs.edgeSound hval.1.1) (hs.subSound hval.1.2) hval.2
  | bottomEdge a role target =>
      simp only [SubRule.valid, Bool.and_eq_true, State.hasEdge, State.hasSub,
        hwf.edge_iff, hwf.sub_iff] at hval
      exact Sub.bottomEdge (hs.edgeSound hval.1) (hs.subSound hval.2)

private theorem EdgeRule.valid_sound {top bottom : Nat} {O : Ontology}
    {Oset : TreeSet (Nat × (Nat × (Nat × Nat)))}
    (hO : ∀ cl, hasClause Oset cl = true ↔ cl ∈ O)
    {s : State} (hwf : WellFormedState s)
    (hs : SoundState s.toMaterialization top bottom O)
    {r : EdgeRule} (hval : r.valid Oset s = true) :
    Edge top bottom O r.conclusion.1 r.conclusion.2.1 r.conclusion.2.2 := by
  cases r with
  | nf3 a sub role filler =>
      simp only [EdgeRule.valid, Bool.and_eq_true, State.hasSub, hwf.sub_iff, hO] at hval
      exact Edge.nf3 (hs.subSound hval.1) hval.2
  | nf6 a sub sup target =>
      simp only [EdgeRule.valid, Bool.and_eq_true, State.hasEdge, hwf.edge_iff, hO] at hval
      exact Edge.nf6 (hs.edgeSound hval.1) hval.2
  | nf7 a first middle second target sup =>
      simp only [EdgeRule.valid, Bool.and_eq_true, State.hasEdge, hwf.edge_iff, hO] at hval
      exact Edge.nf7 (hs.edgeSound hval.1.1) (hs.edgeSound hval.1.2) hval.2
  | reflexive a role =>
      simp only [EdgeRule.valid, hO] at hval
      exact Edge.reflexive a hval

private theorem tryAddSub_good {top bottom : Nat} {O : Ontology}
    {Oset : TreeSet (Nat × (Nat × (Nat × Nat)))}
    (hO : ∀ cl, hasClause Oset cl = true ↔ cl ∈ O)
    (r : SubRule) {s : State} (hs : GoodState top bottom O s) :
    GoodState top bottom O (s.tryAddSub top bottom Oset r).1 := by
  dsimp only [State.tryAddSub]
  split
  · next hcond =>
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
      have hderiv := SubRule.valid_sound hO hs.wf hs.sound hcond.2
      refine ⟨⟨?_, hs.wf.edge_iff⟩, ⟨?_, hs.sound.edgeSound⟩⟩
      · intro p
        rw [TreeSet.contains_insert]
        by_cases hp : r.conclusion top bottom = p
        · subst hp; simp
        · have hp' : p ≠ r.conclusion top bottom := Ne.symm hp
          simp [hp, hp', hs.wf.sub_iff]
      · intro a b hmem
        rcases List.mem_cons.mp hmem with hEq | hmem'
        · rw [Prod.ext_iff] at hEq
          rcases hEq with ⟨rfl, rfl⟩
          exact hderiv
        · exact hs.sound.subSound hmem'
  · exact hs

private theorem tryAddEdge_good {top bottom : Nat} {O : Ontology}
    {Oset : TreeSet (Nat × (Nat × (Nat × Nat)))}
    (hO : ∀ cl, hasClause Oset cl = true ↔ cl ∈ O)
    (r : EdgeRule) {s : State} (hs : GoodState top bottom O s) :
    GoodState top bottom O (s.tryAddEdge Oset r).1 := by
  dsimp only [State.tryAddEdge]
  split
  · next hcond =>
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
      have hderiv := EdgeRule.valid_sound hO hs.wf hs.sound hcond.2
      refine ⟨⟨hs.wf.sub_iff, ?_⟩, ⟨hs.sound.subSound, ?_⟩⟩
      · intro e
        rw [TreeSet.contains_insert]
        by_cases he : r.conclusion = e
        · subst he; simp
        · have he' : e ≠ r.conclusion := Ne.symm he
          simp [he, he', hs.wf.edge_iff]
      · intro a role b hmem
        rcases List.mem_cons.mp hmem with hEq | hmem'
        · have h1 : a = r.conclusion.1 := congrArg Prod.fst hEq
          have h2 : role = r.conclusion.2.1 := congrArg (fun x => x.2.1) hEq
          have h3 : b = r.conclusion.2.2 := congrArg (fun x => x.2.2) hEq
          subst h1 h2 h3
          exact hderiv
        · exact hs.sound.edgeSound hmem'
  · exact hs

structure ClauseIndex where
  nf1BySub : TreeMap Nat (List Nat)
  nf2ByLeft : TreeMap Nat (List (Nat × Nat))
  nf2ByRight : TreeMap Nat (List (Nat × Nat))
  nf3BySub : TreeMap Nat (List (Nat × Nat))
  nf4ByFiller : TreeMap Nat (List (Nat × Nat))
  nf4ByRoleFiller : TreeMap (Nat × Nat) (List Nat)
  nf4Roles : TreeSet Nat
  nf5Set : TreeSet Nat
  nf6BySub : TreeMap Nat (List Nat)
  nf7ByFirst : TreeMap Nat (List (Nat × Nat))
  nf7BySecond : TreeMap Nat (List (Nat × Nat))
  reflexive : List Nat

def buildClauseIndex (O : Ontology) : ClauseIndex :=
  O.foldl (fun idx cl =>
    match cl with
    | .nf1 sub sup =>
        { idx with nf1BySub := idx.nf1BySub.alter sub (fun old => some (sup :: old.getD [])) }
    | .nf2 left right sup =>
        { idx with
          nf2ByLeft := idx.nf2ByLeft.alter left (fun old => some ((right, sup) :: old.getD []))
          nf2ByRight := idx.nf2ByRight.alter right (fun old => some ((left, sup) :: old.getD [])) }
    | .nf3 sub role filler =>
        { idx with nf3BySub := idx.nf3BySub.alter sub (fun old => some ((role, filler) :: old.getD [])) }
    | .nf4 role filler sup =>
        { idx with
          nf4ByFiller := idx.nf4ByFiller.alter filler (fun old => some ((role, sup) :: old.getD []))
          nf4ByRoleFiller := idx.nf4ByRoleFiller.alter (role, filler) (fun old => some (sup :: old.getD []))
          nf4Roles := idx.nf4Roles.insert role }
    | .nf5 sub =>
        { idx with nf5Set := idx.nf5Set.insert sub }
    | .nf6 sub sup =>
        { idx with nf6BySub := idx.nf6BySub.alter sub (fun old => some (sup :: old.getD [])) }
    | .nf7 first second sup =>
        { idx with
          nf7ByFirst := idx.nf7ByFirst.alter first (fun old => some ((second, sup) :: old.getD []))
          nf7BySecond := idx.nf7BySecond.alter second (fun old => some ((first, sup) :: old.getD [])) }
    | .reflexive role =>
        { idx with reflexive := role :: idx.reflexive })
    { nf1BySub := ∅, nf2ByLeft := ∅, nf2ByRight := ∅, nf3BySub := ∅
      nf4ByFiller := ∅, nf4ByRoleFiller := ∅, nf4Roles := ∅, nf5Set := ∅
      nf6BySub := ∅, nf7ByFirst := ∅, nf7BySecond := ∅, reflexive := [] }

structure WorkState where
  state : State
  subQueue : List (Nat × Nat)
  edgeQueue : List (Nat × (Nat × Nat))
  subsOf : TreeMap Nat (List Nat)
  inEdges : TreeMap (Nat × Nat) (List Nat)
  inEdgesAll : TreeMap Nat (List (Nat × Nat))
  outEdges : TreeMap (Nat × Nat) (List Nat)

def WorkState.pushSub (top bottom : Nat)
    (Oset : TreeSet (Nat × (Nat × (Nat × Nat))))
    (r : SubRule) (ws : WorkState) : WorkState :=
  let res := ws.state.tryAddSub top bottom Oset r
  if res.2 then
    let p := r.conclusion top bottom
    { ws with
      state := res.1
      subQueue := p :: ws.subQueue
      subsOf := ws.subsOf.alter p.1 (fun old => some (p.2 :: old.getD [])) }
  else
    { ws with state := res.1 }

def WorkState.pushEdge (Oset : TreeSet (Nat × (Nat × (Nat × Nat))))
    (r : EdgeRule) (ws : WorkState) : WorkState :=
  let res := ws.state.tryAddEdge Oset r
  if res.2 then
    let e := r.conclusion
    let a := e.1
    let role := e.2.1
    let target := e.2.2
    { ws with
      state := res.1
      edgeQueue := e :: ws.edgeQueue
      inEdges := ws.inEdges.alter (target, role) (fun old => some (a :: old.getD []))
      inEdgesAll := ws.inEdgesAll.alter target (fun old => some ((a, role) :: old.getD []))
      outEdges := ws.outEdges.alter (a, role) (fun old => some (target :: old.getD [])) }
  else
    { ws with state := res.1 }

private theorem pushSub_good {top bottom : Nat} {O : Ontology}
    {Oset : TreeSet (Nat × (Nat × (Nat × Nat)))}
    (hO : ∀ cl, hasClause Oset cl = true ↔ cl ∈ O)
    (r : SubRule) {ws : WorkState} (h : GoodState top bottom O ws.state) :
    GoodState top bottom O (ws.pushSub top bottom Oset r).state := by
  have heq : (ws.pushSub top bottom Oset r).state = (ws.state.tryAddSub top bottom Oset r).1 := by
    dsimp only [WorkState.pushSub]
    split <;> rfl
  rw [heq]
  exact tryAddSub_good hO r h

private theorem pushEdge_good {top bottom : Nat} {O : Ontology}
    {Oset : TreeSet (Nat × (Nat × (Nat × Nat)))}
    (hO : ∀ cl, hasClause Oset cl = true ↔ cl ∈ O)
    (r : EdgeRule) {ws : WorkState} (h : GoodState top bottom O ws.state) :
    GoodState top bottom O (ws.pushEdge Oset r).state := by
  have heq : (ws.pushEdge Oset r).state = (ws.state.tryAddEdge Oset r).1 := by
    dsimp only [WorkState.pushEdge]
    split <;> rfl
  rw [heq]
  exact tryAddEdge_good hO r h

private theorem foldl_good {α : Type} {top bottom : Nat} {O : Ontology}
    (f : WorkState → α → WorkState)
    (hf : ∀ ws x, GoodState top bottom O ws.state → GoodState top bottom O (f ws x).state)
    (l : List α) {ws : WorkState} (h : GoodState top bottom O ws.state) :
    GoodState top bottom O (l.foldl f ws).state := by
  induction l generalizing ws with
  | nil => exact h
  | cons x xs ih => exact ih (hf ws x h)

private theorem ite_good {top bottom : Nat} {O : Ontology} (c : Bool)
    {t e : WorkState}
    (ht : GoodState top bottom O t.state)
    (he : GoodState top bottom O e.state) :
    GoodState top bottom O (if c then t else e).state := by
  split <;> assumption

def processSub (top bottom : Nat)
    (Oset : TreeSet (Nat × (Nat × (Nat × Nat))))
    (idx : ClauseIndex) (a b : Nat) (ws : WorkState) : WorkState :=
  let ws := (idx.nf1BySub.getD b []).foldl
    (fun ws sup => ws.pushSub top bottom Oset (.nf1 a b sup)) ws
  let ws := (idx.nf2ByLeft.getD b []).foldl
    (fun ws p =>
      if ws.state.hasSub a p.1 then ws.pushSub top bottom Oset (.nf2 a b p.1 p.2)
      else ws) ws
  let ws := (idx.nf2ByRight.getD b []).foldl
    (fun ws p =>
      if ws.state.hasSub a p.1 then ws.pushSub top bottom Oset (.nf2 a p.1 b p.2)
      else ws) ws
  let ws := (idx.nf3BySub.getD b []).foldl
    (fun ws p => ws.pushEdge Oset (.nf3 a b p.1 p.2)) ws
  let ws :=
    if idx.nf5Set.contains b then ws.pushSub top bottom Oset (.nf5 a b)
    else ws
  let ws := (idx.nf4ByFiller.getD b []).foldl
    (fun ws p =>
      (ws.inEdges.getD (a, p.1) []).foldl
        (fun ws parent => ws.pushSub top bottom Oset (.nf4 parent p.1 a b p.2)) ws) ws
  let ws :=
    if b == bottom then
      (ws.inEdgesAll.getD a []).foldl
        (fun ws p => ws.pushSub top bottom Oset (.bottomEdge p.1 p.2 a)) ws
    else ws
  ws

private theorem processSub_good {top bottom : Nat} {O : Ontology}
    {Oset : TreeSet (Nat × (Nat × (Nat × Nat)))}
    (hO : ∀ cl, hasClause Oset cl = true ↔ cl ∈ O)
    (idx : ClauseIndex) (a b : Nat) {ws : WorkState}
    (h : GoodState top bottom O ws.state) :
    GoodState top bottom O (processSub top bottom Oset idx a b ws).state := by
  dsimp only [processSub]
  refine ite_good _ (foldl_good _ (fun _ _ hw => pushSub_good hO _ hw) _ ?_) ?_ <;>
  refine foldl_good _ (fun _ _ hw =>
    foldl_good _ (fun _ _ hw2 => pushSub_good hO _ hw2) _ hw) _ ?_ <;>
  refine ite_good _ (pushSub_good hO _ ?_) ?_ <;>
  refine foldl_good _ (fun _ _ hw => pushEdge_good hO _ hw) _ ?_ <;>
  refine foldl_good _ (fun _ _ hw => ite_good _ (pushSub_good hO _ hw) hw) _ ?_ <;>
  refine foldl_good _ (fun _ _ hw => ite_good _ (pushSub_good hO _ hw) hw) _ ?_ <;>
  exact foldl_good _ (fun _ _ hw => pushSub_good hO _ hw) _ h

def processEdge (top bottom : Nat)
    (Oset : TreeSet (Nat × (Nat × (Nat × Nat))))
    (idx : ClauseIndex) (a role target : Nat) (ws : WorkState) : WorkState :=
  let ws :=
    if ws.state.hasSub target bottom then
      ws.pushSub top bottom Oset (.bottomEdge a role target)
    else ws
  let ws :=
    if idx.nf4Roles.contains role then
      (ws.subsOf.getD target []).foldl
        (fun ws filler =>
          (idx.nf4ByRoleFiller.getD (role, filler) []).foldl
            (fun ws sup => ws.pushSub top bottom Oset (.nf4 a role target filler sup)) ws) ws
    else ws
  let ws := (idx.nf6BySub.getD role []).foldl
    (fun ws sup => ws.pushEdge Oset (.nf6 a role sup target)) ws
  let ws := (idx.nf7ByFirst.getD role []).foldl
    (fun ws p =>
      (ws.outEdges.getD (target, p.1) []).foldl
        (fun ws last => ws.pushEdge Oset (.nf7 a role target p.1 last p.2)) ws) ws
  let ws := (idx.nf7BySecond.getD role []).foldl
    (fun ws p =>
      (ws.inEdges.getD (a, p.1) []).foldl
        (fun ws prev => ws.pushEdge Oset (.nf7 prev p.1 a role target p.2)) ws) ws
  ws

private theorem processEdge_good {top bottom : Nat} {O : Ontology}
    {Oset : TreeSet (Nat × (Nat × (Nat × Nat)))}
    (hO : ∀ cl, hasClause Oset cl = true ↔ cl ∈ O)
    (idx : ClauseIndex) (a role target : Nat) {ws : WorkState}
    (h : GoodState top bottom O ws.state) :
    GoodState top bottom O (processEdge top bottom Oset idx a role target ws).state := by
  dsimp only [processEdge]
  refine foldl_good _ (fun _ _ hw =>
    foldl_good _ (fun _ _ hw2 => pushEdge_good hO _ hw2) _ hw) _ ?_
  refine foldl_good _ (fun _ _ hw =>
    foldl_good _ (fun _ _ hw2 => pushEdge_good hO _ hw2) _ hw) _ ?_
  refine foldl_good _ (fun _ _ hw => pushEdge_good hO _ hw) _ ?_
  refine ite_good _ (foldl_good _ (fun _ _ hw =>
    foldl_good _ (fun _ _ hw2 => pushSub_good hO _ hw2) _ hw) _ ?_) ?_ <;>
  exact ite_good _ (pushSub_good hO _ h) h

def workLoop (top bottom : Nat)
    (Oset : TreeSet (Nat × (Nat × (Nat × Nat))))
    (idx : ClauseIndex) : Nat → WorkState → State
  | 0, ws => ws.state
  | fuel + 1, ws =>
      match ws.subQueue with
      | (a, b) :: rest =>
          workLoop top bottom Oset idx fuel
            (processSub top bottom Oset idx a b { ws with subQueue := rest })
      | [] =>
          match ws.edgeQueue with
          | (a, (role, target)) :: rest =>
              workLoop top bottom Oset idx fuel
                (processEdge top bottom Oset idx a role target { ws with edgeQueue := rest })
          | [] => ws.state

private theorem workLoop_good {top bottom : Nat} {O : Ontology}
    {Oset : TreeSet (Nat × (Nat × (Nat × Nat)))}
    (hO : ∀ cl, hasClause Oset cl = true ↔ cl ∈ O)
    (idx : ClauseIndex) :
    ∀ (fuel : Nat) {ws : WorkState},
      GoodState top bottom O ws.state →
      GoodState top bottom O (workLoop top bottom Oset idx fuel ws)
  | 0, _, h => h
  | fuel + 1, ws, h => by
      dsimp only [workLoop]
      split
      · exact workLoop_good hO idx fuel (processSub_good hO idx _ _ h)
      · split
        · exact workLoop_good hO idx fuel (processEdge_good hO idx _ _ _ h)
        · exact h

def fastSaturate (top bottom : Nat) (U : List Nat) (O : Ontology) : State :=
  let Oset := TreeSet.ofList (O.map clauseKey)
  let idx := buildClauseIndex O
  let ws0 : WorkState :=
    { state := { subs := [], edges := [], subSet := ∅, edgeSet := ∅ }
      subQueue := [], edgeQueue := []
      subsOf := ∅, inEdges := ∅, inEdgesAll := ∅, outEdges := ∅ }
  let ws1 := U.foldl (fun ws a =>
    let ws := ws.pushSub top bottom Oset (.refl a)
    let ws := ws.pushSub top bottom Oset (.top a)
    idx.reflexive.foldl (fun ws role => ws.pushEdge Oset (.reflexive a role)) ws) ws0
  let fuel := U.length * U.length + U.length * (O.length + 1) * U.length + 1
  workLoop top bottom Oset idx fuel ws1

private theorem fastSaturate_good (top bottom : Nat) (U : List Nat) (O : Ontology) :
    GoodState top bottom O (fastSaturate top bottom U O) := by
  dsimp only [fastSaturate]
  have hO := hasClause_ofList O
  have h0 : GoodState top bottom O
      { subs := [], edges := [], subSet := ∅, edgeSet := ∅ } := by
    refine ⟨⟨by simp, by simp⟩, ⟨?_, ?_⟩⟩
    · intro _ _ h; simp [State.toMaterialization] at h
    · intro _ _ _ h; simp [State.toMaterialization] at h
  apply workLoop_good hO
  refine foldl_good _ (fun ws a hw => ?_) _ h0
  refine foldl_good _ (fun _ _ hw2 => pushEdge_good hO _ hw2) _ ?_
  exact pushSub_good hO _ (pushSub_good hO _ hw)

def indexBy {α κ : Type} [Ord κ] (key : α → Option κ) (l : List α) :
    TreeMap κ (List α) :=
  l.foldl (fun table x => match key x with
    | some k => table.alter k (fun old => some (x :: old.getD []))
    | none => table) ∅

private theorem mem_indexBy_aux {α κ : Type} [Ord κ] [TransOrd κ] [LawfulEqOrd κ]
    (key : α → Option κ) (l : List α) :
    ∀ (table : TreeMap κ (List α)) (k : κ) (y : α),
      (y ∈ table.getD k [] ∨ (y ∈ l ∧ key y = some k)) →
        y ∈ (l.foldl (fun table x => match key x with
          | some k => table.alter k (fun old => some (x :: old.getD []))
          | none => table) table).getD k [] := by
  induction l with
  | nil =>
      intro table k y h
      rcases h with h | ⟨h, _⟩
      · exact h
      · simp at h
  | cons x xs ih =>
      intro table k y h
      simp only [List.foldl_cons]
      apply ih
      rcases h with h | ⟨hmem, hkey⟩
      · left
        cases hx : key x with
        | none => simpa using h
        | some k' =>
            simp only []
            rw [TreeMap.getD_alter]
            split
            · next hcmp =>
                have hk : k' = k := LawfulEqCmp.compare_eq_iff_eq.mp hcmp
                subst hk
                simp [TreeMap.getD_eq_getD_getElem?] at h ⊢
                exact Or.inr h
            · exact h
      · rcases List.mem_cons.mp hmem with rfl | hxs
        · left
          rw [hkey]
          simp [TreeMap.getD_alter_self]
        · right
          exact ⟨hxs, hkey⟩

private theorem mem_indexBy {α κ : Type} [Ord κ] [TransOrd κ] [LawfulEqOrd κ]
    (key : α → Option κ) {l : List α} {y : α} {k : κ}
    (hy : y ∈ l) (hkey : key y = some k) :
    y ∈ (indexBy key l).getD k [] :=
  mem_indexBy_aux key l ∅ k y (Or.inr ⟨hy, hkey⟩)

def subPremiseKey : ELCompletion.Clause Nat Nat → Option Nat
  | .nf1 sub _ => some sub
  | .nf2 left _ _ => some left
  | .nf3 sub _ _ => some sub
  | .nf5 sub => some sub
  | _ => none

def nf4FillerKey : ELCompletion.Clause Nat Nat → Option Nat
  | .nf4 _ filler _ => some filler
  | _ => none

def edgePremiseKey : ELCompletion.Clause Nat Nat → Option Nat
  | .nf6 sub _ => some sub
  | .nf7 first _ _ => some first
  | _ => none

def edgeSourceRoleKey (e : Nat × (Nat × Nat)) : Option (Nat × Nat) :=
  some (e.1, e.2.1)

def edgeTargetRoleKey (e : Nat × (Nat × Nat)) : Option (Nat × Nat) :=
  some (e.2.2, e.2.1)

def reflexiveRoles (O : Ontology) : List Nat :=
  O.filterMap fun
    | .reflexive role => some role
    | _ => none

def subClauseClosed (s : State) (bottom a : Nat) :
    ELCompletion.Clause Nat Nat → Bool
  | .nf1 _ sup => s.hasSub a sup
  | .nf2 _ right sup => !s.hasSub a right || s.hasSub a sup
  | .nf3 _ role filler => s.hasEdge a role filler
  | .nf5 _ => s.hasSub a bottom
  | _ => true

def nf4ClauseClosed (s : State)
    (inEdges : TreeMap (Nat × Nat) (List (Nat × (Nat × Nat))))
    (target : Nat) : ELCompletion.Clause Nat Nat → Bool
  | .nf4 role _ sup =>
      (inEdges.getD (target, role) []).all fun e => s.hasSub e.1 sup
  | _ => true

def edgeClauseClosed (s : State)
    (outEdges : TreeMap (Nat × Nat) (List (Nat × (Nat × Nat))))
    (a target : Nat) : ELCompletion.Clause Nat Nat → Bool
  | .nf6 _ sup => s.hasEdge a sup target
  | .nf7 _ second sup =>
      (outEdges.getD (target, second) []).all fun next => s.hasEdge a sup next.2.2
  | _ => true

def checkClosedTree (top bottom : Nat) (U : List Nat) (O : Ontology) (s : State) : Bool :=
  let bySub := indexBy subPremiseKey O
  let byNf4 := indexBy nf4FillerKey O
  let byEdge := indexBy edgePremiseKey O
  let outEdges := indexBy edgeSourceRoleKey s.edges
  let inEdges := indexBy edgeTargetRoleKey s.edges
  let refl := reflexiveRoles O
  U.all (fun a =>
    s.hasSub a a && s.hasSub a top &&
      refl.all fun role => s.hasEdge a role a) &&
  s.subs.all (fun p =>
    (bySub.getD p.2 []).all (subClauseClosed s bottom p.1) &&
    (byNf4.getD p.2 []).all (nf4ClauseClosed s inEdges p.1)) &&
  s.edges.all (fun e =>
    (!s.hasSub e.2.2 bottom || s.hasSub e.1 bottom) &&
    (byEdge.getD e.2.1 []).all (edgeClauseClosed s outEdges e.1 e.2.2))

private theorem checkClosedTree_closedOn {top bottom : Nat} {named : List Nat}
    {O : Ontology} {s : State} (hwf : WellFormedState s)
    (hcheck : checkClosedTree top bottom (fastUniverse top bottom named O) O s = true) :
    ClosedStateOn (fun a => a ∈ contextUniverse top bottom named O)
      s.toMaterialization top bottom O := by
  simp only [checkClosedTree, Bool.and_eq_true, List.all_eq_true] at hcheck
  rcases hcheck with ⟨⟨hU, hsubs⟩, hedges⟩
  have hhasSub : ∀ a b, s.hasSub a b = true ↔ (a, b) ∈ s.subs :=
    fun a b => hwf.sub_iff (a, b)
  have hhasEdge : ∀ a r b, s.hasEdge a r b = true ↔ (a, (r, b)) ∈ s.edges :=
    fun a r b => hwf.edge_iff (a, (r, b))
  refine {
    fillerIn := fun hcl => mem_universe_of_concept hcl (by simp [clauseConcepts])
    initRefl := fun a ha => (hhasSub a a).mp (hU a (mem_fastUniverse_iff.mpr ha)).1.1
    initTop := fun a ha => (hhasSub a top).mp (hU a (mem_fastUniverse_iff.mpr ha)).1.2
    closeNf1 := ?_
    closeNf2 := ?_
    closeNf5 := ?_
    closeNf4 := ?_
    closeBottomEdge := ?_
    closeNf3 := ?_
    closeNf6 := ?_
    closeNf7 := ?_
    closeReflexive := ?_ }
  · intro a sub sup _ hsub hcl
    have hp := (hsubs (a, sub) hsub).1 _ (mem_indexBy subPremiseKey hcl rfl)
    exact (hhasSub a sup).mp (by simpa [subClauseClosed] using hp)
  · intro a left right sup _ hl hr hcl
    have hp := (hsubs (a, left) hl).1 _ (mem_indexBy subPremiseKey hcl rfl)
    simp only [subClauseClosed, Bool.or_eq_true, Bool.not_eq_true'] at hp
    rcases hp with hnot | hsup
    · rw [(hhasSub a right).mpr hr] at hnot
      contradiction
    · exact (hhasSub a sup).mp hsup
  · intro a sub _ hsub hcl
    have hp := (hsubs (a, sub) hsub).1 _ (mem_indexBy subPremiseKey hcl rfl)
    exact (hhasSub a bottom).mp (by simpa [subClauseClosed] using hp)
  · intro a target filler sup role _ _ hedge hfiller hcl
    have hp := (hsubs (target, filler) hfiller).2 _ (mem_indexBy nf4FillerKey hcl rfl)
    simp only [nf4ClauseClosed, List.all_eq_true] at hp
    have he := hp (a, (role, target)) (mem_indexBy edgeTargetRoleKey hedge rfl)
    exact (hhasSub a sup).mp he
  · intro a target role _ _ hedge hbottom
    have he := (hedges (a, (role, target)) hedge).1
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at he
    rcases he with hnot | hsup
    · rw [(hhasSub target bottom).mpr hbottom] at hnot
      contradiction
    · exact (hhasSub a bottom).mp hsup
  · intro a sub filler role _ hsub hcl
    have hp := (hsubs (a, sub) hsub).1 _ (mem_indexBy subPremiseKey hcl rfl)
    exact (hhasEdge a role filler).mp (by simpa [subClauseClosed] using hp)
  · intro a target sub sup _ hedge hcl
    have he := (hedges (a, (sub, target)) hedge).2 _ (mem_indexBy edgePremiseKey hcl rfl)
    exact (hhasEdge a sup target).mp (by simpa [edgeClauseClosed] using he)
  · intro a middle target first second sup _ _ hfirst hsecond hcl
    have he := (hedges (a, (first, middle)) hfirst).2 _ (mem_indexBy edgePremiseKey hcl rfl)
    simp only [edgeClauseClosed, List.all_eq_true] at he
    have hnext := he (middle, (second, target)) (mem_indexBy edgeSourceRoleKey hsecond rfl)
    exact (hhasEdge a sup target).mp hnext
  · intro a role ha hcl
    have hrefl : role ∈ reflexiveRoles O := by
      simp only [reflexiveRoles, List.mem_filterMap]
      exact ⟨.reflexive role, hcl, rfl⟩
    exact (hhasEdge a role a).mp ((hU a (mem_fastUniverse_iff.mpr ha)).2 role hrefl)

/-- The reference closure for one routed source: runs the fast indexed worklist
saturation and checks fixpoint closure in linear time, falling back to the
specification saturation only if the check were ever to decline. -/
def closure (top bottom : Nat) (named : List Nat) (O : Ontology) : State :=
  let U := fastUniverse top bottom named O
  if U.length ≤ 10 then
    slowClosure top bottom named O
  else
    let s := fastSaturate top bottom U O
    if checkClosedTree top bottom U O s then
      s
    else
      slowClosure top bottom named O

private theorem closure_wf (top bottom : Nat) (named : List Nat) (O : Ontology) :
    WellFormedState (closure top bottom named O) := by
  dsimp only [closure]
  split
  · exact slowClosure_wf top bottom named O
  · split
    · exact (fastSaturate_good top bottom _ O).wf
    · exact slowClosure_wf top bottom named O

/-- The reference closure is closed under every ELC rule on the context universe. -/
theorem closure_closedOn (top bottom : Nat) (named : List Nat) (O : Ontology) :
    ClosedStateOn (fun a => a ∈ contextUniverse top bottom named O)
      (closure top bottom named O).toMaterialization top bottom O := by
  dsimp only [closure]
  split
  · exact slowClosure_closedOn top bottom named O
  · split
    · next hcheck =>
        exact checkClosedTree_closedOn (fastSaturate_good top bottom _ O).wf hcheck
    · exact slowClosure_closedOn top bottom named O

/-- Every fact stored in the reference closure has an inductive ELC derivation. -/
theorem closure_sound (top bottom : Nat) (named : List Nat) (O : Ontology) :
    SoundState (closure top bottom named O).toMaterialization top bottom O := by
  dsimp only [closure]
  split
  · exact slowClosure_sound top bottom named O
  · split
    · exact (fastSaturate_good top bottom _ O).sound
    · exact slowClosure_sound top bottom named O

/-- The taxonomy bit on a precomputed closure state: `sub` is unsatisfiable or
`sup` is in its completed label. -/
def referenceBitOf (c : State) (bottom sub sup : Nat) : Bool :=
  c.hasSub sub bottom || c.hasSub sub sup

/-- The taxonomy bit for one coordinate: `sub` is unsatisfiable or `sup` is in
its completed label. -/
def referenceBit (top bottom : Nat) (named : List Nat) (O : Ontology)
    (sub sup : Nat) : Bool :=
  referenceBitOf (closure top bottom named O) bottom sub sup

theorem referenceBit_eq (top bottom : Nat) (named : List Nat) (O : Ontology)
    (sub sup : Nat) :
    referenceBit top bottom named O sub sup =
      referenceBitOf (closure top bottom named O) bottom sub sup := rfl

/-- The inconsistency flag: `top` is labelled `bottom`. -/
def referenceInconsistent (top bottom : Nat) (named : List Nat) (O : Ontology) :
    Bool :=
  (closure top bottom named O).hasSub top bottom

/-- Exactness of `referenceBit` for every subject in the context universe. -/
theorem referenceBit_exact (top bottom : Nat) (named : List Nat) (O : Ontology)
    {sub : Nat} (hsub : sub ∈ contextUniverse top bottom named O) (sup : Nat) :
    referenceBit top bottom named O sub sup = true ↔
      EntailsSub (top := top) (bottom := bottom) O sub sup := by
  rw [entails_iff_materialized_on (closure_closedOn top bottom named O)
    (closure_sound top bottom named O) hsub]
  have hwf := (closure_wf top bottom named O).sub_iff
  simp [referenceBit, referenceBitOf, State.hasSub, State.toMaterialization, hwf]

/-- Exactness of `referenceBit` for every requested named concept. -/
theorem referenceBit_exact_of_named (top bottom : Nat) (named : List Nat)
    (O : Ontology) {sub : Nat} (hsub : sub ∈ named) (sup : Nat) :
    referenceBit top bottom named O sub sup = true ↔
      EntailsSub (top := top) (bottom := bottom) O sub sup :=
  referenceBit_exact top bottom named O (mem_universe_of_named hsub) sup

/-- Exactness of `referenceInconsistent` for ontology unsatisfiability. -/
theorem referenceInconsistent_exact (top bottom : Nat) (named : List Nat)
    (O : Ontology) :
    referenceInconsistent top bottom named O = true ↔
      Unsatisfiable (top := top) (bottom := bottom) O := by
  rw [unsat_iff_materialized_on (closure_closedOn top bottom named O)
    (closure_sound top bottom named O) (top_mem_contextUniverse top bottom named O)]
  have hwf := (closure_wf top bottom named O).sub_iff
  simp [referenceInconsistent, State.hasSub, State.toMaterialization, hwf]

#print axioms mem_universe_of_concept
#print axioms top_mem_contextUniverse
#print axioms bottom_mem_contextUniverse
#print axioms mem_universe_of_named
#print axioms closure_closedOn
#print axioms closure_sound
#print axioms referenceBit_exact
#print axioms referenceBit_exact_of_named
#print axioms referenceInconsistent_exact

end ContextCalculus.ELReference
