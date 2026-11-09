import ContextCalculus.ELCompletionRelativeRefinement
import Mathlib.Data.List.Dedup

/-!
# Executable reference saturation for the pure ELC calculus

This module is the reference procedure of the v1.6.0 completeness proof for
the EL fragment (`docs/V1.6.0-COMPLETENESS-PLAN.md`, section 4.1).  It
computes the closure of `ELCompletion.Sub`/`Edge` over a finite universe by
plain fixpoint iteration and proves the result closed on that universe and
sound.  Combined with `entails_iff_materialized_on`, the readout
`referenceBit` is exact for every requested named concept.

The universe is `top`, `bottom`, the requested named concepts and every
concept name of the ontology.  A state is a pair of duplicate-free fact lists.
One `step` appends every rule consequence that is not yet present.  `saturate`
stops at the first step that adds nothing; the fuel is the size of the fact
universe plus one, which the pigeonhole argument shows is always enough.

Nothing here is tuned for speed.  The procedure is the completeness witness
that the supervisor runs after every production worker has declined; the
production ELC worker remains the fast path.
-/

namespace ContextCalculus.ELReference

open ContextCalculus.ELCompletion

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

theorem mem_universe_of_concept {top bottom : Nat} {named : List Nat}
    {O : Ontology} {clause : ELCompletion.Clause Nat Nat} {concept : Nat}
    (hclause : clause ∈ O) (hconcept : concept ∈ clauseConcepts clause) :
    concept ∈ contextUniverse top bottom named O :=
  List.mem_dedup.mpr (List.mem_append_right _
    (List.mem_flatMap.mpr ⟨clause, hclause, hconcept⟩))

theorem top_mem_contextUniverse (top bottom : Nat) (named : List Nat) (O : Ontology) :
    top ∈ contextUniverse top bottom named O := by
  simp [contextUniverse]

theorem bottom_mem_contextUniverse (top bottom : Nat) (named : List Nat) (O : Ontology) :
    bottom ∈ contextUniverse top bottom named O := by
  simp [contextUniverse]

theorem mem_universe_of_named {top bottom : Nat} {named : List Nat}
    {O : Ontology} {concept : Nat} (hnamed : concept ∈ named) :
    concept ∈ contextUniverse top bottom named O := by
  simp [contextUniverse, hnamed]

/-- Label facts `(context, member)` and edge facts `(context, (role, target))`. -/
structure State where
  subs : List (Nat × Nat)
  edges : List (Nat × (Nat × Nat))
deriving DecidableEq, Repr

def State.hasSub (s : State) (a b : Nat) : Bool := decide ((a, b) ∈ s.subs)

def State.hasEdge (s : State) (a role b : Nat) : Bool :=
  decide ((a, (role, b)) ∈ s.edges)

def State.size (s : State) : Nat := s.subs.length + s.edges.length

/-- The abstract view used by the refinement contract. -/
def State.toMaterialization (s : State) : Materialization Nat Nat where
  sub a b := (a, b) ∈ s.subs
  edge a role b := (a, (role, b)) ∈ s.edges

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
      | .nf1 sub sup => if s.hasSub a sub then [(a, sup)] else []
      | .nf2 left right sup =>
          if s.hasSub a left && s.hasSub a right then [(a, sup)] else []
      | .nf5 sub => if s.hasSub a sub then [(a, bottom)] else []
      | .nf4 role filler sup =>
          (s.edges.filter fun edge => edge.1 == a && edge.2.1 == role).flatMap
            fun edge => if s.hasSub edge.2.2 filler then [(a, sup)] else []
      | _ => []) ++
    ((s.edges.filter fun edge => edge.1 == a).flatMap
      fun edge => if s.hasSub edge.2.2 bottom then [(a, bottom)] else [])

/-- Every edge consequence of one round (possibly already present). -/
def edgeConsequences (O : Ontology) (U : List Nat) (s : State) :
    List (Nat × (Nat × Nat)) :=
  U.flatMap fun a =>
    O.flatMap fun clause =>
      match clause with
      | .nf3 sub role filler => if s.hasSub a sub then [(a, (role, filler))] else []
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

/-- The reference closure for one routed source. -/
def closure (top bottom : Nat) (named : List Nat) (O : Ontology) : State :=
  let U := contextUniverse top bottom named O
  saturate bottom O U (factBound U (roleUniverse O) + 1) (initial top U)

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

theorem closure_closedOn (top bottom : Nat) (named : List Nat) (O : Ontology) :
    ClosedStateOn (fun a => a ∈ contextUniverse top bottom named O)
      (closure top bottom named O).toMaterialization top bottom O := by
  sorry

theorem closure_sound (top bottom : Nat) (named : List Nat) (O : Ontology) :
    SoundState (closure top bottom named O).toMaterialization top bottom O := by
  sorry

/-- The taxonomy bit for one coordinate: `sub` is unsatisfiable or `sup` is in
its completed label. -/
def referenceBit (top bottom : Nat) (named : List Nat) (O : Ontology)
    (sub sup : Nat) : Bool :=
  let c := closure top bottom named O
  c.hasSub sub bottom || c.hasSub sub sup

/-- The inconsistency flag: `top` is labelled `bottom`. -/
def referenceInconsistent (top bottom : Nat) (named : List Nat) (O : Ontology) :
    Bool :=
  (closure top bottom named O).hasSub top bottom

theorem referenceBit_exact (top bottom : Nat) (named : List Nat) (O : Ontology)
    {sub : Nat} (hsub : sub ∈ contextUniverse top bottom named O) (sup : Nat) :
    referenceBit top bottom named O sub sup = true ↔
      EntailsSub (top := top) (bottom := bottom) O sub sup := by
  rw [entails_iff_materialized_on (closure_closedOn top bottom named O)
    (closure_sound top bottom named O) hsub]
  simp [referenceBit, State.hasSub, State.toMaterialization]

theorem referenceBit_exact_of_named (top bottom : Nat) (named : List Nat)
    (O : Ontology) {sub : Nat} (hsub : sub ∈ named) (sup : Nat) :
    referenceBit top bottom named O sub sup = true ↔
      EntailsSub (top := top) (bottom := bottom) O sub sup :=
  referenceBit_exact top bottom named O (mem_universe_of_named hsub) sup

theorem referenceInconsistent_exact (top bottom : Nat) (named : List Nat)
    (O : Ontology) :
    referenceInconsistent top bottom named O = true ↔
      Unsatisfiable (top := top) (bottom := bottom) O := by
  rw [unsat_iff_materialized_on (closure_closedOn top bottom named O)
    (closure_sound top bottom named O) (top_mem_contextUniverse top bottom named O)]
  simp [referenceInconsistent, State.hasSub, State.toMaterialization]

#print axioms referenceBit_exact
#print axioms referenceInconsistent_exact

end ContextCalculus.ELReference
