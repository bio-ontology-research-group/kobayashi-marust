import ContextCalculus.SRIQ.Procedure
import Mathlib.Data.Finset.Sort
import Std.Data.HashSet.Lemmas

/-!
# Certificate check for the fast SHIQ procedure: definitions (stage C1c)

`docs/V1.7.0-C1C-FAST-SHIQ-DESIGN.md`, "Proof plan after the prototype".
An unverified generator (`SRIQFast/Core.lean`) produces a candidate set
`U` (`Cand`): contexts, nodes in them, and for each node a pool of child
specs. This file defines

- the indexes of the ontology (`Ix`, `mkIx`) and the computations on
  types through them: forward propagation `fwdI`, the parent projection
  names `relI`, the child context `childKey`, a sound part of the
  super-roles `upS`, and branches with one head name per fired gci (`br`);
- the local closure conditions of the rules R1 to R6 (`ClosedP`) and the
  executable check `closedB` (`decide` of `ClosedP`);
- the elimination (`aliveArr`): a node stays while a multiset of entries
  (a pool spec and a live node of its child context whose back set the
  node holds) meets every existential, at-least and at-most clause of the
  node's type together with the parent entry. The support test is an
  exact depth-first search (`dfs`).
- the readout (`fastRows`).

`FastSound.lean` proves the answers sound for every `U`;
`FastComplete.lean` proves them complete when `closedB` holds.
-/

namespace ContextCalculus.SRIQ.Fast

open ContextCalculus.SRI (RoleT Interp)
open ContextCalculus.SRIQ

variable {n m : Nat}

-- Decide bounded quantifiers through their lists and finsets, never by
-- enumerating a finite type (`Finset (Fin n)` has `2 ^ n` elements, `Fin n` has `n`).
attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype
  Nat.decidableForallFin Nat.decidableExistsFin

abbrev Ty (n : Nat) := Finset (Fin n)
abbrev Lab (m : Nat) := Finset (RoleT (Fin m))

/-! ## Role codes and indexes -/

/-- The code of a role term, `2 r` or `2 r + 1`. -/
def rc : RoleT (Fin m) → Nat
  | .pos r => 2 * r.val
  | .inv r => 2 * r.val + 1

theorem rc_lt (R : RoleT (Fin m)) : rc R < 2 * m := by
  cases R with
  | pos r => simp only [rc]; omega
  | inv r => simp only [rc]; omega

theorem rc_inj {R S : RoleT (Fin m)} (h : rc R = rc S) : R = S := by
  cases R <;> cases S <;> simp only [rc] at h <;> first | omega | (congr 1; ext; omega)

/-- The role term of a code below `2 m`. -/
def ofRc (c : Nat) (h : c < 2 * m) : RoleT (Fin m) :=
  if c % 2 = 0 then .pos ⟨c / 2, by omega⟩ else .inv ⟨c / 2, by omega⟩

theorem rc_ofRc (c : Nat) (h : c < 2 * m) : rc (ofRc c h) = c := by
  unfold ofRc
  split <;> simp only [rc] <;> omega

/-- The list at index `i` of an array of lists (empty outside). -/
def getL {β : Type} (A : Array (List β)) (i : Nat) : List β := A[i]?.getD []

/-- An array of `N` lists; entry `i` lists the `b` with `f x = some (i, b)`. -/
def buildIdx {α β : Type} (N : Nat) (f : α → Option (Nat × β)) (l : List α) : Array (List β) :=
  l.foldl (fun acc x => match f x with
    | some (i, b) => acc.modify i (b :: ·)
    | none => acc) (Array.replicate N [])

theorem getL_modify {β : Type} (acc : Array (List β)) (j i : Nat) (c : β) :
    getL (acc.modify j (c :: ·)) i = if j = i ∧ i < acc.size then c :: getL acc i else getL acc i := by
  unfold getL
  rw [Array.getElem?_modify]
  by_cases hji : j = i
  · subst hji
    by_cases hi : j < acc.size
    · simp [hi]
    · simp [hi]
  · simp [hji]

theorem buildIdx_aux {α β : Type} (f : α → Option (Nat × β)) :
    ∀ (l : List α) (acc : Array (List β)) (i : Nat) (b : β),
      b ∈ getL (l.foldl (fun acc x => match f x with
        | some (i, b) => acc.modify i (b :: ·)
        | none => acc) acc) i ↔
      b ∈ getL acc i ∨ (i < acc.size ∧ ∃ x ∈ l, f x = some (i, b))
  | [], acc, i, b => by simp
  | x :: l, acc, i, b => by
    rw [List.foldl_cons, buildIdx_aux f l]
    cases hf : f x with
    | none =>
      constructor
      · rintro (h | ⟨hi, y, hy, hfy⟩)
        · exact Or.inl h
        · exact Or.inr ⟨hi, y, List.mem_cons_of_mem _ hy, hfy⟩
      · rintro (h | ⟨hi, y, hy, hfy⟩)
        · exact Or.inl h
        · rcases List.mem_cons.1 hy with rfl | hy
          · rw [hf] at hfy; exact absurd hfy (by simp)
          · exact Or.inr ⟨hi, y, hy, hfy⟩
    | some p =>
      obtain ⟨j, c⟩ := p
      simp only [Array.size_modify, getL_modify]
      constructor
      · rintro (h | ⟨hi, y, hy, hfy⟩)
        · split_ifs at h with hji
          · rcases List.mem_cons.1 h with rfl | h
            · obtain ⟨rfl, hi⟩ := hji
              exact Or.inr ⟨hi, x, List.mem_cons_self, hf⟩
            · exact Or.inl h
          · exact Or.inl h
        · exact Or.inr ⟨hi, y, List.mem_cons_of_mem _ hy, hfy⟩
      · rintro (h | ⟨hi, y, hy, hfy⟩)
        · left; split_ifs <;> simp [h]
        · rcases List.mem_cons.1 hy with rfl | hy
          · rw [hf] at hfy
            simp only [Option.some.injEq, Prod.mk.injEq] at hfy
            obtain ⟨rfl, rfl⟩ := hfy
            left; simp [hi]
          · exact Or.inr ⟨hi, y, hy, hfy⟩

theorem mem_buildIdx {α β : Type} {N : Nat} {f : α → Option (Nat × β)} {l : List α} {i : Nat}
    (hi : i < N) {b : β} : b ∈ getL (buildIdx N f l) i ↔ ∃ x ∈ l, f x = some (i, b) := by
  unfold buildIdx
  rw [buildIdx_aux]
  simp [getL, hi]

theorem mem_buildIdx_of {α β : Type} {N : Nat} {f : α → Option (Nat × β)} {l : List α} {i : Nat}
    {b : β} (h : b ∈ getL (buildIdx N f l) i) : ∃ x ∈ l, f x = some (i, b) := by
  unfold buildIdx at h
  rw [buildIdx_aux] at h
  rcases h with h | ⟨_, h⟩
  · simp only [getL, Array.getElem?_replicate] at h
    split at h <;> simp at h
  · exact h

/-- The role inclusion steps with their flips. -/
def steps (O : Ontology (Fin n) (Fin m)) : List (RoleT (Fin m) × RoleT (Fin m)) :=
  O.flatMap fun
    | .chain [R] S => [(R, S), (R.flip, S.flip)]
    | _ => []

/-- The gcis of the ontology, in order. -/
def gciL (O : Ontology (Fin n) (Fin m)) : List (List (Fin n) × List (Fin n)) :=
  O.filterMap fun
    | .gci body head => some (body, head)
    | _ => none

/-- `e` if the gci `⊤ ⊑ e ⊔ … ⊔ e` (head nonempty, every head name `e`). -/
def topName : List (Fin n) × List (Fin n) → Option (Fin n)
  | ([], e :: head) => if head.all (· == e) then some e else none
  | _ => none

/-- The indexes of an ontology. -/
structure Ix (n m : Nat) where
  /-- `a ↦ (S, c)` for each `allRight a S c` -/
  allBy : Array (List (RoleT (Fin m) × Fin n))
  /-- role code `↦` fillers of lower (number at least one) and upper clauses -/
  relBy : Array (List (Fin n))
  /-- role code `↦` one-step super-roles -/
  stepsBy : Array (List (RoleT (Fin m)))
  /-- `a ↦ (k, R, b)` for each lower clause -/
  lowBy : Array (List (Nat × RoleT (Fin m) × Fin n))
  /-- `a ↦ (k, S, e)` for each upper clause -/
  uppBy : Array (List (Nat × RoleT (Fin m) × Fin n))
  gciArr : Array (List (Fin n) × List (Fin n))
  /-- name `↦` the gcis with it in the body -/
  gciBy : Array (List Nat)
  /-- the gcis with an empty body -/
  gciTop : List Nat
  /-- names in every type -/
  tops : Ty n
  /-- role code `↦` super-roles found by search -/
  upArr : Array (Lab m)

/-- Fillers by role code: the lower clauses with a positive number and the
upper clauses. -/
def relSrc (O : Ontology (Fin n) (Fin m)) : List (Nat × Fin n) :=
  ((lowerL O).filterMap fun q => if 1 ≤ q.2.1 then some (rc q.2.2.1, q.2.2.2) else none) ++
    (upperL O).map fun q => (rc q.2.2.1, q.2.2.2)

/-- Breadth-first search for super-roles through `stepsBy`. -/
def upAux (stepsBy : Array (List (RoleT (Fin m)))) :
    Nat → Lab m → List (RoleT (Fin m)) → Lab m
  | 0, acc, _ => acc
  | _ + 1, acc, [] => acc
  | f + 1, acc, x :: rest =>
    let nw := (getL stepsBy (rc x)).filter fun S => S ∉ acc
    upAux stepsBy f (acc ∪ nw.toFinset) (nw ++ rest)

def mkIx (O : Ontology (Fin n) (Fin m)) : Ix n m :=
  let stepsBy := buildIdx (2 * m) (fun p => some (rc p.1, p.2)) (steps O)
  let gl := gciL O
  { allBy := buildIdx n (fun cl => match cl with
        | .allRight a S c => some (a.val, (S, c))
        | _ => none) O
    relBy := buildIdx (2 * m) some (relSrc O)
    stepsBy
    lowBy := buildIdx n (fun q => some (q.1.val, q.2)) (lowerL O)
    uppBy := buildIdx n (fun q => some (q.1.val, q.2)) (upperL O)
    gciArr := gl.toArray
    gciBy := buildIdx n some (gl.zipIdx.flatMap fun p => p.1.1.map fun a => (a.val, p.2))
    gciTop := (gl.zipIdx.filter fun p => p.1.1.isEmpty).map (·.2)
    tops := (gl.filterMap topName).toFinset
    upArr := Array.ofFn fun c : Fin (2 * m) =>
      upAux stepsBy (2 * m + 1) {ofRc c.val c.isLt} [ofRc c.val c.isLt] }

/-! ## Computations on types -/

section Comp

variable (ix : Ix n m)

/-- Names an `L`-neighbour of `t` must hold. -/
def fwdI (t : Ty n) (L : Lab m) : Ty n :=
  t.biUnion fun a => (((getL ix.allBy a.val).filter fun p => p.1 ∈ L).map Prod.snd).toFinset

/-- The names of the parent type that the counting of a child across `L`
reads. -/
def relI (L : Lab m) : Ty n :=
  L.biUnion fun S => (getL ix.relBy (rc S)).toFinset

/-- Super-roles of `R` found by search. -/
def upS (R : RoleT (Fin m)) : Lab m := (ix.upArr[rc R]?).getD {R}

/-- A label is closed under the one-step super-roles. -/
def upClosedB (L : Lab m) : Prop := ∀ R ∈ L, ∀ S ∈ getL ix.stepsBy (rc R), S ∈ L

instance (L : Lab m) : Decidable (upClosedB ix L) := by unfold upClosedB; infer_instance

/-- The gci at an index (no clause outside). -/
def gciAt (i : Nat) : List (Fin n) × List (Fin n) := ix.gciArr[i]?.getD ([], [])

/-- Closedness through the indexes. -/
def closedI (t : Ty n) : Prop :=
  (∀ i ∈ ix.gciTop, ∃ h ∈ (gciAt ix i).2, h ∈ t) ∧
  ∀ a ∈ t, ∀ i ∈ getL ix.gciBy a.val, (∀ b ∈ (gciAt ix i).1, b ∈ t) → ∃ h ∈ (gciAt ix i).2, h ∈ t

instance (t : Ty n) : Decidable (closedI ix t) := by unfold closedI; infer_instance

/-- The lower clauses `(a, k, R, b)` with `a ∈ t`. -/
def lowAt (t : Ty n) : List (Fin n × Nat × RoleT (Fin m) × Fin n) :=
  (t.sort (· ≤ ·)).flatMap fun a => (getL ix.lowBy a.val).map fun q => (a, q)

/-- The upper clauses `(a, k, S, e)` with `a ∈ t`. -/
def uppAt (t : Ty n) : List (Fin n × Nat × RoleT (Fin m) × Fin n) :=
  (t.sort (· ≤ ·)).flatMap fun a => (getL ix.uppBy a.val).map fun q => (a, q)

/-- Branches with one head name per fired gci. `queue` holds gci indices
to look at; a gci fires when its body holds and no head name does. -/
def brAux : Nat → Ty n → List Nat → List (Ty n)
  | 0, cur, _ => [cur]
  | _ + 1, cur, [] => [cur]
  | f + 1, cur, i :: rest =>
    match ix.gciArr[i]? with
    | none => brAux (f + 1) cur rest
    | some g =>
      if (∀ b ∈ g.1, b ∈ cur) ∧ ∀ h ∈ g.2, h ∉ cur then
        g.2.flatMap fun h => brAux f (insert h cur) (getL ix.gciBy h.val ++ rest)
      else brAux (f + 1) cur rest
termination_by f cur q => (f, q.length)

def br (s : Ty n) : List (Ty n) :=
  brAux ix (n + 1) s (ix.gciTop ++ (s.sort (· ≤ ·)).flatMap fun a => getL ix.gciBy a.val)

end Comp

/-! ## Candidate sets -/

structure Spec (n m : Nat) where
  lab : Lab m
  fill : Ty n
deriving DecidableEq

instance : Inhabited (Spec n m) := ⟨⟨∅, ∅⟩⟩

/-- Componentwise union and order of specs. -/
def Spec.union (σ τ : Spec n m) : Spec n m := ⟨σ.lab ∪ τ.lab, σ.fill ∪ τ.fill⟩

def Spec.le (σ τ : Spec n m) : Prop := σ.lab ⊆ τ.lab ∧ σ.fill ⊆ τ.fill

instance (σ τ : Spec n m) : Decidable (σ.le τ) := by unfold Spec.le; infer_instance

/-- A pool entry: a spec and the index of its child context. -/
structure Entry (n m : Nat) where
  spec : Spec n m
  kid : Nat
deriving DecidableEq

/-- A context key: seed, label to the parent, projection of the parent type. -/
structure Key (n m : Nat) where
  seed : Ty n
  lab : Lab m
  pi : Ty n
deriving DecidableEq

instance : Inhabited (Key n m) := ⟨⟨∅, ∅, ∅⟩⟩

structure FNode (n m : Nat) where
  ctx : Nat
  ty : Ty n
  pool : List (Entry n m)

instance : Inhabited (FNode n m) := ⟨⟨0, ∅, []⟩⟩

/-- A candidate set: context keys, nodes, the node indices of each
context, and the root context of each requested name (in request order). -/
structure Cand (n m : Nat) where
  keys : Array (Key n m)
  nodes : Array (FNode n m)
  members : Array (Array Nat)
  roots : List Nat
  /-- the back set of each node (checked by `CacheOK`) -/
  bk : Array (Ty n) := #[]
  /-- the union of the node types of each context (checked by `CacheOK`) -/
  uni : Array (Ty n) := #[]

section Cand

variable (ix : Ix n m) (U : Cand n m)

def nd (i : Nat) : FNode n m := U.nodes[i]?.getD default
def keyOf (k : Nat) : Key n m := U.keys[k]?.getD default
def bkOf (j : Nat) : Ty n := U.bk[j]?.getD ∅
def uniOf (k : Nat) : Ty n := U.uni[k]?.getD ∅

/-- The nodes of context `k`. -/
def memb (k : Nat) : List Nat :=
  (U.members[k]?.getD #[]).toList.filter fun i => decide (i < U.nodes.size ∧ (nd U i).ctx = k)

/-- The key of the child context of spec `σ` at a node of type `t`. -/
def childKey (t : Ty n) (σ : Spec n m) : Key n m :=
  ⟨σ.fill ∪ fwdI ix t σ.lab, flipL σ.lab, t ∩ relI ix (flipL σ.lab)⟩

/-- The names a node pushes to its parent. -/
def backOf (i : Nat) : Ty n := fwdI ix (nd U i).ty (keyOf U (nd U i).ctx).lab

/-- A node checks itself: its context exists, its type is closed and holds
the seed. -/
def nodeOK (i : Nat) : Prop :=
  i < U.nodes.size ∧ (nd U i).ctx < U.keys.size ∧ closedI ix (nd U i).ty ∧
    (keyOf U (nd U i).ctx).seed ⊆ (nd U i).ty

instance (i : Nat) : Decidable (nodeOK ix U i) := by unfold nodeOK; infer_instance

/-- A pool entry checks itself: its child context has the right key and
its label is closed under super-roles. -/
def entryOK (t : Ty n) (e : Entry n m) : Prop :=
  e.kid < U.keys.size ∧ keyOf U e.kid = childKey ix t e.spec ∧ upClosedB ix e.spec.lab

instance (t : Ty n) (e : Entry n m) : Decidable (entryOK ix U t e) := by
  unfold entryOK; infer_instance

/-- The parent entry counts for `(R, b)`. -/
def pcB (κ : Key n m) (R : RoleT (Fin m)) (b : Fin n) : Nat :=
  if R ∈ κ.lab ∧ b ∈ κ.pi then 1 else 0

/-- The default spec of a lower clause. -/
def dflt (q : Fin n × Nat × RoleT (Fin m) × Fin n) : Spec n m := ⟨upS ix q.2.2.1, {q.2.2.2}⟩

/-- No default spec: an existential that the parent entry meets. -/
def skipQ (κ : Key n m) (q : Fin n × Nat × RoleT (Fin m) × Fin n) : Prop :=
  q.2.1 = 1 ∧ pcB κ q.2.2.1 q.2.2.2 = 1

instance (κ : Key n m) (q : Fin n × Nat × RoleT (Fin m) × Fin n) : Decidable (skipQ κ q) := by
  unfold skipQ; infer_instance

def inPool (i : Nat) (σ : Spec n m) : Prop := ∃ e ∈ (nd U i).pool, e.spec = σ

/-- Compare sizes before the sets. -/
instance (i : Nat) (σ : Spec n m) : Decidable (inPool U i σ) :=
  decidable_of_iff ((nd U i).pool.any fun e => e.spec.lab.card == σ.lab.card &&
      e.spec.fill.card == σ.fill.card && decide (e.spec = σ)) (by
    simp only [inPool, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    constructor
    · rintro ⟨e, he, -, h⟩
      exact ⟨e, he, h⟩
    · rintro ⟨e, he, rfl⟩
      exact ⟨e, he, ⟨rfl, rfl⟩, rfl⟩)

/-- Every set computed by `br s` contains a node of context `k` that
contains `s`. -/
def BranchCov (k : Nat) (s : Ty n) : Prop :=
  ∀ b ∈ br ix s, ∃ j ∈ memb U k, s ⊆ (nd U j).ty ∧ (nd U j).ty ⊆ b

instance (k : Nat) (s : Ty n) : Decidable (BranchCov ix U k s) := by
  unfold BranchCov; infer_instance

/-- The specs that may count for an upper clause with role `S` and filler `e`. -/
def cset (i : Nat) (S : RoleT (Fin m)) (e : Fin n) : List (Entry n m) :=
  (nd U i).pool.filter fun σ => decide (S ∈ σ.spec.lab ∧ e ∈ uniOf U σ.kid)

/-- The trigger of the merge rule, given the specs `C` that may count and
the parent count `pc`: the parent entry plus the numbers of the lower
clauses that some spec of `C` may serve. -/
def potOf (i : Nat) (C : List (Entry n m)) (pc : Nat) : Nat :=
  pc + (((lowAt ix (nd U i).ty).filter fun q => decide (∃ σ ∈ C,
      q.2.2.1 ∈ σ.spec.lab ∧ q.2.2.2 ∈ uniOf U σ.kid)).map (·.2.1)).sum

/-- The trigger of the merge rule for an upper clause with role `S` and
filler `e`. -/
def pot (i : Nat) (S : RoleT (Fin m)) (e : Fin n) : Nat :=
  potOf ix U i (cset U i S e) (pcB (keyOf U (nd U i).ctx) S e)

/-- The definitely counted default specs of `cset`. -/
def ddef (i : Nat) (S : RoleT (Fin m)) (e : Fin n) : List (Spec n m) :=
  ((cset U i S e).filter fun σ => decide ((∃ q ∈ lowAt ix (nd U i).ty, 1 ≤ q.2.1 ∧
      ¬ skipQ (keyOf U (nd U i).ctx) q ∧ σ.spec = dflt ix q) ∧
    (e ∈ (keyOf U σ.kid).seed ∨ e ∈ ix.tops))).map (·.spec)

def specUnion (l : List (Spec n m)) : Spec n m := l.foldr Spec.union ⟨∅, ∅⟩

/-- The merge rule R5 at node `i` for an upper clause with number `k`, given
its specs `C` that may count, whether its definitely counted default specs
exist, and their union `M`. -/
def mergeCore (i k : Nat) (C : List (Entry n m)) (hasD : Bool) (M : Spec n m) : Prop :=
  if k = 1 ∧ hasD = true then
    (∀ σ ∈ C, inPool U i (σ.spec.union M)) ∧
    (∀ σ₁ ∈ C, ∀ σ₂ ∈ C, M.le σ₁.spec → M.le σ₂.spec → inPool U i (σ₁.spec.union σ₂.spec))
  else ∀ σ₁ ∈ C, ∀ σ₂ ∈ C, inPool U i (σ₁.spec.union σ₂.spec)

instance (i k : Nat) (C : List (Entry n m)) (hasD : Bool) (M : Spec n m) :
    Decidable (mergeCore U i k C hasD M) := by
  unfold mergeCore; infer_instance

/-- The merge rule R5 at node `i` for an upper clause with number `k`. -/
def MergeOK (i : Nat) (k : Nat) (S : RoleT (Fin m)) (e : Fin n) : Prop :=
  mergeCore U i k (cset U i S e) (!(ddef ix U i S e).isEmpty) (specUnion (ddef ix U i S e))

instance (i k : Nat) (S : RoleT (Fin m)) (e : Fin n) : Decidable (MergeOK ix U i k S e) := by
  unfold MergeOK; infer_instance

/-- The grown spec of the parent-witness rule. -/
def grown (σ τ : Spec n m) : Spec n m := ⟨σ.lab ∪ flipL τ.lab, σ.fill⟩

/-- The intersection of a nonempty list of sets. -/
def interL : List (Ty n) → Ty n
  | [] => ∅
  | x :: xs => xs.foldl (· ∩ ·) x

/-- The candidate entries of a lower clause: a pool spec with its role and
a node of its child context with its filler. -/
def candsQ (i : Nat) (q : Fin n × Nat × RoleT (Fin m) × Fin n) : List (Entry n m × Nat) :=
  (nd U i).pool.flatMap fun e =>
    if q.2.2.1 ∈ e.spec.lab then
      ((memb U e.kid).filter fun j => decide (q.2.2.2 ∈ (nd U j).ty)).map fun j => (e, j)
    else []

/-- The lower clauses at node `i` that the parent entry does not meet. -/
def needsL (i : Nat) : List (Fin n × Nat × RoleT (Fin m) × Fin n) :=
  (lowAt ix (nd U i).ty).filter fun q => decide (pcB (keyOf U (nd U i).ctx) q.2.2.1 q.2.2.2 < q.2.1)

/-- For each need, the back sets of its candidate entries. -/
def backLists (i : Nat) : List (List (Ty n)) :=
  (needsL ix U i).map fun q => (candsQ U i q).map fun p => bkOf U p.2

/-- The union over the needs of the back sets every candidate forces. -/
def forcedOf (cl : List (List (Ty n))) : Ty n := cl.foldr (fun l acc => acc ∪ interL l) ∅

def forced (i : Nat) : Ty n := forcedOf (backLists ix U i)

/-- The back rule R4 at node `i`, given the back lists `cl` and their forced
union `F`. -/
def backCore (i : Nat) (cl : List (List (Ty n))) (F : Ty n) : Prop :=
  (∀ l ∈ cl, l ≠ []) →
    (¬ F ⊆ (nd U i).ty → BranchCov ix U (nd U i).ctx ((nd U i).ty ∪ F)) ∧
    (F ⊆ (nd U i).ty → ∀ l ∈ cl, ∀ X ∈ l, ¬ X ⊆ (nd U i).ty →
      BranchCov ix U (nd U i).ctx ((nd U i).ty ∪ X))

instance (i : Nat) (cl : List (List (Ty n))) (F : Ty n) : Decidable (backCore ix U i cl F) := by
  unfold backCore; infer_instance

/-- The back rule R4 at node `i`. -/
def BackOK (i : Nat) : Prop := backCore ix U i (backLists ix U i) (forcedOf (backLists ix U i))

instance (i : Nat) : Decidable (BackOK ix U i) :=
  let cl := backLists ix U i
  (inferInstance : Decidable (backCore ix U i cl (forcedOf cl)))


/-- The parent-witness rule R6 at node `i` as a parent: for a node `j` of
the child context of a pool entry that shows the trigger of an upper clause
counted by its parent entry, every spec `σ` that may count asks node `i`
for the grown entry (when `i` holds `σ`'s fillers) or for a variant that
holds them. -/
def WitOK (i : Nat) : Prop :=
  ∀ e ∈ (nd U i).pool, ∀ j ∈ memb U e.kid, ∀ u ∈ uppAt ix (nd U j).ty,
    pcB (keyOf U e.kid) u.2.2.1 u.2.2.2 = 1 → u.2.1 < pot ix U j u.2.2.1 u.2.2.2 →
    ∀ σ ∈ cset U j u.2.2.1 u.2.2.2,
      (σ.spec.fill ⊆ (nd U i).ty → inPool U i (grown e.spec σ.spec)) ∧
      (¬ σ.spec.fill ⊆ (nd U i).ty →
        BranchCov ix U (nd U i).ctx ((nd U i).ty ∪ σ.spec.fill))

instance (i : Nat) : Decidable (WitOK ix U i) := by unfold WitOK; infer_instance

/-- The local closure conditions of one node. -/
def NodeClosed (i : Nat) : Prop :=
  nodeOK ix U i ∧ (∀ e ∈ (nd U i).pool, entryOK ix U (nd U i).ty e) ∧
  -- R3 default specs
  (∀ q ∈ lowAt ix (nd U i).ty, 1 ≤ q.2.1 → ¬ skipQ (keyOf U (nd U i).ctx) q →
    inPool U i (dflt ix q)) ∧
  -- R4 back
  BackOK ix U i ∧
  -- R5 merge
  (∀ u ∈ uppAt ix (nd U i).ty, u.2.1 < pot ix U i u.2.2.1 u.2.2.2 →
    MergeOK ix U i u.2.1 u.2.2.1 u.2.2.2) ∧
  -- R6 parent witness
  WitOK ix U i

instance (i : Nat) : Decidable (NodeClosed ix U i) := by unfold NodeClosed; infer_instance

/-- The root context of a requested name: right key, every branch covered. -/
def RootOK (a : Fin n) (k : Nat) : Prop :=
  k < U.keys.size ∧ keyOf U k = ⟨{a}, ∅, ∅⟩ ∧ BranchCov ix U k {a}

instance (a : Fin n) (k : Nat) : Decidable (RootOK ix U a k) := by
  unfold RootOK; infer_instance

/-- The stored back sets and context unions are right. -/
def CacheOK : Prop :=
  (∀ j < U.nodes.size, bkOf U j = backOf ix U j) ∧
  ∀ k < U.keys.size, uniOf U k = (memb U k).foldr (fun j acc => (nd U j).ty ∪ acc) ∅

instance : Decidable (CacheOK ix U) := by unfold CacheOK; infer_instance

/-- The closure conditions R1 to R6 on the whole candidate set. -/
def ClosedP (req : List (Fin n)) : Prop :=
  U.roots.length = req.length ∧ (∀ p ∈ req.zip U.roots, RootOK ix U p.1 p.2) ∧
  -- R2 child: every context covers the branches of its seed
  (∀ k < U.keys.size, BranchCov ix U k (keyOf U k).seed) ∧
  (∀ i < U.nodes.size, NodeClosed ix U i) ∧ CacheOK ix U

instance (req : List (Fin n)) : Decidable (ClosedP ix U req) := by
  unfold ClosedP; infer_instance

/-- **The check.** -/
def closedB (req : List (Fin n)) : Bool := decide (ClosedP ix U req)

end Cand

/-! ## Support and elimination -/

section Elim

/-- An entry counts for `(R, b)`. -/
def cntP (R : RoleT (Fin m)) (b : Fin n) (c : Lab m × Ty n) : Bool := decide (R ∈ c.1 ∧ b ∈ c.2)

/-- One step of the search: subtract the counts of `c`. -/
def subC (c : Lab m × Ty n) (l : List (RoleT (Fin m) × Fin n × Nat)) :
    List (RoleT (Fin m) × Fin n × Nat) :=
  l.map fun x => (x.1, x.2.1, if cntP x.1 x.2.1 c then x.2.2 - 1 else x.2.2)

/-- Depth-first search for a multiset of entries from `cs` that meets every
need and stays within every limit. It always serves the first unmet need. -/
def dfs (cs : List (Lab m × Ty n)) : Nat → List (RoleT (Fin m) × Fin n × Nat) →
    List (RoleT (Fin m) × Fin n × Nat) → Bool
  | fuel, needs, lims =>
    match needs.find? (fun x => decide (0 < x.2.2)) with
    | none => true
    | some x =>
      match fuel with
      | 0 => false
      | f + 1 => cs.any fun c => cntP x.1 x.2.1 c &&
          lims.all (fun y => !cntP y.1 y.2.1 c || decide (0 < y.2.2)) &&
          dfs cs f (subC c needs) (subC c lims)

/-- Keep the first element of each key. -/
def dedupAux {α β : Type} [DecidableEq β] [Hashable β] (key : α → β) :
    List α → List α → Std.HashSet β → List α
  | [], acc, _ => acc
  | x :: xs, acc, h =>
    if h.contains (key x) then dedupAux key xs acc h else dedupAux key xs (x :: acc) (h.insert (key x))

def dedupKey {α β : Type} [DecidableEq β] [Hashable β] (key : α → β) (l : List α) : List α :=
  dedupAux key l [] ∅

variable (ix : Ix n m) (U : Cand n m)

/-- The pool entries that pass their own checks, by node. -/
def vpools : Array (List (Entry n m)) :=
  U.nodes.map fun ν => ν.pool.filter fun e => decide (entryOK ix U ν.ty e)

def vpool (i : Nat) : List (Entry n m) := getL (vpools ix U) i

/-- The back sets, by node. -/
def backs : Array (Ty n) := Array.ofFn fun i : Fin U.nodes.size => backOf ix U i.val

def backG (i : Nat) : Ty n := (backs ix U)[i]?.getD ∅

/-- The needs `(R, b, k - parent)` at node `i`. -/
def needsV (i : Nat) : List (RoleT (Fin m) × Fin n × Nat) :=
  (lowAt ix (nd U i).ty).map fun q =>
    (q.2.2.1, q.2.2.2, q.2.1 - pcB (keyOf U (nd U i).ctx) q.2.2.1 q.2.2.2)

/-- The limits `(S, e, k - parent)` at node `i`. -/
def limsV (i : Nat) : List (RoleT (Fin m) × Fin n × Nat) :=
  (uppAt ix (nd U i).ty).map fun u =>
    (u.2.2.1, u.2.2.2, u.2.1 - pcB (keyOf U (nd U i).ctx) u.2.2.1 u.2.2.2)

/-- The parent entry alone does not exceed an at-most clause. -/
def limsOK (i : Nat) : Prop :=
  ∀ u ∈ uppAt ix (nd U i).ty, pcB (keyOf U (nd U i).ctx) u.2.2.1 u.2.2.2 ≤ u.2.1

instance (i : Nat) : Decidable (limsOK ix U i) := by unfold limsOK; infer_instance

/-- Per-node data computed once for the elimination: the checked nodes, the
checked pool entries and the back sets. -/
structure ECache (n m : Nat) where
  ok : Array Bool
  vp : Array (List (Entry n m))
  bk : Array (Ty n)

/-- The nodes that pass their own checks. -/
def okArr : Array Bool := Array.ofFn fun i : Fin U.nodes.size => decide (nodeOK ix U i.val)

def mkCache : ECache n m := ⟨okArr ix U, vpools ix U, backs ix U⟩

/-- The entries of node `i` among the live nodes `A`. -/
def candsA (C : ECache n m) (A : Array Bool) (i : Nat) : List (Lab m × Ty n) :=
  (getL C.vp i).flatMap fun e =>
    ((memb U e.kid).filter fun j => A[j]?.getD false && decide (C.bk[j]?.getD ∅ ⊆ (nd U i).ty)).map
      fun j => (e.spec.lab, (nd U j).ty)

/-- The signature of an entry: which needs and limits it counts for. -/
def sig (i : Nat) (c : Lab m × Ty n) : List Bool × List Bool :=
  ((needsV ix U i).map fun x => cntP x.1 x.2.1 c, (limsV ix U i).map fun x => cntP x.1 x.2.1 c)

/-- Node `i` has a supporting star among the live nodes `A`. -/
def suppB (C : ECache n m) (A : Array Bool) (i : Nat) : Bool :=
  C.ok[i]?.getD false && decide (limsOK ix U i) &&
    dfs (dedupKey (sig ix U i) (candsA U C A i)) (((needsV ix U i).map (·.2.2)).sum + 1)
      (needsV ix U i) (limsV ix U i)

/-- Check node `i` against the current live set and drop it if unsupported. -/
def sweepStep (C : ECache n m) (A : Array Bool) (i : Nat) : Array Bool :=
  if A[i]?.getD false then A.set! i (suppB ix U C A i) else A

/-- One round: check every live node, last index first (children are made
after their parents), against the live set as it shrinks during the round. -/
def prune (C : ECache n m) (A : Array Bool) : Array Bool :=
  (List.range A.size).reverse.foldl (sweepStep ix U C) A

def trues (A : Array Bool) : Nat := A.toList.count true

/-- Pointwise order of live sets of one size. -/
def LeA (A B : Array Bool) : Prop := A.size = B.size ∧ ∀ j : Nat, A[j]? = some true → B[j]? = some true

theorem count_lt : ∀ (l1 l2 : List Bool), l1.length = l2.length →
    (∀ j : Nat, l1[j]? = some true → l2[j]? = some true) →
    l1.count true ≤ l2.count true ∧ (l1 ≠ l2 → l1.count true < l2.count true)
  | [], [], _, _ => by simp
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: l1, b :: l2, hlen, h => by
    have h' : ∀ j : Nat, l1[j]? = some true → l2[j]? = some true := fun j hj => by
      simpa using h (j + 1) (by simpa using hj)
    obtain ⟨ih1, ih2⟩ := count_lt l1 l2 (by simpa using hlen) h'
    have hab : a = true → b = true := fun ha => by simpa [ha] using h 0 (by simp [ha])
    cases a <;> cases b <;> simp_all [List.count_cons] <;> omega

theorem trues_lt {A B : Array Bool} (hle : LeA A B) (hne : A ≠ B) : trues A < trues B := by
  unfold trues
  refine (count_lt A.toList B.toList (by simpa using hle.1) (fun j hj => ?_)).2 (fun he => hne ?_)
  · simpa using hle.2 j (by simpa using hj)
  · exact Array.ext_getElem? fun j => by rw [← Array.getElem?_toList, he, Array.getElem?_toList]

theorem leA_refl (A : Array Bool) : LeA A A := ⟨rfl, fun _ h => h⟩

theorem leA_trans {A B C : Array Bool} (h1 : LeA A B) (h2 : LeA B C) : LeA A C :=
  ⟨h1.1.trans h2.1, fun j h => h2.2 j (h1.2 j h)⟩

theorem sweepStep_le (C : ECache n m) (A : Array Bool) (i : Nat) :
    LeA (sweepStep ix U C A i) A := by
  unfold sweepStep
  split
  · refine ⟨Array.size_setIfInBounds, fun j hj => ?_⟩
    rw [Array.set!, Array.getElem?_setIfInBounds] at hj
    split at hj
    · next hij =>
      subst hij
      split at hj
      · next hlt => rw [Array.getElem?_eq_getElem hlt]; next hA => simpa [Array.getElem?_eq_getElem hlt] using hA
      · simp at hj
    · exact hj
  · exact leA_refl A

theorem foldl_sweep_le (C : ECache n m) : ∀ (l : List Nat) (A : Array Bool),
    LeA (l.foldl (sweepStep ix U C) A) A
  | [], A => leA_refl A
  | i :: l, A => leA_trans (foldl_sweep_le C l _) (sweepStep_le ix U C A i)

theorem trues_prune_lt {C : ECache n m} {A : Array Bool} (h : prune ix U C A ≠ A) :
    trues (prune ix U C A) < trues A :=
  trues_lt (foldl_sweep_le ix U C _ A) h

/-- Remove unsupported nodes until stable. -/
def elim (C : ECache n m) (A : Array Bool) : Array Bool :=
  if h : prune ix U C A = A then A else elim C (prune ix U C A)
termination_by trues A
decreasing_by exact trues_prune_lt ix U h

/-- The live nodes. -/
def aliveArr : Array Bool :=
  let C := mkCache ix U
  elim ix U C C.ok

end Elim

/-! ## Readout -/

section Readout

variable (ix : Ix n m) (U : Cand n m)

/-- The types of the live nodes of context `k` when it has an empty label. -/
def rootTys (A : Array Bool) (k : Nat) : List (Ty n) :=
  if (keyOf U k).lab = ∅ then
    ((memb U k).filter fun i => A[i]?.getD false).map fun i => (nd U i).ty
  else []

/-- `none` (unsatisfiable) or the names in every live root type with `a`. -/
def rowOf (A : Array Bool) (k : Nat) (a : Fin n) : Option (List (Fin n)) :=
  match (rootTys U A k).filter fun t => decide (a ∈ t) with
  | [] => none
  | t :: ts => some ((ts.foldl (· ∩ ·) t).sort (· ≤ ·))

/-- Every requested name with its row, read from the live nodes. -/
def fastRows (req : List (Fin n)) : List (Fin n × Option (List (Fin n))) :=
  let A := aliveArr ix U
  (req.zip U.roots).map fun p => (p.1, rowOf U A p.2 p.1)

end Readout

/-- The checked route: the rows of `U` when `closedB` accepts it, else
`none` (decline). -/
def fastClassify (O : Ontology (Fin n) (Fin m)) (req : List (Fin n)) (U : Cand n m) :
    Option (List (Fin n × Option (List (Fin n)))) :=
  let ix := mkIx O
  if closedB ix U req then some (fastRows ix U req) else none

end ContextCalculus.SRIQ.Fast
