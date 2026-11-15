import ContextCalculus.SRIQ.FastCheckA

/-!
# Certificate check for the fast SHIQ procedure: worklist elimination (stage C1d)

The elimination of `FastDefs.lean` (`aliveArr`) sweeps all nodes until no
node changes and recomputes each node's entries in every sweep. This file
computes the same live set on an array candidate set that passed
`closedFastB`:

- per node, the needs, limits and entries are computed once (`mkNodeE`);
  the support test (`suppF`) filters the entries by the live set and runs
  the depth-first search `dfsG` on their signatures;
- a worklist (`elimW`) re-checks a node only when a node of one of its
  child contexts died (`parentsOf`).

`FastElimAProof.lean` proves that the result is the greatest
self-supporting set, so it equals `aliveArr` on the view.
-/

namespace ContextCalculus.SRIQ.Fast

open ContextCalculus.SRI (RoleT Interp)
open ContextCalculus.SRIQ

variable {n m : Nat}

/-! ## A generic search -/

section DfsG

variable {α κ : Type} (cnt : κ → α → Bool)

def subG (c : α) (l : List (κ × Nat)) : List (κ × Nat) :=
  l.map fun x => (x.1, if cnt x.1 c then x.2 - 1 else x.2)

/-- As `dfs`, for any count relation. -/
def dfsG (cs : List α) : Nat → List (κ × Nat) → List (κ × Nat) → Bool
  | fuel, needs, lims =>
    match needs.find? (fun x => decide (0 < x.2)) with
    | none => true
    | some x =>
      match fuel with
      | 0 => false
      | f + 1 => cs.any fun c => cnt x.1 c &&
          lims.all (fun y => !cnt y.1 c || decide (0 < y.2)) &&
          dfsG cs f (subG cnt c needs) (subG cnt c lims)

end DfsG

/-! ## The search with a memo

`dfsM` is `dfsG` for positions as keys, with a memo of the states (the
remaining needs and limits) that have no solution; with enough fuel it
gives the same answer (`dfsM_iff`). -/

section DfsM

variable {α : Type} (cnt : Nat → α → Bool) (cs : List α)

abbrev MSt := List (Nat × Nat) × List (Nat × Nat)

/-- The entries an entry `c` may extend: it counts for the need `x` and
stays within the limits. -/
def okC (x : Nat × Nat) (lims : List (Nat × Nat)) (c : α) : Bool :=
  cnt x.1 c && lims.all (fun y => !cnt y.1 c || decide (0 < y.2))

mutual
def dfsM : Nat → List (Nat × Nat) → List (Nat × Nat) → Std.HashSet MSt → Bool × Std.HashSet MSt
  | fuel, needs, lims, memo =>
    match needs.find? (fun x => decide (0 < x.2)) with
    | none => (true, memo)
    | some x =>
      match fuel with
      | 0 => (false, memo)
      | f + 1 =>
        if memo.contains (needs, lims) then (false, memo) else
        let r := tryM f x needs lims cs memo
        if r.1 then r else (false, r.2.insert (needs, lims))
termination_by fuel _ _ _ => (fuel, 0)

def tryM : Nat → Nat × Nat → List (Nat × Nat) → List (Nat × Nat) → List α → Std.HashSet MSt →
    Bool × Std.HashSet MSt
  | _, _, _, _, [], memo => (false, memo)
  | f, x, needs, lims, c :: rest, memo =>
    if okC cnt x lims c then
      let r := dfsM f (subG cnt c needs) (subG cnt c lims) memo
      if r.1 then r else tryM f x needs lims rest r.2
    else tryM f x needs lims rest memo
termination_by f _ _ _ l _ => (f, l.length + 1)
end

end DfsM

/-! ## Per-node data -/

/-- An entry counts for `(R, b)`: its label has `R`, its child type has `b`. -/
def cntA (x : RoleT (Fin m) × Fin n) (c : Array Nat × Array Nat) : Bool :=
  bsA c.1 (rc x.1) && bsA c.2 x.2.val

structure NodeE (n m : Nat) where
  /-- the needs with a positive count -/
  needs : List ((RoleT (Fin m) × Fin n) × Nat)
  lims : List ((RoleT (Fin m) × Fin n) × Nat)
  limOK : Bool
  /-- needs and limits by position in the signatures -/
  nS : List (Nat × Nat)
  lS : List (Nat × Nat)
  /-- `(j, (label, type of j), signature)` for each pool entry and node `j`
  of its child context whose back set the node holds, when the entry
  serves some need -/
  cands : List (Nat × (Array Nat × Array Nat) × Array Nat)

instance : Inhabited (NodeE n m) := ⟨⟨[], [], false, [], [], []⟩⟩

/-- The signature of an entry: the positions of the needs and limits it
counts for. -/
def sigA (needs lims : List ((RoleT (Fin m) × Fin n) × Nat)) (c : Array Nat × Array Nat) : Array Nat :=
  (((needs ++ lims).zipIdx.filter fun p => cntA p.1.1 c).map (·.2)).toArray

/-- `sigA` in two steps: the positions the label serves, then the child type. -/
def sigTwo (lp : List (((RoleT (Fin m) × Fin n) × Nat) × Nat)) (ty : Array Nat) : Array Nat :=
  ((lp.filter fun p => bsA ty p.1.1.2.val).map (·.2)).toArray

def cntS (p : Nat) (s : Array Nat) : Bool := s.contains p

section Defs

variable (ix : Ix n m) (C : CandA)

def mkNodeE (i : Nat) : NodeE n m :=
  let v := ndA C i
  let κ := keyA C v.ctx
  let upps := uppAtA ix v.ty
  let needs := ((lowAtA ix v.ty).map fun q =>
    ((q.2.2.1, q.2.2.2), q.2.1 - pcBA κ q.2.2.1 q.2.2.2)).filter fun x => decide (0 < x.2)
  let lims := upps.map fun u => ((u.2.2.1, u.2.2.2), u.2.1 - pcBA κ u.2.2.1 u.2.2.2)
  let nl := needs.length
  { needs, lims
    limOK := upps.all fun u => decide (pcBA κ u.2.2.1 u.2.2.2 ≤ u.2.1)
    nS := needs.zipIdx.map fun p => (p.2, p.1.2)
    lS := lims.zipIdx.map fun p => (nl + p.2, p.1.2)
    cands := v.pool.flatMap fun e =>
      let lp := (needs ++ lims).zipIdx.filter fun p => bsA e.lab (rc p.1.1.1)
      if lp.any (fun p => decide (p.2 < nl)) then
        ((membA C e.kid).filter fun j => (bkA C j).all (bsA v.ty)).filterMap fun j =>
          let sg := sigTwo lp (ndA C j).ty
          if sg.any (fun x => decide (x < nl)) then some (j, (e.lab, (ndA C j).ty), sg) else none
      else [] }

def nodeEs : Array (NodeE n m) := Array.ofFn fun i : Fin C.nodes.size => mkNodeE ix C i.val

/-- The node has a supporting star among the live nodes `A`: the distinct
signatures of its live entries meet every need and stay within every limit. -/
def suppF (E : NodeE n m) (A : Array Bool) : Bool :=
  let ss := dedupKey id ((E.cands.filter fun p => A[p.1]?.getD false).map (·.2.2))
  E.limOK && E.nS.all (fun x => ss.any (cntS x.1)) &&
    (dfsM cntS ss ((E.nS.map (·.2)).sum + 1) E.nS E.lS ∅).1

/-- The nodes with a pool entry into each context. -/
def parentsOf : Array (List Nat) :=
  buildIdx C.keys.size some ((List.range C.nodes.size).flatMap fun i => (ndA C i).pool.map fun e => (e.kid, i))

theorem trues_set_lt {A : Array Bool} {i : Nat} (h : A[i]?.getD false = true) :
    trues (A.set! i false) < trues A := by
  have hlt : i < A.size := by
    by_contra hc; rw [Array.getElem?_eq_none (by omega)] at h; simp at h
  refine trues_lt ⟨Array.size_setIfInBounds, fun j hj => ?_⟩ fun he => ?_
  · rw [Array.set!, Array.getElem?_setIfInBounds] at hj
    split at hj
    · simp at hj
    · exact hj
  · have := congrArg (fun B : Array Bool => B[i]?) he
    simp only [Array.set!, Array.getElem?_setIfInBounds, hlt, if_true] at this
    rw [Array.getElem?_eq_getElem hlt] at this h
    simp only [Option.getD_some] at h
    simp only [Option.some.injEq] at this
    rw [h] at this
    exact Bool.false_ne_true this

/-- Worklist elimination: drop an unsupported live node and queue the live
parents of its context that are not queued (`Q` marks the queued nodes).
The nodes queued in one pass are checked in the next. -/
def elimW (Es : Array (NodeE n m)) (P : Array (List Nat)) :
    Array Bool → Array Bool → List Nat → List Nat → Array Bool
  | A, _, [], [] => A
  | A, Q, [], j :: nxt => elimW Es P A Q (j :: nxt) []
  | A, Q, i :: q, nxt =>
    let Q := Q.set! i false
    if h : A[i]?.getD false = true ∧ suppF (Es[i]?.getD default) A = false then
      let ps := (getL P (ndA C i).ctx).filter fun μ => A[μ]?.getD false && !(Q[μ]?.getD false)
      elimW Es P (A.set! i false) (ps.foldl (fun Q μ => Q.set! μ true) Q) q (ps ++ nxt)
    else elimW Es P A Q q nxt
termination_by A _ q nxt => (trues A, 2 * nxt.length + q.length)
decreasing_by
  · exact Prod.Lex.right _ (by simp)
  · exact Prod.Lex.left _ _ (trues_set_lt h.1)
  · exact Prod.Lex.right _ (by simp)

/-- The live nodes. -/
def aliveFast : Array Bool :=
  elimW C (nodeEs ix C) (parentsOf C) (Array.replicate C.nodes.size true)
    (Array.replicate C.nodes.size true) (List.range C.nodes.size).reverse []

/-- `none` (unsatisfiable) or the names in every live root type with `a`. -/
def rowOfA (A : Array Bool) (k : Nat) (a : Fin n) : Option (List (Fin n)) :=
  if (keyA C k).lab.all (fun x => decide (2 * m ≤ x)) then
    match ((membA C k).filter fun i => A[i]?.getD false && bsA (ndA C i).ty a.val).map
        (fun i => (ndA C i).ty) with
    | [] => none
    | t :: ts => some (finL n (ts.foldl interA t).toList)
  else none

def fastRowsA (req : List (Fin n)) : List (Fin n × Option (List (Fin n))) :=
  let A := aliveFast ix C
  (req.zip C.roots).map fun p => (p.1, rowOfA (m := m) C A p.2 p.1)

end Defs

/-- **The fast checked route.** -/
def fastClassifyA (O : Ontology (Fin n) (Fin m)) (req : List (Fin n)) (C : CandA) :
    Option (List (Fin n × Option (List (Fin n)))) :=
  let ix := mkIx O
  if closedFastB ix (mkIxF O ix) C req then some (fastRowsA ix C req) else none

end ContextCalculus.SRIQ.Fast

#print axioms ContextCalculus.SRIQ.Fast.trues_set_lt
