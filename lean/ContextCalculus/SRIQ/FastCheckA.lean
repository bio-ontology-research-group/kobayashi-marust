import ContextCalculus.SRIQ.FastArr

/-!
# Certificate check for the fast SHIQ procedure: the array check (stage C1d)

`closedFastB` checks the closure conditions R1 to R6 of `FastDefs.lean` on
an array candidate set (`CandA`). It computes on sorted arrays (binary
search, merges by sorting) and memoises the per-node data of the
parent-witness rule (`witArr`). `closedFastB_sound`: when it accepts, the
finset candidate set the arrays denote satisfies `ClosedP`.
-/

namespace ContextCalculus.SRIQ.Fast

open ContextCalculus.SRI (RoleT Interp)
open ContextCalculus.SRIQ

variable {n m : Nat}

/-! ## Definitions -/

section Defs

variable (n m : Nat) in
/-- Every array is sorted; names are below `n`, role codes below `2 m`. -/
def wfNode (v : NodeA) : Bool :=
  sortedB v.ty && v.ty.all (· < n) && v.pool.all fun e =>
    sortedB e.lab && e.lab.all (· < 2 * m) && sortedB e.fill && e.fill.all (· < n)

def wfKey (k : KeyA) : Bool := sortedB k.seed && sortedB k.lab && sortedB k.pi

variable (n m : Nat) in
def wfB (C : CandA) : Bool :=
  C.nodes.all (wfNode n m) && C.keys.all wfKey && C.bk.all (fun b => sortedB b && b.all (· < n)) &&
    C.uni.all sortedB

variable (ix : Ix n m) (ixf : IxF) (C : CandA)

/-- The lower clauses of the names of a sorted type (given as `finL`), as `lowAt`. -/
def lowAtF (tf : List (Fin n)) : List (Fin n × Nat × RoleT (Fin m) × Fin n) :=
  tf.flatMap fun a => (getL ix.lowBy a.val).map fun q => (a, q)

def uppAtF (tf : List (Fin n)) : List (Fin n × Nat × RoleT (Fin m) × Fin n) :=
  tf.flatMap fun a => (getL ix.uppBy a.val).map fun q => (a, q)

def lowAtA (T : Array Nat) : List (Fin n × Nat × RoleT (Fin m) × Fin n) := lowAtF ix (finL n T.toList)

def uppAtA (T : Array Nat) : List (Fin n × Nat × RoleT (Fin m) × Fin n) := uppAtF ix (finL n T.toList)

def pcBA (κ : KeyA) (R : RoleT (Fin m)) (b : Fin n) : Nat :=
  if bsA κ.lab (rc R) && bsA κ.pi b.val then 1 else 0

def skipQA (κ : KeyA) (q : Fin n × Nat × RoleT (Fin m) × Fin n) : Bool :=
  q.2.1 == 1 && pcBA κ q.2.2.1 q.2.2.2 == 1

/-- The universal clauses of the names of `T` (given as `finL`): `(S, c)`
for `allRight a S c`. -/
def abOf (tf : List (Fin n)) : List (RoleT (Fin m) × Fin n) :=
  tf.flatMap fun a => getL ix.allBy a.val

/-- The names an `L`-neighbour must hold, with repetitions, from `abOf`. -/
def fwdL (ab : List (RoleT (Fin m) × Fin n)) (L : Array Nat) : List Nat :=
  (ab.filter fun p => bsA L (rc p.1)).map fun p => p.2.val

/-- The fillers of `abOf` by role code. -/
def abMap (ab : List (RoleT (Fin m) × Fin n)) : Std.HashMap Nat (List Nat) :=
  ab.foldl (fun mp p => mp.insert (rc p.1) (p.2.val :: mp.getD (rc p.1) [])) ∅

/-- `fwdL` through `abMap`. -/
def fwdM (am : Std.HashMap Nat (List Nat)) (L : Array Nat) : List Nat :=
  L.toList.flatMap fun c => am.getD c []

def childKeyA (T : Array Nat) (am : Std.HashMap Nat (List Nat)) (e : EntryA) : KeyA :=
  let fl := flipA e.lab
  ⟨canon (e.fill.toList ++ fwdM am e.lab), fl, T.filter fun a => relHitA ixf a fl⟩

def closedIA (T : Array Nat) (tf : List (Fin n)) : Bool :=
  ix.gciTop.all (fun g => (gciAt ix g).2.any fun h => bsA T h.val) &&
  tf.all fun a => (getL ix.gciBy a.val).all fun g =>
    !((gciAt ix g).1.all fun b => bsA T b.val) || (gciAt ix g).2.any fun h => bsA T h.val

def upClosedA (L : Array Nat) : Bool :=
  L.all fun c => (getL ix.stepsBy c).all fun S => bsA L (rc S)

def nodeOKA (i : Nat) (tf : List (Fin n)) : Bool :=
  decide (i < C.nodes.size) && decide ((ndA C i).ctx < C.keys.size) && closedIA ix (ndA C i).ty tf &&
    (keyA C (ndA C i).ctx).seed.all (bsA (ndA C i).ty)

def entryOKA (T : Array Nat) (am : Std.HashMap Nat (List Nat)) (e : EntryA) : Bool :=
  decide (e.kid < C.keys.size) && decide (keyA C e.kid = childKeyA ixf T am e) && upClosedA ix e.lab

/-- The specs of a pool, for lookups. -/
def poolSet (v : NodeA) : Std.HashSet (Array Nat × Array Nat) :=
  Std.HashSet.ofList (v.pool.map fun e => (e.lab, e.fill))

/-- Branches with one head name per fired gci, as `brAux`, on hash sets. -/
def brAuxA : Nat → Std.HashSet Nat → List Nat → List (Std.HashSet Nat)
  | 0, cur, _ => [cur]
  | _ + 1, cur, [] => [cur]
  | f + 1, cur, i :: rest =>
    match ix.gciArr[i]? with
    | none => brAuxA (f + 1) cur rest
    | some g =>
      if (g.1.all fun b => cur.contains b.val) && (g.2.all fun h => !cur.contains h.val) then
        match g.2 with
        | [h] => brAuxA f (cur.insert h.val) (getL ix.gciBy h.val ++ rest)
        | hs => hs.flatMap fun h => brAuxA f (cur.insert h.val) (getL ix.gciBy h.val ++ rest)
      else brAuxA (f + 1) cur rest
termination_by f cur q => (f, q.length)

def brA (s : Array Nat) : List (Std.HashSet Nat) :=
  brAuxA ix (n + 1) (Std.HashSet.ofList s.toList)
    (ix.gciTop ++ (finL n s.toList).flatMap fun a => getL ix.gciBy a.val)

/-- Every branch of the sorted array `s` contains the type of a node of
context `k` that contains `s`. The node is first looked up in the hint
`C.idx` under the branch itself; the lookup is verified, and the members
of the context are searched when it fails. -/
def brCovA (k : Nat) (s : Array Nat) : Bool :=
  (brA ix s).all fun H =>
    (match C.idx.get? (k, canon H.toList) with
     | some (j, p) => decide ((C.members[k]?.getD #[])[p]? = some j) && decide (j < C.nodes.size) &&
        decide ((ndA C j).ctx = k) && s.all (bsA (ndA C j).ty) && (ndA C j).ty.all (H.contains ·)
     | none => false) ||
    (membA C k).any fun j => s.all (bsA (ndA C j).ty) && (ndA C j).ty.all (H.contains ·)

def candsQA (v : NodeA) (q : Fin n × Nat × RoleT (Fin m) × Fin n) : List (EntryA × Nat) :=
  v.pool.flatMap fun e =>
    if bsA e.lab (rc q.2.2.1) then
      ((membA C e.kid).filter fun j => bsA (ndA C j).ty q.2.2.2.val).map fun j => (e, j)
    else []

def needsLA (κ : KeyA) (lows : List (Fin n × Nat × RoleT (Fin m) × Fin n)) :
    List (Fin n × Nat × RoleT (Fin m) × Fin n) :=
  lows.filter fun q => decide (pcBA κ q.2.2.1 q.2.2.2 < q.2.1)

def backListsA (v : NodeA) (κ : KeyA) (lows : List (Fin n × Nat × RoleT (Fin m) × Fin n)) :
    List (List (Array Nat)) :=
  (needsLA κ lows).map fun q => (candsQA C v q).map fun p => bkA C p.2

def interA (a b : Array Nat) : Array Nat := a.filter fun x => bsA b x

def interLA : List (Array Nat) → Array Nat
  | [] => #[]
  | x :: xs => xs.foldl interA x

def forcedA (cl : List (List (Array Nat))) : Array Nat := cl.foldr (fun l acc => unionA acc (interLA l)) #[]

def backOKA (v : NodeA) (κ : KeyA) (lows : List (Fin n × Nat × RoleT (Fin m) × Fin n)) : Bool :=
  let T := v.ty
  let cl := backListsA C v κ lows
  if cl.all (fun l => !l.isEmpty) then
    let F := forcedA cl
    if F.all (bsA T) then
      (dedupKey id ((cl.flatMap id).filter fun X => !X.all (bsA T))).all fun X =>
        brCovA ix C v.ctx (unionA T X)
    else brCovA ix C v.ctx (unionA T F)
  else true

def csetA (v : NodeA) (S : RoleT (Fin m)) (e : Fin n) : List EntryA :=
  v.pool.filter fun σ => bsA σ.lab (rc S) && bsA (uniA C σ.kid) e.val

def potOfA (lows : List (Fin n × Nat × RoleT (Fin m) × Fin n)) (Cs : List EntryA) (pc : Nat) : Nat :=
  pc + ((lows.filter fun q => Cs.any fun σ =>
    bsA σ.lab (rc q.2.2.1) && bsA (uniA C σ.kid) q.2.2.2.val).map (·.2.1)).sum

def potA (v : NodeA) (κ : KeyA) (lows : List (Fin n × Nat × RoleT (Fin m) × Fin n))
    (S : RoleT (Fin m)) (e : Fin n) : Nat :=
  potOfA C lows (csetA C v S e) (pcBA κ S e)

def ddefA (v : NodeA) (κ : KeyA) (lows : List (Fin n × Nat × RoleT (Fin m) × Fin n))
    (S : RoleT (Fin m)) (e : Fin n) : List (Array Nat × Array Nat) :=
  ((csetA C v S e).filter fun σ =>
    (lows.any fun q => decide (1 ≤ q.2.1) &&
      !skipQA κ q && decide (σ.lab = upSA ixf q.2.2.1) &&
      decide (σ.fill = #[q.2.2.2.val])) &&
    (bsA (keyA C σ.kid).seed e.val || decide (e ∈ ix.tops))).map fun σ => (σ.lab, σ.fill)

def unionS (a b : Array Nat × Array Nat) : Array Nat × Array Nat :=
  (unionA a.1 b.1, unionA a.2 b.2)

def specUnionA (l : List (Array Nat × Array Nat)) : Array Nat × Array Nat :=
  (canon (l.flatMap (·.1.toList)), canon (l.flatMap (·.2.toList)))

def leS (M σ : Array Nat × Array Nat) : Bool := M.1.all (bsA σ.1) && M.2.all (bsA σ.2)

def mergeCoreA (ps : Std.HashSet (Array Nat × Array Nat)) (k : Nat) (Cs : List EntryA)
    (hasD : Bool) (M : Array Nat × Array Nat) : Bool :=
  let Ps := Cs.map fun σ => (σ.lab, σ.fill)
  if k = 1 ∧ hasD = true then
    (Ps.all fun σ => ps.contains (unionS σ M)) &&
      Ps.all fun σ₁ => Ps.all fun σ₂ => !(leS M σ₁) || !(leS M σ₂) || ps.contains (unionS σ₁ σ₂)
  else Ps.all fun σ₁ => Ps.all fun σ₂ => ps.contains (unionS σ₁ σ₂)

def r5A (v : NodeA) (κ : KeyA) (lows upps : List (Fin n × Nat × RoleT (Fin m) × Fin n))
    (ps : Std.HashSet (Array Nat × Array Nat)) : Bool :=
  upps.all fun u =>
    !(decide (u.2.1 < potA C v κ lows u.2.2.1 u.2.2.2)) ||
      (let D := ddefA ix ixf C v κ lows u.2.2.1 u.2.2.2
       mergeCoreA ps u.2.1 (csetA C v u.2.2.1 u.2.2.2) (!D.isEmpty) (specUnionA D))

/-- The specs node `j` asks its parents to grow for (rule R6). -/
def witA (j : Nat) : List (Array Nat × Array Nat) :=
  let v := ndA C j
  let upps := uppAtA ix v.ty
  if upps.isEmpty then [] else
  let κ := keyA C v.ctx
  let lows := lowAtA ix v.ty
  upps.flatMap fun u =>
    if pcBA κ u.2.2.1 u.2.2.2 = 1 ∧ u.2.1 < potA C v κ lows u.2.2.1 u.2.2.2 then
      (csetA C v u.2.2.1 u.2.2.2).map fun σ => (σ.lab, σ.fill)
    else []

def witArr : Array (List (Array Nat × Array Nat)) :=
  Array.ofFn fun j : Fin C.nodes.size => witA ix C j.val

def witOKA (W : Array (List (Array Nat × Array Nat))) (v : NodeA)
    (ps : Std.HashSet (Array Nat × Array Nat)) : Bool :=
  let reqs := v.pool.flatMap fun e => (membA C e.kid).flatMap fun j => (W[j]?.getD []).map fun σ => (e, σ)
  (dedupKey id ((reqs.filter fun r => r.2.2.all (bsA v.ty)).map fun r =>
      (unionA r.1.lab (flipA r.2.1), r.1.fill))).all (ps.contains ·) &&
    (dedupKey id ((reqs.filter fun r => !r.2.2.all (bsA v.ty)).map (·.2.2))).all fun f =>
      brCovA ix C v.ctx (unionA v.ty f)

def r3A (κ : KeyA) (lows : List (Fin n × Nat × RoleT (Fin m) × Fin n))
    (ps : Std.HashSet (Array Nat × Array Nat)) : Bool :=
  lows.all fun q => !(decide (1 ≤ q.2.1)) || skipQA κ q || ps.contains (upSA ixf q.2.2.1, #[q.2.2.2.val])

def nodeClosedA (W : Array (List (Array Nat × Array Nat))) (i : Nat) : Bool :=
  let v := ndA C i
  let κ := keyA C v.ctx
  let tf := finL n v.ty.toList
  let lows := lowAtF ix tf
  let ps := poolSet v
  let am := abMap (abOf ix tf)
  nodeOKA ix C i tf && v.pool.all (entryOKA ix ixf C v.ty am) && r3A ixf κ lows ps &&
    backOKA ix C v κ lows && r5A ix ixf C v κ lows (uppAtF ix tf) ps && witOKA ix C W v ps

def rootOKA (a : Fin n) (k : Nat) : Bool :=
  decide (k < C.keys.size) && decide (keyA C k = ⟨#[a.val], #[], #[]⟩) && brCovA ix C k #[a.val]

def cacheOKA : Bool :=
  (List.range C.nodes.size).all (fun j =>
    decide (bkA C j = canon (fwdL (abOf ix (finL n (ndA C j).ty.toList)) (keyA C (ndA C j).ctx).lab))) &&
  (List.range C.keys.size).all fun k =>
    decide (uniA C k = (membA C k).foldl (fun acc j => unionA acc (ndA C j).ty) #[])

/-- **The fast check.** -/
def closedFastB (req : List (Fin n)) : Bool :=
  wfB n m C && decide (C.roots.length = req.length) &&
    (req.zip C.roots).all (fun p => rootOKA ix C p.1 p.2) &&
    (List.range C.keys.size).all (fun k => brCovA ix C k (keyA C k).seed) &&
    (let W := witArr ix C
     (List.range C.nodes.size).all (nodeClosedA ix ixf C W)) &&
    cacheOKA ix C

end Defs

end ContextCalculus.SRIQ.Fast
