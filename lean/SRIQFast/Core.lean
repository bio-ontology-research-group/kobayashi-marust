import Std.Data.HashMap
import Std.Data.HashSet

/-!
# A demand-driven SHIQ procedure (stage C1c prototype, unproved)

`docs/V1.7.0-C1C-FAST-SHIQ-DESIGN.md`, section 5. This is an unverified
prototype that measures the design on the corpus before anyone proves it.
`partial` is used freely; nothing here is proved.

Input: an ALCHIQ ontology (after `encTransQ`) over names `0 .. n-1` and
role terms coded as `2 * r` (`r`) and `2 * r + 1` (`r⁻`).

Objects (see `C1C-PROTOTYPE.md` for the precise rules):

- A type is a sorted array of names, a label a sorted array of role codes
  closed under super-roles.
- A context `(K, L, π)`: a seed `K`, the label `L` from the child to its
  parent (empty for a root) and the projection `π` of the parent type onto
  the names `Rel L` (fillers of clauses whose role is in `L`).
- A node: a context and a type `t ⊇ K` (a branch). Each node has a pool of
  specs `(Lc, B)`: a label from the node to a child and the fillers the
  child must hold. The child context of a spec is
  `(B ∪ fwd t Lc, flip Lc, t ∩ Rel (flip Lc))`.
- Rules: root, child (every branch of a child context), back (a child
  pushes names to its parent: the parent gets the branches of
  `t ∪ back`), merge (two specs that could both count for a violated
  at-most clause give their union as a new spec), parent witness (a spec
  that could count for a violated at-most clause together with the parent
  entry asks every parent for a variant that holds the spec's fillers,
  with the edge label grown by the spec's label).
- Elimination: a node is supported if a multiset of entries (a pool spec
  and an alive node of its child context whose back set the node's type
  contains) together with the parent entry satisfies every existential,
  at-least and at-most clause of the type.
-/

namespace SRIQFast

open Std

/-! ## Sorted arrays of naturals -/

abbrev Ty := Array Nat

def sortDedup (a : Array Nat) : Ty :=
  -- merge sort: `Array.qsort` is slow on the nearly sorted arrays met here
  let s := a.toList.mergeSort (fun x y => decide (x ≤ y))
  s.foldl (fun acc x => if acc.size > 0 && acc.back! == x then acc else acc.push x) #[]

partial def memAux (t : Ty) (x lo hi : Nat) : Bool :=
  if lo < hi then
    let mid := (lo + hi) / 2
    let v := t[mid]!
    if v == x then true else if v < x then memAux t x (mid + 1) hi else memAux t x lo mid
  else false

@[inline] def mem (t : Ty) (x : Nat) : Bool := memAux t x 0 t.size

partial def unionAux (a b : Ty) (i j : Nat) (acc : Array Nat) : Array Nat :=
  if i < a.size then
    if j < b.size then
      let x := a[i]!; let y := b[j]!
      if x < y then unionAux a b (i + 1) j (acc.push x)
      else if y < x then unionAux a b i (j + 1) (acc.push y)
      else unionAux a b (i + 1) (j + 1) (acc.push x)
    else unionAux a b (i + 1) j (acc.push a[i]!)
  else if j < b.size then unionAux a b i (j + 1) (acc.push b[j]!)
  else acc

def union (a b : Ty) : Ty :=
  if a.isEmpty then b else if b.isEmpty then a else unionAux a b 0 0 (Array.mkEmpty (a.size + b.size))

partial def subAux (a b : Ty) (i j : Nat) : Bool :=
  if i < a.size then
    if j < b.size then
      let x := a[i]!; let y := b[j]!
      if x == y then subAux a b (i + 1) (j + 1)
      else if y < x then subAux a b i (j + 1)
      else false
    else false
  else true

/-- `a ⊆ b`. -/
def sub (a b : Ty) : Bool := a.size ≤ b.size && subAux a b 0 0

partial def interAux (a b : Ty) (i j : Nat) (acc : Array Nat) : Array Nat :=
  if i < a.size && j < b.size then
    let x := a[i]!; let y := b[j]!
    if x == y then interAux a b (i + 1) (j + 1) (acc.push x)
    else if x < y then interAux a b (i + 1) j acc
    else interAux a b i (j + 1) acc
  else acc

def inter (a b : Ty) : Ty := interAux a b 0 0 #[]

/-- The flipped label (`R ↦ R⁻`). -/
def flipL (L : Ty) : Ty := sortDedup (L.map fun r => r ^^^ 1)

/-! ## The ontology -/

/-- Clauses on `Nat` indices; roles are codes. -/
inductive QC where
  | gci (body head : Array Nat)
  | ex (a R b : Nat)
  | all (a S c : Nat)
  | ge (a k R b : Nat)
  | le (a k S e : Nat)
  | sub (R S : Nat)
  deriving Repr, Inhabited

structure Onto where
  n : Nat
  nr : Nat
  gcis : Array (Array Nat × Array Nat)
  gciBy : Array (Array Nat)
  gciTop : Array Nat
  allBy : Array (Array (Nat × Nat))
  /-- lower clauses `(a, k, R, b)`, existentials with `k = 1` -/
  low : Array (Nat × Nat × Nat × Nat)
  upp : Array (Nat × Nat × Nat × Nat)
  lowBy : Array (Array Nat)
  uppBy : Array (Array Nat)
  up : Array Ty
  relBy : Array Ty
  /-- for a lazy disjunction (gci index): its default head name, a pure
  definer `W` (not requested, head of this gci only, in no body, no
  filler, left side of exactly one at-most, at-least or existential clause
  and of nothing else); an at-most definer is preferred -/
  lazyDef : HashMap Nat Nat := ∅
  /-- the lazy disjunction of a default name -/
  lazyOf : HashMap Nat Nat := ∅

def pushAt (a : Array (Array α)) (i : Nat) (x : α) : Array (Array α) :=
  a.modify i (·.push x)

partial def upClose (subs : Array (Array Nat)) (r : Nat) : Ty :=
  let rec go (todo : List Nat) (seen : HashSet Nat) : HashSet Nat :=
    match todo with
    | [] => seen
    | x :: rest =>
      let nxt := (subs[x]!).toList.filter fun y => !seen.contains y
      go (nxt ++ rest) (nxt.foldl (fun s y => s.insert y) seen)
  sortDedup (go [r] ((∅ : HashSet Nat).insert r)).toArray

def mkOnto (n m : Nat) (cls : Array QC) (fullRel : Bool := false) (lazy : Bool := false) (nreq : Nat := 0) : Onto := Id.run do
  let nr := 2 * m
  let mut gcis : Array (Array Nat × Array Nat) := #[]
  let mut gciBy : Array (Array Nat) := Array.replicate n #[]
  let mut gciTop : Array Nat := #[]
  let mut allBy : Array (Array (Nat × Nat)) := Array.replicate n #[]
  let mut low : Array (Nat × Nat × Nat × Nat) := #[]
  let mut upp : Array (Nat × Nat × Nat × Nat) := #[]
  let mut lowBy : Array (Array Nat) := Array.replicate n #[]
  let mut uppBy : Array (Array Nat) := Array.replicate n #[]
  let mut subs : Array (Array Nat) := Array.replicate nr #[]
  let mut rel : Array (Array Nat) := Array.replicate nr #[]
  for c in cls do
    match c with
    | .gci b h =>
      let i := gcis.size
      let b' := sortDedup b
      gcis := gcis.push (b', sortDedup h)
      if b'.isEmpty then gciTop := gciTop.push i
      for a in b' do gciBy := pushAt gciBy a i
    | .ex a R b =>
      lowBy := pushAt lowBy a low.size; low := low.push (a, 1, R, b)
    | .ge a k R b =>
      if k > 0 then
        lowBy := pushAt lowBy a low.size; low := low.push (a, k, R, b)
    | .le a k S e =>
      uppBy := pushAt uppBy a upp.size; upp := upp.push (a, k, S, e); rel := pushAt rel S e
    | .all a S c => allBy := pushAt allBy a (S, c)
    | .sub R S =>
      subs := pushAt subs R S
      subs := pushAt subs (R ^^^ 1) (S ^^^ 1)
  let up := (Array.range nr).map fun r => upClose subs r
  -- `Rel`: upper fillers by role; lower fillers by role only when some
  -- upper clause has a role above it (otherwise the parent entry serving
  -- that demand never matters for an at-most clause)
  let uppRoles : HashSet Nat := upp.foldl (fun h q => h.insert q.2.2.1) ∅
  for (_, _, R, b) in low do
    if fullRel || (up[R]!).any (uppRoles.contains ·) then rel := pushAt rel R b
  -- lazy disjunctions
  let mut lazyDef : HashMap Nat Nat := ∅
  let mut lazyOf : HashMap Nat Nat := ∅
  if lazy then
    let mut headCnt : HashMap Nat Nat := ∅
    for (_, h) in gcis do
      for x in h do headCnt := headCnt.insert x (headCnt.getD x 0 + 1)
    let mut filler : HashSet Nat := ∅
    for (_, _, _, b) in low do filler := filler.insert b
    for (_, _, _, b) in upp do filler := filler.insert b
    for l in allBy do
      for (_, c) in l do filler := filler.insert c
    for i in gciTop do
      let (_, h) := gcis[i]!
      if h.size < 2 then continue
      let pure := h.filter fun x =>
        x ≥ nreq && headCnt.getD x 0 == 1 && (gciBy[x]!).isEmpty && !filler.contains x &&
        (allBy[x]!).isEmpty && (lowBy[x]!).size + (uppBy[x]!).size == 1
      -- prefer an at-most definer as the default
      let pure := pure.filter (fun x => (uppBy[x]!).size == 1) ++ pure.filter (fun x => (uppBy[x]!).size == 0)
      if h : 0 < pure.size then
        lazyDef := lazyDef.insert i pure[0]
        lazyOf := lazyOf.insert pure[0] i
  return { n, nr, gcis, gciBy, gciTop, allBy, low, upp, lowBy, uppBy, up,
           relBy := rel.map sortDedup, lazyDef, lazyOf }

/-- Names a neighbour across label `L` (from `t`) must hold. -/
def fwd (O : Onto) (t : Ty) (L : Ty) : Ty := Id.run do
  if L.isEmpty then return #[]
  let mut acc : Array Nat := #[]
  for a in t do
    for (S, c) in O.allBy[a]! do
      if mem L S then acc := acc.push c
  return sortDedup acc

/-- `Rel L`: fillers of the lower and upper clauses with a role in `L`. -/
def rel (O : Onto) (L : Ty) : Ty :=
  L.foldl (fun acc R => union acc (O.relBy[R]!)) #[]

/-! ## Branches with one head name per fired gci -/

/-- Every branch of `seed` (with `closedPart = some t`: `t ⊆ seed` is
closed, so only the gcis triggered by names outside `t` are queued): fire gcis whose body holds and whose head has
no present name, adding one head name each time (a clash for an empty
head). Every closed superset `T` of `seed` contains some branch. -/
partial def branches (O : Onto) (seed : Ty) (closedPart : Option Ty := none) : Array Ty := Id.run do
  let rec go (cur : HashSet Nat) (acc : Array Nat) (queue : List Nat) (out : Array Ty) : Array Ty :=
    match queue with
    | [] =>
      -- `acc` is the sorted seed followed by the added names: sort only these
      out.push (if acc.size == seed.size then seed
        else union seed (sortDedup (acc.extract seed.size acc.size)))
    | i :: rest =>
      let (b, h) := O.gcis[i]!
      if b.all (cur.contains ·) then
        if h.any (cur.contains ·) then go cur acc rest out
        else match O.lazyDef.get? i with
        | some w => go (cur.insert w) (acc.push w) rest out
        | none =>
          if h.size == 1 then
            -- one head name: no copy of `cur` and `acc` (they are not shared)
            let y := h[0]!
            go (cur.insert y) (acc.push y) (O.gciBy[y]!.toList ++ rest) out
          else h.foldl (fun out y =>
            go (cur.insert y) (acc.push y) (O.gciBy[y]!.toList ++ rest) out) out
      else go cur acc rest out
  let cur : HashSet Nat := seed.foldl (fun s x => s.insert x) ∅
  let q := match closedPart with
    | none => O.gciTop.toList ++ (seed.toList.flatMap fun a => (O.gciBy[a]!).toList)
    | some t => (seed.toList.filter (!mem t ·)).flatMap fun a => (O.gciBy[a]!).toList
  let res := go cur seed q #[]
  -- remove duplicates
  let mut seen : HashSet Ty := ∅
  let mut out : Array Ty := #[]
  for t in res do
    if !seen.contains t then
      seen := seen.insert t
      out := out.push t
  return out

/-- Horn closure: add the head of every gci with one head name whose body
holds (and of every top gci with one head name). -/
partial def hornClose (O : Onto) (s : Ty) : Ty := Id.run do
  let mut cur : HashSet Nat := s.foldl (fun h x => h.insert x) ∅
  let mut acc : Array Nat := #[]
  let mut todo : Array Nat := s
  for g in O.gciTop do
    let (_, h) := O.gcis[g]!
    if h.size == 1 && !cur.contains h[0]! then
      cur := cur.insert h[0]!; acc := acc.push h[0]!; todo := todo.push h[0]!
  let mut i := 0
  while i < todo.size do
    let x := todo[i]!
    i := i + 1
    for g in O.gciBy[x]! do
      let (b, h) := O.gcis[g]!
      if h.size == 1 && !cur.contains h[0]! && b.all (cur.contains ·) then
        cur := cur.insert h[0]!; acc := acc.push h[0]!; todo := todo.push h[0]!
  return if acc.isEmpty then s else union s (sortDedup acc)

/-- The static back set of a type: for every lower clause `(a, k, R, b)`
with `a ∈ t`, the names that every witness (holding `b` and the names
`t` pushes across `up R`, and their Horn closure) pushes back across the
flipped label. Every model element with type above `t` holds them. -/
def staticBack (O : Onto) (t : Ty) : Ty := Id.run do
  let mut acc : Ty := #[]
  for a in t do
    for qi in O.lowBy[a]! do
      let (_, _, R, b) := O.low[qi]!
      let L := O.up[R]!
      let w := hornClose O (union #[b] (fwd O t L))
      acc := union acc (fwd O w (flipL L))
  return acc

/-! ## Contexts, nodes, the generation state -/

structure Spec where
  lab : Ty
  fill : Ty
  deriving BEq, Hashable, Inhabited, Repr

structure CtxKey where
  seed : Ty
  lab : Ty
  pi : Ty
  deriving BEq, Hashable, Inhabited

structure CtxD where
  key : CtxKey
  nodes : Array Nat := #[]
  byTy : HashMap Ty Nat := ∅
  parents : Array (Nat × Nat) := #[]
  uni : HashSet Nat := ∅
  /-- name ↦ nodes of the context whose type holds it -/
  byName : HashMap Nat (Array Nat) := ∅
  backs : HashSet Ty := ∅
  pw : HashSet (Ty × Ty) := ∅
  deriving Inhabited

structure NodeD where
  ctx : Nat
  ty : Ty
  pool : Array Spec := #[]
  poolSet : HashSet Spec := ∅
  /-- seeds `t ∪ X` already expanded by the back rule -/
  backDone : HashSet Ty := ∅
  kids : Array Nat := #[]
  back : Ty := #[]
  /-- superseded by a static back set: no pool, not a candidate -/
  sup : Bool := false
  deriving Inhabited

structure Cfg where
  /-- variants copy the parent's pool -/
  inherit : Bool := true
  /-- no default spec for a demand the parent entry already meets -/
  skipCovered : Bool := true
  /-- back rule through forced sets (`backRule`) instead of every child back set -/
  forcedBack : Bool := true
  /-- key child contexts on the parent's whole type instead of its
  projection `t ∩ Rel L` (no sharing between parents; for measurement) -/
  piFull : Bool := false
  /-- for an at-most 1 clause, merge every definitely counted default spec at once -/
  funcMerge : Bool := true
  /-- lazy alternatives from the at-most trigger during generation (else
  only for dead nodes between rounds) -/
  lazyEager : Bool := false
  /-- stop generation after this many nodes (0: no cap) -/
  maxNodes : Nat := 0
  /-- the merge rule for at-most 1 that `closedB` checks (the earlier
  rule, which merged default specs only, misses a merge of a merged spec
  with a default: `lean/testdata/sriq-fast/funcmerge-cx.sriq`) -/
  checkedMerge : Bool := true
  /-- static back sets: a node whose type misses the back set that the
  witness of one of its lower clauses must push (computed from the
  ontology alone) is superseded: it gets the variant with that set and no
  pool of its own -/
  staticBack : Bool := false
  deriving Repr

inductive Ev where
  | init (v : Nat) (inh : Array Spec)
  | trig (v : Nat)
  | back (v : Nat)
  deriving Inhabited

structure St where
  ctxs : Array CtxD := #[]
  ctxIdx : HashMap CtxKey Nat := ∅
  nodes : Array NodeD := #[]
  queue : Array Ev := #[]
  qpos : Nat := 0
  -- counters
  nMerge : Nat := 0
  nPW : Nat := 0
  nBackVar : Nat := 0
  nPWVar : Nat := 0
  nLazyVar : Nat := 0
  nSup : Nat := 0
  nBranchCalls : Nat := 0
  maxBranches : Nat := 0
  nBranches : Nat := 0
  aborted : Bool := false
  nEvents : Nat := 0
  pendTrig : HashSet Nat := ∅
  pendBack : HashSet Nat := ∅
  nRounds : Nat := 0
  relCache : HashMap Ty Ty := ∅
  nsInit : Nat := 0
  nsTrig : Nat := 0
  nsBack : Nat := 0
  nsBranch : Nat := 0
  lastReport : Nat := 0
  deriving Inhabited

abbrev M := ReaderT (Onto × Cfg) (StateT St IO)

def getO : M Onto := return (← read).1
def getCfg : M Cfg := return (← read).2

def enqueue (e : Ev) : M Unit := do
  match e with
  | .trig v =>
    if (← get).pendTrig.contains v then return
    modify fun s => { s with pendTrig := s.pendTrig.insert v }
  | .back v =>
    if (← get).pendBack.contains v then return
    modify fun s => { s with pendBack := s.pendBack.insert v }
  | .init .. => pure ()
  modify fun s => { s with queue := s.queue.push e }

def branchesM (t : Ty) (closedPart : Option Ty := none) : M (Array Ty) := do
  let O ← getO
  let t0 ← IO.monoNanosNow
  let bs := branches O t closedPart
  let t1 ← IO.monoNanosNow
  modify fun s => { s with nsBranch := s.nsBranch + (t1 - t0) }
  modify fun s => { s with nBranchCalls := s.nBranchCalls + 1 }
  modify fun s => { s with nBranches := s.nBranches + bs.size }
  modify fun s => { s with maxBranches := max s.maxBranches bs.size }
  return bs

/-- The child context of spec `σ` at a node of type `t`. -/
def childKey (O : Onto) (t : Ty) (σ : Spec) : M CtxKey := do
  let L := flipL σ.lab
  let r ← match (← get).relCache.get? L with
    | some r => pure r
    | none =>
      let r := rel O L
      modify fun s => { s with relCache := s.relCache.insert L r }
      pure r
  let pi := if (← getCfg).piFull then t else inter t r
  return { seed := union σ.fill (fwd O t σ.lab), lab := L, pi }

mutual

/-- Add a node (or the specs `inh` to an existing one). -/
partial def addNode (k : Nat) (t : Ty) (inh : Array Spec) : M Unit := do
  -- read plain values only, so that no reference to the state or to the
  -- context survives into the updates below (a live reference would make
  -- every update copy the whole array)
  let existing ← (fun s => (s.ctxs[k]!.byTy.get? t)) <$> get
  match existing with
  | some v =>
    if !(← (fun s => s.nodes[v]!.sup) <$> get) then
      for σ in inh do addSpec v σ
  | none =>
    let cfg ← getCfg
    let size ← (fun s => s.nodes.size) <$> get
    if cfg.maxNodes > 0 && size ≥ cfg.maxNodes then
      modify fun s => { s with aborted := true }
      return
    let O ← getO
    let v := size
    let lab ← (fun s => s.ctxs[k]!.key.lab) <$> get
    let bk := fwd O t lab
    let sb := if cfg.staticBack then staticBack O t else #[]
    let isSup := cfg.staticBack && !sub sb t
    let nd : NodeD := { ctx := k, ty := t, back := bk, sup := isSup }
    let isNewBack ← (fun s => !s.ctxs[k]!.backs.contains bk) <$> get
    -- one field per update: a multi-field update copies the later fields
    modify fun s => { s with nodes := s.nodes.push nd }
    modify fun s => { s with ctxs := s.ctxs.modify k fun c =>
      let c := { c with nodes := c.nodes.push v }
      let c := { c with byTy := c.byTy.insert t v }
      let c := { c with uni := t.foldl (fun u x => u.insert x) c.uni }
      let c := if isSup then c else { c with byName := t.foldl (fun m x => m.insert x ((m.getD x #[]).push v)) c.byName }
      if isSup then c else { c with backs := c.backs.insert bk } }
    if isSup then
      modify fun s => { s with nSup := s.nSup + 1 }
      for t' in ← branchesM (union t sb) (some t) do addNode k t' #[]
      return
    enqueue (.init v inh)
    let parents ← (fun s => s.ctxs[k]!.parents) <$> get
    for (μ, _) in parents do
      if cfg.forcedBack then enqueue (.back μ)
      else if isNewBack then applyBack μ bk
      enqueue (.trig μ)

/-- The context with key `key`, made on first use with every branch of its seed. -/
partial def getCtx (key : CtxKey) : M Nat := do
  match (← get).ctxIdx.get? key with
  | some k => return k
  | none =>
    let k := (← get).ctxs.size
    modify fun s => { s with ctxs := s.ctxs.push { key } }
    modify fun s => { s with ctxIdx := s.ctxIdx.insert key k }
    for t in ← branchesM key.seed do addNode k t #[]
    return k

/-- Add spec `σ` to the pool of node `v` and register `v` as a parent of its context. -/
partial def addSpec (v : Nat) (σ : Spec) : M Unit := do
  let (has, i, ty) ← (fun s => let nd := s.nodes[v]!; (nd.poolSet.contains σ, nd.pool.size, nd.ty)) <$> get
  if has then return
  let O ← getO
  modify fun s => { s with nodes := s.nodes.modify v fun nd =>
    let nd := { nd with pool := nd.pool.push σ }
    { nd with poolSet := nd.poolSet.insert σ } }
  let k ← getCtx (← childKey O ty σ)
  modify fun s => { s with nodes := s.nodes.modify v (fun nd => { nd with kids := nd.kids.push k }) }
  modify fun s => { s with ctxs := s.ctxs.modify k fun c => { c with parents := c.parents.push (v, i) } }
  let (backs, pws) ← (fun s => let c := s.ctxs[k]!; (c.backs.toArray, c.pw.toArray)) <$> get
  if (← getCfg).forcedBack then enqueue (.back v)
  else for bk in backs do applyBack v bk
  for r in pws do applyPW v i r
  enqueue (.trig v)

/-- Back rule: a child pushes `bk` to the parent `v`. -/
partial def applyBack (v : Nat) (bk : Ty) : M Unit := do
  let (ty, k, pool) ← (fun s => let nd := s.nodes[v]!; (nd.ty, nd.ctx, nd.pool)) <$> get
  if sub bk ty then return
  let cfg ← getCfg
  let inh := if cfg.inherit then pool else #[]
  for t' in ← branchesM (union ty bk) (some ty) do
    modify fun s => { s with nBackVar := s.nBackVar + 1 }
    addNode k t' inh

/-- Parent-witness rule: a child of `v` through pool spec `i` asks that
`v` holds `r.1` and that the edge label grows by `flip r.2`. -/
partial def applyPW (v : Nat) (i : Nat) (r : Ty × Ty) : M Unit := do
  let (ty, k, pool) ← (fun s => let nd := s.nodes[v]!; (nd.ty, nd.ctx, nd.pool)) <$> get
  let σ := pool[i]!
  let grown : Spec := { σ with lab := union σ.lab (flipL r.2) }
  if sub r.1 ty then
    addSpec v grown
  else
    let cfg ← getCfg
    let inh := (if cfg.inherit then pool else #[]).push grown
    for t' in ← branchesM (union ty r.1) (some ty) do
      modify fun s => { s with nPWVar := s.nPWVar + 1 }
      addNode k t' inh

/-- Record a parent-witness request in context `k` and apply it to every parent. -/
partial def addPW (k : Nat) (r : Ty × Ty) : M Unit := do
  let (has, parents) ← (fun s => let c := s.ctxs[k]!; (c.pw.contains r, c.parents)) <$> get
  if has then return
  modify fun s => { s with nPW := s.nPW + 1 }
  modify fun s => { s with ctxs := s.ctxs.modify k fun c => { c with pw := c.pw.insert r } }
  for (μ, i) in parents do applyPW μ i r

end

/-- Back rule through forced sets. For each need `q` of node `v` (a lower
clause the parent entry does not meet), the candidate entries are the
nodes of the child contexts of the pool specs that count for `q`; `F q` is
the intersection of their back sets. If the union `F` of the `F q` is not
in the type, every star of `v` fails, and only the variants of `t ∪ F` are
made. Otherwise each candidate back set `X ⊄ t` gives the variants of
`t ∪ X`. Back sets of entries that count for no need are not used. -/
def backPlan (O : Onto) (s : St) (v : Nat) : Array Ty := Id.run do
  let nd := s.nodes[v]!
  let key := s.ctxs[nd.ctx]!.key
  let t := nd.ty
  let mut F : Ty := #[]
  let mut cands : Array Ty := #[]
  let mut candSet : HashSet Ty := ∅
  for a in t do
    for qi in O.lowBy[a]! do
      let (_, k, R, b) := O.low[qi]!
      let pc := if mem key.lab R && mem key.pi b then 1 else 0
      if k ≤ pc then continue
      let mut inter? : Option Ty := none
      for i in [0:nd.pool.size] do
        if !mem nd.pool[i]!.lab R then continue
        for w in s.ctxs[nd.kids[i]!]!.byName.getD b #[] do
          let nw := s.nodes[w]!
          do
            inter? := some (match inter? with | none => nw.back | some x => inter x nw.back)
            if !candSet.contains nw.back then
              candSet := candSet.insert nw.back
              cands := cands.push nw.back
      match inter? with
      | none => return #[]   -- no entry for this need yet: nothing to do
      | some x => F := union F x
  if sub F t then
    return (cands.filter fun X => !sub X t).map (union t ·)
  else return #[union t F]

def backRule (v : Nat) : M Unit := do
  let O ← getO
  let seeds ← (backPlan O · v) <$> get
  let (ty, k, pool) ← (fun s => let nd := s.nodes[v]!; (nd.ty, nd.ctx, nd.pool)) <$> get
  let cfg ← getCfg
  let inh := if cfg.inherit then pool else #[]
  for sd in seeds do
    if (← (fun s => s.nodes[v]!.backDone.contains sd) <$> get) then continue
    modify fun s => { s with nodes := s.nodes.modify v fun nd => { nd with backDone := nd.backDone.insert sd } }
    for t' in ← branchesM sd (some ty) do
      modify fun s => { s with nBackVar := s.nBackVar + 1 }
      addNode k t' inh

/-- Default specs of a node: one per lower clause at its type (unless the
parent entry meets it). -/
def defaultSpecs (O : Onto) (cfg : Cfg) (key : CtxKey) (t : Ty) : Array Spec := Id.run do
  let mut out : Array Spec := #[]
  for a in t do
    for qi in O.lowBy[a]! do
      let (_, k, R, b) := O.low[qi]!
      let covered := k == 1 && mem key.lab R && mem key.pi b
      if !(cfg.skipCovered && covered) then
        out := out.push { lab := O.up[R]!, fill := #[b] }
  return out

/-- Lazy disjunction: node `v` took the default definer `w` of a top
disjunction; its at-most clause may be violated, so add the variants that
take each other head name instead (the branches of `(t \ {w}) ∪ {h}`). -/
def lazyAlt (v : Nat) (w : Nat) : M Unit := do
  let O ← getO
  let (ty, k, pool, done) ← (fun s => let nd := s.nodes[v]!; (nd.ty, nd.ctx, nd.pool, nd.backDone.contains #[w, w])) <$> get
  if done then return
  modify fun s => { s with nodes := s.nodes.modify v fun nd => { nd with backDone := nd.backDone.insert #[w, w] } }
  let some gi := O.lazyOf.get? w | return
  let (_, h) := O.gcis[gi]!
  let cfg ← getCfg
  let inh := if cfg.inherit then pool else #[]
  let base := ty.filter (· != w)
  for x in h do
    if x == w then continue
    for t' in ← branchesM (union base #[x]) do
      modify fun s => { s with nLazyVar := s.nLazyVar + 1 }
      addNode k t' inh

/-- Whether the at-most clauses of `w` may be violated at node `v`: the
parent entry plus the bound on counting entries of a minimal star (as in
`trigger`) exceeds the number. A name with no at-most clause gives `true`. -/
def mayViolate (v : Nat) (w : Nat) : M Bool := do
  let O ← getO
  let s ← get
  let nd := s.nodes[v]!
  let key := s.ctxs[nd.ctx]!.key
  let t := nd.ty
  if (O.uppBy[w]!).isEmpty then return true
  for ui in O.uppBy[w]! do
    let (_, n, S, e) := O.upp[ui]!
    let parentC := mem key.lab S && mem key.pi e
    let mut cs : Array Nat := #[]
    for i in [0:nd.pool.size] do
      if mem nd.pool[i]!.lab S && s.ctxs[nd.kids[i]!]!.uni.contains e then cs := cs.push i
    let mut pot := if parentC then 1 else 0
    for a' in t do
      for qi in O.lowBy[a']! do
        let (_, k, R, b) := O.low[qi]!
        if cs.any fun i => mem nd.pool[i]!.lab R && s.ctxs[nd.kids[i]!]!.uni.contains b then
          pot := pot + k
    if pot > n then return true
  return false

/-- What the merge and parent-witness rules ask at node `v`: specs to add,
parent-witness requests `(B, Lc)`, and lazy definers whose clause may be
violated. A pure function of the state, so that the state is not held
while the updates run. -/
def triggerPlan (O : Onto) (cfg : Cfg) (s : St) (v : Nat) :
    Array Spec × Array (Ty × Ty) × Array Nat := Id.run do
  let nd := s.nodes[v]!
  let key := s.ctxs[nd.ctx]!.key
  let t := nd.ty
  let mut adds : Array Spec := #[]
  let mut pws : Array (Ty × Ty) := #[]
  let mut lz : Array Nat := #[]
  for a in t do
    for ui in O.uppBy[a]! do
      let (_, n, S, e) := O.upp[ui]!
      let parentC := mem key.lab S && mem key.pi e
      -- specs that may count for the clause
      let mut cs : Array Nat := #[]
      for i in [0:nd.pool.size] do
        let σ := nd.pool[i]!
        if mem σ.lab S then
          let u := s.ctxs[nd.kids[i]!]!.uni
          if u.contains e then cs := cs.push i
      let lazyA := O.lazyOf.contains a
      if cs.isEmpty && !(lazyA && parentC && n == 0) then continue
      -- an upper bound on the entries of a minimal star that count
      let mut pot := if parentC then 1 else 0
      for a' in t do
        for qi in O.lowBy[a']! do
          let (_, k, R, b) := O.low[qi]!
          if cs.any fun i => mem nd.pool[i]!.lab R && s.ctxs[nd.kids[i]!]!.uni.contains b then
            pot := pot + k
      if pot ≤ n then continue
      if lazyA && cfg.lazyEager then lz := lz.push a
      if cfg.funcMerge && n == 1 && cfg.checkedMerge then
        -- the merge rule that `SRIQ/FastCheck.lean` checks: `M` is the
        -- union of the definitely counted default specs (filler in the
        -- child seed or in every type); add `σ ∪ M` for every spec `σ`
        -- that may count, and `σ₁ ∪ σ₂` for every two of them that
        -- contain `M`
        let atomic : HashSet Spec := (defaultSpecs O cfg key t).foldl (·.insert ·) ∅
        let always := O.gciTop.any fun g => (O.gcis[g]!).2 == #[e]
        let mut defs : Array Spec := #[]
        for i in cs do
          let σ := nd.pool[i]!
          if atomic.contains σ && (always || mem s.ctxs[nd.kids[i]!]!.key.seed e) then
            defs := defs.push σ
        if !defs.isEmpty then
          let M : Spec := defs.foldl (fun m σ => { lab := union m.lab σ.lab, fill := union m.fill σ.fill }) defs[0]!
          let sup : Array Spec := cs.filterMap fun i =>
            let σ := nd.pool[i]!
            if sub M.lab σ.lab && sub M.fill σ.fill then some σ else none
          for i in cs do
            let σ := nd.pool[i]!
            adds := adds.push { lab := union σ.lab M.lab, fill := union σ.fill M.fill }
          for x in [0:sup.size] do
            for y in [x+1:sup.size] do
              adds := adds.push { lab := union sup[x]!.lab sup[y]!.lab, fill := union sup[x]!.fill sup[y]!.fill }
          if parentC then
            for i in cs do
              let σ := nd.pool[i]!
              pws := pws.push (σ.fill, σ.lab)
          continue
      if cfg.funcMerge && n == 1 && !cfg.checkedMerge then
        -- at most one counted neighbour: the definitely counted default
        -- specs (filler in the child seed or in every type) all go into
        -- one child; the possibly counted ones join it in every combination
        let atomic : HashSet Spec := (defaultSpecs O cfg key t).foldl (·.insert ·) ∅
        let mut defs : Array Spec := #[]
        let mut poss : Array Spec := #[]
        for i in cs do
          let σ := nd.pool[i]!
          if !atomic.contains σ then continue
          let always := O.gciTop.any fun g => (O.gcis[g]!).2 == #[e]
          if always || mem s.ctxs[nd.kids[i]!]!.key.seed e then defs := defs.push σ else poss := poss.push σ
        if !defs.isEmpty && poss.size ≤ 8 then
          let M : Spec := defs.foldl (fun m σ => { lab := union m.lab σ.lab, fill := union m.fill σ.fill }) defs[0]!
          -- the definite group all or nothing (a definite spec left out is
          -- one whose demands another entry or the parent serves), with
          -- every subset of the possible ones
          let mut outs : Array Spec := #[M]
          let mut alone : Array Spec := #[]
          for σ in poss do
            outs := outs ++ outs.map fun (m : Spec) => ({ lab := union m.lab σ.lab, fill := union m.fill σ.fill } : Spec)
            alone := (alone ++ alone.map (fun (m : Spec) => ({ lab := union m.lab σ.lab, fill := union m.fill σ.fill } : Spec))).push σ
          outs := outs ++ alone
          for m in outs do
            adds := adds.push m
            if parentC then pws := pws.push (m.fill, m.lab)
          continue
      for x in [0:cs.size] do
        for y in [x+1:cs.size] do
          let σ1 := nd.pool[cs[x]!]!; let σ2 := nd.pool[cs[y]!]!
          adds := adds.push { lab := union σ1.lab σ2.lab, fill := union σ1.fill σ2.fill }
      if parentC then
        for i in cs do
          let σ := nd.pool[i]!
          pws := pws.push (σ.fill, σ.lab)
  return (adds, pws, lz)

/-- Merge and parent-witness triggers of node `v`. -/
def trigger (v : Nat) : M Unit := do
  let O ← getO
  let cfg ← getCfg
  let (adds, pws, lz) ← (triggerPlan O cfg · v) <$> get
  let k ← (fun s => s.nodes[v]!.ctx) <$> get
  for a in lz do lazyAlt v a
  for m in adds do
    if !(← (fun s => s.nodes[v]!.poolSet.contains m) <$> get) then
      modify fun s => { s with nMerge := s.nMerge + 1 }
      addSpec v m
  for r in pws do addPW k r

def initNode (v : Nat) (inh : Array Spec) : M Unit := do
  let O ← getO
  let cfg ← getCfg
  let specs ← (fun s => let nd := s.nodes[v]!; defaultSpecs O cfg s.ctxs[nd.ctx]!.key nd.ty) <$> get
  for σ in specs do addSpec v σ
  for σ in inh do addSpec v σ
  enqueue (.trig v)
  if cfg.forcedBack then enqueue (.back v)

def progressLine (s : St) : String :=
  let specs := s.nodes.foldl (fun a nd => a + nd.pool.size) 0
  s!"progress: events={s.nEvents} queue={s.queue.size - s.qpos} ctxs={s.ctxs.size} nodes={s.nodes.size} specs={specs} merges={s.nMerge} pw_requests={s.nPW} back_variants={s.nBackVar} pw_variants={s.nPWVar} lazy_variants={s.nLazyVar} superseded={s.nSup} rounds={s.nRounds} ms_init={s.nsInit/1000000} ms_trig={s.nsTrig/1000000} ms_back={s.nsBack/1000000} ms_branch={s.nsBranch/1000000} branch_calls={s.nBranchCalls} branches={s.nBranches} max_branches={s.maxBranches}"

/-- One step of the event loop; `false` when nothing is left. -/
def step : M Bool := do
  let (aborted, nEv, last) ← (fun s => (s.aborted, s.nEvents, s.lastReport)) <$> get
  if aborted then return false
  if nEv % 1000 == 0 then
    let now ← IO.monoMsNow
    if last == 0 then modify fun s => { s with lastReport := now }
    else if now - last ≥ 5000 then
      IO.eprintln (progressLine (← get))
      modify fun s => { s with lastReport := now }
  modify fun s => { s with nEvents := s.nEvents + 1 }
  let next ← (fun s => if s.qpos < s.queue.size then some s.queue[s.qpos]! else none) <$> get
  if let some e := next then
    modify fun s => { s with qpos := s.qpos + 1 }
    let t0 ← IO.monoNanosNow
    match e with
    | .init v inh =>
      initNode v inh
      let t1 ← IO.monoNanosNow
      modify fun s => { s with nsInit := s.nsInit + (t1 - t0) }
    | .trig v =>
      modify fun s => { s with pendTrig := s.pendTrig.erase v }
      trigger v
      let t1 ← IO.monoNanosNow
      modify fun s => { s with nsTrig := s.nsTrig + (t1 - t0) }
    | .back v =>
      modify fun s => { s with pendBack := s.pendBack.erase v }
      backRule v
      let t1 ← IO.monoNanosNow
      modify fun s => { s with nsBack := s.nsBack + (t1 - t0) }
    if (← (fun s => s.qpos) <$> get) > 100000 then
      modify fun s => { s with queue := s.queue.extract s.qpos s.queue.size }
      modify fun s => { s with qpos := 0 }
    return true
  else return false

partial def run : M Unit := do
  while (← step) do pure ()

/-- Generate from the requested names. Returns the state and the root contexts. -/
def generate (O : Onto) (cfg : Cfg) (req : Array Nat) : IO (St × Array Nat) := do
  let act : M (Array Nat) := do
    let mut roots := #[]
    for a in req do
      roots := roots.push (← getCtx { seed := #[a], lab := #[], pi := #[] })
    run
    return roots
  let (roots, st) ← (act.run (O, cfg)).run {}
  return (st, roots)

/-! ## Elimination -/

/-- Search a multiset of entries (each a pair: the lower clauses it counts
for, the upper clauses it counts for) that meets every need without
exceeding any limit. -/
partial def search (entries : Array (Array Nat × Array Nat)) (needs : Array Int) (lims : Array Int) :
    Bool := Id.run do
  let rec go (needs : Array Int) (lims : Array Int) (seen : HashSet (Array Int)) :
      Bool × HashSet (Array Int) :=
    match needs.findIdx? (· > 0) with
    | none => (true, seen)
    | some q =>
      let key := needs ++ lims
      if seen.contains key then (false, seen) else
      let seen := seen.insert key
      entries.foldl (fun (acc : Bool × HashSet (Array Int)) e =>
        if acc.1 then acc else
        if !e.1.contains q then acc else
        if e.2.any (fun u => lims[u]! ≤ 0) then acc else
        let needs' := e.1.foldl (fun ns q' => ns.modify q' (· - 1)) needs
        let lims' := e.2.foldl (fun ls u => ls.modify u (· - 1)) lims
        go needs' lims' acc.2) (false, seen)
  return (go needs lims ∅).1

structure ElimStats where
  checks : Nat := 0
  searches : Nat := 0
  deriving Repr

/-- Whether node `v` has a supporting star among the alive nodes. -/
def supported (O : Onto) (st : St) (alive : Array Bool) (v : Nat) : Bool × Bool := Id.run do
  let nd := st.nodes[v]!
  let key := st.ctxs[nd.ctx]!.key
  let t := nd.ty
  -- lower clauses with a positive need, upper clauses with their limits
  let mut lows : Array (Nat × Nat × Int) := #[]   -- (R, b, need)
  let mut ups : Array (Nat × Nat × Int) := #[]    -- (S, e, limit)
  for a in t do
    for qi in O.lowBy[a]! do
      let (_, k, R, b) := O.low[qi]!
      let pc : Int := if mem key.lab R && mem key.pi b then 1 else 0
      let need : Int := (k : Int) - pc
      if need > 0 then lows := lows.push (R, b, need)
    for ui in O.uppBy[a]! do
      let (_, n, S, e) := O.upp[ui]!
      let pc : Int := if mem key.lab S && mem key.pi e then 1 else 0
      let lim : Int := (n : Int) - pc
      if lim < 0 then return (false, false)
      ups := ups.push (S, e, lim)
  if lows.isEmpty then return (true, false)
  -- candidate entries, deduplicated by signature
  let mut sigs : HashSet (Array Nat × Array Nat) := ∅
  let mut entries : Array (Array Nat × Array Nat) := #[]
  for i in [0:nd.pool.size] do
    let σ := nd.pool[i]!
    let c := st.ctxs[nd.kids[i]!]!
    for w in c.nodes do
      if alive[w]! then
        let nw := st.nodes[w]!
        if sub nw.back t then
          let mut ls : Array Nat := #[]
          for j in [0:lows.size] do
            let (R, b, _) := lows[j]!
            if mem σ.lab R && mem nw.ty b then ls := ls.push j
          if ls.isEmpty then continue
          let mut us : Array Nat := #[]
          for j in [0:ups.size] do
            let (S, e, _) := ups[j]!
            if mem σ.lab S && mem nw.ty e then us := us.push j
          let sg := (ls, us)
          if !sigs.contains sg then
            sigs := sigs.insert sg
            entries := entries.push sg
  -- every need must be coverable
  for j in [0:lows.size] do
    if !entries.any (·.1.contains j) then return (false, false)
  if entries.all (·.2.isEmpty) then return (true, false)
  let needs := lows.map (·.2.2)
  let lims := ups.map (·.2.2)
  return (search entries needs lims, true)

/-- Remove unsupported nodes until stable. -/
partial def eliminate (O : Onto) (st : St) : Array Bool × ElimStats := Id.run do
  let N := st.nodes.size
  let mut alive : Array Bool := Array.replicate N true
  let mut inQ : Array Bool := Array.replicate N true
  let mut q : Array Nat := Array.range N
  let mut pos := 0
  let mut stats : ElimStats := {}
  while pos < q.size do
    let v := q[pos]!
    pos := pos + 1
    inQ := inQ.set! v false
    if !alive[v]! then continue
    stats := { stats with checks := stats.checks + 1 }
    let (ok, srch) := supported O st alive v
    if srch then stats := { stats with searches := stats.searches + 1 }
    if !ok then
      alive := alive.set! v false
      for (μ, _) in st.ctxs[st.nodes[v]!.ctx]!.parents do
        if alive[μ]! && !inQ[μ]! then
          inQ := inQ.set! μ true
          q := q.push μ
  return (alive, stats)

/-- Generation and elimination in rounds: after each elimination, every
dead node that holds the default definer `w` of a lazy disjunction gets
the variants that take the other head names (`lazyAlt`); stop when a round
adds no node. Returns the state, the root contexts and the alive flags. -/
def generateRounds (O : Onto) (cfg : Cfg) (req : Array Nat) :
    IO (St × Array Nat × Array Bool × ElimStats) := do
  let act : M (Array Nat × Array Bool × ElimStats) := do
    let mut roots := #[]
    let tr0 ← IO.monoMsNow
    for a in req do
      roots := roots.push (← getCtx { seed := #[a], lab := #[], pi := #[] })
      if roots.size % 10000 == 0 && (← IO.getEnv "KM_SRIQF_TRACEROOTS").isSome then
        IO.eprintln s!"roots {roots.size} ms {(← IO.monoMsNow) - tr0} nodes {(← get).nodes.size}"
    let mut res : Array Bool × ElimStats := (#[], {})
    repeat
      run
      if (← get).aborted then break
      modify fun s => { s with nRounds := s.nRounds + 1 }
      res ← (eliminate O ·) <$> get
      let before ← (fun s => s.nodes.size) <$> get
      let todo ← (fun (s : St) => Id.run do
        let mut out : Array (Nat × Nat) := #[]
        for v in [0:s.nodes.size] do
          if res.1[v]! then continue
          for w in s.nodes[v]!.ty do
            if O.lazyOf.contains w then out := out.push (v, w)
        return out) <$> get
      for (v, w) in todo do
        if ← mayViolate v w then lazyAlt v w
      if (← get).nodes.size == before then break
      if (← get).nRounds > 0 then
        IO.eprintln s!"round {(← get).nRounds}: nodes {before} -> {(← get).nodes.size}"
    return (roots, res)
  let ((roots, alive, es), st) ← (act.run (O, cfg)).run {}
  return (st, roots, alive, es)

/-! ## Readout -/

/-- For every requested name: `none` (unsatisfiable) or its subsumers,
the names in every alive root type that holds it. -/
def readout (st : St) (alive : Array Bool) (roots : Array Nat) (req : Array Nat) :
    Array (Nat × Option Ty) := Id.run do
  let mut rootTys : Array Ty := #[]
  for k in roots do
    for v in st.ctxs[k]!.nodes do
      if alive[v]! then rootTys := rootTys.push st.nodes[v]!.ty
  -- index by name
  let mut byName : HashMap Nat (Array Nat) := ∅
  for i in [0:rootTys.size] do
    for x in rootTys[i]! do
      byName := byName.insert x ((byName.getD x #[]).push i)
  let mut out := #[]
  for a in req do
    match byName.get? a with
    | none => out := out.push (a, none)
    | some is =>
      let mut acc := rootTys[is[0]!]!
      for i in is do acc := inter acc rootTys[i]!
      out := out.push (a, some acc)
  return out

end SRIQFast
