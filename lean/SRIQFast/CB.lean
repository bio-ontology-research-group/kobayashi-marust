import Std.Data.HashMap
import Std.Data.HashSet
import ContextCalculus.SRIQ.CBTypes
import SRIQFast.Core
import ContextCalculus.SRIQ.FastArr

/-!
# Consequence-based saturation with a derivation certificate (stage C1f, unproved)

`docs/V1.7.0-C1F-CLOSURE.md`, section 4. Nothing here is proved: the
saturation proposes a derivation (`CStep`s) and the derived names of each
requested name; `witness` builds a candidate set (`CandA`) whose live
root types should equal the derived names. The certified route checks
both (`CBCert.lean`).

Contexts. A root context per requested name (core `a`, no predecessor)
and a successor context per (label `upS R`, filler `b`) of a lower
clause. A context with core `b` and label `Lc` stores *items*, each a
clause `⟨Lc, P, {b}, H, Q⟩` with `|H| + |Q| ≤ 1` (a fact, a back name or
a clash) under a condition `P` on the predecessor, with the minimal
conditions kept per head. Hypotheses: names that a predecessor holds and
that a universal clause forwards across `Lc`.
-/

namespace SRIQFast.CBGen

open Std
open ContextCalculus.SRIQ.CB

/-- Item kinds: a name at `x`, a name at `y`, a clash. -/
abbrev Kind := Nat
def kX : Kind := 0
def kY : Kind := 1
def kBot : Kind := 2
/-- a clash clause with one more name at `x` (`⟨Lc, P, {core, h}, ∅, ∅⟩`) -/
def kNeg : Kind := 3
/-- a disjunction of names at `x` -/
def kDisj : Kind := 4

structure Ix where
  n : Nat
  nr : Nat
  /-- ontology clauses (positions as in the ontology) -/
  cls : Array QC
  gciBy : Array (Array Nat)
  gciTop : Array Nat
  /-- `a ↦ (S, c, pos)` -/
  allBy : Array (Array (Nat × Nat × Nat))
  /-- `a ↦ (k, R, b, pos)` with `k ≥ 1` -/
  lowBy : Array (Array (Nat × Nat × Nat × Nat))
  /-- `a ↦ (k, S, e, pos)` -/
  uppBy : Array (Array (Nat × Nat × Nat × Nat))
  up : Array Ty
  /-- the at-most clauses with number 0: `(a, S, e, pos)` -/
  upp0 : Array (Nat × Nat × Nat × Nat)
  /-- heads of gcis with several heads -/
  dh : HashSet Nat

def mkIx (n m : Nat) (cls : Array QC) : Ix := Id.run do
  let nr := 2 * m
  let mut gciBy : Array (Array Nat) := Array.replicate n #[]
  let mut gciTop : Array Nat := #[]
  let mut allBy : Array (Array (Nat × Nat × Nat)) := Array.replicate n #[]
  let mut lowBy : Array (Array (Nat × Nat × Nat × Nat)) := Array.replicate n #[]
  let mut uppBy : Array (Array (Nat × Nat × Nat × Nat)) := Array.replicate n #[]
  let mut subs : Array (Array Nat) := Array.replicate nr #[]
  let mut upp0 : Array (Nat × Nat × Nat × Nat) := #[]
  let mut dh : HashSet Nat := ∅
  for h : i in [0:cls.size] do
    match cls[i] with
    | .gci b hd =>
      let b' := sortDedup b
      if hd.size ≥ 2 then dh := hd.foldl (·.insert ·) dh
      if b'.isEmpty then gciTop := gciTop.push i
      for a in b' do gciBy := pushAt gciBy a i
    | .ex a R b => lowBy := pushAt lowBy a (1, R, b, i)
    | .ge a k R b => if k > 0 then lowBy := pushAt lowBy a (k, R, b, i)
    | .le a k S e =>
      uppBy := pushAt uppBy a (k, S, e, i)
      if k == 0 then upp0 := upp0.push (a, S, e, i)
    | .all a S c => allBy := pushAt allBy a (S, c, i)
    | .sub R S =>
      subs := pushAt subs R S
      subs := pushAt subs (R ^^^ 1) (S ^^^ 1)
  let up := (Array.range nr).map fun r => upClose subs r
  return { n, nr, cls, gciBy, gciTop, allBy, lowBy, uppBy, up, upp0, dh }

/-- A learned rule in a context: body names at `x`, conditions at `y`, a
head of a kind, the role set of its clause, its clause. -/
structure LRule where
  body : Ty
  py : Ty
  kind : Kind
  head : Nat
  cid : Nat
deriving Inhabited

/-- A merge group: an at-most clause at a context with its counted
children (`par`: the parent is counted too). -/
structure Group where
  ctx : Nat
  upos : Nat
  a : Nat
  k : Nat
  S : Nat
  e : Nat
  par : Bool
  members : Array (Nat × Nat) := #[]
  memSet : HashSet Nat := ∅
  /-- children holding `e`: child ↦ (condition, clause) -/
  eHold : HashMap Nat (Array (Ty × Nat)) := ∅
deriving Inhabited

structure Ctx where
  core : Nat
  lab : Ty
  root : Bool
  hyps : HashSet Nat := ∅
  /-- items by (kind, head): their conditions and clauses -/
  items : HashMap (Nat × Nat) (Array (Ty × Nat)) := ∅
  /-- items in order of derivation -/
  itemLog : Array (Kind × Nat × Ty × Nat) := #[]
  rules : Array LRule := #[]
  rulesBy : HashMap Nat (Array Nat) := ∅
  kids : Array (Nat × Nat) := #[]
  kidSet : HashSet Nat := ∅
  parents : Array (Nat × Nat) := #[]
  /-- the groups at this context, by at-most position -/
  groupsAt : HashMap Nat Nat := ∅
  /-- the groups this context is a member of -/
  memb : Array Nat := #[]
  /-- static clause cache: (tag, ontology position) ↦ clause -/
  stat : HashMap (Nat × Nat) Nat := ∅
  ruleSet : HashSet (Ty × Ty × Nat × Nat) := ∅
  negs : HashMap Nat (Array (Ty × Nat)) := ∅
  disj : Array (Array Nat × Ty × Nat) := #[]
  disjBy : HashMap Nat (Array Nat) := ∅
  disjDone : HashSet Nat := ∅
deriving Inhabited

inductive Ev where
  | item (c : Nat) (kind : Kind) (h : Nat) (cond : Ty) (cid : Nat)
  | hyp (c : Nat) (a : Nat)
  | kid (p : Nat) (q : Nat) (c : Nat)
  | rule (c : Nat) (r : Nat)
  /-- children for the lower clauses of a disjunction head -/
  | links (c : Nat) (h : Nat)
deriving Inhabited

structure St where
  steps : Array CStep := #[]
  ctxs : Array Ctx := #[]
  succIdx : HashMap (Ty × Nat) Nat := ∅
  groups : Array Group := #[]
  queue : Array Ev := #[]
  qhead : Nat := 0
  combCut : Nat := 0
  stat : HashMap (Nat × Nat) Nat := ∅
  nEv : Nat := 0
  aborted : Bool := false

abbrev M := ReaderT (Ix × Nat) (StateT St IO)

def getIx : M Ix := return (← read).1

def emit (r : CRule) (c : CCl) : M Nat :=
  modifyGet fun s => (s.steps.size, { s with steps := s.steps.push ⟨r, c⟩ })

def enq (e : Ev) : M Unit := modify fun s => { s with queue := s.queue.push e }

def ctxAt (c : Nat) : M Ctx := return (← get).ctxs[c]!

def modCtx (c : Nat) (f : Ctx → Ctx) : M Unit :=
  modify fun s => { s with ctxs := s.ctxs.modify c f }

def clOf (cid : Nat) : M CCl := return ((← get).steps[cid]!).c

/-- The clause of an item of context `c`. -/
def itemCl (cx : Ctx) (kind : Kind) (h : Nat) (cond : Ty) : CCl :=
  { L := cx.lab, P := cond, B := #[cx.core],
    H := if kind == kX then #[h] else #[], Q := if kind == kY then #[h] else #[] }

/-- Insert an item unless a weaker condition is present; enqueue it. -/
def addItem (c : Nat) (kind : Kind) (h : Nat) (cond : Ty) (cid : Nat) : M Unit := do
  let cx ← ctxAt c
  let old := cx.items.getD (kind, h) #[]
  if old.any (fun p => sub p.1 cond) then return
  modCtx c fun cx => { cx with
    items := cx.items.insert (kind, h) (old.push (cond, cid))
    itemLog := cx.itemLog.push (kind, h, cond, cid) }
  enq (.item c kind h cond cid)

/-- Resolve the heads of disjunction `di` of `c` with the clash clauses
that hold one of them. -/
partial def reduceDisj (c : Nat) (di : Nat) : M Unit := do
  let cx ← ctxAt c
  if cx.disjDone.contains di then return
  let (hs, _, cid) := cx.disj[di]!
  let mut cur := cid
  let mut curC ← clOf cid
  for h in hs do
    match ((← ctxAt c).negs.getD h #[])[0]? with
    | some (_, ni) =>
      let ncl ← clOf ni
      let r : CCl := { L := union curC.L ncl.L, P := union curC.P ncl.P,
                       B := union curC.B (ncl.B.filter (· != h)),
                       H := union (curC.H.filter (· != h)) ncl.H, Q := union curC.Q ncl.Q }
      cur ← emit (.resX cur ni h) r
      curC := r
    | none => pure ()
  if curC.H.size == hs.size then return
  if curC.H.size ≤ 1 then
    modCtx c fun cx => { cx with disjDone := cx.disjDone.insert di }
    if curC.H.size == 1 then addItem c kX curC.H[0]! curC.P cur
    else addItem c kBot 0 curC.P cur
  else
    modCtx c fun cx => { cx with disj := cx.disj.set! di (curC.H, curC.P, cur) }

/-- Record a clash clause with the extra name `o`. -/
partial def addNeg (c : Nat) (o : Nat) (cond : Ty) (cid : Nat) : M Unit := do
  let cx ← ctxAt c
  let old := cx.negs.getD o #[]
  if old.any (fun p => sub p.1 cond) then return
  modCtx c fun cx => { cx with negs := cx.negs.insert o (old.push (cond, cid)) }
  for di in (← ctxAt c).disjBy.getD o #[] do reduceDisj c di

mutual
/-- Derive an item by resolving the body of the clause `rid` (whose body
names are at `x`) with facts of context `c`; `fixed` gives the fact to
use for one body name. -/
partial def fire (c : Nat) (rid : Nat) (body : Ty) (kind : Kind) (h : Nat)
    (fixed : Option (Nat × Ty × Nat)) : M Unit := do
  let (core, lab, choicesO) ← do
    let cx ← ctxAt c
    let mut choices : Array (Nat × Array (Ty × Nat)) := #[]
    let mut ok := true
    let mut opn : Option Nat := none
    for d in body do
      match fixed with
      | some (fd, fc, fi) =>
        if fd == d then choices := choices.push (d, #[(fc, fi)]); continue
      | none => pure ()
      let fs := cx.items.getD (kX, d) #[]
      if fs.isEmpty then
        if kind == kBot && opn.isNone && d != cx.core && (← getIx).dh.contains d then opn := some d; continue
        ok := false; break
      choices := choices.push (d, fs)
    pure (cx.core, cx.lab, if ok then some (choices, opn) else none)
  let some (choices, opn) := choicesO | return
  -- enumerate up to a cap
  let cap := 64
  let mut combos : Array (Array (Ty × Nat)) := #[#[]]
  for (_, fs) in choices do
    let mut nxt : Array (Array (Ty × Nat)) := #[]
    for cmb in combos do
      for f in fs do
        if nxt.size < cap then nxt := nxt.push (cmb.push f)
        else modify fun s => { s with combCut := s.combCut + 1 }
    combos := nxt
  for cmb in combos do
    let mut cur := rid
    let mut curC ← clOf rid
    for i in [0:choices.size] do
      let d := choices[i]!.1
      let (fc, fi) := cmb[i]!
      let nb := union #[core] (curC.B.filter (· != d))
      let nc : CCl := { L := union lab curC.L, P := union fc curC.P, B := nb, H := curC.H, Q := curC.Q }
      cur ← emit (.resX fi cur d) nc
      curC := nc
    match opn with
    | some o => addNeg c o curC.P cur
    | none =>
      if kind == kDisj then addDisj c curC.H curC.P cur
      else addItem c kind h curC.P cur

/-- Record a disjunction; its heads get their children (for the clash
clauses that resolve them). -/
partial def addDisj (c : Nat) (hs : Array Nat) (cond : Ty) (cid : Nat) : M Unit := do
  let cx ← ctxAt c
  if hs.any (fun h => (cx.items.getD (kX, h) #[]).any (fun p => sub p.1 cond)) then return
  let di := cx.disj.size
  let upd (cx : Ctx) : Ctx :=
    let db := hs.foldl (fun m h => m.alter h (fun o => some ((o.getD #[]).push di))) cx.disjBy
    { cx with disj := cx.disj.push (hs, cond, cid), disjBy := db }
  modCtx c upd
  for h in hs do enq (.links c h)
  reduceDisj c di

end

/-- The clause of a static rule at context `c`, emitted once. -/
def statCl (_c : Nat) (tag pos : Nat) (r : CRule) (cl : CCl) : M Nat := do
  match (← get).stat.get? (tag, pos) with
  | some i => return i
  | none =>
    let i ← emit r cl
    modify fun s => { s with stat := s.stat.insert (tag, pos) i }
    return i

/-- Install a learned rule at context `c` and fire it on the facts present. -/
def addRule (c : Nat) (r : LRule) : M Unit := do
  let ri ← modifyGet fun s => ((s.ctxs[c]!).rules.size, s)
  let upd (cx : Ctx) : Ctx :=
    let rb := r.body.foldl (fun m d => m.alter d (fun o => some ((o.getD #[]).push ri))) cx.rulesBy
    { cx with rules := cx.rules.push r, rulesBy := rb, ruleSet := cx.ruleSet.insert (r.body, r.py, r.kind, r.head) }
  modCtx c upd
  enq (.rule c ri)

/-- A rule is worth adding at `c`: not there yet, and its head is not
already an item under a condition inside `py`. -/
def wantRule (c : Nat) (body py : Ty) (kind : Kind) (h : Nat) : M Bool := do
  let cx ← ctxAt c
  if cx.ruleSet.contains (body, py, kind, h) then return false
  let k := if kind == kBot then (kBot, 0) else (kind, h)
  return !((cx.items.getD k #[]).any fun p => sub p.1 py)

/-- The successor context of label `Lc` and core `b`. -/
def succCtx (Lc : Ty) (b : Nat) : M Nat := do
  match (← get).succIdx.get? (Lc, b) with
  | some i => return i
  | none =>
    let i := (← get).ctxs.size
    let cx0 : Ctx := { core := b, lab := Lc, root := false }
    modify fun s => { s with ctxs := s.ctxs.push cx0, succIdx := s.succIdx.insert (Lc, b) i }
    let t ← emit (.taut b) { L := Lc, P := #[], B := #[b], H := #[b], Q := #[] }
    addItem i kX b #[] t
    return i

def newRoot (a : Nat) : M Nat := do
  let i ← modifyGet fun s => (s.ctxs.size, { s with ctxs := s.ctxs.push { core := a, lab := #[], root := true } })
  let t ← emit (.taut a) { L := #[], P := #[], B := #[a], H := #[a], Q := #[] }
  addItem i kX a #[] t
  return i

def lowAt (ix : Ix) (pos : Nat) : Nat × Nat × Nat × Nat :=
  match ix.cls[pos]! with
  | .ex a R b => (a, 1, R, b)
  | .ge a k R b => (a, k, R, b)
  | _ => (0, 0, 0, 0)

/-- Stream item `(kind, h, cond, cid)` of member `c2` (holding `e` under
`(pe, ide)`) of group `g` to the group. -/
def streamItem (g : Nat) (c2 : Nat) (pe : Ty) (ide : Nat) (kind : Kind) (h : Nat) (cond : Ty)
    (cid : Nat) : M Unit := do
  let G := (← get).groups[g]!
  let ix ← getIx
  let some (q2, _) := G.members.find? (·.2 == c2) | return
  let (a2, _, _, b2) := lowAt ix q2
  let _ := b2
  let crB := (← clOf cid).B
  let rB := crB.filter (· != b2)
  if G.par then
    -- rule at the group's context `x`: body {a, a2} ∪ pe ∪ cond ∪ ... at x, py {e} ∪ rB
    let body := union (sortDedup #[G.a, a2]) (union pe cond)
    let nkind := if kind == kX then kY else if kind == kY then kX else kBot
    let ncl : CCl := { L := #[G.S ^^^ 1], P := union #[G.e] rB, B := body,
                       H := if kind == kY then #[h] else #[], Q := if kind == kX then #[h] else #[] }
    if ← wantRule G.ctx body ncl.P nkind h then
      let rid ← emit (.par G.upos q2 ide cid) ncl
      addRule G.ctx { body, py := ncl.P, kind := nkind, head := h, cid := rid }
  else
    if G.k > 1 then return
    let py := union (sortDedup #[G.a, a2]) (union pe cond)
    let ncl : CCl := { L := #[G.S], P := py, B := union #[G.e] rB,
                       H := if kind == kX then #[h] else #[], Q := if kind == kY then #[h] else #[] }
    let mut tg : Array Nat := #[]
    for (_, c3) in G.members do
      if c3 == c2 then continue
      if ← wantRule c3 ncl.B py kind h then tg := tg.push c3
    if tg.isEmpty then return
    let rid ← emit (.sib G.upos q2 ide cid) ncl
    for c3 in tg do
      addRule c3 { body := ncl.B, py, kind, head := h, cid := rid }

/-- Member `c2` of group `g` holds `e` under `(pe, ide)`. -/
def eHolds (g : Nat) (c2 : Nat) (pe : Ty) (ide : Nat) : M Unit := do
  let G := (← get).groups[g]!
  let old := G.eHold.getD c2 #[]
  if old.any (fun p => sub p.1 pe) then return
  modify fun s => { s with groups := s.groups.modify g fun G => { G with eHold := G.eHold.insert c2 (old.push (pe, ide)) } }
  let ix ← getIx
  let some (q2, _) := G.members.find? (·.2 == c2) | return
  let (a2, k2, _, _) := lowAt ix q2
  -- clash: more witnesses than allowed
  if k2 > G.k && !G.par then
    let ncl : CCl := { L := #[], P := #[], B := union (sortDedup #[G.a, a2]) pe, H := #[], Q := #[] }
    if ← wantRule G.ctx ncl.B #[] kBot 0 then
     let rid ← emit (.clash G.upos q2 ide) ncl
     addRule G.ctx { body := ncl.B, py := #[], kind := kBot, head := 0, cid := rid }
  if G.k ≤ 1 then
    let cx ← ctxAt c2
    for (kind, h, cond, cid) in cx.itemLog do
      streamItem g c2 pe ide kind h cond cid

/-- Add child `(q, c)` to group `g` if it is counted. -/
def joinGroup (g : Nat) (q : Nat) (c : Nat) : M Unit := do
  let G := (← get).groups[g]!
  let ix ← getIx
  let (_, _, R, _) := lowAt ix q
  if !mem (ix.up[R]!) G.S then return
  if G.memSet.contains c then return
  modify fun s => { s with groups := s.groups.modify g fun G =>
    { G with members := G.members.push (q, c), memSet := G.memSet.insert c } }
  modCtx c fun cx => { cx with memb := cx.memb.push g }
  -- already holding e?
  let cx ← ctxAt c
  for (pe, ide) in cx.items.getD (kX, G.e) #[] do eHolds g c pe ide
  -- a new sibling receives the items of the members holding `e`
  if !G.par && G.k ≤ 1 then
    let G := (← get).groups[g]!
    for (c2, hs) in G.eHold.toList do
      if c2 == c then continue
      let cx2 ← ctxAt c2
      for (pe, ide) in hs do
        for (kind, h, cond, cid) in cx2.itemLog do
          -- only toward the new member
          let some (q2, _) := G.members.find? (·.2 == c2) | continue
          let (a2, _, _, b2) := lowAt ix q2
          let rB := (← clOf cid).B.filter (· != b2)
          let py := union (sortDedup #[G.a, a2]) (union pe cond)
          let ncl : CCl := { L := #[G.S], P := py, B := union #[G.e] rB,
                             H := if kind == kX then #[h] else #[], Q := if kind == kY then #[h] else #[] }
          if ← wantRule c ncl.B py kind h then
            let rid ← emit (.sib G.upos q2 ide cid) ncl
            addRule c { body := ncl.B, py, kind, head := h, cid := rid }

def newGroup (c : Nat) (upos a k S e : Nat) (par : Bool) : M Unit := do
  let cx ← ctxAt c
  let key := if par then upos + 1000000000 else upos
  if cx.groupsAt.contains key then return
  let g := (← get).groups.size
  modify fun s => { s with groups := s.groups.push { ctx := c, upos, a, k, S, e, par } }
  modCtx c fun cx => { cx with groupsAt := cx.groupsAt.insert key g }
  for (q, c2) in cx.kids do joinGroup g q c2

/-- Send a hypothesis once. -/
def sendHyp (c a : Nat) : M Unit := do
  if (← ctxAt c).hyps.contains a then return
  modCtx c fun cx => { cx with hyps := cx.hyps.insert a }
  enq (.hyp c a)

/-- Process one event. -/
partial def step (e : Ev) : M Unit := do
  let ix ← getIx
  match e with
  | .links c h =>
    for (_, R, b, pos) in ix.lowBy[h]! do
      if (← ctxAt c).kidSet.contains pos then continue
      let c2 ← succCtx (ix.up[R]!) b
      modCtx c fun cx => { cx with kids := cx.kids.push (pos, c2), kidSet := cx.kidSet.insert pos }
      modCtx c2 fun cx => { cx with parents := cx.parents.push (c, pos) }
      enq (.kid c pos c2)
  | .rule c ri =>
    let cx ← ctxAt c
    let r := cx.rules[ri]!
    if !r.py.isEmpty && cx.root then return
    fire c r.cid r.body r.kind r.head none
  | .hyp c a =>
    let cx ← ctxAt c
    for (S, c', pos) in ix.allBy[a]! do
      if mem cx.lab S then
        let i ← emit (.fwd pos) { L := cx.lab, P := #[a], B := #[cx.core], H := #[c'], Q := #[] }
        addItem c kX c' #[a] i
  | .kid p q c =>
    let cp ← ctxAt p
    let (a, _, _, _) := lowAt ix q
    -- the child's back names and clashes become rules at the parent
    let cc ← ctxAt c
    for (kind, h, cond, cid) in cc.itemLog do
      if kind == kY || kind == kBot then
        let body := union cond #[a]
        if ← wantRule p body #[] (if kind == kY then kX else kBot) h then
          let rid ← emit (.pred q cid) { L := #[], P := #[], B := body,
                                         H := if kind == kY then #[h] else #[], Q := #[] }
          addRule p { body, py := #[], kind := if kind == kY then kX else kBot, head := h, cid := rid }
    -- hypotheses
    for ((kind, h), _) in cp.items.toList do
      if kind == kX && (ix.allBy[h]!).any (fun (S, _, _) => mem cc.lab S) then sendHyp c h
    for g in cp.groupsAt.toList do joinGroup g.2 q c
  | .item c kind h cond cid =>
    let (lab, root, parents, memb, rlist) ← do
      let cx ← ctxAt c
      pure (cx.lab, cx.root, cx.parents, cx.memb, cx.rulesBy.getD h #[])
    -- 1. parents: a back name or a clash becomes a rule at each parent
    if kind == kY || kind == kBot then
      for (p, q) in parents do
        let (a, _, _, _) := lowAt ix q
        let body := union cond #[a]
        if ← wantRule p body #[] (if kind == kY then kX else kBot) h then
          let rid ← emit (.pred q cid) { L := #[], P := #[], B := body,
                                         H := if kind == kY then #[h] else #[], Q := #[] }
          addRule p { body, py := #[], kind := if kind == kY then kX else kBot, head := h, cid := rid }
    -- 2. groups this context is in
    for g in memb do
      let G := (← get).groups[g]!
      if kind == kX && h == G.e then eHolds g c cond cid
      else if G.k ≤ 1 then
        for (pe, ide) in G.eHold.getD c #[] do streamItem g c pe ide kind h cond cid
    if kind != kX then return
    -- 3. rules with `h` in the body
    for gi in ix.gciBy[h]! do
      match ix.cls[gi]! with
      | .gci b hd =>
        let b' := sortDedup b
        let gid ← statCl c 0 gi (.gci gi) { L := #[], P := #[], B := b', H := sortDedup hd, Q := #[] }
        fire c gid b' (if hd.size == 1 then kX else if hd.size == 0 then kBot else kDisj) (hd[0]?.getD 0) (some (h, cond, cid))
      | _ => pure ()
    for ri in rlist do
      let r := (← ctxAt c).rules[ri]!
      if !r.py.isEmpty && root then continue
      fire c r.cid r.body r.kind r.head (some (h, cond, cid))
    -- 4. universals back to the predecessor
    if !root then
      for (S, c', pos) in ix.allBy[h]! do
        if mem lab (S ^^^ 1) then
          let bid ← statCl c 1 pos (.bwd pos) { L := #[S ^^^ 1], P := #[], B := #[h], H := #[], Q := #[c'] }
          fire c bid #[h] kY c' (some (h, cond, cid))
    -- 5. at-most clauses of `h`
    for (k, S, e, pos) in ix.uppBy[h]! do
      if k == 0 then
        -- toward a successor: rule at each child with `S` in its label
        -- (installed when the child is linked; see kid events) and toward the parent
        if !root && mem lab (S ^^^ 1) then
          let bid ← statCl c 2 pos (.amo0b pos) { L := #[S ^^^ 1], P := #[e], B := #[h], H := #[], Q := #[] }
          fire c bid #[h] kBot 0 (some (h, cond, cid))
      newGroup c pos h k S e false
      if k == 1 && !root && mem lab (S ^^^ 1) then newGroup c pos h k S e true
    -- 6. lower clauses of `h`: children
    for (_, R, b, pos) in ix.lowBy[h]! do
      if (← ctxAt c).kidSet.contains pos then continue
      let Lc := ix.up[R]!
      let c2 ← succCtx Lc b
      modCtx c fun cx => { cx with kids := cx.kids.push (pos, c2), kidSet := cx.kidSet.insert pos }
      modCtx c2 fun cx => { cx with parents := cx.parents.push (c, pos) }
      -- at-most 0 toward the child: `a(y), S(y,x), e(x) → ⊥` for parents holding `a`
      enq (.kid c pos c2)
    -- 7. hypotheses for the children
    for (_, c2) in (← ctxAt c).kids do
      let cc ← ctxAt c2
      if (ix.allBy[h]!).any (fun (S, _, _) => mem cc.lab S) then sendHyp c2 h

/-- At-most 0 toward `x`: in a successor context with `S ∈ Lc`, `e(x)` and
`a(y)` clash. Installed at context creation as rules. -/
def initRules (c : Nat) : M Unit := do
  let ix ← getIx
  let cx ← ctxAt c
  -- gcis with an empty body, resolved with the core
  for gi in ix.gciTop do
    match ix.cls[gi]! with
    | .gci _ hd =>
      let i ← emit (.gci gi) { L := cx.lab, P := #[], B := #[cx.core], H := sortDedup hd, Q := #[] }
      if hd.size ≤ 1 then addItem c (if hd.size == 1 then kX else kBot) (hd[0]?.getD 0) #[] i
      else addDisj c (sortDedup hd) #[] i
    | _ => pure ()
  if cx.root then return
  for (a, S, e, pos) in ix.upp0 do
    if mem cx.lab S then
      let rid ← emit (.amo0a pos) { L := #[S], P := #[a], B := #[e], H := #[], Q := #[] }
      addRule c { body := #[e], py := #[a], kind := kBot, head := 0, cid := rid }

partial def run (maxSteps : Nat) (deadline : Nat) : M Unit := do
  let mut seenCtx := 0
  repeat
    -- rules for new contexts
    while seenCtx < (← get).ctxs.size do
      initRules seenCtx
      seenCtx := seenCtx + 1
    let s ← get
    if s.qhead ≥ s.queue.size then break
    if s.steps.size > maxSteps || (s.nEv % 4096 == 0 && (← IO.monoMsNow) > deadline) then
      set { s with aborted := true }; break
    let e := s.queue[s.qhead]!
    let _ := s
    let nev := (← get).nEv + 1
    modify fun s => { s with nEv := nev }
    if nev % (if nev < 100000 then 5000 else 1000000) == 0 then
      let s ← get
      let nIt := s.ctxs.foldl (fun a c => a + c.itemLog.size) 0
      let nRu := s.ctxs.foldl (fun a c => a + c.rules.size) 0
      let ev := s.queue.extract s.qhead s.queue.size
      let cnt := ev.foldl (fun (a : Nat × Nat × Nat × Nat) e => match e with
        | .item .. => (a.1 + 1, a.2) | .hyp .. => (a.1, a.2.1 + 1, a.2.2) | .kid .. => (a.1, a.2.1, a.2.2.1 + 1, a.2.2.2)
        | .rule .. => (a.1, a.2.1, a.2.2.1, a.2.2.2 + 1) | .links .. => a) (0, 0, 0, 0)
      if nev % 5000000 == 0 then
        let mut tags : Array Nat := Array.replicate 13 0
        for st in s.steps do
          let t := match st.rule with
            | .gci .. => 0 | .taut .. => 1 | .fwd .. => 2 | .bwd .. => 3 | .up .. => 4 | .resX .. => 5
            | .resY .. => 6 | .pred .. => 7 | .amo0a .. => 8 | .amo0b .. => 9 | .clash .. => 10
            | .sib .. => 11 | .par .. => 12
          tags := tags.modify t (· + 1)
        let mut condItems := 0
        let mut kinds : Array Nat := #[0, 0, 0]
        for c in s.ctxs do
          for (k, _, cond, _) in c.itemLog do
            if !cond.isEmpty then condItems := condItems + 1
            kinds := kinds.modify k (· + 1)
        let roots := s.ctxs.foldl (fun a c => if c.root then a + 1 else a) 0
        IO.eprintln s!"cbtags: gci,taut,fwd,bwd,up,resX,resY,pred,amo0a,amo0b,clash,sib,par={tags} cond_items={condItems} kinds(x,y,bot)={kinds} roots={roots}"
      IO.eprintln s!"cbprog: ev={nev} steps={s.steps.size} ctxs={s.ctxs.size} items={nIt} rules={nRu} groups={s.groups.size} queue={ev.size} q(item,hyp,kid,rule)={cnt} combcut={s.combCut}"
    modify fun s => if s.qhead > 1000000 then
        { s with queue := s.queue.extract (s.qhead + 1) s.queue.size, qhead := 0 }
      else { s with qhead := s.qhead + 1 }
    step e

/-- The result: steps, for each requested name its root context, the
derived names (with their clause) and an unsatisfiability clause. -/
structure Res where
  steps : Array CStep
  st : St
  roots : Array Nat

def saturate (n m : Nat) (cls : Array QC) (req : Array Nat) (maxSteps : Nat := 50000000) (deadline : Nat := 0) :
    IO Res := do
  let ix := mkIx n m cls
  let act : M (Array Nat) := do
    let mut roots := #[]
    for a in req do roots := roots.push (← newRoot a)
    run maxSteps (if deadline == 0 then (1 <<< 62) else deadline)
    return roots
  let (roots, st) ← (act.run (ix, 0)).run {}
  return { steps := st.steps, st, roots }

/-- Rows: `none` for a clash at the root, else the derived names. -/
def rows (r : Res) (req : Array Nat) : Array (Nat × Option Ty) := Id.run do
  let mut out := #[]
  for i in [0:req.size] do
    let cx := r.st.ctxs[r.roots[i]!]!
    if (cx.items.getD (kBot, 0) #[]).any (·.1.isEmpty) then
      out := out.push (req[i]!, none)
    else
      let ds := cx.items.toList.filterMap fun ((k, h), cs) =>
        if k == kX && cs.any (·.1.isEmpty) then some h else none
      out := out.push (req[i]!, some (sortDedup ds.toArray))
  return out

/-! ## The witness: a candidate set from the derived facts -/

section Witness

open ContextCalculus.SRIQ.Fast (CandA NodeA KeyA EntryA)

structure WIx where
  ix : Ix
  /-- role code ↦ fillers of lower (number at least 1) and upper clauses -/
  relBy : Array Ty
  /-- contexts of the saturation by core -/
  byCore : HashMap Nat (Array Nat)
  /-- the facts `(name, condition)` of each saturation context -/
  facts : Array (Array (Nat × Ty))
  nreq : Nat

def mkWIx (ix : Ix) (st : St) (nreq : Nat) : WIx := Id.run do
  let mut rel : Array (Array Nat) := Array.replicate ix.nr #[]
  for c in ix.cls do
    match c with
    | .ex _ R b => rel := pushAt rel R b
    | .ge _ k R b => if k ≥ 1 then rel := pushAt rel R b
    | .le _ _ S e => rel := pushAt rel S e
    | _ => pure ()
  let mut byCore : HashMap Nat (Array Nat) := ∅
  for h : i in [0:st.ctxs.size] do
    let c := st.ctxs[i]
    byCore := byCore.insert c.core ((byCore.getD c.core #[]).push i)
  let facts := st.ctxs.map fun c => c.itemLog.filterMap fun (k, h, cond, _) => if k == kX then some (h, cond) else none
  return { ix, relBy := rel.map sortDedup, byCore, nreq, facts }

def wfwd (ix : Ix) (t : Ty) (L : Ty) : Ty := Id.run do
  if L.isEmpty then return #[]
  let mut acc : Array Nat := #[]
  for a in t do
    for (S, c, _) in ix.allBy[a]! do
      if mem L S then acc := acc.push c
  return sortDedup acc

def wrel (W : WIx) (L : Ty) : Ty := L.foldl (fun acc R => union acc (W.relBy[R]!)) #[]

/-- Does the saturation context `(up R, b)` derive `e` under conditions in `t`? -/
def derivesE (st : St) (ix : Ix) (R b e : Nat) (t : Ty) : Bool :=
  if b == e then true else
  match st.succIdx.get? (ix.up[R]!, b) with
  | none => false
  | some c => ((st.ctxs[c]!).items.getD (kX, e) #[]).any (fun p => sub p.1 t)

/-- A head of a disjunction for the witness: an at-most definer whose bound
already holds for the demands of `cur` (and the parent edge) first, then a
fresh name, then the first head. -/
def chooseHead (W : WIx) (st : St) (cur : HashSet Nat) (lab tp : Ty) (hd : Array Nat) : Nat := Id.run do
  let ix := W.ix
  let fl := flipL lab
  for h in hd do
    if h < W.nreq then continue
    if (ix.lowBy[h]!).size + (ix.allBy[h]!).size + (ix.gciBy[h]!).size != 0 then continue
    for (k, S, e, _) in ix.uppBy[h]! do
      let mut pot := if mem fl S && mem tp e then 1 else 0
      for a in cur.toArray do
        for (kk, R, b, _) in ix.lowBy[a]! do
          if mem (ix.up[R]!) S && derivesE st ix R b e (sortDedup cur.toArray) then pot := pot + kk
      if pot ≤ k then return h
  let fresh := hd.filter (· ≥ W.nreq)
  return if fresh.isEmpty then hd[0]! else fresh[0]!

/-- The type of a node with seed `seed`, label `lab` from the parent, parent
type `tp` (empty for a root): the closure of the seed under the gcis and
the derived facts that apply; `none` on a clash. Disjunctions take a
fresh head first. -/
partial def wtype (W : WIx) (st : St) (seed lab tp : Ty) (isRoot : Bool) : Option Ty := Id.run do
  let ix := W.ix
  let mut cur : HashSet Nat := seed.foldl (fun h x => h.insert x) ∅
  let mut todo : Array Nat := seed
  let mut i := 0
  let mut done : HashSet Nat := ∅
  -- top gcis
  for g in ix.gciTop do
    match ix.cls[g]! with
    | .gci _ hd => if hd.size == 1 && !cur.contains hd[0]! then
        cur := cur.insert hd[0]!; todo := todo.push hd[0]!
    | _ => pure ()
  repeat
    while i < todo.size do
      let x := todo[i]!
      i := i + 1
      -- derived facts of contexts with core `x` that apply
      for c in W.byCore.getD x #[] do
        let cx := st.ctxs[c]!
        if cx.root || (!isRoot && sub cx.lab lab) then
          if (cx.items.getD (kBot, 0) #[]).any (fun p => sub p.1 tp && (!isRoot || p.1.isEmpty)) then
            return none
          for (h, cond) in W.facts[c]! do
            if !cur.contains h && sub cond tp && (!isRoot || cond.isEmpty) then
              cur := cur.insert h; todo := todo.push h
      -- Horn gcis
      for g in ix.gciBy[x]! do
        match ix.cls[g]! with
        | .gci b hd =>
          if hd.size ≤ 1 && b.all (cur.contains ·) then
            if hd.size == 0 then return none
            if !cur.contains hd[0]! then cur := cur.insert hd[0]!; todo := todo.push hd[0]!
        | _ => pure ()
    -- one disjunction that fires
    let mut pick : Option Nat := none
    for x in todo do
      if pick.isSome then break
      for g in ix.gciBy[x]! do
        if done.contains g then continue
        match ix.cls[g]! with
        | .gci b hd =>
          if hd.size ≥ 2 && b.all (cur.contains ·) then
            done := done.insert g
            if !hd.any (cur.contains ·) then
              pick := some (chooseHead W st cur lab tp hd)
              break
        | _ => pure ()
    if pick.isNone then
      for g in ix.gciTop do
        if pick.isSome then break
        match ix.cls[g]! with
        | .gci _ hd =>
          if hd.size ≥ 2 && !hd.any (cur.contains ·) then
            pick := some (chooseHead W st cur lab tp hd)
        | _ => pure ()
    match pick with
    | none => break
    | some h => cur := cur.insert h; todo := todo.push h
  return some (sortDedup cur.toArray)

structure WSt where
  keys : Array KeyA := #[]
  keyIdx : HashMap (Ty × Ty × Ty) Nat := ∅
  nodes : Array NodeA := #[]
  members : Array (Array Nat) := #[]
  nodeIdx : HashMap (Nat × Ty) Nat := ∅
  /-- nodes whose pools are still to be made: (node, label from parent, parent type) -/
  todo : Array (Nat × Ty × Ty) := #[]
  /-- node types by (label, fill) of the spec that made them -/
  fam : HashMap (Ty × Ty) (Array Ty) := ∅
  reused : Nat := 0

def getKey (k : KeyA) : StateM WSt Nat := do
  match (← get).keyIdx.get? (k.seed, k.lab, k.pi) with
  | some i => return i
  | none =>
    let i := (← get).keys.size
    modify fun s => { s with keys := s.keys.push k, keyIdx := s.keyIdx.insert (k.seed, k.lab, k.pi) i, members := s.members.push #[] }
    return i

def getNode (k : Nat) (t : Ty) (lab tp : Ty) : StateM WSt Nat := do
  match (← get).nodeIdx.get? (k, t) with
  | some i => return i
  | none =>
    let i := (← get).nodes.size
    modify fun s => { s with nodes := s.nodes.push ⟨k, t, []⟩, nodeIdx := s.nodeIdx.insert (k, t) i, members := s.members.modify k (·.push i), todo := s.todo.push (i, lab, tp) }
    return i

/-- The pool of a node of type `t` in a context with key `κ`. -/
partial def wpool (W : WIx) (st : St) (t : Ty) (κ : KeyA) : StateM WSt (List EntryA) := do
  let ix := W.ix
  -- demands
  let mut specs : Array (Ty × Ty × Array Nat) := #[]   -- (label, fill, lower positions)
  for a in t do
    for (k, R, b, pos) in ix.lowBy[a]! do
      if k == 1 && mem κ.lab R && mem κ.pi b then continue
      specs := specs.push (ix.up[R]!, #[b], #[pos])
  -- functional merges
  let mut changed := true
  while changed do
    changed := false
    for a in t do
      for (k, S, e, _) in ix.uppBy[a]! do
        if k != 1 || changed then continue
        let cnt := specs.filter fun (L, F, ps) => mem L S &&
          ps.any (fun pos => let (_, _, R, b) := lowAt ix pos; derivesE st ix R b e t) && true
        if cnt.size ≥ 2 then
          let L := cnt.foldl (fun acc x => union acc x.1) #[]
          let F := cnt.foldl (fun acc x => union acc x.2.1) #[]
          let P := cnt.foldl (fun acc x => acc ++ x.2.2) #[]
          specs := (specs.filter fun x => !cnt.any (· == x)).push (L, F, P)
          changed := true
  -- the children
  let mut pool : List EntryA := []
  for (L0, F, _) in specs do
    let mut L := L0
    let mut res : Option (KeyA × Ty) := none
    for _ in [0:4] do
      let fl := flipL L
      let key : KeyA := ⟨union F (wfwd ix t L), fl, inter t (wrel W fl)⟩
      match wtype W st key.seed L t false with
      | none => res := none; break
      | some tc =>
        res := some (key, tc)
        -- the parent as the witness of a functional demand of the child
        let mut grow : Ty := #[]
        for a in tc do
          for (k, S, e, _) in ix.uppBy[a]! do
            if k == 1 && mem fl S && mem key.pi e then
              for a2 in tc do
                for (k2, R2, b2, _) in ix.lowBy[a2]! do
                  if k2 == 1 && mem (ix.up[R2]!) S && mem t b2 && !(mem fl R2 && mem key.pi b2) &&
                      derivesE st ix R2 b2 e tc then
                    grow := union grow (flipL (ix.up[R2]!))
        if grow.isEmpty || sub grow L then break
        L := union L grow
    match res with
    | none => pure ()
    | some (key, tc) =>
      let fl0 := flipL L
      let k ← getKey key
      -- reuse a larger type made for the same spec when its back set fits
      let cands := ((← get).fam.getD (L, F) #[])
      let mut ty := tc
      let mut i := cands.size
      let mut tries := 0
      while i > 0 && tries < 64 do
        i := i - 1
        tries := tries + 1
        let t' := cands[i]!
        if t' != tc && sub tc t' && sub (wfwd ix t' fl0) t && sub key.seed t' then
          ty := t'
          break
      if ty != tc then modify fun s => { s with reused := s.reused + 1 }
      else modify fun s => { s with fam := s.fam.insert (L, F) (cands.push tc) }
      let _ ← getNode k ty L t
      pool := ⟨L, F, k⟩ :: pool
  return pool.reverse

partial def wloop (W : WIx) (st : St) (fuel : Nat) : StateM WSt Unit := do
  let mut f := fuel
  repeat
    if (← get).todo.isEmpty || f == 0 then break
    f := f - 1
    let (i, _, _) ← modifyGet fun s => (s.todo.back!, { s with todo := s.todo.pop })
    let v := (← get).nodes[i]!
    let κ := (← get).keys[v.ctx]!
    let pool ← wpool W st v.ty κ
    modify fun s => { s with nodes := s.nodes.modify i fun v => { v with pool } }

/-- The witness candidate set: one root context per request (in order). -/
def witness (W : WIx) (st : St) (req : Array Nat) (maxNodes : Nat := 3000000) : CandA × Bool := Id.run do
  let act : StateM WSt (List Nat) := do
    let mut roots : List Nat := []
    for a in req do
      let k ← getKey ⟨#[a], #[], #[]⟩
      roots := k :: roots
      match wtype W st #[a] #[] #[] true with
      | none => pure ()
      | some t => let _ ← getNode k t #[] #[]
    wloop W st maxNodes
    return roots.reverse
  let (roots, s) := act.run {}
  let ix := W.ix
  let bk := s.nodes.map fun v => wfwd ix v.ty (s.keys[v.ctx]!).lab
  let uni := s.members.map fun ms => ms.foldl (fun acc j => ContextCalculus.SRIQ.Fast.unionA acc (s.nodes[j]!).ty) #[]
  ({ keys := s.keys, nodes := s.nodes, members := s.members, roots, bk, uni }, !s.todo.isEmpty)

end Witness

end SRIQFast.CBGen
