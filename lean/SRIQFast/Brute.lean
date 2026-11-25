import SRIQFast.Core

/-!
# A brute-force reference for small inputs (unproved)

The C1 star elimination of `SRIQ/Procedure.lean` over every closed type
and every nonempty up-closed label, with names and labels as bit masks.
It differs from `classifyQ` only in the search for a children list: an
exact search over multisets of contributing entries (`SRIQFast.search`)
instead of every list up to `bnd O`. That search finds a supporting
multiset whenever one exists (each step adds an entry of a fixed minimal
solution that counts for the first unmet need), so the alive records are
the same. The probe checks it against `classifyQ` where that finishes.
-/

namespace SRIQFast.Brute

open Std

@[inline] def bit (x : Nat) : Nat := 1 <<< x
@[inline] def has (mask x : Nat) : Bool := (mask >>> x) % 2 == 1
def maskOf (t : Array Nat) : Nat := t.foldl (fun m x => m ||| bit x) 0
def toTy (n mask : Nat) : Ty := (Array.range n).filter (has mask ·)

structure B where
  n : Nat
  O : Onto
  closed : Array Nat
  labels : Array Nat

def isClosed (O : Onto) (t : Nat) : Bool :=
  O.gcis.all fun (b, h) => !(b.all (has t ·)) || h.any (has t ·)

def upClosed (O : Onto) (L : Nat) : Bool :=
  (Array.range O.nr).all fun R => !(has L R) || (O.up[R]!).all (has L ·)

def flipM (nr L : Nat) : Nat :=
  (Array.range nr).foldl (fun acc R => if has L R then acc ||| bit (R ^^^ 1) else acc) 0

def edgeOK (O : Onto) (t L s : Nat) : Bool :=
  (Array.range O.n).all fun a =>
    (O.allBy[a]!).all fun (S, c) =>
      (!(has L S && has t a) || has s c) && (!(has L (S ^^^ 1) && has s a) || has t c)

/-- Every record, with the elimination run to the fixpoint. Returns the
alive root types. -/
partial def aliveRoots (O : Onto) : Array Nat := Id.run do
  let n := O.n
  let closed := (Array.range (bit n)).filter (isClosed O)
  let labels := (Array.range (bit O.nr)).filter fun L => L != 0 && upClosed O L
  -- child records keyed (s, Lchild→parent, t parent)
  let mut aliveC : HashMap (Nat × Nat × Nat) Bool := ∅
  for s in closed do
    for L in labels do
      for t in closed do
        if edgeOK O s L t then aliveC := aliveC.insert (s, L, t) true
  let mut aliveR : HashMap Nat Bool := closed.foldl (fun m t => m.insert t true) ∅
  -- support of a record: centre t, parent entry (L, s) or none
  let supp (aliveC : HashMap (Nat × Nat × Nat) Bool) (t : Nat) (par : Option (Nat × Nat)) : Bool := Id.run do
    let mut lows : Array (Nat × Nat × Int) := #[]
    let mut ups : Array (Nat × Nat × Int) := #[]
    for a in Array.range n do
      if has t a then
        for qi in O.lowBy[a]! do
          let (_, k, R, b) := O.low[qi]!
          let pc : Int := match par with
            | some (L, s) => if has L R && has s b then 1 else 0
            | none => 0
          if (k : Int) - pc > 0 then lows := lows.push (R, b, (k : Int) - pc)
        for ui in O.uppBy[a]! do
          let (_, k, S, e) := O.upp[ui]!
          let pc : Int := match par with
            | some (L, s) => if has L S && has s e then 1 else 0
            | none => 0
          if (k : Int) - pc < 0 then return false
          ups := ups.push (S, e, (k : Int) - pc)
    if lows.isEmpty then return true
    let mut sigs : HashSet (Array Nat × Array Nat) := ∅
    let mut entries : Array (Array Nat × Array Nat) := #[]
    for Lc in labels do
      let Lf := flipM O.nr Lc
      for s in closed do
        if aliveC.getD (s, Lf, t) false then
          let ls := (Array.range lows.size).filter fun j =>
            let (R, b, _) := lows[j]!; has Lc R && has s b
          if ls.isEmpty then continue
          let us := (Array.range ups.size).filter fun j =>
            let (S, e, _) := ups[j]!; has Lc S && has s e
          if !sigs.contains (ls, us) then
            sigs := sigs.insert (ls, us)
            entries := entries.push (ls, us)
    return search entries (lows.map (·.2.2)) (ups.map (·.2.2))
  let mut changed := true
  while changed do
    changed := false
    for (key, al) in aliveC.toArray do
      if al then
        let (s, L, t) := key
        if !supp aliveC s (some (L, t)) then
          aliveC := aliveC.insert key false
          changed := true
    for (t, al) in aliveR.toArray do
      if al && !supp aliveC t none then
        aliveR := aliveR.insert t false
        changed := true
  return (aliveR.toArray.filter (·.2)).map (·.1)

/-- Rows for the requested names, as `readout`. -/
def rows (O : Onto) (req : Array Nat) : Array (Nat × Option Ty) := Id.run do
  let roots := aliveRoots O
  req.map fun a =>
    let ts := roots.filter (has · a)
    if ts.isEmpty then (a, none)
    else (a, some (toTy O.n (ts.foldl (· &&& ·) ts[0]!)))

end SRIQFast.Brute
