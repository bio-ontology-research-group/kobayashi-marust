import ContextCalculus.OWLFrontend.DisjointUnion

/-!
# Normal-form dump for the hint producer (stage H1, untrusted tooling)

Prints the clauses `B` and nominal names `N` that `km-owl-reference
--procedure sroiq-c2a` checks a consistency hint against, using the same
functions as `owlC3Consistent`: `duOff`, `anonOff []`, the chain route
(`encC`) when its checks pass, else the Self route (`encS`), then
`reduceS` for each data part. Not part of any proved statement; the proved
checker stays the judge of every hint.

Run with `lean --run NFDump.lean FILE.ofn` and `LEAN_PATH` set to the
library build. Output, one directive per line:

```
route chain|self
n N            -- concept indices of B (encoding names included)
m M            -- role indices
cname I IRI    -- concept index of a class IRI or nominal class
rname I IRI
nominal I IRI  -- nominal class of a named individual
parts K
part J
nom I          -- a nominal name of part J
gci B1 ... | H1 ...
ex A R B       -- R is +k or -k
all A R B
ge A K R B
le A K R B
chain R1 ... | S
end
```
-/

open ContextCalculus ContextCalculus.OWLFrontend ContextCalculus.OWL
open ContextCalculus.OWL.Datatypes ContextCalculus.OWLFrontend.SHIQD ContextCalculus.OWLFrontend.SHOIQ

def showRT {m : Nat} : SRI.RoleT (Fin m) → String
  | .pos r => s!"+{r.val}" | .inv r => s!"-{r.val}"

def showL {n : Nat} (l : List (Fin n)) : String := " ".intercalate (l.map (toString ·.val))

def showCl {n m : Nat} : SRIQ.Clause (Fin n) (Fin m) → String
  | .gci b h => s!"gci {showL b} | {showL h}"
  | .exRight a R b => s!"ex {a.val} {showRT R} {b.val}"
  | .allRight a R b => s!"all {a.val} {showRT R} {b.val}"
  | .atLeast a k R b => s!"ge {a.val} {k} {showRT R} {b.val}"
  | .atMost a k R b => s!"le {a.val} {k} {showRT R} {b.val}"
  | .chain body S => s!"chain {" ".intercalate (body.map showRT)} | {showRT S}"

def emitNames (out : IO.FS.Stream) (T : SRIQDKBTranslation) (O : OWL.Ontology) : IO Unit := do
  let mut mp : Std.HashMap String Nat := {}
  for p in T.obj.cnames do
    out.putStrLn s!"cname {p.2} {p.1}"
    mp := mp.insert p.1 p.2
  for p in T.obj.rnames do out.putStrLn s!"rname {p.2} {p.1}"
  for (a, nm) in O.individualNames.zip (nomNames O []) do
    match mp[nm]? with
    | some i => out.putStrLn s!"nominal {i} {a}"
    | none => pure ()
  out.flush

def dumpParts {n m p q s : Nat} {K : Type} [DecidableEq K] (out : IO.FS.Stream)
    (D : SRIQN.DOntology (Fin n) (Fin m) (Fin p) (Fin q)) (cells : List K)
    (size : K → Option Nat) (sp : K → Bool) (E : Fin q → K → (Fin s → Bool) → Bool) :
    IO Unit := do
  let ps := SRIQD.partsOf size s (cells.filter sp)
  out.putStrLn s!"n {n + SRIQN.Proc.encKD D}"
  out.putStrLn s!"m {m}"
  out.putStrLn s!"parts {ps.length}"
  let mut j := 0
  for x in ps do
    let R := SRIQN.Proc.reduceS D (SRIQD.partCard cells size sp E (SRIQD.toPart s x))
    out.putStrLn s!"part {j}"
    for a in SRIQN.noms R do out.putStrLn s!"nom {a.val}"
    for cl in SRIQN.basePart R do out.putStrLn (showCl cl)
    out.flush
    j := j + 1
  out.putStrLn "end"

def main (args : List String) : IO UInt32 := do
  let out ← IO.getStdout
  let text ← IO.FS.readFile args[0]!
  match OWL.parse text with
  | .error e => out.putStrLn s!"error parse {e}"; return 1
  | .ok O0 =>
    let O := anonOff [] (duOff O0)
    -- the chain route (`owlSROIQDC2aConsistent`)
    if O.isSROIQDKB then
      match translateSHOIQD (roleOff O) [] with
      | some T =>
        match roleCls T O with
        | some E =>
          let L := nomNames (roleOff O) []
          if sroiqOK T L E then
            out.putStrLn "route chain"
            emitNames out T (roleOff O)
            let sp := spec T.tab
            let as := allBases sp
            let cs := cellsOf as
            dumpParts out (encC T L E) cs (cellSize as)
              (SRIQD.splitCell cs (cellSize as) (sroiqBound T L E) (owlE sp)) (owlE sp)
            return 0
        | none => pure ()
      | none => pure ()
    -- the Self route (`owlSelfCore`)
    if O.isSROIQDSKB && !(selfAxs O).isEmpty then
      match translateSHOIQD (roleOff (selfOff O)) [] with
      | some T =>
        match roleCls T (selfOff O), selfCls T O with
        | some E, some SC =>
          let L := nomNames (roleOff (selfOff O)) []
          if sroiqSOK T L E SC then
            out.putStrLn "route self"
            emitNames out T (roleOff (selfOff O))
            let sp := spec T.tab
            let as := allBases sp
            let cs := cellsOf as
            dumpParts out (encS T L E SC) cs (cellSize as)
              (SRIQD.splitCell cs (cellSize as) (sroiqSBound T L E SC) (owlE sp)) (owlE sp)
            return 0
        | _, _ => pure ()
      | none => pure ()
    out.putStrLn "error declined"
    return 3
