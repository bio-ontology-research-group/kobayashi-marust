import ContextCalculus.OWLFrontend.DisjointUnion

/-!
# Hint diagnosis (stage H1, untrusted tooling)

`lean --run HintDiag.lean FILE.ofn HINT` evaluates the parts of
`checkRealisationN` with a certificate (`CertOK`) on the normal form of the
chain route of `sroiq-c2a` (part 0), and prints the first failing part. It
never computes the alive records, so it does not run out of memory where
the checker falls back to the elimination. Not part of any proved
statement.
-/

open ContextCalculus ContextCalculus.OWLFrontend ContextCalculus.OWL
open ContextCalculus.OWL.Datatypes ContextCalculus.OWLFrontend.SHIQD ContextCalculus.OWLFrontend.SHOIQ

def diag {n m : Nat} (out : IO.FS.Stream) (B : SRIQ.Ontology (Fin n) (Fin m)) (N : List (Fin n))
    (raw : RawHint) (sel : String := "all") : IO Unit := do
  match raw.toHintN n m with
  | none => out.putStrLn "hint does not convert (an index out of range)"
  | some h =>
    out.putStrLn s!"k {h.k} recs {h.recs.length}"; out.flush
    if sel == "symm" then
      out.putStrLn s!"symm {decide (∀ b c, h.lab c b = SRIQ.flipL (h.lab b c))}"; out.flush; return
    if sel == "nomok" then
      out.putStrLn s!"nomOK {decide (SRIQN.NomOK N h.ty)}"; out.flush; return
    if sel == "star" then
      for b in List.finRange h.k do
        out.putStrLn s!"core {b.val} {SRIQ.Proc.starOKB B (h.ty b) (SRIQ.Proc.nbrsL h.ty h.lab b ++ h.kids b)}"; out.flush
      return
    out.putStrLn s!"noms {N.length} distinct {N.eraseDups.length}"; out.flush
    for a in N do
      let c := (List.finRange h.k).filter fun b => decide (a ∈ h.ty b)
      if c.length != 1 then out.putStrLn s!"nominal {a.val} in {c.length} core types"
    if sel == "cert" then
      let G := h.recs.map Prod.fst
      for b in List.finRange h.k do
        for e in h.kids b do
          if !decide (SRIQN.Proc.MemL G (SRIQN.anchorRec b e)) then
            out.putStrLn s!"anchor record missing for a kid of core {b.val}"
      out.putStrLn "anchors done"; out.flush
      let mut i := 0
      for e in h.recs do
        let c1 := decide (∀ a ∈ N, a ∉ e.1.1)
        let c2 := decide (SRIQN.Proc.ceOK B h.ty e.1 e.2.1)
        let c3 := SRIQ.Proc.starOKB B e.1.1 ((SRIQN.parentE h.ty e.1.2 :: SRIQN.Proc.cEntriesL h.ty e.2.1) ++ e.2.2)
        let c4 := decide (∀ x ∈ e.2.2, SRIQN.Proc.MemL G (SRIQN.childRecN e.1.1 x))
        out.putStrLn s!"rec {i}: noNom {c1} ceOK {c2} star {c3} kids {c4}"; out.flush
        i := i + 1
      return
    out.flush
    out.putStrLn s!"symm {decide (∀ b c, h.lab c b = SRIQ.flipL (h.lab b c))}"; out.flush
    out.putStrLn s!"nomOK {decide (SRIQN.NomOK N h.ty)}"; out.flush
    for b in List.finRange h.k do
      let ok := SRIQ.Proc.starOKB B (h.ty b) (SRIQ.Proc.nbrsL h.ty h.lab b ++ h.kids b)
      if !ok then out.putStrLn s!"core star fails at {b.val}"
      out.putStrLn s!"core {b.val} done"; out.flush
    let G := h.recs.map Prod.fst
    for b in List.finRange h.k do
      for e in h.kids b do
        if !decide (SRIQN.Proc.MemL G (SRIQN.anchorRec b e)) then
          out.putStrLn s!"anchor record missing for a kid of core {b.val}"
    let mut i := 0
    for e in h.recs do
      let c1 := decide (∀ a ∈ N, a ∉ e.1.1)
      let c2 := decide (SRIQN.Proc.ceOK B h.ty e.1 e.2.1)
      let c3 := SRIQ.Proc.starOKB B e.1.1 ((SRIQN.parentE h.ty e.1.2 :: SRIQN.Proc.cEntriesL h.ty e.2.1) ++ e.2.2)
      let c4 := decide (∀ x ∈ e.2.2, SRIQN.Proc.MemL G (SRIQN.childRecN e.1.1 x))
      if !(c1 && c2 && c3 && c4) then
        out.putStrLn s!"rec {i}: noNom {c1} ceOK {c2} star {c3} kids {c4}"
      out.flush
      i := i + 1
    if sel == "all" then
      out.putStrLn s!"certOK {decide (SRIQN.Proc.CertOK B N h)}"
  out.flush

def diagParts {n m p q s : Nat} {K : Type} [DecidableEq K] (out : IO.FS.Stream)
    (D : SRIQN.DOntology (Fin n) (Fin m) (Fin p) (Fin q)) (cells : List K)
    (size : K → Option Nat) (sp : K → Bool) (E : Fin q → K → (Fin s → Bool) → Bool)
    (raw : RawHint) (sel : String) : IO Unit := do
  let ps := SRIQD.partsOf size s (cells.filter sp)
  out.putStrLn s!"parts {ps.length}"; out.flush
  for x in ps.take 1 do
    let R := SRIQN.Proc.reduceS D (SRIQD.partCard cells size sp E (SRIQD.toPart s x))
    let B := SRIQN.basePart R
    let N := SRIQN.noms R
    out.putStrLn s!"clauses {B.length} noms {N.length}"; out.flush
    diag out B N raw sel

def main (args : List String) : IO UInt32 := do
  let out ← IO.getStdout
  let text ← IO.FS.readFile args[0]!
  let htext ← IO.FS.readFile args[1]!
  let raw ← match RawHint.parseHint htext with
    | .ok h => pure h
    | .error e => do out.putStrLn s!"bad hint {e}"; return 2
  match OWL.parse text with
  | .error e => out.putStrLn s!"error parse {e}"; return 1
  | .ok O0 =>
    let O := anonOff [] (duOff O0)
    match translateSHOIQD (roleOff O) [] with
    | some T =>
      match roleCls T O with
      | some E =>
        let L := nomNames (roleOff O) []
        let sp := spec T.tab
        let as := allBases sp
        let cs := cellsOf as
        diagParts out (encC T L E) cs (cellSize as)
          (SRIQD.splitCell cs (cellSize as) (sroiqBound T L E) (owlE sp)) (owlE sp) raw (args.getD 2 "all")
        return 0
      | none => out.putStrLn "no roles"; return 3
    | none => out.putStrLn "no translation"; return 3
