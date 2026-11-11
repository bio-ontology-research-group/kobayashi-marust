import ContextCalculus.ELCommonSourceRecognizer
/-! Temporary diagnostic (v161-sparse, not committed): which recogniser
function recurses non-tail on a long list. Usage: `<fn> <n>`. -/
open ContextCalculus ContextCalculus.CheckerTerm ELCommonSourceRecognizer

def nf1Clause : FCL :=
  { body := [FLit.P (FPred.concept 1 (FTerm.var 0))]
    head := [FLit.P (FPred.concept 2 (FTerm.var 0))] }

def main (args : List String) : IO UInt32 := do
  match args with
  | [fn, nStr] =>
    let n := nStr.toNat!
    let r : Nat ← match fn with
      | "maxNatList" => pure (maxNatList (List.replicate n 1))
      | "parseSource" => pure ((parseSource (List.replicate n nf1Clause)).map List.length |>.getD 0)
      | "compileDirect" => pure (compileDirect 0 1 false 5 (List.replicate n (.nf1 2 3))).length
      | "collectRoleHalves" => pure (collectRoleHalves (List.replicate n (.nf3Role 2 3 4))).length
      | "itemsConcepts" => pure (itemsConcepts (List.replicate n (.nf1 2 3))).length
      | "sortHalves" => pure (sortHalves ((List.range n).map fun i => (i, 1, 2))).length
      | "zipSortedHalves" => pure (zipSortedHalves (List.replicate n (1, 2, 3)) (List.replicate n (1, 2, 3))).length
      | "recognizeEL" => pure ((recognizeEL [1, 2] (List.replicate n nf1Clause)).map (·.ontology.length) |>.getD 0)
      | _ => pure 0
    IO.println s!"{fn} {n} ok {r}"
    return 0
  | _ => return 2
