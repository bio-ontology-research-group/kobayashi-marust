import ContextCalculus.ALCCommonSourceRecognizer
import ContextCalculus.SparseTaxonomy
/-! Stack diagnostic for v161-stack (lives in `results/agents/2026-11-12/v161-stack/tools`;
built only temporarily).  Usage: `km-stack-diag <fn> <n>`.  Runs one recogniser,
saturation or readout function on a synthetic input of `n` items and prints a
small summary.  Run with `LEAN_STACK_SIZE_KB=262144` (the size KM passes). -/
open ContextCalculus ContextCalculus.CheckerTerm ELCommonSourceRecognizer

def cv (c : Nat) (x : Int := 0) : FLit := .P (.concept c (.var x))
def rv (r : Nat) (x y : Int) : FLit := .P (.role r (.var x) (.var y))

/-- One synthetic EL clause of every recognised shape (ten-cycle).  The
closure of the whole stream stays linear in its size. -/
def synthClause (i : Nat) : FCL :=
  let a := 3 * i
  match i % 10 with
  | 0 => ⟨[cv a], [cv (a + 1)]⟩
  | 1 => ⟨[cv a, cv (a + 1)], [cv (a + 2)]⟩
  | 2 => ⟨[cv a, cv (a + 1), cv (a + 2), cv (a + 3)], [cv (a + 4)]⟩
  | 3 => ⟨[cv a], [.P (.role 1 (.var 0) (.app i (.var 0)))]⟩
  | 4 => ⟨[cv (a - 3)], [.P (.concept (a + 1) (.app (i - 1) (.var 0)))]⟩
  | 5 => ⟨[rv 1 0 (-1), cv a (-1)], [cv (a + 1)]⟩
  | 6 => ⟨[rv (10 + i) 0 (-1)], [rv (11 + i) 0 (-1)]⟩
  | 7 => ⟨[rv 1 0 (-1), rv 2 (-1) (-2)], [rv 3 0 (-2)]⟩
  | 8 => ⟨[cv a], []⟩
  | _ => ⟨[cv a, cv (a + 1)], []⟩

def synthSource (n : Nat) : List FCL := (List.range n).map synthClause

def synthNamed (n : Nat) : List Nat :=
  ((List.range n).filter (· % 10 == 0)).map (3 * ·)

def synthItems (n : Nat) : List ParsedItem :=
  (List.range n).map fun i =>
    match i % 4 with
    | 0 => .nf1 (3 * i) (3 * i + 1)
    | 1 => .nf3Role (3 * i) 1 i
    | 2 => .naryConj (3 * i) 1 2 [4, 5] 6
    | _ => .nf3Filler (3 * i) 7 (i - 2)

def perm (n : Nat) : List (Nat × Nat × Nat) :=
  (List.range n).map fun i => ((i * 7919) % (n + 1), i, 2)

def main (args : List String) : IO UInt32 := do
  match args with
  | [fn, nStr] =>
    let n := nStr.toNat!
    let r : String ← match fn with
      | "maxNatList" => pure (toString (maxNatList (List.range n)))
      | "parseSource" =>
        pure (toString ((parseSource (synthSource n)).map List.length |>.getD 0))
      | "compileDirect" =>
        pure (toString (compileDirect 0 1 false 5 (synthItems n)).length)
      | "collectRoleHalves" =>
        pure (toString (collectRoleHalves (List.replicate n (.nf3Role 2 3 4))).length)
      | "collectFillerHalves" =>
        pure (toString (collectFillerHalves (List.replicate n (.nf3Filler 2 3 4))).length)
      | "itemsConcepts" => pure (toString (itemsConcepts (synthItems n)).length)
      | "sortHalves" => pure (toString ((sortHalves (perm n)).headD (0, 0, 0)).1)
      | "mergeHalves" =>
        pure (toString (mergeHalves ((List.range n).map fun i => (2 * i, 0, 0))
          ((List.range n).map fun i => (2 * i + 1, 0, 0))).length)
      | "zipSortedHalves" =>
        pure (toString (zipSortedHalves (List.replicate n (1, 2, 3)) (List.replicate n (1, 2, 3))).length)
      | "buildNF3Clauses" =>
        let hs := (List.range n).map fun i => (n - i, i, 2)
        pure (toString ((buildNF3Clauses hs hs).map List.length |>.getD 0))
      | "recognizeEL" =>
        pure (toString ((recognizeEL (synthNamed n) (synthSource n)).map (·.ontology.length) |>.getD 0))
      | "sparseEL" =>
        let src : KMConcreteWorkerAdapters.RequestedTaxonomySource :=
          { ontology := synthSource n, named := synthNamed n }
        match SparseTaxonomy.sparseElReference src with
        | some t => pure s!"rows={t.rows.length} sups={t.rows.foldl (fun acc r => acc + r.sups.length) 0} unsat={(t.rows.filter (·.unsat)).length}"
        | none => pure "declined"
      | "alcListMax" => pure (toString (ALCCommonSourceRecognizer.listMax (List.range n)))
      | "alcAssignFnNames" =>
        pure (toString (ALCCommonSourceRecognizer.assignFnNames 5 (List.replicate n none) 0).length)
      | "alcClassify" =>
        let src := (List.range n).map fun i => (⟨[cv (i % 8)], [cv (8 + i % 8)]⟩ : FCL)
        pure (toString (src.mapM ALCCommonSourceRecognizer.classifyClause |>.map List.length |>.getD 0))
      | "alcSourceConcepts" =>
        pure (toString (ALCCommonSourceRecognizer.sourceConcepts (synthSource n)).length)
      | "alcBuildIndexed" =>
        let items := List.replicate n (ALCCommonSourceRecognizer.RawClauseItem.gci [1] [2])
        pure (toString ((ALCCommonSourceRecognizer.buildIndexedClauses [1, 2] [] [] items).map List.length |>.getD 0))
      | "alcRecognize" =>
        -- 16 concepts, n gci clauses: the shape that passes the binary's ALC budget.
        let src := (List.range n).map fun i => (⟨[cv (i % 8)], [cv (8 + i % 8)]⟩ : FCL)
        pure (toString ((ALCCommonSourceRecognizer.recognizeALC [0] src).map (·.conceptCount) |>.getD 0))
      | _ => pure "unknown"
    IO.println s!"{fn} {n} ok {r}"
    return 0
  | _ => return 2
