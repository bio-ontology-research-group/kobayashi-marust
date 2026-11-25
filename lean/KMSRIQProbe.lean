import ContextCalculus.OWL.Parse
import ContextCalculus.OWLFrontend.ReferenceReadout

/-! Development probe: time the v1.7.0 SHIQ route (`owlSHIQReference`) on
one file. `km-sriq-probe <file.ofn>` prints the sizes of the translation,
the phase times, and the rows; exit `0` when the route publishes, `3` when
it declines (reason on stderr). With `KM_SRIQ_PROBE_ROWS=1` it also prints
every row on stdout as `row <sub IRI> unsat|<sup IRIs separated by spaces>`.
With `KM_SRIQ_PROBE_CLASSES=1` it requests the class IRIs alone, without
the two probe IRIs of `km-owl-reference` (two concept indices fewer). -/

open ContextCalculus ContextCalculus.OWLFrontend

/-- The number of counting clauses of a translation. -/
def countClauses {n m : Nat} (O : SRIQ.Ontology (Fin n) (Fin m)) : Nat :=
  O.foldl (fun acc cl => match cl with
    | .atLeast .. | .atMost .. => acc + 1
    | _ => acc) 0

def main (args : List String) : IO UInt32 := do
  let some path := args.head? | IO.eprintln "usage: km-sriq-probe <file>"; return 2
  let t0 ← IO.monoMsNow
  let text ← IO.FS.readFile path
  match OWL.parse text with
  | .error e => IO.eprintln s!"declined: parse: {e}"; return 3
  | .ok O =>
    let t1 ← IO.monoMsNow
    let req := if (← IO.getEnv "KM_SRIQ_PROBE_CLASSES") == some "1" then O.classNames
      else probeRequest O
    match ← IO.lazyPure fun _ => translateSRIQ O req with
    | none =>
      let first := match O.axioms.find? (fun ax => !ax.isSHIQ) with
        | some ax => ((reprStr ax).take 120).toString
        | none => "every axiom passes alone"
      IO.eprintln s!"declined: not SHIQ: first: {first}"
      return 3
    | some T =>
      let t2 ← IO.monoMsNow
      let ok := isSHIQB T.ontology
      IO.eprintln s!"named={T.named.length} concepts={T.conceptCount} roles={T.roleCount} clauses={T.ontology.length} counting={countClauses T.ontology} shiq={ok} parse_ms={t1-t0} translate_ms={t2-t1}"
      if !ok then
        IO.eprintln "declined: non-simple role in a number restriction or functionality axiom"
        return 3
      let t3 ← IO.monoMsNow
      let E ← IO.lazyPure fun _ => SRIQ.Proc.encTransQ T.ontology
      let t4 ← IO.monoMsNow
      IO.eprintln s!"fresh={E.1} enc_clauses={E.2.length} names={T.conceptCount + E.1} enc_ms={t4-t3}"
      let cls ← IO.lazyPure fun _ => QProc.classifyQO E.2 (sriqRequest T E.1)
      let t5 ← IO.monoMsNow
      let rows := sriqRows T cls
      let total := rows.foldl (fun s r => s + r.sups.length) 0
      let unsat := rows.foldl (fun s r => if r.unsat then s + 1 else s) 0
      IO.println s!"rows={rows.length} sups={total} unsat={unsat} classify_ms={t5-t4}"
      if (← IO.getEnv "KM_SRIQ_PROBE_ROWS") == some "1" then
        let names := T.named.toArray
        for r in rows do
          let sub := names[r.sub]?.getD "?"
          if r.unsat then IO.println s!"row {sub} unsat"
          else IO.println s!"row {sub} {String.intercalate " " (r.sups.map fun j => names[j]?.getD "?")}"
      return 0
