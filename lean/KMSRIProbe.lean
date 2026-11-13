import ContextCalculus.OWL.Parse
import ContextCalculus.OWLFrontend.SRIReference
import ContextCalculus.OWLFrontend.ReferenceReadout

/-! Development probe: time the v1.6.3 SHI route on one file.
`km-sri-probe <file.ofn>` prints names, rows, and phase times. -/

open ContextCalculus ContextCalculus.OWLFrontend

def main (args : List String) : IO UInt32 := do
  let some path := args.head? | IO.eprintln "usage: km-sri-probe <file>"; return 2
  let t0 ← IO.monoMsNow
  let text ← IO.FS.readFile path
  match OWL.parse text with
  | .error e => IO.eprintln s!"parse: {e}"; return 3
  | .ok O =>
    let t1 ← IO.monoMsNow
    let req := probeRequest O
    match translateSRI O req with
    | none => IO.eprintln "not SRI"; return 3
    | some T =>
      let t2 ← IO.monoMsNow
      let gl := T.ontology.foldl (fun (acc : Nat × Nat) cl => match cl with
        | .gci [] h => if h.length ≥ 2 then (acc.1 + 1, acc.2) else acc
        | .gci _ h => if h.length ≥ 2 then (acc.1, acc.2 + 1) else acc
        | _ => acc) (0, 0)
      IO.eprintln s!"global_disj={gl.1} local_disj={gl.2}"
      IO.eprintln s!"named={T.named.length} concepts={T.conceptCount} roles={T.roleCount} clauses={T.ontology.length} shi={isSHIB T.ontology} parse_ms={t1-t0} translate_ms={t2-t1}"
      if (← IO.getEnv "KM_SRI_COUNT") == some "1" then
        let E := ContextCalculus.SRI.Proc.encTrans T.ontology
        let ix := ContextCalculus.SRI.Proc.mkIx E.2
        let tc0 ← IO.monoMsNow
        let c := ContextCalculus.SRI.Proc.candidates E.2 ix (sriRequest T E.1)
        IO.eprintln s!"candidates={c.length} cand_ms={(← IO.monoMsNow) - tc0}"
        let te0 ← IO.monoMsNow
        let al := ContextCalculus.SRI.Proc.elimF ix c
        IO.eprintln s!"alive={al.length} elim_ms={(← IO.monoMsNow) - te0}"
        let tr0 ← IO.monoMsNow
        let arr := al.toArray
        let hs : Array (Std.HashSet (Fin (T.conceptCount + E.1))) := arr.map fun r => Std.HashSet.ofList (ContextCalculus.SRI.Proc.toL r.t)
        let idx := ContextCalculus.SRI.Proc.Idx.ofList ((List.range arr.size).flatMap fun i => (ContextCalculus.SRI.Proc.toL (arr.getD i ⟨∅, ∅, ∅⟩).t).map fun b => (b, i))
        let rows := (sriRequest T E.1).map fun a =>
          match idx.getD a [] with
          | [] => 0
          | i :: rest => (rest.foldl (fun cur j => cur.filter (hs[j]!.contains ·)) (ContextCalculus.SRI.Proc.toL (arr.getD i ⟨∅, ∅, ∅⟩).t)).length
        IO.eprintln s!"fast_readout_sups={rows.foldl (· + ·) 0} readout_ms={(← IO.monoMsNow) - tr0}"
        let tsz := c.foldl (fun acc r => max acc r.t.card) 0
        IO.eprintln s!"max_type={tsz}"
        let ks := (c.map fun r => ContextCalculus.SRI.Proc.toL r.K).eraseDups
        let as := c.foldl (fun acc r => max acc (ContextCalculus.SRI.Proc.toL r.A).length) 0
        IO.eprintln s!"records={c.length} contexts={ks.length} max_aug={as} fresh={E.1}"
      match owlSRIReference O req with
      | none => IO.eprintln "declined (chains)"; return 3
      | some a =>
        let total := a.rows.foldl (fun s r => s + r.sups.length) 0
        let t3 ← IO.monoMsNow
        IO.println s!"rows={a.rows.length} sups={total} classify_ms={t3-t2}"
        return 0
