import ContextCalculus.OWL.Parse
import ContextCalculus.OWLFrontend.SRIQDComplete
import ContextCalculus.OWLFrontend.ReferenceReadout

/-! Development probe for the v1.7.0 stage C4 SHIQ(D) route
(`owlSHIQDReference`). `km-sriqd-probe <file.ofn>` requests the class IRIs
of the ontology and the probe `urn:km:owl-reference:probe-b` (without
the probe `probe-a` of `km-owl-reference`, one concept index fewer),
prints the sizes of the translation on stderr and one line per class on
stdout: `row <class IRI> unsat` when the class is below the fresh probe,
else `row <class IRI> <class superclass IRIs>`. Exit `0` when the route publishes,
`3` when it declines (reason on stderr). The rows are exact under
`owlSHIQDReference_sound` (entailment at the OWL 2 datatype map). -/

open ContextCalculus ContextCalculus.OWLFrontend

/-- The number of parts if every small cell were split (for comparison). -/
def allSmallParts (T : SRIQDTranslation) : Nat :=
  let sp := SHIQD.spec T.tab
  let as := OWL.Datatypes.allBases sp
  (SRIQD.partsOf (OWL.Datatypes.cellSize as) (OWL.Datatypes.allFrees sp).length
    ((OWL.Datatypes.cellsOf as).filter fun c =>
      SRIQD.small (OWL.Datatypes.cellSize as) (partBound T) c)).length

def main (args : List String) : IO UInt32 := do
  let some path := args.head? | IO.eprintln "usage: km-sriqd-probe <file>"; return 2
  let text ← IO.FS.readFile path
  match OWL.parse text with
  | .error e => IO.eprintln s!"declined: parse: {e}"; return 3
  | .ok O =>
    let req := O.classNames ++ [probeB]
    match translateSRIQD O req with
    | none =>
      IO.eprintln s!"declined: not SHIQ(D)"
      return 3
    | some T =>
      IO.eprintln s!"named={T.named.length} concepts={T.obj.conceptCount} roles={T.obj.roleCount} dprops={T.dps.length} atoms={T.tab.length} clauses={T.ontology.length} supported={allSupported T} parts={(partAlive T).length} parts_without_cover={allSmallParts T}"
      let t0 ← IO.monoMsNow
      match ← IO.lazyPure fun _ => owlSHIQDReference O req with
      | none =>
        IO.eprintln "declined: simple-role check or data atoms outside the supported sub-theory"
        return 3
      | some a =>
        let t1 ← IO.monoMsNow
        IO.eprintln s!"classify_ms={t1 - t0}"
        let names := a.named.toArray
        let nc := O.classNames.length
        for i in List.range nc do
          let sub := names[i]?.getD "?"
          if a.bit i nc then IO.println s!"row {sub} unsat"
          else
            let sups := (List.range nc).filter fun j => a.bit i j
            IO.println s!"row {sub} {String.intercalate " " (sups.map fun j => names[j]?.getD "?")}"
        return 0
