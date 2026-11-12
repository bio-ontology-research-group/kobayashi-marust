import Lean.Data.Json
import ContextCalculus.OWL.Parse
import ContextCalculus.OWL.Names

/-!
# `km-owl-parse FILE`

Runs `ContextCalculus.OWL.parse` on an OWL 2 functional-syntax file and
prints one JSON object on stdout:

* `{"status":"ok","classes":[..],"objectProperties":[..],"axiomCounts":{..}}`
  with the sorted `Ontology.classNames` / `Ontology.objectPropertyNames` and
  the number of axioms per `Axiom` constructor, or
* `{"status":"rejected","reason":".."}`.

Read, parse and name times go to stderr. Exit code 0 for both answers, 2
when the file cannot be read as UTF-8 text.
-/

open Lean
open ContextCalculus.OWL

def axiomKind : Axiom → String
  | .subClassOf .. => "subClassOf"
  | .equivalentClasses _ => "equivalentClasses"
  | .disjointClasses _ => "disjointClasses"
  | .domain .. => "domain"
  | .range .. => "range"
  | .subObjectPropertyOf .. => "subObjectPropertyOf"
  | .equivalentObjectProperties _ => "equivalentObjectProperties"
  | .inverseObjectProperties .. => "inverseObjectProperties"
  | .transitive _ => "transitive"
  | .symmetric _ => "symmetric"
  | .declareClass _ => "declareClass"
  | .declareObjectProperty _ => "declareObjectProperty"

def kinds : List String :=
  ["subClassOf", "equivalentClasses", "disjointClasses", "domain", "range",
   "subObjectPropertyOf", "equivalentObjectProperties", "inverseObjectProperties",
   "transitive", "symmetric", "declareClass", "declareObjectProperty"]

def axiomCounts (O : Ontology) : Json :=
  let counts : Std.HashMap String Nat :=
    O.axioms.foldl (init := {}) fun m ax => m.insert (axiomKind ax) (m.getD (axiomKind ax) 0 + 1)
  Json.mkObj (kinds.map fun k => (k, toJson (counts.getD k 0)))

def sortedJson (names : List IRI) : Json :=
  Json.arr ((names.toArray.qsort (· < ·)).map Json.str)

def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
    let t0 ← IO.monoMsNow
    let text ← match ← (IO.FS.readFile path).toBaseIO with
      | .ok text => pure text
      | .error e =>
        IO.println (Json.mkObj [("status", "error"), ("reason", toString e)]).compress
        return 2
    let t1 ← IO.monoMsNow
    match parse text with
    | .error reason =>
      let t2 ← IO.monoMsNow
      IO.eprintln s!"read {t1 - t0} ms, parse {t2 - t1} ms"
      IO.println (Json.mkObj [("status", "rejected"), ("reason", reason)]).compress
      return 0
    | .ok O =>
      let t2 ← IO.monoMsNow
      let classes := O.classNames
      let roles := O.objectPropertyNames
      let out := Json.mkObj [("status", "ok"), ("classes", sortedJson classes),
        ("objectProperties", sortedJson roles), ("axiomCounts", axiomCounts O)]
      let t3 ← IO.monoMsNow
      IO.eprintln s!"read {t1 - t0} ms, parse {t2 - t1} ms, names {t3 - t2} ms"
      IO.println out.compress
      return 0
  | _ =>
    IO.eprintln "usage: km-owl-parse FILE.ofn"
    return 2
