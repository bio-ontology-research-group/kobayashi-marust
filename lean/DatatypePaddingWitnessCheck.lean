import Lean
import ContextCalculus.DatatypePaddingCheck

/-! Diagnostic checker of ALL source GCIs in a Rust TInput document, for a
supplied edgeless padding valuation. It reads the original source_axioms array,
not a certificate-selected subset. This is NOT an ontology admission checker.
In particular, nominal/self lowering below preserves only padding truth, and
does not establish object-side class transport. The caller must reject duplicate
JSON keys before Lean's map-based JSON parser can erase them. -/

open Lean
open ContextCalculus.DatatypeClassTransport (Expr)
open ContextCalculus.DatatypePadding (checkPadding)

private abbrev PaddingExpr := Expr String Unit Bool

private def exactFields (json : Json) (names : List String) : Except String Unit := do
  let fields ← json.getObj?
  let keys := fields.toList.map Prod.fst
  unless keys.length == names.length && keys.all names.contains do
    throw s!"unexpected fields; expected {names}"

private def singleton (json : Json) : Except String (String × Json) := do
  let fields ← json.getObj?
  match fields.toList with
  | [pair] => return pair
  | _ => throw "expected exactly one constructor"

private def ordinaryRole (json : Json) : Except String Unit := do
  let (kind, name) ← singleton json
  unless kind == "Name" || kind == "Inverse" do
    throw "padding requires an ordinary named or inverse role"
  let _ ← name.getStr?

private def tuple (json : Json) (size : Nat) : Except String (Array Json) := do
  let items ← json.getArr?
  unless items.size == size do throw s!"expected {size} constructor arguments"
  return items

/-- Fuel makes malformed/deep documents fail closed. Fillers are fully parsed
even though their truth cannot affect an edgeless padding node. -/
private def decodeExpr : Nat → Bool → Json → Except String PaddingExpr
  | 0, _, _ => .error "source expression nesting limit exceeded"
  | fuel + 1, inFiller, json => do
    match json with
    | .str "Top" => return .dataAtom true
    | .str "Bottom" => return .dataAtom false
    | _ => pure ()
    let (kind, value) ← singleton json
    match kind with
    | "Name" =>
        let name ← value.getStr?
        if name.startsWith "__dt__" && !inFiller then
          throw "direct datatype predicate has no checked padding interpretation"
        return .atom name
    | "Nominal" =>
        let _ ← value.getStr?
        return .dataAtom false
    | "Not" => return .neg (← decodeExpr fuel inFiller value)
    | "And" | "Or" =>
        let items ← value.getArr?
        let decoded ← items.toList.mapM (decodeExpr fuel inFiller)
        if kind == "And" then
          return decoded.foldr Expr.conj (.dataAtom true)
        else
          return decoded.foldr Expr.disj (.dataAtom false)
    | "Exists" | "Forall" =>
        let args ← tuple value 2
        ordinaryRole args[0]!
        let filler ← decodeExpr fuel true args[1]!
        if kind == "Exists" then return .some () filler else return .all () filler
    | "AtLeast" | "AtMost" =>
        let args ← tuple value 3
        let n ← args[0]!.getNat?
        ordinaryRole args[1]!
        let filler ← decodeExpr fuel true args[2]!
        if kind == "AtLeast" then return .min () n filler else return .max () n filler
    | "HasSelf" =>
        ordinaryRole value
        return .some () (.dataAtom true)
    | _ => throw s!"unknown source constructor: {kind}"

private def decodeAxiom (json : Json) :
    Except String (List (PaddingExpr × PaddingExpr)) := do
  exactFields json ["kind", "left", "right"]
  let kind ← (← json.getObjVal? "kind").getStr?
  let left ← decodeExpr 512 false (← json.getObjVal? "left")
  let right ← decodeExpr 512 false (← json.getObjVal? "right")
  match kind with
  | "sub-class" => return [(left, right)]
  | "equivalent" => return [(left, right), (right, left)]
  | "disjoint" => return [(.conj left right, .dataAtom false)]
  | _ => throw s!"unknown source axiom kind: {kind}"

private def checkDocument (source witness : Json) : Except String (Nat × Nat) := do
  exactFields witness ["positive_classes"]
  let positive ← (← (← witness.getObjVal? "positive_classes").getArr?).toList.mapM Json.getStr?
  unless positive.eraseDups.length == positive.length do throw "duplicate witness class"
  let vocabulary ← (← (← source.getObjVal? "concepts").getArr?).toList.mapM Json.getStr?
  unless positive.all (fun name => vocabulary.contains name && !name.startsWith "__dt__") do
    throw "witness class is undeclared or a datatype"
  let sourceAxioms ← (← source.getObjVal? "source_axioms").getArr?
  -- Traverse the complete array; no axiom IDs or subset selection is accepted.
  let expanded ← sourceAxioms.toList.mapM decodeAxiom
  let axioms := expanded.flatten
  unless checkPadding positive.contains id axioms do
    throw "padding valuation violates a source axiom"
  return (sourceAxioms.size, axioms.length)

def main (args : List String) : IO UInt32 := do
  match args with
  | [sourcePath, witnessPath] =>
      try
        let sourceText ← IO.FS.readFile sourcePath
        let witnessText ← IO.FS.readFile witnessPath
        let result := do
          let source ← Json.parse sourceText
          let witness ← Json.parse witnessText
          checkDocument source witness
        match result with
        | .ok (count, expanded) =>
            IO.println s!"Padding GCI obligation accepted: {count} source axioms, {expanded} implications"
            return 0
        | .error message =>
            IO.eprintln s!"Padding GCI obligation rejected: {message}"
            return 1
      catch error =>
        IO.eprintln s!"Padding GCI input error: {error}"
        return 2
  | _ =>
      IO.eprintln "usage: DatatypePaddingWitnessCheck SOURCE-TINPUT.json WITNESS.json"
      return 2
