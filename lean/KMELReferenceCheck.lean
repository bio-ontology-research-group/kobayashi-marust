import Lean.Data.Json
import Std.Data.HashMap
import ContextCalculus.KMConcreteWorkerAdapters

open Lean
open ContextCalculus
open ContextCalculus.CheckerTerm
open ContextCalculus.CertifiedRouting
open ContextCalculus.KMCommonRoutingSource
open ContextCalculus.KMConcreteWorkerAdapters
open ELCommonSourceRecognizer

namespace KMELReferenceCheck

structure Interner where
  toId : Std.HashMap String Nat := {}
  names : Array String := #[]

def Interner.intern (it : Interner) (name : String) : Nat × Interner :=
  match it.toId[name]? with
  | some id => (id, it)
  | none =>
    let id := it.names.size
    (id, { toId := it.toId.insert name id, names := it.names.push name })

private def objField (json : Json) (name : String) : Except String Json :=
  json.getObjVal? name

private def strField (json : Json) (name : String) : Except String String := do
  (← objField json name).getStr?

private def natField (json : Json) (name : String) : Except String Nat := do
  (← objField json name).getNat?

private def arrField (json : Json) (name : String) : Except String (Array Json) := do
  (← objField json name).getArr?

partial def parseTerm
    (json : Json)
    (vars : Std.HashMap String Int)
    (fns consts : Interner) :
    Except String (FTerm × Std.HashMap String Int × Interner × Interner) := do
  let kind ← strField json "kind"
  if kind == "var" then
    let name ← strField json "name"
    if name == "x" then
      pure (FTerm.var 0, vars, fns, consts)
    else if name == "y" then
      pure (FTerm.var (-1), vars, fns, consts)
    else
      match vars[name]? with
      | some v => pure (FTerm.var v, vars, fns, consts)
      | none =>
        let v : Int := -(Int.ofNat (vars.size + 2))
        pure (FTerm.var v, vars.insert name v, fns, consts)
  else if kind == "fun" then
    let fnName ← strField json "function"
    let argJson ← objField json "arg"
    let (fid, fns) := fns.intern fnName
    let (argTerm, vars, fns, consts) ← parseTerm argJson vars fns consts
    pure (FTerm.app fid argTerm, vars, fns, consts)
  else if kind == "ind" then
    let indName ← strField json "name"
    let (cid, consts) := consts.intern ("ind:" ++ indName)
    pure (FTerm.const cid, vars, fns, consts)
  else if kind == "aux" then
    let auxId ← natField json "id"
    let (cid, consts) := consts.intern ("aux:" ++ toString auxId)
    pure (FTerm.const cid, vars, fns, consts)
  else
    throw s!"unsupported JTerm kind: {kind}"

def parseClause
    (json : Json)
    (concepts roles fns consts : Interner) :
    Except String (FCL × Interner × Interner × Interner × Interner) := do
  let bodyArr ← arrField json "body"
  let headArr ← arrField json "head"
  let mut vars : Std.HashMap String Int := {}
  let mut concepts := concepts
  let mut roles := roles
  let mut fns := fns
  let mut consts := consts
  let mut bodyLits : Array FLit := #[]
  let mut bodyIneqs : Array FLit := #[]
  for atomJson in bodyArr do
    let kind ← strField atomJson "kind"
    if kind == "concept" then
      let cName ← strField atomJson "concept"
      let tJson ← objField atomJson "term"
      let (cid, concepts') := concepts.intern cName
      concepts := concepts'
      let (t, vars', fns', consts') ← parseTerm tJson vars fns consts
      vars := vars'
      fns := fns'
      consts := consts'
      bodyLits := bodyLits.push (FLit.P (FPred.concept cid t))
    else if kind == "role" then
      let rName ← strField atomJson "role"
      let sJson ← objField atomJson "source"
      let tJson ← objField atomJson "target"
      let (rid, roles') := roles.intern rName
      roles := roles'
      let (s, vars', fns', consts') ← parseTerm sJson vars fns consts
      let (t, vars'', fns'', consts'') ← parseTerm tJson vars' fns' consts'
      vars := vars''
      fns := fns''
      consts := consts''
      bodyLits := bodyLits.push (FLit.P (FPred.role rid s t))
    else if kind == "eq" then
      let lJson ← objField atomJson "left"
      let rJson ← objField atomJson "right"
      let (l, vars', fns', consts') ← parseTerm lJson vars fns consts
      let (r, vars'', fns'', consts'') ← parseTerm rJson vars' fns' consts'
      vars := vars''
      fns := fns''
      consts := consts''
      bodyIneqs := bodyIneqs.push (FLit.ineq l r)
    else
      throw s!"unsupported body JAtom kind: {kind}"
  let mut headLits : Array FLit := #[]
  for atomJson in headArr do
    let kind ← strField atomJson "kind"
    if kind == "concept" then
      let cName ← strField atomJson "concept"
      let tJson ← objField atomJson "term"
      let (cid, concepts') := concepts.intern cName
      concepts := concepts'
      let (t, vars', fns', consts') ← parseTerm tJson vars fns consts
      vars := vars'
      fns := fns'
      consts := consts'
      headLits := headLits.push (FLit.P (FPred.concept cid t))
    else if kind == "role" then
      let rName ← strField atomJson "role"
      let sJson ← objField atomJson "source"
      let tJson ← objField atomJson "target"
      let (rid, roles') := roles.intern rName
      roles := roles'
      let (s, vars', fns', consts') ← parseTerm sJson vars fns consts
      let (t, vars'', fns'', consts'') ← parseTerm tJson vars' fns' consts'
      vars := vars''
      fns := fns''
      consts := consts''
      headLits := headLits.push (FLit.P (FPred.role rid s t))
    else if kind == "eq" then
      let lJson ← objField atomJson "left"
      let rJson ← objField atomJson "right"
      let (l, vars', fns', consts') ← parseTerm lJson vars fns consts
      let (r, vars'', fns'', consts'') ← parseTerm rJson vars' fns' consts'
      vars := vars''
      fns := fns''
      consts := consts''
      headLits := headLits.push (FLit.eq l r)
    else
      throw s!"unsupported head JAtom kind: {kind}"
  let clause : FCL := {
    body := bodyLits.toList
    head := bodyIneqs.toList ++ headLits.toList
  }
  pure (clause, concepts, roles, fns, consts)

private def parseNamedItem (json : Json) : Except String String :=
  match json.getStr? with
  | .ok s => .ok s
  | .error _ =>
    match json.getNat? with
    | .ok n => .ok (toString n)
    | .error err => .error err

def parseSource (json : Json) (requireNamed : Bool) :
    Except String (RequestedTaxonomySource × Interner) := do
  let clausesArr ← arrField json "clauses"
  let namedArr ← match json.getObjVal? "named" with
    | .ok v => v.getArr?
    | .error err =>
      if requireNamed then
        throw err
      else
        pure #[]
  let mut concepts : Interner := {}
  let mut roles : Interner := {}
  let mut fns : Interner := {}
  let mut consts : Interner := {}
  let mut namedIds : Array Nat := #[]
  for item in namedArr do
    let name ← parseNamedItem item
    let (cid, concepts') := concepts.intern name
    concepts := concepts'
    namedIds := namedIds.push cid
  let mut fclClauses : Array FCL := #[]
  for clauseJson in clausesArr do
    let (clause, concepts', roles', fns', consts') ←
      parseClause clauseJson concepts roles fns consts
    concepts := concepts'
    roles := roles'
    fns := fns'
    consts := consts'
    fclClauses := fclClauses.push clause
  pure ({ ontology := fclClauses.toList, named := namedIds.toList }, concepts)

private def termHasConst : FTerm → Bool
  | FTerm.const _ => true
  | FTerm.var _ => false
  | FTerm.app _ t => termHasConst t

private def termFirstApp : FTerm → Option Nat
  | FTerm.app f _ => some f
  | FTerm.const _ => none
  | FTerm.var _ => none

private def predHasConst : FPred → Bool
  | FPred.concept _ t => termHasConst t
  | FPred.role _ s t => termHasConst s || termHasConst t

private def predFirstApp : FPred → Option Nat
  | FPred.concept _ t => termFirstApp t
  | FPred.role _ s t => (termFirstApp s).orElse fun _ => termFirstApp t

private def litHasConst : FLit → Bool
  | FLit.P p => predHasConst p
  | FLit.eq s t | FLit.ineq s t => termHasConst s || termHasConst t

private def litFirstApp : FLit → Option Nat
  | FLit.P p => predFirstApp p
  | FLit.eq s t | FLit.ineq s t => (termFirstApp s).orElse fun _ => termFirstApp t

private def litIsEqOrIneq : FLit → Bool
  | FLit.eq _ _ | FLit.ineq _ _ => true
  | FLit.P _ => false

private def litIsConcept : FLit → Bool
  | FLit.P (FPred.concept _ _) => true
  | _ => false

private def litIsRole : FLit → Bool
  | FLit.P (FPred.role _ _ _) => true
  | _ => false

private def maxConceptLit : FLit → Nat
  | FLit.P (FPred.concept c _) => c
  | _ => 0

private def maxConceptClause (c : FCL) : Nat :=
  (c.body ++ c.head).foldl (fun acc l => max acc (maxConceptLit l)) 0

private def freshConceptLocal (named : List Nat) (cs : List FCL) : Nat :=
  let m1 := named.foldl max 0
  let m2 := cs.foldl (fun acc c => max acc (maxConceptClause c)) 0
  max m1 m2 + 1

private def classifyRejectedClause (seenFns : List Nat) (idx : Nat) (c : FCL) : String :=
  if c.head.any litIsEqOrIneq then
    s!"equality_or_inequality_literal (clause {idx})"
  else if c.body.any litHasConst || c.head.any litHasConst then
    s!"individual_or_constant_term (clause {idx})"
  else if c.head.length > 1 then
    s!"disjunctive_head (clause {idx})"
  else if c.body.length > 2 && c.body.all litIsConcept then
    s!"nary_concept_conjunction (clause {idx}, body_len={c.body.length})"
  else if c.body.length > 2 && c.body.all litIsRole then
    s!"nary_role_chain (clause {idx}, body_len={c.body.length})"
  else
    match c.body, c.head with
    | [FLit.P (FPred.concept _ (FTerm.var vx)), FLit.P (FPred.role _ (FTerm.var vx') (FTerm.var vy))],
      [FLit.P (FPred.concept _ (FTerm.var vy'))] =>
      if vx == vx' && vy == vy' && vx != vy then
        s!"universal_restriction_propagation (clause {idx})"
      else
        s!"concept_role_to_concept_var_mismatch (clause {idx})"
    | [FLit.P (FPred.role _ (FTerm.var vx') (FTerm.var vy)), FLit.P (FPred.concept _ (FTerm.var vx))],
      [FLit.P (FPred.concept _ (FTerm.var vy'))] =>
      if vx == vx' && vy == vy' && vx != vy then
        s!"universal_restriction_propagation (clause {idx})"
      else
        s!"concept_role_to_concept_var_mismatch (clause {idx})"
    | [FLit.P (FPred.role _ (FTerm.var vx) (FTerm.var vy))],
      [FLit.P (FPred.role _ (FTerm.var vy') (FTerm.var vx'))] =>
      if vx == vx' && vy == vy' && vx != vy then
        s!"inverse_or_symmetric_role_clause (clause {idx})"
      else
        s!"role_to_role_var_mismatch (clause {idx})"
    | [FLit.P (FPred.role _ (FTerm.var vx) (FTerm.var vy))],
      [FLit.P (FPred.concept _ (FTerm.var vy'))] =>
      if vx == vy && vx == vy' then
        s!"self_restriction_lhs (clause {idx})"
      else if vy == vy' && vx != vy then
        s!"role_range_clause (clause {idx})"
      else
        s!"role_to_concept_var_mismatch (clause {idx})"
    | [FLit.P (FPred.concept _ (FTerm.var vx))],
      [FLit.P (FPred.role _ (FTerm.var vx') (FTerm.var vy'))] =>
      if vx == vx' && vx == vy' then
        s!"self_restriction_rhs (clause {idx})"
      else
        s!"concept_to_role_clause (clause {idx})"
    | _, _ =>
      match (c.body.findSome? litFirstApp).orElse (fun _ => c.head.findSome? litFirstApp) with
      | some f =>
        if f ∈ seenFns then
          s!"reused_skolem_function (clause {idx})"
        else
          s!"unpaired_or_nonadjacent_skolem_clause (clause {idx})"
      | none =>
        s!"unsupported_clause_shape (clause {idx}, body_len={c.body.length}, head_len={c.head.length})"

partial def explainFirstRejectionAux
    (top bottom : Nat) (seenFns : List Nat) (idx : Nat) : List FCL → String
  | [] => "unknown rejection"
  | c1 :: c2 :: rest =>
    match c1.body, c1.head, c2.body, c2.head with
    | [FLit.P (FPred.concept a1 (FTerm.var vx))],
      [FLit.P (FPred.role _ (FTerm.var vx') (FTerm.app f (FTerm.var vx'')))],
      [FLit.P (FPred.concept a2 (FTerm.var vy))],
      [FLit.P (FPred.concept b (FTerm.app f' (FTerm.var vy')))] =>
      if a1 == a2 && vx == vx' && vx == vx'' && vy == vy' &&
          f ∉ seenFns && f == f' &&
          a1 != top && a1 != bottom && b != top && b != bottom then
        explainFirstRejectionAux top bottom (f :: seenFns) (idx + 2) rest
      else if (recognizeEL [] [c1]).isSome then
        explainFirstRejectionAux top bottom seenFns (idx + 1) (c2 :: rest)
      else
        classifyRejectedClause seenFns idx c1
    | [FLit.P (FPred.concept a2 (FTerm.var vy))],
      [FLit.P (FPred.concept b (FTerm.app f' (FTerm.var vy')))],
      [FLit.P (FPred.concept a1 (FTerm.var vx))],
      [FLit.P (FPred.role _ (FTerm.var vx') (FTerm.app f (FTerm.var vx'')))] =>
      if a1 == a2 && vx == vx' && vx == vx'' && vy == vy' &&
          f ∉ seenFns && f == f' &&
          a1 != top && a1 != bottom && b != top && b != bottom then
        explainFirstRejectionAux top bottom (f :: seenFns) (idx + 2) rest
      else if (recognizeEL [] [c1]).isSome then
        explainFirstRejectionAux top bottom seenFns (idx + 1) (c2 :: rest)
      else
        classifyRejectedClause seenFns idx c1
    | _, _, _, _ =>
      if (recognizeEL [] [c1]).isSome then
        explainFirstRejectionAux top bottom seenFns (idx + 1) (c2 :: rest)
      else
        classifyRejectedClause seenFns idx c1
  | [c1] =>
    if (recognizeEL [] [c1]).isSome then
      "unknown rejection"
    else
      classifyRejectedClause seenFns idx c1

def explainFirstRejection (source : RequestedTaxonomySource) : String :=
  let top := freshConceptLocal source.named source.ontology
  let bottom := max (top + 1) (freshConceptLocal (top :: source.named) source.ontology)
  explainFirstRejectionAux top bottom [] 0 source.ontology

def renderTaxonomyJson (answer : TaxonomyAnswer) (concepts : Interner) : String :=
  let nameOf (id : Nat) : Json :=
    match concepts.names[id]? with
    | some s => Json.str s
    | none => Json.num id
  let namedJson := Json.arr (answer.named.toArray.map nameOf)
  let cellsJson := Json.arr (answer.cells.toArray.map fun cell =>
    Json.mkObj [
      ("sub", nameOf cell.sub),
      ("sup", nameOf cell.sup),
      ("answer", Json.bool cell.answer)
    ])
  (Json.mkObj [
    ("named", namedJson),
    ("cells", cellsJson)
  ]).compress

private def parseCliArgs : List String → Option (Bool × String)
  | [path] => some (false, path)
  | ["--recognize-only", path] => some (true, path)
  | [path, "--recognize-only"] => some (true, path)
  | _ => none

def runFile (recognizeOnly : Bool) (path : String) : IO UInt32 := do
  let raw ← IO.FS.readFile path
  let json ← match Json.parse raw with
    | .ok value => pure value
    | .error err =>
      IO.eprintln s!"invalid JSON: {err}"
      return 2
  let (source, concepts) ← match parseSource json (!recognizeOnly) with
    | .ok value => pure value
    | .error err =>
      IO.eprintln s!"invalid EL reference input: {err}"
      return 2
  if !source.named.Nodup then
    IO.eprintln "duplicate names"
    return 3
  if recognizeOnly then
    match recognizeEL source.named source.ontology with
    | some _ =>
      IO.println "recognised"
      return 0
    | none =>
      let reason := explainFirstRejection source
      IO.eprintln s!"not recognised: {reason}"
      return 3
  match elReferenceExecution.run source with
  | .publish published =>
    IO.println (renderTaxonomyJson published.answer concepts)
    return 0
  | .defer | .timeout | .error =>
    let reason := explainFirstRejection source
    IO.eprintln s!"not recognised: {reason}"
    return 3

end KMELReferenceCheck

def main (args : List String) : IO UInt32 := do
  match KMELReferenceCheck.parseCliArgs args with
  | none =>
    IO.eprintln "usage: km-el-reference [--recognize-only] <clauses.json>"
    return 2
  | some (recognizeOnly, path) =>
    try
      KMELReferenceCheck.runFile recognizeOnly path
    catch err =>
      IO.eprintln s!"failed to read {path}: {err}"
      pure (2 : UInt32)
