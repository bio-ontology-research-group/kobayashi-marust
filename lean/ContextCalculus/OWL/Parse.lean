import Std.Data.HashMap
import ContextCalculus.OWL.Semantics

/-!
# OWL 2 functional-style syntax parser for the fragment `F` (v1.6.2)

`OWL.parse text` reads an OWL 2 functional-style syntax (OFN) document and
returns the ontology of `OWL/Semantics.lean`, or a reason for rejecting it.
In v1.6.2 this function is part of the trusted specification: the meaning of
a document is the direct semantics of `OWL.parse text`
(`docs/V1.6.2-FRONTEND-PLAN.md`, section 2). The code is therefore kept
plain: a byte-level tokeniser, an s-expression reader with an explicit
stack, and a converter from s-expressions to `Axiom`.

## Lexical rules (OWL 2 FSS section 2.3, the Rust tokeniser `sexpr.rs`)

* Whitespace is U+20, U+9, U+A and U+D. A comment starts with `#` where a
  token may start and runs to the next line feed or carriage return.
* `(` and `)` are tokens. A full IRI is `<` up to the next `>`, taken
  verbatim (no normalisation). A string literal is `"` up to the next
  unescaped `"`; a backslash escapes the following byte, so `\"` and `\\`
  do not end the literal. Literal contents are never used (literals only
  occur in skipped annotations), but they may contain `)`, `"` escapes and
  non-ASCII text without disturbing the token stream.
* Every other token is a word: the longest run of bytes that are neither
  whitespace nor parentheses. A typed or language-tagged literal
  `"v"^^xsd:string` / `"v"@en` is therefore a literal followed by the word
  `^^xsd:string` / `@en`, as in the Rust tokeniser.
* A word made only of ASCII letters and followed by `(` opens a list with
  that head (`SubClassOf(`...`)`); whitespace may separate the two. A `(`
  without such a head opens an anonymous list (only `HasKey` uses one).

Differences from the Rust tokeniser (recorded as Rust deviations in the
v1.6.2 parse hand-back): Rust also treats the bytes 0x0B, 0x0C, 0x85 and
0xA0 as whitespace (the last two are UTF-8 continuation bytes, so a bare
word containing, for example, `à` makes Rust slice inside a character), and
ends a comment only at a line feed. Rust accepts an unterminated IRI or
literal as a token running to the end of the text; here they are syntax
errors.

## IRIs (OWL 2 FSS sections 2.4 and 3.7)

IRIs are expanded strings. `Prefix(p:=<ns>)` binds `p`; the empty prefix is
written `Prefix(:=<ns>)`. A word `p:local` (split at its first `:`) expands
to `ns ++ local`; a full IRI `<iri>` is `iri`. Two spellings of one IRI
therefore give the same string. As in `conformance.rs`, the prefixes
`owl:`, `rdf:`, `rdfs:` and `xsd:` are predeclared with their standard
namespaces (the four of FSS Table 2; `xml:` is not predeclared, by the
standard or by Rust); declaring one of them again with the same namespace is
allowed, with another namespace is an error; declaring any prefix twice is
an error; using an undeclared prefix is an error. The Rust parser itself
does not expand prefixed names: its registry (`iri.rs`) keys an entity by
its raw spelling, so it treats `ex:A` and `<http://ex#A>` as two entities
(a deviation from FSS 2.4 that the suite never exercises, see the plan,
section 3).

`owl:Thing` and `owl:Nothing` are recognised after expansion, so every
spelling of `http://www.w3.org/2002/07/owl#Thing` is `ClassExpr.thing`.
`ObjectInverseOf(ObjectInverseOf(r))` is `r` (FSS only allows a named
property inside `ObjectInverseOf`; the double inverse is accepted as the
v1.6.2 plan asks).

## Document structure (FSS section 3.7)

`Prefix(...)*` then one `Ontology(` [ontology IRI [version IRI]]
`Import(...)*` `Annotation(...)*` axioms `)` and the end of the text.
Imports are rejected. Ontology annotations and axiom annotations (the
leading `Annotation(...)` arguments of an axiom) are skipped.

## What is accepted, skipped and rejected

Accepted (the fragment `F`, plan section 3): `SubClassOf`,
`EquivalentClasses`, `DisjointClasses`, `ObjectPropertyDomain`,
`ObjectPropertyRange`, `SubObjectPropertyOf` (with an atomic property or an
`ObjectPropertyChain` of at least two properties),
`EquivalentObjectProperties`, `InverseObjectProperties`,
`TransitiveObjectProperty`, `SymmetricObjectProperty`, and
`Declaration(Class(..))`, `Declaration(ObjectProperty(..))`; class
expressions over class IRIs, `owl:Thing`, `owl:Nothing`,
`ObjectIntersectionOf`, `ObjectUnionOf`, `ObjectComplementOf`,
`ObjectSomeValuesFrom`, `ObjectAllValuesFrom`; object-property expressions
over property IRIs and `ObjectInverseOf`. Operand counts follow FSS
(`EquivalentClasses`, `DisjointClasses`, `EquivalentObjectProperties`,
`ObjectIntersectionOf` and `ObjectUnionOf` need at least two operands).

Skipped (no semantic content): `Annotation(...)`, `AnnotationAssertion`,
`SubAnnotationPropertyOf`, `AnnotationPropertyDomain`,
`AnnotationPropertyRange`, and declarations of annotation properties,
datatypes, data properties and named individuals. A declaration of
`owl:Thing` or `owl:Nothing` is skipped as well (they are not class IRIs of
the semantics).

Rejected with a reason naming the construct: everything else. Every
rejection is an `Except.error`, never a panic.

## Cost

The tokeniser and the reader run in loops (tail recursion with a fuel bound
of the text length, since every step consumes at least one byte); the
converter recurses only on the nesting depth of one axiom. Repeated
spellings are resolved once and share one string (`Cache`).
-/

namespace ContextCalculus.OWL

namespace Parse

/-! ## Bytes -/

section Bytes

def byteLParen : UInt8 := 40   -- (
def byteRParen : UInt8 := 41   -- )
def byteLess : UInt8 := 60     -- <
def byteGreater : UInt8 := 62  -- >
def byteQuote : UInt8 := 34    -- "
def byteBackslash : UInt8 := 92
def byteHash : UInt8 := 35     -- #
def byteLF : UInt8 := 10
def byteCR : UInt8 := 13

/-- Whitespace bytes of OWL 2 FSS section 2.3. -/
def isSpace (b : UInt8) : Bool :=
  b == 32 || b == 9 || b == byteLF || b == byteCR

/-- Bytes that end a word. -/
def isWordEnd (b : UInt8) : Bool :=
  isSpace b || b == byteLParen || b == byteRParen

/-- The first position at or after `i` that is neither whitespace nor inside
a comment. `comment` says whether position `i` is inside a comment. -/
def skipSpace (bs : ByteArray) (i : Nat) (comment : Bool) : Nat :=
  if h : i < bs.size then
    let b := bs[i]
    if comment then
      skipSpace bs (i + 1) (!(b == byteLF || b == byteCR))
    else if isSpace b then
      skipSpace bs (i + 1) false
    else if b == byteHash then
      skipSpace bs (i + 1) true
    else
      i
  else
    i
termination_by bs.size - i

/-- The position of the first `target` byte at or after `i`, if any. -/
def findByte (bs : ByteArray) (target : UInt8) (i : Nat) : Option Nat :=
  if h : i < bs.size then
    if bs[i] == target then some i else findByte bs target (i + 1)
  else
    none
termination_by bs.size - i

/-- The position just after the closing quote of a string literal whose
contents start at `i`, if the literal is terminated. -/
def literalEnd (bs : ByteArray) (i : Nat) : Option Nat :=
  if h : i < bs.size then
    let b := bs[i]
    if b == byteBackslash then literalEnd bs (i + 2)
    else if b == byteQuote then some (i + 1)
    else literalEnd bs (i + 1)
  else
    none
termination_by bs.size - i

/-- The end of the word starting at `i`. -/
def wordEnd (bs : ByteArray) (i : Nat) : Nat :=
  if h : i < bs.size then
    if isWordEnd bs[i] then i else wordEnd bs (i + 1)
  else
    i
termination_by bs.size - i

/-- The bytes `[i, j)` as a string. Token boundaries are ASCII bytes of a
valid UTF-8 text, so the slice is valid UTF-8; the check is kept so that the
function is total without that argument. -/
def slice (bs : ByteArray) (i j : Nat) : Except String String :=
  match String.fromUTF8? (bs.extract i j) with
  | some s => .ok s
  | none => .error "syntax error: token is not valid UTF-8"

end Bytes

/-! ## Tokens -/

inductive Tok where
  | lparen
  | rparen
  /-- A word: keyword, abbreviated IRI, number, `^^datatype`, `@lang`, ... -/
  | word (text : String)
  /-- A full IRI, without the angle brackets. -/
  | iri (text : String)
  /-- A quoted string literal; its contents are not kept. -/
  | literal
  | eof
deriving Repr, Inhabited

/-- The token starting at the first non-space position at or after `i`, and
the position after it. -/
def nextTok (bs : ByteArray) (i : Nat) : Except String (Tok × Nat) := do
  let i := skipSpace bs i false
  if h : i < bs.size then
    let b := bs[i]
    if b == byteLParen then
      return (.lparen, i + 1)
    else if b == byteRParen then
      return (.rparen, i + 1)
    else if b == byteLess then
      match findByte bs byteGreater (i + 1) with
      | some j => return (.iri (← slice bs (i + 1) j), j + 1)
      | none => throw "syntax error: unterminated full IRI"
    else if b == byteQuote then
      match literalEnd bs (i + 1) with
      | some j => return (.literal, j)
      | none => throw "syntax error: unterminated string literal"
    else
      let j := wordEnd bs i
      return (.word (← slice bs i j), j)
  else
    return (.eof, i)

/-- Whether the next token at or after `i` is `(`. -/
def nextIsLParen (bs : ByteArray) (i : Nat) : Bool :=
  let i := skipSpace bs i false
  if h : i < bs.size then bs[i] == byteLParen else false

/-- A word that introduces a list when followed by `(`: nonempty and made
only of ASCII letters (as in `sexpr.rs`). -/
def isKeyword (w : String) : Bool :=
  !w.isEmpty && w.all Char.isAlpha

/-! ## S-expressions -/

inductive Node where
  | word (text : String)
  | iri (text : String)
  | literal
  /-- `head(args)`; the head of an anonymous list `(args)` is `""`. -/
  | list (head : String) (args : Array Node)
deriving Repr, Inhabited

/-- A short description of a node for error messages. -/
def Node.describe : Node → String
  | .word w => w
  | .iri s => s!"<{s}>"
  | .literal => "a literal"
  | .list "" _ => "an anonymous list"
  | .list h _ => h

/-- A list being read: its head and the arguments read so far. -/
abbrev Frame := String × Array Node

/-- Add a finished node to the innermost open list. `Array.modify` keeps the
argument array unshared, so the push does not copy it. -/
def addChild (stack : Array Frame) (n : Node) : Array Frame :=
  stack.modify (stack.size - 1) fun (h, args) => (h, args.push n)

/-- The node read, once only the bottom frame is left and holds one node. -/
def finished (stack : Array Frame) : Option Node :=
  if stack.size == 1 then
    match stack.back? with
    | some (_, #[n]) => some n
    | _ => none
  else none

/-- Read one node from position `i`. `stack` holds the open lists, innermost
last, above a bottom frame that receives the finished node. Each step
consumes at least one byte, so `fuel = bs.size + 1` suffices. -/
def readNodeFrom (bs : ByteArray) (fuel i : Nat) (stack : Array Frame) :
    Except String (Node × Nat) :=
  match fuel with
  | 0 => .error "syntax error: input too long"
  | fuel + 1 => do
    let (t, j) ← nextTok bs i
    let (stack, j) ← match t with
      | .eof => throw "syntax error: unexpected end of input"
      | .lparen => pure (stack.push ("", #[]), j)
      | .word w =>
        if isKeyword w && nextIsLParen bs j then
          -- a keyword followed by `(`: consume the `(` and open the list
          let (_, k) ← nextTok bs j
          pure (stack.push (w, #[]), k)
        else pure (addChild stack (.word w), j)
      | .iri s => pure (addChild stack (.iri s), j)
      | .literal => pure (addChild stack .literal, j)
      | .rparen =>
        if stack.size ≤ 1 then throw "syntax error: unexpected )"
        else match stack.back? with
          | some (h, args) => pure (addChild stack.pop (.list h args), j)
          | none => throw "syntax error: unexpected )"
    match finished stack with
    | some n => return (n, j)
    | none => readNodeFrom bs fuel j stack

/-- Read one node starting at position `i`; return it and the position
after it. -/
def readNode (bs : ByteArray) (i : Nat) : Except String (Node × Nat) :=
  readNodeFrom bs (bs.size + 1) i #[("", #[])]

/-! ## IRIs -/

abbrev Prefixes := Std.HashMap String String

def owlNs : String := "http://www.w3.org/2002/07/owl#"
def owlThing : IRI := owlNs ++ "Thing"
def owlNothing : IRI := owlNs ++ "Nothing"
def owlTopObjectProperty : IRI := owlNs ++ "topObjectProperty"
def owlBottomObjectProperty : IRI := owlNs ++ "bottomObjectProperty"

/-- FSS Table 2, as in `STANDARD_PREFIXES` of `conformance.rs`. -/
def standardPrefixes : List (String × String) :=
  [("rdfs", "http://www.w3.org/2000/01/rdf-schema#"),
   ("owl", owlNs),
   ("xsd", "http://www.w3.org/2001/XMLSchema#"),
   ("rdf", "http://www.w3.org/1999/02/22-rdf-syntax-ns#")]

/-- Expand an abbreviated IRI `p:local` (split at the first `:`). -/
def expandWord (pfx : Prefixes) (w : String) : Except String IRI :=
  match w.splitOn ":" with
  | [] | [_] => .error s!"syntax error: {w} is not an IRI"
  | p :: rest =>
    if p == "_" then .error s!"out of fragment: anonymous individual {w}"
    else match pfx.get? p with
      | some ns => .ok (ns ++ ":".intercalate rest)
      | none => .error s!"syntax error: undeclared prefix {p}: in {w}"

/-- Resolved spellings: `full` interns full IRIs, `abbreviated` maps an
abbreviated IRI to its expansion. A pure memo table: every entry is what
`expandWord` returns, so results do not depend on it. -/
structure Cache where
  full : Std.HashMap String IRI := {}
  abbreviated : Std.HashMap String IRI := {}

abbrev ConvM := StateT Cache (Except String)

/-- The IRI a node spells. -/
def iriOf (pfx : Prefixes) : Node → ConvM IRI
  | .iri s => do
    let c ← get
    match c.full.get? s with
    | some x => return x
    | none => set { c with full := c.full.insert s s }; return s
  | .word w => do
    let c ← get
    match c.abbreviated.get? w with
    | some x => return x
    | none =>
      let x ← expandWord pfx w
      set { c with abbreviated := c.abbreviated.insert w x }
      return x
  | n => throw s!"syntax error: expected an IRI, found {n.describe}"

def outOfFragment {α : Type} (what : String) : ConvM α :=
  throw s!"out of fragment: {what}"

/-! ## Expressions -/

/-- The inverse of an object-property expression. -/
def invert : ObjProp → ObjProp
  | .named r => .inv r
  | .inv r => .named r

/-- An object-property expression. -/
def toRole (pfx : Prefixes) (n : Node) : ConvM ObjProp :=
  match n with
  | .list "ObjectInverseOf" args =>
    if h : args.size = 1 then return invert (← toRole pfx args[0])
    else throw "syntax error: ObjectInverseOf takes one property"
  | .list h _ => outOfFragment s!"object property expression {if h == "" then "(anonymous list)" else h}"
  | _ => do
    let r ← iriOf pfx n
    if r == owlTopObjectProperty then outOfFragment "owl:topObjectProperty"
    else if r == owlBottomObjectProperty then outOfFragment "owl:bottomObjectProperty"
    else return .named r
termination_by sizeOf n
decreasing_by
  simp_wf
  have := Array.sizeOf_getElem args 0 (by omega)
  omega

/-- The reason for rejecting a class constructor outside `F`. -/
def classConstructRejection (h : String) : String :=
  if h == "ObjectMinCardinality" || h == "ObjectMaxCardinality" ||
      h == "ObjectExactCardinality" then
    s!"{h} (cardinality restriction)"
  else if h == "ObjectOneOf" || h == "ObjectHasValue" then s!"{h} (nominal)"
  else if h == "ObjectHasSelf" then s!"{h} (self restriction)"
  else if h.startsWith "Data" then s!"{h} (data construct)"
  else if h == "" then "anonymous list in a class position"
  else s!"class expression {h}"

/-- A class expression. -/
def toClass (pfx : Prefixes) (n : Node) : ConvM ClassExpr :=
  match n with
  | .list "ObjectIntersectionOf" args => do
    if args.size < 2 then throw "syntax error: ObjectIntersectionOf needs two operands"
    let cs ← args.attach.mapM fun ⟨a, _⟩ => toClass pfx a
    return .and cs.toList
  | .list "ObjectUnionOf" args => do
    if args.size < 2 then throw "syntax error: ObjectUnionOf needs two operands"
    let cs ← args.attach.mapM fun ⟨a, _⟩ => toClass pfx a
    return .or cs.toList
  | .list "ObjectComplementOf" args =>
    if h : args.size = 1 then return .not (← toClass pfx args[0])
    else throw "syntax error: ObjectComplementOf takes one operand"
  | .list "ObjectSomeValuesFrom" args =>
    if h : args.size = 2 then return .some (← toRole pfx args[0]) (← toClass pfx args[1])
    else throw "syntax error: ObjectSomeValuesFrom takes a property and a class"
  | .list "ObjectAllValuesFrom" args =>
    if h : args.size = 2 then return .all (← toRole pfx args[0]) (← toClass pfx args[1])
    else throw "syntax error: ObjectAllValuesFrom takes a property and a class"
  | .list h _ => outOfFragment (classConstructRejection h)
  | _ => do
    let a ← iriOf pfx n
    if a == owlThing then return .thing
    else if a == owlNothing then return .nothing
    else return .cls a
termination_by sizeOf n
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := Array.sizeOf_lt_of_mem ‹_ ∈ args›; omega)
    | (have := Array.sizeOf_getElem args 0 (by omega); omega)
    | (have := Array.sizeOf_getElem args 1 (by omega); omega)

/-! ## Axioms -/

def Node.isAnnotation : Node → Bool
  | .list "Annotation" _ => true
  | _ => false

/-- The operands of an axiom: its leading `Annotation(...)` arguments
removed. FSS puts axiom annotations first; one after an operand is a syntax
error. -/
def operands (h : String) (args : Array Node) : ConvM (Array Node) := do
  let ops := args.extract (args.findIdx? (fun a => !a.isAnnotation) |>.getD args.size) args.size
  if ops.any (·.isAnnotation) then
    throw s!"syntax error: Annotation after an operand of {h}"
  return ops

/-- Axiom heads with no semantic content. -/
def skippedAxioms : List String :=
  ["AnnotationAssertion", "SubAnnotationPropertyOf", "AnnotationPropertyDomain",
   "AnnotationPropertyRange"]

/-- Rejected axiom heads, with the reason. -/
def rejectedAxiom (h : String) : String :=
  if ["ClassAssertion", "ObjectPropertyAssertion", "NegativeObjectPropertyAssertion",
      "DataPropertyAssertion", "NegativeDataPropertyAssertion", "SameIndividual",
      "DifferentIndividuals"].contains h then s!"{h} (ABox assertion)"
  else if ["FunctionalObjectProperty", "InverseFunctionalObjectProperty",
      "ReflexiveObjectProperty", "IrreflexiveObjectProperty",
      "AsymmetricObjectProperty", "DisjointObjectProperties"].contains h then
    s!"{h} (object property characteristic)"
  else if ["SubDataPropertyOf", "EquivalentDataProperties", "DisjointDataProperties",
      "DataPropertyDomain", "DataPropertyRange", "FunctionalDataProperty",
      "DatatypeDefinition"].contains h then s!"{h} (data property axiom)"
  else if h == "DLSafeRule" then s!"{h} (rule)"
  else if h == "HasKey" then s!"{h} (key)"
  else if h == "DisjointUnion" then s!"{h} (disjoint union)"
  else if h == "" then "anonymous list in an axiom position"
  else s!"axiom {h}"

def arityError {α : Type} (h : String) : ConvM α :=
  throw s!"syntax error: wrong number of operands for {h}"

/-- A declaration: `some` for classes and object properties, `none` for the
other entity kinds and for `owl:Thing` / `owl:Nothing`. -/
def toDeclaration (pfx : Prefixes) (ops : Array Node) : ConvM (Option Axiom) := do
  match ops with
  | #[.list "Class" #[x]] =>
    let a ← iriOf pfx x
    if a == owlThing || a == owlNothing then return none
    return some (.declareClass a)
  | #[.list "ObjectProperty" #[x]] =>
    let r ← iriOf pfx x
    if r == owlTopObjectProperty || r == owlBottomObjectProperty then return none
    return some (.declareObjectProperty r)
  | #[.list k #[x]] =>
    if ["DataProperty", "NamedIndividual", "AnnotationProperty", "Datatype"].contains k then
      let _ ← iriOf pfx x
      return none
    else throw s!"syntax error: unknown entity kind {k} in Declaration"
  | _ => arityError "Declaration"

/-- One axiom (a child of `Ontology(...)` that is a list): `some` for an axiom
of `F`, `none` for a skipped one. -/
def toAxiom (pfx : Prefixes) (h : String) (args : Array Node) : ConvM (Option Axiom) := do
  if skippedAxioms.contains h then return none
  let ops ← operands h args
  let classes : ConvM (List ClassExpr) := do
    if ops.size < 2 then arityError h
    return (← ops.mapM (toClass pfx)).toList
  let roles : ConvM (List ObjProp) := do
    if ops.size < 2 then arityError h
    return (← ops.mapM (toRole pfx)).toList
  match h with
  | "Declaration" => toDeclaration pfx ops
  | "SubClassOf" =>
    match ops with
    | #[c, d] => return some (.subClassOf (← toClass pfx c) (← toClass pfx d))
    | _ => arityError h
  | "EquivalentClasses" => return some (.equivalentClasses (← classes))
  | "DisjointClasses" => return some (.disjointClasses (← classes))
  | "ObjectPropertyDomain" =>
    match ops with
    | #[r, c] => return some (.domain (← toRole pfx r) (← toClass pfx c))
    | _ => arityError h
  | "ObjectPropertyRange" =>
    match ops with
    | #[r, c] => return some (.range (← toRole pfx r) (← toClass pfx c))
    | _ => arityError h
  | "SubObjectPropertyOf" =>
    match ops with
    | #[.list "ObjectPropertyChain" chain, s] =>
      if chain.size < 2 then
        throw "syntax error: ObjectPropertyChain needs two properties"
      let rs ← chain.mapM (toRole pfx)
      return some (.subObjectPropertyOf rs.toList (← toRole pfx s))
    | #[r, s] => return some (.subObjectPropertyOf [← toRole pfx r] (← toRole pfx s))
    | _ => arityError h
  | "EquivalentObjectProperties" => return some (.equivalentObjectProperties (← roles))
  | "InverseObjectProperties" =>
    match ops with
    | #[r, s] => return some (.inverseObjectProperties (← toRole pfx r) (← toRole pfx s))
    | _ => arityError h
  | "TransitiveObjectProperty" =>
    match ops with
    | #[r] => return some (.transitive (← toRole pfx r))
    | _ => arityError h
  | "SymmetricObjectProperty" =>
    match ops with
    | #[r] => return some (.symmetric (← toRole pfx r))
    | _ => arityError h
  | _ => outOfFragment (rejectedAxiom h)

/-! ## Documents -/

/-- A `Prefix(...)` declaration added to `pfx`. As in `conformance.rs`, the
argument words are concatenated (`p:=<ns>` or `p: = <ns>`) and split at the
first `:=`. -/
def addPrefix (pfx : Prefixes) (declared : List String) (args : Array Node) :
    Except String (Prefixes × List String) := do
  let mut text := ""
  for a in args do
    match a with
    | .word w => text := text ++ w
    | .iri s => text := text ++ "<" ++ s ++ ">"
    | _ => throw "syntax error: malformed prefix declaration"
  match text.splitOn ":=" with
  | p :: rest =>
    let value := ":=".intercalate rest
    if rest.isEmpty || p.contains ':' || !(value.startsWith "<" && value.endsWith ">") then
      throw s!"syntax error: malformed prefix declaration {text}"
    let ns := ((value.drop 1).dropEnd 1).toString
    if declared.contains p then
      throw s!"syntax error: prefix {p}: is declared more than once"
    match standardPrefixes.lookup p with
    | some standard =>
      if ns != standard then
        throw s!"syntax error: standard prefix {p}: cannot be rebound to <{ns}>"
    | none => pure ()
    return (pfx.insert p ns, p :: declared)
  | [] => throw "syntax error: malformed prefix declaration"

/-- Where the reader is inside `Ontology(...)`: FSS orders the children as
IRIs, imports, annotations, axioms. -/
inductive Phase where
  | iris (seen : Nat)
  | annotations
  | axioms
deriving DecidableEq

/-- Read the children of `Ontology(` from position `i` up to the closing `)`;
return the axioms and the position after `)`. -/
def readOntologyBody (bs : ByteArray) (pfx : Prefixes) (fuel i : Nat) (phase : Phase)
    (cache : Cache) (acc : Array Axiom) : Except String (Array Axiom × Nat) :=
  match fuel with
  | 0 => .error "syntax error: input too long"
  | fuel + 1 => do
    let (t, j) ← nextTok bs i
    match t with
    | .rparen => return (acc, j)
    | .eof => throw "syntax error: unexpected end of input in Ontology"
    | _ =>
      let (node, j) ← readNode bs i
      match node, phase with
      | .list "Import" _, _ => throw "out of fragment: Import (imports are not resolved)"
      | .list "Annotation" _, .axioms =>
        throw "syntax error: ontology Annotation after an axiom"
      | .list "Annotation" _, _ =>
        readOntologyBody bs pfx fuel j .annotations cache acc
      | .list h args, _ =>
        let (ax, cache) ← (toAxiom pfx h args).run cache
        let acc := match ax with
          | some a => acc.push a
          | none => acc
        readOntologyBody bs pfx fuel j .axioms cache acc
      | n, .iris seen =>
        if seen < 2 then
          let (_, cache) ← (iriOf pfx n).run cache
          readOntologyBody bs pfx fuel j (.iris (seen + 1)) cache acc
        else throw s!"syntax error: unexpected {n.describe} in Ontology"
      | n, _ => throw s!"syntax error: unexpected {n.describe} in Ontology"

/-- Read the prefix declarations from position `i`, then the ontology. -/
def readDocument (bs : ByteArray) (fuel i : Nat) (pfx : Prefixes) (declared : List String) :
    Except String Ontology :=
  match fuel with
  | 0 => .error "syntax error: input too long"
  | fuel + 1 => do
    let (t, j) ← nextTok bs i
    match t with
    | .word "Prefix" =>
      match ← readNode bs i with
      | (.list "Prefix" args, k) =>
        let (pfx, declared) ← addPrefix pfx declared args
        readDocument bs fuel k pfx declared
      | _ => throw "syntax error: malformed prefix declaration"
    | .word "Ontology" =>
      let (open_, k) ← nextTok bs j
      match open_ with
      | .lparen =>
        let (axioms, k) ← readOntologyBody bs pfx (bs.size + 1) k (.iris 0) {} #[]
        match (← nextTok bs k).1 with
        | .eof => return { axioms := axioms.toList }
        | _ => throw "syntax error: content after the closing ) of Ontology"
      | _ => throw "syntax error: Ontology must be followed by ("
    | .eof => throw "syntax error: no Ontology(...) in the document"
    | .word w => throw s!"syntax error: unexpected {w} before Ontology"
    | _ => throw "syntax error: unexpected token before Ontology"

def initialPrefixes : Prefixes :=
  standardPrefixes.foldl (fun m (p, ns) => m.insert p ns) {}

end Parse

/-- Parse an OWL 2 functional-syntax document of the fragment `F`.
`.ok O` gives the ontology; `.error reason` says why the text is not a
document of `F` (a syntax error, or the first construct outside `F`). -/
def parse (text : String) : Except String Ontology :=
  let bs := text.toUTF8
  Parse.readDocument bs (bs.size + 1) 0 Parse.initialPrefixes []

end ContextCalculus.OWL
