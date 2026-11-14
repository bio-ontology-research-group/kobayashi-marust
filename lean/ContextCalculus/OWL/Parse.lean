import Std.Data.HashMap
import ContextCalculus.OWL.Semantics

/-!
# OWL 2 functional-style syntax parser (v1.6.2, extended to OWL 2 DL in v1.7.0 stage C0)

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
  do not end the literal. The lexical form resolves the escapes `\"` and
  `\\` (FSS section 2.3); a backslash before any other byte is kept with
  that byte. A literal token also takes a following `^^datatype` (a full
  or abbreviated IRI) or `@languageTag`; whitespace and comments may come
  in between, as in the Rust parser, which glues such an atom to the
  literal before it.
* Every other token is a word: the longest run of bytes that are neither
  whitespace nor parentheses.
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

Accepted: every axiom and expression of `OWL/Semantics.lean`, that is the
OWL 2 structural specification without annotations and without n-ary data
ranges. Class expressions: class IRIs, `owl:Thing`, `owl:Nothing`, the
Boolean connectives, `ObjectSomeValuesFrom`, `ObjectAllValuesFrom`,
`ObjectOneOf`, `ObjectHasValue`, `ObjectHasSelf`, the object
cardinalities (unqualified: filler `owl:Thing`), `DataSomeValuesFrom` and
`DataAllValuesFrom` with one data property, `DataHasValue` and the data
cardinalities (unqualified: range `rdfs:Literal`). Object-property
expressions: IRIs, `ObjectInverseOf` (in every property position; the
double inverse collapses), `owl:topObjectProperty`,
`owl:bottomObjectProperty`. Data-property expressions: IRIs,
`owl:topDataProperty`, `owl:bottomDataProperty`. Data ranges: datatype
IRIs, `DataIntersectionOf`, `DataUnionOf`, `DataComplementOf`,
`DataOneOf`, `DatatypeRestriction`. Individuals: IRIs and node IDs `_:x`
(only in individual positions). Axioms: the class axioms including
`DisjointUnion`, every object- and data-property axiom,
`DatatypeDefinition`, `HasKey`, the assertions, and declarations of every
entity kind. Declarations of `owl:Thing`, `owl:Nothing` and the top and
bottom object and data properties are skipped (they are not IRIs of the
semantics). Operand counts follow FSS.

Literals: `"abc"` has datatype `xsd:string`, `"abc"@en` has datatype
`rdf:PlainLiteral` and language tag `en` (structural specification,
section 5.7). A literal whose datatype is in the OWL 2 datatype map must
have a lexical form in that datatype's lexical space, or the document is
rejected (`ill-typed literal`). The checks follow XML Schema 1.1 and the
OWL 2 structural specification, section 4, with two approximations: XML
name characters accept every non-ASCII character, and `rdf:XMLLiteral` and
`xsd:anyURI` accept every string. `owl:real` and `rdfs:Literal` have no
lexical forms. Literals with a datatype outside the map are accepted. A
`DatatypeRestriction` must use a datatype of the map and facets that the
map defines for it (`xsd:minInclusive` and its three siblings for the
numeric and time types; `xsd:length`, `xsd:minLength`, `xsd:maxLength`
and, except for the binary types, `xsd:pattern` for the string, URI and
binary types; also `rdf:langRange` for `rdf:PlainLiteral`); length facets
take a nonnegative integer. Facet values are not checked further.

Skipped (no semantic content): `Annotation(...)`, `AnnotationAssertion`,
`SubAnnotationPropertyOf`, `AnnotationPropertyDomain`,
`AnnotationPropertyRange`.

Rejected with a reason: imports (`out of fragment: Import`), `DLSafeRule`
(`out of fragment: DLSafeRule (rule)`), n-ary data ranges
(`DataSomeValuesFrom` / `DataAllValuesFrom` with more than one data
property), property chains outside `SubObjectPropertyOf`, unknown heads,
ill-typed literals, bad facets, annotations after an operand, and syntax
errors. Every rejection is an `Except.error`, never a panic.

The global restrictions of OWL 2 DL (simple roles, regularity, ...) are not
checked here.

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

/-- How an IRI is spelled: a full IRI (without the angle brackets) or an
abbreviated IRI `p:local`. -/
inductive Spelling where
  | full (text : String)
  | abbreviated (text : String)
deriving Repr, Inhabited

/-- What follows the lexical form of a literal: nothing, `^^datatype` or
`@languageTag`. -/
inductive LitSuffix where
  | plain
  | typed (datatype : Spelling)
  | lang (tag : String)
deriving Repr, Inhabited

inductive Tok where
  | lparen
  | rparen
  /-- A word: keyword, abbreviated IRI, number, node ID, ... -/
  | word (text : String)
  /-- A full IRI, without the angle brackets. -/
  | iri (text : String)
  /-- A literal: its lexical form (escapes resolved) and its suffix. -/
  | literal (lexical : String) (suffix : LitSuffix)
  | eof
deriving Repr, Inhabited

/-- The byte at `k`, or `0` past the end. -/
def byteAt (bs : ByteArray) (k : Nat) : UInt8 :=
  if h : k < bs.size then bs[k] else 0

def byteCaret : UInt8 := 94    -- ^
def byteAt' : UInt8 := 64      -- @

/-- The bytes `[k, j)` of a literal's contents with the escapes `\"` and
`\\` resolved; a backslash before any other byte is kept with that byte. -/
def unescapeFrom (bs : ByteArray) (j k : Nat) (acc : ByteArray) : ByteArray :=
  if k < j then
    let b := byteAt bs k
    let c := byteAt bs (k + 1)
    if b == byteBackslash && k + 1 < j && (c == byteQuote || c == byteBackslash) then
      unescapeFrom bs j (k + 2) (acc.push c)
    else
      unescapeFrom bs j (k + 1) (acc.push b)
  else
    acc
termination_by j - k

/-- The lexical form of the literal whose contents are the bytes `[i, j)`. -/
def lexicalForm (bs : ByteArray) (i j : Nat) : Except String String :=
  match String.fromUTF8? (unescapeFrom bs j i ByteArray.empty) with
  | some s => .ok s
  | none => .error "syntax error: literal is not valid UTF-8"

/-- The suffix of a literal that ends just before position `j`, and the
position after the suffix. Whitespace and comments may separate the
lexical form from `^^` or `@`, as in the Rust parser, which glues a
following `^^dt` or `@lang` atom to the literal. -/
def literalSuffix (bs : ByteArray) (j : Nat) : Except String (LitSuffix × Nat) := do
  let k := skipSpace bs j false
  if byteAt bs k == byteCaret && byteAt bs (k + 1) == byteCaret then
    let m := k + 2
    if byteAt bs m == byteLess then
      match findByte bs byteGreater (m + 1) with
      | some e => return (.typed (.full (← slice bs (m + 1) e)), e + 1)
      | none => throw "syntax error: unterminated full IRI"
    else
      let e := wordEnd bs m
      if e == m then throw "syntax error: missing datatype after ^^"
      return (.typed (.abbreviated (← slice bs m e)), e)
  else if byteAt bs k == byteAt' then
    let e := wordEnd bs (k + 1)
    if e == k + 1 then throw "syntax error: missing language tag after @"
    return (.lang (← slice bs (k + 1) e), e)
  else
    return (.plain, j)

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
      | some j =>
        let lex ← lexicalForm bs (i + 1) (j - 1)
        let (sfx, k) ← literalSuffix bs j
        -- `literalSuffix` returns a position at or after `j > i`
        return (.literal lex sfx, max k j)
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
  | literal (lexical : String) (suffix : LitSuffix)
  /-- `head(args)`; the head of an anonymous list `(args)` is `""`. -/
  | list (head : String) (args : Array Node)
deriving Repr, Inhabited

/-- A short description of a node for error messages. -/
def Node.describe : Node → String
  | .word w => w
  | .iri s => s!"<{s}>"
  | .literal .. => "a literal"
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
      | .literal lex sfx => pure (addChild stack (.literal lex sfx), j)
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
def owlTopDataProperty : IRI := owlNs ++ "topDataProperty"
def owlBottomDataProperty : IRI := owlNs ++ "bottomDataProperty"

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
    if p == "_" then .error s!"syntax error: anonymous individual {w} where an IRI is expected"
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

/-! ## Literals and the OWL 2 datatype map (lexical forms, facets) -/

section Datatypes

def xsdNs : String := "http://www.w3.org/2001/XMLSchema#"
def rdfNs : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#"
def xsdString : IRI := xsdNs ++ "string"
def rdfPlainLiteral : IRI := rdfNs ++ "PlainLiteral"

/-- The kinds of datatypes of the OWL 2 datatype map (structural
specification, section 4), as far as lexical forms and facets go. -/
inductive DtKind where
  /-- `owl:real`: no lexical forms. -/
  | real
  | rational
  | decimal
  /-- An integer type with optional lower and upper bounds. -/
  | integer (lo hi : Option Int)
  | float
  | string
  | normalizedString
  | token
  | language
  | name
  | ncName
  | nmToken
  | boolean
  | hexBinary
  | base64Binary
  | anyURI
  | dateTime
  | dateTimeStamp
  | plainLiteral
  | xmlLiteral
  /-- `rdfs:Literal`: no lexical forms. -/
  | literal
deriving Repr, Inhabited

/-- The kind of a datatype IRI of the OWL 2 datatype map, `none` for any
other IRI. -/
def dtKind (dt : IRI) : Option DtKind :=
  let xsd : List (String × DtKind) :=
    [("decimal", .decimal), ("integer", .integer none none),
     ("nonNegativeInteger", .integer (some 0) none),
     ("nonPositiveInteger", .integer none (some 0)),
     ("positiveInteger", .integer (some 1) none),
     ("negativeInteger", .integer none (some (-1))),
     ("long", .integer (some (-9223372036854775808)) (some 9223372036854775807)),
     ("int", .integer (some (-2147483648)) (some 2147483647)),
     ("short", .integer (some (-32768)) (some 32767)),
     ("byte", .integer (some (-128)) (some 127)),
     ("unsignedLong", .integer (some 0) (some 18446744073709551615)),
     ("unsignedInt", .integer (some 0) (some 4294967295)),
     ("unsignedShort", .integer (some 0) (some 65535)),
     ("unsignedByte", .integer (some 0) (some 255)),
     ("double", .float), ("float", .float),
     ("string", .string), ("normalizedString", .normalizedString), ("token", .token),
     ("language", .language), ("Name", .name), ("NCName", .ncName),
     ("NMTOKEN", .nmToken), ("boolean", .boolean), ("hexBinary", .hexBinary),
     ("base64Binary", .base64Binary), ("anyURI", .anyURI), ("dateTime", .dateTime),
     ("dateTimeStamp", .dateTimeStamp)]
  if dt == owlNs ++ "real" then some .real
  else if dt == owlNs ++ "rational" then some .rational
  else if dt == rdfPlainLiteral then some .plainLiteral
  else if dt == rdfNs ++ "XMLLiteral" then some .xmlLiteral
  else if dt == rdfsLiteral then some .literal
  else if dt.startsWith xsdNs then xsd.lookup (dt.drop xsdNs.length).toString
  else none

def isDigitC (c : Char) : Bool := '0' ≤ c && c ≤ '9'
def isHexC (c : Char) : Bool :=
  isDigitC c || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')
def isAlphaC (c : Char) : Bool := ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z')

/-- The value of a nonempty digit string. -/
def digitsVal (ds : List Char) : Nat :=
  ds.foldl (fun n c => 10 * n + (c.toNat - '0'.toNat)) 0

/-- `[+-]?[0-9]+` as an integer. -/
def parseInt (cs : List Char) : Option Int :=
  let (neg, ds) := match cs with
    | '-' :: ds => (true, ds)
    | '+' :: ds => (false, ds)
    | ds => (false, ds)
  if !ds.isEmpty && ds.all isDigitC then
    let n : Int := digitsVal ds
    some (if neg then -n else n)
  else none

/-- `[+-]?([0-9]+(.[0-9]*)?|.[0-9]+)`. -/
def isDecimal (cs : List Char) : Bool :=
  let ds := match cs with
    | '-' :: ds | '+' :: ds => ds
    | ds => ds
  match ds.splitOn '.' with
  | [a] => !a.isEmpty && a.all isDigitC
  | [a, b] => (!a.isEmpty || !b.isEmpty) && a.all isDigitC && b.all isDigitC
  | _ => false

/-- XSD `double` / `float` lexical forms. -/
def isFloat (cs : List Char) : Bool :=
  cs == "INF".toList || cs == "+INF".toList || cs == "-INF".toList || cs == "NaN".toList ||
  match cs.findIdx? (fun c => c == 'e' || c == 'E') with
  | none => isDecimal cs
  | some i => isDecimal (cs.take i) && (parseInt (cs.drop (i + 1))).isSome

def isLanguageTag (cs : List Char) : Bool :=
  match cs.splitOn '-' with
  | [] => false
  | p :: ps =>
    (!p.isEmpty && p.length ≤ 8 && p.all isAlphaC) &&
      ps.all fun q => !q.isEmpty && q.length ≤ 8 && q.all fun c => isAlphaC c || isDigitC c

/-- XML name characters, approximated: every non-ASCII character is
accepted. -/
def isNameStart (c : Char) : Bool := isAlphaC c || c == '_' || c == ':' || c.toNat ≥ 0x80
def isNameChar (c : Char) : Bool :=
  isNameStart c || isDigitC c || c == '-' || c == '.'

def isNormalized (cs : List Char) : Bool := cs.all fun c => c != '\t' && c != '\n' && c != '\r'

def isToken (cs : List Char) : Bool :=
  isNormalized cs && cs.head? != some ' ' && cs.getLast? != some ' ' &&
    !(cs.zip cs.tail).any fun (a, b) => a == ' ' && b == ' '

def isBase64 (cs : List Char) : Bool :=
  let ds := cs.filter (· != ' ')
  let isB (c : Char) := isAlphaC c || isDigitC c || c == '+' || c == '/'
  let body := ds.reverse.dropWhile (· == '=') |>.reverse
  ds.length % 4 == 0 && ds.length - body.length ≤ 2 && body.all isB

/-- Two digits as a number. -/
def twoDigits : List Char → Option Nat
  | [a, b] => if isDigitC a && isDigitC b then some (digitsVal [a, b]) else none
  | _ => none

def daysIn (year : Int) (month : Nat) : Nat :=
  if month == 2 then
    if (year % 4 == 0 && year % 100 != 0) || year % 400 == 0 then 29 else 28
  else if month == 4 || month == 6 || month == 9 || month == 11 then 30
  else 31

/-- A timezone: `Z` or `[+-]hh:mm` with `hh:mm` at most `14:00`. -/
def isTimezone : List Char → Bool
  | ['Z'] => true
  | s :: h1 :: h2 :: ':' :: m1 :: m2 :: [] =>
    (s == '+' || s == '-') &&
      match twoDigits [h1, h2], twoDigits [m1, m2] with
      | some h, some m => m ≤ 59 && (h < 14 || (h == 14 && m == 0))
      | _, _ => false
  | _ => false

/-- XSD `dateTime` lexical forms; `needTz` for `dateTimeStamp`. -/
def isDateTime (needTz : Bool) (cs : List Char) : Bool :=
  match cs.splitOn 'T' with
  | [date, time] =>
    let (neg, date) := match date with
      | '-' :: d => (true, d)
      | d => (false, d)
    match date.splitOn '-' with
    | [y, mo, d] =>
      let yOk := y.length ≥ 4 && y.all isDigitC && (y.length == 4 || y.head? != some '0')
      let year : Int := if neg then -(digitsVal y : Int) else digitsVal y
      match twoDigits mo, twoDigits d with
      | some mo', some d' =>
        let dateOk := yOk && 1 ≤ mo' && mo' ≤ 12 && 1 ≤ d' && d' ≤ daysIn year mo'
        -- the time is `hh:mm:ss(.s+)?` followed by an optional timezone
        let clock := time.take 8
        let rest := time.drop 8
        let (frac, tz) := match rest with
          | '.' :: r => (r.takeWhile isDigitC, r.dropWhile isDigitC)
          | r => ([], r)
        let fracOk := match rest with
          | '.' :: _ => !frac.isEmpty
          | _ => true
        match clock with
        | [h1, h2, ':', m1, m2, ':', s1, s2] =>
          match twoDigits [h1, h2], twoDigits [m1, m2], twoDigits [s1, s2] with
          | some h, some m, some s =>
            let timeOk := (h ≤ 23 && m ≤ 59 && s ≤ 59) ||
              (h == 24 && m == 0 && s == 0 && frac.all (· == '0'))
            dateOk && timeOk && fracOk &&
              (if tz.isEmpty then !needTz else isTimezone tz)
          | _, _, _ => false
        | _ => false
      | _, _ => false
    | _ => false
  | _ => false

/-- `[+-]?[0-9]+/[0-9]*[1-9][0-9]*` (`owl:rational`). -/
def isRational (cs : List Char) : Bool :=
  match cs.splitOn '/' with
  | [n, d] => (parseInt n).isSome && !d.isEmpty && d.all isDigitC && d.any (· != '0')
  | _ => false

/-- Whether `lex` is in the lexical space of a datatype of kind `k`. -/
def lexicalOk (k : DtKind) (lex : String) : Bool :=
  let cs := lex.toList
  match k with
  | .real | .literal => false
  | .rational => isRational cs
  | .decimal => isDecimal cs
  | .integer lo hi =>
    match parseInt cs with
    | some v => (lo.all fun l => l ≤ v) && (hi.all fun h => v ≤ h)
    | none => false
  | .float => isFloat cs
  | .string | .anyURI | .xmlLiteral => true
  | .normalizedString => isNormalized cs
  | .token => isToken cs
  | .language => isLanguageTag cs
  | .nmToken => !cs.isEmpty && cs.all isNameChar
  | .name => (cs.head?.map isNameStart).getD false && cs.all isNameChar
  | .ncName => (cs.head?.map isNameStart).getD false && cs.all isNameChar && !cs.contains ':'
  | .boolean => lex == "true" || lex == "false" || lex == "1" || lex == "0"
  | .hexBinary => cs.length % 2 == 0 && cs.all isHexC
  | .base64Binary => isBase64 cs
  | .dateTime => isDateTime false cs
  | .dateTimeStamp => isDateTime true cs
  | .plainLiteral =>
    -- `text@lang`, split at the last `@`; the tag may be empty
    match (cs.reverse.splitOn '@') with
    | [] | [_] => false
    | tag :: _ => tag.isEmpty || isLanguageTag tag.reverse

/-- Why a literal is ill-typed for the OWL 2 datatype map, if it is. A
literal whose datatype is outside the map is accepted (its datatype may be
introduced by `DatatypeDefinition`); the semantics gives it the value the
abstract datatype map gives. -/
def literalProblem (l : Literal) : Option String :=
  match l.lang with
  | some tag =>
    if isLanguageTag tag.toList then none else some s!"bad language tag @{tag}"
  | none =>
    match dtKind l.datatype with
    | some k =>
      if lexicalOk k l.lexical then none
      else some s!"\"{l.lexical}\" is not a lexical form of <{l.datatype}>"
    | none => none

/-- The facet groups of the OWL 2 datatype map (structural specification,
section 4). -/
def numericFacets : List String :=
  ["minInclusive", "maxInclusive", "minExclusive", "maxExclusive"]
def lengthFacets : List String := ["length", "minLength", "maxLength"]

/-- The facets a datatype of kind `k` admits (local names in the `xsd:`
namespace, plus `rdf:langRange` for `rdf:PlainLiteral`). -/
def facetsOf : DtKind → List IRI
  | .real | .rational | .decimal | .integer .. | .float | .dateTime | .dateTimeStamp =>
    numericFacets.map (xsdNs ++ ·)
  | .string | .normalizedString | .token | .language | .name | .ncName | .nmToken | .anyURI =>
    (lengthFacets ++ ["pattern"]).map (xsdNs ++ ·)
  | .plainLiteral => (lengthFacets ++ ["pattern"]).map (xsdNs ++ ·) ++ [rdfNs ++ "langRange"]
  | .hexBinary | .base64Binary => lengthFacets.map (xsdNs ++ ·)
  | .boolean | .xmlLiteral | .literal => []

/-- Why a facet restriction `DatatypeRestriction(dt ... f l ...)` is
rejected, if it is: the datatype is outside the map, the facet does not
apply to it, or a length facet has a value that is not a nonnegative
integer. -/
def facetProblem (dt f : IRI) (l : Literal) : Option String :=
  match dtKind dt with
  | none => some s!"facet <{f}> on datatype <{dt}> outside the OWL 2 datatype map"
  | some k =>
    if !(facetsOf k).contains f then some s!"facet <{f}> does not apply to <{dt}>"
    else if (lengthFacets.map (xsdNs ++ ·)).contains f then
      match dtKind l.datatype, parseInt l.lexical.toList with
      | some (.integer ..), some v => if v ≥ 0 then none else some s!"negative length facet"
      | _, _ => some s!"facet <{f}> needs a nonnegative integer"
    else none

end Datatypes

/-! ## Expressions -/

/-- The inverse of an object-property expression. The top and bottom
properties are their own inverses. -/
def invert : ObjProp → ObjProp
  | .named r => .inv r
  | .inv r => .named r
  | .top => .top
  | .bot => .bot

/-- An object-property expression. -/
def toRole (pfx : Prefixes) (n : Node) : ConvM ObjProp :=
  match n with
  | .list "ObjectInverseOf" args =>
    if h : args.size = 1 then return invert (← toRole pfx args[0])
    else throw "syntax error: ObjectInverseOf takes one property"
  | .list h _ => outOfFragment s!"object property expression {if h == "" then "(anonymous list)" else h}"
  | _ => do
    let r ← iriOf pfx n
    if r == owlTopObjectProperty then return .top
    else if r == owlBottomObjectProperty then return .bot
    else return .named r
termination_by sizeOf n
decreasing_by
  simp_wf
  have := Array.sizeOf_getElem args 0 (by omega)
  omega

/-- A data-property expression (an IRI). -/
def toDataProp (pfx : Prefixes) (n : Node) : ConvM DataProp :=
  match n with
  | .list h _ => throw s!"syntax error: expected a data property, found {if h == "" then "an anonymous list" else h}"
  | _ => do
    let p ← iriOf pfx n
    if p == owlTopDataProperty then return .top
    else if p == owlBottomDataProperty then return .bot
    else return .named p

/-- An individual: a node ID `_:x` or a named individual. -/
def toIndividual (pfx : Prefixes) (n : Node) : ConvM Individual :=
  match n with
  | .word w =>
    if w.startsWith "_:" then return .anon (w.drop 2).toString
    else return .named (← iriOf pfx n)
  | _ => return .named (← iriOf pfx n)

/-- A literal; ill-typed literals (for the OWL 2 datatype map) are
rejected. -/
def toLiteral (pfx : Prefixes) (n : Node) : ConvM Literal := do
  let l ← match n with
    | .literal lex .plain => pure { lexical := lex, datatype := xsdString, lang := none }
    | .literal lex (.lang tag) => pure { lexical := lex, datatype := rdfPlainLiteral, lang := some tag }
    | .literal lex (.typed (.full s)) =>
      pure { lexical := lex, datatype := ← iriOf pfx (.iri s), lang := none }
    | .literal lex (.typed (.abbreviated w)) =>
      pure { lexical := lex, datatype := ← iriOf pfx (.word w), lang := none }
    | n => throw s!"syntax error: expected a literal, found {n.describe}"
  match literalProblem l with
  | some why => throw s!"ill-typed literal: {why}"
  | none => return l

/-- A cardinality: a nonnegative integer. -/
def toNat (n : Node) : ConvM Nat :=
  match n with
  | .word w =>
    if !w.isEmpty && w.all Char.isDigit then return digitsVal w.toList
    else throw s!"syntax error: {w} is not a nonnegative integer"
  | n => throw s!"syntax error: expected a nonnegative integer, found {n.describe}"

/-- A data range. -/
def toDataRange (pfx : Prefixes) (n : Node) : ConvM DataRange :=
  match n with
  | .list "DataIntersectionOf" args => do
    if args.size < 2 then throw "syntax error: DataIntersectionOf needs two operands"
    let rs ← args.attach.mapM fun ⟨a, _⟩ => toDataRange pfx a
    return .and rs.toList
  | .list "DataUnionOf" args => do
    if args.size < 2 then throw "syntax error: DataUnionOf needs two operands"
    let rs ← args.attach.mapM fun ⟨a, _⟩ => toDataRange pfx a
    return .or rs.toList
  | .list "DataComplementOf" args =>
    if h : args.size = 1 then return .not (← toDataRange pfx args[0])
    else throw "syntax error: DataComplementOf takes one operand"
  | .list "DataOneOf" args => do
    if args.size < 1 then throw "syntax error: DataOneOf needs a literal"
    return .oneOf (← args.mapM (toLiteral pfx)).toList
  | .list "DatatypeRestriction" args => do
    if h : 0 < args.size then
      let dt ← iriOf pfx args[0]
      let rest := args.extract 1 args.size
      if rest.size == 0 || rest.size % 2 != 0 then
        throw "syntax error: DatatypeRestriction needs facet and literal pairs"
      let mut fs : Array (IRI × Literal) := #[]
      for k in [0:rest.size / 2] do
        let f ← iriOf pfx rest[2 * k]!
        let l ← toLiteral pfx rest[2 * k + 1]!
        match facetProblem dt f l with
        | some why => throw s!"bad facet: {why}"
        | none => fs := fs.push (f, l)
      return .restriction dt fs.toList
    else throw "syntax error: DatatypeRestriction needs a datatype"
  | .list h _ => throw s!"syntax error: unknown data range {if h == "" then "(anonymous list)" else h}"
  | _ => return .datatype (← iriOf pfx n)
termination_by sizeOf n
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := Array.sizeOf_lt_of_mem ‹_ ∈ args›; omega)
    | (have := Array.sizeOf_getElem args 0 (by omega); omega)

/-- The reason for rejecting an unknown class constructor. -/
def classConstructRejection (h : String) : String :=
  if h == "" then "anonymous list in a class position"
  else s!"class expression {h}"

/-- The property and data range of a unary `DataSomeValuesFrom` /
`DataAllValuesFrom`; more than one property is an n-ary data range. -/
def unaryData (pfx : Prefixes) (h : String) (args : Array Node) : ConvM (DataProp × DataRange) :=
  if hs : args.size = 2 then do
    return (← toDataProp pfx args[0], ← toDataRange pfx args[1])
  else if args.size > 2 then
    outOfFragment s!"{h} with {args.size - 1} data properties (n-ary data range)"
  else throw s!"syntax error: {h} takes a data property and a data range"

/-- The number, property and data range of a data cardinality restriction
(unqualified: `rdfs:Literal`). -/
def dataCard (pfx : Prefixes) (h : String) (args : Array Node) :
    ConvM (Nat × DataProp × DataRange) :=
  if hs : args.size = 2 then do
    return (← toNat args[0], ← toDataProp pfx args[1], .datatype rdfsLiteral)
  else if hs : args.size = 3 then do
    return (← toNat args[0], ← toDataProp pfx args[1], ← toDataRange pfx args[2])
  else throw s!"syntax error: {h} takes a number, a data property and an optional data range"

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
  | .list "ObjectOneOf" args => do
    if args.size < 1 then throw "syntax error: ObjectOneOf needs an individual"
    return .oneOf (← args.mapM (toIndividual pfx)).toList
  | .list "ObjectHasValue" args =>
    if h : args.size = 2 then return .hasValue (← toRole pfx args[0]) (← toIndividual pfx args[1])
    else throw "syntax error: ObjectHasValue takes a property and an individual"
  | .list "ObjectHasSelf" args =>
    if h : args.size = 1 then return .hasSelf (← toRole pfx args[0])
    else throw "syntax error: ObjectHasSelf takes a property"
  | .list "ObjectMinCardinality" args =>
    if h : args.size = 2 then return .min (← toNat args[0]) (← toRole pfx args[1]) .thing
    else if h : args.size = 3 then
      return .min (← toNat args[0]) (← toRole pfx args[1]) (← toClass pfx args[2])
    else throw "syntax error: ObjectMinCardinality takes a number, a property and an optional class"
  | .list "ObjectMaxCardinality" args =>
    if h : args.size = 2 then return .max (← toNat args[0]) (← toRole pfx args[1]) .thing
    else if h : args.size = 3 then
      return .max (← toNat args[0]) (← toRole pfx args[1]) (← toClass pfx args[2])
    else throw "syntax error: ObjectMaxCardinality takes a number, a property and an optional class"
  | .list "ObjectExactCardinality" args =>
    if h : args.size = 2 then return .exact (← toNat args[0]) (← toRole pfx args[1]) .thing
    else if h : args.size = 3 then
      return .exact (← toNat args[0]) (← toRole pfx args[1]) (← toClass pfx args[2])
    else throw "syntax error: ObjectExactCardinality takes a number, a property and an optional class"
  | .list "DataSomeValuesFrom" args => do
    let (p, r) ← unaryData pfx "DataSomeValuesFrom" args
    return .dataSome p r
  | .list "DataAllValuesFrom" args => do
    let (p, r) ← unaryData pfx "DataAllValuesFrom" args
    return .dataAll p r
  | .list "DataHasValue" args =>
    if h : args.size = 2 then return .dataHasValue (← toDataProp pfx args[0]) (← toLiteral pfx args[1])
    else throw "syntax error: DataHasValue takes a data property and a literal"
  | .list "DataMinCardinality" args => do
    let (k, p, r) ← dataCard pfx "DataMinCardinality" args
    return .dataMin k p r
  | .list "DataMaxCardinality" args => do
    let (k, p, r) ← dataCard pfx "DataMaxCardinality" args
    return .dataMax k p r
  | .list "DataExactCardinality" args => do
    let (k, p, r) ← dataCard pfx "DataExactCardinality" args
    return .dataExact k p r
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
    | (have := Array.sizeOf_getElem args 2 (by omega); omega)

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
  if h == "DLSafeRule" then s!"{h} (rule)"
  else if h == "" then "anonymous list in an axiom position"
  else s!"axiom {h}"

def arityError {α : Type} (h : String) : ConvM α :=
  throw s!"syntax error: wrong number of operands for {h}"

/-- A declaration: `none` for the declarations of `owl:Thing`,
`owl:Nothing` and the top and bottom object and data properties, which
are not IRIs of the semantics. -/
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
  | #[.list "DataProperty" #[x]] =>
    let p ← iriOf pfx x
    if p == owlTopDataProperty || p == owlBottomDataProperty then return none
    return some (.declareDataProperty p)
  | #[.list "NamedIndividual" #[x]] => return some (.declareNamedIndividual (← iriOf pfx x))
  | #[.list "Datatype" #[x]] => return some (.declareDatatype (← iriOf pfx x))
  | #[.list "AnnotationProperty" #[x]] =>
    return some (.declareAnnotationProperty (← iriOf pfx x))
  | #[.list k #[_]] => throw s!"syntax error: unknown entity kind {k} in Declaration"
  | _ => arityError "Declaration"

/-- One axiom (a child of `Ontology(...)` that is a list): `some` for an
axiom of the model, `none` for a skipped one. -/
def toAxiom (pfx : Prefixes) (h : String) (args : Array Node) : ConvM (Option Axiom) := do
  if skippedAxioms.contains h then return none
  let ops ← operands h args
  let classes : ConvM (List ClassExpr) := do
    if ops.size < 2 then arityError h
    return (← ops.mapM (toClass pfx)).toList
  let roles : ConvM (List ObjProp) := do
    if ops.size < 2 then arityError h
    return (← ops.mapM (toRole pfx)).toList
  let dataProps : ConvM (List DataProp) := do
    if ops.size < 2 then arityError h
    return (← ops.mapM (toDataProp pfx)).toList
  let individuals : ConvM (List Individual) := do
    if ops.size < 2 then arityError h
    return (← ops.mapM (toIndividual pfx)).toList
  let oneRole : ConvM ObjProp := do
    match ops with
    | #[r] => toRole pfx r
    | _ => arityError h
  match h with
  | "Declaration" => toDeclaration pfx ops
  | "SubClassOf" =>
    match ops with
    | #[c, d] => return some (.subClassOf (← toClass pfx c) (← toClass pfx d))
    | _ => arityError h
  | "EquivalentClasses" => return some (.equivalentClasses (← classes))
  | "DisjointClasses" => return some (.disjointClasses (← classes))
  | "DisjointUnion" =>
    if hs : 3 ≤ ops.size then
      let a ← iriOf pfx ops[0]
      if a == owlThing || a == owlNothing then
        outOfFragment "DisjointUnion of owl:Thing or owl:Nothing (the class must be a class IRI)"
      let cs ← (ops.extract 1 ops.size).mapM (toClass pfx)
      return some (.disjointUnion a cs.toList)
    else arityError h
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
  | "DisjointObjectProperties" => return some (.disjointObjectProperties (← roles))
  | "InverseObjectProperties" =>
    match ops with
    | #[r, s] => return some (.inverseObjectProperties (← toRole pfx r) (← toRole pfx s))
    | _ => arityError h
  | "TransitiveObjectProperty" => return some (.transitive (← oneRole))
  | "SymmetricObjectProperty" => return some (.symmetric (← oneRole))
  | "FunctionalObjectProperty" => return some (.functional (← oneRole))
  | "InverseFunctionalObjectProperty" => return some (.inverseFunctional (← oneRole))
  | "ReflexiveObjectProperty" => return some (.reflexive (← oneRole))
  | "IrreflexiveObjectProperty" => return some (.irreflexive (← oneRole))
  | "AsymmetricObjectProperty" => return some (.asymmetric (← oneRole))
  | "SubDataPropertyOf" =>
    match ops with
    | #[p, q] => return some (.subDataPropertyOf (← toDataProp pfx p) (← toDataProp pfx q))
    | _ => arityError h
  | "EquivalentDataProperties" => return some (.equivalentDataProperties (← dataProps))
  | "DisjointDataProperties" => return some (.disjointDataProperties (← dataProps))
  | "DataPropertyDomain" =>
    match ops with
    | #[p, c] => return some (.dataDomain (← toDataProp pfx p) (← toClass pfx c))
    | _ => arityError h
  | "DataPropertyRange" =>
    match ops with
    | #[p, r] => return some (.dataRange (← toDataProp pfx p) (← toDataRange pfx r))
    | _ => arityError h
  | "FunctionalDataProperty" =>
    match ops with
    | #[p] => return some (.functionalData (← toDataProp pfx p))
    | _ => arityError h
  | "DatatypeDefinition" =>
    match ops with
    | #[t, r] => return some (.datatypeDefinition (← iriOf pfx t) (← toDataRange pfx r))
    | _ => arityError h
  | "HasKey" =>
    match ops with
    | #[c, .list "" os, .list "" ds] =>
      return some (.hasKey (← toClass pfx c) (← os.mapM (toRole pfx)).toList
        (← ds.mapM (toDataProp pfx)).toList)
    | _ => throw "syntax error: HasKey takes a class and two parenthesised property lists"
  | "SameIndividual" => return some (.sameIndividual (← individuals))
  | "DifferentIndividuals" => return some (.differentIndividuals (← individuals))
  | "ClassAssertion" =>
    match ops with
    | #[c, a] => return some (.classAssertion (← toClass pfx c) (← toIndividual pfx a))
    | _ => arityError h
  | "ObjectPropertyAssertion" =>
    match ops with
    | #[r, a, b] => return some (.objectPropertyAssertion (← toRole pfx r)
        (← toIndividual pfx a) (← toIndividual pfx b))
    | _ => arityError h
  | "NegativeObjectPropertyAssertion" =>
    match ops with
    | #[r, a, b] => return some (.negativeObjectPropertyAssertion (← toRole pfx r)
        (← toIndividual pfx a) (← toIndividual pfx b))
    | _ => arityError h
  | "DataPropertyAssertion" =>
    match ops with
    | #[p, a, l] => return some (.dataPropertyAssertion (← toDataProp pfx p)
        (← toIndividual pfx a) (← toLiteral pfx l))
    | _ => arityError h
  | "NegativeDataPropertyAssertion" =>
    match ops with
    | #[p, a, l] => return some (.negativeDataPropertyAssertion (← toDataProp pfx p)
        (← toIndividual pfx a) (← toLiteral pfx l))
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

/-- Parse an OWL 2 functional-syntax document. `.ok O` gives the ontology;
`.error reason` says why the text is rejected (a syntax error, an
ill-typed literal or bad facet, or the first construct outside the model:
imports, rules, n-ary data ranges). -/
def parse (text : String) : Except String Ontology :=
  let bs := text.toUTF8
  Parse.readDocument bs (bs.size + 1) 0 Parse.initialPrefixes []

end ContextCalculus.OWL
