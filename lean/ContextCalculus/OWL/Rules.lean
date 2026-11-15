import ContextCalculus.OWL.Parse
import ContextCalculus.OWL.Names

/-!
# DL-safe rules (stage C5, item 3)

The OWL 2 functional syntax allows SWRL rules as `DLSafeRule(Body(...)
Head(...))` axioms. This file adds them to the model beside the ontology,
without changing `Axiom` (so every statement about `Axiom` and `Ontology`
stays as it is): an `OntologyR` is an ontology and a list of rules.

## Atoms

In: `ClassAtom(C x)` (any class expression), `ObjectPropertyAtom(r x y)`,
`DataPropertyAtom(p x d)`, `DataRangeAtom(R d)`, `SameIndividualAtom(x y)`,
`DifferentIndividualsAtom(x y)`, `BuiltInAtom(f d1 ... dn)`. An individual
argument is `Variable(v)` or an individual, a data argument `Variable(v)` or
a literal.

## Semantics (DL-safe)

Individual variables range over the **named individuals** of the ontology
and its rules (`OntologyR.named`); this is DL-safety. Data variables range
over all data values. A built-in atom is read by a relation
`bi : IRI → List D.Val → Prop` that every statement takes as a parameter,
so no meaning of a SWRL built-in is fixed (the encodings of
`OWLFrontend/RuleGround.lean` never see a built-in atom of an instance they
keep). A rule holds when every assignment of named individuals to its
individual variables and data values to the data variables that makes the
body true makes every head atom true.

## Parser

`parseR` reads a document as `OWL.parse` does and collects the
`DLSafeRule` axioms as rules (`OWL.parse` still rejects them).
-/

namespace ContextCalculus.OWL

/-- An individual argument of an atom. -/
inductive IArg where
  | var (v : IRI)
  | ind (i : Individual)
deriving DecidableEq, Repr, Inhabited

/-- A data argument of an atom. -/
inductive DArg where
  | var (v : IRI)
  | lit (l : Literal)
deriving Repr, Inhabited

/-- A rule atom. -/
inductive RAtom where
  | cls (c : ClassExpr) (x : IArg)
  | obj (r : ObjProp) (x y : IArg)
  | data (p : DataProp) (x : IArg) (d : DArg)
  | drange (r : DataRange) (d : DArg)
  | same (x y : IArg)
  | diff (x y : IArg)
  | builtin (f : IRI) (args : List DArg)
deriving Repr, Inhabited

/-- A DL-safe rule. -/
structure DLRule where
  body : List RAtom
  head : List RAtom
deriving Repr, Inhabited

/-- An ontology with rules. -/
structure OntologyR where
  onto : Ontology
  rules : List DLRule
deriving Repr, Inhabited

/-- The reading of the SWRL built-ins. -/
abbrev BuiltIns (D : DatatypeMap) := IRI → List D.Val → Prop

def IArg.vars : IArg → List IRI
  | .var v => [v]
  | .ind _ => []

def IArg.named : IArg → List IRI
  | .var _ => []
  | .ind i => i.namedIRI

def RAtom.ivars : RAtom → List IRI
  | .cls _ x => x.vars
  | .obj _ x y | .same x y | .diff x y => x.vars ++ y.vars
  | .data _ x _ => x.vars
  | .drange .. | .builtin .. => []

def RAtom.named : RAtom → List IRI
  | .cls c x => c.namedIndividuals ++ x.named
  | .obj _ x y | .same x y | .diff x y => x.named ++ y.named
  | .data _ x _ => x.named
  | .drange .. | .builtin .. => []

/-- The individual variables of a rule. -/
def DLRule.ivars (ρ : DLRule) : List IRI := (ρ.body ++ ρ.head).flatMap RAtom.ivars

/-- The named individuals a rule mentions. -/
def DLRule.named (ρ : DLRule) : List IRI := (ρ.body ++ ρ.head).flatMap RAtom.named

/-- The named individuals of an ontology with rules. -/
def OntologyR.named (O : OntologyR) : List IRI :=
  O.onto.namedIndividuals ++ O.rules.flatMap DLRule.named

section Sem

variable {D : DatatypeMap} {Domain : Type} (bi : BuiltIns D) (I : Interp D Domain)

/-- The value of an individual argument. -/
def IArg.val (σ : IRI → Domain) : IArg → Domain
  | .var v => σ v
  | .ind i => I.ind i

/-- A data argument has the value `w`. -/
def DArg.is (δ : IRI → D.Val) : DArg → D.Val → Prop
  | .var v => fun w => δ v = w
  | .lit l => fun w => D.literal l = some w

/-- Satisfaction of an atom under an assignment. -/
def RAtom.sat (σ : IRI → Domain) (δ : IRI → D.Val) : RAtom → Prop
  | .cls c x => I.ext c (x.val I σ)
  | .obj r x y => I.prop r (x.val I σ) (y.val I σ)
  | .data p x d => ∃ w, d.is δ w ∧ I.dp p (x.val I σ) w
  | .drange r d => ∃ w, d.is δ w ∧ I.drExt r w
  | .same x y => x.val I σ = y.val I σ
  | .diff x y => x.val I σ ≠ y.val I σ
  | .builtin f args => ∃ ws : List D.Val, args.length = ws.length ∧
      (∀ p ∈ args.zip ws, p.1.is δ p.2) ∧ bi f ws

/-- **A DL-safe rule holds**: individual variables over the named
individuals `N`, data variables over all data values. -/
def DLRule.sat (N : List IRI) (ρ : DLRule) : Prop :=
  ∀ (σ : IRI → Domain) (δ : IRI → D.Val), (∀ v ∈ ρ.ivars, I.IsNamed N (σ v)) →
    (∀ a ∈ ρ.body, a.sat bi I σ δ) → ∀ a ∈ ρ.head, a.sat bi I σ δ

end Sem

/-- A model of an ontology with rules. -/
def ModelR {D : DatatypeMap} {Domain : Type} (bi : BuiltIns D) (O : OntologyR)
    (I : Interp D Domain) : Prop :=
  (∀ ax ∈ O.onto.axioms, I.sat O.named ax) ∧ ∀ ρ ∈ O.rules, ρ.sat bi I O.named

/-- Without rules, a model is a model of the ontology. -/
theorem modelR_nil {D : DatatypeMap} {Domain : Type} (bi : BuiltIns D) (O : Ontology)
    (I : Interp D Domain) : ModelR bi ⟨O, []⟩ I ↔ Model O I := by
  simp [ModelR, Model, OntologyR.named]

/-! ## Parser -/

namespace Parse

/-- An individual argument. -/
def toIArg (pfx : Prefixes) (n : Node) : ConvM IArg :=
  match n with
  | .list "Variable" #[v] => return .var (← iriOf pfx v)
  | n => return .ind (← toIndividual pfx n)

/-- A data argument. -/
def toDArg (pfx : Prefixes) (n : Node) : ConvM DArg :=
  match n with
  | .list "Variable" #[v] => return .var (← iriOf pfx v)
  | n => return .lit (← toLiteral pfx n)

/-- An atom. -/
def toAtom (pfx : Prefixes) (n : Node) : ConvM RAtom :=
  match n with
  | .list "ClassAtom" #[c, x] => return .cls (← toClass pfx c) (← toIArg pfx x)
  | .list "ObjectPropertyAtom" #[r, x, y] =>
    return .obj (← toRole pfx r) (← toIArg pfx x) (← toIArg pfx y)
  | .list "DataPropertyAtom" #[p, x, d] =>
    return .data (← toDataProp pfx p) (← toIArg pfx x) (← toDArg pfx d)
  | .list "DataRangeAtom" #[r, d] => return .drange (← toDataRange pfx r) (← toDArg pfx d)
  | .list "SameIndividualAtom" #[x, y] => return .same (← toIArg pfx x) (← toIArg pfx y)
  | .list "DifferentIndividualsAtom" #[x, y] => return .diff (← toIArg pfx x) (← toIArg pfx y)
  | .list "BuiltInAtom" args => do
    if h : 0 < args.size then
      return .builtin (← iriOf pfx args[0]) (← (args.extract 1 args.size).toList.mapM (toDArg pfx))
    else throw "syntax error: BuiltInAtom needs an IRI"
  | n => throw s!"syntax error: unknown rule atom {n.describe}"

/-- A `DLSafeRule(...)`: annotations, `Body(...)`, `Head(...)`. -/
def toRule (pfx : Prefixes) (args : Array Node) : ConvM DLRule := do
  let ops ← operands "DLSafeRule" args
  match ops with
  | #[.list "Body" bs, .list "Head" hs] =>
    return ⟨← bs.toList.mapM (toAtom pfx), ← hs.toList.mapM (toAtom pfx)⟩
  | _ => throw "syntax error: DLSafeRule takes Body(...) and Head(...)"

/-- `readOntologyBody` with the rules collected. -/
def readOntologyBodyR (bs : ByteArray) (pfx : Prefixes) (fuel i : Nat) (phase : Phase)
    (cache : Cache) (acc : Array Axiom) (rs : Array DLRule) :
    Except String (Array Axiom × Array DLRule × Nat) :=
  match fuel with
  | 0 => .error "syntax error: input too long"
  | fuel + 1 => do
    let (t, j) ← nextTok bs i
    match t with
    | .rparen => return (acc, rs, j)
    | .eof => throw "syntax error: unexpected end of input in Ontology"
    | _ =>
      let (node, j) ← readNode bs i
      match node, phase with
      | .list "Import" _, _ => throw "out of fragment: Import (imports are not resolved)"
      | .list "Annotation" _, .axioms =>
        throw "syntax error: ontology Annotation after an axiom"
      | .list "Annotation" _, _ =>
        readOntologyBodyR bs pfx fuel j .annotations cache acc rs
      | .list "DLSafeRule" args, _ =>
        let (ρ, cache) ← (toRule pfx args).run cache
        readOntologyBodyR bs pfx fuel j .axioms cache acc (rs.push ρ)
      | .list h args, _ =>
        let (ax, cache) ← (toAxiom pfx h args).run cache
        let acc := match ax with
          | some a => acc.push a
          | none => acc
        readOntologyBodyR bs pfx fuel j .axioms cache acc rs
      | n, .iris seen =>
        if seen < 2 then
          let (_, cache) ← (iriOf pfx n).run cache
          readOntologyBodyR bs pfx fuel j (.iris (seen + 1)) cache acc rs
        else throw s!"syntax error: unexpected {n.describe} in Ontology"
      | n, _ => throw s!"syntax error: unexpected {n.describe} in Ontology"

/-- `readDocument` with the rules collected. -/
def readDocumentR (bs : ByteArray) (fuel i : Nat) (pfx : Prefixes) (declared : List String) :
    Except String OntologyR :=
  match fuel with
  | 0 => .error "syntax error: input too long"
  | fuel + 1 => do
    let (t, j) ← nextTok bs i
    match t with
    | .word "Prefix" =>
      match ← readNode bs i with
      | (.list "Prefix" args, k) =>
        let (pfx, declared) ← addPrefix pfx declared args
        readDocumentR bs fuel k pfx declared
      | _ => throw "syntax error: malformed prefix declaration"
    | .word "Ontology" =>
      let (open_, k) ← nextTok bs j
      match open_ with
      | .lparen =>
        let (axioms, rs, k) ← readOntologyBodyR bs pfx (bs.size + 1) k (.iris 0) {} #[] #[]
        match (← nextTok bs k).1 with
        | .eof => return { onto := { axioms := axioms.toList }, rules := rs.toList }
        | _ => throw "syntax error: content after the closing ) of Ontology"
      | _ => throw "syntax error: Ontology must be followed by ("
    | .eof => throw "syntax error: no Ontology(...) in the document"
    | .word w => throw s!"syntax error: unexpected {w} before Ontology"
    | _ => throw "syntax error: unexpected token before Ontology"

end Parse

/-- Parse a document with its `DLSafeRule` axioms as rules. -/
def parseR (text : String) : Except String OntologyR :=
  let bs := text.toUTF8
  Parse.readDocumentR bs (bs.size + 1) 0 Parse.initialPrefixes []

/-! ## Printer -/

def IArg.text : IArg → String
  | .var v => s!"Variable(<{v}>)"
  | .ind (.named a) => s!"<{a}>"
  | .ind (.anon x) => s!"_:{x}"

/-- The kind of an atom, for messages. -/
def RAtom.kind : RAtom → String
  | .cls .. => "ClassAtom"
  | .obj .. => "ObjectPropertyAtom"
  | .data .. => "DataPropertyAtom"
  | .drange .. => "DataRangeAtom"
  | .same .. => "SameIndividualAtom"
  | .diff .. => "DifferentIndividualsAtom"
  | .builtin .. => "BuiltInAtom"

end ContextCalculus.OWL

#print axioms ContextCalculus.OWL.modelR_nil
