/-!
# OWL 2 direct semantics (v1.7.0 stage C0)

Syntax and direct semantics of OWL 2 DL, after the W3C OWL 2 Structural
Specification and the OWL 2 Direct Semantics (second edition). The model
covers every construct of the structural specification except two:

* annotations (the parser drops them; they carry no semantic condition), and
* n-ary data ranges of arity greater than one (the parser rejects them, so
  `DataSomeValuesFrom` and `DataAllValuesFrom` take one data property).

Up to v1.6.3 this file modelled only the SHI-with-chains fragment `F` of
`docs/V1.6.2-FRONTEND-PLAN.md`. The constructors of that fragment keep their
names, their order and their semantics; the new constructors come after
them, and `Fragment.lean`, `FragmentSRI.lean` and the translations decline
every new one.

IRIs are the expanded strings the parser produces: two spellings denote the
same entity exactly when they expand to the same string (OWL 2 structural
specification, section 2.4). The parser maps `owl:Thing`, `owl:Nothing`,
`owl:topObjectProperty`, `owl:bottomObjectProperty`, `owl:topDataProperty`
and `owl:bottomDataProperty` to dedicated constructors, so a class or
property IRI here is never one of them.

## Interpretations

An interpretation (`Interp D Domain`) fixes, as in Direct Semantics
section 2.2:

* a nonempty object domain `Domain` (the nonemptiness is a hypothesis of the
  entailment notions below),
* a set of objects per class IRI and a binary relation per object-property
  IRI,
* an object per individual, named or anonymous,
* a relation between objects and data values per data-property IRI,
* a set of data values per datatype IRI outside the datatype map.

Anonymous individuals are existentially quantified in the direct semantics.
Every entailment notion below quantifies over all interpretations, so giving
anonymous individuals a free value in the interpretation (`ind (.anon _)`)
yields the same entailments.

## Datatype maps

The data domain and the datatypes come from a `DatatypeMap` `D`: its value
type `D.Val` is the data domain, `D.datatype` gives the value space of each
datatype of the map, `D.literal` the value of each literal (`none` for an
ill-typed literal, or a literal whose datatype the map does not know), and
`D.facet dt f l` the set of values of `dt` that satisfy the facet `f` with
the literal `l` (`none` for an unknown facet). `rdfs:Literal` denotes all of
`D.Val`. A datatype IRI that the map does not contain is interpreted freely
by the interpretation (`Interp.dtype`); `DatatypeDefinition` axioms
constrain it.

The semantics never rejects: an ill-typed literal denotes no value, and a
facet restriction with an unknown facet denotes the empty set. The parser
is where malformed input is rejected.

`EntailsSub`, `Unsatisfiable`, `Inconsistent` and `Entails` quantify over
every datatype map. That gives fewer entailments than the OWL 2 datatype
map does (for example, an empty integer interval is not unsatisfiable
here); stage C4 of the v1.7.0 plan fixes the map.

## Global restrictions

Placeholder: the global restrictions of OWL 2 DL (structural specification,
section 11: simple properties in cardinalities, functionality, Self,
disjointness, irreflexivity and asymmetry; regularity of the property
hierarchy; restrictions on anonymous individuals and on datatype
definitions) are not stated in this file. The semantics below is defined
for every ontology, inside OWL 2 DL or not.

## Lists and sets

The structural specification treats the operands of n-ary constructs as
sets or lists, depending on the construct. Here every operand collection is
a `List`; the semantics of each constructor does not depend on order, and
the pairwise constructs (`DisjointClasses`, `DisjointObjectProperties`,
`DisjointDataProperties`, `DifferentIndividuals`, `DisjointUnion`) read
"`j ≠ k`" of the direct semantics as `List.Pairwise` over positions.
-/

namespace ContextCalculus.OWL

abbrev IRI := String

/-- `rdfs:Literal`, the datatype whose extension is the whole data domain. -/
def rdfsLiteral : IRI := "http://www.w3.org/2000/01/rdf-schema#Literal"

/-- An individual: a named individual (an IRI) or an anonymous individual
(a node ID, `_:x` in the functional syntax). -/
inductive Individual where
  | named (iri : IRI)
  | anon (nodeID : String)
deriving DecidableEq, Repr, Inhabited

/-- A literal: lexical form, datatype IRI and optional language tag. The
parser reads `"abc"` as datatype `xsd:string` and `"abc"@en` as datatype
`rdf:PlainLiteral` with language tag `en` (structural specification,
section 5.7). -/
structure Literal where
  lexical : String
  datatype : IRI
  lang : Option String
deriving DecidableEq, Repr, Inhabited

inductive ObjProp where
  | named (role : IRI)
  | inv (role : IRI)
  /-- `owl:topObjectProperty`: the full relation. -/
  | top
  /-- `owl:bottomObjectProperty`: the empty relation. -/
  | bot
deriving DecidableEq, Repr, Inhabited

/-- Data property expressions: a data-property IRI, `owl:topDataProperty`
(every object to every value) or `owl:bottomDataProperty` (empty). -/
inductive DataProp where
  | named (prop : IRI)
  | top
  | bot
deriving DecidableEq, Repr, Inhabited

/-- Unary data ranges (structural specification, section 7). -/
inductive DataRange where
  /-- A datatype IRI; `rdfs:Literal` is the whole data domain. -/
  | datatype (dt : IRI)
  | and (ranges : List DataRange)
  | or (ranges : List DataRange)
  | not (range : DataRange)
  | oneOf (literals : List Literal)
  /-- `DatatypeRestriction(dt f1 l1 ... fn ln)`: facet IRI and literal. -/
  | restriction (dt : IRI) (facets : List (IRI × Literal))
deriving Repr, Inhabited

inductive ClassExpr where
  | cls (name : IRI)
  | thing
  | nothing
  | and (conjuncts : List ClassExpr)
  | or (disjuncts : List ClassExpr)
  | not (operand : ClassExpr)
  | some (role : ObjProp) (filler : ClassExpr)
  | all (role : ObjProp) (filler : ClassExpr)
  /-- `ObjectOneOf(a1 ... an)`. -/
  | oneOf (members : List Individual)
  /-- `ObjectHasValue(r a)`. -/
  | hasValue (role : ObjProp) (ind : Individual)
  /-- `ObjectHasSelf(r)`. -/
  | hasSelf (role : ObjProp)
  /-- `ObjectMinCardinality(n r C)`; the unqualified form has filler
  `thing`. -/
  | min (n : Nat) (role : ObjProp) (filler : ClassExpr)
  | max (n : Nat) (role : ObjProp) (filler : ClassExpr)
  | exact (n : Nat) (role : ObjProp) (filler : ClassExpr)
  /-- `DataSomeValuesFrom(p R)` with one data property. -/
  | dataSome (prop : DataProp) (range : DataRange)
  | dataAll (prop : DataProp) (range : DataRange)
  | dataHasValue (prop : DataProp) (lit : Literal)
  /-- `DataMinCardinality(n p R)`; the unqualified form has range
  `rdfs:Literal`. -/
  | dataMin (n : Nat) (prop : DataProp) (range : DataRange)
  | dataMax (n : Nat) (prop : DataProp) (range : DataRange)
  | dataExact (n : Nat) (prop : DataProp) (range : DataRange)
deriving Repr, Inhabited

inductive Axiom where
  | subClassOf (sub sup : ClassExpr)
  | equivalentClasses (members : List ClassExpr)
  | disjointClasses (members : List ClassExpr)
  | domain (role : ObjProp) (cls : ClassExpr)
  | range (role : ObjProp) (cls : ClassExpr)
  /-- `SubObjectPropertyOf(ObjectPropertyChain(r1 ... rn) r)`; `n = 1` is a
  plain role inclusion. The parser never produces an empty chain. -/
  | subObjectPropertyOf (chain : List ObjProp) (sup : ObjProp)
  | equivalentObjectProperties (members : List ObjProp)
  | inverseObjectProperties (left right : ObjProp)
  | transitive (role : ObjProp)
  | symmetric (role : ObjProp)
  | declareClass (name : IRI)
  | declareObjectProperty (name : IRI)
  /-- `DisjointUnion(A C1 ... Cn)`. -/
  | disjointUnion (cls : IRI) (members : List ClassExpr)
  | disjointObjectProperties (members : List ObjProp)
  | functional (role : ObjProp)
  | inverseFunctional (role : ObjProp)
  | reflexive (role : ObjProp)
  | irreflexive (role : ObjProp)
  | asymmetric (role : ObjProp)
  | subDataPropertyOf (sub sup : DataProp)
  | equivalentDataProperties (members : List DataProp)
  | disjointDataProperties (members : List DataProp)
  | dataDomain (prop : DataProp) (cls : ClassExpr)
  | dataRange (prop : DataProp) (range : DataRange)
  | functionalData (prop : DataProp)
  /-- `DatatypeDefinition(dt R)`. -/
  | datatypeDefinition (dt : IRI) (range : DataRange)
  /-- `HasKey(C (r1 ... rm) (p1 ... pn))`. -/
  | hasKey (cls : ClassExpr) (objProps : List ObjProp) (dataProps : List DataProp)
  | sameIndividual (members : List Individual)
  | differentIndividuals (members : List Individual)
  | classAssertion (cls : ClassExpr) (ind : Individual)
  | objectPropertyAssertion (role : ObjProp) (source target : Individual)
  | negativeObjectPropertyAssertion (role : ObjProp) (source target : Individual)
  | dataPropertyAssertion (prop : DataProp) (source : Individual) (target : Literal)
  | negativeDataPropertyAssertion (prop : DataProp) (source : Individual) (target : Literal)
  | declareDataProperty (name : IRI)
  | declareNamedIndividual (name : IRI)
  | declareDatatype (name : IRI)
  | declareAnnotationProperty (name : IRI)
deriving Repr, Inhabited

structure Ontology where
  axioms : List Axiom
deriving Repr, Inhabited

/-- A datatype map (Direct Semantics, section 2.1), kept abstract: the value
type, the value spaces of its datatypes, the values of literals and the
facets. -/
structure DatatypeMap where
  Val : Type
  datatype : IRI → Option (Val → Prop)
  literal : Literal → Option Val
  facet : IRI → IRI → Literal → Option (Val → Prop)

/-- The datatype map with one value and no datatypes, literals or facets.
Proofs that need some datatype map use it. -/
def DatatypeMap.trivial : DatatypeMap where
  Val := Unit
  datatype _ := none
  literal _ := none
  facet _ _ _ := none

structure Interp (D : DatatypeMap) (Domain : Type) where
  cls : IRI → Domain → Prop
  role : IRI → Domain → Domain → Prop
  ind : Individual → Domain
  dprop : IRI → Domain → D.Val → Prop
  dtype : IRI → D.Val → Prop

/-- At least `n` distinct elements satisfy `P`. -/
def AtLeast {α : Type} (n : Nat) (P : α → Prop) : Prop :=
  ∃ l : List α, l.Nodup ∧ l.length = n ∧ ∀ y ∈ l, P y

/-- At most `n` distinct elements satisfy `P`. -/
def AtMost {α : Type} (n : Nat) (P : α → Prop) : Prop :=
  ∀ l : List α, l.Nodup → (∀ y ∈ l, P y) → l.length ≤ n

/-- The extension of a datatype IRI, given the extensions `dtype` of the
datatypes outside the map: every value for `rdfs:Literal`, the value space
for a datatype of the map, `dtype` otherwise. -/
def DatatypeMap.dtExt (D : DatatypeMap) (dtype : IRI → D.Val → Prop) (t : IRI) :
    D.Val → Prop :=
  if t = rdfsLiteral then fun _ => True
  else match D.datatype t with
    | some p => p
    | none => dtype t

/-- The extension of a data range, given the extensions `dtype` of the
datatypes outside the map. A literal that the map gives no value (an
ill-typed literal) adds nothing to `DataOneOf`; a facet the map does not
know makes a `DatatypeRestriction` empty. -/
def DataRange.ext (D : DatatypeMap) (dtype : IRI → D.Val → Prop) :
    DataRange → D.Val → Prop
  | .datatype t => D.dtExt dtype t
  | .and rs => fun v => ∀ r, (h : r ∈ rs) → DataRange.ext D dtype r v
  | .or rs => fun v => ∃ r, ∃ (_ : r ∈ rs), DataRange.ext D dtype r v
  | .not r => fun v => ¬ DataRange.ext D dtype r v
  | .oneOf ls => fun v => ∃ l ∈ ls, D.literal l = some v
  | .restriction t fs => fun v =>
      D.dtExt dtype t v ∧ ∀ f ∈ fs, ∃ p, D.facet t f.1 f.2 = some p ∧ p v
termination_by r => sizeOf r
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ rs›; omega)
    | omega

namespace Interp

variable {D : DatatypeMap} {Domain : Type} (I : Interp D Domain)

def prop : ObjProp → Domain → Domain → Prop
  | .named r => I.role r
  | .inv r => fun x y => I.role r y x
  | .top => fun _ _ => True
  | .bot => fun _ _ => False

/-- The extension of a data property expression. -/
def dp : DataProp → Domain → D.Val → Prop
  | .named p => I.dprop p
  | .top => fun _ _ => True
  | .bot => fun _ _ => False

/-- The extension of a datatype IRI in `I`. -/
def dt (t : IRI) : D.Val → Prop := D.dtExt I.dtype t

/-- The extension of a data range in `I`. -/
def drExt (r : DataRange) : D.Val → Prop := r.ext D I.dtype

/-- The extension of a class expression. -/
def ext : ClassExpr → Domain → Prop
  | .cls a => I.cls a
  | .thing => fun _ => True
  | .nothing => fun _ => False
  | .and cs => fun x => ∀ c, (h : c ∈ cs) → ext c x
  | .or cs => fun x => ∃ c, ∃ (_ : c ∈ cs), ext c x
  | .not c => fun x => ¬ ext c x
  | .some r c => fun x => ∃ y, I.prop r x y ∧ ext c y
  | .all r c => fun x => ∀ y, I.prop r x y → ext c y
  | .oneOf as => fun x => ∃ a ∈ as, x = I.ind a
  | .hasValue r a => fun x => I.prop r x (I.ind a)
  | .hasSelf r => fun x => I.prop r x x
  | .min n r c => fun x => AtLeast n fun y => I.prop r x y ∧ ext c y
  | .max n r c => fun x => AtMost n fun y => I.prop r x y ∧ ext c y
  | .exact n r c => fun x =>
      AtLeast n (fun y => I.prop r x y ∧ ext c y) ∧
        AtMost n (fun y => I.prop r x y ∧ ext c y)
  | .dataSome p r => fun x => ∃ v, I.dp p x v ∧ I.drExt r v
  | .dataAll p r => fun x => ∀ v, I.dp p x v → I.drExt r v
  | .dataHasValue p l => fun x => ∃ v, D.literal l = some v ∧ I.dp p x v
  | .dataMin n p r => fun x => AtLeast n fun v => I.dp p x v ∧ I.drExt r v
  | .dataMax n p r => fun x => AtMost n fun v => I.dp p x v ∧ I.drExt r v
  | .dataExact n p r => fun x =>
      AtLeast n (fun v => I.dp p x v ∧ I.drExt r v) ∧
        AtMost n (fun v => I.dp p x v ∧ I.drExt r v)
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ cs›; omega)
    | omega

/-- The composition of a chain of object-property expressions. -/
def chain : List ObjProp → Domain → Domain → Prop
  | [] => fun x y => x = y
  | r :: rs => fun x z => ∃ y, I.prop r x y ∧ chain rs y z

/-- `x` is the value of a named individual whose IRI is in `N` (`ISNAMED`
of Direct Semantics, section 2.3, with `N` the named individuals of the
ontology). -/
def IsNamed (N : List IRI) (x : Domain) : Prop :=
  ∃ a ∈ N, x = I.ind (.named a)

/-- Satisfaction of one axiom. `N` lists the named individuals of the
ontology the axiom belongs to; only `HasKey` uses it. -/
def sat (N : List IRI) : Axiom → Prop
  | .subClassOf c d => ∀ x, I.ext c x → I.ext d x
  | .equivalentClasses cs => ∀ c ∈ cs, ∀ d ∈ cs, ∀ x, I.ext c x → I.ext d x
  | .disjointClasses cs => cs.Pairwise fun c d => ∀ x, ¬ (I.ext c x ∧ I.ext d x)
  | .domain r c => ∀ x y, I.prop r x y → I.ext c x
  | .range r c => ∀ x y, I.prop r x y → I.ext c y
  | .subObjectPropertyOf rs r => ∀ x y, I.chain rs x y → I.prop r x y
  | .equivalentObjectProperties rs =>
      ∀ r ∈ rs, ∀ s ∈ rs, ∀ x y, I.prop r x y → I.prop s x y
  | .inverseObjectProperties r s => ∀ x y, I.prop r x y ↔ I.prop s y x
  | .transitive r => ∀ x y z, I.prop r x y → I.prop r y z → I.prop r x z
  | .symmetric r => ∀ x y, I.prop r x y → I.prop r y x
  | .declareClass _ => True
  | .declareObjectProperty _ => True
  | .disjointUnion a cs =>
      (∀ x, I.cls a x ↔ ∃ c ∈ cs, I.ext c x) ∧
        cs.Pairwise fun c d => ∀ x, ¬ (I.ext c x ∧ I.ext d x)
  | .disjointObjectProperties rs =>
      rs.Pairwise fun r s => ∀ x y, ¬ (I.prop r x y ∧ I.prop s x y)
  | .functional r => ∀ x y z, I.prop r x y → I.prop r x z → y = z
  | .inverseFunctional r => ∀ x y z, I.prop r y x → I.prop r z x → y = z
  | .reflexive r => ∀ x, I.prop r x x
  | .irreflexive r => ∀ x, ¬ I.prop r x x
  | .asymmetric r => ∀ x y, I.prop r x y → ¬ I.prop r y x
  | .subDataPropertyOf p q => ∀ x v, I.dp p x v → I.dp q x v
  | .equivalentDataProperties ps =>
      ∀ p ∈ ps, ∀ q ∈ ps, ∀ x v, I.dp p x v → I.dp q x v
  | .disjointDataProperties ps =>
      ps.Pairwise fun p q => ∀ x v, ¬ (I.dp p x v ∧ I.dp q x v)
  | .dataDomain p c => ∀ x v, I.dp p x v → I.ext c x
  | .dataRange p r => ∀ x v, I.dp p x v → I.drExt r v
  | .functionalData p => ∀ x v w, I.dp p x v → I.dp p x w → v = w
  | .datatypeDefinition t r => ∀ v, I.dt t v ↔ I.drExt r v
  | .hasKey c rs ps =>
      ∀ x y, I.IsNamed N x → I.IsNamed N y → I.ext c x → I.ext c y →
        (∀ r ∈ rs, ∃ z, I.IsNamed N z ∧ I.prop r x z ∧ I.prop r y z) →
        (∀ p ∈ ps, ∃ v, I.dp p x v ∧ I.dp p y v) → x = y
  | .sameIndividual as => ∀ a ∈ as, ∀ b ∈ as, I.ind a = I.ind b
  | .differentIndividuals as => as.Pairwise fun a b => I.ind a ≠ I.ind b
  | .classAssertion c a => I.ext c (I.ind a)
  | .objectPropertyAssertion r a b => I.prop r (I.ind a) (I.ind b)
  | .negativeObjectPropertyAssertion r a b => ¬ I.prop r (I.ind a) (I.ind b)
  | .dataPropertyAssertion p a l => ∃ v, D.literal l = some v ∧ I.dp p (I.ind a) v
  | .negativeDataPropertyAssertion p a l => ¬ ∃ v, D.literal l = some v ∧ I.dp p (I.ind a) v
  | .declareDataProperty _ => True
  | .declareNamedIndividual _ => True
  | .declareDatatype _ => True
  | .declareAnnotationProperty _ => True

end Interp

/-! ## Named individuals (for `HasKey`) -/

def Individual.namedIRI : Individual → List IRI
  | .named a => [a]
  | .anon _ => []

/-- The named individuals a class expression mentions. -/
def ClassExpr.namedIndividuals : ClassExpr → List IRI
  | .cls _ | .thing | .nothing => []
  | .and cs | .or cs => cs.attach.flatMap fun ⟨c, _⟩ => c.namedIndividuals
  | .not c | .some _ c | .all _ c => c.namedIndividuals
  | .min _ _ c | .max _ _ c | .exact _ _ c => c.namedIndividuals
  | .oneOf as => as.flatMap Individual.namedIRI
  | .hasValue _ a => a.namedIRI
  | .hasSelf _ => []
  | .dataSome .. | .dataAll .. | .dataHasValue .. => []
  | .dataMin .. | .dataMax .. | .dataExact .. => []
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ cs›; omega)
    | omega

/-- The named individuals an axiom mentions or declares. -/
def Axiom.namedIndividuals : Axiom → List IRI
  | .subClassOf c d => c.namedIndividuals ++ d.namedIndividuals
  | .equivalentClasses cs | .disjointClasses cs | .disjointUnion _ cs =>
      cs.flatMap ClassExpr.namedIndividuals
  | .domain _ c | .range _ c | .dataDomain _ c => c.namedIndividuals
  | .hasKey c _ _ => c.namedIndividuals
  | .sameIndividual as | .differentIndividuals as => as.flatMap Individual.namedIRI
  | .classAssertion c a => c.namedIndividuals ++ a.namedIRI
  | .objectPropertyAssertion _ a b | .negativeObjectPropertyAssertion _ a b =>
      a.namedIRI ++ b.namedIRI
  | .dataPropertyAssertion _ a _ | .negativeDataPropertyAssertion _ a _ => a.namedIRI
  | .declareNamedIndividual a => [a]
  | _ => []

/-- The named individuals of an ontology (with repetitions). -/
def Ontology.namedIndividuals (O : Ontology) : List IRI :=
  O.axioms.flatMap Axiom.namedIndividuals

/-! ## Models and entailment -/

/-- `I` is a model of `O`. -/
def Model {D : DatatypeMap} {Domain : Type} (O : Ontology) (I : Interp D Domain) : Prop :=
  ∀ ax ∈ O.axioms, I.sat O.namedIndividuals ax

/-- `O` entails `SubClassOf(A B)` for class IRIs `A`, `B`. -/
def EntailsSub (O : Ontology) (A B : IRI) : Prop :=
  ∀ (D : DatatypeMap) (Domain : Type) [Nonempty Domain] (I : Interp D Domain),
    Model O I → ∀ x, I.cls A x → I.cls B x

/-- The class IRI `A` is unsatisfiable in `O`. -/
def Unsatisfiable (O : Ontology) (A : IRI) : Prop :=
  ∀ (D : DatatypeMap) (Domain : Type) [Nonempty Domain] (I : Interp D Domain),
    Model O I → ∀ x, ¬ I.cls A x

/-- `O` has no model. -/
def Inconsistent (O : Ontology) : Prop :=
  ∀ (D : DatatypeMap) (Domain : Type) [Nonempty Domain] (I : Interp D Domain), ¬ Model O I

/-- `O` entails the axiom `ax`: every model of `O` satisfies `ax`. As in
Direct Semantics, section 2.4, `ax` is read as the ontology `{ax}`, so
`ISNAMED` in a `HasKey` axiom refers to the named individuals of `ax`. -/
def Entails (O : Ontology) (ax : Axiom) : Prop :=
  ∀ (D : DatatypeMap) (Domain : Type) [Nonempty Domain] (I : Interp D Domain),
    Model O I → I.sat ax.namedIndividuals ax

/-- An inconsistent ontology entails every subsumption. -/
theorem entailsSub_of_inconsistent {O : Ontology} (h : Inconsistent O)
    (A B : IRI) : EntailsSub O A B := by
  intro D Domain _ I hI
  exact absurd hI (h D Domain I)

/-- Subsumption between class IRIs is entailment of the `SubClassOf`
axiom. -/
theorem entailsSub_iff_entails (O : Ontology) (A B : IRI) :
    EntailsSub O A B ↔ Entails O (.subClassOf (.cls A) (.cls B)) := by
  constructor
  · intro h D Domain _ I hI x hx
    rw [Interp.ext] at hx ⊢
    exact h D Domain I hI x hx
  · intro h D Domain _ I hI x hx
    have := h D Domain I hI x
    simp only [Interp.ext] at this
    exact this hx

#print axioms entailsSub_iff_entails

/-- The class IRIs a class expression mentions. -/
def ClassExpr.names : ClassExpr → List IRI
  | .cls a => [a]
  | .thing | .nothing => []
  | .and cs | .or cs => cs.attach.flatMap fun ⟨c, _⟩ => c.names
  | .not c | .some _ c | .all _ c => c.names
  | .min _ _ c | .max _ _ c | .exact _ _ c => c.names
  | .oneOf _ | .hasValue .. | .hasSelf _ => []
  | .dataSome .. | .dataAll .. | .dataHasValue .. => []
  | .dataMin .. | .dataMax .. | .dataExact .. => []
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ cs›; omega)
    | omega

end ContextCalculus.OWL
