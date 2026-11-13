/-!
# OWL 2 direct semantics for the KM frontend fragment (v1.6.2 draft)

Syntax and direct semantics of the fragment `F` of
`docs/V1.6.2-FRONTEND-PLAN.md`: class expressions over names, `owl:Thing`,
`owl:Nothing`, intersection, union, complement, existential and universal
restriction; object-property expressions over names and their inverses;
class axioms, domain and range, role inclusions with chains, equivalent and
inverse properties, transitivity and symmetry.

IRIs are the expanded strings the parser produces: two spellings denote the
same entity exactly when they expand to the same string (OWL 2 structural
specification, section 2.4). The parser maps `owl:Thing` and `owl:Nothing`
to `ClassExpr.thing` and `ClassExpr.nothing`, so a class IRI here is never
one of the two.

The semantics follows the OWL 2 direct semantics (section 2 and 4 of the
W3C recommendation) restricted to the fragment: an interpretation has a
nonempty domain, a set of individuals per class IRI and a binary relation
per object-property IRI; declarations and annotations carry no semantic
condition.
-/

namespace ContextCalculus.OWL

abbrev IRI := String

inductive ObjProp where
  | named (role : IRI)
  | inv (role : IRI)
deriving DecidableEq, Repr, Inhabited

inductive ClassExpr where
  | cls (name : IRI)
  | thing
  | nothing
  | and (conjuncts : List ClassExpr)
  | or (disjuncts : List ClassExpr)
  | not (operand : ClassExpr)
  | some (role : ObjProp) (filler : ClassExpr)
  | all (role : ObjProp) (filler : ClassExpr)
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
deriving Repr, Inhabited

structure Ontology where
  axioms : List Axiom
deriving Repr, Inhabited

structure Interp (Domain : Type) where
  cls : IRI → Domain → Prop
  role : IRI → Domain → Domain → Prop

namespace Interp

variable {Domain : Type} (I : Interp Domain)

def prop : ObjProp → Domain → Domain → Prop
  | .named r => I.role r
  | .inv r => fun x y => I.role r y x

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

/-- Satisfaction of one axiom. -/
def sat : Axiom → Prop
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

end Interp

/-- `I` is a model of `O`. -/
def Model {Domain : Type} (O : Ontology) (I : Interp Domain) : Prop :=
  ∀ ax ∈ O.axioms, I.sat ax

/-- `O` entails `SubClassOf(A B)` for class IRIs `A`, `B`. -/
def EntailsSub (O : Ontology) (A B : IRI) : Prop :=
  ∀ (Domain : Type) [Nonempty Domain] (I : Interp Domain),
    Model O I → ∀ x, I.cls A x → I.cls B x

/-- The class IRI `A` is unsatisfiable in `O`. -/
def Unsatisfiable (O : Ontology) (A : IRI) : Prop :=
  ∀ (Domain : Type) [Nonempty Domain] (I : Interp Domain),
    Model O I → ∀ x, ¬ I.cls A x

/-- `O` has no model. -/
def Inconsistent (O : Ontology) : Prop :=
  ∀ (Domain : Type) [Nonempty Domain] (I : Interp Domain), ¬ Model O I

/-- An inconsistent ontology entails every subsumption. -/
theorem entailsSub_of_inconsistent {O : Ontology} (h : Inconsistent O)
    (A B : IRI) : EntailsSub O A B := by
  intro Domain _ I hI
  exact absurd hI (h Domain I)

/-- The class IRIs an ontology mentions or declares (the requested names). -/
def ClassExpr.names : ClassExpr → List IRI
  | .cls a => [a]
  | .thing | .nothing => []
  | .and cs | .or cs => cs.attach.flatMap fun ⟨c, _⟩ => c.names
  | .not c | .some _ c | .all _ c => c.names
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ cs›; omega)
    | omega

end ContextCalculus.OWL
