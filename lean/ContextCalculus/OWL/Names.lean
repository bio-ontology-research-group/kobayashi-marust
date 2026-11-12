import Std.Data.HashSet
import ContextCalculus.OWL.Semantics

/-!
# Class and object-property names of an ontology (v1.6.2)

`O.classNames` and `O.objectPropertyNames` list the names an ontology
declares or mentions, deduplicated, in first-occurrence order (axioms in
order, and inside an axiom from left to right). `owl:Thing` and
`owl:Nothing` are not class IRIs here: the parser maps them to
`ClassExpr.thing` / `.nothing` and skips their declarations.

The per-axiom lists (`Axiom.classNames`, `Axiom.objectPropertyNames`) are
the specification; the ontology-level functions only deduplicate them, in
one pass with a hash set, so they run in time linear in the ontology.
-/

namespace ContextCalculus.OWL

def ObjProp.name : ObjProp → IRI
  | .named r => r
  | .inv r => r

/-- The object-property IRIs a class expression mentions. -/
def ClassExpr.roleNames : ClassExpr → List IRI
  | .cls _ | .thing | .nothing => []
  | .and cs | .or cs => cs.attach.flatMap fun ⟨c, _⟩ => c.roleNames
  | .not c => c.roleNames
  | .some r c | .all r c => r.name :: c.roleNames
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ cs›; omega)
    | omega

/-- The class IRIs an axiom declares or mentions. -/
def Axiom.classNames : Axiom → List IRI
  | .subClassOf c d => c.names ++ d.names
  | .equivalentClasses cs | .disjointClasses cs => cs.flatMap ClassExpr.names
  | .domain _ c | .range _ c => c.names
  | .declareClass a => [a]
  | .subObjectPropertyOf .. | .equivalentObjectProperties _ | .inverseObjectProperties .. => []
  | .transitive _ | .symmetric _ | .declareObjectProperty _ => []

/-- The object-property IRIs an axiom declares or mentions. -/
def Axiom.objectPropertyNames : Axiom → List IRI
  | .subClassOf c d => c.roleNames ++ d.roleNames
  | .equivalentClasses cs | .disjointClasses cs => cs.flatMap ClassExpr.roleNames
  | .domain r c | .range r c => r.name :: c.roleNames
  | .subObjectPropertyOf rs r => rs.map ObjProp.name ++ [r.name]
  | .equivalentObjectProperties rs => rs.map ObjProp.name
  | .inverseObjectProperties r s => [r.name, s.name]
  | .transitive r | .symmetric r => [r.name]
  | .declareObjectProperty r => [r]
  | .declareClass _ => []

/-- Append the names of `xs` not seen yet; `seen` holds the names already in
`acc`. -/
def appendNew (acc : Array IRI × Std.HashSet IRI) (xs : List IRI) :
    Array IRI × Std.HashSet IRI :=
  xs.foldl (init := acc) fun (out, seen) x =>
    if seen.contains x then (out, seen) else (out.push x, seen.insert x)

/-- The names `f` gives for the axioms of `O`, deduplicated, in
first-occurrence order. -/
def Ontology.namesBy (O : Ontology) (f : Axiom → List IRI) : List IRI :=
  (O.axioms.foldl (init := (#[], {})) fun acc ax => appendNew acc (f ax)).1.toList

/-- The class IRIs `O` declares or mentions (deduplicated, first occurrence
first). -/
def Ontology.classNames (O : Ontology) : List IRI :=
  O.namesBy Axiom.classNames

/-- The object-property IRIs `O` declares or mentions (deduplicated, first
occurrence first). -/
def Ontology.objectPropertyNames (O : Ontology) : List IRI :=
  O.namesBy Axiom.objectPropertyNames

end ContextCalculus.OWL
