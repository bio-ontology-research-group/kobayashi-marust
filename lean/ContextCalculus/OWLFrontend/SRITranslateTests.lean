import ContextCalculus.OWLFrontend.SRITranslate

/-!
# Executable tests for the OWL SRI translation

Hand-computed clause lists for the rows that differ from the ALC translation
(inverse properties in restrictions, the negative existential as a universal
over the flipped role term, domain and range over an inverse) and for every
object-property axiom (symmetry, inverse properties, transitivity, a chain
of length 3, equivalent properties); `none` outside the SRI fragment; and an
ALC ontology translates to clauses with only `.pos` role terms and no
`chain`.

Layout as in `ALCTranslateTests`: requested names first, then the other
class IRIs, then `top` and `bottom` (clauses `gci [] [top]`,
`gci [bottom] []` open every list), then the definers. Role indices follow
the first occurrence of each property IRI.
-/

namespace ContextCalculus.OWLFrontend.SRITests

open ContextCalculus.OWL

/-- A role term over `Fin` indices read on `Nat`. -/
def unfinRT {m : Nat} : SRI.RoleT (Fin m) → SRI.RoleT Nat
  | .pos r => .pos r.val
  | .inv r => .inv r.val

/-- A clause over `Fin` indices read on `Nat`. -/
def unfin {n m : Nat} : SRI.Clause (Fin n) (Fin m) → SRI.Clause Nat Nat
  | .gci b h => .gci (b.map Fin.val) (h.map Fin.val)
  | .exRight a R c => .exRight a.val (unfinRT R) c.val
  | .allRight a R c => .allRight a.val (unfinRT R) c.val
  | .chain body S => .chain (body.map unfinRT) (unfinRT S)

/-- The translated clauses, on `Nat` indices. -/
def clauses (O : Ontology) (requested : List IRI) : Option (List (SRI.Clause Nat Nat)) :=
  (translateSRI O requested).map fun T => T.ontology.map unfin

def r : ObjProp := .named "r"
def s : ObjProp := .named "s"
def t : ObjProp := .named "t"
def u : ObjProp := .named "u"
def ri : ObjProp := .inv "r"
def si : ObjProp := .inv "s"
def A : ClassExpr := .cls "A"
def B : ClassExpr := .cls "B"
def C : ClassExpr := .cls "C"
def E : ClassExpr := .cls "E"

/-! ## Class expressions -/

/- Positive `some` over an inverse: `C ⊑ ∃r⁻.A`; `A, C = 0, 1`, `top = 2`,
`bottom = 3`, role `r = 0`, definer `4`. -/
#guard clauses ⟨[.subClassOf C (.some ri A)]⟩ ["A", "C"] ==
  some [.gci [] [2], .gci [3] [], .exRight 4 (.inv 0) 0, .gci [1] [4]]

/- Negative `some`: `∃r.A ⊑ C` is `A ⊑ ∀r⁻.X`. -/
#guard clauses ⟨[.subClassOf (.some r A) C]⟩ ["A", "C"] ==
  some [.gci [] [2], .gci [3] [], .allRight 0 (.inv 0) 4, .gci [4] [1]]

/- Negative `some` over an inverse: `∃r⁻.A ⊑ C` is `A ⊑ ∀r.X`. -/
#guard clauses ⟨[.subClassOf (.some ri A) C]⟩ ["A", "C"] ==
  some [.gci [] [2], .gci [3] [], .allRight 0 (.pos 0) 4, .gci [4] [1]]

/- Positive `all` over an inverse: `C ⊑ ∀r⁻.A`. -/
#guard clauses ⟨[.subClassOf C (.all ri A)]⟩ ["A", "C"] ==
  some [.gci [] [2], .gci [3] [], .allRight 4 (.inv 0) 0, .gci [1] [4]]

/- Negative `all` over an inverse: `∀r⁻.A ⊑ C`; `X = 4`, `W = 5`, `N = 6`. -/
#guard clauses ⟨[.subClassOf (.all ri A) C]⟩ ["A", "C"] ==
  some [.gci [] [2], .gci [3] [], .gci [] [4, 5], .exRight 5 (.inv 0) 6, .gci [6, 0] [],
    .gci [4] [1]]

/- Two properties: `∃s.A ⊑ ∃r⁻.C`; roles `s = 0`, `r = 1` in order of first
occurrence. -/
#guard clauses ⟨[.subClassOf (.some s A) (.some ri C)]⟩ ["A", "C"] ==
  some [.gci [] [2], .gci [3] [], .allRight 0 (.inv 0) 4, .exRight 5 (.inv 1) 1,
    .gci [4] [5]]

/-! ## Domain and range -/

/- `ObjectPropertyDomain(r A)` is `top ⊑ ∀r⁻.A`; over `r⁻` it is
`top ⊑ ∀r.A`. `A = 0`, `top = 1`, `bottom = 2`. -/
#guard clauses ⟨[.domain r A]⟩ ["A"] ==
  some [.gci [] [1], .gci [2] [], .allRight 1 (.inv 0) 0]
#guard clauses ⟨[.domain ri A]⟩ ["A"] ==
  some [.gci [] [1], .gci [2] [], .allRight 1 (.pos 0) 0]

/- `ObjectPropertyRange(r A)` is `top ⊑ ∀r.A`; over `r⁻` it is
`top ⊑ ∀r⁻.A`. -/
#guard clauses ⟨[.range r A]⟩ ["A"] ==
  some [.gci [] [1], .gci [2] [], .allRight 1 (.pos 0) 0]
#guard clauses ⟨[.range ri A]⟩ ["A"] ==
  some [.gci [] [1], .gci [2] [], .allRight 1 (.inv 0) 0]

/-! ## Object-property axioms (no class names: `top = 0`, `bottom = 1`) -/

/- Symmetry: `r ⊑ r⁻`. -/
#guard clauses ⟨[.symmetric r]⟩ [] ==
  some [.gci [] [0], .gci [1] [], .chain [.pos 0] (.inv 0)]

/- Inverse properties `r`, `s`: `r ⊑ s⁻` and `s ⊑ r⁻`. -/
#guard clauses ⟨[.inverseObjectProperties r s]⟩ [] ==
  some [.gci [] [0], .gci [1] [], .chain [.pos 0] (.inv 1), .chain [.pos 1] (.inv 0)]

/- Inverse properties `r⁻`, `s`: `r⁻ ⊑ s⁻` and `s ⊑ r`. -/
#guard clauses ⟨[.inverseObjectProperties ri s]⟩ [] ==
  some [.gci [] [0], .gci [1] [], .chain [.inv 0] (.inv 1), .chain [.pos 1] (.pos 0)]

/- Transitivity: `r ∘ r ⊑ r`; over an inverse, `r⁻ ∘ r⁻ ⊑ r⁻`. -/
#guard clauses ⟨[.transitive r]⟩ [] ==
  some [.gci [] [0], .gci [1] [], .chain [.pos 0, .pos 0] (.pos 0)]
#guard clauses ⟨[.transitive ri]⟩ [] ==
  some [.gci [] [0], .gci [1] [], .chain [.inv 0, .inv 0] (.inv 0)]

/- A role inclusion and a chain of length 3: `s ⊑ r`, `r ∘ s⁻ ∘ t ⊑ u`. -/
#guard clauses ⟨[.subObjectPropertyOf [s] r, .subObjectPropertyOf [r, si, t] u]⟩ [] ==
  some [.gci [] [0], .gci [1] [], .chain [.pos 0] (.pos 1),
    .chain [.pos 1, .inv 0, .pos 2] (.pos 3)]

/- Equivalent properties `r`, `s`, `r⁻`: `chain [R] S` for every ordered
pair of distinct role terms, in list order. -/
#guard clauses ⟨[.equivalentObjectProperties [r, s, ri]]⟩ [] ==
  some [.gci [] [0], .gci [1] [], .chain [.pos 0] (.pos 1), .chain [.pos 0] (.inv 0),
    .chain [.pos 1] (.pos 0), .chain [.pos 1] (.inv 0), .chain [.inv 0] (.pos 0),
    .chain [.inv 0] (.pos 1)]

/- Repeated members give no clause for the equal pair. -/
#guard clauses ⟨[.equivalentObjectProperties [r, r]]⟩ [] ==
  some [.gci [] [0], .gci [1] []]

/- Declarations give no clause. -/
#guard clauses ⟨[.declareClass "D", .declareObjectProperty "p"]⟩ [] ==
  some [.gci [] [1], .gci [2] []]

/-! ## Named IRIs, sizes, `none` outside SRI -/

#guard (translateSRI ⟨[.subClassOf A B]⟩ ["B", "Z", "B", "A"]).map (·.named) ==
  some ["B", "Z", "A"]
#guard (translateSRI ⟨[.subClassOf A (.some ri B), .transitive s]⟩ ["A", "B"]).map
  (fun T => (T.conceptCount, T.roleCount)) == some (5, 2)
#guard (translateSRI ⟨[.subObjectPropertyOf [] r]⟩ []).isNone

/-! ## An ALC ontology: no `chain`, `.inv` only where the design flips

An ALC ontology gives no `chain` clause. Its role terms are `.pos` except in
the two places where the design writes `∃R.C` on the left as a universal
over the flipped role term: a negative existential (`∃r.C ⊑ X` as
`C ⊑ ∀r⁻.X`) and a domain (`⊤ ⊑ ∀r⁻.C`). Every `exRight` keeps `.pos`. An
ALC ontology with neither gives only `.pos` role terms. -/

def RoleT.isPos : SRI.RoleT Nat → Bool
  | .pos _ => true
  | .inv _ => false

/-- The clause has only `.pos` role terms and is not a chain. -/
def posShape : SRI.Clause Nat Nat → Bool
  | .gci _ _ => true
  | .exRight _ R _ | .allRight _ R _ => RoleT.isPos R
  | .chain _ _ => false

/-- The clause is not a chain and an `exRight` has a `.pos` role term. -/
def alcShape : SRI.Clause Nat Nat → Bool
  | .gci _ _ | .allRight _ _ _ => true
  | .exRight _ R _ => RoleT.isPos R
  | .chain _ _ => false

/-- ALC with negative existentials (also inside a negative universal's
complement and a positive complement) and a domain. -/
def alcOnt : Ontology :=
  ⟨[.subClassOf A (.or [B, C]), .subClassOf (.some r (.and [A, B])) E,
    .subClassOf (.all s A) (.not (.some r C)), .equivalentClasses [E, .all r (.or [A, C])],
    .disjointClasses [A, B, C], .domain r A, .range s B]⟩

/-- ALC without negative existentials or domains. -/
def alcPosOnt : Ontology :=
  ⟨[.subClassOf A (.or [B, C]), .subClassOf A (.some r (.and [A, B])),
    .subClassOf (.all s A) (.all r C), .subClassOf (.not (.all r C)) E,
    .disjointClasses [A, B, C], .range s B]⟩

#guard alcOnt.isALC
#guard alcPosOnt.isALC
#guard ((clauses alcOnt ["A", "B", "C", "E"]).map (·.all alcShape)) == some true
#guard ((clauses alcOnt ["A", "B", "C", "E"]).map (·.all posShape)) == some false
#guard ((clauses alcPosOnt ["A", "B", "C", "E"]).map (·.all posShape)) == some true
#guard ((clauses alcPosOnt ["A", "B", "C", "E"]).map (·.length)) ==
  (translateALC alcPosOnt ["A", "B", "C", "E"]).map (·.ontology.length)

/- The clause counts match the ALC route (an ALC `exLeft` becomes one SRI
`allRight`). -/
#guard ((clauses alcOnt ["A", "B", "C", "E"]).map (·.length)) ==
  (translateALC alcOnt ["A", "B", "C", "E"]).map (·.ontology.length)

/- One inverse in an existential on the right gives an `exRight` with `.inv`. -/
#guard ((clauses ⟨.subClassOf A (.some ri B) :: alcOnt.axioms⟩ ["A"]).map
  (·.all alcShape)) == some false

end ContextCalculus.OWLFrontend.SRITests
