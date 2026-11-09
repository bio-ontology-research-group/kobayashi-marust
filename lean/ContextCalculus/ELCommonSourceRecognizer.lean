import ContextCalculus.KMCommonRoutingSource

/-!
# Recognising the pure EL fragment of the common clause source

The routed source of the automatic supervisor is a list of proper-term
clauses (`List FCL`, `KMCommonRoutingSource`).  The EL reference procedure of
v1.6.0 needs that list as an `ELCompletion.Ontology` with distinguished `top`
and `bottom` concepts.  `recognizeEL` reads the clauses back into NF1–NF7 and
reflexive-role clauses and fails closed on anything else; the theorem
`recognizeEL_entails_iff` states that the reading changes no named
subsumption.

Accepted clause shapes (`x`, `y`, `z` distinct per-clause variables; `C a t` is
`FLit.P (FPred.concept a t)` and `R r s t` is `FLit.P (FPred.role r s t)`):

| common clause | normal form |
|---|---|
| `⟨[C a x], [C b x]⟩` | `nf1 a b` |
| `⟨[C a x, C b x], [C c x]⟩` | `nf2 a b c` |
| `⟨[C a x, C b x], []⟩` | `nf2 a b bottom` |
| `⟨[C a x], [R r x (app f x)]⟩` with `⟨[C a y], [C b (app f y)]⟩` | `nf3 a r b`; both halves share `a` and `f`, `f` is used by exactly one pair |
| `⟨[R r x y, C b y], [C c x]⟩` or `⟨[C b y, R r x y], [C c x]⟩` | `nf4 r b c` |
| `⟨[R r x y], [C c x]⟩` | `nf4 r top c` |
| `⟨[C a x], []⟩` | `nf5 a` |
| `⟨[R r x y], [R s x y]⟩` | `nf6 r s` |
| `⟨[R r x y, R s y z], [R t x z]⟩` or `⟨[R s y z, R r x y], [R t x z]⟩` | `nf7 r s t` |
| `⟨[], [R r x x]⟩` | `reflexive r` |
| `⟨[], [C a x]⟩` | `top` candidate; the first such `a` becomes `top`, every further one becomes `nf1 top a` |

Literal order inside a clause does not matter for the semantics
(`sat` is membership-based), so the recogniser accepts both orders of a
two-literal body (`nf4` and `nf7`).  Variables may be any distinct integers,
because `valid` quantifies over all assignments; the recogniser accepts
injective renamings of `x`, `y`, `z` per clause (including negative neighbour
indices `-1`, `-2` emitted on the CB wire).

`top` and `bottom` are taken from the source when it has a total concept
clause `⟨[], [C a x]⟩` or an `nf5` clause `⟨[C a x], []⟩`; otherwise they are
fresh names above every identifier of the source and the requested list.  A
fresh distinguished name is conservative: a model of the source extends to a
model interpreting the fresh names as the total and the empty concept, and the
equivalence `recognizeEL_entails_iff` holds for every pair of requested names.
-/

namespace ContextCalculus.ELCommonSourceRecognizer

open ContextCalculus
open ContextCalculus.CheckerTerm
open ContextCalculus.KMCommonRoutingSource

deriving instance Repr for ELCompletion.Clause

/-- The recognised fragment: distinguished concepts and the normal-form
ontology. -/
structure RecognizedEL where
  top : Nat
  bottom : Nat
  ontology : ELCompletion.Ontology Nat Nat
deriving DecidableEq, Repr

/-- Concept identifiers occurring in one literal. -/
def literalConcepts : FLit → List Nat
  | .P (.concept iri _) => [iri]
  | _ => []

/-- Concept identifiers occurring in the source. -/
def sourceConcepts (source : List FCL) : List Nat :=
  source.flatMap fun clause =>
    clause.body.flatMap literalConcepts ++ clause.head.flatMap literalConcepts

/-- Intermediate representation of one recognised source clause. -/
inductive ParsedItem where
  | topCand (a : Nat)
  | nf5 (a : Nat)
  | nf1 (a b : Nat)
  | nf2 (a b c : Nat)
  | nf2Bottom (a b : Nat)
  | nf3Role (a r f : Nat)
  | nf3Filler (a b f : Nat)
  | nf4 (r b c : Nat)
  | nf4Top (r c : Nat)
  | nf6 (r s : Nat)
  | nf7 (r s t : Nat)
  | reflexive (r : Nat)
deriving DecidableEq, Repr

/-- Concept identifiers occurring in one parsed item. -/
def itemConcepts : ParsedItem → List Nat
  | .topCand a => [a]
  | .nf5 a => [a]
  | .nf1 a b => [a, b]
  | .nf2 a b c => [a, b, c]
  | .nf2Bottom a b => [a, b]
  | .nf3Role a _ _ => [a]
  | .nf3Filler a b _ => [a, b]
  | .nf4 _ b c => [b, c]
  | .nf4Top _ c => [c]
  | .nf6 _ _ => []
  | .nf7 _ _ _ => []
  | .reflexive _ => []

/-- Concept identifiers occurring across a parsed item list. -/
def itemsConcepts (items : List ParsedItem) : List Nat :=
  items.flatMap itemConcepts

/-- First-order model satisfaction of a single parsed item. -/
def satParsedItem {Domain : Type} (M : TModel Domain) : ParsedItem → Prop
  | .topCand a => ∀ x, M.conc a x
  | .nf5 a => ∀ x, ¬ M.conc a x
  | .nf1 a b => ∀ x, M.conc a x → M.conc b x
  | .nf2 a b c => ∀ x, M.conc a x → M.conc b x → M.conc c x
  | .nf2Bottom a b => ∀ x, M.conc a x → M.conc b x → False
  | .nf3Role a r f => ∀ x, M.conc a x → M.rol r x (M.fn f x)
  | .nf3Filler a b f => ∀ x, M.conc a x → M.conc b (M.fn f x)
  | .nf4 r b c => ∀ x, (∃ y, M.rol r x y ∧ M.conc b y) → M.conc c x
  | .nf4Top r c => ∀ x, (∃ y, M.rol r x y) → M.conc c x
  | .nf6 r s => ∀ x y, M.rol r x y → M.rol s x y
  | .nf7 r s t => ∀ x y z, M.rol r x y → M.rol s y z → M.rol t x z
  | .reflexive r => ∀ x, M.rol r x x

theorem satParsedItem_congr {Domain : Type} {M₁ M₂ : TModel Domain} {item : ParsedItem}
    (hrol : M₁.rol = M₂.rol) (hfn : M₁.fn = M₂.fn)
    (hconc : ∀ c ∈ itemConcepts item, M₁.conc c = M₂.conc c) :
    satParsedItem M₁ item ↔ satParsedItem M₂ item := by
  cases item with
  | topCand a =>
      have ha : M₁.conc a = M₂.conc a := hconc a (by simp [itemConcepts])
      simp [satParsedItem, ha]
  | nf5 a =>
      have ha : M₁.conc a = M₂.conc a := hconc a (by simp [itemConcepts])
      simp [satParsedItem, ha]
  | nf1 a b =>
      have ha : M₁.conc a = M₂.conc a := hconc a (by simp [itemConcepts])
      have hb : M₁.conc b = M₂.conc b := hconc b (by simp [itemConcepts])
      simp [satParsedItem, ha, hb]
  | nf2 a b c =>
      have ha : M₁.conc a = M₂.conc a := hconc a (by simp [itemConcepts])
      have hb : M₁.conc b = M₂.conc b := hconc b (by simp [itemConcepts])
      have hc : M₁.conc c = M₂.conc c := hconc c (by simp [itemConcepts])
      simp [satParsedItem, ha, hb, hc]
  | nf2Bottom a b =>
      have ha : M₁.conc a = M₂.conc a := hconc a (by simp [itemConcepts])
      have hb : M₁.conc b = M₂.conc b := hconc b (by simp [itemConcepts])
      simp [satParsedItem, ha, hb]
  | nf3Role a r f =>
      have ha : M₁.conc a = M₂.conc a := hconc a (by simp [itemConcepts])
      simp [satParsedItem, ha, hrol, hfn]
  | nf3Filler a b f =>
      have ha : M₁.conc a = M₂.conc a := hconc a (by simp [itemConcepts])
      have hb : M₁.conc b = M₂.conc b := hconc b (by simp [itemConcepts])
      simp [satParsedItem, ha, hb, hfn]
  | nf4 r b c =>
      have hb : M₁.conc b = M₂.conc b := hconc b (by simp [itemConcepts])
      have hc : M₁.conc c = M₂.conc c := hconc c (by simp [itemConcepts])
      simp [satParsedItem, hb, hc, hrol]
  | nf4Top r c =>
      have hc : M₁.conc c = M₂.conc c := hconc c (by simp [itemConcepts])
      simp [satParsedItem, hc, hrol]
  | nf6 r s =>
      simp [satParsedItem, hrol]
  | nf7 r s t =>
      simp [satParsedItem, hrol]
  | reflexive r =>
      simp [satParsedItem, hrol]

/-- Structural evidence connecting a raw `FCL` clause to its `ParsedItem`. -/
inductive ClauseItemEvidence : FCL → ParsedItem → Prop where
  | topCand (a : Nat) (x : Int) :
      ClauseItemEvidence ⟨[], [.P (.concept a (.var x))]⟩ (.topCand a)
  | reflexive (r : Nat) (x : Int) :
      ClauseItemEvidence ⟨[], [.P (.role r (.var x) (.var x))]⟩ (.reflexive r)
  | nf5 (a : Nat) (x : Int) :
      ClauseItemEvidence ⟨[.P (.concept a (.var x))], []⟩ (.nf5 a)
  | nf2Bottom (a b : Nat) (x : Int) :
      ClauseItemEvidence
        ⟨[.P (.concept a (.var x)), .P (.concept b (.var x))], []⟩
        (.nf2Bottom a b)
  | nf1 (a b : Nat) (x : Int) :
      ClauseItemEvidence
        ⟨[.P (.concept a (.var x))], [.P (.concept b (.var x))]⟩
        (.nf1 a b)
  | nf3Filler (a b f : Nat) (x : Int) :
      ClauseItemEvidence
        ⟨[.P (.concept a (.var x))], [.P (.concept b (.app f (.var x)))]⟩
        (.nf3Filler a b f)
  | nf3Role (a r f : Nat) (x : Int) :
      ClauseItemEvidence
        ⟨[.P (.concept a (.var x))], [.P (.role r (.var x) (.app f (.var x)))]⟩
        (.nf3Role a r f)
  | nf2 (a b c : Nat) (x : Int) :
      ClauseItemEvidence
        ⟨[.P (.concept a (.var x)), .P (.concept b (.var x))],
         [.P (.concept c (.var x))]⟩
        (.nf2 a b c)
  | nf4Top (r c : Nat) (x y : Int) (hne : x ≠ y) :
      ClauseItemEvidence
        ⟨[.P (.role r (.var x) (.var y))], [.P (.concept c (.var x))]⟩
        (.nf4Top r c)
  | nf4RoleFirst (r b c : Nat) (x y : Int) (hne : x ≠ y) :
      ClauseItemEvidence
        ⟨[.P (.role r (.var x) (.var y)), .P (.concept b (.var y))],
         [.P (.concept c (.var x))]⟩
        (.nf4 r b c)
  | nf4ConceptFirst (r b c : Nat) (x y : Int) (hne : x ≠ y) :
      ClauseItemEvidence
        ⟨[.P (.concept b (.var y)), .P (.role r (.var x) (.var y))],
         [.P (.concept c (.var x))]⟩
        (.nf4 r b c)
  | nf6 (r s : Nat) (x y : Int) (hne : x ≠ y) :
      ClauseItemEvidence
        ⟨[.P (.role r (.var x) (.var y))], [.P (.role s (.var x) (.var y))]⟩
        (.nf6 r s)
  | nf7 (r s t : Nat) (x y z : Int) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
      ClauseItemEvidence
        ⟨[.P (.role r (.var x) (.var y)), .P (.role s (.var y) (.var z))],
         [.P (.role t (.var x) (.var z))]⟩
        (.nf7 r s t)
  | nf7Rev (r s t : Nat) (x y z : Int) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
      ClauseItemEvidence
        ⟨[.P (.role s (.var y) (.var z)), .P (.role r (.var x) (.var y))],
         [.P (.role t (.var x) (.var z))]⟩
        (.nf7 r s t)

/-- Proof-producing single-clause classifier. -/
def classifyClauseWithProof : (clause : FCL) →
    Option { item : ParsedItem // ClauseItemEvidence clause item }
  | ⟨[], [.P (.concept a (.var x))]⟩ =>
      some ⟨.topCand a, .topCand a x⟩
  | ⟨[], [.P (.role r (.var x) (.var x'))]⟩ =>
      if h : x' = x then
        some ⟨.reflexive r, by subst h; exact .reflexive r _⟩
      else none
  | ⟨[.P (.concept a (.var x))], []⟩ =>
      some ⟨.nf5 a, .nf5 a x⟩
  | ⟨[.P (.concept a (.var x)), .P (.concept b (.var x'))], []⟩ =>
      if h : x' = x then
        some ⟨.nf2Bottom a b, by subst h; exact .nf2Bottom a b _⟩
      else none
  | ⟨[.P (.concept a (.var x))], [.P (.concept b (.var x'))]⟩ =>
      if h : x' = x then
        some ⟨.nf1 a b, by subst h; exact .nf1 a b _⟩
      else none
  | ⟨[.P (.concept a (.var x))], [.P (.concept b (.app f (.var x')))]⟩ =>
      if h : x' = x then
        some ⟨.nf3Filler a b f, by subst h; exact .nf3Filler a b f _⟩
      else none
  | ⟨[.P (.concept a (.var x))], [.P (.role r (.var x') (.app f (.var x'')))]⟩ =>
      if h : x' = x ∧ x'' = x then
        some ⟨.nf3Role a r f, by
          rcases h with ⟨rfl, rfl⟩
          exact .nf3Role a r f _⟩
      else none
  | ⟨[.P (.concept a (.var x)), .P (.concept b (.var x'))],
     [.P (.concept c (.var x''))]⟩ =>
      if h : x' = x ∧ x'' = x then
        some ⟨.nf2 a b c, by
          rcases h with ⟨rfl, rfl⟩
          exact .nf2 a b c _⟩
      else none
  | ⟨[.P (.role r (.var x) (.var y))], [.P (.concept c (.var x'))]⟩ =>
      if h : x' = x ∧ x ≠ y then
        some ⟨.nf4Top r c, by
          rcases h with ⟨rfl, hne⟩
          exact .nf4Top r c _ _ hne⟩
      else none
  | ⟨[.P (.role r (.var x) (.var y)), .P (.concept b (.var y'))],
     [.P (.concept c (.var x'))]⟩ =>
      if h : x' = x ∧ y' = y ∧ x ≠ y then
        some ⟨.nf4 r b c, by
          rcases h with ⟨rfl, rfl, hne⟩
          exact .nf4RoleFirst r b c _ _ hne⟩
      else none
  | ⟨[.P (.concept b (.var y')), .P (.role r (.var x) (.var y))],
     [.P (.concept c (.var x'))]⟩ =>
      if h : x' = x ∧ y' = y ∧ x ≠ y then
        some ⟨.nf4 r b c, by
          rcases h with ⟨rfl, rfl, hne⟩
          exact .nf4ConceptFirst r b c _ _ hne⟩
      else none
  | ⟨[.P (.role r (.var x) (.var y))], [.P (.role s (.var x') (.var y'))]⟩ =>
      if h : x' = x ∧ y' = y ∧ x ≠ y then
        some ⟨.nf6 r s, by
          rcases h with ⟨rfl, rfl, hne⟩
          exact .nf6 r s _ _ hne⟩
      else none
  | ⟨[.P (.role r (.var x) (.var y)), .P (.role s (.var y') (.var z))],
     [.P (.role t (.var x') (.var z'))]⟩ =>
      if h : y' = y ∧ x' = x ∧ z' = z ∧ x ≠ y ∧ y ≠ z ∧ x ≠ z then
        some ⟨.nf7 r s t, by
          rcases h with ⟨rfl, rfl, rfl, hxy, hyz, hxz⟩
          exact .nf7 r s t _ _ _ hxy hyz hxz⟩
      else if h : z = x ∧ x' = y' ∧ z' = y ∧ y' ≠ x ∧ x ≠ y ∧ y' ≠ y then
        some ⟨.nf7 s r t, by
          rcases h with ⟨rfl, rfl, rfl, hxy, hyz, hxz⟩
          exact .nf7Rev s r t _ _ _ hxy hyz hxz⟩
      else none
  | _ => none

/-- Classify a single `FCL` clause into its `ParsedItem`. -/
def classifyClause (clause : FCL) : Option ParsedItem :=
  (classifyClauseWithProof clause).map Subtype.val

theorem classifyClause_evidence {clause : FCL} {item : ParsedItem}
    (h : classifyClause clause = some item) :
    ClauseItemEvidence clause item := by
  unfold classifyClause at h
  cases hcert : classifyClauseWithProof clause with
  | none => simp [hcert] at h
  | some cert =>
      simp [hcert] at h
      subst h
      exact cert.2

theorem ClauseItemEvidence.valid_iff {Domain : Type} {clause : FCL} {item : ParsedItem}
    (h : ClauseItemEvidence clause item) (M : TModel Domain) :
    valid M clause ↔ satParsedItem M item := by
  cases h with
  | topCand a x =>
      constructor
      · intro hval u
        have hsat := hval (fun _ => u)
        simpa [sat, TModel.evalL, TModel.evalT] using hsat
      · intro hsat ρ _
        exact ⟨.P (.concept a (.var x)), by simp, hsat (ρ x)⟩
  | reflexive r x =>
      constructor
      · intro hval u
        have hsat := hval (fun _ => u)
        simpa [sat, TModel.evalL, TModel.evalT] using hsat
      · intro hsat ρ _
        exact ⟨.P (.role r (.var x) (.var x)), by simp, hsat (ρ x)⟩
  | nf5 a x =>
      constructor
      · intro hval u hu
        have hsat := hval (fun _ => u)
        simp [sat, TModel.evalL, TModel.evalT, hu] at hsat
      · intro hsat ρ hbody
        have hx : M.conc a (ρ x) := hbody (.P (.concept a (.var x))) (by simp)
        exact False.elim (hsat (ρ x) hx)
  | nf2Bottom a b x =>
      constructor
      · intro hval u ha hb
        have hsat := hval (fun _ => u)
        have hbody : ∀ l ∈ ([.P (.concept a (.var x)), .P (.concept b (.var x))] : List FLit),
            M.evalL (fun _ => u) l := by
          intro l hl
          rcases List.mem_cons.mp hl with rfl | hl
          · exact ha
          · rcases List.mem_singleton.mp hl with rfl
            exact hb
        simpa [sat] using hsat hbody
      · intro hsat ρ hbody
        have ha : M.conc a (ρ x) := hbody (.P (.concept a (.var x))) (by simp)
        have hb : M.conc b (ρ x) := hbody (.P (.concept b (.var x))) (by simp)
        exact False.elim (hsat (ρ x) ha hb)
  | nf1 a b x =>
      constructor
      · intro hval u ha
        have hsat := hval (fun _ => u)
        simpa [sat, TModel.evalL, TModel.evalT, ha] using hsat
      · intro hsat ρ hbody
        have ha : M.conc a (ρ x) := hbody (.P (.concept a (.var x))) (by simp)
        exact ⟨.P (.concept b (.var x)), by simp, hsat (ρ x) ha⟩
  | nf3Filler a b f x =>
      constructor
      · intro hval u ha
        have hsat := hval (fun _ => u)
        simpa [sat, TModel.evalL, TModel.evalT, ha] using hsat
      · intro hsat ρ hbody
        have ha : M.conc a (ρ x) := hbody (.P (.concept a (.var x))) (by simp)
        exact ⟨.P (.concept b (.app f (.var x))), by simp, hsat (ρ x) ha⟩
  | nf3Role a r f x =>
      constructor
      · intro hval u ha
        have hsat := hval (fun _ => u)
        simpa [sat, TModel.evalL, TModel.evalT, ha] using hsat
      · intro hsat ρ hbody
        have ha : M.conc a (ρ x) := hbody (.P (.concept a (.var x))) (by simp)
        exact ⟨.P (.role r (.var x) (.app f (.var x))), by simp, hsat (ρ x) ha⟩
  | nf2 a b c x =>
      constructor
      · intro hval u ha hb
        have hsat := hval (fun _ => u)
        have hbody : ∀ l ∈ ([.P (.concept a (.var x)), .P (.concept b (.var x))] : List FLit),
            M.evalL (fun _ => u) l := by
          intro l hl
          rcases List.mem_cons.mp hl with rfl | hl
          · exact ha
          · rcases List.mem_singleton.mp hl with rfl
            exact hb
        simpa [sat, TModel.evalL, TModel.evalT] using hsat hbody
      · intro hsat ρ hbody
        have ha : M.conc a (ρ x) := hbody (.P (.concept a (.var x))) (by simp)
        have hb : M.conc b (ρ x) := hbody (.P (.concept b (.var x))) (by simp)
        exact ⟨.P (.concept c (.var x)), by simp, hsat (ρ x) ha hb⟩
  | nf4Top r c x y hne =>
      constructor
      · intro hval u ⟨v, hruv⟩
        let ρ : Int → Domain := fun vId => if vId = y then v else u
        have hsat := hval ρ
        have hbody : ∀ l ∈ ([.P (.role r (.var x) (.var y))] : List FLit), M.evalL ρ l := by
          intro l hl
          rcases List.mem_singleton.mp hl with rfl
          simpa [TModel.evalL, TModel.evalT, ρ, hne] using hruv
        simpa [sat, TModel.evalL, TModel.evalT, ρ, hne] using hsat hbody
      · intro hsat ρ hbody
        have hr : M.rol r (ρ x) (ρ y) := hbody (.P (.role r (.var x) (.var y))) (by simp)
        exact ⟨.P (.concept c (.var x)), by simp, hsat (ρ x) ⟨ρ y, hr⟩⟩
  | nf4RoleFirst r b c x y hne =>
      constructor
      · intro hval u ⟨v, hruv, hbv⟩
        let ρ : Int → Domain := fun vId => if vId = y then v else u
        have hsat := hval ρ
        have hbody : ∀ l ∈ ([.P (.role r (.var x) (.var y)), .P (.concept b (.var y))] : List FLit),
            M.evalL ρ l := by
          intro l hl
          rcases List.mem_cons.mp hl with rfl | hl
          · simpa [TModel.evalL, TModel.evalT, ρ, hne] using hruv
          · rcases List.mem_singleton.mp hl with rfl
            simpa [TModel.evalL, TModel.evalT, ρ] using hbv
        simpa [sat, TModel.evalL, TModel.evalT, ρ, hne] using hsat hbody
      · intro hsat ρ hbody
        have hr : M.rol r (ρ x) (ρ y) := hbody (.P (.role r (.var x) (.var y))) (by simp)
        have hb : M.conc b (ρ y) := hbody (.P (.concept b (.var y))) (by simp)
        exact ⟨.P (.concept c (.var x)), by simp, hsat (ρ x) ⟨ρ y, hr, hb⟩⟩
  | nf4ConceptFirst r b c x y hne =>
      constructor
      · intro hval u ⟨v, hruv, hbv⟩
        let ρ : Int → Domain := fun vId => if vId = y then v else u
        have hsat := hval ρ
        have hbody : ∀ l ∈ ([.P (.concept b (.var y)), .P (.role r (.var x) (.var y))] : List FLit),
            M.evalL ρ l := by
          intro l hl
          rcases List.mem_cons.mp hl with rfl | hl
          · simpa [TModel.evalL, TModel.evalT, ρ] using hbv
          · rcases List.mem_singleton.mp hl with rfl
            simpa [TModel.evalL, TModel.evalT, ρ, hne] using hruv
        simpa [sat, TModel.evalL, TModel.evalT, ρ, hne] using hsat hbody
      · intro hsat ρ hbody
        have hb : M.conc b (ρ y) := hbody (.P (.concept b (.var y))) (by simp)
        have hr : M.rol r (ρ x) (ρ y) := hbody (.P (.role r (.var x) (.var y))) (by simp)
        exact ⟨.P (.concept c (.var x)), by simp, hsat (ρ x) ⟨ρ y, hr, hb⟩⟩
  | nf6 r s x y hne =>
      constructor
      · intro hval u v hruv
        let ρ : Int → Domain := fun vId => if vId = y then v else u
        have hsat := hval ρ
        have hbody : ∀ l ∈ ([.P (.role r (.var x) (.var y))] : List FLit), M.evalL ρ l := by
          intro l hl
          rcases List.mem_singleton.mp hl with rfl
          simpa [TModel.evalL, TModel.evalT, ρ, hne] using hruv
        simpa [sat, TModel.evalL, TModel.evalT, ρ, hne] using hsat hbody
      · intro hsat ρ hbody
        have hr : M.rol r (ρ x) (ρ y) := hbody (.P (.role r (.var x) (.var y))) (by simp)
        exact ⟨.P (.role s (.var x) (.var y)), by simp, hsat (ρ x) (ρ y) hr⟩
  | nf7 r s t x y z hxy hyz hxz =>
      constructor
      · intro hval u v w hruv hsvw
        let ρ : Int → Domain := fun vId => if vId = z then w else if vId = y then v else u
        have hsat := hval ρ
        have hbody : ∀ l ∈ ([.P (.role r (.var x) (.var y)), .P (.role s (.var y) (.var z))] : List FLit),
            M.evalL ρ l := by
          intro l hl
          rcases List.mem_cons.mp hl with rfl | hl
          · simpa [TModel.evalL, TModel.evalT, ρ, hxy, hyz, hxz] using hruv
          · rcases List.mem_singleton.mp hl with rfl
            simpa [TModel.evalL, TModel.evalT, ρ, hyz] using hsvw
        simpa [sat, TModel.evalL, TModel.evalT, ρ, hxy, hxz] using hsat hbody
      · intro hsat ρ hbody
        have hr : M.rol r (ρ x) (ρ y) := hbody (.P (.role r (.var x) (.var y))) (by simp)
        have hs : M.rol s (ρ y) (ρ z) := hbody (.P (.role s (.var y) (.var z))) (by simp)
        exact ⟨.P (.role t (.var x) (.var z)), by simp, hsat (ρ x) (ρ y) (ρ z) hr hs⟩
  | nf7Rev r s t x y z hxy hyz hxz =>
      constructor
      · intro hval u v w hruv hsvw
        let ρ : Int → Domain := fun vId => if vId = z then w else if vId = y then v else u
        have hsat := hval ρ
        have hbody : ∀ l ∈ ([.P (.role s (.var y) (.var z)), .P (.role r (.var x) (.var y))] : List FLit),
            M.evalL ρ l := by
          intro l hl
          rcases List.mem_cons.mp hl with rfl | hl
          · simpa [TModel.evalL, TModel.evalT, ρ, hyz] using hsvw
          · rcases List.mem_singleton.mp hl with rfl
            simpa [TModel.evalL, TModel.evalT, ρ, hxy, hyz, hxz] using hruv
        simpa [sat, TModel.evalL, TModel.evalT, ρ, hxy, hxz] using hsat hbody
      · intro hsat ρ hbody
        have hs : M.rol s (ρ y) (ρ z) := hbody (.P (.role s (.var y) (.var z))) (by simp)
        have hr : M.rol r (ρ x) (ρ y) := hbody (.P (.role r (.var x) (.var y))) (by simp)
        exact ⟨.P (.role t (.var x) (.var z)), by simp, hsat (ρ x) (ρ y) (ρ z) hr hs⟩

/-- Parse all clauses in `source` into `ParsedItem`s. -/
def parseSource : List FCL → Option (List ParsedItem)
  | [] => some []
  | clause :: rest =>
      match classifyClause clause, parseSource rest with
      | some item, some tail => some (item :: tail)
      | _, _ => none

theorem parseSource_valid_iff {Domain : Type} {source : List FCL} {items : List ParsedItem}
    (hparse : parseSource source = some items) (M : TModel Domain) :
    (∀ clause ∈ source, valid M clause) ↔ (∀ item ∈ items, satParsedItem M item) := by
  induction source generalizing items with
  | nil =>
      simp only [parseSource, Option.some.injEq] at hparse
      subst hparse
      simp
  | cons clause rest ih =>
      cases hhead : classifyClause clause <;> cases htail : parseSource rest <;>
        simp [parseSource, hhead, htail] at hparse
      rename_i item tail
      subst hparse
      have hev := classifyClause_evidence hhead
      simp only [List.mem_cons, forall_eq_or_imp]
      exact and_congr (hev.valid_iff M) (ih htail)

/-- Maximum of a list of natural numbers (0 on empty). -/
def maxNatList : List Nat → Nat
  | [] => 0
  | x :: xs => max x (maxNatList xs)

theorem le_maxNatList {x : Nat} {xs : List Nat} (hx : x ∈ xs) :
    x ≤ maxNatList xs := by
  induction xs with
  | nil => contradiction
  | cons y ys ih =>
      rcases List.mem_cons.mp hx with rfl | hmem
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih hmem) (Nat.le_max_right _ _)

/-- A fresh identifier strictly greater than every requested or item concept. -/
def freshBase (named : List Nat) (items : List ParsedItem) : Nat :=
  maxNatList (named ++ itemsConcepts items) + 1

theorem lt_freshBase_of_mem_named {named : List Nat} {items : List ParsedItem}
    {c : Nat} (hc : c ∈ named) : c < freshBase named items := by
  unfold freshBase
  have hle : c ≤ maxNatList (named ++ itemsConcepts items) :=
    le_maxNatList (List.mem_append_left _ hc)
  exact Nat.lt_succ_of_le hle

theorem lt_freshBase_of_mem_itemsConcepts {named : List Nat} {items : List ParsedItem}
    {c : Nat} (hc : c ∈ itemsConcepts items) : c < freshBase named items := by
  unfold freshBase
  have hle : c ≤ maxNatList (named ++ itemsConcepts items) :=
    le_maxNatList (List.mem_append_right _ hc)
  exact Nat.lt_succ_of_le hle

/-- First `topCand` concept in `items`, if any. -/
def findTopCand : List ParsedItem → Option Nat
  | [] => none
  | .topCand a :: _ => some a
  | _ :: rest => findTopCand rest

theorem findTopCand_mem {items : List ParsedItem} {a : Nat}
    (h : findTopCand items = some a) : .topCand a ∈ items := by
  induction items with
  | nil => simp [findTopCand] at h
  | cons item rest ih =>
      cases item <;> simp [findTopCand] at h
      case topCand b =>
        subst h
        exact List.Mem.head _
      all_goals
        exact List.Mem.tail _ (ih h)

/-- Select the distinguished `top` concept. -/
def selectTop (named : List Nat) (items : List ParsedItem) : Nat :=
  match findTopCand items with
  | some a => a
  | none => freshBase named items

theorem selectTop_le_freshBase (named : List Nat) (items : List ParsedItem) :
    selectTop named items ≤ freshBase named items := by
  unfold selectTop
  cases h : findTopCand items with
  | none => exact Nat.le_refl _
  | some a =>
      have hmem : .topCand a ∈ items := findTopCand_mem h
      have hconc : a ∈ itemsConcepts items := by
        unfold itemsConcepts
        exact List.mem_flatMap.mpr ⟨.topCand a, hmem, by simp [itemConcepts]⟩
      exact Nat.le_of_lt (lt_freshBase_of_mem_itemsConcepts hconc)

/-- First `nf5` concept in `items`, if any. -/
def findBottomCand : List ParsedItem → Option Nat
  | [] => none
  | .nf5 a :: _ => some a
  | _ :: rest => findBottomCand rest

theorem findBottomCand_mem {items : List ParsedItem} {a : Nat}
    (h : findBottomCand items = some a) : .nf5 a ∈ items := by
  induction items with
  | nil => simp [findBottomCand] at h
  | cons item rest ih =>
      cases item <;> simp [findBottomCand] at h
      case nf5 b =>
        subst h
        exact List.Mem.head _
      all_goals
        exact List.Mem.tail _ (ih h)

/-- Select the distinguished `bottom` concept. -/
def selectBottom (named : List Nat) (items : List ParsedItem) : Nat :=
  match findBottomCand items with
  | some a => a
  | none => freshBase named items + 1

/-- Compile all non-`nf3` items into normal-form clauses. -/
def compileDirect (top bottom : Nat) (seenTop : Bool) :
    List ParsedItem → List (ELCompletion.Clause Nat Nat)
  | [] => []
  | item :: rest =>
      match item with
      | .topCand a =>
          if seenTop then
            .nf1 top a :: compileDirect top bottom true rest
          else
            compileDirect top bottom true rest
      | .nf5 a => .nf5 a :: compileDirect top bottom seenTop rest
      | .nf1 a b => .nf1 a b :: compileDirect top bottom seenTop rest
      | .nf2 a b c => .nf2 a b c :: compileDirect top bottom seenTop rest
      | .nf2Bottom a b => .nf2 a b bottom :: compileDirect top bottom seenTop rest
      | .nf3Role _ _ _ => compileDirect top bottom seenTop rest
      | .nf3Filler _ _ _ => compileDirect top bottom seenTop rest
      | .nf4 r b c => .nf4 r b c :: compileDirect top bottom seenTop rest
      | .nf4Top r c => .nf4 r top c :: compileDirect top bottom seenTop rest
      | .nf6 r s => .nf6 r s :: compileDirect top bottom seenTop rest
      | .nf7 r s t => .nf7 r s t :: compileDirect top bottom seenTop rest
      | .reflexive r => .reflexive r :: compileDirect top bottom seenTop rest

/-- Direct normal-form clause corresponding to a non-`topCand`, non-`nf3` item. -/
def directClauseOf (top bottom : Nat) : ParsedItem → Option (ELCompletion.Clause Nat Nat)
  | .nf5 a => some (.nf5 a)
  | .nf1 a b => some (.nf1 a b)
  | .nf2 a b c => some (.nf2 a b c)
  | .nf2Bottom a b => some (.nf2 a b bottom)
  | .nf4 r b c => some (.nf4 r b c)
  | .nf4Top r c => some (.nf4 r top c)
  | .nf6 r s => some (.nf6 r s)
  | .nf7 r s t => some (.nf7 r s t)
  | .reflexive r => some (.reflexive r)
  | _ => none

theorem mem_compileDirect_of_directClauseOf {top bottom : Nat} (seenTop : Bool)
    {items : List ParsedItem} {item : ParsedItem} {cl : ELCompletion.Clause Nat Nat}
    (hmem : item ∈ items) (hcl : directClauseOf top bottom item = some cl) :
    cl ∈ compileDirect top bottom seenTop items := by
  induction items generalizing seenTop with
  | nil => contradiction
  | cons head rest ih =>
      rcases List.mem_cons.mp hmem with rfl | htail
      · cases item <;> simp [directClauseOf] at hcl <;>
          subst hcl <;> simp [compileDirect]
      · cases head <;> simp [compileDirect, ih _ htail]
        cases seenTop <;> simp [ih _ htail]

theorem topCand_compileDirect {top bottom : Nat} {seenTop : Bool}
    {items : List ParsedItem} {a : Nat}
    (hmem : .topCand a ∈ items)
    (hfirst : seenTop = false → ∀ b, findTopCand items = some b → b = top) :
    a = top ∨ .nf1 top a ∈ compileDirect top bottom seenTop items := by
  induction items generalizing seenTop with
  | nil => contradiction
  | cons item rest ih =>
      cases item with
      | topCand b =>
          rcases List.mem_cons.mp hmem with hhead | htail
          · cases hhead
            cases seenTop
            · left
              exact hfirst rfl a rfl
            · right
              simp [compileDirect]
          · have hrec : a = top ∨ .nf1 top a ∈ compileDirect top bottom true rest :=
              ih htail (by intro h; cases h)
            rcases hrec with rfl | hcl
            · left; rfl
            · right
              cases seenTop <;> simp [compileDirect, hcl]
      | _ =>
          rcases List.mem_cons.mp hmem with hhead | htail
          · cases hhead
          · have hrec : a = top ∨ .nf1 top a ∈ compileDirect top bottom seenTop rest :=
              ih htail (by
                intro hfalse c hc
                exact hfirst hfalse c (by simpa [findTopCand] using hc))
            rcases hrec with rfl | hcl
            · left; rfl
            · right
              simp [compileDirect, hcl]

theorem compileDirect_models {Domain : Type} {top bottom : Nat}
    (M : TModel Domain)
    (I : ELCompletion.Interp Domain Nat Nat top bottom)
    (hconc : I.concept = M.conc) (hrol : I.role = M.rol)
    {items : List ParsedItem} (seenTop : Bool)
    (hitems : ∀ item ∈ items, satParsedItem M item) :
    ∀ cl ∈ compileDirect top bottom seenTop items, ELCompletion.satClause I cl := by
  induction items generalizing seenTop with
  | nil =>
      intro cl hcl
      cases hcl
  | cons item rest ih =>
      have hhead : satParsedItem M item := hitems item (List.Mem.head _)
      have htail : ∀ x ∈ rest, satParsedItem M x :=
        fun x hx => hitems x (List.Mem.tail _ hx)
      intro cl hcl
      cases item with
      | topCand a =>
          cases seenTop with
          | false =>
              exact ih true htail cl hcl
          | true =>
              rcases List.mem_cons.mp hcl with rfl | hrest
              · intro u _
                rw [hconc]
                exact hhead u
              · exact ih true htail cl hrest
      | nf5 a =>
          rcases List.mem_cons.mp hcl with rfl | hrest
          · intro u hu
            rw [hconc] at hu
            exact hhead u hu
          · exact ih seenTop htail cl hrest
      | nf1 a b =>
          rcases List.mem_cons.mp hcl with rfl | hrest
          · intro u hu
            rw [hconc] at hu ⊢
            exact hhead u hu
          · exact ih seenTop htail cl hrest
      | nf2 a b c =>
          rcases List.mem_cons.mp hcl with rfl | hrest
          · intro u ha hb
            rw [hconc] at ha hb ⊢
            exact hhead u ha hb
          · exact ih seenTop htail cl hrest
      | nf2Bottom a b =>
          rcases List.mem_cons.mp hcl with rfl | hrest
          · intro u ha hb
            rw [hconc] at ha hb
            exact False.elim (hhead u ha hb)
          · exact ih seenTop htail cl hrest
      | nf3Role a r f =>
          exact ih seenTop htail cl hcl
      | nf3Filler a b f =>
          exact ih seenTop htail cl hcl
      | nf4 r b c =>
          rcases List.mem_cons.mp hcl with rfl | hrest
          · intro u ⟨v, hrv, hbv⟩
            rw [hrol] at hrv
            rw [hconc] at hbv ⊢
            exact hhead u ⟨v, hrv, hbv⟩
          · exact ih seenTop htail cl hrest
      | nf4Top r c =>
          rcases List.mem_cons.mp hcl with rfl | hrest
          · intro u ⟨v, hrv, _⟩
            rw [hrol] at hrv
            rw [hconc]
            exact hhead u ⟨v, hrv⟩
          · exact ih seenTop htail cl hrest
      | nf6 r s =>
          rcases List.mem_cons.mp hcl with rfl | hrest
          · intro u v hrv
            rw [hrol] at hrv ⊢
            exact hhead u v hrv
          · exact ih seenTop htail cl hrest
      | nf7 r s t =>
          rcases List.mem_cons.mp hcl with rfl | hrest
          · intro u v w hruv hsvw
            rw [hrol] at hruv hsvw ⊢
            exact hhead u v w hruv hsvw
          · exact ih seenTop htail cl hrest
      | reflexive r =>
          rcases List.mem_cons.mp hcl with rfl | hrest
          · intro u
            rw [hrol]
            exact hhead u
          · exact ih seenTop htail cl hrest

/-- Collect `(fn, sub, role)` for every `nf3Role` item. -/
def collectRoleHalves : List ParsedItem → List (Nat × Nat × Nat)
  | [] => []
  | .nf3Role a r f :: rest => (f, a, r) :: collectRoleHalves rest
  | _ :: rest => collectRoleHalves rest

/-- Collect `(fn, sub, filler)` for every `nf3Filler` item. -/
def collectFillerHalves : List ParsedItem → List (Nat × Nat × Nat)
  | [] => []
  | .nf3Filler a b f :: rest => (f, a, b) :: collectFillerHalves rest
  | _ :: rest => collectFillerHalves rest

theorem mem_collectRoleHalves {items : List ParsedItem} {f a r : Nat} :
    (f, a, r) ∈ collectRoleHalves items ↔ .nf3Role a r f ∈ items := by
  induction items with
  | nil => simp [collectRoleHalves]
  | cons item rest ih =>
      cases item <;> simp [collectRoleHalves, ih]
      case nf3Role a' r' f' =>
        constructor
        · rintro (⟨rfl, rfl, rfl⟩ | h)
          · left; exact ⟨rfl, rfl, rfl⟩
          · right; exact h
        · rintro (⟨rfl, rfl, rfl⟩ | h)
          · left; exact ⟨rfl, rfl, rfl⟩
          · right; exact h

theorem mem_collectFillerHalves {items : List ParsedItem} {f a b : Nat} :
    (f, a, b) ∈ collectFillerHalves items ↔ .nf3Filler a b f ∈ items := by
  induction items with
  | nil => simp [collectFillerHalves]
  | cons item rest ih =>
      cases item <;> simp [collectFillerHalves, ih]
      case nf3Filler a' b' f' =>
        constructor
        · rintro (⟨rfl, rfl, rfl⟩ | h)
          · left; exact ⟨rfl, rfl, rfl⟩
          · right; exact h
        · rintro (⟨rfl, rfl, rfl⟩ | h)
          · left; exact ⟨rfl, rfl, rfl⟩
          · right; exact h

/-- Look up a function symbol in a list of `(fn, sub, payload)` triples. -/
def lookupHalf (f : Nat) : List (Nat × Nat × Nat) → Option (Nat × Nat)
  | [] => none
  | (f', a, x) :: rest => if f' = f then some (a, x) else lookupHalf f rest

theorem lookupHalf_mem {f a x : Nat} {halves : List (Nat × Nat × Nat)}
    (h : lookupHalf f halves = some (a, x)) : (f, a, x) ∈ halves := by
  induction halves with
  | nil => simp [lookupHalf] at h
  | cons head rest ih =>
      rcases head with ⟨f', a', x'⟩
      simp only [lookupHalf] at h
      split at h
      · rename_i heq
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        subst heq
        exact List.Mem.head _
      · exact List.Mem.tail _ (ih h)

theorem mem_lookupHalf_of_nodup {f a x : Nat} {halves : List (Nat × Nat × Nat)}
    (hnodup : (halves.map Prod.fst).Nodup) (hmem : (f, a, x) ∈ halves) :
    lookupHalf f halves = some (a, x) := by
  induction halves with
  | nil => contradiction
  | cons head rest ih =>
      rcases head with ⟨f', a', x'⟩
      simp only [List.map_cons, List.nodup_cons] at hnodup
      rcases hnodup with ⟨hnotmem, htailNodup⟩
      rcases List.mem_cons.mp hmem with heq | htail
      · simp only [Prod.mk.injEq] at heq
        rcases heq with ⟨rfl, rfl, rfl⟩
        simp [lookupHalf]
      · have hne : f' ≠ f := by
          intro hfeq
          apply hnotmem
          subst hfeq
          exact List.mem_map.mpr ⟨(f', a, x), htail, rfl⟩
        simp [lookupHalf, hne, ih htailNodup htail]

/-- Check whether `(f, a, _)` has a partner with matching subject `a` in `other`. -/
def halfMatches (other : List (Nat × Nat × Nat)) (p : Nat × Nat × Nat) : Bool :=
  match lookupHalf p.1 other with
  | some (a', _) => decide (p.2.1 = a')
  | none => false

/-- Validate and pair `nf3` role and filler halves into `.nf3` clauses. -/
def buildNF3Clauses (roles fillers : List (Nat × Nat × Nat)) :
    Option (List (ELCompletion.Clause Nat Nat)) :=
  if (roles.map Prod.fst).Nodup && (fillers.map Prod.fst).Nodup &&
      roles.all (halfMatches fillers) &&
      fillers.all (halfMatches roles) then
    some (roles.filterMap fun (f, a, r) =>
      match lookupHalf f fillers with
      | some (_, b) => some (.nf3 a r b)
      | none => none)
  else
    none

theorem halfMatches_iff {other : List (Nat × Nat × Nat)} {f a x : Nat} :
    halfMatches other (f, a, x) = true ↔ ∃ y, lookupHalf f other = some (a, y) := by
  unfold halfMatches
  cases h : lookupHalf f other with
  | none => simp
  | some pair =>
      rcases pair with ⟨a', y⟩
      simp only [Option.some.injEq, Prod.mk.injEq, decide_eq_true_eq]
      constructor
      · intro heq
        exact ⟨y, heq.symm, rfl⟩
      · rintro ⟨y', ha, _⟩
        exact ha.symm

theorem buildNF3Clauses_role_mem {roles fillers : List (Nat × Nat × Nat)}
    {nf3Clauses : List (ELCompletion.Clause Nat Nat)}
    (hbuild : buildNF3Clauses roles fillers = some nf3Clauses)
    {f a r : Nat} (hmem : (f, a, r) ∈ roles) :
    lookupHalf f roles = some (a, r) ∧
      ∃ b, lookupHalf f fillers = some (a, b) ∧ .nf3 a r b ∈ nf3Clauses := by
  unfold buildNF3Clauses at hbuild
  split at hbuild
  · rename_i hcond
    simp only [Option.some.injEq] at hbuild
    subst hbuild
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hcond
    rcases hcond with ⟨⟨⟨hroleNodup, _⟩, hrolesAll⟩, _⟩
    have hroleLookup := mem_lookupHalf_of_nodup hroleNodup hmem
    obtain ⟨b, hfillerLookup⟩ := halfMatches_iff.mp (hrolesAll (f, a, r) hmem)
    refine ⟨hroleLookup, b, hfillerLookup, ?_⟩
    exact List.mem_filterMap.mpr ⟨(f, a, r), hmem, by simp [hfillerLookup]⟩
  · simp at hbuild

theorem buildNF3Clauses_filler_mem {roles fillers : List (Nat × Nat × Nat)}
    {nf3Clauses : List (ELCompletion.Clause Nat Nat)}
    (hbuild : buildNF3Clauses roles fillers = some nf3Clauses)
    {f a b : Nat} (hmem : (f, a, b) ∈ fillers) :
    lookupHalf f fillers = some (a, b) ∧
      ∃ r, lookupHalf f roles = some (a, r) ∧ .nf3 a r b ∈ nf3Clauses := by
  unfold buildNF3Clauses at hbuild
  split at hbuild
  · rename_i hcond
    simp only [Option.some.injEq] at hbuild
    subst hbuild
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hcond
    rcases hcond with ⟨⟨⟨_, hfillerNodup⟩, _⟩, hfillersAll⟩
    have hfillerLookup := mem_lookupHalf_of_nodup hfillerNodup hmem
    obtain ⟨r, hroleLookup⟩ := halfMatches_iff.mp (hfillersAll (f, a, b) hmem)
    have hroleMem : (f, a, r) ∈ roles := lookupHalf_mem hroleLookup
    refine ⟨hfillerLookup, r, hroleLookup, ?_⟩
    exact List.mem_filterMap.mpr ⟨(f, a, r), hroleMem, by simp [hfillerLookup]⟩
  · simp at hbuild

theorem buildNF3Clauses_clause_mem {roles fillers : List (Nat × Nat × Nat)}
    {nf3Clauses : List (ELCompletion.Clause Nat Nat)}
    (hbuild : buildNF3Clauses roles fillers = some nf3Clauses)
    {cl : ELCompletion.Clause Nat Nat} (hcl : cl ∈ nf3Clauses) :
    ∃ f a r b, cl = .nf3 a r b ∧ (f, a, r) ∈ roles ∧ (f, a, b) ∈ fillers := by
  unfold buildNF3Clauses at hbuild
  split at hbuild
  · rename_i hcond
    simp only [Option.some.injEq] at hbuild
    subst hbuild
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hcond
    rcases hcond with ⟨⟨_, hrolesAll⟩, _⟩
    rcases List.mem_filterMap.mp hcl with ⟨⟨f, a, r⟩, hroleMem, hfilter⟩
    obtain ⟨b, hfillerLookup⟩ := halfMatches_iff.mp (hrolesAll (f, a, r) hroleMem)
    simp only [hfillerLookup, Option.some.injEq] at hfilter
    subst hfilter
    exact ⟨f, a, r, b, rfl, hroleMem, lookupHalf_mem hfillerLookup⟩
  · simp at hbuild

/-- Witness function interpretation built from an `ELCompletion.Interp`. -/
noncomputable def witnessFn {Domain : Type} {top bottom : Nat}
    (I : ELCompletion.Interp Domain Nat Nat top bottom)
    (roles fillers : List (Nat × Nat × Nat)) (f : Nat) (x : Domain) : Domain := by
  classical
  exact match lookupHalf f roles, lookupHalf f fillers with
  | some (_, r), some (_, b) =>
      if h : ∃ y, I.role r x y ∧ I.concept b y then Classical.choose h else x
  | _, _ => x

theorem witnessFn_spec {Domain : Type} {top bottom : Nat}
    {I : ELCompletion.Interp Domain Nat Nat top bottom}
    {roles fillers : List (Nat × Nat × Nat)} {f a r a' b : Nat} {x : Domain}
    (hrole : lookupHalf f roles = some (a, r))
    (hfiller : lookupHalf f fillers = some (a', b))
    (hex : ∃ y, I.role r x y ∧ I.concept b y) :
    I.role r x (witnessFn I roles fillers f x) ∧
      I.concept b (witnessFn I roles fillers f x) := by
  classical
  have hfn : witnessFn I roles fillers f x = Classical.choose hex := by
    simp [witnessFn, hrole, hfiller, hex]
  rw [hfn]
  exact Classical.choose_spec hex

/-- First-order model built from an `ELCompletion.Interp`. -/
noncomputable def modelOfInterp {Domain : Type} {top bottom : Nat}
    (fallback : Domain)
    (I : ELCompletion.Interp Domain Nat Nat top bottom)
    (roles fillers : List (Nat × Nat × Nat)) : TModel Domain where
  conc := I.concept
  rol := I.role
  const := fun _ => fallback
  fn := witnessFn I roles fillers

/-- Assemble `RecognizedEL` from parsed items. -/
def recognizeItems (named : List Nat) (items : List ParsedItem) : Option RecognizedEL :=
  let top := selectTop named items
  let bottom := selectBottom named items
  let roles := collectRoleHalves items
  let fillers := collectFillerHalves items
  match buildNF3Clauses roles fillers with
  | none => none
  | some nf3Clauses =>
      some {
        top := top
        bottom := bottom
        ontology := compileDirect top bottom false items ++ nf3Clauses
      }

theorem recognizeItems_models_to_satParsedItem {Domain : Type}
    {named : List Nat} {items : List ParsedItem} {recognized : RecognizedEL}
    (hrec : recognizeItems named items = some recognized)
    (fallback : Domain)
    (I : ELCompletion.Interp Domain Nat Nat recognized.top recognized.bottom)
    (hI : ELCompletion.models I recognized.ontology) :
    ∀ item ∈ items,
      satParsedItem (modelOfInterp fallback I (collectRoleHalves items) (collectFillerHalves items)) item := by
  unfold recognizeItems at hrec
  cases hbuild : buildNF3Clauses (collectRoleHalves items) (collectFillerHalves items) with
  | none => simp [hbuild] at hrec
  | some nf3Clauses =>
      simp only [hbuild, Option.some.injEq] at hrec
      rcases recognized with ⟨top, bottom, ontology⟩
      simp only [RecognizedEL.mk.injEq] at hrec
      rcases hrec with ⟨htopEq, hbotEq, hontEq⟩
      subst htopEq; subst hbotEq; subst hontEq
      intro item hmem
      have hdirect : ∀ cl, directClauseOf (selectTop named items) (selectBottom named items) item = some cl →
          ELCompletion.satClause I cl := by
        intro cl hcl
        apply hI cl
        exact List.mem_append_left _ (mem_compileDirect_of_directClauseOf false hmem hcl)
      cases item with
      | topCand a =>
          have htopOr := topCand_compileDirect (top := selectTop named items)
            (bottom := selectBottom named items) (seenTop := false) hmem (by
              intro _ b hb
              simp [selectTop, hb])
          rcases htopOr with rfl | hnf1
          · intro u
            exact I.top_true u
          · have hsat : ELCompletion.satClause I (.nf1 (selectTop named items) a) :=
              hI _ (List.mem_append_left _ hnf1)
            intro u
            exact hsat u (I.top_true u)
      | nf5 a =>
          exact hdirect (.nf5 a) rfl
      | nf1 a b =>
          exact hdirect (.nf1 a b) rfl
      | nf2 a b c =>
          exact hdirect (.nf2 a b c) rfl
      | nf2Bottom a b =>
          have hsat := hdirect (.nf2 a b (selectBottom named items)) rfl
          intro u ha hb
          exact I.bottom_false u (hsat u ha hb)
      | nf4 r b c =>
          exact hdirect (.nf4 r b c) rfl
      | nf4Top r c =>
          have hsat := hdirect (.nf4 r (selectTop named items) c) rfl
          intro u ⟨v, hrv⟩
          exact hsat u ⟨v, hrv, I.top_true v⟩
      | nf6 r s =>
          exact hdirect (.nf6 r s) rfl
      | nf7 r s t =>
          exact hdirect (.nf7 r s t) rfl
      | reflexive r =>
          exact hdirect (.reflexive r) rfl
      | nf3Role a r f =>
          have hroleMem : (f, a, r) ∈ collectRoleHalves items :=
            mem_collectRoleHalves.mpr hmem
          obtain ⟨hroleLookup, b, hfillerLookup, hnf3Mem⟩ :=
            buildNF3Clauses_role_mem hbuild hroleMem
          have hsat : ELCompletion.satClause I (.nf3 a r b) :=
            hI _ (List.mem_append_right _ hnf3Mem)
          intro u hu
          exact (witnessFn_spec hroleLookup hfillerLookup (hsat u hu)).1
      | nf3Filler a b f =>
          have hfillerMem : (f, a, b) ∈ collectFillerHalves items :=
            mem_collectFillerHalves.mpr hmem
          obtain ⟨hfillerLookup, r, hroleLookup, hnf3Mem⟩ :=
            buildNF3Clauses_filler_mem hbuild hfillerMem
          have hsat : ELCompletion.satClause I (.nf3 a r b) :=
            hI _ (List.mem_append_right _ hnf3Mem)
          intro u hu
          exact (witnessFn_spec hroleLookup hfillerLookup (hsat u hu)).2

theorem adjustModelTop {Domain : Type} (named : List Nat) (items : List ParsedItem)
    (M : TModel Domain) (hitems : ∀ item ∈ items, satParsedItem M item) :
    ∃ M₁ : TModel Domain,
      (∀ item ∈ items, satParsedItem M₁ item) ∧
      (∀ u, M₁.conc (selectTop named items) u) ∧
      (∀ c ∈ named, M₁.conc c = M.conc c) := by
  unfold selectTop
  cases hfind : findTopCand items with
  | some a =>
      refine ⟨M, hitems, ?_, fun _ _ => rfl⟩
      exact hitems (.topCand a) (findTopCand_mem hfind)
  | none =>
      let top := freshBase named items
      let M₁ : TModel Domain := {
        M with
        conc := fun c u => if c = top then True else M.conc c u
      }
      refine ⟨M₁, ?_, ?_, ?_⟩
      · intro item hmem
        apply (satParsedItem_congr (M₁ := M₁) (M₂ := M) rfl rfl ?_).mpr (hitems item hmem)
        intro c hc
        have hlt : c < top := lt_freshBase_of_mem_itemsConcepts
          (List.mem_flatMap.mpr ⟨item, hmem, hc⟩)
        have hne : c ≠ top := Nat.ne_of_lt hlt
        simp [M₁, hne]
      · intro u
        simp [M₁, top]
      · intro c hc
        have hne : c ≠ top := Nat.ne_of_lt (lt_freshBase_of_mem_named hc)
        simp [M₁, hne]

theorem adjustModelBottom {Domain : Type} (named : List Nat) (items : List ParsedItem)
    (M₁ : TModel Domain) (hitems₁ : ∀ item ∈ items, satParsedItem M₁ item)
    (htop₁ : ∀ u, M₁.conc (selectTop named items) u) :
    ∃ M₂ : TModel Domain,
      (∀ item ∈ items, satParsedItem M₂ item) ∧
      (∀ u, M₂.conc (selectTop named items) u) ∧
      (∀ u, ¬ M₂.conc (selectBottom named items) u) ∧
      (∀ c ∈ named, M₂.conc c = M₁.conc c) := by
  unfold selectBottom
  cases hfind : findBottomCand items with
  | some b =>
      refine ⟨M₁, hitems₁, htop₁, ?_, fun _ _ => rfl⟩
      exact hitems₁ (.nf5 b) (findBottomCand_mem hfind)
  | none =>
      let bottom := freshBase named items + 1
      let M₂ : TModel Domain := {
        M₁ with
        conc := fun c u => if c = bottom then False else M₁.conc c u
      }
      refine ⟨M₂, ?_, ?_, ?_, ?_⟩
      · intro item hmem
        apply (satParsedItem_congr (M₁ := M₂) (M₂ := M₁) rfl rfl ?_).mpr (hitems₁ item hmem)
        intro c hc
        have hlt : c < freshBase named items := lt_freshBase_of_mem_itemsConcepts
          (List.mem_flatMap.mpr ⟨item, hmem, hc⟩)
        have hne : c ≠ bottom := Nat.ne_of_lt (Nat.lt_succ_of_lt hlt)
        simp [M₂, hne]
      · intro u
        have hle : selectTop named items ≤ freshBase named items :=
          selectTop_le_freshBase named items
        have hne : selectTop named items ≠ bottom :=
          Nat.ne_of_lt (Nat.lt_succ_of_le hle)
        simpa [M₂, hne] using htop₁ u
      · intro u
        simp [M₂, bottom]
      · intro c hc
        have hlt : c < freshBase named items := lt_freshBase_of_mem_named hc
        have hne : c ≠ bottom := Nat.ne_of_lt (Nat.lt_succ_of_lt hlt)
        simp [M₂, hne]

theorem recognizeItems_satParsedItem_to_models {Domain : Type}
    {named : List Nat} {items : List ParsedItem} {recognized : RecognizedEL}
    (hrec : recognizeItems named items = some recognized)
    (M : TModel Domain) (hitems : ∀ item ∈ items, satParsedItem M item) :
    ∃ I : ELCompletion.Interp Domain Nat Nat recognized.top recognized.bottom,
      (∀ c ∈ named, I.concept c = M.conc c) ∧
      ELCompletion.models I recognized.ontology := by
  unfold recognizeItems at hrec
  cases hbuild : buildNF3Clauses (collectRoleHalves items) (collectFillerHalves items) with
  | none => simp [hbuild] at hrec
  | some nf3Clauses =>
      simp only [hbuild, Option.some.injEq] at hrec
      rcases recognized with ⟨top, bottom, ontology⟩
      simp only [RecognizedEL.mk.injEq] at hrec
      rcases hrec with ⟨htopEq, hbotEq, hontEq⟩
      subst htopEq; subst hbotEq; subst hontEq
      obtain ⟨M₁, hitems₁, htop₁, hnamed₁⟩ := adjustModelTop named items M hitems
      obtain ⟨M₂, hitems₂, htop₂, hbot₂, hnamed₂⟩ :=
        adjustModelBottom named items M₁ hitems₁ htop₁
      let I : ELCompletion.Interp Domain Nat Nat (selectTop named items) (selectBottom named items) := {
        concept := M₂.conc
        role := M₂.rol
        top_true := htop₂
        bottom_false := hbot₂
      }
      refine ⟨I, ?_, ?_⟩
      · intro c hc
        exact (hnamed₂ c hc).trans (hnamed₁ c hc)
      · intro cl hcl
        rcases List.mem_append.mp hcl with hdirect | hnf3
        · exact compileDirect_models M₂ I rfl rfl false hitems₂ cl hdirect
        · obtain ⟨f, a, r, b, rfl, hroleMem, hfillerMem⟩ :=
            buildNF3Clauses_clause_mem hbuild hnf3
          have hroleSat : satParsedItem M₂ (.nf3Role a r f) :=
            hitems₂ (.nf3Role a r f) (mem_collectRoleHalves.mp hroleMem)
          have hfillerSat : satParsedItem M₂ (.nf3Filler a b f) :=
            hitems₂ (.nf3Filler a b f) (mem_collectFillerHalves.mp hfillerMem)
          intro u hu
          exact ⟨M₂.fn f u, hroleSat u hu, hfillerSat u hu⟩

/-- Read the common clause source as a pure EL ontology.  Fails closed
(`none`) on any clause outside the table above.  The requested names are
needed only to keep fresh distinguished names apart from them. -/
def recognizeEL (named : List Nat) (source : List FCL) : Option RecognizedEL :=
  match parseSource source with
  | none => none
  | some items => recognizeItems named items

/-- The semantic obligation of the recogniser: for every pair of requested
names, the common-source entailment and the EL entailment of the reading
agree. -/
theorem recognizeEL_entails_iff (named : List Nat) (source : List FCL)
    (recognized : RecognizedEL)
    (hrecognized : recognizeEL named source = some recognized)
    {sub sup : Nat} (hsub : sub ∈ named) (hsup : sup ∈ named) :
    Entails source sub sup ↔
      ELCompletion.EntailsSub (top := recognized.top) (bottom := recognized.bottom)
        recognized.ontology sub sup := by
  unfold recognizeEL at hrecognized
  cases hparse : parseSource source with
  | none => simp [hparse] at hrecognized
  | some items =>
      simp only [hparse] at hrecognized
      constructor
      · intro hentails Domain I hmodels x hx
        let M := modelOfInterp x I (collectRoleHalves items) (collectFillerHalves items)
        have hsatItems := recognizeItems_models_to_satParsedItem hrecognized x I hmodels
        have hvalid := (parseSource_valid_iff hparse M).mpr hsatItems
        exact hentails Domain M hvalid x hx
      · intro hentails Domain M hvalid x hx
        have hsatItems := (parseSource_valid_iff hparse M).mp hvalid
        obtain ⟨I, hnamed, hmodels⟩ :=
          recognizeItems_satParsedItem_to_models hrecognized M hsatItems
        have hsubEq : I.concept sub = M.conc sub := hnamed sub hsub
        have hsupEq : I.concept sup = M.conc sup := hnamed sup hsup
        have hx' : I.concept sub x := hsubEq ▸ hx
        have hy' : I.concept sup x := hentails I hmodels x hx'
        exact hsupEq ▸ hy'

/-- Inconsistency of the common source agrees with EL inconsistency of the
reading.  `Unsatisfiable source concept` for a concept that is `top` of the
reading is the common-source form of inconsistency. -/
theorem recognizeEL_unsat_iff (named : List Nat) (source : List FCL)
    (recognized : RecognizedEL)
    (hrecognized : recognizeEL named source = some recognized) :
    (∀ (Domain : Type) [Nonempty Domain] (model : TModel Domain),
        (∀ clause ∈ source, valid model clause) → False) ↔
      ELCompletion.Unsatisfiable (top := recognized.top)
        (bottom := recognized.bottom) recognized.ontology := by
  unfold recognizeEL at hrecognized
  cases hparse : parseSource source with
  | none => simp [hparse] at hrecognized
  | some items =>
      simp only [hparse] at hrecognized
      constructor
      · intro hunsat Domain inst I hmodels
        rcases inst with ⟨fallback⟩
        let M := modelOfInterp fallback I (collectRoleHalves items) (collectFillerHalves items)
        have hsatItems := recognizeItems_models_to_satParsedItem hrecognized fallback I hmodels
        have hvalid := (parseSource_valid_iff hparse M).mpr hsatItems
        exact @hunsat Domain ⟨fallback⟩ M hvalid
      · intro hunsat Domain inst M hvalid
        have hsatItems := (parseSource_valid_iff hparse M).mp hvalid
        obtain ⟨I, _, hmodels⟩ :=
          recognizeItems_satParsedItem_to_models hrecognized M hsatItems
        exact @hunsat Domain inst I hmodels

#print axioms recognizeEL_entails_iff
#print axioms recognizeEL_unsat_iff

end ContextCalculus.ELCommonSourceRecognizer
