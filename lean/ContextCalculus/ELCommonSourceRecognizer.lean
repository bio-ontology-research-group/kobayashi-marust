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
| `⟨[C a1 x, …, C an x], [C d x]⟩` (`n ≥ 3`) | `nf2 a1 a2 p2`, `nf2 p2 a3 p3`, …, `nf2 p(n-1) an d` (fresh `pk`) |
| `⟨[C a1 x, …, C an x], []⟩` (`n ≥ 3`) | `nf2 a1 a2 p2`, `nf2 p2 a3 p3`, …, `nf2 p(n-1) an bottom` (fresh `pk`) |
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
  | naryConj (a1 a2 a3 : Nat) (rest : List Nat) (d : Nat)
  | naryConjBottom (a1 a2 a3 : Nat) (rest : List Nat)
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
  | .naryConj a1 a2 a3 rest d => a1 :: a2 :: a3 :: d :: rest
  | .naryConjBottom a1 a2 a3 rest => a1 :: a2 :: a3 :: rest
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
  | .naryConj a1 a2 a3 rest d =>
      ∀ x, M.conc a1 x → M.conc a2 x → M.conc a3 x →
        (∀ c ∈ rest, M.conc c x) → M.conc d x
  | .naryConjBottom a1 a2 a3 rest =>
      ∀ x, M.conc a1 x → M.conc a2 x → M.conc a3 x →
        (∀ c ∈ rest, M.conc c x) → False
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
  | naryConj a1 a2 a3 rest d =>
      have ha1 : M₁.conc a1 = M₂.conc a1 := hconc a1 (by simp [itemConcepts])
      have ha2 : M₁.conc a2 = M₂.conc a2 := hconc a2 (by simp [itemConcepts])
      have ha3 : M₁.conc a3 = M₂.conc a3 := hconc a3 (by simp [itemConcepts])
      have hd : M₁.conc d = M₂.conc d := hconc d (by simp [itemConcepts])
      have hrest : ∀ x, (∀ c ∈ rest, M₁.conc c x) ↔ (∀ c ∈ rest, M₂.conc c x) := by
        intro x
        refine forall_congr' fun c => imp_congr_right fun hc => ?_
        rw [hconc c (by simp [itemConcepts, hc])]
      simp [satParsedItem, ha1, ha2, ha3, hd, hrest]
  | naryConjBottom a1 a2 a3 rest =>
      have ha1 : M₁.conc a1 = M₂.conc a1 := hconc a1 (by simp [itemConcepts])
      have ha2 : M₁.conc a2 = M₂.conc a2 := hconc a2 (by simp [itemConcepts])
      have ha3 : M₁.conc a3 = M₂.conc a3 := hconc a3 (by simp [itemConcepts])
      have hrest : ∀ x, (∀ c ∈ rest, M₁.conc c x) ↔ (∀ c ∈ rest, M₂.conc c x) := by
        intro x
        refine forall_congr' fun c => imp_congr_right fun hc => ?_
        rw [hconc c (by simp [itemConcepts, hc])]
      simp [satParsedItem, ha1, ha2, ha3, hrest]
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

/-- Concept literals on variable `x` for a list of concept identifiers. -/
def conceptVarLits (x : Int) (cs : List Nat) : List FLit :=
  cs.map fun c => .P (.concept c (.var x))

/-- Extract concept identifiers from a list of concept literals on variable `x`. -/
def extractConceptVarLits (x : Int) : (lits : List FLit) →
    Option { cs : List Nat // lits = conceptVarLits x cs }
  | [] => some ⟨[], rfl⟩
  | .P (.concept c (.var x')) :: tail =>
      if h : x' = x then
        match extractConceptVarLits x tail with
        | some ⟨rest, hrest⟩ =>
            some ⟨c :: rest, by subst h; simp [conceptVarLits, hrest]⟩
        | none => none
      else none
  | _ => none

theorem evalL_conceptVarLits_iff {Domain : Type} (M : TModel Domain)
    (ρ : Int → Domain) (x : Int) (cs : List Nat) :
    (∀ l ∈ conceptVarLits x cs, M.evalL ρ l) ↔ ∀ c ∈ cs, M.conc c (ρ x) := by
  simp [conceptVarLits, TModel.evalL, TModel.evalT]

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
  | naryConj (a1 a2 a3 : Nat) (rest : List Nat) (d : Nat) (x : Int) :
      ClauseItemEvidence
        ⟨.P (.concept a1 (.var x)) :: .P (.concept a2 (.var x)) ::
          .P (.concept a3 (.var x)) :: conceptVarLits x rest,
         [.P (.concept d (.var x))]⟩
        (.naryConj a1 a2 a3 rest d)
  | naryConjBottom (a1 a2 a3 : Nat) (rest : List Nat) (x : Int) :
      ClauseItemEvidence
        ⟨.P (.concept a1 (.var x)) :: .P (.concept a2 (.var x)) ::
          .P (.concept a3 (.var x)) :: conceptVarLits x rest,
         []⟩
        (.naryConjBottom a1 a2 a3 rest)
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
  | ⟨.P (.concept a1 (.var x)) :: .P (.concept a2 (.var x')) ::
      .P (.concept a3 (.var x'')) :: tail,
     [.P (.concept d (.var xd))]⟩ =>
      if h : x' = x ∧ x'' = x ∧ xd = x then
        match extractConceptVarLits x tail with
        | some ⟨rest, htail⟩ =>
            some ⟨.naryConj a1 a2 a3 rest d, by
              rcases h with ⟨rfl, rfl, rfl⟩
              subst htail
              exact .naryConj a1 a2 a3 rest d _⟩
        | none => none
      else none
  | ⟨.P (.concept a1 (.var x)) :: .P (.concept a2 (.var x')) ::
      .P (.concept a3 (.var x'')) :: tail,
     []⟩ =>
      if h : x' = x ∧ x'' = x then
        match extractConceptVarLits x tail with
        | some ⟨rest, htail⟩ =>
            some ⟨.naryConjBottom a1 a2 a3 rest, by
              rcases h with ⟨rfl, rfl⟩
              subst htail
              exact .naryConjBottom a1 a2 a3 rest _⟩
        | none => none
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
  | naryConj a1 a2 a3 rest d x =>
      constructor
      · intro hval u ha1 ha2 ha3 hrest
        have hsat := hval (fun _ => u)
        have hbody : ∀ l ∈ (.P (.concept a1 (.var x)) :: .P (.concept a2 (.var x)) ::
            .P (.concept a3 (.var x)) :: conceptVarLits x rest : List FLit),
            M.evalL (fun _ => u) l := by
          intro l hl
          rcases List.mem_cons.mp hl with rfl | hl
          · exact ha1
          · rcases List.mem_cons.mp hl with rfl | hl
            · exact ha2
            · rcases List.mem_cons.mp hl with rfl | hl
              · exact ha3
              · exact (evalL_conceptVarLits_iff M (fun _ => u) x rest).mpr hrest l hl
        simpa [sat, TModel.evalL, TModel.evalT] using hsat hbody
      · intro hsat ρ hbody
        have ha1 : M.conc a1 (ρ x) := hbody (.P (.concept a1 (.var x))) (by simp)
        have ha2 : M.conc a2 (ρ x) := hbody (.P (.concept a2 (.var x))) (by simp)
        have ha3 : M.conc a3 (ρ x) := hbody (.P (.concept a3 (.var x))) (by simp)
        have hrest : ∀ c ∈ rest, M.conc c (ρ x) := by
          apply (evalL_conceptVarLits_iff M ρ x rest).mp
          intro l hl
          exact hbody l (by simp [hl])
        exact ⟨.P (.concept d (.var x)), by simp, hsat (ρ x) ha1 ha2 ha3 hrest⟩
  | naryConjBottom a1 a2 a3 rest x =>
      constructor
      · intro hval u ha1 ha2 ha3 hrest
        have hsat := hval (fun _ => u)
        have hbody : ∀ l ∈ (.P (.concept a1 (.var x)) :: .P (.concept a2 (.var x)) ::
            .P (.concept a3 (.var x)) :: conceptVarLits x rest : List FLit),
            M.evalL (fun _ => u) l := by
          intro l hl
          rcases List.mem_cons.mp hl with rfl | hl
          · exact ha1
          · rcases List.mem_cons.mp hl with rfl | hl
            · exact ha2
            · rcases List.mem_cons.mp hl with rfl | hl
              · exact ha3
              · exact (evalL_conceptVarLits_iff M (fun _ => u) x rest).mpr hrest l hl
        simpa [sat] using hsat hbody
      · intro hsat ρ hbody
        have ha1 : M.conc a1 (ρ x) := hbody (.P (.concept a1 (.var x))) (by simp)
        have ha2 : M.conc a2 (ρ x) := hbody (.P (.concept a2 (.var x))) (by simp)
        have ha3 : M.conc a3 (ρ x) := hbody (.P (.concept a3 (.var x))) (by simp)
        have hrest : ∀ c ∈ rest, M.conc c (ρ x) := by
          apply (evalL_conceptVarLits_iff M ρ x rest).mp
          intro l hl
          exact hbody l (by simp [hl])
        exact False.elim (hsat (ρ x) ha1 ha2 ha3 hrest)
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

theorem selectBottom_le_freshBase_succ (named : List Nat) (items : List ParsedItem) :
    selectBottom named items ≤ freshBase named items + 1 := by
  unfold selectBottom
  cases h : findBottomCand items with
  | none => exact Nat.le_refl _
  | some b =>
      have hmem : .nf5 b ∈ items := findBottomCand_mem h
      have hconc : b ∈ itemsConcepts items := by
        unfold itemsConcepts
        exact List.mem_flatMap.mpr ⟨.nf5 b, hmem, by simp [itemConcepts]⟩
      exact Nat.le_of_lt (Nat.lt_succ_of_lt (lt_freshBase_of_mem_itemsConcepts hconc))

/-- Emit the NF2 prefix chain from accumulator `acc` across `middle :: rem`
ending in `target`, using fresh auxiliary concepts starting at `nextAux`. -/
def compileConjChain (acc middle : Nat) :
    List Nat → (target nextAux : Nat) → List (ELCompletion.Clause Nat Nat)
  | [], target, _ => [.nf2 acc middle target]
  | next :: rest, target, nextAux =>
      .nf2 acc middle nextAux :: compileConjChain nextAux next rest target (nextAux + 1)

/-- Number of fresh auxiliary concepts consumed by one parsed item. -/
def itemAuxCount : ParsedItem → Nat
  | .naryConj _ _ _ rem _ => rem.length + 1
  | .naryConjBottom _ _ _ rem => rem.length + 1
  | _ => 0

/-- Compile all non-`nf3` items into normal-form clauses. -/
def compileDirect (top bottom : Nat) (seenTop : Bool) (nextAux : Nat) :
    List ParsedItem → List (ELCompletion.Clause Nat Nat)
  | [] => []
  | item :: rest =>
      let nextAux' := nextAux + itemAuxCount item
      match item with
      | .topCand a =>
          if seenTop then
            .nf1 top a :: compileDirect top bottom true nextAux' rest
          else
            compileDirect top bottom true nextAux' rest
      | .nf5 a => .nf5 a :: compileDirect top bottom seenTop nextAux' rest
      | .nf1 a b => .nf1 a b :: compileDirect top bottom seenTop nextAux' rest
      | .nf2 a b c => .nf2 a b c :: compileDirect top bottom seenTop nextAux' rest
      | .nf2Bottom a b => .nf2 a b bottom :: compileDirect top bottom seenTop nextAux' rest
      | .naryConj a1 a2 a3 rem d =>
          compileConjChain a1 a2 (a3 :: rem) d nextAux ++
            compileDirect top bottom seenTop nextAux' rest
      | .naryConjBottom a1 a2 a3 rem =>
          compileConjChain a1 a2 (a3 :: rem) bottom nextAux ++
            compileDirect top bottom seenTop nextAux' rest
      | .nf3Role _ _ _ => compileDirect top bottom seenTop nextAux' rest
      | .nf3Filler _ _ _ => compileDirect top bottom seenTop nextAux' rest
      | .nf4 r b c => .nf4 r b c :: compileDirect top bottom seenTop nextAux' rest
      | .nf4Top r c => .nf4 r top c :: compileDirect top bottom seenTop nextAux' rest
      | .nf6 r s => .nf6 r s :: compileDirect top bottom seenTop nextAux' rest
      | .nf7 r s t => .nf7 r s t :: compileDirect top bottom seenTop nextAux' rest
      | .reflexive r => .reflexive r :: compileDirect top bottom seenTop nextAux' rest

/-- Direct normal-form clause corresponding to a non-`topCand`, non-`nf3`, non-nary item. -/
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

theorem mem_compileDirect_of_directClauseOf {top bottom : Nat} (seenTop : Bool) (nextAux : Nat)
    {items : List ParsedItem} {item : ParsedItem} {cl : ELCompletion.Clause Nat Nat}
    (hmem : item ∈ items) (hcl : directClauseOf top bottom item = some cl) :
    cl ∈ compileDirect top bottom seenTop nextAux items := by
  induction items generalizing seenTop nextAux with
  | nil => contradiction
  | cons head rest ih =>
      rcases List.mem_cons.mp hmem with rfl | htail
      · cases item <;> simp [directClauseOf] at hcl <;>
          subst hcl <;> simp [compileDirect]
      · cases head <;> simp [compileDirect, ih _ _ htail]
        cases seenTop <;> simp [ih _ _ htail]

theorem topCand_compileDirect {top bottom : Nat} {seenTop : Bool} (nextAux : Nat)
    {items : List ParsedItem} {a : Nat}
    (hmem : .topCand a ∈ items)
    (hfirst : seenTop = false → ∀ b, findTopCand items = some b → b = top) :
    a = top ∨ .nf1 top a ∈ compileDirect top bottom seenTop nextAux items := by
  induction items generalizing seenTop nextAux with
  | nil => contradiction
  | cons item rest ih =>
      let nextAux' := nextAux + itemAuxCount item
      cases item with
      | topCand b =>
          rcases List.mem_cons.mp hmem with hhead | htail
          · cases hhead
            cases seenTop
            · left
              exact hfirst rfl a rfl
            · right
              simp [compileDirect]
          · have hrec : a = top ∨ .nf1 top a ∈
                compileDirect top bottom true nextAux' rest :=
              ih nextAux' htail (by intro h; cases h)
            rcases hrec with rfl | hcl
            · left; rfl
            · right
              cases seenTop <;> simp [compileDirect, nextAux', hcl]
      | _ =>
          rcases List.mem_cons.mp hmem with hhead | htail
          · cases hhead
          · have hrec : a = top ∨ .nf1 top a ∈
                compileDirect top bottom seenTop nextAux' rest :=
              ih nextAux' htail (by
                intro hfalse c hc
                exact hfirst hfalse c (by simpa [findTopCand] using hc))
            rcases hrec with rfl | hcl
            · left; rfl
            · right
              simp [compileDirect, nextAux', hcl]

theorem sub_compileDirect_of_naryConj {top bottom : Nat} (seenTop : Bool) (nextAux : Nat)
    {items : List ParsedItem} {a1 a2 a3 : Nat} {rem : List Nat} {d : Nat}
    (hmem : .naryConj a1 a2 a3 rem d ∈ items) :
    ∃ aux, ∀ cl ∈ compileConjChain a1 a2 (a3 :: rem) d aux,
      cl ∈ compileDirect top bottom seenTop nextAux items := by
  induction items generalizing seenTop nextAux with
  | nil => contradiction
  | cons head rest ih =>
      rcases List.mem_cons.mp hmem with rfl | htail
      · refine ⟨nextAux, fun cl hcl => ?_⟩
        simp [compileDirect, hcl]
      · obtain ⟨aux, haux⟩ := ih (match head with | .topCand _ => true | _ => seenTop)
          (nextAux + itemAuxCount head) htail
        refine ⟨aux, fun cl hcl => ?_⟩
        have hmemTail := haux cl hcl
        cases head <;> simp [compileDirect] at hmemTail ⊢
        · cases seenTop <;> simp [hmemTail]
        all_goals simp [hmemTail]

theorem sub_compileDirect_of_naryConjBottom {top bottom : Nat} (seenTop : Bool) (nextAux : Nat)
    {items : List ParsedItem} {a1 a2 a3 : Nat} {rem : List Nat}
    (hmem : .naryConjBottom a1 a2 a3 rem ∈ items) :
    ∃ aux, ∀ cl ∈ compileConjChain a1 a2 (a3 :: rem) bottom aux,
      cl ∈ compileDirect top bottom seenTop nextAux items := by
  induction items generalizing seenTop nextAux with
  | nil => contradiction
  | cons head rest ih =>
      rcases List.mem_cons.mp hmem with rfl | htail
      · refine ⟨nextAux, fun cl hcl => ?_⟩
        simp [compileDirect, hcl]
      · obtain ⟨aux, haux⟩ := ih (match head with | .topCand _ => true | _ => seenTop)
          (nextAux + itemAuxCount head) htail
        refine ⟨aux, fun cl hcl => ?_⟩
        have hmemTail := haux cl hcl
        cases head <;> simp [compileDirect] at hmemTail ⊢
        · cases seenTop <;> simp [hmemTail]
        all_goals simp [hmemTail]

theorem compileConjChain_derives {Domain : Type} {top bottom : Nat}
    (I : ELCompletion.Interp Domain Nat Nat top bottom)
    (acc middle : Nat) (rem : List Nat) (target nextAux : Nat)
    (hmodels : ∀ cl ∈ compileConjChain acc middle rem target nextAux,
      ELCompletion.satClause I cl)
    (u : Domain) (hacc : I.concept acc u) (hmid : I.concept middle u)
    (hrem : ∀ c ∈ rem, I.concept c u) :
    I.concept target u := by
  induction rem generalizing acc middle nextAux with
  | nil =>
      have hcl : ELCompletion.satClause I (.nf2 acc middle target) :=
        hmodels _ (by simp [compileConjChain])
      exact hcl u hacc hmid
  | cons next rest ih =>
      have hhead : ELCompletion.satClause I (.nf2 acc middle nextAux) :=
        hmodels _ (by simp [compileConjChain])
      have htail : ∀ cl ∈ compileConjChain nextAux next rest target (nextAux + 1),
          ELCompletion.satClause I cl :=
        fun cl hcl => hmodels cl (by simp [compileConjChain, hcl])
      exact ih nextAux next (nextAux + 1) htail (hhead u hacc hmid)
        (hrem next (List.Mem.head _))
        (fun c hc => hrem c (List.Mem.tail _ hc))

/-- Concept identifiers occurring in one normal-form EL clause. -/
def nfClauseConcepts : ELCompletion.Clause Nat Nat → List Nat
  | .nf1 a b => [a, b]
  | .nf2 a b c => [a, b, c]
  | .nf3 a _ b => [a, b]
  | .nf4 _ b c => [b, c]
  | .nf5 a => [a]
  | .nf6 _ _ => []
  | .nf7 _ _ _ => []
  | .reflexive _ => []

theorem satClause_congr {Domain : Type} {top bottom : Nat}
    {I₁ I₂ : ELCompletion.Interp Domain Nat Nat top bottom}
    {cl : ELCompletion.Clause Nat Nat}
    (hrol : I₁.role = I₂.role)
    (hconc : ∀ c ∈ nfClauseConcepts cl, I₁.concept c = I₂.concept c) :
    ELCompletion.satClause I₁ cl ↔ ELCompletion.satClause I₂ cl := by
  cases cl with
  | nf1 a b =>
      have ha : I₁.concept a = I₂.concept a := hconc a (by simp [nfClauseConcepts])
      have hb : I₁.concept b = I₂.concept b := hconc b (by simp [nfClauseConcepts])
      simp [ELCompletion.satClause, ha, hb]
  | nf2 a b c =>
      have ha : I₁.concept a = I₂.concept a := hconc a (by simp [nfClauseConcepts])
      have hb : I₁.concept b = I₂.concept b := hconc b (by simp [nfClauseConcepts])
      have hc : I₁.concept c = I₂.concept c := hconc c (by simp [nfClauseConcepts])
      simp [ELCompletion.satClause, ha, hb, hc]
  | nf3 a r b =>
      have ha : I₁.concept a = I₂.concept a := hconc a (by simp [nfClauseConcepts])
      have hb : I₁.concept b = I₂.concept b := hconc b (by simp [nfClauseConcepts])
      simp [ELCompletion.satClause, ha, hb, hrol]
  | nf4 r b c =>
      have hb : I₁.concept b = I₂.concept b := hconc b (by simp [nfClauseConcepts])
      have hc : I₁.concept c = I₂.concept c := hconc c (by simp [nfClauseConcepts])
      simp [ELCompletion.satClause, hb, hc, hrol]
  | nf5 a =>
      have ha : I₁.concept a = I₂.concept a := hconc a (by simp [nfClauseConcepts])
      simp [ELCompletion.satClause, ha]
  | nf6 r s =>
      simp [ELCompletion.satClause, hrol]
  | nf7 r s t =>
      simp [ELCompletion.satClause, hrol]
  | reflexive r =>
      simp [ELCompletion.satClause, hrol]

theorem compileConjChain_concepts_lt {acc middle : Nat} {rem : List Nat} {target nextAux : Nat}
    (hacc : acc < nextAux) (hmid : middle < nextAux)
    (hrem : ∀ b ∈ rem, b < nextAux) (htarget : target < nextAux) :
    ∀ cl ∈ compileConjChain acc middle rem target nextAux,
      ∀ c ∈ nfClauseConcepts cl, c < nextAux + rem.length := by
  induction rem generalizing acc middle nextAux with
  | nil =>
      intro cl hcl c hc
      simp only [compileConjChain, List.length_nil, Nat.add_zero, List.mem_singleton] at hcl ⊢
      subst hcl
      simp only [nfClauseConcepts, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;> omega
  | cons next rest ih =>
      intro cl hcl c hc
      have hnext : next < nextAux := hrem next (List.Mem.head _)
      have hrest : ∀ b ∈ rest, b < nextAux := fun b hb => hrem b (List.Mem.tail _ hb)
      simp only [compileConjChain, List.length_cons, List.mem_cons] at hcl ⊢
      rcases hcl with rfl | htail
      · simp only [nfClauseConcepts, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl <;> omega
      · have hlt := ih (acc := nextAux) (middle := next) (nextAux := nextAux + 1)
          (by omega) (by omega)
          (fun b hb => Nat.lt_succ_of_lt (hrest b hb))
          (by omega) cl htail c hc
        omega

/-- Update a single auxiliary concept interpretation in an `ELCompletion.Interp`
when that concept is distinct from `top` and `bottom`. -/
def setAuxConcept {Domain : Type} {top bottom : Nat}
    (I : ELCompletion.Interp Domain Nat Nat top bottom)
    (p : Nat) (P : Domain → Prop)
    (htop : p ≠ top) (hbot : p ≠ bottom) :
    ELCompletion.Interp Domain Nat Nat top bottom where
  concept := fun c u => if c = p then P u else I.concept c u
  role := I.role
  top_true := fun u => by simp [htop.symm, I.top_true u]
  bottom_false := fun u => by simp [hbot.symm, I.bottom_false u]

theorem compileConjChain_extend_interp {Domain : Type} {top bottom : Nat}
    (I : ELCompletion.Interp Domain Nat Nat top bottom)
    (acc middle : Nat) (rem : List Nat) (target nextAux : Nat)
    (htop : top < nextAux) (hbot : bottom < nextAux)
    (hacc : acc < nextAux) (hmid : middle < nextAux)
    (hrem : ∀ b ∈ rem, b < nextAux) (htarget : target < nextAux)
    (hsat : ∀ u, I.concept acc u → I.concept middle u →
      (∀ b ∈ rem, I.concept b u) → I.concept target u) :
    ∃ I' : ELCompletion.Interp Domain Nat Nat top bottom,
      I'.role = I.role ∧
      (∀ c < nextAux, I'.concept c = I.concept c) ∧
      (∀ cl ∈ compileConjChain acc middle rem target nextAux, ELCompletion.satClause I' cl) := by
  induction rem generalizing I acc middle nextAux with
  | nil =>
      refine ⟨I, rfl, fun _ _ => rfl, ?_⟩
      intro cl hcl
      simp only [compileConjChain, List.mem_singleton] at hcl
      subst hcl
      intro u h1 h2
      exact hsat u h1 h2 (by intro b hb; cases hb)
  | cons next rest ih =>
      have hnext : next < nextAux := hrem next (List.Mem.head _)
      have hrest : ∀ b ∈ rest, b < nextAux := fun b hb => hrem b (List.Mem.tail _ hb)
      let I₁ := setAuxConcept I nextAux (fun u => I.concept acc u ∧ I.concept middle u)
        (Nat.ne_of_gt htop) (Nat.ne_of_gt hbot)
      have hacc_ne : acc ≠ nextAux := Nat.ne_of_lt hacc
      have hmid_ne : middle ≠ nextAux := Nat.ne_of_lt hmid
      have hnext_ne : next ≠ nextAux := Nat.ne_of_lt hnext
      have htarget_ne : target ≠ nextAux := Nat.ne_of_lt htarget
      have hsat₁ : ∀ u, I₁.concept nextAux u → I₁.concept next u →
          (∀ b ∈ rest, I₁.concept b u) → I₁.concept target u := by
        intro u hp h3 hall
        have hp' : I.concept acc u ∧ I.concept middle u := by
          simpa [I₁, setAuxConcept] using hp
        have h3' : I.concept next u := by
          simpa [I₁, setAuxConcept, hnext_ne] using h3
        have hall' : ∀ b ∈ next :: rest, I.concept b u := by
          intro b hb
          rcases List.mem_cons.mp hb with rfl | hmem
          · exact h3'
          · have hb_ne : b ≠ nextAux := Nat.ne_of_lt (hrest b hmem)
            have hbu := hall b hmem
            simpa [I₁, setAuxConcept, hb_ne] using hbu
        have htu : I.concept target u := hsat u hp'.1 hp'.2 hall'
        simpa [I₁, setAuxConcept, htarget_ne] using htu
      obtain ⟨I', hrol', hconc', hclauses'⟩ :=
        ih I₁ nextAux next (nextAux + 1)
          (Nat.lt_succ_of_lt htop) (Nat.lt_succ_of_lt hbot)
          (Nat.lt_succ_self _) (Nat.lt_succ_of_lt hnext)
          (fun b hb => Nat.lt_succ_of_lt (hrest b hb))
          (Nat.lt_succ_of_lt htarget)
          hsat₁
      refine ⟨I', hrol', ?_, ?_⟩
      · intro c hc
        have hc1 : I'.concept c = I₁.concept c := hconc' c (Nat.lt_succ_of_lt hc)
        have hne : c ≠ nextAux := Nat.ne_of_lt hc
        rw [hc1]
        funext u
        simp [I₁, setAuxConcept, hne]
      · intro cl hcl
        simp only [compileConjChain, List.mem_cons] at hcl
        rcases hcl with rfl | htail
        · have hsat_head : ELCompletion.satClause I₁ (.nf2 acc middle nextAux) := by
            intro u h1 h2
            have h1' : I.concept acc u := by simpa [I₁, setAuxConcept, hacc_ne] using h1
            have h2' : I.concept middle u := by simpa [I₁, setAuxConcept, hmid_ne] using h2
            simp [I₁, setAuxConcept, h1', h2']
          apply (satClause_congr hrol' ?_).mpr hsat_head
          intro c hc
          simp only [nfClauseConcepts, List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl | rfl
          · exact hconc' c (Nat.lt_succ_of_lt hacc)
          · exact hconc' c (Nat.lt_succ_of_lt hmid)
          · exact hconc' c (Nat.lt_succ_self _)
        · exact hclauses' cl htail

theorem compileDirect_models {Domain : Type} {top bottom : Nat}
    (M : TModel Domain)
    (I : ELCompletion.Interp Domain Nat Nat top bottom)
    {items : List ParsedItem} (seenTop : Bool) (nextAux : Nat)
    (htop : top < nextAux) (hbot : bottom < nextAux)
    (hconcepts : ∀ item ∈ items, ∀ c ∈ itemConcepts item, c < nextAux)
    (hconc : ∀ item ∈ items, ∀ c ∈ itemConcepts item, I.concept c = M.conc c)
    (hrol : I.role = M.rol)
    (hitems : ∀ item ∈ items, satParsedItem M item) :
    ∃ I' : ELCompletion.Interp Domain Nat Nat top bottom,
      I'.role = I.role ∧
      (∀ c < nextAux, I'.concept c = I.concept c) ∧
      (∀ cl ∈ compileDirect top bottom seenTop nextAux items,
        ELCompletion.satClause I' cl) := by
  induction items generalizing I seenTop nextAux with
  | nil =>
      refine ⟨I, rfl, fun _ _ => rfl, ?_⟩
      intro cl hcl
      cases hcl
  | cons item rest ih =>
      have hhead : satParsedItem M item := hitems item (List.Mem.head _)
      have htail : ∀ x ∈ rest, satParsedItem M x :=
        fun x hx => hitems x (List.Mem.tail _ hx)
      have hheadConcepts : ∀ c ∈ itemConcepts item, c < nextAux :=
        hconcepts item (List.Mem.head _)
      have htailConcepts : ∀ x ∈ rest, ∀ c ∈ itemConcepts x, c < nextAux :=
        fun x hx => hconcepts x (List.Mem.tail _ hx)
      have hheadConc : ∀ c ∈ itemConcepts item, I.concept c = M.conc c :=
        hconc item (List.Mem.head _)
      have htailConc : ∀ x ∈ rest, ∀ c ∈ itemConcepts x, I.concept c = M.conc c :=
        fun x hx => hconc x (List.Mem.tail _ hx)
      cases item with
      | topCand a =>
          cases seenTop with
          | false =>
              exact ih I true nextAux htop hbot htailConcepts htailConc hrol htail
          | true =>
              obtain ⟨I', hrol', hpres, hclauses⟩ :=
                ih I true nextAux htop hbot htailConcepts htailConc hrol htail
              refine ⟨I', hrol', hpres, ?_⟩
              intro cl hcl
              rcases List.mem_cons.mp hcl with rfl | hrest
              · have ha_lt : a < nextAux := hheadConcepts a (by simp [itemConcepts])
                have ha_eq : I'.concept a = M.conc a :=
                  (hpres a ha_lt).trans (hheadConc a (by simp [itemConcepts]))
                intro u _
                rw [ha_eq]
                exact hhead u
              · exact hclauses cl hrest
      | nf5 a =>
          obtain ⟨I', hrol', hpres, hclauses⟩ :=
            ih I seenTop nextAux htop hbot htailConcepts htailConc hrol htail
          refine ⟨I', hrol', hpres, ?_⟩
          intro cl hcl
          rcases List.mem_cons.mp hcl with rfl | hrest
          · have ha_lt : a < nextAux := hheadConcepts a (by simp [itemConcepts])
            have ha_eq : I'.concept a = M.conc a :=
              (hpres a ha_lt).trans (hheadConc a (by simp [itemConcepts]))
            intro u hu
            rw [ha_eq] at hu
            exact hhead u hu
          · exact hclauses cl hrest
      | nf1 a b =>
          obtain ⟨I', hrol', hpres, hclauses⟩ :=
            ih I seenTop nextAux htop hbot htailConcepts htailConc hrol htail
          refine ⟨I', hrol', hpres, ?_⟩
          intro cl hcl
          rcases List.mem_cons.mp hcl with rfl | hrest
          · have ha_lt : a < nextAux := hheadConcepts a (by simp [itemConcepts])
            have hb_lt : b < nextAux := hheadConcepts b (by simp [itemConcepts])
            have ha_eq : I'.concept a = M.conc a :=
              (hpres a ha_lt).trans (hheadConc a (by simp [itemConcepts]))
            have hb_eq : I'.concept b = M.conc b :=
              (hpres b hb_lt).trans (hheadConc b (by simp [itemConcepts]))
            intro u hu
            rw [ha_eq] at hu
            rw [hb_eq]
            exact hhead u hu
          · exact hclauses cl hrest
      | nf2 a b c =>
          obtain ⟨I', hrol', hpres, hclauses⟩ :=
            ih I seenTop nextAux htop hbot htailConcepts htailConc hrol htail
          refine ⟨I', hrol', hpres, ?_⟩
          intro cl hcl
          rcases List.mem_cons.mp hcl with rfl | hrest
          · have ha_lt : a < nextAux := hheadConcepts a (by simp [itemConcepts])
            have hb_lt : b < nextAux := hheadConcepts b (by simp [itemConcepts])
            have hc_lt : c < nextAux := hheadConcepts c (by simp [itemConcepts])
            have ha_eq : I'.concept a = M.conc a :=
              (hpres a ha_lt).trans (hheadConc a (by simp [itemConcepts]))
            have hb_eq : I'.concept b = M.conc b :=
              (hpres b hb_lt).trans (hheadConc b (by simp [itemConcepts]))
            have hc_eq : I'.concept c = M.conc c :=
              (hpres c hc_lt).trans (hheadConc c (by simp [itemConcepts]))
            intro u ha hb
            rw [ha_eq] at ha
            rw [hb_eq] at hb
            rw [hc_eq]
            exact hhead u ha hb
          · exact hclauses cl hrest
      | nf2Bottom a b =>
          obtain ⟨I', hrol', hpres, hclauses⟩ :=
            ih I seenTop nextAux htop hbot htailConcepts htailConc hrol htail
          refine ⟨I', hrol', hpres, ?_⟩
          intro cl hcl
          rcases List.mem_cons.mp hcl with rfl | hrest
          · have ha_lt : a < nextAux := hheadConcepts a (by simp [itemConcepts])
            have hb_lt : b < nextAux := hheadConcepts b (by simp [itemConcepts])
            have ha_eq : I'.concept a = M.conc a :=
              (hpres a ha_lt).trans (hheadConc a (by simp [itemConcepts]))
            have hb_eq : I'.concept b = M.conc b :=
              (hpres b hb_lt).trans (hheadConc b (by simp [itemConcepts]))
            intro u ha hb
            rw [ha_eq] at ha
            rw [hb_eq] at hb
            exact False.elim (hhead u ha hb)
          · exact hclauses cl hrest
      | naryConj a1 a2 a3 rem d =>
          have ha1_lt : a1 < nextAux := hheadConcepts a1 (by simp [itemConcepts])
          have ha2_lt : a2 < nextAux := hheadConcepts a2 (by simp [itemConcepts])
          have ha3_lt : a3 < nextAux := hheadConcepts a3 (by simp [itemConcepts])
          have hd_lt : d < nextAux := hheadConcepts d (by simp [itemConcepts])
          have hrem_lt : ∀ b ∈ a3 :: rem, b < nextAux := by
            intro b hb
            rcases List.mem_cons.mp hb with rfl | hmem
            · exact ha3_lt
            · exact hheadConcepts b (by simp [itemConcepts, hmem])
          have ha1_eq : I.concept a1 = M.conc a1 := hheadConc a1 (by simp [itemConcepts])
          have ha2_eq : I.concept a2 = M.conc a2 := hheadConc a2 (by simp [itemConcepts])
          have ha3_eq : I.concept a3 = M.conc a3 := hheadConc a3 (by simp [itemConcepts])
          have hd_eq : I.concept d = M.conc d := hheadConc d (by simp [itemConcepts])
          have hrem_eq : ∀ b ∈ rem, I.concept b = M.conc b :=
            fun b hb => hheadConc b (by simp [itemConcepts, hb])
          have hsatChain : ∀ u, I.concept a1 u → I.concept a2 u →
              (∀ b ∈ a3 :: rem, I.concept b u) → I.concept d u := by
            intro u h1 h2 hall
            have h3 : I.concept a3 u := hall a3 (List.Mem.head _)
            rw [ha1_eq] at h1
            rw [ha2_eq] at h2
            rw [ha3_eq] at h3
            rw [hd_eq]
            apply hhead u h1 h2 h3
            intro b hb
            rw [← hrem_eq b hb]
            exact hall b (List.Mem.tail _ hb)
          obtain ⟨I₁, hrol₁, hpres₁, hchain₁⟩ :=
            compileConjChain_extend_interp I a1 a2 (a3 :: rem) d nextAux
              htop hbot ha1_lt ha2_lt hrem_lt hd_lt hsatChain
          let nextAux' := nextAux + (rem.length + 1)
          have hle : nextAux ≤ nextAux' := Nat.le_add_right _ _
          obtain ⟨I', hrol', hpres', hclauses'⟩ :=
            ih I₁ seenTop nextAux'
              (Nat.lt_of_lt_of_le htop hle)
              (Nat.lt_of_lt_of_le hbot hle)
              (fun x hx c hc => Nat.lt_of_lt_of_le (htailConcepts x hx c hc) hle)
              (fun x hx c hc =>
                (hpres₁ c (htailConcepts x hx c hc)).trans (htailConc x hx c hc))
              (hrol₁.trans hrol)
              htail
          refine ⟨I', hrol'.trans hrol₁, ?_, ?_⟩
          · intro c hc
            exact (hpres' c (Nat.lt_of_lt_of_le hc hle)).trans (hpres₁ c hc)
          · intro cl hcl
            simp only [compileDirect, itemAuxCount] at hcl
            rcases List.mem_append.mp hcl with hchain | hrest
            · have hlt_cl := compileConjChain_concepts_lt ha1_lt ha2_lt hrem_lt hd_lt cl hchain
              apply (satClause_congr hrol' ?_).mpr (hchain₁ cl hchain)
              intro c hc
              exact hpres' c (hlt_cl c hc)
            · exact hclauses' cl hrest
      | naryConjBottom a1 a2 a3 rem =>
          have ha1_lt : a1 < nextAux := hheadConcepts a1 (by simp [itemConcepts])
          have ha2_lt : a2 < nextAux := hheadConcepts a2 (by simp [itemConcepts])
          have ha3_lt : a3 < nextAux := hheadConcepts a3 (by simp [itemConcepts])
          have hrem_lt : ∀ b ∈ a3 :: rem, b < nextAux := by
            intro b hb
            rcases List.mem_cons.mp hb with rfl | hmem
            · exact ha3_lt
            · exact hheadConcepts b (by simp [itemConcepts, hmem])
          have ha1_eq : I.concept a1 = M.conc a1 := hheadConc a1 (by simp [itemConcepts])
          have ha2_eq : I.concept a2 = M.conc a2 := hheadConc a2 (by simp [itemConcepts])
          have ha3_eq : I.concept a3 = M.conc a3 := hheadConc a3 (by simp [itemConcepts])
          have hrem_eq : ∀ b ∈ rem, I.concept b = M.conc b :=
            fun b hb => hheadConc b (by simp [itemConcepts, hb])
          have hsatChain : ∀ u, I.concept a1 u → I.concept a2 u →
              (∀ b ∈ a3 :: rem, I.concept b u) → I.concept bottom u := by
            intro u h1 h2 hall
            have h3 : I.concept a3 u := hall a3 (List.Mem.head _)
            rw [ha1_eq] at h1
            rw [ha2_eq] at h2
            rw [ha3_eq] at h3
            refine False.elim (hhead u h1 h2 h3 ?_)
            intro b hb
            rw [← hrem_eq b hb]
            exact hall b (List.Mem.tail _ hb)
          obtain ⟨I₁, hrol₁, hpres₁, hchain₁⟩ :=
            compileConjChain_extend_interp I a1 a2 (a3 :: rem) bottom nextAux
              htop hbot ha1_lt ha2_lt hrem_lt hbot hsatChain
          let nextAux' := nextAux + (rem.length + 1)
          have hle : nextAux ≤ nextAux' := Nat.le_add_right _ _
          obtain ⟨I', hrol', hpres', hclauses'⟩ :=
            ih I₁ seenTop nextAux'
              (Nat.lt_of_lt_of_le htop hle)
              (Nat.lt_of_lt_of_le hbot hle)
              (fun x hx c hc => Nat.lt_of_lt_of_le (htailConcepts x hx c hc) hle)
              (fun x hx c hc =>
                (hpres₁ c (htailConcepts x hx c hc)).trans (htailConc x hx c hc))
              (hrol₁.trans hrol)
              htail
          refine ⟨I', hrol'.trans hrol₁, ?_, ?_⟩
          · intro c hc
            exact (hpres' c (Nat.lt_of_lt_of_le hc hle)).trans (hpres₁ c hc)
          · intro cl hcl
            simp only [compileDirect, itemAuxCount] at hcl
            rcases List.mem_append.mp hcl with hchain | hrest
            · have hlt_cl := compileConjChain_concepts_lt ha1_lt ha2_lt hrem_lt hbot cl hchain
              apply (satClause_congr hrol' ?_).mpr (hchain₁ cl hchain)
              intro c hc
              exact hpres' c (hlt_cl c hc)
            · exact hclauses' cl hrest
      | nf3Role a r f =>
          exact ih I seenTop nextAux htop hbot htailConcepts htailConc hrol htail
      | nf3Filler a b f =>
          exact ih I seenTop nextAux htop hbot htailConcepts htailConc hrol htail
      | nf4 r b c =>
          obtain ⟨I', hrol', hpres, hclauses⟩ :=
            ih I seenTop nextAux htop hbot htailConcepts htailConc hrol htail
          refine ⟨I', hrol', hpres, ?_⟩
          intro cl hcl
          rcases List.mem_cons.mp hcl with rfl | hrest
          · have hb_lt : b < nextAux := hheadConcepts b (by simp [itemConcepts])
            have hc_lt : c < nextAux := hheadConcepts c (by simp [itemConcepts])
            have hb_eq : I'.concept b = M.conc b :=
              (hpres b hb_lt).trans (hheadConc b (by simp [itemConcepts]))
            have hc_eq : I'.concept c = M.conc c :=
              (hpres c hc_lt).trans (hheadConc c (by simp [itemConcepts]))
            have hrol_eq : I'.role = M.rol := hrol'.trans hrol
            intro u ⟨v, hrv, hbv⟩
            rw [hrol_eq] at hrv
            rw [hb_eq] at hbv
            rw [hc_eq]
            exact hhead u ⟨v, hrv, hbv⟩
          · exact hclauses cl hrest
      | nf4Top r c =>
          obtain ⟨I', hrol', hpres, hclauses⟩ :=
            ih I seenTop nextAux htop hbot htailConcepts htailConc hrol htail
          refine ⟨I', hrol', hpres, ?_⟩
          intro cl hcl
          rcases List.mem_cons.mp hcl with rfl | hrest
          · have hc_lt : c < nextAux := hheadConcepts c (by simp [itemConcepts])
            have hc_eq : I'.concept c = M.conc c :=
              (hpres c hc_lt).trans (hheadConc c (by simp [itemConcepts]))
            have hrol_eq : I'.role = M.rol := hrol'.trans hrol
            intro u ⟨v, hrv, _⟩
            rw [hrol_eq] at hrv
            rw [hc_eq]
            exact hhead u ⟨v, hrv⟩
          · exact hclauses cl hrest
      | nf6 r s =>
          obtain ⟨I', hrol', hpres, hclauses⟩ :=
            ih I seenTop nextAux htop hbot htailConcepts htailConc hrol htail
          refine ⟨I', hrol', hpres, ?_⟩
          intro cl hcl
          rcases List.mem_cons.mp hcl with rfl | hrest
          · have hrol_eq : I'.role = M.rol := hrol'.trans hrol
            intro u v hrv
            rw [hrol_eq] at hrv ⊢
            exact hhead u v hrv
          · exact hclauses cl hrest
      | nf7 r s t =>
          obtain ⟨I', hrol', hpres, hclauses⟩ :=
            ih I seenTop nextAux htop hbot htailConcepts htailConc hrol htail
          refine ⟨I', hrol', hpres, ?_⟩
          intro cl hcl
          rcases List.mem_cons.mp hcl with rfl | hrest
          · have hrol_eq : I'.role = M.rol := hrol'.trans hrol
            intro u v w hruv hsvw
            rw [hrol_eq] at hruv hsvw ⊢
            exact hhead u v w hruv hsvw
          · exact hclauses cl hrest
      | reflexive r =>
          obtain ⟨I', hrol', hpres, hclauses⟩ :=
            ih I seenTop nextAux htop hbot htailConcepts htailConc hrol htail
          refine ⟨I', hrol', hpres, ?_⟩
          intro cl hcl
          rcases List.mem_cons.mp hcl with rfl | hrest
          · have hrol_eq : I'.role = M.rol := hrol'.trans hrol
            intro u
            rw [hrol_eq]
            exact hhead u
          · exact hclauses cl hrest

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

/-- Order `nf3` halves by their function identifier. -/
def halfLe (x y : Nat × Nat × Nat) : Bool :=
  decide (x.1 ≤ y.1)

/-- Fuel-bounded structurally recursive merge of two sorted `nf3` half lists. -/
def mergeHalvesFuel :
    Nat → List (Nat × Nat × Nat) → List (Nat × Nat × Nat) → List (Nat × Nat × Nat)
  | _, [], ys => ys
  | _, xs, [] => xs
  | 0, xs, ys => xs ++ ys
  | fuel + 1, x :: xs, y :: ys =>
      if halfLe x y then
        x :: mergeHalvesFuel fuel xs (y :: ys)
      else
        y :: mergeHalvesFuel fuel (x :: xs) ys

/-- Merge two sorted `nf3` half lists. -/
def mergeHalves (xs ys : List (Nat × Nat × Nat)) : List (Nat × Nat × Nat) :=
  mergeHalvesFuel (xs.length + ys.length) xs ys

/-- Merge adjacent pairs of runs in one bottom-up pass. -/
def mergePairs : List (List (Nat × Nat × Nat)) → List (List (Nat × Nat × Nat))
  | [] => []
  | [xs] => [xs]
  | xs :: ys :: rest => mergeHalves xs ys :: mergePairs rest

/-- Repeatedly merge runs using structural recursion on fuel. -/
def mergeAllRuns : Nat → List (List (Nat × Nat × Nat)) → List (Nat × Nat × Nat)
  | _, [] => []
  | _, [xs] => xs
  | 0, runs => runs.flatten
  | fuel + 1, runs => mergeAllRuns fuel (mergePairs runs)

/-- Bottom-up merge sort on `nf3` halves using structural recursion. -/
def sortHalves (xs : List (Nat × Nat × Nat)) : List (Nat × Nat × Nat) :=
  mergeAllRuns xs.length (xs.map (fun x => [x]))

theorem mergeHalvesFuel_perm (fuel : Nat) (xs ys : List (Nat × Nat × Nat)) :
    (mergeHalvesFuel fuel xs ys).Perm (xs ++ ys) := by
  induction fuel generalizing xs ys with
  | zero =>
      cases xs <;> cases ys <;> simp [mergeHalvesFuel]
  | succ fuel ih =>
      cases xs with
      | nil => simp [mergeHalvesFuel]
      | cons x xs' =>
          cases ys with
          | nil => simp [mergeHalvesFuel]
          | cons y ys' =>
              unfold mergeHalvesFuel
              split
              · exact List.Perm.cons x (ih xs' (y :: ys'))
              · exact (List.Perm.cons y (ih (x :: xs') ys')).trans
                  List.perm_middle.symm

theorem mergeHalves_perm (xs ys : List (Nat × Nat × Nat)) :
    (mergeHalves xs ys).Perm (xs ++ ys) :=
  mergeHalvesFuel_perm (xs.length + ys.length) xs ys

theorem mergePairs_flatten_perm :
    ∀ (runs : List (List (Nat × Nat × Nat))),
      (mergePairs runs).flatten.Perm runs.flatten
  | [] => List.Perm.refl _
  | [xs] => List.Perm.refl _
  | xs :: ys :: rest => by
      simp only [mergePairs, List.flatten_cons, ← List.append_assoc]
      exact (mergeHalves_perm xs ys).append (mergePairs_flatten_perm rest)

theorem mergeAllRuns_perm (fuel : Nat) (runs : List (List (Nat × Nat × Nat))) :
    (mergeAllRuns fuel runs).Perm runs.flatten := by
  induction fuel generalizing runs with
  | zero =>
      cases runs with
      | nil => simp [mergeAllRuns]
      | cons r rs =>
          cases rs <;> simp [mergeAllRuns]
  | succ fuel ih =>
      cases runs with
      | nil => simp [mergeAllRuns]
      | cons r rs =>
          cases rs with
          | nil => simp [mergeAllRuns]
          | cons r2 rs' =>
              simp only [mergeAllRuns]
              exact (ih (mergePairs (r :: r2 :: rs'))).trans
                (mergePairs_flatten_perm (r :: r2 :: rs'))

theorem flatten_map_singleton :
    ∀ (xs : List (Nat × Nat × Nat)), (xs.map (fun x => [x])).flatten = xs
  | [] => rfl
  | x :: xs => by simp [flatten_map_singleton xs]

theorem sortHalves_perm (xs : List (Nat × Nat × Nat)) :
    (sortHalves xs).Perm xs := by
  simpa [sortHalves, flatten_map_singleton] using
    mergeAllRuns_perm xs.length (xs.map (fun x => [x]))

/-- Check in one tail-recursive pass that two function-sorted `nf3` half lists
have strictly increasing function identifiers and matching `(fn, sub)` pairs. -/
def validSortedHalves (prevF : Option Nat) :
    List (Nat × Nat × Nat) → List (Nat × Nat × Nat) → Bool
  | [], [] => true
  | (f, a, _) :: rs, (f', a', _) :: fs =>
      if prevF.all (fun p => decide (p < f)) && decide (f = f') && decide (a = a') then
        validSortedHalves (some f) rs fs
      else
        false
  | _, _ => false

/-- Zip paired role and filler halves into `.nf3` clauses. -/
def zipSortedHalves :
    List (Nat × Nat × Nat) → List (Nat × Nat × Nat) →
      List (ELCompletion.Clause Nat Nat)
  | (_, a, r) :: rs, (_, _, b) :: fs => .nf3 a r b :: zipSortedHalves rs fs
  | _, _ => []

/-- Validate and pair `nf3` role and filler halves into `.nf3` clauses. -/
def buildNF3Clauses (roles fillers : List (Nat × Nat × Nat)) :
    Option (List (ELCompletion.Clause Nat Nat)) :=
  let sRoles := sortHalves roles
  let sFillers := sortHalves fillers
  if validSortedHalves none sRoles sFillers then
    some (zipSortedHalves sRoles sFillers)
  else
    none

theorem validSortedHalves_cons {prevF : Option Nat}
    {f a r f' a' b : Nat} {rs fs : List (Nat × Nat × Nat)}
    (h : validSortedHalves prevF ((f, a, r) :: rs) ((f', a', b) :: fs) = true) :
    prevF.all (fun p => decide (p < f)) = true ∧
      f = f' ∧ a = a' ∧
      validSortedHalves (some f) rs fs = true := by
  unfold validSortedHalves at h
  split at h
  · rename_i hcond
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
    rcases hcond with ⟨⟨hprev, hfeq⟩, haeq⟩
    exact ⟨hprev, hfeq, haeq, h⟩
  · contradiction

theorem validSortedHalves_fst_gt {prevF : Option Nat} {rs fs : List (Nat × Nat × Nat)}
    (hvalid : validSortedHalves prevF rs fs = true)
    {p : Nat} (hp : prevF = some p)
    {q : Nat} (hq : q ∈ rs.map Prod.fst) : p < q := by
  induction rs generalizing prevF fs p with
  | nil => simp at hq
  | cons rhead rs' ih =>
      cases fs with
      | nil =>
          rcases rhead with ⟨f, a, r⟩
          simp [validSortedHalves] at hvalid
      | cons fhead fs' =>
          rcases rhead with ⟨f, a, r⟩
          rcases fhead with ⟨f', a', b⟩
          obtain ⟨hprev, _, _, htail⟩ := validSortedHalves_cons hvalid
          subst hp
          simp only [Option.all, decide_eq_true_eq] at hprev
          rcases List.mem_cons.mp hq with rfl | hqTail
          · exact hprev
          · exact Nat.lt_trans hprev (ih htail rfl hqTail)

theorem validSortedHalves_roles_nodup {prevF : Option Nat} {rs fs : List (Nat × Nat × Nat)}
    (hvalid : validSortedHalves prevF rs fs = true) :
    (rs.map Prod.fst).Nodup := by
  induction rs generalizing prevF fs with
  | nil => simp
  | cons rhead rs' ih =>
      cases fs with
      | nil =>
          rcases rhead with ⟨f, a, r⟩
          simp [validSortedHalves] at hvalid
      | cons fhead fs' =>
          rcases rhead with ⟨f, a, r⟩
          rcases fhead with ⟨f', a', b⟩
          obtain ⟨_, _, _, htail⟩ := validSortedHalves_cons hvalid
          simp only [List.map_cons, List.nodup_cons]
          refine ⟨?_, ih htail⟩
          intro hmem
          exact Nat.lt_irrefl f (validSortedHalves_fst_gt htail rfl hmem)

theorem validSortedHalves_map_fst_eq {prevF : Option Nat} {rs fs : List (Nat × Nat × Nat)}
    (hvalid : validSortedHalves prevF rs fs = true) :
    fs.map Prod.fst = rs.map Prod.fst := by
  induction rs generalizing prevF fs with
  | nil =>
      cases fs with
      | nil => rfl
      | cons fhead fs' =>
          rcases fhead with ⟨f', a', b⟩
          simp [validSortedHalves] at hvalid
  | cons rhead rs' ih =>
      cases fs with
      | nil =>
          rcases rhead with ⟨f, a, r⟩
          simp [validSortedHalves] at hvalid
      | cons fhead fs' =>
          rcases rhead with ⟨f, a, r⟩
          rcases fhead with ⟨f', a', b⟩
          obtain ⟨_, rfl, _, htail⟩ := validSortedHalves_cons hvalid
          simp [ih htail]

theorem validSortedHalves_fillers_nodup {prevF : Option Nat} {rs fs : List (Nat × Nat × Nat)}
    (hvalid : validSortedHalves prevF rs fs = true) :
    (fs.map Prod.fst).Nodup := by
  rw [validSortedHalves_map_fst_eq hvalid]
  exact validSortedHalves_roles_nodup hvalid

theorem validSortedHalves_role_mem {prevF : Option Nat} {rs fs : List (Nat × Nat × Nat)}
    (hvalid : validSortedHalves prevF rs fs = true)
    {f a r : Nat} (hmem : (f, a, r) ∈ rs) :
    ∃ b, (f, a, b) ∈ fs ∧ .nf3 a r b ∈ zipSortedHalves rs fs := by
  induction rs generalizing prevF fs with
  | nil => contradiction
  | cons rhead rs' ih =>
      cases fs with
      | nil =>
          rcases rhead with ⟨f₁, a₁, r₁⟩
          simp [validSortedHalves] at hvalid
      | cons fhead fs' =>
          rcases rhead with ⟨f₁, a₁, r₁⟩
          rcases fhead with ⟨f₂, a₂, b₂⟩
          obtain ⟨_, rfl, rfl, htail⟩ := validSortedHalves_cons hvalid
          rcases List.mem_cons.mp hmem with heq | htailMem
          · simp only [Prod.mk.injEq] at heq
            rcases heq with ⟨rfl, rfl, rfl⟩
            exact ⟨b₂, List.Mem.head _, List.Mem.head _⟩
          · obtain ⟨b, hbfs, hbzip⟩ := ih htail htailMem
            exact ⟨b, List.Mem.tail _ hbfs, List.Mem.tail _ hbzip⟩

theorem validSortedHalves_filler_mem {prevF : Option Nat} {rs fs : List (Nat × Nat × Nat)}
    (hvalid : validSortedHalves prevF rs fs = true)
    {f a b : Nat} (hmem : (f, a, b) ∈ fs) :
    ∃ r, (f, a, r) ∈ rs ∧ .nf3 a r b ∈ zipSortedHalves rs fs := by
  induction rs generalizing prevF fs with
  | nil =>
      cases fs with
      | nil => contradiction
      | cons fhead fs' =>
          rcases fhead with ⟨f₂, a₂, b₂⟩
          simp [validSortedHalves] at hvalid
  | cons rhead rs' ih =>
      cases fs with
      | nil =>
          rcases rhead with ⟨f₁, a₁, r₁⟩
          simp [validSortedHalves] at hvalid
      | cons fhead fs' =>
          rcases rhead with ⟨f₁, a₁, r₁⟩
          rcases fhead with ⟨f₂, a₂, b₂⟩
          obtain ⟨_, rfl, rfl, htail⟩ := validSortedHalves_cons hvalid
          rcases List.mem_cons.mp hmem with heq | htailMem
          · simp only [Prod.mk.injEq] at heq
            rcases heq with ⟨rfl, rfl, rfl⟩
            exact ⟨r₁, List.Mem.head _, List.Mem.head _⟩
          · obtain ⟨r, hrrs, hrzip⟩ := ih htail htailMem
            exact ⟨r, List.Mem.tail _ hrrs, List.Mem.tail _ hrzip⟩

theorem validSortedHalves_clause_mem {prevF : Option Nat} {rs fs : List (Nat × Nat × Nat)}
    (hvalid : validSortedHalves prevF rs fs = true)
    {cl : ELCompletion.Clause Nat Nat} (hcl : cl ∈ zipSortedHalves rs fs) :
    ∃ f a r b, cl = .nf3 a r b ∧ (f, a, r) ∈ rs ∧ (f, a, b) ∈ fs := by
  induction rs generalizing prevF fs with
  | nil => simp [zipSortedHalves] at hcl
  | cons rhead rs' ih =>
      cases fs with
      | nil =>
          rcases rhead with ⟨f₁, a₁, r₁⟩
          simp [zipSortedHalves] at hcl
      | cons fhead fs' =>
          rcases rhead with ⟨f₁, a₁, r₁⟩
          rcases fhead with ⟨f₂, a₂, b₂⟩
          obtain ⟨_, rfl, rfl, htail⟩ := validSortedHalves_cons hvalid
          rcases List.mem_cons.mp hcl with rfl | htailCl
          · exact ⟨f₁, a₁, r₁, b₂, rfl, List.Mem.head _, List.Mem.head _⟩
          · obtain ⟨f, a, r, b, rfl, hrrs, hffs⟩ := ih htail htailCl
            exact ⟨f, a, r, b, rfl, List.Mem.tail _ hrrs, List.Mem.tail _ hffs⟩

theorem buildNF3Clauses_role_mem {roles fillers : List (Nat × Nat × Nat)}
    {nf3Clauses : List (ELCompletion.Clause Nat Nat)}
    (hbuild : buildNF3Clauses roles fillers = some nf3Clauses)
    {f a r : Nat} (hmem : (f, a, r) ∈ roles) :
    lookupHalf f roles = some (a, r) ∧
      ∃ b, lookupHalf f fillers = some (a, b) ∧ .nf3 a r b ∈ nf3Clauses := by
  dsimp only [buildNF3Clauses] at hbuild
  split at hbuild
  · rename_i hvalid
    simp only [Option.some.injEq] at hbuild
    subst hbuild
    have hpermR := sortHalves_perm roles
    have hpermF := sortHalves_perm fillers
    have hroleNodup : (roles.map Prod.fst).Nodup :=
      (hpermR.map Prod.fst).nodup_iff.mp (validSortedHalves_roles_nodup hvalid)
    have hfillerNodup : (fillers.map Prod.fst).Nodup :=
      (hpermF.map Prod.fst).nodup_iff.mp (validSortedHalves_fillers_nodup hvalid)
    have hmemSR : (f, a, r) ∈ sortHalves roles := hpermR.mem_iff.mpr hmem
    obtain ⟨b, hmemSF, hmemZip⟩ := validSortedHalves_role_mem hvalid hmemSR
    have hmemF : (f, a, b) ∈ fillers := hpermF.mem_iff.mp hmemSF
    exact ⟨mem_lookupHalf_of_nodup hroleNodup hmem,
      b, mem_lookupHalf_of_nodup hfillerNodup hmemF, hmemZip⟩
  · simp at hbuild

theorem buildNF3Clauses_filler_mem {roles fillers : List (Nat × Nat × Nat)}
    {nf3Clauses : List (ELCompletion.Clause Nat Nat)}
    (hbuild : buildNF3Clauses roles fillers = some nf3Clauses)
    {f a b : Nat} (hmem : (f, a, b) ∈ fillers) :
    lookupHalf f fillers = some (a, b) ∧
      ∃ r, lookupHalf f roles = some (a, r) ∧ .nf3 a r b ∈ nf3Clauses := by
  dsimp only [buildNF3Clauses] at hbuild
  split at hbuild
  · rename_i hvalid
    simp only [Option.some.injEq] at hbuild
    subst hbuild
    have hpermR := sortHalves_perm roles
    have hpermF := sortHalves_perm fillers
    have hroleNodup : (roles.map Prod.fst).Nodup :=
      (hpermR.map Prod.fst).nodup_iff.mp (validSortedHalves_roles_nodup hvalid)
    have hfillerNodup : (fillers.map Prod.fst).Nodup :=
      (hpermF.map Prod.fst).nodup_iff.mp (validSortedHalves_fillers_nodup hvalid)
    have hmemSF : (f, a, b) ∈ sortHalves fillers := hpermF.mem_iff.mpr hmem
    obtain ⟨r, hmemSR, hmemZip⟩ := validSortedHalves_filler_mem hvalid hmemSF
    have hmemR : (f, a, r) ∈ roles := hpermR.mem_iff.mp hmemSR
    exact ⟨mem_lookupHalf_of_nodup hfillerNodup hmem,
      r, mem_lookupHalf_of_nodup hroleNodup hmemR, hmemZip⟩
  · simp at hbuild

theorem buildNF3Clauses_clause_mem {roles fillers : List (Nat × Nat × Nat)}
    {nf3Clauses : List (ELCompletion.Clause Nat Nat)}
    (hbuild : buildNF3Clauses roles fillers = some nf3Clauses)
    {cl : ELCompletion.Clause Nat Nat} (hcl : cl ∈ nf3Clauses) :
    ∃ f a r b, cl = .nf3 a r b ∧ (f, a, r) ∈ roles ∧ (f, a, b) ∈ fillers := by
  dsimp only [buildNF3Clauses] at hbuild
  split at hbuild
  · rename_i hvalid
    simp only [Option.some.injEq] at hbuild
    subst hbuild
    have hpermR := sortHalves_perm roles
    have hpermF := sortHalves_perm fillers
    obtain ⟨f, a, r, b, rfl, hmemSR, hmemSF⟩ := validSortedHalves_clause_mem hvalid hcl
    exact ⟨f, a, r, b, rfl, hpermR.mem_iff.mp hmemSR, hpermF.mem_iff.mp hmemSF⟩
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
  let firstAux := freshBase named items + 2
  let roles := collectRoleHalves items
  let fillers := collectFillerHalves items
  match buildNF3Clauses roles fillers with
  | none => none
  | some nf3Clauses =>
      some {
        top := top
        bottom := bottom
        ontology := compileDirect top bottom false firstAux items ++ nf3Clauses
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
      let firstAux := freshBase named items + 2
      intro item hmem
      have hdirect : ∀ cl, directClauseOf (selectTop named items) (selectBottom named items) item = some cl →
          ELCompletion.satClause I cl := by
        intro cl hcl
        apply hI cl
        exact List.mem_append_left _ (mem_compileDirect_of_directClauseOf false firstAux hmem hcl)
      cases item with
      | topCand a =>
          have htopOr := topCand_compileDirect (top := selectTop named items)
            (bottom := selectBottom named items) (seenTop := false) (nextAux := firstAux) hmem (by
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
      | naryConj a1 a2 a3 rem d =>
          obtain ⟨aux, hsub⟩ := sub_compileDirect_of_naryConj
            (top := selectTop named items) (bottom := selectBottom named items)
            false firstAux hmem
          have hchain : ∀ cl ∈ compileConjChain a1 a2 (a3 :: rem) d aux,
              ELCompletion.satClause I cl :=
            fun cl hcl => hI cl (List.mem_append_left _ (hsub cl hcl))
          intro u h1 h2 h3 hall
          refine compileConjChain_derives I a1 a2 (a3 :: rem) d aux hchain u h1 h2 ?_
          intro c hc
          rcases List.mem_cons.mp hc with rfl | hmem
          · exact h3
          · exact hall c hmem
      | naryConjBottom a1 a2 a3 rem =>
          obtain ⟨aux, hsub⟩ := sub_compileDirect_of_naryConjBottom
            (top := selectTop named items) (bottom := selectBottom named items)
            false firstAux hmem
          have hchain : ∀ cl ∈ compileConjChain a1 a2 (a3 :: rem) (selectBottom named items) aux,
              ELCompletion.satClause I cl :=
            fun cl hcl => hI cl (List.mem_append_left _ (hsub cl hcl))
          intro u h1 h2 h3 hall
          refine I.bottom_false u
            (compileConjChain_derives I a1 a2 (a3 :: rem) (selectBottom named items) aux hchain u h1 h2 ?_)
          intro c hc
          rcases List.mem_cons.mp hc with rfl | hmem
          · exact h3
          · exact hall c hmem
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
      let I₀ : ELCompletion.Interp Domain Nat Nat (selectTop named items) (selectBottom named items) := {
        concept := M₂.conc
        role := M₂.rol
        top_true := htop₂
        bottom_false := hbot₂
      }
      let firstAux := freshBase named items + 2
      have htop_lt : selectTop named items < firstAux := by
        have hle := selectTop_le_freshBase named items
        omega
      have hbot_lt : selectBottom named items < firstAux := by
        have hle := selectBottom_le_freshBase_succ named items
        omega
      have hconcepts_lt : ∀ item ∈ items, ∀ c ∈ itemConcepts item, c < firstAux := by
        intro item hmem c hc
        have hlt : c < freshBase named items := lt_freshBase_of_mem_itemsConcepts
          (List.mem_flatMap.mpr ⟨item, hmem, hc⟩)
        omega
      obtain ⟨I, hrolI, hpresI, hdirectI⟩ :=
        compileDirect_models M₂ I₀ false firstAux htop_lt hbot_lt hconcepts_lt
          (fun _ _ _ _ => rfl) rfl hitems₂
      refine ⟨I, ?_, ?_⟩
      · intro c hc
        have hlt_named : c < firstAux := by
          have hlt : c < freshBase named items := lt_freshBase_of_mem_named hc
          omega
        exact (hpresI c hlt_named).trans ((hnamed₂ c hc).trans (hnamed₁ c hc))
      · intro cl hcl
        rcases List.mem_append.mp hcl with hdirect | hnf3
        · exact hdirectI cl hdirect
        · obtain ⟨f, a, r, b, rfl, hroleMem, hfillerMem⟩ :=
            buildNF3Clauses_clause_mem hbuild hnf3
          have hroleItem : .nf3Role a r f ∈ items := mem_collectRoleHalves.mp hroleMem
          have hfillerItem : .nf3Filler a b f ∈ items := mem_collectFillerHalves.mp hfillerMem
          have hroleSat : satParsedItem M₂ (.nf3Role a r f) :=
            hitems₂ (.nf3Role a r f) hroleItem
          have hfillerSat : satParsedItem M₂ (.nf3Filler a b f) :=
            hitems₂ (.nf3Filler a b f) hfillerItem
          have ha_lt : a < firstAux := hconcepts_lt (.nf3Role a r f) hroleItem a (by simp [itemConcepts])
          have hb_lt : b < firstAux := hconcepts_lt (.nf3Filler a b f) hfillerItem b (by simp [itemConcepts])
          have ha_eq : I.concept a = M₂.conc a := hpresI a ha_lt
          have hb_eq : I.concept b = M₂.conc b := hpresI b hb_lt
          intro u hu
          rw [ha_eq] at hu
          refine ⟨M₂.fn f u, ?_, ?_⟩
          · rw [hrolI]
            exact hroleSat u hu
          · rw [hb_eq]
            exact hfillerSat u hu

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
