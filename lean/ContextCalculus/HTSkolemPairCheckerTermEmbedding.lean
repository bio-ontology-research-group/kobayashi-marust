import ContextCalculus.HTCheckerTermEmbedding
import ContextCalculus.HypertableauSkolemProjection

/-!
# Exact HT Skolem-pair embedding into the common proper-term source

The frontend represents `body -> exists r.C` by two clauses sharing the unary
term `f(source)`.  HT replaces those clauses by one existential atom.  This
module reconstructs the two proper-term clauses and proves that their validity
is exactly `ModelsSkolemPair`, including signed body and filler concepts.
-/

namespace ContextCalculus.HTSkolemPairCheckerTermEmbedding

open ContextCalculus
open ContextCalculus.Hypertableau
open ContextCalculus.CheckerTerm
open ContextCalculus.HTCheckerTermEmbedding

def pairTerm (pair : SkolemPairSpec Nat Nat Nat Nat) : FTerm :=
  .app pair.function (encodeVariable pair.source)

def pairRoleLiteral (pair : SkolemPairSpec Nat Nat Nat Nat) : FLit :=
  .P (.role pair.role (encodeVariable pair.source) (pairTerm pair))

def pairFillerLiteral (pair : SkolemPairSpec Nat Nat Nat Nat) : FLit :=
  .P (.concept pair.filler.concept (pairTerm pair))

def roleClause (pair : SkolemPairSpec Nat Nat Nat Nat) : FCL where
  body := pair.body.filterMap encodePositive
  head := pairRoleLiteral pair :: pair.body.filterMap encodeNegative

def fillerClause (pair : SkolemPairSpec Nat Nat Nat Nat) : FCL :=
  if pair.filler.neg then
    { body := pair.body.filterMap encodePositive ++ [pairFillerLiteral pair]
      head := pair.body.filterMap encodeNegative }
  else
    { body := pair.body.filterMap encodePositive
      head := pairFillerLiteral pair :: pair.body.filterMap encodeNegative }

def Direct (pair : SkolemPairSpec Nat Nat Nat Nat) : Prop :=
  ∀ atom ∈ pair.body, directAtom atom = true

def skolemInterp (model : TModel Domain) : SkolemInterp Domain Nat where
  app := model.fn

private theorem filterMap_mem {α β : Type} {f : α → Option β}
    {items : List α} {value : β} :
    value ∈ items.filterMap f ↔ ∃ item ∈ items, f item = some value := by
  induction items with
  | nil => simp
  | cons item items ih =>
      cases h : f item <;> simp [List.filterMap, h, ih, eq_comm]

theorem holdsBody_iff (model : TModel Domain) (assignment : Int → Domain)
    (body : List (Atom Nat Nat Nat))
    (hdirect : ∀ atom ∈ body, directAtom atom = true) :
    HoldsBody (htInterp model) (fun index => assignment (Int.ofNat index)) body ↔
      (∀ literal ∈ body.filterMap encodePositive, model.evalL assignment literal) ∧
      (∀ literal ∈ body.filterMap encodeNegative, ¬model.evalL assignment literal) := by
  constructor
  · intro hbody
    constructor
    · intro literal hliteral
      rcases filterMap_mem.mp hliteral with ⟨atom, hatom, hencode⟩
      exact (eval_positive_iff model assignment atom literal hencode).2
        (hbody atom hatom)
    · intro literal hliteral
      rcases filterMap_mem.mp hliteral with ⟨atom, hatom, hencode⟩
      exact fun heval =>
        ((eval_negative_iff model assignment atom literal hencode).1 heval)
          (hbody atom hatom)
  · rintro ⟨hpositive, hnegative⟩ atom hatom
    rcases directAtom_no_exists atom (hdirect atom hatom) with
      ⟨literal, hencode | hencode⟩
    · exact (eval_positive_iff model assignment atom literal hencode).1
        (hpositive literal (filterMap_mem.mpr ⟨atom, hatom, hencode⟩))
    · classical
      by_contra hsat
      exact hnegative literal (filterMap_mem.mpr ⟨atom, hatom, hencode⟩)
        ((eval_negative_iff model assignment atom literal hencode).2 hsat)

@[simp] theorem eval_pairRoleLiteral (model : TModel Domain)
    (assignment : Int → Domain) (pair : SkolemPairSpec Nat Nat Nat Nat) :
    model.evalL assignment (pairRoleLiteral pair) ↔
      (htInterp model).role pair.role (assignment (Int.ofNat pair.source))
        ((skolemInterp model).app pair.function
          (assignment (Int.ofNat pair.source))) := by
  rfl

@[simp] theorem eval_pairFillerLiteral (model : TModel Domain)
    (assignment : Int → Domain) (pair : SkolemPairSpec Nat Nat Nat Nat) :
    model.evalL assignment (pairFillerLiteral pair) ↔
      (htInterp model).concept pair.filler.concept
        ((skolemInterp model).app pair.function
          (assignment (Int.ofNat pair.source))) := by
  rfl

theorem valid_roleClause_iff (model : TModel Domain)
    (pair : SkolemPairSpec Nat Nat Nat Nat) (hdirect : Direct pair) :
    valid model (roleClause pair) ↔
      ∀ environment, HoldsBody (htInterp model) environment pair.body →
        (htInterp model).role pair.role (environment pair.source)
          ((skolemInterp model).app pair.function (environment pair.source)) := by
  constructor
  · intro hvalid environment hbody
    let assignment : Int → Domain := fun index =>
      match index with
      | .ofNat index => environment index
      | .negSucc _ => environment 0
    have hparts := (holdsBody_iff model assignment pair.body hdirect).1
      (by simpa [assignment] using hbody)
    rcases hvalid assignment hparts.1 with ⟨literal, hliteral, heval⟩
    simp only [roleClause, List.mem_cons] at hliteral
    rcases hliteral with rfl | hliteral
    · simpa [assignment] using heval
    · exact False.elim (hparts.2 literal hliteral heval)
  · intro hpair assignment hpositive
    classical
    by_cases hnegative :
        ∀ literal ∈ pair.body.filterMap encodeNegative, ¬model.evalL assignment literal
    · have hbody := (holdsBody_iff model assignment pair.body hdirect).2
        ⟨hpositive, hnegative⟩
      refine ⟨pairRoleLiteral pair, by simp [roleClause], ?_⟩
      exact hpair (fun index => assignment (Int.ofNat index)) hbody
    · push Not at hnegative
      rcases hnegative with ⟨literal, hliteral, heval⟩
      exact ⟨literal, by simp [roleClause, hliteral], heval⟩

theorem valid_fillerClause_iff (model : TModel Domain)
    (pair : SkolemPairSpec Nat Nat Nat Nat) (hdirect : Direct pair) :
    valid model (fillerClause pair) ↔
      ∀ environment, HoldsBody (htInterp model) environment pair.body →
        (htInterp model).satLit pair.filler
          ((skolemInterp model).app pair.function (environment pair.source)) := by
  constructor
  · intro hvalid environment hbody
    let assignment : Int → Domain := fun index =>
      match index with
      | .ofNat index => environment index
      | .negSucc _ => environment 0
    have hparts := (holdsBody_iff model assignment pair.body hdirect).1
      (by simpa [assignment] using hbody)
    cases hneg : pair.filler.neg
    · have hencodedBody : ∀ literal ∈ (fillerClause pair).body,
          model.evalL assignment literal := by
        simpa [fillerClause, hneg] using hparts.1
      rcases hvalid assignment hencodedBody with ⟨literal, hliteral, heval⟩
      simp only [fillerClause, hneg, Bool.false_eq_true, ↓reduceIte,
        List.mem_cons] at hliteral
      rcases hliteral with rfl | hliteral
      · simpa [Interp.satLit, hneg, assignment] using heval
      · exact False.elim (hparts.2 literal hliteral heval)
    · have hfiller : ¬model.evalL assignment (pairFillerLiteral pair) := by
        intro hfiller
        have hencodedBody : ∀ literal ∈
            pair.body.filterMap encodePositive ++ [pairFillerLiteral pair],
            model.evalL assignment literal := by
          intro literal hliteral
          simp only [List.mem_append, List.mem_singleton] at hliteral
          rcases hliteral with hliteral | rfl
          · exact hparts.1 literal hliteral
          · exact hfiller
        rcases hvalid assignment (by simpa [fillerClause, hneg] using hencodedBody) with
          ⟨literal, hliteral, heval⟩
        simp only [fillerClause, hneg, ↓reduceIte] at hliteral
        exact hparts.2 literal hliteral heval
      simpa [Interp.satLit, hneg, assignment] using hfiller
  · intro hpair assignment hbody
    classical
    by_cases hnegative :
        ∀ literal ∈ pair.body.filterMap encodeNegative, ¬model.evalL assignment literal
    · have hholds := (holdsBody_iff model assignment pair.body hdirect).2
        ⟨fun literal hliteral => hbody literal (by
            cases hneg : pair.filler.neg
            · simp [fillerClause, hneg, hliteral]
            · simp [fillerClause, hneg, hliteral]), hnegative⟩
      have hfiller := hpair (fun index => assignment (Int.ofNat index)) hholds
      cases hneg : pair.filler.neg
      · refine ⟨pairFillerLiteral pair, ?_, ?_⟩
        · simp [fillerClause, hneg]
        · simpa [Interp.satLit, hneg] using hfiller
      · have hnotEval : ¬model.evalL assignment (pairFillerLiteral pair) := by
          simpa [Interp.satLit, hneg] using hfiller
        exact False.elim (hnotEval
          (hbody (pairFillerLiteral pair) (by simp [fillerClause, hneg])))
    · push Not at hnegative
      rcases hnegative with ⟨literal, hliteral, heval⟩
      cases hneg : pair.filler.neg
      · exact ⟨literal, by simp [fillerClause, hneg, hliteral], heval⟩
      · exact ⟨literal, by simp [fillerClause, hneg, hliteral], heval⟩

theorem valid_pair_iff (model : TModel Domain)
    (pair : SkolemPairSpec Nat Nat Nat Nat) (hdirect : Direct pair) :
    (valid model (roleClause pair) ∧ valid model (fillerClause pair)) ↔
      pair.models (htInterp model) (skolemInterp model) := by
  exact ⟨fun h => ⟨(valid_roleClause_iff model pair hdirect).1 h.1,
      (valid_fillerClause_iff model pair hdirect).1 h.2⟩,
    fun h => ⟨(valid_roleClause_iff model pair hdirect).2 h.1,
      (valid_fillerClause_iff model pair hdirect).2 h.2⟩⟩

def encodePair (pair : SkolemPairSpec Nat Nat Nat Nat) : List FCL :=
  [roleClause pair, fillerClause pair]

def encodeMixed (direct : List (Hypertableau.Clause Nat Nat Nat))
    (pairs : List (SkolemPairSpec Nat Nat Nat Nat)) : List FCL :=
  direct.map encodeClause ++ pairs.flatMap encodePair

def DirectMixed (direct : List (Hypertableau.Clause Nat Nat Nat))
    (pairs : List (SkolemPairSpec Nat Nat Nat Nat)) : Prop :=
  DirectOntology direct ∧ ∀ pair ∈ pairs, Direct pair

theorem models_mixed_encode_iff (model : TModel Domain)
    (direct : List (Hypertableau.Clause Nat Nat Nat))
    (pairs : List (SkolemPairSpec Nat Nat Nat Nat))
    (hdirect : DirectMixed direct pairs) :
    (∀ clause ∈ encodeMixed direct pairs, valid model clause) ↔
      (htInterp model).models direct ∧
        ModelsSkolemPairs (htInterp model) (skolemInterp model) pairs := by
  constructor
  · intro hmodels
    constructor
    · intro clause hclause
      exact (modelsClause_encode_iff model clause (hdirect.1 clause hclause)).1
        (hmodels (encodeClause clause) (by
          exact List.mem_append.mpr (Or.inl
            (List.mem_map.mpr ⟨clause, hclause, rfl⟩))))
    · intro pair hpair
      apply (valid_pair_iff model pair (hdirect.2 pair hpair)).1
      constructor
      · exact hmodels (roleClause pair) (by
          exact List.mem_append.mpr (Or.inr
            (List.mem_flatMap.mpr ⟨pair, hpair, by simp [encodePair]⟩)))
      · exact hmodels (fillerClause pair) (by
          exact List.mem_append.mpr (Or.inr
            (List.mem_flatMap.mpr ⟨pair, hpair, by simp [encodePair]⟩)))
  · rintro ⟨hdirectModels, hpairs⟩ clause hclause
    simp only [encodeMixed, List.mem_append] at hclause
    rcases hclause with hclause | hclause
    · rcases List.mem_map.mp hclause with ⟨source, hsource, rfl⟩
      exact (modelsClause_encode_iff model source (hdirect.1 source hsource)).2
        (hdirectModels source hsource)
    · rcases List.mem_flatMap.mp hclause with ⟨pair, hpair, hclause⟩
      have hvalid := (valid_pair_iff model pair (hdirect.2 pair hpair)).2
        (hpairs pair hpair)
      simp [encodePair] at hclause
      rcases hclause with rfl | rfl
      · exact hvalid.1
      · exact hvalid.2

noncomputable def mixedCheckerModel [Nonempty Domain]
    (interpretation : Interp Domain Nat Nat)
    (functions : SkolemInterp Domain Nat) : TModel Domain where
  conc := interpretation.concept
  rol := interpretation.role
  const := fun _ => Classical.choice inferInstance
  fn := functions.app

def CommonEntailsSub (direct : List (Hypertableau.Clause Nat Nat Nat))
    (pairs : List (SkolemPairSpec Nat Nat Nat Nat)) (sub sup : Nat) : Prop :=
  ∀ (Domain : Type) (model : TModel Domain),
    (∀ clause ∈ encodeMixed direct pairs, valid model clause) →
      ∀ value, model.conc sub value → model.conc sup value

def SourceEntailsSub (direct : List (Hypertableau.Clause Nat Nat Nat))
    (pairs : List (SkolemPairSpec Nat Nat Nat Nat)) (sub sup : Nat) : Prop :=
  ∀ (Domain : Type) (interpretation : Interp Domain Nat Nat)
    (functions : SkolemInterp Domain Nat),
    interpretation.models direct → ModelsSkolemPairs interpretation functions pairs →
      ∀ value, interpretation.concept sub value → interpretation.concept sup value

def CommonUnsatisfiableConcept
    (direct : List (Hypertableau.Clause Nat Nat Nat))
    (pairs : List (SkolemPairSpec Nat Nat Nat Nat)) (concept : Nat) : Prop :=
  ∀ (Domain : Type) (model : TModel Domain),
    (∀ clause ∈ encodeMixed direct pairs, valid model clause) →
      ∀ value, ¬model.conc concept value

def SourceUnsatisfiableConcept
    (direct : List (Hypertableau.Clause Nat Nat Nat))
    (pairs : List (SkolemPairSpec Nat Nat Nat Nat)) (concept : Nat) : Prop :=
  ∀ (Domain : Type) (interpretation : Interp Domain Nat Nat)
    (functions : SkolemInterp Domain Nat),
    interpretation.models direct → ModelsSkolemPairs interpretation functions pairs →
      ∀ value, ¬interpretation.concept concept value

theorem entailsSub_mixed_encode_iff
    (direct : List (Hypertableau.Clause Nat Nat Nat))
    (pairs : List (SkolemPairSpec Nat Nat Nat Nat))
    (hdirect : DirectMixed direct pairs) (sub sup : Nat) :
    CommonEntailsSub direct pairs sub sup ↔
      SourceEntailsSub direct pairs sub sup := by
  constructor
  · intro hcommon Domain interpretation functions hdirectModels hpairs value hsub
    letI : Nonempty Domain := ⟨value⟩
    let model := mixedCheckerModel interpretation functions
    exact hcommon Domain model
      ((models_mixed_encode_iff model direct pairs hdirect).2 (by
        simpa [model, htInterp, mixedCheckerModel, skolemInterp] using
          And.intro hdirectModels hpairs)) value hsub
  · intro hsource Domain model hmodels value hsub
    have hmixed := (models_mixed_encode_iff model direct pairs hdirect).1 hmodels
    exact hsource Domain (htInterp model) (skolemInterp model)
      hmixed.1 hmixed.2 value hsub

theorem unsatisfiableConcept_mixed_encode_iff
    (direct : List (Hypertableau.Clause Nat Nat Nat))
    (pairs : List (SkolemPairSpec Nat Nat Nat Nat))
    (hdirect : DirectMixed direct pairs) (concept : Nat) :
    CommonUnsatisfiableConcept direct pairs concept ↔
      SourceUnsatisfiableConcept direct pairs concept := by
  constructor
  · intro hcommon Domain interpretation functions hdirectModels hpairs value hconcept
    letI : Nonempty Domain := ⟨value⟩
    let model := mixedCheckerModel interpretation functions
    exact hcommon Domain model
      ((models_mixed_encode_iff model direct pairs hdirect).2 (by
        simpa [model, htInterp, mixedCheckerModel, skolemInterp] using
          And.intro hdirectModels hpairs)) value hconcept
  · intro hsource Domain model hmodels value hconcept
    have hmixed := (models_mixed_encode_iff model direct pairs hdirect).1 hmodels
    exact hsource Domain (htInterp model) (skolemInterp model)
      hmixed.1 hmixed.2 value hconcept

#print axioms valid_roleClause_iff
#print axioms valid_fillerClause_iff
#print axioms valid_pair_iff
#print axioms models_mixed_encode_iff
#print axioms entailsSub_mixed_encode_iff
#print axioms unsatisfiableConcept_mixed_encode_iff

end ContextCalculus.HTSkolemPairCheckerTermEmbedding
