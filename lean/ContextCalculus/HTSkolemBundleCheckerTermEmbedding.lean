import ContextCalculus.HTSkolemPairCheckerTermEmbedding
import ContextCalculus.HypertableauSkolemBundleListProjection

/-!
# Multi-filler Skolem bundles in the common proper-term source

One bundle has one role-witness clause and zero or more filler clauses sharing
the same unary function.  Keeping the role clause separate is essential when
the filler list is empty.
-/

namespace ContextCalculus.HTSkolemBundleCheckerTermEmbedding

open ContextCalculus
open ContextCalculus.Hypertableau
open ContextCalculus.CheckerTerm
open ContextCalculus.HTCheckerTermEmbedding
open ContextCalculus.HTSkolemPairCheckerTermEmbedding

def roleTerm (bundle : BundleSpec Nat Nat Nat Nat) : FTerm :=
  .app bundle.function (encodeVariable bundle.source)

def roleLiteral (bundle : BundleSpec Nat Nat Nat Nat) : FLit :=
  .P (.role bundle.role (encodeVariable bundle.source) (roleTerm bundle))

def roleClause (bundle : BundleSpec Nat Nat Nat Nat) : FCL where
  body := bundle.body.filterMap encodePositive
  head := roleLiteral bundle :: bundle.body.filterMap encodeNegative

def fillerPair (bundle : BundleSpec Nat Nat Nat Nat) (filler : Hypertableau.Lit Nat) :
    SkolemPairSpec Nat Nat Nat Nat where
  body := bundle.body
  source := bundle.source
  function := bundle.function
  role := bundle.role
  filler

def fillerClause (bundle : BundleSpec Nat Nat Nat Nat)
    (filler : Hypertableau.Lit Nat) : FCL :=
  HTSkolemPairCheckerTermEmbedding.fillerClause (fillerPair bundle filler)

def encodeBundle (bundle : BundleSpec Nat Nat Nat Nat) : List FCL :=
  roleClause bundle :: bundle.fillers.map (fillerClause bundle)

def Direct (bundle : BundleSpec Nat Nat Nat Nat) : Prop :=
  ∀ atom ∈ bundle.body, directAtom atom = true

theorem valid_roleClause_iff (model : TModel Domain)
    (bundle : BundleSpec Nat Nat Nat Nat) (hdirect : Direct bundle) :
    valid model (roleClause bundle) ↔
      ∀ environment, HoldsBody (htInterp model) environment bundle.body →
        (htInterp model).role bundle.role (environment bundle.source)
          ((skolemInterp model).app bundle.function (environment bundle.source)) := by
  constructor
  · intro hvalid environment hbody
    let assignment : Int → Domain := fun index =>
      match index with
      | .ofNat index => environment index
      | .negSucc _ => environment 0
    have hparts := (holdsBody_iff model assignment bundle.body hdirect).1
      (by simpa [assignment] using hbody)
    rcases hvalid assignment hparts.1 with ⟨literal, hliteral, heval⟩
    simp only [roleClause, List.mem_cons] at hliteral
    rcases hliteral with rfl | hliteral
    · simpa [roleLiteral, roleTerm, skolemInterp, assignment,
        TModel.evalL, TModel.evalT, htInterp] using heval
    · exact False.elim (hparts.2 literal hliteral heval)
  · intro hrole assignment hpositive
    classical
    by_cases hnegative :
        ∀ literal ∈ bundle.body.filterMap encodeNegative, ¬model.evalL assignment literal
    · have hbody := (holdsBody_iff model assignment bundle.body hdirect).2
        ⟨hpositive, hnegative⟩
      refine ⟨roleLiteral bundle, by simp [roleClause], ?_⟩
      simpa [roleLiteral, roleTerm, skolemInterp, TModel.evalL, TModel.evalT,
        htInterp] using
        hrole (fun index => assignment (Int.ofNat index)) hbody
    · push Not at hnegative
      rcases hnegative with ⟨literal, hliteral, heval⟩
      exact ⟨literal, by simp [roleClause, hliteral], heval⟩

theorem valid_fillerClause_iff (model : TModel Domain)
    (bundle : BundleSpec Nat Nat Nat Nat) (hdirect : Direct bundle)
    (filler : Hypertableau.Lit Nat) :
    valid model (fillerClause bundle filler) ↔
      ∀ environment, HoldsBody (htInterp model) environment bundle.body →
        (htInterp model).satLit filler
          ((skolemInterp model).app bundle.function (environment bundle.source)) := by
  exact HTSkolemPairCheckerTermEmbedding.valid_fillerClause_iff model
    (fillerPair bundle filler) hdirect

theorem valid_bundle_iff (model : TModel Domain)
    (bundle : BundleSpec Nat Nat Nat Nat) (hdirect : Direct bundle) :
    (∀ clause ∈ encodeBundle bundle, valid model clause) ↔
      ModelsSkolemBundle (htInterp model) (skolemInterp model)
        bundle.body bundle.source bundle.function bundle.role bundle.fillers := by
  constructor
  · intro hvalid
    constructor
    · exact (valid_roleClause_iff model bundle hdirect).1
        (hvalid (roleClause bundle) (by simp [encodeBundle]))
    · intro filler hfiller
      exact (valid_fillerClause_iff model bundle hdirect filler).1
        (hvalid (fillerClause bundle filler) (by
          exact List.mem_cons_of_mem _
            (List.mem_map.mpr ⟨filler, hfiller, rfl⟩)))
  · rintro ⟨hrole, hfillers⟩ clause hclause
    simp only [encodeBundle, List.mem_cons, List.mem_map] at hclause
    rcases hclause with rfl | ⟨filler, hfiller, rfl⟩
    · exact (valid_roleClause_iff model bundle hdirect).2 hrole
    · exact (valid_fillerClause_iff model bundle hdirect filler).2
        (hfillers filler hfiller)

def ModelsBundleList (interpretation : Interp Domain Nat Nat)
    (functions : SkolemInterp Domain Nat)
    (bundles : List (BundleSpec Nat Nat Nat Nat)) : Prop :=
  ∀ bundle ∈ bundles, ModelsSkolemBundle interpretation functions bundle.body
    bundle.source bundle.function bundle.role bundle.fillers

def encodeBundles (direct : List (Hypertableau.Clause Nat Nat Nat))
    (bundles : List (BundleSpec Nat Nat Nat Nat)) : List FCL :=
  direct.map encodeClause ++ bundles.flatMap encodeBundle

def DirectBundles (direct : List (Hypertableau.Clause Nat Nat Nat))
    (bundles : List (BundleSpec Nat Nat Nat Nat)) : Prop :=
  DirectOntology direct ∧ ∀ bundle ∈ bundles, Direct bundle

theorem models_bundles_encode_iff (model : TModel Domain)
    (direct : List (Hypertableau.Clause Nat Nat Nat))
    (bundles : List (BundleSpec Nat Nat Nat Nat))
    (hdirect : DirectBundles direct bundles) :
    (∀ clause ∈ encodeBundles direct bundles, valid model clause) ↔
      (htInterp model).models direct ∧
        ModelsBundleList (htInterp model) (skolemInterp model) bundles := by
  constructor
  · intro hmodels
    constructor
    · intro clause hclause
      exact (modelsClause_encode_iff model clause (hdirect.1 clause hclause)).1
        (hmodels (encodeClause clause) (List.mem_append.mpr (Or.inl
          (List.mem_map.mpr ⟨clause, hclause, rfl⟩))))
    · intro bundle hbundle
      apply (valid_bundle_iff model bundle (hdirect.2 bundle hbundle)).1
      intro clause hclause
      exact hmodels clause (List.mem_append.mpr (Or.inr
        (List.mem_flatMap.mpr ⟨bundle, hbundle, hclause⟩)))
  · rintro ⟨hdirectModels, hbundles⟩ clause hclause
    simp only [encodeBundles, List.mem_append] at hclause
    rcases hclause with hclause | hclause
    · rcases List.mem_map.mp hclause with ⟨source, hsource, rfl⟩
      exact (modelsClause_encode_iff model source (hdirect.1 source hsource)).2
        (hdirectModels source hsource)
    · rcases List.mem_flatMap.mp hclause with ⟨bundle, hbundle, hclause⟩
      exact (valid_bundle_iff model bundle (hdirect.2 bundle hbundle)).2
        (hbundles bundle hbundle) clause hclause

def CommonEntailsSub (direct : List (Hypertableau.Clause Nat Nat Nat))
    (bundles : List (BundleSpec Nat Nat Nat Nat)) (sub sup : Nat) : Prop :=
  ∀ (Domain : Type) (model : TModel Domain),
    (∀ clause ∈ encodeBundles direct bundles, valid model clause) →
      ∀ value, model.conc sub value → model.conc sup value

def SourceEntailsSub (direct : List (Hypertableau.Clause Nat Nat Nat))
    (bundles : List (BundleSpec Nat Nat Nat Nat)) (sub sup : Nat) : Prop :=
  ∀ (Domain : Type) (interpretation : Interp Domain Nat Nat)
    (functions : SkolemInterp Domain Nat),
    interpretation.models direct → ModelsBundleList interpretation functions bundles →
      ∀ value, interpretation.concept sub value → interpretation.concept sup value

theorem entailsSub_bundles_encode_iff
    (direct : List (Hypertableau.Clause Nat Nat Nat))
    (bundles : List (BundleSpec Nat Nat Nat Nat))
    (hdirect : DirectBundles direct bundles) (sub sup : Nat) :
    CommonEntailsSub direct bundles sub sup ↔ SourceEntailsSub direct bundles sub sup := by
  constructor
  · intro hcommon Domain interpretation functions hdirectModels hbundles value hsub
    letI : Nonempty Domain := ⟨value⟩
    let model := mixedCheckerModel interpretation functions
    exact hcommon Domain model
      ((models_bundles_encode_iff model direct bundles hdirect).2 (by
        simpa [model, htInterp, mixedCheckerModel, skolemInterp] using
          And.intro hdirectModels hbundles)) value hsub
  · intro hsource Domain model hmodels value hsub
    have hbundleModels :=
      (models_bundles_encode_iff model direct bundles hdirect).1 hmodels
    exact hsource Domain (htInterp model) (skolemInterp model)
      hbundleModels.1 hbundleModels.2 value hsub

#print axioms valid_bundle_iff
#print axioms models_bundles_encode_iff
#print axioms entailsSub_bundles_encode_iff

end ContextCalculus.HTSkolemBundleCheckerTermEmbedding
