import ContextCalculus.CBALCEncoding
import ContextCalculus.HypertableauRegularCertificate

/-!
# Regular HT countermodels for the ALC-shaped CB source

This is the semantic bridge between two already certified layers.  An ALC
ontology is translated to the exact guarded clauses consumed by the regular
hypertableau checker.  A checked regular HT model therefore induces an ALC
model; `CBALCEncoding.models_extend` then equips the same (possibly infinite)
domain with the indexed Skolem functions used by the CB source clauses.

The eventual wire must require syntactic identity with both translations.  No
unsupported CB clause is approximated or discarded.
-/

namespace ContextCalculus.CBRegularALCCountermodel

open ContextCalculus CheckerTerm
open ContextCalculus.Ctx
open ContextCalculus.CBALCEncoding
open ContextCalculus.Hypertableau

def htAtom (concept : Fin conceptCount) (node : Fin variableCount) :
    Hypertableau.Atom (Fin variableCount) (Fin conceptCount) (Fin roleCount) :=
  .concept (.pos concept) node

/-- Exact guarded HT form of one normalized ALC clause.  The caller supplies
two distinct variables because the binary clauses quantify source and target
independently. -/
def htClause (source target : Fin variableCount) :
    Ctx.Clause (Fin conceptCount) (Fin roleCount) →
      Hypertableau.Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)
  | .gci body head =>
      ⟨body.map (htAtom · source), head.map (htAtom · source)⟩
  | .exRight trigger role filler =>
      ⟨[htAtom trigger source], [.exists_ role (.pos filler) source]⟩
  | .exLeft role filler conclusion =>
      ⟨[.role role source target, htAtom filler target],
        [htAtom conclusion source]⟩
  | .allRight trigger role filler =>
      ⟨[htAtom trigger source, .role role source target],
        [htAtom filler target]⟩

def htOntology (source target : Fin variableCount)
    (ontology : Ctx.Ontology (Fin conceptCount) (Fin roleCount)) :=
  ontology.map (htClause source target)

def restrictHT (interpretation : Hypertableau.Interp D
    (Fin conceptCount) (Fin roleCount)) :
    Ctx.Interp D (Fin conceptCount) (Fin roleCount) where
  c := interpretation.concept
  r := interpretation.role

theorem models_ctx_of_models_ht
    (interpretation : Hypertableau.Interp D
      (Fin conceptCount) (Fin roleCount))
    (source target : Fin variableCount) (hne : source ≠ target)
    (ontology : Ctx.Ontology (Fin conceptCount) (Fin roleCount))
    (hmodels : interpretation.models (htOntology source target ontology)) :
    Ctx.models (restrictHT interpretation) ontology := by
  intro clause hclause
  have htranslated : interpretation.modelsClause (htClause source target clause) :=
    hmodels _ (List.mem_map.mpr ⟨clause, hclause, rfl⟩)
  cases clause with
  | gci body head =>
      intro element hbody
      let assignment : Fin variableCount → D := fun _ => element
      rcases htranslated assignment (by
        intro atom hatom
        simp only [htClause, List.mem_map] at hatom
        rcases hatom with ⟨concept, hconcept, rfl⟩
        simpa [htAtom, Hypertableau.Interp.satAtom,
          Hypertableau.Interp.satLit] using hbody concept hconcept) with
        ⟨atom, hatom, hsat⟩
      simp only [htClause, List.mem_map] at hatom
      rcases hatom with ⟨concept, hconcept, rfl⟩
      exact ⟨concept, hconcept, by
        simpa [restrictHT, htAtom, Hypertableau.Interp.satAtom,
          Hypertableau.Interp.satLit] using hsat⟩
  | exRight trigger role filler =>
      intro element htrigger
      let assignment : Fin variableCount → D := fun _ => element
      rcases htranslated assignment (by
        intro atom hatom
        simp only [htClause, List.mem_singleton] at hatom
        subst atom
        simpa [restrictHT, htAtom, Hypertableau.Interp.satAtom,
          Hypertableau.Interp.satLit] using htrigger) with
        ⟨atom, hatom, hsat⟩
      simp only [htClause, List.mem_singleton] at hatom
      subst atom
      simpa [restrictHT, Hypertableau.Interp.satAtom,
        Hypertableau.Interp.satLit] using hsat
  | exLeft role filler conclusion =>
      intro element hexists
      rcases hexists with ⟨witness, hedge, hfiller⟩
      let assignment : Fin variableCount → D := fun node =>
        if node = target then witness else element
      have hsource : assignment source = element := by simp [assignment, hne]
      have htarget : assignment target = witness := by simp [assignment]
      rcases htranslated assignment (by
        intro atom hatom
        simp only [htClause, List.mem_cons, List.not_mem_nil, or_false] at hatom
        rcases hatom with rfl | rfl
        · simpa [Hypertableau.Interp.satAtom, hsource, htarget, restrictHT] using hedge
        · simpa [htAtom, Hypertableau.Interp.satAtom,
            Hypertableau.Interp.satLit, htarget, restrictHT] using hfiller) with
        ⟨atom, hatom, hsat⟩
      simp only [htClause, List.mem_singleton] at hatom
      subst atom
      simpa [htAtom, Hypertableau.Interp.satAtom,
        Hypertableau.Interp.satLit, hsource, restrictHT] using hsat
  | allRight trigger role filler =>
      intro element htrigger witness hedge
      let assignment : Fin variableCount → D := fun node =>
        if node = target then witness else element
      have hsource : assignment source = element := by simp [assignment, hne]
      have htarget : assignment target = witness := by simp [assignment]
      rcases htranslated assignment (by
        intro atom hatom
        simp only [htClause, List.mem_cons, List.not_mem_nil, or_false] at hatom
        rcases hatom with rfl | rfl
        · simpa [htAtom, Hypertableau.Interp.satAtom,
            Hypertableau.Interp.satLit, hsource, restrictHT] using htrigger
        · simpa [Hypertableau.Interp.satAtom, hsource, htarget, restrictHT] using hedge) with
        ⟨atom, hatom, hsat⟩
      simp only [htClause, List.mem_singleton] at hatom
      subst atom
      simpa [htAtom, Hypertableau.Interp.satAtom,
        Hypertableau.Interp.satLit, htarget, restrictHT] using hsat

/-- A checked regular HT certificate whose ontology is exactly the ALC
translation yields a CB nested-term countermodel for the same query. -/
theorem checked_regular_countermodel
    [NeZero nodeCount]
    (certificate : FiniteRegularCertificate
      nodeCount conceptCount roleCount variableCount)
    (source target : Fin variableCount) (hne : source ≠ target)
    (ontology : Ctx.Ontology (Fin conceptCount) (Fin roleCount))
    (sub sup : Fin conceptCount)
    (hontology : certificate.ontology = htOntology source target ontology)
    (hsub : certificate.state.label 0 (.pos sub))
    (hnotSup : certificate.state.label 0 (.negated sup))
    (hcheck : certificate.check = true) :
    ∃ (D : Type) (model : TModel D) (element : D),
      (∀ clause ∈ CBALCEncoding.encode ontology, valid model clause) ∧
      model.conc sub.val element ∧ ¬model.conc sup.val element := by
  let htModel := certificate.state.regularUnravelling certificate.redirect
    (fun _ _ _ _ => True) 0 certificate.rules
  let element : UnravellingDomain certificate.state certificate.redirect
      (fun _ _ _ _ => True) 0 := ⟨0, .root⟩
  have hhtModels : htModel.models (htOntology source target ontology) := by
    rw [← hontology]
    exact certificate.check_models hcheck
  have hctxModels : Ctx.models (restrictHT htModel) ontology :=
    models_ctx_of_models_ht htModel source target hne ontology hhtModels
  let model := CBALCEncoding.extendModel ontology (restrictHT htModel)
    hctxModels element
  refine ⟨_, model, element,
    CBALCEncoding.models_extend ontology (restrictHT htModel) hctxModels element,
    ?_, ?_⟩
  · simpa [model, restrictHT, CBALCEncoding.extendModel_conc, htModel,
      Hypertableau.Interp.satLit, Lit.pos] using
      certificate.state.regularUnravelling_sat_label certificate.redirect
        (fun _ _ _ _ => True) 0 certificate.rules
        (certificate.check_sound hcheck).2.2.2.1 element (.pos sub) hsub
  · simpa [model, restrictHT, CBALCEncoding.extendModel_conc, htModel,
      Hypertableau.Interp.satLit, Lit.negated] using
      certificate.state.regularUnravelling_sat_label certificate.redirect
        (fun _ _ _ _ => True) 0 certificate.rules
        (certificate.check_sound hcheck).2.2.2.1 element (.negated sup) hnotSup

#print axioms models_ctx_of_models_ht
#print axioms checked_regular_countermodel

end ContextCalculus.CBRegularALCCountermodel
