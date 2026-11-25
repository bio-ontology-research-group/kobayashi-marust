import ContextCalculus.OWLFrontend.HintWitnessA
import ContextCalculus.SRIQN.HintModelFlat
import ContextCalculus.SROIQ.CoreReach

/-!
# Role facts of the witness model (stage H4, item 1)

`docs/V1.7.0-C5-HINT-ROUTE.md`, section 12. On the chain route the model
of an accepted witness hint gives every named property `r` (role term `R`
in the normal form) the relation "some path spells a word of `R`'s
language" over the model of the chain encoding (`downC_rt`). Over the
core this is decided by the product of the label graph with the role's
automaton (`SROIQ.Proc.succOf`):

* `WRF pat X W` (the role facts): with `W.chainR`, a model of `X` with the
  core inside it in which
  - a path of the label graph along a word of `R` from `w` to `v` gives
    `r(f w, f v)` (every hint);
  - for a flat hint (`W.flat`: no `kid` lines), `r(f w, f v)` gives such a
    path, and every element of the model is a core element;
  - for a simple property (`W.props`), `r(f w, f v)` iff `R ∈ lab w v`, for
    every pair of core elements, the same element included.
* `wTabCore_rfacts`, `wCoreA_rfacts`, `wTabA_rfacts`: the facts for the
  chain route, the route choice and every preparation step. On the Self
  and `ObjectHasSelf` routes `W.chainR` is false and nothing is claimed.

Hints with `kid` lines: the forest of `SRIQN/Forest.lean` gives a tree node
an edge to every core element its record's chosen support lists, and the
support is picked by choice, so a path through tree nodes can join two
core elements that the hint's labels do not join. Only the positive
direction (a path of the labels gives the edge) holds for them; the
negative direction needs a flat hint (or simple properties).
-/

namespace ContextCalculus.OWLFrontend

open ContextCalculus.OWL ContextCalculus.OWL.Datatypes SHIQD SHOIQ
open ContextCalculus.SRIQN (dbase dnoms NomAt)
open ContextCalculus.SROIQ (Gen)
open ContextCalculus.SROIQ.Proc (LPath)

/-- **The role facts on every route of the hint route.** -/
theorem wTabA_rfacts (pat : String → String → Prop) {O : Ontology} {req : List IRI}
    {hint : RawHint} {W : WTab} (hw : wTabA O req hint = some W) : WRF pat O W := by
  intro hcr
  unfold wTabA at hw
  split at hw
  · cases hw
  next O1 hO1 =>
    obtain ⟨E, W0, hE, hEn, hk, hkX, hW0, rfl⟩ := wTabEdge_cases' hw
    obtain ⟨Dom, hD, J, f, hJ, hinj, hcls, hind, hrole, hadj, hpos, hneg, hsur⟩ :=
      wCoreA_rfacts pat hW0 hcr
    haveI := hD
    set g := anonG [] (duOff E)
    have hgcls : (J.indMap g).cls = J.cls := by cases J; rfl
    have hgprop : (J.indMap g).prop = J.prop := by cases J; rfl
    have hM1 : OWL.Model O1 (J.indMap g) :=
      wTabEdge_model (fun r R hr w v => by rw [hgprop]; exact hrole r R hr w v) hadj hsur hE
        ((model_duOff _ _).1 (model_of_anonOff' hk hJ))
    have hM : ∃ J' : Interp (owl2MapP pat) Dom, OWL.Model O J' ∧ J'.cls = (J.indMap g).cls ∧
        J'.ind = (J.indMap g).ind ∧ J'.prop = (J.indMap g).prop := by
      unfold wDT at hO1
      split_ifs at hO1
      · exact model_of_dtLoop hO1 _ hM1
      · cases hO1; exact ⟨_, hM1, rfl, rfl, rfl⟩
    obtain ⟨I, hI, hIc, hIi, hIp⟩ := hM
    have hp : I.prop = J.prop := hIp.trans hgprop
    refine ⟨Dom, hD, I, f, hI, hinj, fun s x hs w => ?_, fun a x hax w => ?_,
      fun r R hr w v => by rw [hp]; exact hrole r R hr w v, hadj,
      fun r R hr w v word hg hpth => by rw [hp]; exact hpos r R hr w v word hg hpth,
      fun hfl r R hr w v h => hneg hfl r R hr w v (by rw [← hp]; exact h), hsur⟩
    · rw [hIc, hgcls]; exact hcls s x hs w
    · obtain ⟨hax, hc⟩ := List.mem_filter.1 hax
      have ha : a ∈ (duOff E).namedIndividuals := by
        rw [mem_namedIndividuals_duOff, hEn]
        simpa [Std.HashSet.contains_ofList] using hc
      have hfix : g (.named a) = .named a := anonF_short (anonBase_long (by
        simp only [List.nil_append]; exact ha))
      have : I.ind (.named a) = J.ind (.named a) := by
        rw [hIi]; cases J; simp only [Interp.indMap, hfix]
      rw [this]
      exact hind a x hax w

end ContextCalculus.OWLFrontend

#print axioms ContextCalculus.OWLFrontend.chainDownR
#print axioms ContextCalculus.OWLFrontend.wTabCore_rfacts
#print axioms ContextCalculus.OWLFrontend.wTabA_rfacts
