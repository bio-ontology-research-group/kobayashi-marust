import ContextCalculus.OWLFrontend.SHOIQNom
import ContextCalculus.OWLFrontend.SRIQKBReference
import ContextCalculus.SRIQN.Transitivity

/-!
# The OWL route for SHOIQ knowledge bases in C2a (stage C2a)

`docs/V1.7.0-C2-NOMINALS-DESIGN.md`, sections 1, 5 and 7. An ontology of
the SHOIQ knowledge-base part (`Ontology.isSHOIQKB`) is rewritten with
nominal classes (`nomOnt`), translated by the SHIQ knowledge-base
translation (`translateSRIQKB`, here without assertions), and read as an
`SRIQN` ontology: the translated clauses plus `nom X` for the index `X`
of each nominal class (`osn`). Transitivity is removed by `encTransN`
(`osnE`). The route requires a SHIQ base part (simple roles in counting
clauses) and C2a after transitivity removal (`c2aOK`), and decides with
the C2a procedures.

* `owlSHOIQC2aConsistent O hint`: consistency, exact for every hint
  (`owlSHOIQC2aConsistent_sound`), answering exactly on the SHOIQ
  knowledge-base part with the checks passed
  (`owlSHOIQC2aConsistent_isSome_iff`).
* `owlSHOIQC2aSubRow`, `owlSHOIQC2aTypeRow`, `owlSHOIQC2aSameRow`:
  subsumption between class IRIs, class assertions and equality of
  individuals, each exact for every hint (`_sound`) and answering on the
  fragment with the checks passed (`_complete`).

Hints use the text format of `SRIQKBReference.lean` without `blk` lines:
`blocks K` is the number of core elements, `ty`, `lab` and `kid` lines as
there (`RawHint.toHintN`). Concept indices: the requested IRIs, then the
nominal classes (one per named individual, in the order of
`O.individualNames`), then the other names of the translation, then the
names the transitivity encoding adds.
-/

namespace ContextCalculus.OWLFrontend

open ContextCalculus.OWL SHOIQ
open ContextCalculus.SRI (RoleT)
open ContextCalculus.SRIQ (flipL)

/-! ## The translation -/

/-- The concept index of an IRI among the named IRIs of a translation. -/
def nameIx (T : SRIQKBTranslation) (a : IRI) : Option (Fin T.conceptCount) :=
  if h : T.named.idxOf a < T.named.length then some ⟨_, Nat.lt_of_lt_of_le h T.hnamed⟩ else none

theorem nameIx_some {T : SRIQKBTranslation} {a : IRI} (ha : a ∈ T.named) :
    ∃ x, nameIx T a = some x := by
  unfold nameIx
  rw [dif_pos (List.idxOf_lt_length_of_mem ha)]
  exact ⟨_, rfl⟩

theorem nameIx_spec {T : SRIQKBTranslation} {a : IRI} {x : Fin T.conceptCount}
    (h : nameIx T a = some x) : ∃ hi : x.val < T.named.length, T.named[x.val] = a := by
  unfold nameIx at h
  split at h
  · rename_i hlt
    simp only [Option.some.injEq] at h
    subst h
    exact ⟨hlt, List.getElem_idxOf hlt⟩
  · simp at h

/-- The nominal indices of a list of IRIs. -/
def nomIxs (T : SRIQKBTranslation) (L : List IRI) : List (Fin T.conceptCount) :=
  L.filterMap (nameIx T)

/-- The `SRIQN` ontology of a translation: its clauses and a nominal
clause for each index of `L`. -/
def osn (T : SRIQKBTranslation) (L : List IRI) :
    SRIQN.Ontology (Fin T.conceptCount) (Fin T.roleCount) :=
  SRIQN.ofSRIQ T.ontology ++ (nomIxs T L).map SRIQN.Clause.nom

theorem basePart_osn (T : SRIQKBTranslation) (L : List IRI) :
    SRIQN.basePart (osn T L) = T.ontology := by
  rw [osn, SRIQN.basePart_append, SRIQN.basePart_ofSRIQ]
  simp [SRIQN.basePart, List.filterMap_map]

theorem noms_osn (T : SRIQKBTranslation) (L : List IRI) :
    SRIQN.noms (osn T L) = nomIxs T L := by
  rw [osn, SRIQN.noms_append, SRIQN.noms_ofSRIQ]
  simp [SRIQN.noms, List.filterMap_map, nomIxs]

/-- The translation of the SHOIQ route. -/
def translateSHOIQ (O : Ontology) (requested : List IRI) : Option SRIQKBTranslation :=
  if O.isSHOIQKB then translateSRIQKB (nomOnt O requested) (requested ++ nomNames O requested)
  else none

theorem collect_nil {α β : Type} {f : α → Option (List β)} :
    ∀ {xs : List α} {L : List β}, SRIQKB.collect f xs = some L → (∀ x ∈ xs, f x = some []) →
      L = []
  | [], L, h, _ => by
    simp only [SRIQKB.collect, Option.some.injEq] at h
    exact h.symm
  | x :: xs, L, h, hf => by
    have hx := hf x List.mem_cons_self
    cases hc : SRIQKB.collect f xs with
    | none => simp [SRIQKB.collect, hx, hc] at h
    | some l =>
      have hl := collect_nil hc fun y hy => hf y (List.mem_cons_of_mem _ hy)
      simp only [SRIQKB.collect, hx, hc, hl, List.nil_append, Option.some.injEq] at h
      exact h.symm

theorem assertsOf_nonAssert {F : SRIQT.St} {base : String} {inds : List IRI} {n m : Nat}
    {ax : Axiom} (h : ax.isAssertion = false) (j : Nat) :
    SRIQKB.assertsOf F base inds n m (ax, j) = some [] := by
  cases ax <;> first | rfl | simp [Axiom.isAssertion] at h

variable {O : Ontology} {requested : List IRI} {T : SRIQKBTranslation}

theorem translateSHOIQ_spec (h : translateSHOIQ O requested = some T) :
    O.isSHOIQKB = true ∧
      translateSRIQKB (nomOnt O requested) (requested ++ nomNames O requested) = some T ∧
      T.named = (requested ++ nomNames O requested).eraseDups := by
  unfold translateSHOIQ at h
  split at h
  · exact ⟨by assumption, h, (translateSRIQKB_spec h).2.1⟩
  · simp at h

theorem translateSHOIQ_isSome (hO : O.isSHOIQKB = true) (requested : List IRI) :
    (translateSHOIQ O requested).isSome = true := by
  unfold translateSHOIQ
  rw [if_pos hO]
  exact translateSRIQKB_isSome (Ontology.isSHIQKB_of_isSHIQ (nomOnt_isSHIQ hO requested).1)

theorem abox_nil (h : translateSHOIQ O requested = some T) : T.abox = [] := by
  obtain ⟨hO, hT, -⟩ := translateSHOIQ_spec h
  have hna := (nomOnt_isSHIQ hO requested).2
  unfold translateSRIQKB at hT
  dsimp only at hT
  split at hT
  · split at hT
    · obtain ⟨A, hA, rfl⟩ := Option.map_eq_some_iff.1 hT
      refine collect_nil hA fun p hp => ?_
      obtain ⟨ax, j⟩ := p
      exact assertsOf_nonAssert (hna ax (SRIQKB.mem_of_zipIdx hp)) j
    · simp at hT
  · simp at hT

theorem mem_named_nom (h : translateSHOIQ O requested = some T) {a : IRI}
    (ha : a ∈ O.individualNames) : nmOf O requested a ∈ T.named := by
  rw [(translateSHOIQ_spec h).2.2]
  exact List.mem_eraseDups.2 (List.mem_append_right _ (List.mem_map_of_mem ha))

theorem mem_named_req (h : translateSHOIQ O requested = some T) {A : IRI} (hA : A ∈ requested) :
    A ∈ T.named := by
  rw [(translateSHOIQ_spec h).2.2]
  exact List.mem_eraseDups.2 (List.mem_append_left _ hA)

theorem nom_mem_noms (_h : translateSHOIQ O requested = some T) {a : IRI}
    (ha : a ∈ O.individualNames) {x : Fin T.conceptCount}
    (hx : nameIx T (nmOf O requested a) = some x) :
    x ∈ SRIQN.noms (osn T (nomNames O requested)) := by
  rw [noms_osn]
  exact List.mem_filterMap.2 ⟨_, List.mem_map_of_mem ha, hx⟩

/-! ## The model maps -/

/-- **Up.** -/
theorem shoiq_up (h : translateSHOIQ O requested = some T) {DM : DatatypeMap} {D : Type}
    [Nonempty D] (I : Interp DM D) (hI : OWL.Model O I) :
    ∃ J : SRI.Interp D (Fin T.conceptCount) (Fin T.roleCount),
      SRIQN.models J (osn T (nomNames O requested)) ∧
      ∀ s x (ix : Fin T.conceptCount), nameIx T s = some ix →
        (J.c ix x ↔ (upI O requested I).cls s x) := by
  obtain ⟨hO, hT, -⟩ := translateSHOIQ_spec h
  obtain ⟨J, hJ, -, hc⟩ := translateSRIQKB_up hT (upI O requested I) (nomOnt_up hO requested hI)
  have hcs : ∀ s x (ix : Fin T.conceptCount), nameIx T s = some ix →
      (J.c ix x ↔ (upI O requested I).cls s x) := by
    intro s x ix hs
    obtain ⟨hi, he⟩ := nameIx_spec hs
    have := hc ix.val hi x
    rw [he] at this
    exact this
  refine ⟨J, SRIQN.models_iff.2 ⟨by rw [basePart_osn]; exact hJ, ?_⟩, hcs⟩
  intro x hx
  rw [noms_osn] at hx
  obtain ⟨s, hs, hsx⟩ := List.mem_filterMap.1 hx
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hs
  exact ⟨I.ind (.named a), fun y => (hcs _ y x hsx).trans (upI_nom I ha y)⟩

/-- **Down.** -/
theorem shoiq_down (h : translateSHOIQ O requested = some T) {D : Type} [Nonempty D]
    (J : SRI.Interp D (Fin T.conceptCount) (Fin T.roleCount))
    (hJ : SRIQN.models J (osn T (nomNames O requested))) :
    ∃ I : Interp DatatypeMap.trivial D, OWL.Model O I ∧
      (∀ s x (ix : Fin T.conceptCount), nameIx T s = some ix → (I.cls s x ↔ J.c ix x)) ∧
      ∀ a ∈ O.individualNames, ∀ ix, nameIx T (nmOf O requested a) = some ix →
        ∀ x, J.c ix x ↔ x = I.ind (.named a) := by
  obtain ⟨hO, hT, -⟩ := translateSHOIQ_spec h
  obtain ⟨hJb, hJn⟩ := SRIQN.models_iff.1 hJ
  rw [basePart_osn] at hJb
  obtain ⟨x0⟩ := (inferInstance : Nonempty D)
  obtain ⟨I0, hI0, -, hc⟩ := translateSRIQKB_down hT J (fun _ => x0) hJb (by
    rw [abox_nil h]
    intro _ h'
    simp at h')
  have hcs : ∀ s x (ix : Fin T.conceptCount), nameIx T s = some ix → (I0.cls s x ↔ J.c ix x) := by
    intro s x ix hs
    obtain ⟨hi, he⟩ := nameIx_spec hs
    have := hc ix.val hi x
    rw [he] at this
    exact this
  have hsing : ∀ a ∈ O.individualNames, ∃ x, ∀ y, I0.cls (nmOf O requested a) y ↔ y = x := by
    intro a ha
    obtain ⟨ix, hix⟩ := nameIx_some (mem_named_nom h ha)
    obtain ⟨z, hz⟩ := hJn ix (nom_mem_noms h ha hix)
    exact ⟨z, fun y => (hcs _ y ix hix).trans (hz y)⟩
  obtain ⟨hM, hcls⟩ := nomOnt_down hO requested hI0 hsing
  refine ⟨downI O requested I0, hM, fun s x ix hs => by rw [hcls]; exact hcs s x ix hs,
    fun a ha ix hix x => ?_⟩
  rw [← hcs _ x ix hix]
  exact downI_nom (hsing a ha) x

theorem shoiq_consistent (h : translateSHOIQ O requested = some T) :
    ¬ OWL.Inconsistent O ↔ SRIQN.ConsistentN (osn T (nomNames O requested)) := by
  constructor
  · intro hn
    by_contra hc
    apply hn
    intro DM D _ I hI
    obtain ⟨J, hJ, -⟩ := shoiq_up h I hI
    exact hc ⟨D, inferInstance, J, hJ⟩
  · rintro ⟨D, hD, J, hJ⟩ hinc
    obtain ⟨I, hI, -⟩ := shoiq_down h J hJ
    exact hinc _ D I hI

theorem shoiq_entailsSub (h : translateSHOIQ O requested = some T) {A B : IRI}
    (hA : A ∈ requested) (hB : B ∈ requested) {ia ib : Fin T.conceptCount}
    (hia : nameIx T A = some ia) (hib : nameIx T B = some ib) :
    OWL.EntailsSub O A B ↔ SRIQN.EntailsSubN (osn T (nomNames O requested)) ia ib := by
  constructor
  · intro he D _ J hJ x hx
    obtain ⟨I, hI, hc, -⟩ := shoiq_down h J hJ
    exact (hc B x ib hib).1 (he _ D I hI x ((hc A x ia hia).2 hx))
  · intro he DM D _ I hI x hx
    obtain ⟨J, hJ, hc⟩ := shoiq_up h I hI
    have hold : ∀ C ∈ requested, (upI O requested I).cls C = I.cls C := fun C hC =>
      upI_old I (List.mem_append_right _ hC)
    have h1 : J.c ia x := (hc A x ia hia).2 (by rw [hold A hA]; exact hx)
    have h2 := (hc B x ib hib).1 (he D J hJ x h1)
    rwa [hold B hB] at h2

theorem shoiq_entailsType (h : translateSHOIQ O requested = some T) {C a : IRI}
    (hC : C ∈ requested) (ha : a ∈ O.individualNames) {ic ia : Fin T.conceptCount}
    (hic : nameIx T C = some ic) (hia : nameIx T (nmOf O requested a) = some ia) :
    OWL.Entails O (.classAssertion (.cls C) (.named a)) ↔
      SRIQN.EntailsSubN (osn T (nomNames O requested)) ia ic := by
  constructor
  · intro he D _ J hJ x hx
    obtain ⟨I, hI, hc, hn⟩ := shoiq_down h J hJ
    have := he _ D I hI
    simp only [Interp.sat, Interp.ext] at this
    rw [(hn a ha ia hia x).1 hx]
    exact (hc C _ ic hic).1 this
  · intro he DM D _ I hI
    obtain ⟨J, hJ, hc⟩ := shoiq_up h I hI
    simp only [Interp.sat, Interp.ext]
    have h1 : J.c ia (I.ind (.named a)) := (hc _ _ ia hia).2 ((upI_nom I ha _).2 rfl)
    have h2 := (hc C _ ic hic).1 (he D J hJ _ h1)
    rwa [upI_old I (List.mem_append_right _ hC)] at h2

theorem sat_same {DM : DatatypeMap} {D : Type} (I : Interp DM D) (N : List IRI) (a b : IRI) :
    I.sat N (.sameIndividual [.named a, .named b]) ↔ I.ind (.named a) = I.ind (.named b) := by
  simp only [Interp.sat]
  constructor
  · intro h; exact h _ (by simp) _ (by simp)
  · intro h x hx y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · rfl
    · exact h
    · exact h.symm
    · rfl

theorem shoiq_entailsSame (h : translateSHOIQ O requested = some T) {a b : IRI}
    (ha : a ∈ O.individualNames) (hb : b ∈ O.individualNames) {ia ib : Fin T.conceptCount}
    (hia : nameIx T (nmOf O requested a) = some ia) (hib : nameIx T (nmOf O requested b) = some ib) :
    OWL.Entails O (.sameIndividual [.named a, .named b]) ↔
      SRIQN.EntailsSubN (osn T (nomNames O requested)) ia ib := by
  constructor
  · intro he D _ J hJ x hx
    obtain ⟨I, hI, -, hn⟩ := shoiq_down h J hJ
    have := (sat_same I _ a b).1 (he _ D I hI)
    rw [(hn a ha ia hia x).1 hx, this]
    exact (hn b hb ib hib _).2 rfl
  · intro he DM D _ I hI
    obtain ⟨J, hJ, hc⟩ := shoiq_up h I hI
    refine (sat_same I _ a b).2 ?_
    have h1 : J.c ia (I.ind (.named a)) := (hc _ _ ia hia).2 ((upI_nom I ha _).2 rfl)
    exact ((upI_nom I hb _).1 ((hc _ _ ib hib).1 (he D J hJ _ h1)))

/-! ## Hints -/

/-- A hint in the text format as a core over `Fin K`: `blocks K`, `ty`,
`lab` and `kid` lines (the `blk` lines are ignored); `none` when an index
is out of range. -/
def RawHint.toHintN (h : RawHint) (n m : Nat) : Option (SRIQN.Proc.HintN n m) :=
  match h.ty.mapM (fun e => (RawHint.finsOf n e.2).map (e.1, ·)),
    h.lab.mapM (fun e => (RawHint.rtsOf m e.2.2).map (e.1, e.2.1, ·)),
    h.kids.mapM (fun e => ((RawHint.rtsOf m e.2.1).bind fun L =>
      (RawHint.finsOf n e.2.2).map (e.1, L, ·)))
  with
  | some ty, some lab, some kids =>
    let half := fun (b c : Fin h.nb) =>
      lab.foldl (fun acc e => if e.1 = b.val ∧ e.2.1 = c.val then acc ∪ e.2.2 else acc) ∅
    some { k := h.nb
           ty := fun b => ty.foldl (fun acc e => if e.1 = b.val then acc ∪ e.2 else acc) ∅
           lab := fun b c => half b c ∪ flipL (half c b)
           kids := fun b => (kids.filter fun e => e.1 = b.val).map fun e => (e.2.1, e.2.2) }
  | _, _, _ => none

/-! ## The route -/

/-- The `SRIQN` ontology after transitivity removal. -/
abbrev osnE (T : SRIQKBTranslation) (L : List IRI) :=
  SRIQN.encTransN (osn T L)

/-- The route's checks on the `SRIQN` ontology: SHIQ base part (transitivity
and inclusions, simple roles in counting clauses) and C2a after
transitivity removal. -/
def c2aOK (T : SRIQKBTranslation) (L : List IRI) : Bool :=
  isSHIQB (SRIQN.basePart (osn T L)) && decide (SRIQN.IsC2a (osnE T L))

theorem of_c2aOK {T : SRIQKBTranslation} {L : List IRI} (h : c2aOK T L = true) :
    SRIQN.IsSHOIQ (osn T L) ∧ SRIQN.IsALCHOIQ (osnE T L) ∧ SRIQN.IsC2a (osnE T L) := by
  simp only [c2aOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨isSHIQ_of_isSHIQB h.1, SRIQN.isALCHOIQ_encTransN _, h.2⟩

theorem nomE_mem {O : Ontology} {requested : List IRI} {T : SRIQKBTranslation}
    (h : translateSHOIQ O requested = some T) {a : IRI} (ha : a ∈ O.individualNames)
    {x : Fin T.conceptCount} (hx : nameIx T (nmOf O requested a) = some x) :
    Fin.castAdd (SRIQN.encK (osn T (nomNames O requested))) x ∈
      SRIQN.noms (osnE T (nomNames O requested)) := by
  rw [SRIQN.noms_encTransN]
  exact List.mem_map_of_mem (nom_mem_noms h ha hx)

/-- The checks pass on the translation. -/
def SHOIQC2aChecks (O : Ontology) (requested : List IRI) : Prop :=
  ∀ T, translateSHOIQ O requested = some T → c2aOK T (nomNames O requested) = true

/-- **Consistency of a SHOIQ knowledge base in C2a.** -/
def owlSHOIQC2aConsistent (O : Ontology) (hint : Option RawHint) : Option Bool :=
  match translateSHOIQ O [] with
  | none => none
  | some T =>
    if c2aOK T (nomNames O []) then
      some (SRIQN.Proc.consistentN (SRIQN.basePart (osnE T (nomNames O [])))
        (SRIQN.noms (osnE T (nomNames O []))) (hint.bind (·.toHintN _ _)))
    else none

/-- **Soundness.** Every answer is exact under the OWL 2 direct semantics,
for every hint. -/
theorem owlSHOIQC2aConsistent_sound {O : Ontology} {hint : Option RawHint} {v : Bool}
    (h : owlSHOIQC2aConsistent O hint = some v) : v = true ↔ ¬ OWL.Inconsistent O := by
  unfold owlSHOIQC2aConsistent at h
  split at h
  · simp at h
  · next T hT =>
    split at h
    · next hok =>
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨hS, hA, hC⟩ := of_c2aOK hok
      rw [SRIQN.Proc.consistentN_iff hA hC, ← SRIQN.consistentN_encTransN hS, shoiq_consistent hT]
    · simp at h

/-- **Completeness.** The route answers exactly on the SHOIQ knowledge-base
part with the checks passed. -/
theorem owlSHOIQC2aConsistent_isSome_iff (O : Ontology) (hint : Option RawHint) :
    (owlSHOIQC2aConsistent O hint).isSome = true ↔ O.isSHOIQKB = true ∧ SHOIQC2aChecks O [] := by
  constructor
  · intro h
    unfold owlSHOIQC2aConsistent at h
    split at h
    · simp at h
    · next T hT =>
      split at h
      · next hok =>
        refine ⟨(translateSHOIQ_spec hT).1, fun T' hT' => ?_⟩
        rw [hT] at hT'
        cases hT'
        exact hok
      · simp at h
  · rintro ⟨hO, hc⟩
    have hT := translateSHOIQ_isSome hO []
    unfold owlSHOIQC2aConsistent
    split
    · next hn => rw [hn] at hT; simp at hT
    · next T hT' => simp [hc T hT']

/-! ## Rows -/

/-- `O` with declarations of the individuals `L`. -/
def withInds (O : Ontology) (L : List IRI) : Ontology :=
  ⟨O.axioms ++ L.map Axiom.declareNamedIndividual⟩

theorem sat_N_shoiq {DM : DatatypeMap} {D : Type} {I : Interp DM D} {ax : Axiom}
    (h : ax.isSHOIQKB = true) (N N' : List IRI) : I.sat N ax ↔ I.sat N' ax := by
  cases ax <;> first | exact Iff.rfl | simp [Axiom.isSHOIQKB, Axiom.isSHIQ, Axiom.isSHI,
    Axiom.isSRI] at h

theorem isSHOIQKB_withInds {O : Ontology} (hO : O.isSHOIQKB = true) (L : List IRI) :
    (withInds O L).isSHOIQKB = true := by
  simp only [Ontology.isSHOIQKB, withInds, List.all_append, Bool.and_eq_true] at hO ⊢
  refine ⟨hO, ?_⟩
  simp [List.all_eq_true, Axiom.isSHOIQKB]

theorem model_withInds {O : Ontology} (hO : O.isSHOIQKB = true) (L : List IRI)
    {DM : DatatypeMap} {D : Type} (I : Interp DM D) :
    OWL.Model (withInds O L) I ↔ OWL.Model O I := by
  have hO' : ∀ ax ∈ O.axioms, ax.isSHOIQKB = true := by
    simpa [Ontology.isSHOIQKB, List.all_eq_true] using hO
  simp only [OWL.Model, withInds, List.mem_append, List.mem_map]
  constructor
  · intro h ax hax
    exact (sat_N_shoiq (hO' ax hax) _ _).1 (h ax (Or.inl hax))
  · rintro h ax (hax | ⟨a, -, rfl⟩)
    · exact (sat_N_shoiq (hO' ax hax) _ _).1 (h ax hax)
    · trivial

theorem entails_withInds {O : Ontology} (hO : O.isSHOIQKB = true) (L : List IRI) (ax : Axiom) :
    OWL.Entails (withInds O L) ax ↔ OWL.Entails O ax := by
  unfold OWL.Entails
  simp only [model_withInds hO]

theorem mem_individualNames_withInds {O : Ontology} {L : List IRI} {a : IRI} (ha : a ∈ L) :
    a ∈ (withInds O L).individualNames :=
  (Ontology.mem_namesBy _ _ a).2 ⟨.declareNamedIndividual a,
    by simp [withInds, ha], by simp [Axiom.namedIndividuals]⟩

/-- **Subsumption** `SubClassOf(A B)` between class IRIs. -/
def owlSHOIQC2aSubRow (O : Ontology) (A B : IRI) (hint : Option RawHint) : Option Bool :=
  match translateSHOIQ O [A, B] with
  | none => none
  | some T =>
    if c2aOK T (nomNames O [A, B]) then
      match nameIx T A, nameIx T B with
      | some ia, some ib =>
        some (SRIQN.Proc.subRowN (osnE T (nomNames O [A, B])) (Fin.castAdd _ ia) (Fin.castAdd _ ib)
          (hint.bind (·.toHintN _ _)))
      | _, _ => none
    else none

theorem owlSHOIQC2aSubRow_sound {O : Ontology} {A B : IRI} {hint : Option RawHint} {v : Bool}
    (h : owlSHOIQC2aSubRow O A B hint = some v) : v = true ↔ OWL.EntailsSub O A B := by
  unfold owlSHOIQC2aSubRow at h
  split at h
  · simp at h
  · next T hT =>
    split at h
    · next hok =>
      split at h
      · next ia ib hia hib =>
        simp only [Option.some.injEq] at h
        subst h
        obtain ⟨hS, hA, hC⟩ := of_c2aOK hok
        rw [SRIQN.Proc.subRowN_iff hA hC, ← SRIQN.entailsSubN_encTransN hS,
          shoiq_entailsSub hT (by simp) (by simp) hia hib]
      · simp at h
    · simp at h

theorem owlSHOIQC2aSubRow_complete {O : Ontology} (A B : IRI) (hO : O.isSHOIQKB = true)
    (hc : SHOIQC2aChecks O [A, B]) (hint : Option RawHint) :
    (owlSHOIQC2aSubRow O A B hint).isSome = true := by
  have hT := translateSHOIQ_isSome hO [A, B]
  unfold owlSHOIQC2aSubRow
  split
  · next hn => rw [hn] at hT; simp at hT
  · next T hT' =>
    obtain ⟨ia, hia⟩ := nameIx_some (mem_named_req hT' (A := A) (by simp))
    obtain ⟨ib, hib⟩ := nameIx_some (mem_named_req hT' (A := B) (by simp))
    simp [hc T hT', hia, hib]

/-- **Type** `ClassAssertion(C a)` of a named individual. -/
def owlSHOIQC2aTypeRow (O : Ontology) (C a : IRI) (hint : Option RawHint) : Option Bool :=
  match translateSHOIQ (withInds O [a]) [C] with
  | none => none
  | some T =>
    if c2aOK T (nomNames (withInds O [a]) [C]) then
      match nameIx T C, nameIx T (nmOf (withInds O [a]) [C] a) with
      | some ic, some ia =>
        some (SRIQN.Proc.nomRowN (osnE T (nomNames (withInds O [a]) [C])) (Fin.castAdd _ ia)
          (Fin.castAdd _ ic) (hint.bind (·.toHintN _ _)))
      | _, _ => none
    else none

theorem owlSHOIQC2aTypeRow_sound {O : Ontology} {C a : IRI} {hint : Option RawHint} {v : Bool}
    (h : owlSHOIQC2aTypeRow O C a hint = some v) :
    v = true ↔ OWL.Entails O (.classAssertion (.cls C) (.named a)) := by
  unfold owlSHOIQC2aTypeRow at h
  split at h
  · simp at h
  · next T hT =>
    split at h
    · next hok =>
      split at h
      · next ic ia hic hia =>
        simp only [Option.some.injEq] at h
        subst h
        obtain ⟨hS, hA, hC⟩ := of_c2aOK hok
        have hO := (translateSHOIQ_spec hT).1
        have ha : a ∈ (withInds O [a]).individualNames := mem_individualNames_withInds (by simp)
        rw [SRIQN.Proc.nomRowN_iff hA hC (nomE_mem hT ha hia), ← SRIQN.entailsSubN_encTransN hS,
          ← shoiq_entailsType hT (by simp) ha hic hia]
        refine entails_withInds ?_ [a] _
        simp only [Ontology.isSHOIQKB, withInds, List.all_append, Bool.and_eq_true] at hO
        exact hO.1
      · simp at h
    · simp at h

theorem owlSHOIQC2aTypeRow_complete {O : Ontology} (C a : IRI) (hO : O.isSHOIQKB = true)
    (hc : SHOIQC2aChecks (withInds O [a]) [C]) (hint : Option RawHint) :
    (owlSHOIQC2aTypeRow O C a hint).isSome = true := by
  have hT := translateSHOIQ_isSome (isSHOIQKB_withInds hO [a]) [C]
  unfold owlSHOIQC2aTypeRow
  split
  · next hn => rw [hn] at hT; simp at hT
  · next T hT' =>
    obtain ⟨ic, hic⟩ := nameIx_some (mem_named_req hT' (A := C) (by simp))
    obtain ⟨ia, hia⟩ := nameIx_some (mem_named_nom hT'
      (mem_individualNames_withInds (O := O) (L := [a]) (a := a) (by simp)))
    simp [hc T hT', hic, hia]

/-- **Equality** `SameIndividual(a b)` of named individuals. -/
def owlSHOIQC2aSameRow (O : Ontology) (a b : IRI) (hint : Option RawHint) : Option Bool :=
  match translateSHOIQ (withInds O [a, b]) [] with
  | none => none
  | some T =>
    if c2aOK T (nomNames (withInds O [a, b]) []) then
      match nameIx T (nmOf (withInds O [a, b]) [] a), nameIx T (nmOf (withInds O [a, b]) [] b) with
      | some ia, some ib =>
        some (SRIQN.Proc.nomRowN (osnE T (nomNames (withInds O [a, b]) [])) (Fin.castAdd _ ia)
          (Fin.castAdd _ ib) (hint.bind (·.toHintN _ _)))
      | _, _ => none
    else none

theorem owlSHOIQC2aSameRow_sound {O : Ontology} {a b : IRI} {hint : Option RawHint} {v : Bool}
    (h : owlSHOIQC2aSameRow O a b hint = some v) :
    v = true ↔ OWL.Entails O (.sameIndividual [.named a, .named b]) := by
  unfold owlSHOIQC2aSameRow at h
  split at h
  · simp at h
  · next T hT =>
    split at h
    · next hok =>
      split at h
      · next ia ib hia hib =>
        simp only [Option.some.injEq] at h
        subst h
        obtain ⟨hS, hA, hC⟩ := of_c2aOK hok
        have hO := (translateSHOIQ_spec hT).1
        have ha : a ∈ (withInds O [a, b]).individualNames := mem_individualNames_withInds (by simp)
        have hb : b ∈ (withInds O [a, b]).individualNames := mem_individualNames_withInds (by simp)
        rw [SRIQN.Proc.nomRowN_iff hA hC (nomE_mem hT ha hia), ← SRIQN.entailsSubN_encTransN hS,
          ← shoiq_entailsSame hT ha hb hia hib]
        refine entails_withInds ?_ [a, b] _
        simp only [Ontology.isSHOIQKB, withInds, List.all_append, Bool.and_eq_true] at hO
        exact hO.1
      · simp at h
    · simp at h

theorem owlSHOIQC2aSameRow_complete {O : Ontology} (a b : IRI) (hO : O.isSHOIQKB = true)
    (hc : SHOIQC2aChecks (withInds O [a, b]) []) (hint : Option RawHint) :
    (owlSHOIQC2aSameRow O a b hint).isSome = true := by
  have hT := translateSHOIQ_isSome (isSHOIQKB_withInds hO [a, b]) []
  unfold owlSHOIQC2aSameRow
  split
  · next hn => rw [hn] at hT; simp at hT
  · next T hT' =>
    obtain ⟨ia, hia⟩ := nameIx_some (mem_named_nom hT'
      (mem_individualNames_withInds (O := O) (L := [a, b]) (a := a) (by simp)))
    obtain ⟨ib, hib⟩ := nameIx_some (mem_named_nom hT'
      (mem_individualNames_withInds (O := O) (L := [a, b]) (a := b) (by simp)))
    simp [hc T hT', hia, hib]

end ContextCalculus.OWLFrontend

#print axioms ContextCalculus.OWLFrontend.owlSHOIQC2aConsistent_sound
#print axioms ContextCalculus.OWLFrontend.owlSHOIQC2aConsistent_isSome_iff
#print axioms ContextCalculus.OWLFrontend.owlSHOIQC2aSubRow_sound
#print axioms ContextCalculus.OWLFrontend.owlSHOIQC2aSubRow_complete
#print axioms ContextCalculus.OWLFrontend.owlSHOIQC2aTypeRow_sound
#print axioms ContextCalculus.OWLFrontend.owlSHOIQC2aTypeRow_complete
#print axioms ContextCalculus.OWLFrontend.owlSHOIQC2aSameRow_sound
#print axioms ContextCalculus.OWLFrontend.owlSHOIQC2aSameRow_complete
