import ContextCalculus.OWL.Datatypes.CellsEval

/-!
# The oracle of the OWL 2 datatype map (v1.7.0 stage C4, part C)

Data atoms are OWL data ranges (`spec : Fin q → DataRange`). Their data
theory at the map `owl2MapP pat` (`owlTheory`) has one admissible pair
per interpretation of the datatypes outside the map: up to a bijection
with the values of the map, atom `p` holds at `v` iff `v` lies in
`(spec p).ext (owl2MapP pat) dtype`.

A data range of the supported sub-language (`drSupported`) is a Boolean
combination of base atoms (`OWL/Datatypes/Cells.lean`) and free datatypes:
`drEval` evaluates it from the base atoms and the free datatypes that
hold (`ext_iff_drEval`). Declined (`drSupported` is `false`): the kinds
that `supportedKind` declines (`xsd:normalizedString`,
`xsd:token`, `xsd:Name`, `xsd:NCName`, `xsd:NMTOKEN`) and facet
restrictions on the datatypes of the map other than the numeric ones and
`xsd:double`, `xsd:float` (`xsd:string` length facets, `xsd:pattern`,
`rdf:langRange`, `xsd:dateTime` bounds). Restrictions on numeric types
with facets other than the four bounds, or with facet values that are not
numbers, are empty in the map, and are supported as such; the same holds
for `xsd:double` and `xsd:float` with facet values that are not floats of
the same type (`floatBound`); restrictions on datatypes outside the map with at least one facet
are empty as well.

`owlCard spec` is the cell oracle (`SRIQD/CellOracle.lean`) over the base
atoms of all atoms and the free datatypes. **`oracleSpec_owl`**: if every
atom is supported and the free datatypes pass `freeCheck`, `owlCard spec`
satisfies `OracleSpec (owlTheory pat spec)`, for every reading `pat` of
`xsd:pattern`. `owlCheck` decides both conditions.

The free-datatype condition is needed: with a free datatype `F` and a
literal atom `{l}`, the value types `{l}, F` and `{l}, ¬F` can each have one
value, but not together, so no oracle exists (`SRIQD/CellOracle.lean`).
-/

namespace ContextCalculus.OWL.Datatypes

open ContextCalculus.SRIQD

/-! ## Data ranges over base atoms -/

/-- A bound facet with a numeric value. -/
def facetBound (f : IRI × Literal) : Option ((Bool × Bool) × ℚ) :=
  match boundFacet f.1, litVal f.2 with
  | some b, some (.num q) => some (b, q)
  | _, _ => none

/-- A bound facet whose value is a float of the restricted float type `k`. -/
def floatBound (k : Kind) (f : IRI × Literal) : Option ((Bool × Bool) × ValOf ℚ) :=
  match boundFacet f.1, litVal f.2 with
  | some b, some (.dbl y) => if k = .double then some (b, .dbl y) else none
  | some b, some (.flt y) => if k = .float then some (b, .flt y) else none
  | _, _ => none

/-- Evaluate a data range from the base atoms `bv` and the free datatypes
`fv` that hold at a value. -/
def drEval (bv : BAtom → Bool) (fv : IRI → Bool) : DataRange → Bool
  | .datatype t =>
    match kindOf t with
    | some k => bv (.kind k)
    | none => fv t
  | .and rs => rs.attach.all fun ⟨r, _⟩ => drEval bv fv r
  | .or rs => rs.attach.any fun ⟨r, _⟩ => drEval bv fv r
  | .not r => !drEval bv fv r
  | .oneOf ls => ls.any fun l =>
    match litVal l with
    | some w => bv (.lit w)
    | none => false
  | .restriction t fs =>
    if fs = [] then
      match kindOf t with
      | some k => bv (.kind k)
      | none => fv t
    else
      match kindOf t with
      | some k =>
        if fltKind k then
          match fs.mapM (floatBound k) with
          | some bs => bv (.fltB k bs)
          | none => false
        else
          match fs.mapM facetBound with
          | some bs => bv (.numR k bs)
          | none => false
      | none => false
termination_by r => sizeOf r
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ rs›; omega)

/-- The base atoms of a data range. -/
def drBases : DataRange → List BAtom
  | .datatype t =>
    match kindOf t with
    | some k => [.kind k]
    | none => []
  | .and rs => rs.attach.flatMap fun ⟨r, _⟩ => drBases r
  | .or rs => rs.attach.flatMap fun ⟨r, _⟩ => drBases r
  | .not r => drBases r
  | .oneOf ls => ls.filterMap fun l => (litVal l).map .lit
  | .restriction t fs =>
    if fs = [] then
      match kindOf t with
      | some k => [.kind k]
      | none => []
    else
      match kindOf t with
      | some k =>
        if fltKind k then
          match fs.mapM (floatBound k) with
          | some bs => [.fltB k bs]
          | none => []
        else
          match fs.mapM facetBound with
          | some bs => [.numR k bs]
          | none => []
      | none => []
termination_by r => sizeOf r
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ rs›; omega)

/-- The free datatypes of a data range. -/
def drFrees : DataRange → List IRI
  | .datatype t =>
    match kindOf t with
    | some _ => []
    | none => [t]
  | .and rs => rs.attach.flatMap fun ⟨r, _⟩ => drFrees r
  | .or rs => rs.attach.flatMap fun ⟨r, _⟩ => drFrees r
  | .not r => drFrees r
  | .oneOf _ => []
  | .restriction t fs =>
    if fs = [] then
      match kindOf t with
      | some _ => []
      | none => [t]
    else []
termination_by r => sizeOf r
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ rs›; omega)

/-- The supported sub-language. -/
def drSupported : DataRange → Bool
  | .datatype t =>
    match kindOf t with
    | some k => supportedKind k
    | none => true
  | .and rs => rs.attach.all fun ⟨r, _⟩ => drSupported r
  | .or rs => rs.attach.all fun ⟨r, _⟩ => drSupported r
  | .not r => drSupported r
  | .oneOf _ => true
  | .restriction t fs =>
    if fs = [] then
      match kindOf t with
      | some k => supportedKind k
      | none => true
    else
      match kindOf t with
      | some k => numKind k || fltKind k
      | none => true
termination_by r => sizeOf r
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ rs›; omega)

/-! ## The map on datatypes and facets -/

section MapFacts

variable (pat : String → String → Prop)

theorem owl2MapP_datatype (t : IRI) : (owl2MapP pat).datatype t = (kindOf t).map kindSem := rfl

theorem kindOf_rdfsLiteral : kindOf rdfsLiteral = some .literal := by decide +kernel

theorem dtExt_some {t : IRI} {k : Kind} (h : kindOf t = some k) (dtype : IRI → Val → Prop) :
    (owl2MapP pat).dtExt dtype t = kindSem k := by
  unfold DatatypeMap.dtExt
  split_ifs with ht
  · subst ht
    rw [kindOf_rdfsLiteral] at h
    cases h
    rfl
  · rw [owl2MapP_datatype, h]
    rfl

theorem dtExt_none {t : IRI} (h : kindOf t = none) (dtype : IRI → Val → Prop) :
    (owl2MapP pat).dtExt dtype t = dtype t := by
  unfold DatatypeMap.dtExt
  split_ifs with ht
  · subst ht
    rw [kindOf_rdfsLiteral] at h
    cases h
  · rw [owl2MapP_datatype, h]
    rfl

theorem facet_numeric {t : IRI} {k : Kind} (h : kindOf t = some k) (hk : numKind k = true)
    (f : IRI × Literal) :
    (owl2MapP pat).facet t f.1 f.2 =
      (facetBound f).map fun bq => fun v => ∃ x, v = .num x ∧ boundRel bq.1 x (bq.2 : ℝ) := by
  show (match kindOf t with
    | some k => facetSem pat k f.1 (litVal f.2)
    | none => none) = _
  rw [h]
  have hnum : numeric k = true := by cases k <;> simp_all [numKind, numeric]
  have hd : k ≠ .double := by rintro rfl; simp [numKind] at hk
  have hf : k ≠ .float := by rintro rfl; simp [numKind] at hk
  have ht : ¬ (k = .dateTime ∨ k = .dateTimeStamp) := by
    rintro (rfl | rfl) <;> simp [numKind] at hk
  have hs : stringish k = false := by cases k <;> simp_all [numKind, stringish]
  have hb : ¬ (k = .hexBinary ∨ k = .base64Binary) := by
    rintro (rfl | rfl) <;> simp [numKind] at hk
  have hp : ¬ k = .plainLiteral := by rintro rfl; simp [numKind] at hk
  unfold facetSem facetBound
  rcases hbf : boundFacet f.1 with _ | b <;> rcases hl : litVal f.2 with _ | w <;>
    rcases hlf : lengthFacet f.1 with _ | L <;>
    (try rcases w with q | x | x | ⟨s, _ | t⟩ | b | bs | bs | s | ⟨t, z⟩ | s | n) <;> simp_all <;> rfl

theorem facet_float {t : IRI} {k : Kind} (h : kindOf t = some k) (hk : fltKind k = true)
    (f : IRI × Literal) :
    (owl2MapP pat).facet t f.1 f.2 = (floatBound k f).map fun bq => fltSem bq.1 bq.2 := by
  show (match kindOf t with
    | some k => facetSem pat k f.1 (litVal f.2)
    | none => none) = _
  rw [h]
  cases k <;> simp [fltKind] at hk <;> unfold facetSem floatBound <;>
    rcases hbf : boundFacet f.1 with _ | b <;> rcases hl : litVal f.2 with _ | w <;>
    rcases hlf : lengthFacet f.1 with _ | L <;>
    (try rcases w with q | x | x | ⟨s, _ | t⟩ | b | bs | bs | s | ⟨t, z⟩ | s | n) <;>
    simp_all [numeric, stringish] <;> rfl

theorem facet_free {t : IRI} (h : kindOf t = none) (f : IRI) (l : Literal) :
    (owl2MapP pat).facet t f l = none := by
  show (match kindOf t with
    | some k => facetSem pat k f (litVal l)
    | none => none) = none
  rw [h]

end MapFacts

theorem mapM_facets {fs : List (IRI × Literal)} {bs : List ((Bool × Bool) × ℚ)}
    (h : fs.mapM facetBound = some bs) (P : (Bool × Bool) × ℚ → Prop) :
    (∀ f ∈ fs, ∃ bq, facetBound f = some bq ∧ P bq) ↔ ∀ b ∈ bs, P b := by
  induction fs generalizing bs with
  | nil =>
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    simp
  | cons f fs ih =>
    simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind] at h
    rcases hf : facetBound f with _ | bq
    · rw [hf] at h; simp at h
    · rw [hf] at h
      rcases hfs : fs.mapM facetBound with _ | bs'
      · rw [hfs] at h; simp at h
      · rw [hfs] at h
        simp only [Option.bind_some, Option.some.injEq] at h
        subst h
        simp only [List.mem_cons, forall_eq_or_imp, hf, Option.some.injEq, exists_eq_left']
        rw [ih hfs]

theorem mapM_none {fs : List (IRI × Literal)} (h : fs.mapM facetBound = none) :
    ∃ f ∈ fs, facetBound f = none := by
  induction fs with
  | nil => simp at h
  | cons f fs ih =>
    simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind] at h
    rcases hf : facetBound f with _ | bq
    · exact ⟨f, List.mem_cons_self, hf⟩
    · rw [hf] at h
      rcases hfs : fs.mapM facetBound with _ | bs'
      · obtain ⟨f', hf', h'⟩ := ih hfs
        exact ⟨f', List.mem_cons_of_mem _ hf', h'⟩
      · rw [hfs] at h; simp at h

theorem mapM_all {β : Type} {g : IRI × Literal → Option β} {fs : List (IRI × Literal)} {bs : List β}
    (h : fs.mapM g = some bs) (P : β → Prop) :
    (∀ f ∈ fs, ∃ bq, g f = some bq ∧ P bq) ↔ ∀ b ∈ bs, P b := by
  induction fs generalizing bs with
  | nil =>
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    simp
  | cons f fs ih =>
    simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind] at h
    rcases hf : g f with _ | bq
    · rw [hf] at h; simp at h
    · rw [hf] at h
      rcases hfs : fs.mapM g with _ | bs'
      · rw [hfs] at h; simp at h
      · rw [hfs] at h
        simp only [Option.bind_some, Option.some.injEq] at h
        subst h
        simp only [List.mem_cons, forall_eq_or_imp, hf, Option.some.injEq, exists_eq_left']
        rw [ih hfs]

theorem mapM_none' {β : Type} {g : IRI × Literal → Option β} {fs : List (IRI × Literal)}
    (h : fs.mapM g = none) : ∃ f ∈ fs, g f = none := by
  induction fs with
  | nil => simp at h
  | cons f fs ih =>
    simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind] at h
    rcases hf : g f with _ | bq
    · exact ⟨f, List.mem_cons_self, hf⟩
    · rw [hf] at h
      rcases hfs : fs.mapM g with _ | bs'
      · obtain ⟨f', hf', h'⟩ := ih hfs
        exact ⟨f', List.mem_cons_of_mem _ hf', h'⟩
      · rw [hfs] at h; simp at h

/-! ## Data ranges as Boolean combinations -/

section Eval

variable (pat : String → String → Prop) (dtype : IRI → Val → Prop) (v : Val)
  (bv : BAtom → Bool) (fv : IRI → Bool)

/-- **A supported data range is its Boolean combination.** -/
theorem ext_iff_drEval : ∀ (dr : DataRange), drSupported dr = true →
    (∀ a ∈ drBases dr, a.sem v ↔ bv a = true) → (∀ t ∈ drFrees dr, dtype t v ↔ fv t = true) →
    (dr.ext (owl2MapP pat) dtype v ↔ drEval bv fv dr = true)
  | .datatype t, _, hb, hf => by
    rw [DataRange.ext, drEval]
    rcases hk : kindOf t with _ | k
    · rw [dtExt_none pat hk]
      exact hf t (by rw [drFrees, hk]; exact List.mem_singleton_self _)
    · rw [dtExt_some pat hk]
      exact hb (.kind k) (by rw [drBases, hk]; exact List.mem_singleton_self _)
  | .and rs, hs, hb, hf => by
    rw [DataRange.ext, drEval, List.all_eq_true]
    rw [drSupported, List.all_eq_true] at hs
    constructor
    · rintro h ⟨r, hr⟩ -
      refine (ext_iff_drEval r (hs ⟨r, hr⟩ (List.mem_attach _ _)) (fun a ha => hb a ?_)
        (fun t ht => hf t ?_)).1 (h r hr)
      · rw [drBases]; exact List.mem_flatMap.2 ⟨⟨r, hr⟩, List.mem_attach _ _, ha⟩
      · rw [drFrees]; exact List.mem_flatMap.2 ⟨⟨r, hr⟩, List.mem_attach _ _, ht⟩
    · intro h r hr
      refine (ext_iff_drEval r (hs ⟨r, hr⟩ (List.mem_attach _ _)) (fun a ha => hb a ?_)
        (fun t ht => hf t ?_)).2 (h ⟨r, hr⟩ (List.mem_attach _ _))
      · rw [drBases]; exact List.mem_flatMap.2 ⟨⟨r, hr⟩, List.mem_attach _ _, ha⟩
      · rw [drFrees]; exact List.mem_flatMap.2 ⟨⟨r, hr⟩, List.mem_attach _ _, ht⟩
  | .or rs, hs, hb, hf => by
    rw [DataRange.ext, drEval, List.any_eq_true]
    rw [drSupported, List.all_eq_true] at hs
    constructor
    · rintro ⟨r, hr, h⟩
      refine ⟨⟨r, hr⟩, List.mem_attach _ _, (ext_iff_drEval r (hs ⟨r, hr⟩ (List.mem_attach _ _))
        (fun a ha => hb a ?_) (fun t ht => hf t ?_)).1 h⟩
      · rw [drBases]; exact List.mem_flatMap.2 ⟨⟨r, hr⟩, List.mem_attach _ _, ha⟩
      · rw [drFrees]; exact List.mem_flatMap.2 ⟨⟨r, hr⟩, List.mem_attach _ _, ht⟩
    · rintro ⟨⟨r, hr⟩, -, h⟩
      refine ⟨r, hr, (ext_iff_drEval r (hs ⟨r, hr⟩ (List.mem_attach _ _))
        (fun a ha => hb a ?_) (fun t ht => hf t ?_)).2 h⟩
      · rw [drBases]; exact List.mem_flatMap.2 ⟨⟨r, hr⟩, List.mem_attach _ _, ha⟩
      · rw [drFrees]; exact List.mem_flatMap.2 ⟨⟨r, hr⟩, List.mem_attach _ _, ht⟩
  | .not r, hs, hb, hf => by
    rw [DataRange.ext, drEval]
    rw [drSupported] at hs
    beta_reduce
    rw [ext_iff_drEval r hs (fun a ha => hb a (by rw [drBases]; exact ha))
      (fun t ht => hf t (by rw [drFrees]; exact ht))]
    simp
  | .oneOf ls, _, hb, _ => by
    rw [DataRange.ext, drEval, List.any_eq_true]
    constructor
    · rintro ⟨l, hl, he⟩
      refine ⟨l, hl, ?_⟩
      rw [owl2MapP_literal] at he
      rcases hw : litVal l with _ | w
      · rw [hw] at he; cases he
      · rw [hw] at he
        simp only [Option.map_some] at he
        exact (hb (.lit w) (by
          rw [drBases]; exact List.mem_filterMap.2 ⟨l, hl, by rw [hw]; rfl⟩)).1
          (Option.some_inj.1 he).symm
    · rintro ⟨l, hl, he⟩
      refine ⟨l, hl, ?_⟩
      rcases hw : litVal l with _ | w
      · rw [hw] at he; cases he
      · rw [hw] at he
        have := (hb (.lit w) (by
          rw [drBases]; exact List.mem_filterMap.2 ⟨l, hl, by rw [hw]; rfl⟩)).2 he
        rw [owl2MapP_literal, hw, Option.map_some]
        exact congrArg some this.symm
  | .restriction t fs, hs, hb, hf => by
    rw [DataRange.ext, drEval]
    by_cases hfs : fs = []
    · subst hfs
      simp only [List.not_mem_nil, false_implies, implies_true, and_true, if_true]
      rcases hk : kindOf t with _ | k
      · rw [dtExt_none pat hk]
        exact hf t (by rw [drFrees, if_pos rfl, hk]; exact List.mem_singleton_self _)
      · rw [dtExt_some pat hk]
        exact hb (.kind k) (by rw [drBases, if_pos rfl, hk]; exact List.mem_singleton_self _)
    · rw [if_neg hfs]
      obtain ⟨f0, hf0⟩ := List.exists_mem_of_ne_nil fs hfs
      rcases hk : kindOf t with _ | k
      · simp only [facet_free pat hk, reduceCtorEq, false_and, exists_false, iff_false]
        rintro ⟨-, h⟩
        exact h f0 hf0
      · rw [drSupported, if_neg hfs, hk] at hs
        rw [dtExt_some pat hk]
        dsimp only at hs ⊢
        by_cases hfk : fltKind k = true
        · rw [if_pos hfk]
          have hfacet := facet_float pat hk hfk
          rcases hm : fs.mapM (floatBound k) with _ | bs
          · simp only [Bool.false_eq_true, iff_false]
            rintro ⟨-, h⟩
            obtain ⟨f, hf, hnone⟩ := mapM_none' hm
            obtain ⟨p, hp, -⟩ := h f hf
            rw [hfacet f, hnone] at hp
            cases hp
          · have hbm := hb (.fltB k bs) (by
              rw [drBases, if_neg hfs, hk]; simp only [hfk, if_true, hm]; exact List.mem_singleton_self _)
            simp only at hbm ⊢
            rw [← hbm, BAtom.sem]
            refine and_congr_right fun _ => ?_
            rw [← mapM_all hm (fun bq => fltSem bq.1 bq.2 v)]
            refine forall₂_congr fun f _ => ?_
            rw [hfacet f]
            constructor
            · rintro ⟨p, hp, hpv⟩
              rcases hfb : floatBound k f with _ | bq
              · rw [hfb] at hp; cases hp
              · rw [hfb] at hp
                simp only [Option.map_some] at hp
                have hp' := Option.some.inj hp
                subst hp'
                exact ⟨bq, rfl, hpv⟩
            · rintro ⟨bq, hbq, hpv⟩
              exact ⟨_, by rw [hbq]; rfl, hpv⟩
        rw [if_neg hfk]
        replace hs : numKind k = true := by simpa [hfk] using hs
        have hfacet := facet_numeric pat hk hs
        rcases hm : fs.mapM facetBound with _ | bs
        · simp only [Bool.false_eq_true, iff_false]
          rintro ⟨-, h⟩
          obtain ⟨f, hf, hnone⟩ := mapM_none hm
          obtain ⟨p, hp, -⟩ := h f hf
          rw [hfacet f, hnone] at hp
          cases hp
        · have hbm := hb (.numR k bs) (by
            rw [drBases, if_neg hfs, hk]; simp only [hfk, if_false, Bool.false_eq_true, hm]
            exact List.mem_singleton_self _)
          simp only at hbm ⊢
          rw [← hbm, BAtom.sem]
          refine and_congr_right fun _ => ?_
          rw [← mapM_facets hm]
          refine forall₂_congr fun f _ => ?_
          rw [hfacet f]
          constructor
          · rintro ⟨p, hp, hpv⟩
            rcases hfb : facetBound f with _ | bq
            · rw [hfb] at hp; cases hp
            · rw [hfb] at hp
              simp only [Option.map_some, Option.some.injEq] at hp
              subst hp
              exact ⟨bq, rfl, hpv⟩
          · rintro ⟨bq, hbq, hpv⟩
            exact ⟨_, by rw [hbq]; rfl, hpv⟩
termination_by dr => sizeOf dr
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ rs›; omega)

end Eval

/-- The base atoms of a supported data range are supported. -/
theorem supported_of_drBases : ∀ (dr : DataRange), drSupported dr = true →
    ∀ a ∈ drBases dr, a.supported = true
  | .datatype t, hs, a, ha => by
    rw [drBases] at ha
    rw [drSupported] at hs
    rcases hk : kindOf t with _ | k <;> rw [hk] at ha hs
    · simp at ha
    · rw [List.mem_singleton] at ha
      subst ha
      exact hs
  | .and rs, hs, a, ha => by
    rw [drBases] at ha
    rw [drSupported, List.all_eq_true] at hs
    obtain ⟨⟨r, hr⟩, hm, ha⟩ := List.mem_flatMap.1 ha
    exact supported_of_drBases r (hs ⟨r, hr⟩ hm) a ha
  | .or rs, hs, a, ha => by
    rw [drBases] at ha
    rw [drSupported, List.all_eq_true] at hs
    obtain ⟨⟨r, hr⟩, hm, ha⟩ := List.mem_flatMap.1 ha
    exact supported_of_drBases r (hs ⟨r, hr⟩ hm) a ha
  | .not r, hs, a, ha => by
    rw [drBases] at ha
    rw [drSupported] at hs
    exact supported_of_drBases r hs a ha
  | .oneOf ls, _, a, ha => by
    rw [drBases] at ha
    obtain ⟨l, -, hl⟩ := List.mem_filterMap.1 ha
    rcases hw : litVal l with _ | w <;> rw [hw] at hl
    · cases hl
    · simp only [Option.map_some, Option.some.injEq] at hl
      subst hl
      rfl
  | .restriction t fs, hs, a, ha => by
    rw [drBases] at ha
    rw [drSupported] at hs
    by_cases hfs : fs = []
    · rw [if_pos hfs] at ha hs
      rcases hk : kindOf t with _ | k <;> rw [hk] at ha hs
      · simp at ha
      · rw [List.mem_singleton] at ha
        subst ha
        exact hs
    · rw [if_neg hfs] at ha hs
      rcases hk : kindOf t with _ | k <;> rw [hk] at ha hs
      · simp at ha
      · dsimp only at ha hs
        by_cases hfk : fltKind k = true
        · rw [if_pos hfk] at ha
          rcases hm : fs.mapM (floatBound k) with _ | bs <;> rw [hm] at ha
          · simp at ha
          · rw [List.mem_singleton] at ha
            subst ha
            exact hfk
        · rw [if_neg hfk] at ha
          rcases hm : fs.mapM facetBound with _ | bs <;> rw [hm] at ha
          · simp at ha
          · rw [List.mem_singleton] at ha
            subst ha
            simpa [hfk] using hs
termination_by dr => sizeOf dr
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ rs›; omega)

/-! ## The theory and the oracle -/

section Theory

variable {q : Nat}

/-- **The data theory of OWL data ranges at the map `owl2MapP pat`**: one
admissible pair per interpretation `dtype` of the datatypes outside the
map, up to a bijection with the values of the map. -/
def owlTheory (pat : String → String → Prop) (spec : Fin q → DataRange) : DataTheory (Fin q) :=
  fun V atom => ∃ (e : V ≃ Val) (dtype : IRI → Val → Prop),
    ∀ p v, atom p v ↔ (spec p).ext (owl2MapP pat) dtype (e v)

/-- The base atoms of all atoms. -/
def allBases (spec : Fin q → DataRange) : List BAtom :=
  (List.finRange q).flatMap fun p => drBases (spec p)

/-- The free datatypes of all atoms, without repetitions. -/
def allFrees (spec : Fin q → DataRange) : List IRI :=
  ((List.finRange q).flatMap fun p => drFrees (spec p)).dedup

/-- A free datatype under a reading of the list `frees`. -/
def freeVal (frees : List IRI) (g : Fin frees.length → Bool) (t : IRI) : Bool :=
  if h : frees.idxOf t < frees.length then g ⟨_, h⟩ else false

/-- Pre-parsed data range for fast repeated evaluation across cells. -/
inductive CExpr where
  | const (b : Bool)
  | atom (a : BAtom)
  | free (t : IRI)
  | not (e : CExpr)
  | and (es : List CExpr)
  | or (es : List CExpr)
  | oneOf (ws : List (Option (ValOf ℚ)))
deriving Repr

/-- Compile a data range into a `CExpr`, parsing literals, kinds and facet
bounds once. -/
def compileDR : DataRange → CExpr
  | .datatype t =>
    match kindOf t with
    | some k => .atom (.kind k)
    | none => .free t
  | .and rs => .and (rs.attach.map fun ⟨r, _⟩ => compileDR r)
  | .or rs => .or (rs.attach.map fun ⟨r, _⟩ => compileDR r)
  | .not r => .not (compileDR r)
  | .oneOf ls => .oneOf (ls.map litVal)
  | .restriction t fs =>
    if fs = [] then
      match kindOf t with
      | some k => .atom (.kind k)
      | none => .free t
    else
      match kindOf t with
      | some k =>
        if fltKind k then
          match fs.mapM (floatBound k) with
          | some bs => .atom (.fltB k bs)
          | none => .const false
        else
          match fs.mapM facetBound with
          | some bs => .atom (.numR k bs)
          | none => .const false
      | none => .const false
termination_by r => sizeOf r
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ rs›; omega)

mutual

/-- Evaluate a compiled data range. -/
def evalCE (bv : BAtom → Bool) (fv : IRI → Bool) : CExpr → Bool
  | .const b => b
  | .atom a => bv a
  | .free t => fv t
  | .not e => !evalCE bv fv e
  | .and es => evalCEAll bv fv es
  | .or es => evalCEAny bv fv es
  | .oneOf ws => ws.any fun
    | some w => bv (.lit w)
    | none => false

def evalCEAll (bv : BAtom → Bool) (fv : IRI → Bool) : List CExpr → Bool
  | [] => true
  | e :: es => evalCE bv fv e && evalCEAll bv fv es

def evalCEAny (bv : BAtom → Bool) (fv : IRI → Bool) : List CExpr → Bool
  | [] => false
  | e :: es => evalCE bv fv e || evalCEAny bv fv es

end

theorem evalCEAll_eq (bv : BAtom → Bool) (fv : IRI → Bool) :
    ∀ (es : List CExpr), evalCEAll bv fv es = es.all (evalCE bv fv)
  | [] => rfl
  | e :: es => by simp [evalCEAll, evalCEAll_eq bv fv es]

theorem evalCEAny_eq (bv : BAtom → Bool) (fv : IRI → Bool) :
    ∀ (es : List CExpr), evalCEAny bv fv es = es.any (evalCE bv fv)
  | [] => rfl
  | e :: es => by simp [evalCEAny, evalCEAny_eq bv fv es]

theorem evalCE_compileDR (bv : BAtom → Bool) (fv : IRI → Bool) :
    ∀ (dr : DataRange), evalCE bv fv (compileDR dr) = drEval bv fv dr
  | .datatype t => by
    rw [compileDR, drEval]
    cases kindOf t <;> rfl
  | .and rs => by
    have ih : ∀ r ∈ rs, evalCE bv fv (compileDR r) = drEval bv fv r :=
      fun r _ => evalCE_compileDR bv fv r
    rw [compileDR, evalCE, evalCEAll_eq, drEval]
    apply Bool.eq_iff_iff.2
    simp only [List.all_eq_true, List.mem_map, List.mem_attach, true_and, Subtype.exists,
      true_implies, Subtype.forall]
    constructor
    · intro h r hr
      rw [← ih r hr]
      exact h (compileDR r) ⟨r, hr, rfl⟩
    · rintro h _ ⟨r, hr, rfl⟩
      rw [ih r hr]
      exact h r hr
  | .or rs => by
    have ih : ∀ r ∈ rs, evalCE bv fv (compileDR r) = drEval bv fv r :=
      fun r _ => evalCE_compileDR bv fv r
    rw [compileDR, evalCE, evalCEAny_eq, drEval]
    apply Bool.eq_iff_iff.2
    simp only [List.any_eq_true, List.mem_map, List.mem_attach, true_and, Subtype.exists]
    constructor
    · rintro ⟨_, ⟨r, hr, rfl⟩, h⟩
      rw [ih r hr] at h
      exact ⟨r, hr, h⟩
    · rintro ⟨r, hr, h⟩
      refine ⟨compileDR r, ⟨r, hr, rfl⟩, ?_⟩
      rwa [ih r hr]
  | .not r => by
    rw [compileDR, evalCE, drEval, evalCE_compileDR bv fv r]
  | .oneOf ls => by
    rw [compileDR, evalCE, drEval, List.any_map]
    rfl
  | .restriction t fs => by
    rw [compileDR, drEval]
    split_ifs with hfs
    · cases kindOf t <;> rfl
    · cases hk : kindOf t with
      | none => rfl
      | some k =>
        dsimp only
        split_ifs with hfk
        · cases fs.mapM (floatBound k) <;> rfl
        · cases fs.mapM facetBound <;> rfl
termination_by dr => sizeOf dr
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ rs›; omega)

/-- The atoms on a cell under a reading of the free datatypes. -/
def owlE (spec : Fin q → DataRange) : Fin q → Cell → (Fin (allFrees spec).length → Bool) → Bool :=
  fun p c g => drEval (fun a => evalCell a c) (freeVal (allFrees spec) g) (spec p)

/-- `owlE` with the free-datatype list and compiled data ranges given. -/
def owlEWith (frees : List IRI) (arr : Array CExpr) (q : Nat) (h : arr.size = q)
    (p : Fin q) (c : Cell) (g : Fin frees.length → Bool) : Bool :=
  evalCE (fun a => evalCell a c) (freeVal frees g) (arr[p.val]'(by rw [h]; exact p.isLt))

/-- `owlE` with `allFrees spec` and `compileDR (spec p)` computed once. -/
def owlEF (spec : Fin q → DataRange) : Fin q → Cell → (Fin (allFrees spec).length → Bool) → Bool :=
  let arr : Array CExpr := Array.ofFn fun p => compileDR (spec p)
  owlEWith (allFrees spec) arr q (Array.size_ofFn ..)

@[csimp] theorem owlE_eq_F : @owlE = @owlEF := by
  funext q spec p c g
  simp only [owlEF, owlEWith, Array.getElem_ofFn, evalCE_compileDR, owlE]

/-- **The oracle of the map.** -/
def owlCard (spec : Fin q → DataRange) : Finset (Fin q) → Option Nat :=
  cellCard (cellsOf (allBases spec)) (cellSize (allBases spec)) (owlE spec)

/-- `owlCard` with the cells computed once (for the executable). -/
def owlCardC (spec : Fin q → DataRange) : Finset (Fin q) → Option Nat :=
  let as := allBases spec
  let cs := cellsOf as
  fun τ => cellCard cs (cellSize as) (owlE spec) τ

theorem owlCardC_eq (spec : Fin q → DataRange) : owlCardC spec = owlCard spec := rfl

/-- Every atom is supported, and the free datatypes pass `freeCheck`. -/
def owlCheck (spec : Fin q → DataRange) : Bool :=
  (List.finRange q).all (fun p => drSupported (spec p)) &&
    freeCheck (cellsOf (allBases spec)) (cellSize (allBases spec)) (owlE spec)

theorem freeVal_mem {frees : List IRI} {t : IRI} (ht : t ∈ frees)
    (g : Fin frees.length → Bool) :
    freeVal frees g t = g ⟨frees.idxOf t, List.idxOf_lt_length_of_mem ht⟩ := by
  unfold freeVal
  rw [dif_pos (List.idxOf_lt_length_of_mem ht)]

theorem owlTheory_iff (pat : String → String → Prop) {spec : Fin q → DataRange}
    (hs : ∀ p, drSupported (spec p) = true) (V : Type) (atom : Fin q → V → Prop) :
    owlTheory pat spec V atom ↔ cellTheory (cellOf (allBases spec)) (owlE spec) V atom := by
  classical
  let as := allBases spec
  let frees := allFrees spec
  have hnd : frees.Nodup := List.nodup_dedup _
  have hfm : ∀ p, ∀ t ∈ drFrees (spec p), t ∈ frees := fun p t ht =>
    List.mem_dedup.2 (List.mem_flatMap.2 ⟨p, List.mem_finRange _, ht⟩)
  have hbm : ∀ p, ∀ a ∈ drBases (spec p), a ∈ as := fun p a ha =>
    List.mem_flatMap.2 ⟨p, List.mem_finRange _, ha⟩
  have hb : ∀ p (w : Val), ∀ a ∈ drBases (spec p), a.sem w ↔ evalCell a (cellOf as w) = true :=
    fun p w a ha => evalCell_correct (hbm p a ha) (supported_of_drBases _ (hs p) a ha) w
  constructor
  · rintro ⟨e, dtype, h⟩
    refine ⟨e, fun j w => decide (dtype (frees.get j) w), fun p v => ?_⟩
    rw [h p v]
    refine ext_iff_drEval pat dtype (e v) _ _ (spec p) (hs p) (hb p (e v)) fun t ht => ?_
    rw [freeVal_mem (hfm p t ht)]
    simp only [List.get_eq_getElem, List.getElem_idxOf, decide_eq_true_eq]
  · rintro ⟨e, fr, h⟩
    refine ⟨e, fun t w => ∃ j, frees.get j = t ∧ fr j w = true, fun p v => ?_⟩
    rw [h p v]
    refine (ext_iff_drEval pat _ (e v) _ _ (spec p) (hs p) (hb p (e v)) fun t ht => ?_).symm
    rw [freeVal_mem (hfm p t ht)]
    constructor
    · rintro ⟨j, hj, hfr⟩
      have : j = ⟨frees.idxOf t, List.idxOf_lt_length_of_mem (hfm p t ht)⟩ := by
        apply Fin.ext
        simp only
        rw [← hj, List.get_eq_getElem, hnd.idxOf_getElem]
      rw [← this]
      exact hfr
    · intro hfr
      exact ⟨_, by simp [List.getElem_idxOf], hfr⟩

/-- **The oracle of the OWL 2 datatype map.** For data atoms that pass
`owlCheck`, `owlCard` satisfies `OracleSpec` for the theory of the map,
for every reading `pat` of `xsd:pattern`. -/
theorem oracleSpec_owl (pat : String → String → Prop) {spec : Fin q → DataRange}
    (h : owlCheck spec = true) : OracleSpec (owlTheory pat spec) (owlCard spec) := by
  rw [owlCheck, Bool.and_eq_true, List.all_eq_true] at h
  have hs : ∀ p, drSupported (spec p) = true := fun p => h.1 p (List.mem_finRange _)
  have heq : owlTheory pat spec = cellTheory (cellOf (allBases spec)) (owlE spec) := by
    funext V atom
    exact propext (owlTheory_iff pat hs V atom)
  rw [heq]
  exact oracleSpec_cell (cellSpec _) (freeOK_of_check h.2)

end Theory

end ContextCalculus.OWL.Datatypes

#print axioms ContextCalculus.OWL.Datatypes.ext_iff_drEval
#print axioms ContextCalculus.OWL.Datatypes.oracleSpec_owl
#print axioms ContextCalculus.OWL.Datatypes.owlE_eq_F
