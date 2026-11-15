import ContextCalculus.OWLFrontend.EdgeStrengthen
import ContextCalculus.SRIQN.HintModel

/-!
# The global witness row (stage H2, item 5)

`docs/V1.7.0-PLAN.md`, section 20. One hint `H` for the base ontology `O`
(after the encodings of the chain route, no row axioms added) certifies
every non-subsumption, non-type and non-sameness that can be read off the
types of its core elements:

* `wTab O req hint`: the route of `sroiq-hint` with the requested classes
  `req` given to the translation; `some W` when the hint checks. `W` holds
  the core types (`W.ty`), the requested classes with their concept index
  (`W.cls`) and the named individuals with the index of their nominal
  class (`W.inds`), each entry validated against the translation tables.
* `hintWitness_sound`: from `wTab O req hint = some W`, `O` is consistent,
  and for core elements `w`, `v`:
  - `(A, iA), (B, iB) ∈ W.cls`, `iA ∈ W.ty w`, `iB ∉ W.ty w`: `O ⊭ A ⊑ B`;
  - `(a, ia) ∈ W.inds`, `(C, iC) ∈ W.cls`, `ia ∈ W.ty w`, `iC ∉ W.ty w`:
    `O ⊭ C(a)`;
  - `(a, ia), (b, ib) ∈ W.inds`, `ia ∈ W.ty w`, `ib ∈ W.ty v`, `w ≠ v`:
    `O ⊭ SameIndividual(a b)`.

The model is the forest of the realisation (`SRIQN.forest_of_check`),
carried down through the data reduction, the transitivity encoding
(`SRIQN.hintPartsS_model`), chain elimination (`chainDown`), the
translation with the class correspondence of the requested names
(`downW`), the role axioms (`model_roleOff`), the renaming of anonymous
individuals, disjoint unions and the strengthening of asymmetric and
disjoint properties. A core element is in a requested class exactly when
the class's index is in its type.

Scope: the chain route (no `ObjectHasSelf`, no irreflexive property, no
counting over a reflexive property), no `HasKey`, no datatype definition.
Witnesses are core elements (anonymous ones allowed); tree records are not
witnesses. Role rows are not covered: an edge of the model between two
core elements can come from a chain or a transitive role through tree
nodes, so the absence of a label in the hint does not refute a role
assertion.
-/

namespace ContextCalculus.OWLFrontend

open ContextCalculus.OWL ContextCalculus.OWL.Datatypes SHIQD SHOIQ
open ContextCalculus.SRIQN (dbase dnoms NomAt)

/-! ## Chain elimination, with the concepts -/

theorem chainDown {n m p q : Nat} {Dom V : Type}
    {X : SRIQN.DOntology (Fin n) (Fin m) (Fin p) (Fin q)} (hC : SROIQ.Proc.CondCD X)
    {atom : Fin q → V → Prop}
    {J : ContextCalculus.SRIQD.DInterp Dom V (Fin (n + SROIQ.Proc.kCD X)) (Fin m) (Fin p)}
    (hJ : ContextCalculus.SRIQD.models atom J (dbase (SROIQ.Proc.encChainDN X)))
    (hn : ∀ a ∈ dnoms (SROIQ.Proc.encChainDN X), NomAt J.toInterp a) :
    ∃ J' : ContextCalculus.SRIQD.DInterp Dom V (Fin n) (Fin m) (Fin p),
      ContextCalculus.SRIQD.models atom J' (dbase X) ∧ (∀ a ∈ dnoms X, NomAt J'.toInterp a) ∧
      (∀ a y, J'.c a y ↔ J.c (Fin.castAdd _ a) y) ∧
      ∀ R x y, SROIQ.SimpleC (ContextCalculus.SRIQD.objPart (dbase X)) R →
        (J'.rt R x y ↔ J.rt R x y) := by
  rw [SROIQ.Proc.dbase_encChainDN] at hJ
  have hJo : SRIQ.models J.toInterp (SROIQ.Proc.encChain (ContextCalculus.SRIQD.objPart (dbase X))) := by
    have := (ContextCalculus.SRIQD.models_iff.1 hJ).1
    rwa [SROIQ.Proc.objPart_encChainQD] at this
  refine ⟨_, SROIQ.Proc.models_encChainQD_down hC hJ, fun a ha => ?_, fun a y => Iff.rfl,
    fun R x y hs => SROIQ.Proc.downC_rt_simple hJo hs x y⟩
  exact hn (Fin.castAdd _ a) (by rw [SROIQ.Proc.dnoms_encChainDN]; exact List.mem_map_of_mem ha)

/-! ## The translation down, with classes and individuals -/

variable {O : Ontology} {requested : List IRI} {T : SRIQDKBTranslation}

/-- **Down, with the requested classes and the named individuals.** -/
theorem downW (pat : String → String → Prop) (h : translateSHOIQD O requested = some T)
    {Dom V : Type} [Nonempty Dom] {atom : Fin T.tab.length → V → Prop}
    (hΘ : owlTheory pat (spec T.tab) V atom)
    (K : ContextCalculus.SRIQD.DInterp Dom V (Fin T.obj.conceptCount) (Fin T.obj.roleCount)
      (Fin T.dps.length))
    (hK : ContextCalculus.SRIQD.models atom K (dbase (dosn T (nomNames O requested))))
    (hn : ∀ a ∈ dnoms (dosn T (nomNames O requested)), NomAt K.toInterp a) :
    ∃ I : Interp (owl2MapP pat) Dom, OWL.Model O I ∧ RoleCorr T K.toInterp I ∧
      (∀ (i : Nat) (hi : i < T.obj.named.length), T.obj.named[i] ∈ requested → ∀ y,
        K.c ⟨i, Nat.lt_of_lt_of_le hi T.obj.hnamed⟩ y ↔ I.cls T.obj.named[i] y) ∧
      ∀ a ∈ O.individualNames, ∀ (i : Nat) (hi : i < T.obj.named.length),
        T.obj.named[i] = nmOf O requested a → ∀ y,
        K.c ⟨i, Nat.lt_of_lt_of_le hi T.obj.hnamed⟩ y ↔ y = I.ind (.named a) := by
  obtain ⟨hO, hT⟩ := translateSHOIQD_spec h
  obtain ⟨x0⟩ := (inferInstance : Nonempty Dom)
  rw [dbase_dosn] at hK
  obtain ⟨I0, hI0, hc, hr⟩ := (translateSRIQDKB_mapsR pat hT).2 Dom V atom hΘ K (fun _ => x0) hK
    (by rw [translateSHOIQD_abox h]; intro _ h'; simp at h')
  have hcs : ∀ s ∈ requested ++ nomNames O requested, ∀ (ix : Fin T.obj.conceptCount),
      nameIx T.obj s = some ix → ∀ y, I0.cls s y ↔ K.c ix y := by
    intro s hs ix hix y
    obtain ⟨hi, he⟩ := nameIx_spec hix
    have := hc ix.val hi (he ▸ hs) y
    rw [he] at this
    exact this
  have hmem : ∀ a ∈ O.individualNames, nmOf O requested a ∈ requested ++ nomNames O requested :=
    fun a ha => List.mem_append_right _ (List.mem_map_of_mem ha)
  have hsing : ∀ a ∈ O.individualNames, ∃ x, ∀ y, I0.cls (nmOf O requested a) y ↔ y = x := by
    intro a ha
    obtain ⟨ix, hix⟩ := nameIx_some (named_obj h (hmem a ha))
    obtain ⟨z, hz⟩ := hn ix (nomD_mem h ha hix)
    exact ⟨z, fun y => (hcs _ (hmem a ha) ix hix y).trans (hz y)⟩
  obtain ⟨hM, hcls⟩ := nomOntD_down hO requested hI0 hsing
  refine ⟨downI O requested I0, hM, fun r hb k hk R hfin x y => ?_, fun i hi hs y => ?_,
    fun a ha i hi he y => ?_⟩
  · have := hr r hb k hk R hfin x y
    cases r <;> exact this.symm
  · rw [hcls]
    exact (hc i hi (List.mem_append_left _ hs) y).symm
  · have h1 := hc i hi (by rw [he]; exact hmem a ha) y
    rw [he] at h1
    rw [← h1]
    exact downI_nom (hsing a ha) y

/-! ## The witness tables -/

/-- The tables a witness hint is read with: the core types and the
validated indices of the requested classes and of the named individuals. -/
structure WTab where
  N : Nat
  k : Nat
  ty : Fin k → Finset (Fin N)
  cls : List (IRI × Fin N)
  inds : List (IRI × Fin N)
  /-- the role terms and the labels of the core (stage H2, role rows) -/
  M : Nat := 0
  lab : Fin k → Fin k → Finset (SRI.RoleT (Fin M)) := fun _ _ => ∅
  /-- named properties with their role term, each a simple role of the normal form -/
  props : List (ObjProp × SRI.RoleT (Fin M)) := []
  /-- stage H4, the role rows over the core: `ob` the object part of the
  chain route before chain elimination (its role inclusions give the
  languages of the roles) -/
  n2 : Nat := 0
  ob : SRIQ.Ontology (Fin n2) (Fin M) := []
  /-- the edges of each core element (both directions, as `HintS.adj`) -/
  adj : Fin k → List (Fin k × Finset (SRI.RoleT (Fin M))) := fun _ => []
  /-- every named property and its inverse, with their role terms -/
  rprops : List (ObjProp × SRI.RoleT (Fin M)) := []
  /-- the hint has no `kid` lines: every element of the model is a core element -/
  flat : Bool := false
  /-- the tables come from the chain route -/
  chainR : Bool := false

/-- The first index of each name (a table for the lookups below; every
entry is validated against `T.obj.named`). -/
def namedMap (named : List IRI) : Std.HashMap IRI Nat :=
  named.zipIdx.foldl (fun mp p => mp.insertIfNew p.1 p.2) {}

/-- A name's index, validated: `named[i] = s`. -/
def ixOf (T : SRIQDKBTranslation) (arr : Array IRI) (mp : Std.HashMap IRI Nat) (s : IRI) :
    Option (Fin T.obj.conceptCount) :=
  match mp.get? s with
  | none => none
  | some i =>
    if h : i < T.obj.named.length then
      if T.obj.named[i] = s then some ⟨i, Nat.lt_of_lt_of_le h T.obj.hnamed⟩ else none
    else none

theorem ixOf_spec {T : SRIQDKBTranslation} {arr : Array IRI} {mp : Std.HashMap IRI Nat} {s : IRI}
    {x : Fin T.obj.conceptCount} (h : ixOf T arr mp s = some x) :
    ∃ hi : x.val < T.obj.named.length, T.obj.named[x.val] = s ∧
      x = ⟨x.val, Nat.lt_of_lt_of_le hi T.obj.hnamed⟩ := by
  unfold ixOf at h
  split at h
  · cases h
  · split_ifs at h with h1 h2
    cases h
    exact ⟨h1, h2, rfl⟩

/-- `ixOf` through the array of the names (stage H4: `ixOf` indexes the
list of names, linear in the index). -/
def ixOfA (T : SRIQDKBTranslation) (arr : Array IRI) (harr : arr = T.obj.named.toArray)
    (mp : Std.HashMap IRI Nat) (s : IRI) : Option (Fin T.obj.conceptCount) :=
  match mp.get? s with
  | none => none
  | some i =>
    if h : i < arr.size then
      if arr[i] = s then
        some ⟨i, Nat.lt_of_lt_of_le (by rw [harr, List.size_toArray] at h; exact h) T.obj.hnamed⟩
      else none
    else none

theorem ixOfA_spec {T : SRIQDKBTranslation} {arr : Array IRI} {harr : arr = T.obj.named.toArray}
    {mp : Std.HashMap IRI Nat} {s : IRI} {x : Fin T.obj.conceptCount}
    (h : ixOfA T arr harr mp s = some x) :
    ∃ hi : x.val < T.obj.named.length, T.obj.named[x.val] = s ∧
      x = ⟨x.val, Nat.lt_of_lt_of_le hi T.obj.hnamed⟩ := by
  subst harr
  unfold ixOfA at h
  split at h
  · cases h
  · split_ifs at h with h1 h2
    cases h
    rw [List.size_toArray] at h1
    exact ⟨h1, by simpa using h2, rfl⟩

/-- The named properties of a translation whose role term is simple in the
normal form `B` (checked by `simpleB`). -/
def propsOf (T : SRIQDKBTranslation) (simpleB : SRI.RoleT (Fin T.obj.roleCount) → Bool) :
    List (ObjProp × SRI.RoleT (Fin T.obj.roleCount)) :=
  T.obj.rnames.filterMap fun e =>
    match SRIT.finRT T.obj.roleCount (SRIT.mkRT (.named e.1) e.2) with
    | some R => if simpleB R then some (.named e.1, R) else none
    | none => none

theorem mem_propsOf {T : SRIQDKBTranslation} {simpleB : SRI.RoleT (Fin T.obj.roleCount) → Bool}
    {r : ObjProp} {R : SRI.RoleT (Fin T.obj.roleCount)} (h : (r, R) ∈ propsOf T simpleB) :
    r.isBasic = true ∧ simpleB R = true ∧ ∃ k, (EL.propIRI r, k) ∈ T.obj.rnames ∧
      SRIT.finRT T.obj.roleCount (SRIT.mkRT r k) = some R := by
  obtain ⟨e, he, hf⟩ := List.mem_filterMap.1 h
  split at hf
  next R' hR' =>
    split_ifs at hf with hs
    simp only [Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    exact ⟨rfl, hs, e.2, he, hR'⟩
  next => cases hf

/-- Every named property of a translation and its inverse, with their
role terms (stage H4). -/
def rpropsOf (T : SRIQDKBTranslation) : List (ObjProp × SRI.RoleT (Fin T.obj.roleCount)) :=
  T.obj.rnames.flatMap fun e => [ObjProp.named e.1, ObjProp.inv e.1].filterMap fun r =>
    (SRIT.finRT T.obj.roleCount (SRIT.mkRT r e.2)).map fun R => (r, R)

theorem mem_rpropsOf {T : SRIQDKBTranslation} {r : ObjProp} {R : SRI.RoleT (Fin T.obj.roleCount)}
    (h : (r, R) ∈ rpropsOf T) :
    r.isBasic = true ∧ ∃ k, (EL.propIRI r, k) ∈ T.obj.rnames ∧
      SRIT.finRT T.obj.roleCount (SRIT.mkRT r k) = some R := by
  obtain ⟨e, he, hm⟩ := List.mem_flatMap.1 h
  obtain ⟨r', hr', hf⟩ := List.mem_filterMap.1 hm
  obtain ⟨R', hR', hp⟩ := Option.map_eq_some_iff.1 hf
  simp only [Prod.mk.injEq] at hp
  obtain ⟨rfl, rfl⟩ := hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl
  · exact ⟨rfl, e.2, he, hR'⟩
  · exact ⟨rfl, e.2, he, hR'⟩

/-- The chain route with the requested classes `req`, on an ontology
without datatype definitions, keys or anonymous individuals: `some W`
when the hint checks. -/
def wTabCore (X : Ontology) (req : List IRI) (hint : RawHint) : Option WTab :=
  if X.isSROIQDKB then
    match translateSHOIQD (roleOff X) req with
    | none => none
    | some T =>
      match roleCls T X with
      | none => none
      | some E =>
        let L := nomNames (roleOff X) req
        if sroiqHOK T L E then
          let sp := spec T.tab
          let as := allBases sp
          let cs := cellsOf as
          let D := encC T L E
          -- the cells to split as a table (`lookSplit_eq`)
          let spT := SRIQN.HF.splitTab cs (cellSize as) (sroiqBound T L E) (owlE sp)
          match hint.toHintS _ _ with
          | none => none
          | some h =>
            if SRIQN.HF.hintPartsP D cs (cellSize as)
                (SRIQN.HF.lookSplit spT
                  (ContextCalculus.SRIQD.splitCell cs (cellSize as) (sroiqBound T L E) (owlE sp)))
                (owlE sp) h then
              let mp := namedMap T.obj.named
              let arr := T.obj.named.toArray
              let emb := fun x : Fin T.obj.conceptCount =>
                Fin.castAdd (SRIQN.Proc.encKD D) (Fin.castAdd (SROIQ.Proc.kCD (dosnC T L E)) x)
              let base := nomBase (roleOff X) req
              some { N := _, k := h.k, ty := h.tyF
                     cls := req.filterMap fun s => (ixOfA T arr rfl mp s).map fun x => (s, emb x)
                     inds := (roleOff X).individualNames.zipIdx.filterMap fun p =>
                       (ixOfA T arr rfl mp (nomName base p.2)).map fun x => (p.1, emb x)
                     M := T.obj.roleCount, lab := h.toN.lab
                     props := propsOf T fun R =>
                       SROIQ.Proc.selfSimpleB (objC T L E) [.selfL R []]
                     n2 := T.obj.conceptCount, ob := objC T L E
                     adj := fun b => ContextCalculus.SRIQ.Fast.getL h.adj b.val
                     rprops := rpropsOf T, flat := h.kids.isEmpty, chainR := true }
            else none
        else none
  else none

/-- The facts the witness rows read. -/
structure WFacts (pat : String → String → Prop) (X : Ontology) (W : WTab) : Prop where
  model : ∃ (Dom : Type) (_ : Nonempty Dom) (I : Interp (owl2MapP pat) Dom) (f : Fin W.k → Dom),
    OWL.Model X I ∧ Function.Injective f ∧
    (∀ s x, (s, x) ∈ W.cls → ∀ w, I.cls s (f w) ↔ x ∈ W.ty w) ∧
    (∀ a x, (a, x) ∈ W.inds → a ∈ (roleOff X).individualNames ∧ ∀ w, f w = I.ind (.named a) ↔ x ∈ W.ty w) ∧
    (∀ r R, (r, R) ∈ W.props → ∀ w v, (I.prop r (f w) (f v) ↔ R ∈ W.lab w v))

theorem nmOf_eq {X : Ontology} {req : List IRI} {a : IRI} {j : Nat}
    (h : (a, j) ∈ X.individualNames.zipIdx) :
    a ∈ X.individualNames ∧ nmOf X req a = nomName (nomBase X req) j := by
  rw [List.mem_zipIdx_iff_getElem?] at h
  have hj : j < X.individualNames.length := by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at h
    cases h
  rw [List.getElem?_eq_getElem hj, Option.some.injEq] at h
  have h' : X.individualNames[j] = a := h
  refine ⟨h' ▸ List.getElem_mem hj, ?_⟩
  unfold nmOf
  congr 1
  rw [← h']
  exact (Ontology.namesBy_nodup _ _).idxOf_getElem j hj

/-- **The model of an accepted witness hint, with the tables.** -/
theorem wTabCore_facts (pat : String → String → Prop) {X : Ontology} {req : List IRI}
    {hint : RawHint} {W : WTab} (hw : wTabCore X req hint = some W) : WFacts pat X W := by
  unfold wTabCore at hw
  split_ifs at hw with hX
  split at hw
  · cases hw
  next T hT =>
    split at hw
    · cases hw
    next E hE =>
      dsimp only at hw
      split_ifs at hw with hok
      split at hw
      · cases hw
      next h hh =>
        split_ifs at hw with hp
        rw [SRIQN.HF.lookSplit_eq] at hp
        simp only [Option.some.injEq] at hw
        subst hw
        simp only [sroiqHOK, Bool.and_eq_true] at hok
        obtain ⟨⟨-, h1⟩, h3⟩ := hok
        obtain ⟨Dom, V, hD, atom, hΘ, J, f, hJ, hn, hinj, hty, hlab⟩ := SRIQN.hintPartsP_model
          (cellSpec _) (le_refl _) ContextCalculus.SRIQD.splitCell_ok.1
          ContextCalculus.SRIQD.splitCell_ok.2 (SROIQ.Proc.isSHIQD_encChainDN _) (le_refl _) hp
        have hAs : SRI.IsALCHI (SRIQ.sriPart (ContextCalculus.SRIQD.objPart (dbase (encC T (nomNames (roleOff X) req) E)))) := by
          refine SRIQ.isALCHI_sriPart ?_
          rw [SROIQ.Proc.dbase_encChainDN, SROIQ.Proc.objPart_encChainQD]
          exact SROIQ.Proc.encChain_isALCHIQ _
        rw [← owlTheory_eq pat h3] at hΘ
        obtain ⟨K, hK, hKn, hKc, hKr⟩ := chainDown (SROIQ.Proc.condC_of_condB h1) hJ hn
        rw [dbase_dosnC, models_append_obj] at hK
        rw [dnoms_dosnC] at hKn
        haveI := hD
        obtain ⟨I, hI, hC, hcl, hind⟩ := downW pat hT hΘ K (by rw [dbase_dosn]; exact hK.1) hKn
        have hM : OWL.Model X I := (model_roleOff hX I).2 ⟨hI, (sat_roleCls hC hE).1 hK.2⟩
        refine ⟨⟨Dom, hD, I, f, hM, hinj, fun s x hs w => ?_, fun a x ha => ?_, fun r R hr w v => ?_⟩⟩
        · obtain ⟨s', hs', hsx⟩ := List.mem_filterMap.1 hs
          obtain ⟨y, hy, hyx⟩ := Option.map_eq_some_iff.1 hsx
          simp only [Prod.mk.injEq] at hyx
          obtain ⟨rfl, rfl⟩ := hyx
          obtain ⟨hi, hnm, hyv⟩ := ixOfA_spec hy
          rw [← hty, ← hKc, hyv]
          have := hcl y.val hi (hnm ▸ hs') (f w)
          rw [hnm] at this
          exact this.symm
        · obtain ⟨⟨a', j⟩, hp', hax⟩ := List.mem_filterMap.1 ha
          obtain ⟨y, hy, hyx⟩ := Option.map_eq_some_iff.1 hax
          simp only [Prod.mk.injEq] at hyx
          obtain ⟨rfl, rfl⟩ := hyx
          obtain ⟨hi, hnm, hyv⟩ := ixOfA_spec hy
          obtain ⟨hmem, hnmOf⟩ := nmOf_eq (req := req) hp'
          refine ⟨hmem, fun w => ?_⟩
          rw [← hty, ← hKc, hyv]
          exact (hind _ hmem y.val hi (hnm.trans hnmOf.symm) (f w)).symm
        · obtain ⟨hb, hs, k, hk, hR⟩ := mem_propsOf hr
          have hsim : SROIQ.SimpleC (ContextCalculus.SRIQD.objPart (dbase (dosnC T (nomNames (roleOff X) req) E))) R :=
            selfSimple_of (SC := [.selfL R []]) hs R [] List.mem_cons_self
          exact ((hC r hb k hk R hR (f w) (f v)).symm.trans (hKr R _ _ hsim)).trans (hlab hAs R w v)

/-! ## The prepared ontology -/

/-- The strengthening of asymmetric and disjoint properties, when there are any. -/
def edgeP (O : Ontology) : Ontology := if hasEdgeAx O then edgeOff O else O

theorem model_of_edgeP {O : Ontology} {DM : DatatypeMap} {Dom : Type} {I : Interp DM Dom}
    (h : OWL.Model (edgeP O) I) : OWL.Model O I := by
  unfold edgeP at h
  split_ifs at h
  · exact model_of_edgeOff h
  · exact h

theorem named_edgeP (O : Ontology) : (edgeP O).namedIndividuals = O.namedIndividuals := by
  unfold edgeP
  split_ifs
  · exact named_edgeOff O
  · rfl

/-- The ontology before the renaming of anonymous individuals. -/
def wPre (O : Ontology) : Ontology := duOff (edgeP O)

/-- The ontology the witness route checks: the strengthening of asymmetric
and disjoint properties, disjoint unions rewritten, anonymous individuals
renamed. -/
def wPrep (O : Ontology) : Ontology := anonOff [] (wPre O)

/-- **The witness route**: `none` outside its scope or when the hint does
not check. -/
def wTab (O : Ontology) (req : List IRI) (hint : RawHint) : Option WTab :=
  if (wPre O).noKey && (splitDef O.axioms).isNone && (selfPairs (wPrep O)).isEmpty then
    let H := Std.HashSet.ofList O.namedIndividuals
    (wTabCore (wPrep O) req hint).map fun W => { W with inds := W.inds.filter fun p => H.contains p.1 }
  else none

theorem model_of_prep {O : Ontology} (hk : (wPre O).noKey = true) {Dom : Type} {DM : DatatypeMap}
    {J : Interp DM Dom} (hJ : OWL.Model (wPrep O) J) :
    OWL.Model O (J.indMap (anonG [] (wPre O))) := by
  have h2 := (model_anonOff (W := []) hk (J.indMap (anonG [] (wPre O)))).1 (by
    rw [indMap_indMap J (anonG_inv [] _)]; exact hJ)
  exact model_of_edgeP ((model_duOff _ _).1 h2)

theorem named_prep (O : Ontology) (a : IRI) :
    a ∈ (wPre O).namedIndividuals ↔ a ∈ O.namedIndividuals := by
  unfold wPre
  rw [mem_namedIndividuals_duOff, named_edgeP]

/-- **The model of an accepted witness hint**: a model of `O` with the core
inside it, the requested classes and the named individuals read off the
core types. -/
theorem wTab_model (pat : String → String → Prop) {O : Ontology} {req : List IRI}
    {hint : RawHint} {W : WTab} (hw : wTab O req hint = some W) :
    ∃ (Dom : Type) (_ : Nonempty Dom) (I : Interp (owl2MapP pat) Dom) (f : Fin W.k → Dom),
      OWL.Model O I ∧ Function.Injective f ∧
      (∀ s x, (s, x) ∈ W.cls → ∀ w, I.cls s (f w) ↔ x ∈ W.ty w) ∧
      (∀ a x, (a, x) ∈ W.inds → ∀ w, f w = I.ind (.named a) ↔ x ∈ W.ty w) := by
  unfold wTab at hw
  split_ifs at hw with hs
  simp only [Bool.and_eq_true] at hs
  obtain ⟨⟨hk, -⟩, -⟩ := hs
  obtain ⟨W0, hW0, rfl⟩ := Option.map_eq_some_iff.1 hw
  obtain ⟨Dom, hD, J, f, hJ, hinj, hcls, hind, -⟩ := (wTabCore_facts pat hW0).model
  haveI := hD
  set g := anonG [] (wPre O)
  have hM : OWL.Model O (J.indMap g) := model_of_prep hk hJ
  have hgcls : (J.indMap g).cls = J.cls := by cases J; rfl
  have hgind : ∀ a ∈ O.namedIndividuals, (J.indMap g).ind (.named a) = J.ind (.named a) := by
    intro a ha
    have hfix : g (.named a) = .named a := anonF_short (anonBase_long (by
      simp only [List.nil_append]; exact (named_prep O a).2 ha))
    cases J
    simp only [Interp.indMap, hfix]
  refine ⟨Dom, hD, J.indMap g, f, hM, hinj, fun s x hs w => ?_, fun a x hax w => ?_⟩
  · rw [hgcls]; exact hcls s x hs w
  · obtain ⟨hax, hc⟩ := List.mem_filter.1 hax
    have ha : a ∈ O.namedIndividuals := by
      simpa [Std.HashSet.contains_ofList] using hc
    rw [hgind a ha]
    exact (hind a x hax).2 w

/-- **Soundness of the global witness row.** -/
theorem hintWitness_sound (pat : String → String → Prop) {O : Ontology} {req : List IRI}
    {hint : RawHint} {W : WTab} (hw : wTab O req hint = some W) :
    ConsistentAt (owl2MapP pat) O ∧
    (∀ (A B : IRI) (iA iB : Fin W.N) (w : Fin W.k), (A, iA) ∈ W.cls → (B, iB) ∈ W.cls →
      iA ∈ W.ty w → iB ∉ W.ty w → ¬ EntailsSubAt (owl2MapP pat) O A B) ∧
    (∀ (a C : IRI) (ia iC : Fin W.N) (w : Fin W.k), (a, ia) ∈ W.inds → (C, iC) ∈ W.cls →
      ia ∈ W.ty w → iC ∉ W.ty w →
      ¬ EntailsAt (owl2MapP pat) O (.classAssertion (.cls C) (.named a))) ∧
    (∀ (a b : IRI) (ia ib : Fin W.N) (w v : Fin W.k), (a, ia) ∈ W.inds → (b, ib) ∈ W.inds →
      ia ∈ W.ty w → ib ∈ W.ty v → w ≠ v →
      ¬ EntailsAt (owl2MapP pat) O (.sameIndividual [.named a, .named b])) := by
  unfold wTab at hw
  split_ifs at hw with hs
  simp only [Bool.and_eq_true] at hs
  obtain ⟨⟨hk, -⟩, -⟩ := hs
  obtain ⟨W0, hW0, rfl⟩ := Option.map_eq_some_iff.1 hw
  obtain ⟨Dom, hD, J, f, hJ, hinj, hcls, hind, -⟩ := (wTabCore_facts pat hW0).model
  haveI := hD
  set g := anonG [] (wPre O)
  have hM : OWL.Model O (J.indMap g) := model_of_prep hk hJ
  have hgcls : (J.indMap g).cls = J.cls := by cases J; rfl
  have hgind : ∀ a ∈ O.namedIndividuals, (J.indMap g).ind (.named a) = J.ind (.named a) := by
    intro a ha
    have hfix : g (.named a) = .named a := anonF_short (anonBase_long (by
      simp only [List.nil_append]; exact (named_prep O a).2 ha))
    cases J
    simp only [Interp.indMap, hfix]
  have hindO : ∀ a x, (a, x) ∈ (W0.inds.filter fun p => (Std.HashSet.ofList O.namedIndividuals).contains p.1) →
      ∀ w, f w = (J.indMap g).ind (.named a) ↔ x ∈ W0.ty w := by
    intro a x hax w
    obtain ⟨hax, hc⟩ := List.mem_filter.1 hax
    have ha : a ∈ O.namedIndividuals := by
      simpa [Std.HashSet.contains_ofList] using hc
    rw [hgind a ha]
    exact (hind a x hax).2 w
  refine ⟨⟨Dom, hD, _, hM⟩, ?_, ?_, ?_⟩
  · intro A B iA iB w hA hB hiA hiB he
    have h1 : (J.indMap g).cls A (f w) := by rw [hgcls]; exact (hcls A iA hA w).2 hiA
    have h2 := he Dom (J.indMap g) hM (f w) h1
    rw [hgcls] at h2
    exact hiB ((hcls B iB hB w).1 h2)
  · intro a C ia iC w ha hC hia hiC he
    have h1 := he Dom (J.indMap g) hM
    simp only [Interp.sat, Interp.ext] at h1
    rw [← (hindO a ia ha w).2 hia, hgcls] at h1
    exact hiC ((hcls C iC hC w).1 h1)
  · intro a b ia ib w v ha hb hia hib hwv he
    have h1 := (sat_same (J.indMap g) _ a b).1 (he Dom (J.indMap g) hM)
    rw [← (hindO a ia ha w).2 hia, ← (hindO b ib hb v).2 hib] at h1
    exact hwv (hinj h1)

end ContextCalculus.OWLFrontend

#print axioms ContextCalculus.OWLFrontend.downW
#print axioms ContextCalculus.OWLFrontend.wTabCore_facts
#print axioms ContextCalculus.OWLFrontend.hintWitness_sound
#print axioms ContextCalculus.OWLFrontend.wTab_model
