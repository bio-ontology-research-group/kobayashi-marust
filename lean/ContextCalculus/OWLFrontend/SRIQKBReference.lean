import ContextCalculus.OWLFrontend.SRIQKBTranslateCorrect

/-!
# The OWL route for SHIQ knowledge bases (stage C1b)

`docs/V1.7.0-C1B-ABOX-DESIGN.md`, sections 5 and 6.

`owlSHIQKBReference O requested hint` translates the knowledge base
(`translateSRIQKB`), checks the SHIQ conditions on the translation
(`kbOK`: the chain and simple-role checks `isSHIQB` of the SHIQ route, and
simple roles in the negative property assertions, `negSimpleB`), decides
consistency with `SRIQ.Proc.consistentKBQ` (the hint first, the exhaustive
search as fallback) and then publishes

* when consistent: the rows of the SHIQ route on the TBox alone
  (`QProc.classifyQO` on the transitivity encoding); `entailsSubKB_iff`
  says the ABox does not change them;
* when inconsistent: every requested IRI below every requested IRI
  (`unsat := true` rows).

`owlSHIQKBReference_sound` (every hint) and `owlSHIQKBReference_complete`
(on `OWL.Ontology.isSHIQKB` with the simple-role checks passed,
`SHIQKBSimple`) have the shape of the SHIQ capstones.

Realization: `owlTypeRow O C a hint` decides
`OWL.Entails O (ClassAssertion(C a))` and `owlSameRow O a b hint` decides
`OWL.Entails O (SameIndividual(a b))`, through `SRIQ.Proc.typeRow` and
`SRIQ.Proc.sameRow`; `owlTypeRow_sound`, `owlTypeRow_complete`,
`owlSameRow_sound` and `owlSameRow_complete` are their capstones.

## Hints

A hint is a realisation of the translated knowledge base over the concept
indices of its transitivity encoding (`RawHint`, converted by
`RawHint.toHint`; a hint that does not convert counts as no hint). The text
format (`parseHint`) has one directive per line; `#` starts a comment and
blank lines are skipped. Numbers are decimal; a role is `+k` (role index
`k`) or `-k` (its inverse).

```
blocks N                  -- the number of blocks
blk B0 B1 ... Bk-1        -- the block of each individual, in the order of `inds`
ty B C1 C2 ...            -- concept indices in the type of block B (repeatable)
lab B B' R1 R2 ...        -- roles in the label from block B to block B' (repeatable)
kid B R1 ... / C1 ...     -- a tree child of block B: its label, `/`, its type
```

The label from `B'` back to `B` is completed with the inverses, so each
edge needs one `lab` line. Concept indices: the requested IRIs first (in
request order, duplicates removed), then the other class IRIs, `top`,
`bottom` and the definers of the translation, then the names the
transitivity encoding adds. Role indices follow the first occurrence of each
property IRI.
-/

namespace ContextCalculus.OWLFrontend

open ContextCalculus
open ContextCalculus.SparseTaxonomy
open ContextCalculus.SRI (RoleT)
open ContextCalculus.SRIQ

/-! ## Simple roles in negative property assertions -/

/-- The roles of the negative role assertions. -/
def nroleRoles {n m k : Nat} (A : SRIQ.ABox (Fin n) (Fin m) (Fin k)) : List (RoleT (Fin m)) :=
  A.filterMap fun
    | .nrole _ R _ => some R
    | _ => none

/-- No transitive role lies below the role of a negative role assertion or
below its inverse. -/
def negSimpleB {n m k : Nat} (O : SRIQ.Ontology (Fin n) (Fin m))
    (A : SRIQ.ABox (Fin n) (Fin m) (Fin k)) : Bool :=
  (transRoles O).all fun T =>
    let up := SRI.Proc.roleUp (sriPart O) T
    (nroleRoles A).all fun R => !(up.contains R) && !(up.contains R.flip)

theorem isSHIQKB_of_checks {n m k : Nat} {O : SRIQ.Ontology (Fin n) (Fin m)}
    {A : SRIQ.ABox (Fin n) (Fin m) (Fin k)} (h1 : isSHIQB O = true) (h2 : negSimpleB O A = true) :
    Proc.IsSHIQKB O A := by
  refine ⟨isSHIQ_of_isSHIQB h1, fun a R b hn T hT => ?_⟩
  have h3 := List.all_eq_true.1 h2 T (mem_transRoles hT)
  have h4 := List.all_eq_true.1 h3 R (List.mem_filterMap.2 ⟨_, hn, rfl⟩)
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h4
  refine ⟨fun hle => ?_, fun hle => ?_⟩
  · have h' : (SRI.Proc.roleUp (sriPart O) T).contains R = true :=
      List.contains_iff_mem.2 (SRI.Proc.mem_roleUp.2 hle)
    rw [h4.1] at h'; exact absurd h' (by simp)
  · have h' : (SRI.Proc.roleUp (sriPart O) T).contains R.flip = true :=
      List.contains_iff_mem.2 (SRI.Proc.mem_roleUp.2 hle)
    rw [h4.2] at h'; exact absurd h' (by simp)

/-- The route's checks on a translation. -/
def kbOK (T : SRIQKBTranslation) : Bool :=
  isSHIQB T.ontology && negSimpleB T.ontology T.abox

theorem isSHIQKB_of_kbOK {T : SRIQKBTranslation} (h : kbOK T = true) :
    Proc.IsSHIQKB T.ontology T.abox := by
  simp only [kbOK, Bool.and_eq_true] at h
  exact isSHIQKB_of_checks h.1 h.2

/-! ## Hints -/

/-- A hint in the text format: a realisation over the blocks `0 .. nb - 1`,
on `Nat` indices. -/
structure RawHint where
  nb : Nat := 0
  blk : List Nat := []
  ty : List (Nat × List Nat) := []
  lab : List (Nat × Nat × List (RoleT Nat)) := []
  kids : List (Nat × List (RoleT Nat) × List Nat) := []
deriving Repr, Inhabited

namespace RawHint

def finOf (n x : Nat) : Option (Fin n) := if h : x < n then some ⟨x, h⟩ else none

def finsOf (n : Nat) (xs : List Nat) : Option (Finset (Fin n)) :=
  (xs.mapM (finOf n)).map List.toFinset

def rtOf (m : Nat) : RoleT Nat → Option (RoleT (Fin m))
  | .pos r => (finOf m r).map .pos
  | .inv r => (finOf m r).map .inv

def rtsOf (m : Nat) (Rs : List (RoleT Nat)) : Option (Finset (RoleT (Fin m))) :=
  (Rs.mapM (rtOf m)).map List.toFinset

/-- The hint over `Fin n` concepts, `Fin m` roles and `Fin k` individuals;
`none` when the block map has the wrong length or an index is out of
range. -/
def toHint (h : RawHint) (n m k : Nat) : Option (Proc.Hint n m k) :=
  if hnb : 0 < h.nb then
    if h.blk.length = k then
      match h.blk.mapM (finOf h.nb), h.ty.mapM (fun e => (finsOf n e.2).map (e.1, ·)),
        h.lab.mapM (fun e => (rtsOf m e.2.2).map (e.1, e.2.1, ·)),
        h.kids.mapM (fun e => ((rtsOf m e.2.1).bind fun L => (finsOf n e.2.2).map (e.1, L, ·)))
      with
      | some blk, some ty, some lab, some kids =>
        let d : Fin h.nb := ⟨0, hnb⟩
        let half := fun (b c : Fin h.nb) =>
          lab.foldl (fun acc e => if e.1 = b.val ∧ e.2.1 = c.val then acc ∪ e.2.2 else acc) ∅
        some { nb := h.nb
               blk := fun i => blk.getD i.val d
               ty := fun b => ty.foldl (fun acc e => if e.1 = b.val then acc ∪ e.2 else acc) ∅
               lab := fun b c => half b c ∪ flipL (half c b)
               kids := fun b => (kids.filter fun e => e.1 = b.val).map fun e => (e.2.1, e.2.2) }
      | _, _, _, _ => none
    else none
  else none

/-- A role `+k` or `-k`. -/
def parseRT (s : String) : Option (RoleT Nat) :=
  if s.startsWith "+" then (s.drop 1).toString.toNat?.map .pos
  else if s.startsWith "-" then (s.drop 1).toString.toNat?.map .inv
  else none

def parseNats (ws : List String) : Except String (List Nat) :=
  ws.mapM fun w => match w.toNat? with
    | some k => .ok k
    | none => .error s!"not a number: {w}"

def parseRTs (ws : List String) : Except String (List (RoleT Nat)) :=
  ws.mapM fun w => match parseRT w with
    | some R => .ok R
    | none => .error s!"not a role (+k or -k): {w}"

/-- One line of the text format. -/
def parseLine (h : RawHint) (ws : List String) : Except String RawHint :=
  match ws with
  | [] => .ok h
  | ["blocks", w] => match w.toNat? with
    | some k => .ok { h with nb := k }
    | none => .error s!"not a number: {w}"
  | "blk" :: rest => do
    let bs ← parseNats rest
    .ok { h with blk := h.blk ++ bs }
  | "ty" :: b :: rest => do
    let b' ← parseNats [b]
    let cs ← parseNats rest
    .ok { h with ty := h.ty ++ [(b'.headD 0, cs)] }
  | "lab" :: b :: c :: rest => do
    let bc ← parseNats [b, c]
    let Rs ← parseRTs rest
    .ok { h with lab := h.lab ++ [(bc.headD 0, bc.getD 1 0, Rs)] }
  | "kid" :: b :: rest => do
    let b' ← parseNats [b]
    match rest.splitOn "/" with
    | [rs, cs] =>
      let Rs ← parseRTs rs
      let cs' ← parseNats cs
      .ok { h with kids := h.kids ++ [(b'.headD 0, Rs, cs')] }
    | _ => .error "kid: expected `kid B R ... / C ...`"
  | w :: _ => .error s!"unknown directive: {w}"

/-- Parse the text format. -/
def parseHint (text : String) : Except String RawHint :=
  (text.splitOn "\n").foldlM (init := {}) fun h line =>
    let body := (line.splitOn "#").headD ""
    let ws := ((body.split fun c => c == ' ' || c == '\t' || c == '\r').toList.map
      (·.toString)).filter (· ≠ "")
    parseLine h ws

end RawHint

/-! ## The route -/

/-- The TBox part of a knowledge-base translation, for the rows of the SHIQ
route. -/
def SRIQKBTranslation.tbox (T : SRIQKBTranslation) : SRIQTranslation :=
  ⟨T.named, T.conceptCount, T.roleCount, T.hnamed, T.ontology⟩

/-- The hint over the names of the transitivity encoding. -/
def kbHint (T : SRIQKBTranslation) (hint : Option RawHint) :
    Option (Proc.Hint (T.conceptCount + (Proc.encTransQ T.ontology).1) T.roleCount T.inds.length) :=
  hint.bind fun h => h.toHint _ _ _

/-- The answer: the rows of the SHIQ route on the TBox when consistent,
every bit set otherwise. -/
def kbAnswerOf (T : SRIQKBTranslation)
    (E : Σ k, SRIQ.Ontology (Fin (T.conceptCount + k)) (Fin T.roleCount)) (consistent : Bool) :
    OWLAnswer :=
  if consistent then
    { named := T.named, rows := sriqRows T.tbox (QProc.classifyQO E.2 (sriqRequest T.tbox E.1)) }
  else
    { named := T.named, rows := (List.range T.named.length).map fun i => ⟨i, true, []⟩ }

/-- The SHIQ knowledge-base route. -/
def owlSHIQKBReference (O : OWL.Ontology) (requested : List OWL.IRI) (hint : Option RawHint) :
    Option OWLAnswer :=
  match translateSRIQKB O requested with
  | none => none
  | some T =>
    if kbOK T then
      some (kbAnswerOf T (Proc.encTransQ T.ontology)
        (Proc.consistentKBQ T.ontology T.abox (kbHint T hint)))
    else none

/-! ### Exactness -/

/-- Every answer of the SHIQ knowledge-base route is exact under the OWL 2
direct semantics, for every requested pair and every hint. -/
theorem owlSHIQKBReference_sound {O : OWL.Ontology} {requested : List OWL.IRI}
    {hint : Option RawHint} {a : OWLAnswer} (h : owlSHIQKBReference O requested hint = some a) :
    a.named = requested.eraseDups ∧
      ∀ i j (hi : i < a.named.length) (hj : j < a.named.length),
        (a.bit i j = true ↔ OWL.EntailsSub O a.named[i] a.named[j]) := by
  unfold owlSHIQKBReference at h
  split at h
  · exact absurd h (by simp)
  next T hT =>
    split at h
    · next hok =>
      simp only [Option.some.injEq] at h
      subst h
      have hKB := isSHIQKB_of_kbOK hok
      have hnamed : (kbAnswerOf T (Proc.encTransQ T.ontology)
          (Proc.consistentKBQ T.ontology T.abox (kbHint T hint))).named = T.named := by
        unfold kbAnswerOf; split <;> rfl
      refine ⟨hnamed.trans (translateSRIQKB_spec hT).2.1, ?_⟩
      intro i j hi hj
      have hi' : i < T.named.length := hnamed ▸ hi
      have hj' : j < T.named.length := hnamed ▸ hj
      have he : ∀ k (hk : k < (kbAnswerOf T (Proc.encTransQ T.ontology)
          (Proc.consistentKBQ T.ontology T.abox (kbHint T hint))).named.length),
          (kbAnswerOf T (Proc.encTransQ T.ontology)
            (Proc.consistentKBQ T.ontology T.abox (kbHint T hint))).named[k] =
          T.named[k]'(hnamed ▸ hk) := by
        intro k hk; simp only [hnamed]
      rw [he i hi, he j hj, translateSRIQKB_entailsSub hT i j hi' hj', entailsSubKB_iff]
      cases hc : Proc.consistentKBQ T.ontology T.abox (kbHint T hint)
      · have hn : ¬ ConsistentKB T.ontology T.abox := fun h' =>
          absurd ((Proc.consistentKBQ_iff hKB _).2 h') (by rw [hc]; simp)
        have hb : (kbAnswerOf T (Proc.encTransQ T.ontology) false).bit i j = true := by
          simp [kbAnswerOf, OWLAnswer.bit, hi', SparseRow.bit]
        simp only [hb, true_iff]
        exact Or.inl hn
      · have hy : ConsistentKB T.ontology T.abox := (Proc.consistentKBQ_iff hKB _).1 hc
        simp only [hy, not_true_eq_false, false_or]
        rw [Proc.encTransQ_correct hKB.1]
        exact sriq_bit T.tbox (Proc.encTransQ_isALCHIQ T.ontology) i j hi' hj'
    · exact absurd h (by simp)

/-- The simple-role restriction of OWL 2 DL, checked on the translated
knowledge base: no transitive role lies below a role of a counting clause
(`simpleB`) or below the role of a negative property assertion
(`negSimpleB`), or below their inverses. -/
def SHIQKBSimple (O : OWL.Ontology) (requested : List OWL.IRI) (extra : List OWL.IRI := []) :
    Prop :=
  ∀ T, translateSRIQKB O requested extra = some T →
    simpleB T.ontology = true ∧ negSimpleB T.ontology T.abox = true

theorem kbOK_of_simple {O : OWL.Ontology} {requested extra : List OWL.IRI}
    {T : SRIQKBTranslation} (hT : translateSRIQKB O requested extra = some T)
    (hs : SHIQKBSimple O requested extra) : kbOK T = true := by
  have := hs T hT
  simp [kbOK, isSHIQB, translateSRIQKB_chainsOK hT, this.1, this.2]

/-- On every knowledge base of the SHIQ knowledge-base part that passes the
simple-role checks, the route publishes, for every hint. -/
theorem owlSHIQKBReference_complete {O : OWL.Ontology} (requested : List OWL.IRI)
    (h : O.isSHIQKB = true) (hs : SHIQKBSimple O requested) (hint : Option RawHint) :
    (owlSHIQKBReference O requested hint).isSome = true := by
  have hT := translateSRIQKB_isSome (requested := requested) (extra := []) h
  unfold owlSHIQKBReference
  split
  · next hnone => rw [hnone] at hT; exact absurd hT (by simp)
  · next T hT' => simp [kbOK_of_simple hT' hs]

/-- The route publishes exactly on the SHIQ knowledge-base part with the
simple-role checks passed. -/
theorem owlSHIQKBReference_isSome_iff {O : OWL.Ontology} (requested : List OWL.IRI)
    (hint : Option RawHint) :
    (owlSHIQKBReference O requested hint).isSome = true ↔
      O.isSHIQKB = true ∧ SHIQKBSimple O requested := by
  constructor
  · intro h
    unfold owlSHIQKBReference at h
    split at h
    · simp at h
    · next T hT =>
        split at h
        · next hok =>
            refine ⟨(translateSRIQKB_spec hT).1, fun T' hT' => ?_⟩
            rw [hT] at hT'
            cases hT'
            simp only [kbOK, isSHIQB, Bool.and_eq_true] at hok
            exact ⟨hok.1.2, hok.2⟩
        · simp at h
  · rintro ⟨h, hs⟩
    exact owlSHIQKBReference_complete requested h hs hint

/-! ## Realization -/

/-- **Type of an individual.** Decides `O ⊨ ClassAssertion(C a)` for a
class IRI `C` and a named individual `a`, with an optional countermodel
hint (a realisation of the translation of `O` with the complement of `C`
at `a`, over the names of the transitivity encoding of `complO`; the
complement name is the last index before the encoding's names). -/
def owlTypeRow (O : OWL.Ontology) (C a : OWL.IRI) (hint : Option RawHint) : Option Bool :=
  match translateSRIQKB O [C] [a] with
  | none => none
  | some T =>
    if kbOK T then
      if hC : 0 < T.named.length then
        if ha : T.inds.idxOf a < T.inds.length then
          some (Proc.typeRow T.ontology T.abox ⟨_, ha⟩ ⟨0, Nat.lt_of_lt_of_le hC T.hnamed⟩
            (hint.bind fun h => h.toHint _ _ _))
        else none
      else none
    else none

/-- **Equality of individuals.** Decides `O ⊨ SameIndividual(a b)`, with an
optional countermodel hint (a realisation of the translation of `O` with
`a ≠ b`). -/
def owlSameRow (O : OWL.Ontology) (a b : OWL.IRI) (hint : Option RawHint) : Option Bool :=
  match translateSRIQKB O [] [a, b] with
  | none => none
  | some T =>
    if kbOK T then
      if ha : T.inds.idxOf a < T.inds.length then
        if hb : T.inds.idxOf b < T.inds.length then
          some (Proc.sameRow T.ontology T.abox ⟨_, ha⟩ ⟨_, hb⟩
            (hint.bind fun h => h.toHint _ _ _))
        else none
      else none
    else none

/-- Every answer of `owlTypeRow` is exact, for every hint. -/
theorem owlTypeRow_sound {O : OWL.Ontology} {C a : OWL.IRI} {hint : Option RawHint} {v : Bool}
    (h : owlTypeRow O C a hint = some v) :
    v = true ↔ OWL.Entails O (.classAssertion (.cls C) (.named a)) := by
  unfold owlTypeRow at h
  split at h
  · exact absurd h (by simp)
  next T hT =>
    split at h
    case isFalse => exact absurd h (by simp)
    rename_i hok
    split at h
    case isFalse => exact absurd h (by simp)
    rename_i hC
    split at h
    case isFalse => exact absurd h (by simp)
    rename_i ha
    simp only [Option.some.injEq] at h
    subst h
    have hn : T.named = [C] := by rw [(translateSRIQKB_spec hT).2.1]; rfl
    have h0 : T.named[0] = C := by simp only [hn, List.getElem_cons_zero]
    rw [Proc.typeRow_iff (isSHIQKB_of_kbOK hok), ← translateSRIQKB_entailsType hT 0 hC a ha, h0]

/-- On the SHIQ knowledge-base part with the simple-role checks passed,
`owlTypeRow` answers, for every hint. -/
theorem owlTypeRow_complete {O : OWL.Ontology} (C a : OWL.IRI) (h : O.isSHIQKB = true)
    (hs : SHIQKBSimple O [C] [a]) (hint : Option RawHint) :
    (owlTypeRow O C a hint).isSome = true := by
  have hT := translateSRIQKB_isSome (requested := [C]) (extra := [a]) h
  unfold owlTypeRow
  split
  · next hnone => rw [hnone] at hT; exact absurd hT (by simp)
  · next T hT' =>
    have hsp := translateSRIQKB_spec hT'
    have hC : 0 < T.named.length := by rw [hsp.2.1, List.eraseDups_cons]; simp
    have ha : T.inds.idxOf a < T.inds.length :=
      List.idxOf_lt_length_of_mem (by rw [hsp.2.2]; simp)
    simp [kbOK_of_simple hT' hs, hC, ha]

/-- Every answer of `owlSameRow` is exact, for every hint. -/
theorem owlSameRow_sound {O : OWL.Ontology} {a b : OWL.IRI} {hint : Option RawHint} {v : Bool}
    (h : owlSameRow O a b hint = some v) :
    v = true ↔ OWL.Entails O (.sameIndividual [.named a, .named b]) := by
  unfold owlSameRow at h
  split at h
  · exact absurd h (by simp)
  next T hT =>
    split at h
    case isFalse => exact absurd h (by simp)
    rename_i hok
    split at h
    case isFalse => exact absurd h (by simp)
    rename_i ha
    split at h
    case isFalse => exact absurd h (by simp)
    rename_i hb
    simp only [Option.some.injEq] at h
    subst h
    rw [Proc.sameRow_iff (isSHIQKB_of_kbOK hok), ← translateSRIQKB_entailsSame hT a b ha hb]

/-- On the SHIQ knowledge-base part with the simple-role checks passed,
`owlSameRow` answers, for every hint. -/
theorem owlSameRow_complete {O : OWL.Ontology} (a b : OWL.IRI) (h : O.isSHIQKB = true)
    (hs : SHIQKBSimple O [] [a, b]) (hint : Option RawHint) :
    (owlSameRow O a b hint).isSome = true := by
  have hT := translateSRIQKB_isSome (requested := []) (extra := [a, b]) h
  unfold owlSameRow
  split
  · next hnone => rw [hnone] at hT; exact absurd hT (by simp)
  · next T hT' =>
    have hsp := translateSRIQKB_spec hT'
    have ha : T.inds.idxOf a < T.inds.length :=
      List.idxOf_lt_length_of_mem (by rw [hsp.2.2]; simp)
    have hb : T.inds.idxOf b < T.inds.length :=
      List.idxOf_lt_length_of_mem (by rw [hsp.2.2]; simp)
    simp [kbOK_of_simple hT' hs, ha, hb]

end ContextCalculus.OWLFrontend

#print axioms ContextCalculus.OWLFrontend.isSHIQKB_of_checks
#print axioms ContextCalculus.OWLFrontend.owlSHIQKBReference_sound
#print axioms ContextCalculus.OWLFrontend.owlSHIQKBReference_complete
#print axioms ContextCalculus.OWLFrontend.owlSHIQKBReference_isSome_iff
#print axioms ContextCalculus.OWLFrontend.owlTypeRow_sound
#print axioms ContextCalculus.OWLFrontend.owlTypeRow_complete
#print axioms ContextCalculus.OWLFrontend.owlSameRow_sound
#print axioms ContextCalculus.OWLFrontend.owlSameRow_complete
