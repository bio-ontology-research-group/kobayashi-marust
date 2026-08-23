import ContextCalculus.CBProductionTraceWire
import ContextCalculus.Nominals

/-!
# Executable allocation evidence for production CB Nom firings

Nom is not an ordinary local derivation step.  Its soundness theorem chooses
interpretations for fresh individual constants, and a complete run may make
many such choices.  This wire checks the operational side condition required
by `Nominals.nom_family_sound`: every exact grounded Hyper firing owns one
stable, nonempty, consecutive block, and all blocks are globally fresh and
disjoint.  It also checks exact budget accounting and rejects truncated runs.

The semantic connection from each firing key to its covering premise remains a
separate certificate layer.  Keeping allocation evidence separate prevents a
Nom conclusion from being incorrectly justified as ordinary resolution.
-/

namespace ContextCalculus.CBNominalAllocationWire

open Lean ContextCalculus.CBTermWire ContextCalculus.CBSourceWire
open ContextCalculus.Nominals
open ContextCalculus.CBProductionTrace

structure WireNominalFiringKey where
  context : Nat
  source_body : List WirePredicate
  source_head : List WireLiteral
  side_body : List WirePredicate
  side_head : List WireLiteral
  selected : List (Nat × WirePredicate)
  substitution : List WireSubstitutionEntry
deriving DecidableEq, FromJson, ToJson

structure WireNominalBlock where
  key : WireNominalFiringKey
  first : Nat
  width : Nat
  body : List WireLiteral
  kept_head : List WireLiteral
  conclusion : WireClause
deriving DecidableEq, FromJson, ToJson

structure WireNominalAllocation where
  version : Nat
  source : WireSourceBinding
  individual_count : Nat
  budget : Nat
  allocated : Nat
  truncated : Bool
  blocks : List WireNominalBlock
deriving FromJson, ToJson

structure NominalFiringKey where
  context : Nat
  sourceBody : List CheckerTerm.FPred
  sourceHead : List CheckerTerm.FLit
  sideBody : List CheckerTerm.FPred
  sideHead : List CheckerTerm.FLit
  selected : List (Nat × CheckerTerm.FPred)
  substitution : List (Int × CheckerTerm.FTerm)

structure NominalBlock where
  wireKey : WireNominalFiringKey
  key : NominalFiringKey
  first : Nat
  width : Nat
  body : List CheckerTerm.FLit
  keptHead : List CheckerTerm.FLit
  conclusion : CheckerTerm.FCL
  conclusion_equiv : CheckerTerm.clEquivT conclusion
    ⟨body, keptHead ++ (List.finRange width).map fun index =>
      .eq (.var (-1)) (.const (first + index.val))⟩

private def decodeSelected (bounds : Bounds)
    (entry : Nat × WirePredicate) :
    Except String (Nat × CheckerTerm.FPred) := do
  let predicate ← entry.2.decode bounds
  return (entry.1, predicate)

def WireNominalFiringKey.decode (bounds : Bounds)
    (wire : WireNominalFiringKey) : Except String NominalFiringKey := do
  let variableIds := wire.substitution.map WireSubstitutionEntry.variableId
  if !wire.selected.isEmpty then
    if variableIds.Nodup then
      return {
        context := wire.context
        sourceBody := ← wire.source_body.mapM (WirePredicate.decode bounds)
        sourceHead := ← wire.source_head.mapM (WireLiteral.decode bounds)
        sideBody := ← wire.side_body.mapM (WirePredicate.decode bounds)
        sideHead := ← wire.side_head.mapM (WireLiteral.decode bounds)
        selected := ← wire.selected.mapM (decodeSelected bounds)
        substitution := ← wire.substitution.mapM
          (WireSubstitutionEntry.decode bounds)
      }
    else throw "Nom firing substitution contains a duplicate variable"
  else throw "Nom firing must select at least one matched predicate"

def WireNominalBlock.decode (bounds : Bounds)
    (wire : WireNominalBlock) : Except String NominalBlock := do
  let key ← wire.key.decode bounds
  if wire.body.Nodup then
    if wire.kept_head.Nodup then
      let body ← wire.body.mapM (WireLiteral.decode bounds)
      let keptHead ← wire.kept_head.mapM (WireLiteral.decode bounds)
      let conclusion ← wire.conclusion.decode bounds
      let expected : CheckerTerm.FCL :=
        ⟨body, keptHead ++ (List.finRange wire.width).map fun index =>
          .eq (.var (-1)) (.const (wire.first + index.val))⟩
      if hequivalent : CheckerTerm.clEquivT conclusion expected then
        return NominalBlock.mk wire.key key wire.first wire.width body
          keptHead conclusion hequivalent
      else throw "CB Nom emitted clause differs from its checked block conclusion"
    else throw "CB Nom retained head contains a duplicate literal"
  else throw "CB Nom conclusion body contains a duplicate literal"

def blockIds (block : NominalBlock) : List Nat :=
  (List.range block.width).map (block.first + ·)

def allBlockIds (blocks : List NominalBlock) : List Nat :=
  blocks.flatMap blockIds

def sequentialFrom : Nat → List NominalBlock → Bool
  | _, [] => true
  | cursor, block :: rest =>
      decide (block.first = cursor) &&
        sequentialFrom (cursor + block.width) rest

structure DecodedNominalAllocation where
  source : DecodedSourceBinding
  individualCount : Nat
  source_count_le : source.bounds.individuals ≤ individualCount
  budget : Nat
  allocated : Nat
  blocks : List NominalBlock
  keys_nodup : (blocks.map (·.wireKey)).Nodup
  widths_positive : ∀ block ∈ blocks, 0 < block.width
  sequential : sequentialFrom source.bounds.individuals blocks = true
  ids_nodup : (allBlockIds blocks).Nodup
  ids_fresh : ∀ id ∈ allBlockIds blocks,
    source.bounds.individuals ≤ id ∧ id < individualCount
  allocated_eq : allocated = (blocks.map (·.width)).sum
  allocated_le_budget : allocated ≤ budget

def WireNominalAllocation.decode (wire : WireNominalAllocation) :
    Except String DecodedNominalAllocation := do
  if wire.version != 1 then
    throw s!"unsupported CB Nom-allocation version {wire.version}"
  if wire.truncated then
    throw "CB Nom allocation was truncated"
  let source ← wire.source.decode
  if hcount : source.bounds.individuals ≤ wire.individual_count then
    let bounds := { source.bounds with individuals := wire.individual_count }
    let blocks ← wire.blocks.mapM (WireNominalBlock.decode bounds)
    if blocks.isEmpty then
      throw "CB Nom allocation must contain at least one firing"
    if hkeys : (blocks.map (·.wireKey)).Nodup then
      if hwidths : ∀ block ∈ blocks, 0 < block.width then
        if hsequential : sequentialFrom source.bounds.individuals blocks = true then
          if hids : (allBlockIds blocks).Nodup then
            if hfresh : ∀ id ∈ allBlockIds blocks,
                source.bounds.individuals ≤ id ∧ id < wire.individual_count then
              if hallocated : wire.allocated = (blocks.map (·.width)).sum then
                if hbudget : wire.allocated ≤ wire.budget then
                  return {
                    source
                    individualCount := wire.individual_count
                    source_count_le := hcount
                    budget := wire.budget
                    allocated := wire.allocated
                    blocks
                    keys_nodup := hkeys
                    widths_positive := hwidths
                    sequential := hsequential
                    ids_nodup := hids
                    ids_fresh := hfresh
                    allocated_eq := hallocated
                    allocated_le_budget := hbudget
                  }
                else throw "CB Nom allocation exceeds its declared budget"
              else throw "CB Nom allocated count differs from the block widths"
            else throw "CB Nom block contains a non-fresh or out-of-range individual"
          else throw "CB Nom blocks overlap"
        else throw "CB Nom blocks are not one consecutive allocation sequence"
      else throw "CB Nom block has zero width"
    else throw "CB Nom firing key occurs more than once"
  else throw "CB Nom individual table is smaller than the source individual table"

def WireNominalAllocation.check (wire : WireNominalAllocation) :
    Except String Bool := do
  let _ ← wire.decode
  return true

theorem WireNominalAllocation.check_sound (wire : WireNominalAllocation)
    (hcheck : wire.check = .ok true) :
    ∃ decoded : DecodedNominalAllocation,
      wire.decode = .ok decoded ∧
      (decoded.blocks.map (·.wireKey)).Nodup ∧
      (allBlockIds decoded.blocks).Nodup ∧
      (∀ id ∈ allBlockIds decoded.blocks,
        decoded.source.bounds.individuals ≤ id ∧
          id < decoded.individualCount) ∧
      decoded.allocated = (decoded.blocks.map (·.width)).sum ∧
      decoded.allocated ≤ decoded.budget := by
  cases hdecode : wire.decode with
  | error message => simp [WireNominalAllocation.check, hdecode] at hcheck
  | ok decoded =>
      exact ⟨decoded, rfl, decoded.keys_nodup, decoded.ids_nodup,
        decoded.ids_fresh, decoded.allocated_eq, decoded.allocated_le_budget⟩

/-- The semantic obligations and allocation document agree firing-for-firing.
The obligation list is supplied by the next premise-decoding layer; this
predicate makes its exact remaining responsibility explicit. -/
structure AlignedObligations {D : Type}
    (decoded : DecodedNominalAllocation)
    (obligations : List (NomObligation D)) : Prop where
  length_eq : decoded.blocks.length = obligations.length
  widths : ∀ index : Fin obligations.length,
    (decoded.blocks.get (Fin.cast length_eq.symm index)).width =
      (obligations.get index).width

/-- Allocation acceptance composes with the finite-family Nom theorem.  Thus,
once the premise layer produces an aligned obligation for every checked firing,
all firings have simultaneous witnesses while their concrete constant blocks
remain fresh and disjoint. -/
theorem WireNominalAllocation.check_family_sound {D : Type}
    (wire : WireNominalAllocation) (hcheck : wire.check = .ok true)
    (obligations : List (NomObligation D))
    (haligned : ∀ decoded, wire.decode = .ok decoded →
      AlignedObligations decoded obligations) :
    ∃ decoded : DecodedNominalAllocation,
      wire.decode = .ok decoded ∧
      AlignedObligations decoded obligations ∧
      (allBlockIds decoded.blocks).Nodup ∧
      (∀ id ∈ allBlockIds decoded.blocks,
        decoded.source.bounds.individuals ≤ id ∧
          id < decoded.individualCount) ∧
      ∃ interp : NomFamilyInterpretation obligations,
        ∀ index : Fin obligations.length,
          (obligations.get index).SatisfiedWith (interp index) := by
  obtain ⟨decoded, hdecode, _, hids, hfresh, _, _⟩ :=
    wire.check_sound hcheck
  obtain ⟨interp, hinterp⟩ := nom_family_sound obligations
  exact ⟨decoded, hdecode, haligned decoded hdecode, hids, hfresh,
    interp, hinterp⟩

/-! ## Binding a semantic Nom obligation to the emitted production clause -/

/-- Exact clause shape emitted after Nom replaces the triggering equalities:
the ordinary residual head is retained and one `y ≈ fresh` disjunct is added
for every slot in the firing's checked block. -/
def nomConclusion {width : Nat} (body keptHead : List CheckerTerm.FLit)
    (fresh : Fin width → CheckerTerm.FTerm) : CheckerTerm.FCL :=
  ⟨body, keptHead ++ (List.finRange width).map fun index =>
    .eq (.var (-1)) (fresh index)⟩

theorem NominalBlock.emitted_conclusion_sound {D : Type}
    (block : NominalBlock) (model : CheckerTerm.TModel D)
    (assignment : Int → D)
    (hexpected : HoldsAt model assignment
      (nomConclusion (width := block.width) block.body block.keptHead
        fun index => .const (block.first + index.val))) :
    HoldsAt model assignment block.conclusion := by
  exact CheckerTerm.sat_of_clEquivT block.conclusion_equiv hexpected

/-- Interpret one consecutive block of fresh individual constants while
leaving concepts, roles, functions, and every other constant unchanged. -/
def extendNomBlock {D : Type} (model : CheckerTerm.TModel D) (first : Nat)
    {width : Nat} (interp : Fin width → D) : CheckerTerm.TModel D where
  conc := model.conc
  rol := model.rol
  fn := model.fn
  const := fun individual =>
    if h : first ≤ individual ∧ individual < first + width then
      interp ⟨individual - first, by omega⟩
    else model.const individual

def constantsBelowTerm (bound : Nat) : CheckerTerm.FTerm → Prop
  | .var _ => True
  | .const individual => individual < bound
  | .app _ argument => constantsBelowTerm bound argument

def constantsBelowPredicate (bound : Nat) : CheckerTerm.FPred → Prop
  | .concept _ term => constantsBelowTerm bound term
  | .role _ source target =>
      constantsBelowTerm bound source ∧ constantsBelowTerm bound target

def constantsBelowLiteral (bound : Nat) : CheckerTerm.FLit → Prop
  | .P predicate => constantsBelowPredicate bound predicate
  | .eq left right | .ineq left right =>
      constantsBelowTerm bound left ∧ constantsBelowTerm bound right

def ConstantsBelowClause (bound : Nat) (clause : CheckerTerm.FCL) : Prop :=
  (∀ literal ∈ clause.body, constantsBelowLiteral bound literal) ∧
  (∀ literal ∈ clause.head, constantsBelowLiteral bound literal)

theorem extendNomBlock_fresh {D : Type} (model : CheckerTerm.TModel D)
    (first : Nat) {width : Nat} (interp : Fin width → D)
    (assignment : Int → D) (index : Fin width) :
    (extendNomBlock model first interp).evalT assignment
        (.const (first + index.val)) = interp index := by
  simp only [CheckerTerm.TModel.evalT, extendNomBlock]
  have hrange : first ≤ first + index.val ∧
      first + index.val < first + width := by omega
  rw [dif_pos hrange]
  congr
  omega

theorem evalT_extendNomBlock_of_below {D : Type}
    (model : CheckerTerm.TModel D) (first : Nat) {width : Nat}
    (interp : Fin width → D) (assignment : Int → D) :
    ∀ term : CheckerTerm.FTerm, constantsBelowTerm first term →
      (extendNomBlock model first interp).evalT assignment term =
        model.evalT assignment term
  | .var _, _ => rfl
  | .const individual, hbelow => by
      simp only [CheckerTerm.TModel.evalT, extendNomBlock]
      rw [dif_neg]
      exact fun hrange => (Nat.not_lt_of_ge hrange.1) hbelow
  | .app function argument, hbelow => by
      change model.fn function
          ((extendNomBlock model first interp).evalT assignment argument) =
        model.fn function (model.evalT assignment argument)
      rw [evalT_extendNomBlock_of_below model first interp assignment
        argument hbelow]

theorem evalL_extendNomBlock_of_below {D : Type}
    (model : CheckerTerm.TModel D) (first : Nat) {width : Nat}
    (interp : Fin width → D) (assignment : Int → D) :
    ∀ literal : CheckerTerm.FLit, constantsBelowLiteral first literal →
      ((extendNomBlock model first interp).evalL assignment literal ↔
        model.evalL assignment literal) := by
  intro literal hbelow
  cases literal with
  | P predicate => cases predicate with
    | concept concept term =>
      simp only [constantsBelowLiteral, constantsBelowPredicate] at hbelow
      change model.conc concept
          ((extendNomBlock model first interp).evalT assignment term) ↔
        model.conc concept (model.evalT assignment term)
      rw [evalT_extendNomBlock_of_below model first interp assignment term hbelow]
    | role role source target =>
      simp only [constantsBelowLiteral, constantsBelowPredicate] at hbelow
      change model.rol role
          ((extendNomBlock model first interp).evalT assignment source)
          ((extendNomBlock model first interp).evalT assignment target) ↔
        model.rol role (model.evalT assignment source)
          (model.evalT assignment target)
      rw [evalT_extendNomBlock_of_below model first interp assignment source hbelow.1,
        evalT_extendNomBlock_of_below model first interp assignment target hbelow.2]
  | eq left right =>
    simp only [constantsBelowLiteral, CheckerTerm.TModel.evalL] at hbelow ⊢
    rw [evalT_extendNomBlock_of_below model first interp assignment left hbelow.1,
      evalT_extendNomBlock_of_below model first interp assignment right hbelow.2]
  | ineq left right =>
    simp only [constantsBelowLiteral, CheckerTerm.TModel.evalL] at hbelow ⊢
    rw [evalT_extendNomBlock_of_below model first interp assignment left hbelow.1,
      evalT_extendNomBlock_of_below model first interp assignment right hbelow.2]

theorem valid_extendNomBlock_of_below {D : Type}
    (model : CheckerTerm.TModel D) (first : Nat) {width : Nat}
    (interp : Fin width → D) (clause : CheckerTerm.FCL)
    (hbelow : ConstantsBelowClause first clause)
    (hvalid : CheckerTerm.valid model clause) :
    CheckerTerm.valid (extendNomBlock model first interp) clause := by
  intro assignment hbody
  have hbodyBase : ∀ literal ∈ clause.body,
      model.evalL assignment literal := by
    intro literal hliteral
    exact (evalL_extendNomBlock_of_below model first interp assignment
      literal (hbelow.1 literal hliteral)).mp
        (hbody literal hliteral)
  obtain ⟨literal, hliteral, htrue⟩ := hvalid assignment hbodyBase
  exact ⟨literal, hliteral,
    (evalL_extendNomBlock_of_below model first interp assignment
      literal (hbelow.2 literal hliteral)).mpr htrue⟩

/-- A simultaneous witness supplied by `nom_family_sound` makes the exact
production equality disjunction true. The premise decoder has two precise
semantic duties: identify the retained body with `B`, and identify the retained
non-Nom head with `groundEscape`. The constant decoder must identify each
checked block slot with the corresponding interpretation selected for it. -/
theorem nomConclusion_sound {D : Type} (model : CheckerTerm.TModel D)
    (obligation : NomObligation D)
    (interp : Fin obligation.width → D)
    (hsatisfied : obligation.SatisfiedWith interp)
    (body keptHead : List CheckerTerm.FLit)
    (fresh : Fin obligation.width → CheckerTerm.FTerm)
    (hbodyMeaning : ∀ assignment : Int → D,
      (∀ literal ∈ body, model.evalL assignment literal) →
        obligation.B (assignment (-1)))
    (hgroundMeaning : obligation.groundEscape →
      ∀ assignment : Int → D, ∃ literal ∈ keptHead,
        model.evalL assignment literal)
    (hfreshMeaning : ∀ (assignment : Int → D)
      (index : Fin obligation.width),
        model.evalT assignment (fresh index) = interp index) :
    ∀ assignment : Int → D,
      HoldsAt model assignment (nomConclusion body keptHead fresh) := by
  intro assignment hbody
  rcases hsatisfied with hground | hcover
  · obtain ⟨literal, hliteral, htrue⟩ := hgroundMeaning hground assignment
    exact ⟨literal, by simp [nomConclusion, hliteral], htrue⟩
  · obtain ⟨index, heq⟩ := hcover (assignment (-1))
      (hbodyMeaning assignment hbody)
    refine ⟨.eq (.var (-1)) (fresh index), ?_, ?_⟩
    · simp [nomConclusion]
    · simpa [CheckerTerm.TModel.evalL, CheckerTerm.TModel.evalT,
        hfreshMeaning assignment index] using heq

/-- One checked Nom firing can be realized by an explicit fresh-constant model
extension. Every source clause below the block boundary remains valid, and the
exact equality-disjunction conclusion becomes valid in the extended model. -/
theorem nomConclusion_exists_extension {D : Type}
    (model : CheckerTerm.TModel D) (obligation : NomObligation D)
    (first : Nat) (source : List CheckerTerm.FCL)
    (body keptHead : List CheckerTerm.FLit)
    (hsourceBelow : ∀ clause ∈ source, ConstantsBelowClause first clause)
    (hsourceValid : ∀ clause ∈ source, CheckerTerm.valid model clause)
    (hbodyBelow : ∀ literal ∈ body,
      constantsBelowLiteral first literal)
    (hheadBelow : ∀ literal ∈ keptHead,
      constantsBelowLiteral first literal)
    (hbodyMeaning : ∀ assignment : Int → D,
      (∀ literal ∈ body, model.evalL assignment literal) →
        obligation.B (assignment (-1)))
    (hgroundMeaning : obligation.groundEscape →
      ∀ assignment : Int → D, ∃ literal ∈ keptHead,
        model.evalL assignment literal) :
    ∃ interp : Fin obligation.width → D,
      let extended := extendNomBlock model first interp
      (∀ clause ∈ source, CheckerTerm.valid extended clause) ∧
      CheckerTerm.valid extended
        (nomConclusion (width := obligation.width) body keptHead
          fun (index : Fin obligation.width) =>
          .const (first + index.val)) := by
  obtain ⟨interp, hsatisfied⟩ := obligation.exists_interp
  refine ⟨interp, ?_, ?_⟩
  · intro clause hclause
    exact valid_extendNomBlock_of_below model first interp clause
      (hsourceBelow clause hclause) (hsourceValid clause hclause)
  · apply nomConclusion_sound (extendNomBlock model first interp)
      obligation interp hsatisfied body keptHead
      (fun index => .const (first + index.val))
    · intro assignment hextendedBody
      apply hbodyMeaning assignment
      intro literal hliteral
      exact (evalL_extendNomBlock_of_below model first interp assignment
        literal (hbodyBelow literal hliteral)).mp
          (hextendedBody literal hliteral)
    · intro hground assignment
      obtain ⟨literal, hliteral, htrue⟩ :=
        hgroundMeaning hground assignment
      exact ⟨literal, hliteral,
        (evalL_extendNomBlock_of_below model first interp assignment
          literal (hheadBelow literal hliteral)).mpr htrue⟩
    · exact extendNomBlock_fresh model first interp

private def conceptAt (concept individual : Nat) : WirePredicate :=
  .concept concept (.constant individual)

private def exampleKey (context : Nat) : WireNominalFiringKey where
  context
  source_body := [.role 0 (.constant 0) (.var (-1))]
  source_head := [.equality (.var (-1)) (.var (-1))]
  side_body := [.concept 0 (.var (-1))]
  side_head := []
  selected := [(0, conceptAt 0 0)]
  substitution := [{ variableId := 0, term := .constant 0 }]

private def exampleSource : WireSourceBinding where
  version := 1
  concept_count := 1
  role_count := 1
  function_count := 0
  individual_count := 1
  source_clauses := []
  role_chains := []
  ontology := []

private def acceptedExample : WireNominalAllocation where
  version := 1
  source := exampleSource
  individual_count := 4
  budget := 3
  allocated := 3
  truncated := false
  blocks :=
    [{ key := exampleKey 0, first := 1, width := 2, body := [], kept_head := [],
       conclusion := { body := [], head :=
         [.equality (.var (-1)) (.constant 1),
          .equality (.var (-1)) (.constant 2)] } },
     { key := exampleKey 1, first := 3, width := 1, body := [], kept_head := [],
       conclusion := { body := [], head :=
         [.equality (.var (-1)) (.constant 3)] } }]

example : acceptedExample.check = .ok true := by native_decide

private def overlappingExample : WireNominalAllocation :=
  { acceptedExample with
    blocks :=
      [{ key := exampleKey 0, first := 1, width := 2, body := [], kept_head := [],
         conclusion := { body := [], head :=
           [.equality (.var (-1)) (.constant 1),
            .equality (.var (-1)) (.constant 2)] } },
       { key := exampleKey 1, first := 2, width := 1, body := [], kept_head := [],
         conclusion := { body := [], head :=
           [.equality (.var (-1)) (.constant 2)] } }] }

private def rejected (result : Except String Bool) : Bool :=
  match result with
  | .error _ => true
  | .ok _ => false

example : rejected overlappingExample.check = true := by native_decide

private def replayedKeyExample : WireNominalAllocation :=
  { acceptedExample with
    blocks :=
      [{ key := exampleKey 0, first := 1, width := 2, body := [], kept_head := [],
         conclusion := { body := [], head :=
           [.equality (.var (-1)) (.constant 1),
            .equality (.var (-1)) (.constant 2)] } },
       { key := exampleKey 0, first := 3, width := 1, body := [], kept_head := [],
         conclusion := { body := [], head :=
           [.equality (.var (-1)) (.constant 3)] } }] }

example : rejected replayedKeyExample.check = true := by native_decide

private def forgedConclusionExample : WireNominalAllocation :=
  { acceptedExample with blocks :=
    [{ key := exampleKey 0, first := 1, width := 2, body := [], kept_head := [],
       conclusion := { body := [], head :=
         [.equality (.var (-1)) (.constant 1)] } },
     { key := exampleKey 1, first := 3, width := 1, body := [], kept_head := [],
       conclusion := { body := [], head :=
         [.equality (.var (-1)) (.constant 3)] } }] }

example : rejected forgedConclusionExample.check = true := by native_decide

private def truncatedExample : WireNominalAllocation :=
  { acceptedExample with truncated := true }

example : rejected truncatedExample.check = true := by native_decide

#print axioms WireNominalAllocation.check_sound
#print axioms WireNominalAllocation.check_family_sound
#print axioms nomConclusion_sound
#print axioms NominalBlock.emitted_conclusion_sound
#print axioms extendNomBlock_fresh
#print axioms valid_extendNomBlock_of_below
#print axioms nomConclusion_exists_extension

end ContextCalculus.CBNominalAllocationWire
