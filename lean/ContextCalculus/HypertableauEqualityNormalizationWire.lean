import ContextCalculus.HypertableauEqualityNormalization
import ContextCalculus.HypertableauWire

/-!
# Executable wire checker for HT equality-premise normalization

Untrusted natural-number representatives and paths are decoded into finite
variables. Every adjacent path pair must be an equality premise (in either
orientation), every variable path must start at that variable and end at its
claimed representative, and every equality premise must map to one
representative. The target clause is then compared with the exact semantic
normal form before a `BodyEqualityNormalization` proof is returned.
-/

namespace ContextCalculus.Hypertableau

open Lean

structure WireClauseNormalization where
  source : WireClause
  representatives : List Nat
  representative_paths : List (List Nat)
deriving FromJson, ToJson, Repr

def decodeVariableVector (variableCount : Nat) (values : List Nat) :
    Except String (Fin variableCount → Fin variableCount) := do
  let decoded ← values.mapM (checkedFin "representative variable" variableCount)
  if h : decoded.length = variableCount then
    return fun index => decoded.get (h.symm ▸ index)
  else
    throw s!"representatives has {decoded.length} entries, expected {variableCount}"

structure CheckedBodyEqualityPath
    (body : List (Atom (Fin variableCount) Concept Role))
    (start finish : Fin variableCount) : Type where
  proof : BodyEqualityPath body start finish

private def buildBodyEqualityPath [DecidableEq Concept] [DecidableEq Role]
    (body : List (Atom (Fin variableCount) Concept Role))
    (start finish : Fin variableCount) :
    List (Fin variableCount) → Except String (CheckedBodyEqualityPath body start finish)
  | [] => throw "equality path is empty"
  | [node] =>
      if hstart : node = start then
        if hfinish : node = finish then
          return ⟨hstart ▸ hfinish ▸ .refl node⟩
        else throw "equality path has the wrong endpoint"
      else throw "equality path has the wrong start"
  | first :: second :: rest => do
      if hstart : first = start then
        let edge : CheckedBodyEqualityPath body first second ←
          if hforward : Atom.eq first second ∈ body then
            pure (CheckedBodyEqualityPath.mk (BodyEqualityPath.premise hforward))
          else if hbackward : Atom.eq second first ∈ body then
            pure (CheckedBodyEqualityPath.mk
              (BodyEqualityPath.symm (BodyEqualityPath.premise hbackward)))
          else
            throw "equality path step is not a body premise"
        let tail ← buildBodyEqualityPath body second finish (second :: rest)
        return ⟨hstart ▸ .trans edge.proof tail.proof⟩
      else
        throw "equality path has the wrong start"

def decodeBodyEqualityPath [DecidableEq Concept] [DecidableEq Role]
    (body : List (Atom (Fin variableCount) Concept Role))
    (start finish : Fin variableCount) (path : List Nat) :
    Except String (CheckedBodyEqualityPath body start finish) := do
  let decoded ← path.mapM (checkedFin "equality-path variable" variableCount)
  buildBodyEqualityPath body start finish decoded

structure CheckedCollapse
    (representative : Fin variableCount → Fin variableCount)
    (body : List (Atom (Fin variableCount) Concept Role)) : Type where
  proof : ∀ left right, Atom.eq left right ∈ body →
    representative left = representative right

private def buildCollapseProof
    (representative : Fin variableCount → Fin variableCount) :
    (body : List (Atom (Fin variableCount) Concept Role)) →
    Except String (CheckedCollapse representative body)
  | [] => return ⟨by simp⟩
  | atom :: tail => do
      let tailProof ← buildCollapseProof representative tail
      match atom with
      | .eq premiseLeft premiseRight =>
          if hpremise : representative premiseLeft = representative premiseRight then
            return ⟨by
              intro left right member
              rcases List.mem_cons.mp member with head | rest
              · cases head
                exact hpremise
              · exact tailProof.proof left right rest⟩
          else
            throw "an equality premise has different representatives"
      | .concept _ _ | .role _ _ _ | .exists_ _ _ _ =>
          return ⟨by
            intro left right member
            rcases List.mem_cons.mp member with head | rest
            · contradiction
            · exact tailProof.proof left right rest⟩

structure CheckedRepresentativePaths
    (body : List (Atom (Fin variableCount) Concept Role))
    (representative : Fin variableCount → Fin variableCount)
    (indices : List (Fin variableCount)) : Type where
  proof : ∀ v, v ∈ indices → BodyEqualityPath body v (representative v)

private def decodePathsFor [DecidableEq Concept] [DecidableEq Role]
    (body : List (Atom (Fin variableCount) Concept Role))
    (representative : Fin variableCount → Fin variableCount)
    (pathFor : Fin variableCount → List Nat) :
    (indices : List (Fin variableCount)) → Except String
      (CheckedRepresentativePaths body representative indices)
  | [] => return ⟨by simp⟩
  | first :: rest => do
      let head ← decodeBodyEqualityPath body first (representative first) (pathFor first)
      let tail ← decodePathsFor body representative pathFor rest
      return ⟨fun v member => by
        rcases List.mem_cons.mp member with equal | member
        · exact equal ▸ head.proof
        · exact tail.proof v member⟩

structure AllRepresentativePaths
    (body : List (Atom (Fin variableCount) Concept Role))
    (representative : Fin variableCount → Fin variableCount) : Type where
  proof : ∀ v, BodyEqualityPath body v (representative v)

private def decodeRepresentativePaths [DecidableEq Concept] [DecidableEq Role]
    (body : List (Atom (Fin variableCount) Concept Role))
    (representative : Fin variableCount → Fin variableCount)
    (paths : List (List Nat)) : Except String
      (AllRepresentativePaths body representative) := do
  if hlength : paths.length = variableCount then
    let pathFor : Fin variableCount → List Nat :=
      fun v => paths.get (hlength.symm ▸ v)
    let proofs ← decodePathsFor body representative pathFor (List.finRange variableCount)
    return ⟨fun v => proofs.proof v (List.mem_finRange v)⟩
  else
    throw s!"representative_paths has {paths.length} entries, expected {variableCount}"

structure DecodedClauseNormalization
    (target : Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)) where
  source : Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)
  proof : BodyEqualityNormalization source target

def WireClauseNormalization.decode
    (wire : WireClauseNormalization) (variableCount conceptCount roleCount : Nat)
    (target : Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)) :
    Except String (DecodedClauseNormalization target) := do
  let source ← wire.source.decode variableCount conceptCount roleCount
  let representative ← decodeVariableVector variableCount wire.representatives
  let representativePath ←
    decodeRepresentativePaths source.body representative wire.representative_paths
  let collapsesPremise ← buildCollapseProof representative source.body
  let expectedBody :=
    (source.body.filter fun atom => !atom.isEquality).map (Atom.rename representative)
  let expectedHead := source.head.map (Atom.rename representative)
  if hbody : target.body = expectedBody then
    if hhead : target.head = expectedHead then
      return {
        source
        proof := {
          representative
          representative_path := representativePath.proof
          collapses_premise := collapsesPremise.proof
          target_body := hbody
          target_head := hhead
        }
      }
    else
      throw "normalized clause head does not match the checked representative map"
  else
    throw "normalized clause body does not match the checked representative map"

structure DecodedOntologyNormalization
    (target : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))) where
  source : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))
  proof : OntologyEqualityNormalization source target

def decodeOntologyNormalization
    (variableCount conceptCount roleCount : Nat) :
    List WireClauseNormalization →
    (target : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))) →
    Except String (DecodedOntologyNormalization target)
  | [], [] => return ⟨[], .nil⟩
  | wire :: wires, targetClause :: targets => do
      let head ← wire.decode variableCount conceptCount roleCount targetClause
      let tail ← decodeOntologyNormalization variableCount conceptCount roleCount wires targets
      return ⟨head.source :: tail.source, .cons head.proof tail.proof⟩
  | _, _ => throw "normalization clause count does not match the target ontology"

def WireClauseNormalization.checkAgainst
    (wire : WireClauseNormalization) (variableCount conceptCount roleCount : Nat)
    (target : WireClause) : Except String Bool := do
  let decodedTarget ← target.decode variableCount conceptCount roleCount
  let _ ← wire.decode variableCount conceptCount roleCount decodedTarget
  return true

section Tests

private def rejected : Except String Bool → Bool
  | .error _ => true
  | .ok _ => false

private def sourceClause : WireClause where
  body := [
    .eq 0 1,
    .eq 1 2,
    .concept { concept := 0, neg := false } 2
  ]
  head := [.concept { concept := 1, neg := false } 1]

private def targetClause : WireClause where
  body := [.concept { concept := 0, neg := false } 0]
  head := [.concept { concept := 1, neg := false } 0]

private def validNormalization : WireClauseNormalization where
  source := sourceClause
  representatives := [0, 0, 0]
  representative_paths := [[0], [1, 0], [2, 1, 0]]

example : validNormalization.checkAgainst 3 2 0 targetClause = .ok true := by
  native_decide

private def disconnectedPath : WireClauseNormalization :=
  { validNormalization with representative_paths := [[0], [1, 0], [2, 0]] }

example : rejected (disconnectedPath.checkAgainst 3 2 0 targetClause) = true := by
  native_decide

private def splitRepresentatives : WireClauseNormalization :=
  { validNormalization with
    representatives := [0, 0, 2]
    representative_paths := [[0], [1, 0], [2]] }

example : rejected (splitRepresentatives.checkAgainst 3 2 0 targetClause) = true := by
  native_decide

private def wrongTarget : WireClause :=
  { targetClause with head := [.concept { concept := 1, neg := false } 1] }

example : rejected (validNormalization.checkAgainst 3 2 0 wrongTarget) = true := by
  native_decide

end Tests

end ContextCalculus.Hypertableau
