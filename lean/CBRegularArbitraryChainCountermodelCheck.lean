import ContextCalculus.CBRegularArbitraryChainCountermodelWire

open Lean ContextCalculus ContextCalculus.CBTermWire
open ContextCalculus.CBRegularArbitraryChainCountermodelWire

structure WireCountermodelDocument where
  concept_count : Nat
  role_count : Nat
  function_count : Nat
  individual_count : Nat
  source : List WireClause
  sub : Nat
  sup : Nat
  countermodel : WireRegularArbitraryChainCountermodel
deriving FromJson

#print axioms DecodedRegularArbitraryChainCountermodel.refutes

def WireCountermodelDocument.check (wire : WireCountermodelDocument) : Except String Bool := do
  let bounds : Bounds := {
    concepts := wire.concept_count
    roles := wire.role_count
    functions := wire.function_count
    individuals := wire.individual_count }
  let source ← wire.source.mapM (WireClause.decode bounds)
  let _ ← wire.countermodel.decode bounds source wire.sub wire.sup
  return true

def checkFile (path : System.FilePath) : IO UInt32 := do
  try
    let input ← IO.FS.readFile path
    let result : Except String Bool := do
      let json ← Json.parse input
      let document : WireCountermodelDocument ← fromJson? json
      document.check
    match result with
    | .ok true =>
        IO.println "regular arbitrary-chain CB countermodel accepted"
        return (0 : UInt32)
    | .ok false =>
        IO.eprintln "regular arbitrary-chain CB countermodel rejected"
        return (1 : UInt32)
    | .error error =>
        IO.eprintln s!"regular arbitrary-chain CB countermodel rejected: {error}"
        return (1 : UInt32)
  catch error =>
    IO.eprintln s!"regular arbitrary-chain CB countermodel read error: {error}"
    return (2 : UInt32)

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => checkFile path
  | _ => do
      IO.eprintln "usage: cb-regular-arbitrary-chain-countermodel-check CERTIFICATE.json"
      return (2 : UInt32)
