import ContextCalculus.CBTypedRegularArbitraryChainCountermodelWire

open Lean ContextCalculus
open ContextCalculus.CBSourceWire
open ContextCalculus.CBRegularArbitraryChainCountermodelWire
open ContextCalculus.CBTypedRegularArbitraryChainCountermodelWire

structure WireDocument where
  source : WireSourceBinding
  sub : Nat
  sup : Nat
  countermodel : WireRegularArbitraryChainCountermodel
deriving FromJson

def main (args : List String) : IO UInt32 := do
  let path ← match args with
    | [path] => pure path
    | _ =>
        IO.eprintln "usage: cb-typed-regular-arbitrary-chain-countermodel-check FILE"
        return (2 : UInt32)
  try
    let text ← IO.FS.readFile path
    let result : Except String Unit := do
      let json ← Json.parse text
      let wire : WireDocument ← fromJson? json
      let source ← wire.source.decode
      let decoded ← WireRegularArbitraryChainCountermodel.decodeTyped
        source wire.sub wire.sup wire.countermodel
      let _ := decoded.refutesProduction
      pure ()
    match result with
    | .ok () =>
        IO.println "typed regular arbitrary-chain CB countermodel accepted"
        return (0 : UInt32)
    | .error message =>
        IO.eprintln s!"typed regular arbitrary-chain CB countermodel rejected: {message}"
        return (1 : UInt32)
  catch error =>
    IO.eprintln s!"typed regular arbitrary-chain CB countermodel read error: {error}"
    return (2 : UInt32)
