import ContextCalculus.HypertableauSourceBoundNativeABoxWire

open Lean
open ContextCalculus.Hypertableau

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => do
      try
        let input ← IO.FS.readFile path
        let result : Except String Bool := do
          let json ← Json.parse input
          let document : WireSourceBoundNativeABoxGlobal ← fromJson? json
          return document.check
        match result with
        | .ok true => do IO.println "HT source-bound native ABox global accepted"; return (0 : UInt32)
        | .ok false => do IO.eprintln "HT source-bound native ABox global rejected"; return (1 : UInt32)
        | .error error => do IO.eprintln s!"HT source-bound native ABox global rejected: {error}"; return (1 : UInt32)
      catch error =>
        IO.eprintln s!"HT source-bound native ABox global read error: {error}"
        return (2 : UInt32)
  | _ => do
      IO.eprintln "usage: ht-source-bound-native-abox-global-check CERTIFICATE.json"
      return (2 : UInt32)
