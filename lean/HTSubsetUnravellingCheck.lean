import ContextCalculus.HypertableauSubsetUnravelling

open Lean
open ContextCalculus.Hypertableau

/-! Executable checker for subset-blocked production terminals of the native
hypertableau (`KM_HT_SUBSET_MODEL_CERT`). Acceptance means, by
`WireSubsetUnravelling.check_sound`, that the unravelled terminal is a finite
model of the certificate's ontology whose root satisfies the query seed. -/

def checkFile (path : System.FilePath) : IO UInt32 := do
  try
    let input ← IO.FS.readFile path
    let result : Except String Bool := do
      let json ← Json.parse input
      let document : WireSubsetUnravelling ← fromJson? json
      document.check
    match result with
    | .ok true =>
        IO.println "HT subset unravelling accepted"
        return (0 : UInt32)
    | .ok false =>
        IO.eprintln "HT subset unravelling rejected: a fold is not a subset pair or the unravelled model fails"
        return (1 : UInt32)
    | .error error =>
        IO.eprintln s!"HT subset unravelling rejected: {error}"
        return (1 : UInt32)
  catch error =>
    IO.eprintln s!"HT subset unravelling read error: {error}"
    return (2 : UInt32)

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => checkFile path
  | _ => do
      IO.eprintln "usage: ht-subset-unravelling-check CERTIFICATE.json"
      return (2 : UInt32)
