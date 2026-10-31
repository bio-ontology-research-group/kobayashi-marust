# Lean proofs of the Boolean data ranges and ordered cells (agent `lean-data-ranges`)

2026-10-31, branch `fix/v155-lean-data-ranges` off `development/v1.5.5`
(aacd11cb). No Rust change. Statements, hypotheses and the one gap:
`docs/DATATYPES.md`, "Lean coverage of Boolean ranges and cells
(2026-10-31, agent `lean-data-ranges`)".

## Modules (`lean/ContextCalculus/`)

| module | imports | main theorems |
|---|---|---|
| `DataRangeBoolean.lean` | core (`TwoSortedDL`) | `defClauses_iff`, `labels_agree`, `realizes_of_atomic`, `extends_to_clause_model`, `owl_satisfies_clauses`, `clause_model_boolean` |
| `DataRangeCells.lean` | `Mathlib.Data.Set.Card`, `DataValueSingletonElision`, `DataRangeBoolean`, `DataRangeStrings` | `fresh_values`, `fresh_realizes`, `value_realizes`, `cell_node_realizable`, `undecidedRealizable_of_cells`, `laminar_realizable`, `owl_satisfies_cell_clauses`, `string_residue_infinite`, `string_chain_pairwise` |
| `DataRangeStrings.lean` | core (`DataValueSingletonElision`) | `oracleDec_sound`, `chain_sub`, `chain_strict`, `language_sub_NCName`, `Name_sub_NMTOKEN`, `dateTimeStamp_sub_dateTime`, `hex_b64_disjoint`, `step_family`, `step_avoids_inner`, `rustMember_sound` |
| `DataRangeDecimalBands.lean` | Mathlib (reals, irrationals, integer intervals) | `int_band_encard`, `decimal_band_infinite`, `rational_band_infinite`, `real_band_infinite` |

All four are imported by `lean/ContextCalculus.lean`. `axioms.txt` is the
`#print axioms` output for every theorem in the table (`propext`,
`Classical.choice`, `Quot.sound` at most); `Axioms.lean` is the file that
prints it (`lake env lean Axioms.lean` from `lean/`).

## Lean build

`lean/.lake/packages` is a hard-link copy (`cp -al`) of
`.work/worktrees/checkers-on/lean/.lake/packages`. A plain `lake build`
fails at once with ENOMEM (`vm.overcommit_memory = 2`), as for
`lean-data-values`; the library was therefore built by import level, four
modules per `lake build` call (`levelbuild.py`, copied from
`.work/agent-scratch/lean-data-values/`), and then confirmed with a plain
`lake build` (see `build.txt` for the job count and the absence of
`sorry`). The new modules need only Mathlib modules that were already
built in the shared package; nothing in the package was rebuilt.

## Probes

`probes/string_ctrl*.ofn`: a string literal with the character U+0001
(outside the XML character set), as a plain literal, as `xsd:string` and
in a TBox `DataHasValue`. They check the side condition of
`rustMember_sound` (the oracle sees only strings of XML characters).
`probes-output.txt`: `km-dv3g classify` (data-values-3 final binary,
`.work/agent-scratch/data-values-3/bin/km-dv3g`, sha256 prefix
`5ce5f7c80809d861`, source 20057f0f) exits 2 with "literal contains a
character outside the XML character set" on all three; the HermiT oracle
(`.work/agent-scratch/data-values/oracle`) throws
`MalformedLiteralException` on all three. No gold answer exists, so the
differential runner was not used.

## Tests

No Rust was changed, so no cargo suite was run. The Lean modules are the
tests: each builds without `sorry` and with standard axioms only.
