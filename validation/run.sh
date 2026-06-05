#!/usr/bin/env bash
# Validate the actual Rust reasoner's verdicts against the Lean-verified checker.
#
# For each input ontology this:
#   1. runs the real Rust engine (the `kobayashi-marust` binary),
#   2. independently re-derives every reported verdict from the genuine premises
#      (engine output is never assumed as an axiom; see engine/py/certgen_term.py),
#      emitting a Lean file under lean/Validation/,
#   3. has the Lean kernel re-check each certificate via the proven checker.
#
# A green `lake build Validation` means every emitted verdict is a machine-checked
# theorem: the verified checker confirms the reasoner's output is entailed.
#
# The hand-authored JSON inputs run standalone.  The `.ofn` inputs additionally
# need the (separate) `moose` package for the OWL front-end -- set MOOSE_HOME or
# place moose as a sibling of this repo.  When moose is absent those steps are
# skipped and the checked-in `.ofn`-derived proofs are still re-verified.
set -euo pipefail

# Deterministic certificate generation (frozenset iteration order), so a re-run
# reproduces the checked-in proofs byte-for-byte.
export PYTHONHASHSEED=0

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
CRATE="$ROOT/engine"
LEANDIR="$ROOT/lean"
INPUTS="$ROOT/validation/inputs"
ONTOS="$ROOT/examples/ontologies"
OUTDIR="$LEANDIR/Validation"

echo "== building the Rust engine =="
( cd "$CRATE" && cargo build --release )

mkdir -p "$OUTDIR"

gen () {
  local name="$1" file="$2" mod="$3"
  echo "== $name =="
  python3 "$CRATE/py/certgen_term.py" "$name" "$file" "$OUTDIR/$mod.lean"
}

# hand-authored normalised inputs, one per rule class (standalone)
gen disj      "$INPUTS/disj.json"      Disj        # disjunctive subsumption
gen disjoint  "$INPUTS/disjoint.json"  Disjoint    # disjointness ⊥
gen hierarchy "$INPUTS/hierarchy.json" Hierarchy   # class hierarchy
gen exists    "$INPUTS/exists.json"    Exists      # ∃R / value restriction (Succ)
gen numrestr  "$INPUTS/numrestr.json"  Numrestr    # number restrictions (Eq/Factor)
gen paramod   "$INPUTS/paramod.json"   Paramod     # paramodulation into a literal
gen disjsucc  "$INPUTS/disjsucc.json"  Disjsucc    # disjunction × successor (complete engine)

# real .ofn ontologies via the OWL front-end (needs the moose package)
if ( cd "$CRATE/py" && python3 -c "import frontend" >/dev/null 2>&1 ); then
  gen trans_test   "$ONTOS/trans_test.ofn"   Transtest    # nested successors (A ⊑ D)
  gen kinship      "$ONTOS/kinship.ofn"      Kinship      # 21 subs incl. nominal
  gen forall_intro "$ONTOS/forall_intro.ofn" ForallIntro  # ∀-introduction (A ⊑ B)
else
  echo "== .ofn front-end skipped (moose not found): re-verifying checked-in"
  echo "   Transtest.lean / Kinship.lean / ForallIntro.lean instead. Set MOOSE_HOME to regenerate."
fi

echo "== kernel-checking all certificates (lake build Validation) =="
( cd "$LEANDIR" && lake build Validation )
echo "OK: every reasoner verdict above is a kernel-checked theorem."
