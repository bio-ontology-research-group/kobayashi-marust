# Task: fix GitHub issue #4 in the KM OWL 2 DL reasoner (Rust)

You work in the git worktree that is your current directory
(/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/worktrees/fix-issue4-utf8,
branch fix/v154-issue4-utf8, based on development/v1.5.4). Edit, build, test and commit only here.

## The issue (opened 2026-10-28 by an external user, KM v1.5.3)
`km classify qudt-merged.ttl` panics:

    thread 'main' panicked at .../horned-owl-1.4.0/src/io/ofn/writer/as_functional.rs:17:23:
    end byte index 4 is not a char boundary; it is inside '°' (bytes 3..5 of string)

Input: https://purl.allotrope.org/voc/qudt/REC/2022/09/qudt-merged.ttl

KM reads Turtle/RDF/OWL-XML with horned-owl and converts it to OWL functional syntax using
horned-owl's OFN writer (see engine/src/orchestrate/input.rs and engine/src/orchestrate/features.rs).
That writer slices a string by byte index and panics on multi-byte UTF-8 characters.

## Rules
- Build and test on this machine. Never run `ssh ws`.
- Always build with `CARGO_TARGET_DIR=$PWD/engine/target nice cargo build --release` (run cargo from engine/).
- Never push. Never touch other worktrees or branches.
- Kill processes by PID, never with `pkill -f`.
- Wrap runs of the reproducer in `timeout 600`.
- Keep scratch files in /tmp/claude-1000/-home-leechuck--herdr-worktrees-kobayashi-marust-worktree-paper/0285edda-d83d-4be5-8ecb-bb0aeb5575cb/scratchpad/pi/issue4/ and nowhere else in /tmp.
- Do not delete files you did not create.

## Steps
1. Download the input into the scratch directory with curl and reproduce the panic with
   engine/target/release/km classify. Record the exact panic.
2. Find the exact cause: read as_functional.rs:17 in the vendored horned-owl source
   (~/.cargo/registry/src/*/horned-owl-1.4.0/src/io/ofn/writer/as_functional.rs) and work out
   which KM call reaches it and which string (an IRI, a literal, a prefix) holds the multi-byte
   character.
3. Fix it generally, for any non-ASCII text, not only '°'. Preferred order:
   (a) avoid the faulty code path in KM, for example by writing that construct ourselves or by
   passing the writer input it handles correctly, as long as the output is exactly equivalent OWL;
   (b) otherwise a minimal patch of horned-owl, through a `[patch.crates-io]` entry pointing at a
   vendored copy inside this repository. Keep the change minimal and document it.
   Never drop or alter axioms to avoid the panic. The output must preserve every IRI and literal
   exactly, character for character.
4. Add a regression test under engine/tests/ with a small Turtle input containing non-ASCII
   characters in IRIs, literals and annotations (for example '°', 'µ', 'é', an emoji). Check that
   classification succeeds and that the classified taxonomy equals the one obtained from an
   equivalent hand-written OWL functional-syntax file.
5. Run the full reproducer: `km classify` on qudt-merged.ttl must finish without a panic.
   Report the time, CONSISTENT, DROPPED and the number of SUB lines. If the run is slow, report
   that and do not try to optimise.
6. Run these test suites and report their exact `test result` lines:
   - `cargo test --release --lib orchestrate::input`
   - `cargo test --release --lib frontend::`
   - the integration tests whose names contain rdf, owlxml, turtle or input
     (find them with `ls engine/tests`)
7. Commit with a message that ends with this line:
   Co-Authored-By: kimi-k2.7-code via pi-opencode <noreply@opencode.ai>

## Final report
- the root cause, with file:line;
- the fix and why the output is exactly equivalent;
- the reproducer result;
- the exact test results;
- the commit hash;
- anything unresolved.
Say clearly which statements you verified by running something and which you inferred.
