# Fast-reference coverage failures

The completed dense-data sweep has 46 verified Konclude successes that KM did
not verify, alongside eight KM successes outside Konclude's verified set.
It needs 39 net additional verified successes to exceed Konclude's total.
The full single-worker sweep remains the authoritative next candidate run;
this diagnostic does not replace any of its failures or alter its corpus.

Job 53326865 profiles the eight missing cases with the lowest Konclude time:
1342, 8666, 14379, 8250, 12566, 13799, 6272 and 2182. It uses the exact same
binary and flags as the single-worker sweep, with timing and progress tracing
added. Limits remain 240 seconds, 20 GiB and one CPU. Traced runtimes are not
release performance measurements. Completed outputs, if any, need independent
answer auditing before counting as verified.

Initial live traces from the first four tasks narrow the next investigations:

- 1342 selects the nominal route after about 0.01 seconds of frontend work.
- 8666 reaches a typed bridge with 125 nominals, but the datatype vocabulary
  guard declines and its HT worker exits unsuccessfully at about 0.05 seconds.
- 14379 declines native HT conversion because ABox conversion is incomplete,
  then selects the nominal route after about 0.03 seconds.
- 8250 completes its rules-consistency worker successfully at about 0.07
  seconds, but the classification process remains running afterward. That
  trace rules out consistency as the dominant cost for this specific case.

Earlier job 53309995 supplies a precise datatype lead for two later tasks.
The typed input for 12566 contains decimal literals such as
`__dt__val__"12"^^xsd:decimal`. The current atomic-family function admits the
decimal range but excludes decimal-typed literal values. This is an admission
boundary, not evidence that accepting those values without further proof is
sound. Exact numeric identity and relation evidence still need checking.

For 13799 the source includes both `SurfaceArchitectureElement <= forall
hasMass.__dt__float` and the global range `Top <= forall hasMass.__dt__float`,
with analogous int restrictions on hasYearOfLaunch. The local universal is
redundant given the global range, yet the source occurrence collector accepts
the global form and rejects the local form. Its diagnostic says non-atomic
filler even though the filler is atomic. The downstream role-use guard already
recognizes atomic Forall. This identifies a concrete guard mismatch to test;
it does not establish that changing that guard alone completes the ontology.
The new profiles must confirm the current candidate reaches the same boundary.

No production admission or reasoning code changes accompany this diagnostic.
The next change must preserve exact datatype semantics and the Lean boundary,
then pass independent real-ontology answer comparisons and the full corpus.
