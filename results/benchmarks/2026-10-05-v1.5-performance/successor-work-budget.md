# Bound successor visits without reported updates

ORE 15167 has a successor-extension notification cycle. Copy-dependent nodes
repeatedly enqueue each other while both ALL and FUNCTIONAL callbacks return
false. The ordinary saturation deadline eventually interrupts this loop, but
shortening that deadline globally damages productive passes on other inputs.

The driver now gives each successor-queue invocation an allowance of
`max(4096, 64 * saturation_node_count)` visits without a reported extension
update. An update returns immediately and the next invocation gets a fresh
allowance. Exhaustion with pending work returns an explicit unfinished result;
the bridge discards the pass and performs exact completion. Queue exhaustion
on the final allowed visit remains a normal drain.

This is a scheduling heuristic, not a proof that a repeated state forms a cycle.
Callbacks can change bookkeeping without reporting an extension update. The
threshold therefore cannot justify a SAT verdict or reuse of a partial label
set. Safety comes from discarding the unfinished pass and using the existing
exact completion path. No inference rule or completed saturation result is
changed. The normal wall-time budget remains in place.

All 1,473 hypertableau tests passed, with seven ignored tests. Regression checks
cover a cyclic qualified notification, preservation of pending work at a zero
allowance, and successful draining at the allowance boundary. The relevant
checks are included in the hypertableau certification gate.

With one CPU and the default saturation budget, the previous optimized binary
does not complete ORE 15167 within the 15-second local diagnostic bound. The new
diagnostic build completes in 0.40 seconds and agrees with Konclude, HermiT,
Openllet, and JFact. Its trace explicitly reports the successor work limit and
discard of the unfinished pass. ORE 1028 and 11629 both complete and agree with
Konclude without discarding their productive saturation passes.

These observations are bounded diagnostics across different build profiles,
not a release performance comparison. Optimized-build verification and all four
exact-source certification gates are tracked in
`successor-work-budget-work-state.json`. The full audit 53309442 uses the earlier
binary without this work limit and must remain unchanged. A separate diagnostic
job, 53309995, profiles 37 remaining worker-timeout cases to guide coverage work;
that subset is never an acceptance benchmark.
