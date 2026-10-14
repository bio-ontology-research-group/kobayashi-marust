# ORE 15167 successor-extension deadline

The one-second saturation cap previously did not interrupt ORE 15167. A bounded
trace observed more than eight million queue visits in twelve seconds. Nodes
71, 92, and 69 repeatedly re-entered the queue while both ALL and FUNCTIONAL
extension callbacks reported no structural update. The driver only checked its
deadline outside this queue loop.

The repair passes the existing saturation deadline into the successor queue
loop. Expiry leaves pending work queued. The enclosing driver detects remaining
work and returns an unfinished result. The initial repair retained extracted
labels for scheduling. Subsequent full-corpus testing exposed that extraction
also promoted unfinished node statuses to complete verdicts. The follow-up
guard discards the entire interrupted pass before verdict extraction and runs
exact completion without those labels or saturation coupling.
The existing deadline value and default route are
unchanged. No calculus rule, label, or successful saturation result is altered.
Callbacks themselves are not preempted; this repair addresses the observed
between-callback queue cycle.

Regression coverage includes an already-expired deadline that leaves the queue
unchanged and two copy-dependent nodes that continuously forward a qualified
cardinality notification to each other. The latter must return with pending
work when its deadline expires.

`check_successor_deadline.py` runs the explicit bridge and automatic routes with
a one-second saturation cap, then compares source-bound consistency and full-IRI
taxonomies against Konclude, HermiT, Openllet, and JFact. These are bounded local
diagnostics, not release performance results. The unrestricted default-budget
case and full-corpus release targets require separate measurement.

The first deadline-only check exposed stale terminology references after the
partial graph was freed. Completion's OR branch ordering reads saturation clash
references independently of the cache setting, so it dereferenced a removed
node. Context-level cleanup now detaches every saturation concept reference
before releasing the graph. A completion regression test exercises both positive
and negative references before and after release.
