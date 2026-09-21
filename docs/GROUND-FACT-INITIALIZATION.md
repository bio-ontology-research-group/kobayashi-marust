# Universal facts on named individuals

An empty-body normalized clause still quantifies its central variable. Keeping
only its x-shaped copy in the nominal ground context misses consequences at
named individuals. For example, `Top <= {a}`, `X(a)` and `not X(b)` are jointly
inconsistent. The previous CB path returned consistent. Adding the source's
empty-body instances at a and b makes the existing rules derive the clash.

The candidate indexes empty-body clauses whose heads depend on x, including
mixed heads such as `R(x,a)`. Each named individual entering the ground context
receives the corresponding instances. The original clauses remain unchanged.
Retained insertion also schedules instances of newly added universal facts.
There is no unique-name assumption: equality between individuals remains the
responsibility of the existing equality rules.

Every added clause carries zero-premise Hyper evidence: its source index,
substitution and instantiated source. This uses the existing source-bound
certificate format. `CBGroundFactInstantiation.lean` proves that adding these
source instances preserves exactly the original models, and derives seed
soundness from the existing Hyper checker. The certification surface imports
and audits both results; their only dependencies are Lean's standard
`propext` and `Quot.sound`.

This is an unpromoted candidate. Runtime tests, concrete certificate acceptance,
the complete release gates and corpus correctness/performance checks remain
required. The additional ground clauses may increase memory on large ABoxes;
resource-limited runs must continue to decline rather than publish partial
closure.
