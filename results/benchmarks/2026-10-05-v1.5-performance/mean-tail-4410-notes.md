# Largest shared-runtime gaps

On the completed IRI-cache diagnostic sweep, the 1,609 jointly verified inputs
cost KM 5,723 seconds more than Konclude in total. The largest 20 differences
account for 2,057 seconds. This is an attribution target, not a paired speedup
measurement; the diagnostic build profile differs from production.

4410 is the largest difference: 190.293 seconds versus Konclude's 3.758.
A bounded local route probe against the unmodified 45,114,936-byte source
confirms automatic routing selects nominals. Explicit ht_bridge refuses all
9,343 data-property assertions before reasoning. Explicit ground-source
compilation then refuses at its hard-coded 4 MiB development size bound.
No result from these diagnostic probes is counted as solved.

The source has 147,118 object-property assertions, 6,033 class assertions,
9,343 data-property assertions, and only 21 subclass axioms. A line-level
literal suffix inventory finds 7,739 xsd:string assertions and 1,604 untyped
or language-tagged assertions. This inventory does not prove full admission,
but directs the next test toward scalable source conversion rather than URI
literal support.

Both the automatic source scheduler and ground-source compiler have a 4 MiB
cost bound. The scheduler also bounds assertion and individual counts. Do not
remove those bounds and call the ontology solved: a larger-source diagnostic
must retain process limits and complete compiler/bridge admission, and its
answer must pass the independent taxonomy audit.

Source inspection also identifies a potential quadratic cost in assertion
alias allocation: each new distinct value restarts its unused-name search at
zero. A monotone cursor could preserve exactly the same generated names while
avoiding repeated searches, but this requires a before/after source-output
comparison and targeted collision controls before use.
