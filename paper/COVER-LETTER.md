# Cover letter: Semantic Web Journal Full Paper

Dear Editors-in-Chief,

Please consider our manuscript, “Kobayashi-MaRust 1.3: A Proof-Carrying Hybrid
OWL Reasoner and an Agentic, Verification-Centred Development Method,” as a
Full Paper in the *Semantic Web Journal*.

The manuscript makes two connected contributions. First, it presents and
evaluates Kobayashi-MaRust (KM), an open-source hybrid OWL 2 DL classifier that
combines EL completion, consequence-based saturation, and
complete-answer-or-defer hypertableau procedures behind an automatic
source-feature router. Second, it reconstructs the human-directed agentic
engineering process that produced the reasoner. Exact-artifact benchmark
falsification, isolated candidate integration, and source-bound Lean
publication checks constrained that process. The methodological claim is not
that language-model output is inherently reliable. It is that explicit gates
made proposed changes inexpensive to reject and prevented insufficiently
supported results from being published.

We believe this work fits the Full Paper category because it contributes a
reasoner architecture, its formal publication boundary, a substantial
empirical evaluation, and an evidence-backed software-engineering method. The
evaluation includes the historical ORE 2015 regression panel, a prospectively
frozen 2026 OBO Foundry panel, named biomedical hard cases, and eight pinned
reasoner families. It uses process-tree resource limits, full-IRI semantic
comparisons, exact source and artifact identities, incremental scale checks,
and explicit adjudication of disagreements. The paper separates
profile-limited evidence from OWL 2 DL evidence and does not treat any single
reasoner as an infallible oracle.

KM grew out of our Moose and subsequent Baobab research in neuro-symbolic
ontology reasoning. Both lines of work led to published or accepted papers,
including Moose at ISWC. The present manuscript makes a distinct contribution:
it develops the reasoning infrastructure into a standalone, evaluated,
proof-carrying OWL reasoner and studies the development process itself.

The source code is available under the BSD 3-Clause licence at
<https://github.com/bio-ontology-research-group/kobayashi-marust>, with the
evaluated software identified by tag `v1.3.0`. We have prepared a
digest-verified replication package containing the manuscript source and PDFs,
tagged software, corpus and artifact manifests, redistributable inputs and
references, complete result records, validation and disagreement evidence,
proof-gate logs, privacy-preserving agent-process telemetry, exact commands,
and a top-level replication README. Immediately before submission, we will
synchronize the final GitHub release to Zenodo, freeze the package, and add its
DOI and stable URL to the manuscript and submission metadata.

Two planned inputs were unavailable at the evaluation cutoff. SNOMED CT is
licensed, and no licensed release was available to the authors; it therefore
does not enter the reported hard-case results or artifact. BioPortal
programmatic downloads required an API key that was unavailable at the
cutoff. The predeclared sampling protocol and candidate-freeze machinery are
retained, but no BioPortal result enters an aggregate. The public package
contains no credential, private conversation body, restricted ontology
payload, or private workstation identifier. Benchmark compute-node identifiers
are retained only where they form part of scheduler provenance.

OpenAI Codex and Anthropic Claude coding-agent interfaces were used
substantively during software and proof development. They are not authors. The
manuscript reports their roles, available native usage telemetry, attribution
limits, and the human authors’ responsibility for objectives, integration,
evidence interpretation, and every published claim.

This work was supported by King Abdullah University of Science and Technology
(KAUST) through the KAUST Center of Excellence for Generative AI, award 5940
(`FCC/1/5940-07-02`); baseline funding `BAS/1/1659-01-01`; the KCSH theme
allocation `FCC/1/5932-11-01`; and the KCSH student general-ledger allocation
`FCC/1/5932-12-10`.

The manuscript is original, has not been published previously, and is not
under review elsewhere. The authors declare no competing interests. We would
welcome assignment to a handling editor with expertise in Semantic Web
reasoning, description logics, ontology engineering, or formal verification.

Thank you for your consideration.

Sincerely,

Robert Hoehndorf
King Abdullah University of Science and Technology (KAUST)
robert.hoehndorf@kaust.edu.sa
