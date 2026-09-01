# Independent Fable review briefs

Run every numbered brief in a separate Claude Code/Fable context. A reviewer
must inspect `paper/main.tex` and only the additional files named in its brief.
Reviewers do not edit repository files. Each report identifies locations by
section, paragraph opening, citation key, or line number; separates major from
minor findings; and avoids reviewing aspects assigned to another brief.

Run these in three batches (1--3, 4--6, then 7), never exceeding the three
simultaneous Fable-agent limit. Archive each report separately under
`.work/artifacts/paper-reviews/` and record the manuscript SHA-256 reviewed.

## 1. Overall structure

Act as a senior Semantic Web Journal or Journal of Automated Reasoning editor.
Review only the manuscript's macrostructure: contribution framing, section
order, balance between the system/evaluation and Methods contributions,
duplicated or misplaced material, and whether the conclusion answers the
research questions. Assess venue fit. Propose a revised outline only when it
materially improves the argument. Do not review transitions, prose, terms, or
citations.

## 2. Section and paragraph flow

Review only argumentative continuity. Check every section-to-section and
paragraph-to-paragraph transition, whether each paragraph has a clear role,
whether claims appear before their support, and whether forward/backward
references guide the reader. Identify abrupt topic shifts, buried premises,
and redundant recapitulation. Supply replacement transitions for the most
important failures. Do not redesign the outline or conduct a style review.

## 3. Clarity

Review only semantic clarity for an interdisciplinary SWJ/JAR readership.
Flag ambiguous antecedents, underspecified claims, unexplained assumptions,
overloaded sentences, unclear notation, missing subjects or comparison sets,
and places where a reader cannot tell what was measured or proved. Propose
precise replacement wording for high-impact findings. Do not review elegance,
tone, acronym introduction, structure, or citation accuracy.

## 4. Writing style

Review only prose style and consistency. Check active voice, concision,
sentence rhythm, paragraph length, repetition, hedging, promotional language,
and the repository's writing rules: no em dashes and avoid “thus”, “uniquely”,
“comprehensive”, “rigorous”, and “robust”. Identify mechanical or awkward
phrasing and suggest concise revisions. Do not assess technical clarity,
terminology introduction, structure, or sources.

## 5. Acronyms, notation, and technical terms

Audit every acronym, abbreviation, symbol, description-logic constructor,
system component, benchmark term, and specialised software-engineering or
formal-methods term. Verify expansion or explanation at first use,
consistency thereafter, notation scope, and suitability for readers outside
the immediate subfield. Produce a complete issue list and a short glossary
recommendation if one is warranted. Do not rewrite prose beyond the words
needed to repair an introduction.

## 6. Related work and state of the art

Read `paper/main.tex` and `paper/references.bib`. Review only coverage and
positioning of related work. Check current and foundational OWL reasoners,
consequence-based and hypertableau calculi, ORE and current biomedical
benchmarks, formal verification of reasoners, incremental/explanation work,
and agentic software engineering. In particular assess the treatment of
Konclude, ELK and ELK successors, HermiT, JFact/FaCT++, Openllet/Pellet, MORe,
Sequoia, and Lean-assisted development. Recommend missing primary work and
explain exactly which comparison it enables. Do not verify BibTeX metadata or
perform a prose review.

## 7. Citation support and bibliographic accuracy

Read `paper/main.tex`, `paper/references.bib`, and `paper/citation-audit.tsv`.
Audit every citation occurrence and every bibliography entry. Verify that the
cited source supports the surrounding claim and that authors, title, venue,
year, volume, issue, pages, DOI, and URL are accurate. Prefer primary sources
and official specifications. Explicitly distinguish verified records,
unsupported claims, metadata errors, and sources that cannot be checked.
Supply BibTeX-ready corrections. Do not assess whether the related-work
section covers enough topics; that belongs to review 6.
