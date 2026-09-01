LATEX = pdflatex
REPO_COMMON = $(shell dirname "$$(git rev-parse --path-format=absolute --git-common-dir)")

.PHONY: all clean history milestones agent-evidence agent-usage laptop-evidence incremental disagreement-witnesses stato-adjudication uo-witness ore current-tables km-causes route-glossary citation-occurrences manuscript-contract checks submission-audit

all: main.pdf

history:
	python3 scripts/extract_history.py

milestones:
	python3 scripts/render_method_milestones.py

agent-evidence:
	python3 scripts/extract_agent_sessions.py

agent-usage:
	python3 scripts/render_agentsview_usage.py

laptop-evidence:
	python3 scripts/import_laptop_evidence.py

incremental:
	python3 benchmark/render_incremental_v13.py

submission-audit:
	python3 scripts/audit_submission_readiness.py

manuscript-contract:
	python3 scripts/verify_manuscript_contract.py

disagreement-witnesses:
	python3 benchmark/verify_disagreement_witnesses.py \
	  --ledger benchmark/disagreement-evidence.tsv \
	  --evidence-root benchmark/generated/disagreement-evidence \
	  --output benchmark/generated/disagreement-witness-verification.json

stato-adjudication:
	python3 benchmark/verify_stato_adjudication.py \
	  --evidence-root benchmark/generated/disagreement-evidence/stato \
	  --output benchmark/generated/disagreement-evidence/stato/verification.json

uo-witness:
	mkdir -p ../.work/artifacts
	python3 benchmark/verify_uo_nominal_witness.py \
	  --witness benchmark/generated/disagreement-evidence/uo/witness.tsv \
	  --output ../.work/artifacts/uo-nominal-witness-verification.json

ore:
	python3 scripts/render_ore_tables.py \
	  --baselines benchmark/ore-baselines.tsv \
	  --shared generated/shared-correct.json \
	  --shared-detail generated/shared-correct.tsv \
	  --output generated/ore-results.tex

current-tables:
	python3 benchmark/render_current_tables.py \
	  --aggregate benchmark/generated/current-final/current-aggregate.json \
	  --output generated/current-results.tex

km-causes:
	python3 benchmark/render_km_terminal_causes.py \
	  --summary benchmark/generated/km-terminal-cause-summary.json \
	  --output generated/km-obo-causes.tex

route-glossary:
	python3 scripts/render_route_glossary.py

citation-occurrences:
	python3 scripts/render_citation_occurrences.py

checks: milestones agent-evidence agent-usage laptop-evidence incremental disagreement-witnesses stato-adjudication uo-witness ore current-tables km-causes route-glossary citation-occurrences manuscript-contract main.pdf
	bash -n scripts/collect_laptop_history.sh
	bash -n scripts/collect_laptop_agentsview.sh
	bash -n benchmark/*.sbatch
	python3 -m py_compile scripts/*.py benchmark/*.py
	python3 scripts/verify_formal_claims.py
	python3 scripts/verify_case_study_commits.py
	python3 scripts/verify_tagged_evidence.py
	python3 scripts/verify_citations.py
	python3 scripts/summarize_release_gates.py \
	  --logs $(REPO_COMMON)/.work/worktrees/v1.3/.work/logs \
	  --output generated/release-gate-summary.json
	python3 -m unittest discover -s scripts -p 'test_*.py' -v
	python3 -m unittest discover -s benchmark/tests -v
	! grep -Eq 'undefined|Overfull|multiply defined' main.log

main.pdf: main.tex references.bib generated/history-summary.tex \
	generated/phase-stats.tex generated/method-milestones.tex \
	generated/agent-session-summary.tex \
	generated/agent-usage-summary.tex generated/agent-usage-phases.tex \
	generated/laptop-evidence-summary.tex \
	generated/incremental-results.tex \
	generated/ore-results.tex generated/fma-results.tex \
	generated/km-obo-causes.tex generated/current-results.tex
	$(LATEX) -interaction=nonstopmode -halt-on-error main.tex
	bibtex main
	$(LATEX) -interaction=nonstopmode -halt-on-error main.tex
	$(LATEX) -interaction=nonstopmode -halt-on-error main.tex

clean:
	rm -f main.aux main.bbl main.blg main.log main.out main.pdf main.toc
