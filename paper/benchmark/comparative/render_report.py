"""Render comparative evidence without turning partial results into release approval."""
import argparse
from collections import Counter, defaultdict
import hashlib
import json
from pathlib import Path
import statistics
from run_set import DEFAULT


PANEL_RUN_KEYS = {
    'classification': {'inventory', 'classification', 'classification_km', 'classification_konclude'},
    'updates': {'inventory', 'updates_preparation', 'retained_konclude',
                'updates_java', 'updates_km', 'updates_native', 'updates_whelk', 'updates_konclude'},
    'justifications': {'inventory', 'queries_preparation', 'justifications_km', 'justifications_java',
                       'justifications_native', 'justifications_external', 'justifications_whelk'},
    'preparation': {'inventory', 'updates_preparation', 'queries_preparation',
                    'updates_konclude', 'classification_konclude', 'justifications_external'},
}


def validate_run_sets(reports, selected=None):
    if selected is None:
        runs = reports['classification']['run_set']
        assert all(r['run_set'] == runs for r in reports.values()), 'reports select different measurements'
        return runs
    assert set(selected) == set(DEFAULT), 'selected run set must name every measurement'
    assert all(isinstance(v, str) and v for v in selected.values()), 'invalid selected run set'
    for panel, record in reports.items():
        for key in PANEL_RUN_KEYS[panel]:
            assert record['run_set'].get(key) == selected[key], panel + ' selects different measurement: ' + key
    return selected


def cell(value):
    if value is None:
        return 'n/a'
    if isinstance(value, float):
        return f'{value:.4g}'
    return str(value).replace('|', '\\|').replace('\n', ' ')


def table(headers, rows):
    lines = ['| ' + ' | '.join(headers) + ' |', '| ' + ' | '.join(['---'] * len(headers)) + ' |']
    lines += ['| ' + ' | '.join(cell(v) for v in row) + ' |' for row in rows]
    return '\n'.join(lines) + '\n'


def status_table(coverage):
    statuses = sorted({s for counts in coverage.values() for s in counts})
    return table(['Method'] + statuses,
                 [[name] + [coverage[name].get(s, 0) for s in statuses] for name in sorted(coverage)])


def cost_table(pairs, cost_key, km_method='km'):
    rows = []
    for pair in pairs:
        if not any(p == km_method or p.startswith(km_method + '-') for p in (pair['left'], pair['right'])):
            continue
        costs = pair[cost_key]
        time, memory = costs['wall_s'], costs['peak_bytes']
        rows.append([pair.get('phase', ''), pair['left'], pair['right'], costs['cases'],
                     time.get('left_median'), time.get('right_median'), time.get('median_paired_ratio'),
                     memory.get('left_median', 0) / 1024**2 if 'left_median' in memory else None,
                     memory.get('right_median', 0) / 1024**2 if 'right_median' in memory else None,
                     memory.get('median_paired_ratio')])
    return table(['Phase', 'Left', 'Right', 'Paired cases', 'Left s', 'Right s', 'Time right/left',
                  'Left MiB', 'Right MiB', 'Memory right/left'], rows)


def render(classification, updates, justifications, preparation=None, selected_run_set=None):
    reports = dict(classification=classification, updates=updates, justifications=justifications)
    if preparation:
        reports['preparation'] = preparation
    runs = validate_run_sets(reports, selected_run_set)
    lines = ['# v1.4.5 comparative benchmark evidence', '',
             'This document summarizes recorded outcomes. Release approval and correctness adjudication are separate. '
             'Missing audits and failed measurements remain visible; raw output production is not a correctness result.', '',
             'Measurements use one CPU, a 20 GiB memory limit, and 240 seconds per classification, update, '
             'or justification generation. Independent justification verification has a separate 240-second limit.', '',
             '**Classification coverage**', '',
             f"The unchanged corpus contains {classification['expected_inputs']} inputs. "
             'Admission and raw measurement status appear together below. Invalid-input refusals are retained.', '',
             status_table(classification['coverage']), '', '**Classification comparisons with KM**', '',
             'Each cost row uses the same valid inputs for both reasoners and requires full semantic agreement. '
             'Unknown consistency is not promoted to agreement. Times and memory are medians; ratios are medians '
             'of per-case right/left ratios, not ratios of independent medians. All baseline pairs remain in the JSON report.', '',
             cost_table(classification['pairwise'], 'costs_on_valid_fully_agreeing_cases'), '',
             '**Incremental coverage**', '',
             f"The panel retains {updates['selected_ontologies']} ontologies, five revisions, and three repetitions. "
             'Cold means a fresh process. Retained means the same session; it does not establish internal reuse. '
             'The JSON report includes actual KM reuse receipts and unknown reuse for interfaces that do not expose it.', '',
             status_table(updates['coverage_per_revision_repetition']), '',
             '**Incremental comparisons with KM**', '',
             'Initialization is reported separately from the four update revisions. Pairing uses identical source, '
             'revision, and repetition, and requires full agreement. Pairwise agreement alone does not adjudicate '
             'a disagreement with an independent reference; all comparison outcomes remain in the JSON report.', '',
             cost_table(updates['pairwise'], 'costs_on_fully_agreeing_cases'), '',
             '**Justification coverage**', '',
             f"The frozen panel contains {justifications['selected_ontologies']} ontologies. "
             'Preparation failures and sources without eligible inferred queries are not replaced.', '',
             table(['Ontology outcome', 'Count'], sorted(justifications['eligibility'].items())), '',
             status_table(justifications['coverage_per_query_repetition']), '',
             '**Justification comparisons with KM**', '',
             'Cost pairs require independently verified source membership, entailment, and subset-minimality '
             'for both results on the same source, query, and repetition. Generation cost is separate from verification.', '',
             cost_table(justifications['pairwise'], 'common_verified_generation_costs')]
    proof_values = defaultdict(list)
    for source in justifications['sources']:
        for case in source['cases']:
            if case['status'] == 'verified_evidence_intact':
                proof_values[case['baseline']].append(case)
    lines += ['', '**Verified support sizes and verification costs**', '',
              'These descriptive medians cover each reasoner’s verified cases, which may differ. '
              'Use the paired table above for generation-cost comparisons.', '',
              table(['Reasoner', 'Verified cases', 'Median logical axioms', 'Median verification s'],
                    [[b, len(rows), statistics.median(x['logical_axioms'] for x in rows),
                      statistics.median(x['verification_wall_s'] for x in rows)]
                     for b, rows in sorted(proof_values.items())])]
    if preparation:
        stages = defaultdict(list)
        modules = []
        for source in preparation['sources']:
            for stage in source['queries'].get('record', {}).get('stages', []):
                stages['query ' + stage['name']].append(stage)
            reference = source['queries'].get('record', {}).get('reused_reference_stage')
            if reference:
                stages['frozen HermiT reference'].append(reference)
            update = source['updates'].get('record')
            if update:
                stages['update preparation including compilation'].append({
                    'wall_s': update.get('seconds'), 'peak_bytes': source['updates'].get('preparation_peak_bytes')})
            for module in source['modules']:
                modules.append(module['module_bytes'])
                measured = module['more_consistency_preparation'].get('record')
                if measured:
                    stages['MORe module consistency preparation'].append(measured)
            for conversion in source['konclude_update_conversions']:
                if 'record' in conversion:
                    stages['Konclude update conversion'].append(conversion['record'])
        for conversion in preparation['konclude_classification_conversions']:
            if 'record' in conversion:
                stages['Konclude classification conversion'].append(conversion['record'])
        rows = []
        for name, values in sorted(stages.items()):
            times = [v['wall_s'] for v in values if isinstance(v.get('wall_s'), (float, int))]
            peaks = [v['peak_bytes'] for v in values if isinstance(v.get('peak_bytes'), (float, int))]
            rows.append([name, len(values), len(times), sum(times) if times else None,
                         max(peaks)/1024**2 if peaks else None])
        lines += ['', '**Preparation costs**', '', preparation['accounting'], '',
                  f"The report includes {len(modules)} modules, totaling {sum(modules)} bytes. "
                  'The JSON supplement retains individual source/module sizes and all preparation receipts. '
                  'The following totals include recorded failures and are not added to each repetition.', '',
                  table(['Stage', 'Recorded stages', 'Timed stages', 'Total recorded s', 'Maximum recorded MiB'], rows)]
    lines += ['', '**Outstanding evidence review**', '',
              table(['Panel', 'Recorded issues requiring review'], [
                  ['classification', len(classification['issues'])],
                  ['incremental', len(updates['issues'])],
                  ['justification', len(justifications['issues'])]]), '',
              'Issue counts include missing evidence, preparation failures, and disagreements as recorded by each '
              'reporter. They do not replace inspection of individual outcomes.', '']
    lines += ['', '**Selected measurement runs**', '',
              'Each panel is checked against the selected runs it actually consumes. Original JSON reports '
              'retain their complete historical run sets; rerunning one panel does not relabel another panel’s evidence.', '',
              table(['Run-set field', 'Selected artifact or job'], sorted(runs.items()))]
    return '\n'.join(lines)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('classification', type=Path)
    parser.add_argument('updates', type=Path)
    parser.add_argument('justifications', type=Path)
    parser.add_argument('output', type=Path)
    parser.add_argument('--preparation', type=Path)
    parser.add_argument('--run-set', type=Path, help='Explicit final selection; validate each panel against its consumed runs')
    args = parser.parse_args()
    paths = [args.classification, args.updates, args.justifications]
    records = [json.loads(p.read_text()) for p in paths]
    extra = json.loads(args.preparation.read_text()) if args.preparation else None
    selected = json.loads(args.run_set.read_text()) if args.run_set else None
    content = render(*records, extra, selected)
    if args.preparation:
        paths.append(args.preparation)
    if args.run_set:
        paths.append(args.run_set)
    content += '\n**Input report hashes**\n\n' + table(['File', 'SHA-256'],
        [[p.name, hashlib.sha256(p.read_bytes()).hexdigest()] for p in paths])
    with args.output.open('x') as stream:
        stream.write(content)
