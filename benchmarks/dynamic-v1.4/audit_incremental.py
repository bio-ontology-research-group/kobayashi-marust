#!/usr/bin/env python3
"""Stream source-history signatures and audit completeness, agreement and receipts.

Runs on compute nodes for real panels. Memory is bounded by one signature line
plus small per-state summaries; no taxonomy or transitive closure is materialized.
"""
import argparse
from collections import Counter
import csv
from datetime import datetime, timezone
import gzip
import hashlib
import json
import math
import os
from pathlib import Path
import re

TOP = 'http://www.w3.org/2002/07/owl#Thing'
BOTTOM = 'http://www.w3.org/2002/07/owl#Nothing'


def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda: f.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def signature(path):
    if path.name.endswith('.sig.sha256'):
        raw = path.read_text()
        if not re.fullmatch(r'[0-9a-f]{64}\n', raw):
            raise ValueError('invalid canonical SHA-256 file')
        return dict(sha256=raw.strip(), consistent=None, rows=None,
            evidence='producer_digest_only', issues=[])
    h, counts, previous = hashlib.sha256(), Counter(), None
    issues, consistent = [], None
    opener = gzip.open if path.suffix == '.gz' else open
    with opener(path, 'rb') as stream:
        for line in stream:
            h.update(line)
            if previous is not None and line <= previous:
                if 'noncanonical_order_or_duplicate' not in issues:
                    issues.append('noncanonical_order_or_duplicate')
            previous = line
            if not line.endswith(b'\n'):
                issues.append('missing_final_newline')
            fields = line.decode('utf-8').rstrip('\n').split('\t')
            kind = fields[0]
            counts[kind] += 1
            if kind == 'C' and len(fields) == 2 and fields[1] in ('true', 'false'):
                consistent = fields[1] == 'true'
            elif kind == 'U' and len(fields) == 2 and fields[1] not in ('', TOP, BOTTOM):
                pass
            elif kind == 'S' and len(fields) == 3 and fields[1] != fields[2] and all(x and x not in (TOP, BOTTOM) for x in fields[1:]):
                pass
            elif 'malformed_row' not in issues:
                issues.append('malformed_row')
    if counts['C'] != 1 or consistent is None:
        issues.append('missing_or_repeated_consistency')
    if consistent is False and sum(counts.values()) != 1:
        issues.append('taxonomy_rows_for_inconsistent_ontology')
    return dict(sha256=h.hexdigest(), consistent=consistent, rows=dict(counts),
        evidence='streamed_full_signature', issues=issues)


def timings(path, expected):
    if not path.exists():
        return {'issues': ['missing_timings']}
    with path.open() as stream:
        reader = csv.DictReader(stream, delimiter='\t')
        columns = reader.fieldnames or []
        rows = list(reader)
    issues = []
    if [r.get('revision') for r in rows] != [str(i) for i in range(expected)]:
        issues.append('timing_revision_count_or_order')
    time_columns = [c for c in columns if c.endswith('_s')]
    values = {}
    for col in time_columns:
        try:
            seq = [float(r[col]) for r in rows]
            if any(not math.isfinite(x) or x < 0 for x in seq):
                raise ValueError()
            values[col] = dict(initial_s=seq[0] if seq else None, update_sum_s=sum(seq[1:]), total_s=sum(seq))
        except (KeyError, ValueError, TypeError):
            issues.append('invalid_timing_' + col)
    return dict(sha256=sha(path), rows=len(rows), intervals=values, issues=issues)


def inspect_arm(directory, manifest, expected, reasoner, arm, analytic):
    out = dict(path=str(directory), issues=[], states={}, receipts={})
    measurement = directory / 'measurement.json'
    if not measurement.exists():
        out.update(status='missing', issues=['missing_measurement'], complete=False)
        return out
    try:
        m = json.loads(measurement.read_text())
    except (ValueError, OSError) as exc:
        out.update(status='invalid_measurement', issues=[str(exc)], complete=False)
        return out
    out['measurement'] = m
    out['measurement_sha256'] = sha(measurement)
    out['status'] = m.get('status', 'unknown')
    if out['status'] != 'ok':
        out['issues'].append('measurement_status_' + out['status'])
    if m.get('expected_states') != expected:
        out['issues'].append('measurement_expected_count_mismatch')
    if manifest.exists() and m.get('manifest_sha256') != sha(manifest):
        out['issues'].append('manifest_hash_mismatch')
    files = {}
    for path in directory.glob('*.sig*'):
        match = re.fullmatch(r'(\d+)\.sig(?:\.gz|\.sha256)?', path.name)
        if match:
            i = int(match.group(1))
            if i in files:
                out['issues'].append('duplicate_signature_revision_' + str(i))
            files[i] = path
    if sorted(files) != list(range(expected)):
        out['issues'].append('signature_revision_count_or_order')
    if m.get('completed_states') != len(files):
        out['issues'].append('measurement_completed_count_mismatch')
    complete = directory / 'COMPLETE'
    if not complete.exists() or complete.read_text().strip() != 'states=' + str(expected):
        out['issues'].append('missing_or_invalid_complete_marker')
    for i, path in sorted(files.items()):
        try:
            s = signature(path)
        except (OSError, ValueError, UnicodeError, EOFError) as exc:
            s = dict(issues=['invalid_signature:' + str(exc)])
        if analytic and i < len(analytic['consistent']):
            if s.get('consistent') is None:
                s['issues'].append('analytic_consistency_unverified_without_full_signature')
            elif s['consistent'] != analytic['consistent'][i]:
                s['issues'].append('analytic_consistency_mismatch')
        out['states'][str(i)] = s
        if s['issues']:
            out['issues'].append('signature_issue_revision_' + str(i))
    out['timings'] = timings(directory / 'timings.tsv', expected)
    out['issues'].extend(out['timings']['issues'])
    if analytic and analytic.get('restores_initial'):
        initial = out['states'].get('0', {}).get('sha256')
        checks = {}
        for i in range(2, expected, 2):
            current = out['states'].get(str(i), {}).get('sha256')
            checks[str(i)] = current == initial if initial and current else None
        out['analytic_restoration'] = checks
        if any(v is False for v in checks.values()):
            out['issues'].append('analytic_restoration_mismatch')
    if reasoner == 'km':
        strategies, routes, reuse = Counter(), Counter(), Counter()
        for i in range(expected):
            path = directory / ('%03d.json' % i)
            if not path.exists():
                out['issues'].append('missing_km_receipt_' + str(i))
                continue
            try:
                value = json.loads(path.read_text())
                receipt = value.get('receipt') or {}
                expected_op = 'init' if arm == 'fresh' or i == 0 else 'replace'
                if value.get('status') != 'ok' or value.get('op') != expected_op:
                    out['issues'].append('invalid_km_response_' + str(i))
                routes[value.get('route', 'unknown')] += 1
                strategy = receipt.get('strategy', 'init' if expected_op == 'init' else 'missing')
                strategies[strategy] += 1
                # retained_backend alone says nothing about preserved inference.
                for key in ('meaningful_incremental_update', 'reused_fixpoint', 'route_migrated'):
                    reuse[key] += int(receipt.get(key, False))
                for key in ('retained_states', 'reused_edges', 'reused_subsumptions', 'invalidated_states'):
                    reuse[key] += int(receipt.get(key, 0))
                out['receipts'][str(i)] = dict(receipt)
                out['receipts'][str(i)].update(sha256=sha(path), strategy=strategy,
                    retained_backend=value.get('retained_backend'))
            except (ValueError, TypeError, OSError) as exc:
                out['issues'].append('invalid_km_receipt_' + str(i) + ':' + str(exc))
        out['km_receipt_summary'] = dict(strategies=dict(strategies), routes=dict(routes), reuse=dict(reuse))
    out['complete'] = not out['issues']
    return out


def compare(left, right, expected):
    checked, mismatches, unavailable = 0, [], []
    for i in range(expected):
        a, b = left.get('states', {}).get(str(i)), right.get('states', {}).get(str(i))
        if not a or not b or a.get('issues') or b.get('issues'):
            unavailable.append(i)
        else:
            checked += 1
            if a['sha256'] != b['sha256']:
                mismatches.append(i)
    return dict(checked_states=checked, mismatch_revisions=mismatches,
        unavailable_revisions=unavailable,
        full_agreement=left.get('complete', False) and right.get('complete', False)
            and checked == expected and not mismatches)


def main():
    p = argparse.ArgumentParser()
    p.add_argument('root', type=Path)
    p.add_argument('--phase', choices=['panel-pilot', 'measured'], default='panel-pilot')
    p.add_argument('--scope', choices=['controls', 'panel', 'all'], default='all')
    p.add_argument('--repetitions', type=int, default=1)
    p.add_argument('--konclude',action='store_true',help='include fresh-only Konclude comparator')
    p.add_argument('--out', type=Path, required=True)
    a = p.parse_args()
    root = a.root.resolve()
    controls_path = root / 'inputs/controls.json'
    controls = json.loads(controls_path.read_text()) if controls_path.exists() else {}
    panel_path = root / 'incremental-panel.tsv'
    panel = list(csv.DictReader(panel_path.open(), delimiter='\t')) if panel_path.exists() else []
    cases = {}
    if a.scope in ('controls', 'all'):
        cases.update({name: ['km', 'hermit', 'jfact', 'openllet'] for name in controls})
    if a.scope in ('panel', 'all'):
        cases.update({row['id'] + '-n'+str(n): ['km', 'hermit', 'jfact', 'openllet'] + (['elk', 'whelk'] if row['profile'] == 'EL' else []) for row in panel for n in ((1,10,100) if a.phase=='measured' else (10,))})
    if a.konclude:
        for reasoners in cases.values():reasoners.append('konclude')
    def arms_for(reasoner):return ('fresh',) if reasoner=='konclude' else ('session','fresh')
    report = dict(schema=1, root=str(root), phase=a.phase, scope=a.scope,
        generated_utc=datetime.now(timezone.utc).isoformat(), auditor_sha256=sha(Path(__file__)),
        slurm_job=os.environ.get('SLURM_JOB_ID'), host=os.uname().nodename,
        controls_sha256=sha(controls_path) if controls_path.exists() else None,
        panel_sha256=sha(panel_path) if panel_path.exists() else None,
        scope_note='This scoped audit does not establish full benchmark or release completion.', cases={})
    statuses, problems = Counter(), []
    rep_names = (['warmup'] if a.phase == 'measured' else []) + [str(i) for i in range(a.repetitions)]
    arm_count = sum(sum(len(arms_for(r)) for r in rs)*len(rep_names) for rs in cases.values())
    complete_count = 0
    if not cases:
        problems.append('no_cases_in_requested_scope')
    for case, reasoners in cases.items():
        manifest = root / 'inputs' / case / ('pilot-states.txt' if a.phase == 'panel-pilot' else 'states.txt')
        if not manifest.exists():
            report['cases'][case] = dict(issue='missing_manifest')
            problems.append(case + ':missing_manifest')
            continue
        expected = len(manifest.read_text().splitlines())
        analytic = controls.get(case)
        c = dict(expected_states=expected, manifest_sha256=sha(manifest), repetitions={})
        report['cases'][case] = c
        for rep in rep_names:
            r = dict(arms={}, own_session_fresh={}, cross_reference={})
            c['repetitions'][str(rep)] = r
            for reasoner in reasoners:
                for arm in arms_for(reasoner):
                    directory = root / a.phase / case / reasoner / ('warmup' if rep == 'warmup' else 'rep-' + rep) / arm
                    result = inspect_arm(directory, manifest, expected, reasoner, arm, analytic)
                    r['arms'][reasoner + '/' + arm] = result
                    statuses[result['status']] += 1
                    complete_count += int(result['complete'])
                    if result['issues']:
                        problems.append('%s/rep-%s/%s/%s: %s' % (case, rep, reasoner, arm, ','.join(result['issues'])))
                if reasoner!='konclude':r['own_session_fresh'][reasoner] = compare(r['arms'][reasoner + '/session'], r['arms'][reasoner + '/fresh'], expected)
            hermit, jfact = r['arms'].get('hermit/fresh', {}), r['arms'].get('jfact/fresh', {})
            reference = compare(hermit, jfact, expected)
            r['independent_reference_agreement'] = reference
            for reasoner in reasoners:
                for arm in arms_for(reasoner):
                    key = reasoner + '/' + arm
                    check = compare(r['arms'][key], hermit, expected)
                    check['validated_against_two_agreeing_references'] = check['full_agreement'] and reference['full_agreement']
                    r['cross_reference'][key] = check
                    if check['mismatch_revisions']:
                        problems.append('%s/rep-%s/%s: HermiT taxonomy mismatch revisions %s' %
                            (case, rep, key, check['mismatch_revisions']))
            for reasoner, check in r['own_session_fresh'].items():
                if check['mismatch_revisions']:
                    problems.append('%s/rep-%s/%s: own session/fresh mismatch revisions %s' %
                        (case, rep, reasoner, check['mismatch_revisions']))
    report['summary'] = dict(expected_arms=arm_count, complete_arms=complete_count,
        measurement_statuses=dict(statuses), issues=problems,
        full_scope_verified=bool(cases) and complete_count == arm_count and not problems)
    a.out.parent.mkdir(parents=True, exist_ok=True)
    a.out.with_suffix('.json').write_text(json.dumps(report, indent=2) + '\n')
    lines = ['# Incremental audit', '', report['scope_note'], '',
        'Auditor SHA-256: `' + report['auditor_sha256'] + '`.',
        'Root: `' + str(root) + '`. Phase: `' + a.phase + '`. Generated: ' + report['generated_utc'] + '.', '',
        '%d/%d expected arms complete; statuses: `%s`.' % (complete_count, arm_count, json.dumps(dict(statuses), sort_keys=True)), '',
        '| Case | Repetition | States | Complete arms | Own session/fresh agree | HermiT/JFact fresh agree |',
        '|---|---:|---:|---:|---:|---|']
    for case, c in report['cases'].items():
        if 'issue' in c:
            lines.append('| ' + case + ' | | | missing manifest | | |')
            continue
        for rep, r in c['repetitions'].items():
            lines.append('| %s | %s | %d | %d/%d | %d/%d | %s |' % (case, rep, c['expected_states'],
                sum(x['complete'] for x in r['arms'].values()), len(r['arms']),
                sum(x['full_agreement'] for x in r['own_session_fresh'].values()), len(r['own_session_fresh']),
                r['independent_reference_agreement']['full_agreement']))
    lines += ['', 'KM retained_backend is not evidence of inference reuse. Per-revision strategies,',
        'retained states, reused edges/fixpoints and rebuild counts are in the JSON.',
        'Timing intervals retain their original names; no cross-interface speedup is computed.',
        'Missing outputs and nonterminal measurement files do not establish process liveness.', '', '## Issues', '']
    lines += ['* ' + problem for problem in problems] or ['None in the inspected scope.']
    a.out.with_suffix('.md').write_text('\n'.join(lines) + '\n')
    print(json.dumps(report['summary'], sort_keys=True))


if __name__ == '__main__':
    main()
