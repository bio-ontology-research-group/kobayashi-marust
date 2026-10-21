#!/usr/bin/env python3
"""Selection-bound full80 wrapper using the v3 subreaper OWLAPI adapter.

Pending binding templates deliberately fail both preflight and execution.
Deploy beside run_four_arm_cleanup_v3.py, with the pinned v3.2 digest timing runtime.
"""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'timing-runner'))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'owlapi-runner/cleanup-evidence-v3.2-digest'))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'timing-runner/cleanup-evidence-v3.2-digest'))
from run_prepared_fixture import validate_preparation, expand_revisions, digest, json_write
from run_four_arm_cleanup_v3 import preflight as inventory_preflight
from run_panel import ARMS, ORDERS


SELECTION_SHA256 = 'd51dff7640b82a84ccf22857532817c39c1952c9b6c7e2acd00ad4df6ab246e7'
PROTOCOL_SHA256 = 'fce89e1db19b49176ac2d389f73fc5f4cb41ad90dcd027f1660e7278c8210143'
RELEASED_BINARY_SHA256 = '1dbc0dd92170abcd70e948fa2dc2d9d13d5c72076bcff9ad7a664921188e5900'
EXPECTED_ARMS = ('candidate_retained', 'candidate_fresh',
                 'released_baseline_retained', 'released_baseline_fresh')
CONTROLS = ('control/full80-inputs.json', 'control/acceptance-protocol.json',
            'control/four-arm-bindings-remote.json', 'inputs/workload-selection.json')
RUNTIME = ('runtime/owlapi-runner/run_prepared_owlapi_full80.py',
           'runtime/owlapi-runner/cleanup-evidence-v3.2-digest/run_four_arm_cleanup_v3.py',
           'runtime/owlapi-runner/cleanup-evidence-v3.2-digest/evaluate_public_owlapi.py',
           'runtime/timing-runner/compact_full80_slurm_final.py',
           'runtime/timing-runner/audit_full80_compact.py',
           'runtime/timing-runner/run_prepared_fixture.py',
           'runtime/timing-runner/cleanup-evidence-v3.2-digest/run_panel.py',
           'runtime/timing-runner/cleanup-evidence-v3.2-digest/measure_classification_cleanup_v3.py',
           'runtime/timing-runner/cleanup-evidence-v3.2-digest/measure_retained_km_cleanup_v3.py',
           'runtime/timing-runner/measure_retained_java.py',
           'runtime/timing-runner/cleanup-evidence-v3.2-digest/process_tree_subreaper_v3.py',
           'runtime/timing-runner/four-arm-panel-driver-provenance.json',
           'runtime/owlapi-runner/cleanup-evidence-v3.2-digest/measure_public_owlapi_cleanup_v3.py',
           'runtime/owlapi-runner/cleanup-evidence-v3.2-digest/process_tree_subreaper_v3.py',
           'runtime/timing-runner/timing_support.py',
           'runtime/timing-runner/tree_watchdog.py')


def require(condition, message):
    if not condition:
        raise ValueError(message)


def hash_value(value):
    return isinstance(value, str) and re.fullmatch('[0-9a-f]{64}', value) is not None


def preflight(package, binding_path, expected_binding_sha256):
    # This preflight streams every pinned payload (including giant gzip inputs),
    # so it is compute work, not a login-node administrative metadata check.
    require(bool(os.environ.get('SLURM_JOB_ID')), 'preflight hashing requires Slurm compute allocation')
    package = Path(package).resolve()
    require(hash_value(expected_binding_sha256), 'missing final binding SHA256')
    require(digest(binding_path) == expected_binding_sha256, 'binding hash mismatch')
    binding = json.loads(Path(binding_path).read_text())
    require(binding.get('schema') == 'km-owlapi-full80-binding-v1', 'binding schema')
    require(binding.get('status') == 'execution_bound', 'pending execution binding')
    require(binding.get('package_root') == str(package), 'package path not rebound')
    for key in ('candidate_binary_sha256', 'candidate_source_manifest_sha256',
                'candidate_build_receipt_sha256'):
        require(hash_value(binding.get(key)), 'unset ' + key)
    files = binding.get('files', {})
    require(isinstance(files, dict) and set(CONTROLS + RUNTIME) <= set(files),
            'binding omits required control/runtime files')
    for relative, expected in files.items():
        path = (package / relative).resolve()
        require(not Path(relative).is_absolute() and path.is_relative_to(package),
                'file outside package: ' + relative)
        require(hash_value(expected) and digest(path) == expected, 'file mismatch: ' + relative)
    require(files['inputs/workload-selection.json'] == SELECTION_SHA256, 'selection changed')
    require(files['control/acceptance-protocol.json'] == PROTOCOL_SHA256, 'protocol changed')
    selection = json.loads((package / 'inputs/workload-selection.json').read_text())['selected']
    require(len(selection) == 80 and len({s['ontology'] for s in selection}) == 80,
            'selection must contain exactly80 unique ontologies')
    plan = json.loads((package / 'control/full80-inputs.json').read_text())
    require(plan.get('schema') == 'km-owlapi-full80-inputs-v1', 'input plan schema')
    require(plan.get('selection_sha256') == SELECTION_SHA256, 'input selection binding')
    require(plan.get('fixed_indices') == list(range(80))
            and all(type(i) is int for i in plan['fixed_indices'])
            and plan.get('revision_ids') == list(range(9))
            and all(type(i) is int for i in plan['revision_ids']), 'indices/revisions changed')
    rows = plan.get('fixtures', [])
    require([r.get('index') for r in rows] == list(range(80))
            and all(type(r.get('index')) is int for r in rows), 'missing/duplicate/reordered cases')
    for index, (row, selected) in enumerate(zip(rows, selection)):
        require(row.get('id') == selected['ontology'], 'ontology mapping at ' + str(index))
        for field in ('preparation_status_sha256', 'revision_manifest_sha256',
                      'generator_source_provenance_sha256'):
            require(hash_value(row.get(field)), 'unset fixture ' + field)
        revisions = row.get('revisions', [])
        require([r.get('revision') for r in revisions] == list(range(9))
                and all(type(r.get('revision')) is int for r in revisions), 'revision ordering')
        require(all(hash_value(r.get('raw_sha256')) and hash_value(r.get('compressed_sha256'))
                    and r.get('expected_valid') is True
                    and bool(r.get('OWLAPI_expected_valid_basis')) for r in revisions),
                'unbound revision or missing verified-OWLAPI validity expectation')
    protocol = json.loads((package / 'control/acceptance-protocol.json').read_text())
    measurement = protocol['measurement_protocol']
    require(measurement['repetitions'] == 5 and measurement['resources'] == {
        'cpu_threads': 1, 'memory_mib': 20480,
        'per_classification_or_update_timeout_s': 240,
        'cluster_execution': 'Slurm compute allocations only; never run benchmark work on login nodes'},
        'repetitions/resources changed')
    require(ARMS == EXPECTED_ARMS and len(ORDERS) == 5
            and all(len(order) == 4 and set(order) == set(ARMS) for order in ORDERS),
            'five paired four-arm schedule changed')
    inventory = inventory_preflight(package / 'control/four-arm-bindings-remote.json')
    require(set(inventory['variants']) == {'candidate', 'released_baseline'}, 'binary variants changed')
    for absolute, expected in inventory['files'].items():
        path = Path(absolute).resolve()
        require(path.is_relative_to(package)
                and files.get(str(path.relative_to(package))) == expected,
                'inventory file omitted from package binding')
    for name, variant in inventory['variants'].items():
        require(name in ('candidate', 'released_baseline'), 'unknown binary variant')
        for field in ('binary', 'native_source_manifest', 'native_build_receipt',
                      'adapter_compile_receipt', 'java'):
            path = Path(variant[field]).resolve()
            require(path.is_relative_to(package), 'inventory path outside package')
            relative = str(path.relative_to(package))
            require(files.get(relative) == inventory['files'].get(str(path)),
                    'unbound inventory input: ' + field)
    candidate = inventory['variants']['candidate']
    for key, field in (('candidate_binary_sha256', 'binary'),
                       ('candidate_source_manifest_sha256', 'native_source_manifest'),
                       ('candidate_build_receipt_sha256', 'native_build_receipt')):
        require(binding[key] == digest(candidate[field]), 'candidate pin mismatch: ' + key)
    require(inventory['variants']['released_baseline']['binary_sha256'] == RELEASED_BINARY_SHA256,
            'released binary changed')
    return plan


def run_task(package, plan, index, output, prepare_only=False):
    # Even prepare-only validates/hashes and decompresses potentially giant
    # snapshots. Guard before touching any fixture, including in dry-run mode.
    require(bool(os.environ.get('SLURM_JOB_ID')), 'preparation requires Slurm compute allocation')
    require(type(index) is int and 0 <= index < 80, 'task index outside full80 selection')
    row = plan['fixtures'][index]
    validated = validate_preparation(package / 'inputs', index)
    require(validated['selected']['ontology'] == row['id'], 'prepared ontology mismatch')
    require(validated['status_sha256'] == row['preparation_status_sha256'], 'status binding')
    require(digest(validated['revision_manifest_path']) == row['revision_manifest_sha256'],
            'revision manifest binding')
    require(validated['source_provenance_sha256'] == row['generator_source_provenance_sha256'],
            'generator provenance binding')
    require([r['raw_sha256'] for r in validated['revisions']]
            == [r['raw_sha256'] for r in row['revisions']], 'raw revision binding')
    require([r['gzip_sha256'] for r in validated['revisions']]
            == [r['compressed_sha256'] for r in row['revisions']], 'compressed revision binding')
    # validate_preparation already rehashes every compressed revision and verifies
    # exact OWLAxiom/annotation generation, just as the unchanged pilot wrapper.
    output.mkdir(parents=True, exist_ok=False)
    expanded = output / 'expanded'
    expanded.mkdir()
    fixture, snapshot = expand_revisions(validated, expanded, output)
    revisions = fixture['fixtures'][0]['revisions']
    require(len(revisions) == 9, 'expanded revision count')
    for revision, original in zip(revisions, row['revisions']):
        require(revision['sha256'] == original['raw_sha256'], 'expanded raw binding')
        revision['entailed_if_consistent'] = original.get('entailed_if_consistent', [])
        revision['OWLAPI_expected_valid_basis'] = original['OWLAPI_expected_valid_basis']
    manifest = output / 'owlapi-fixture-manifest.json'
    json_write(manifest, fixture)
    if prepare_only:
        return {'status': 'prepared_not_run', 'fixture': row['id'], 'revisions': 9,
                'manifest_sha256': digest(manifest)}
    command = [sys.executable, str(package / 'runtime/owlapi-runner/cleanup-evidence-v3.2-digest/run_four_arm_cleanup_v3.py'),
               '--bindings', str(package / 'control/four-arm-bindings-remote.json'),
               '--protocol', str(package / 'control/acceptance-protocol.json'),
               '--fixtures', str(manifest), '--output', str(output / 'panel')]
    result = subprocess.run(command)
    json_write(output / 'driver-terminal.json', {'actual_exit_code': result.returncode,
               'command': command, 'fixture_manifest_sha256': digest(manifest),
               'input_plan_sha256': digest(package / 'control/full80-inputs.json')})
    return {'actual_exit_code': result.returncode}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--package', type=Path, required=True)
    parser.add_argument('--binding', type=Path, required=True)
    parser.add_argument('--binding-sha256', required=True)
    parser.add_argument('--task-index', type=int, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--prepare-only', action='store_true')
    parser.add_argument('--preflight-only', action='store_true')
    args = parser.parse_args()
    package = args.package.resolve()
    plan = preflight(package, args.binding, args.binding_sha256)
    require(0 <= args.task_index < 80, 'task index outside full80 selection')
    if args.preflight_only:
        print(json.dumps({'status': 'full80_preflight_passed_not_run', 'cases': 80,
                          'revisions_per_case': 9, 'repetitions': 5, 'arms': list(ARMS)}))
        return
    result = run_task(package, plan, args.task_index, args.output, args.prepare_only)
    preflight(package, args.binding, args.binding_sha256)
    print(json.dumps(result))
    raise SystemExit(result.get('actual_exit_code', 0))


if __name__ == '__main__':
    main()
