#!/usr/bin/env python3
"""Verify one compressed real-panel fixture, expand it in private scratch, run panel.

The wrapper fails closed before starting the timing driver if any prepared
revision, source binding, protocol, runner, or binary inventory is unsupported
or does not match its pinned receipt. It does not choose, omit, or reorder
revisions.
"""
import argparse
import csv
import gzip
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import shutil
import signal
import subprocess
import sys
import tempfile
import time


REVISION_IDS = [f'{i:03d}' for i in range(9)]
GENERATOR_NAMES = ('PrepareUpdates.java', 'VerifyUpdates.java', 'PrepareRealPanel.java')
RUNTIME_DRIVER_FILES = ('run_panel.py', 'measure_classification_cleanup_v3.py',
                        'measure_retained_km_cleanup_v3.py', 'measure_retained_java.py',
                        'process_tree_subreaper_v3.py', 'timing_support.py', 'tree_watchdog.py')


class PreparationError(RuntimeError):
    pass


def digest(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def json_write(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    part = path.with_suffix(path.suffix + '.part')
    part.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n', encoding='utf-8')
    part.replace(path)


def read_json(path):
    return json.loads(Path(path).read_text(encoding='utf-8'))


def read_tsv(path):
    with Path(path).open(newline='', encoding='utf-8') as stream:
        return list(csv.DictReader(stream, delimiter='\t'))


def validate_runner_bundle(run_panel_path, provenance_path, provenance_sha256, protocol_sha256):
    run_panel_path, provenance_path = Path(run_panel_path).resolve(), Path(provenance_path).resolve()
    if not provenance_path.is_file() or digest(provenance_path) != provenance_sha256:
        raise PreparationError('four-arm driver provenance is missing or hash-mismatched')
    provenance = read_json(provenance_path)
    if provenance.get('driver', {}).get('sha256') != digest(run_panel_path):
        raise PreparationError('four-arm driver provenance does not bind run_panel.py')
    if provenance.get('protocol', {}).get('sha256') != protocol_sha256:
        raise PreparationError('four-arm driver provenance does not bind the selected protocol')
    dependencies = {}
    for row in provenance.get('variant_dependencies', []):
        name = Path(row.get('path', '')).name
        expected = row.get('sha256')
        if name in dependencies and dependencies[name] != expected:
            raise PreparationError(f'conflicting driver dependency pins for {name}')
        dependencies[name] = expected
    if not set(RUNTIME_DRIVER_FILES).issubset(dependencies):
        raise PreparationError('driver provenance omits one or more runtime modules')
    checked = {}
    for name in RUNTIME_DRIVER_FILES:
        path = run_panel_path.parent / name
        if not path.is_file() or digest(path) != dependencies[name]:
            raise PreparationError(f'four-arm runtime dependency missing or hash-mismatched: {name}')
        checked[name] = {'path': str(path), 'sha256': dependencies[name]}
    return {'provenance_path': str(provenance_path), 'provenance_sha256': provenance_sha256,
            'runtime_dependencies': checked}


def safe_output_path(root, rel):
    item = PurePosixPath(rel)
    if item.is_absolute() or not item.parts or any(part in ('', '.', '..') for part in item.parts):
        raise PreparationError(f'unsafe path in output_files: {rel!r}')
    path = root.joinpath(*item.parts)
    if not path.is_file():
        raise PreparationError(f'missing prepared output: {rel}')
    return path


def validate_preparation(panel_root, index):
    panel_root = Path(panel_root).resolve()
    selection_path = panel_root / 'workload-selection.json'
    rules_path = panel_root / 'transaction-rules.json'
    provenance_path = panel_root / 'source-provenance.json'
    if not all(p.is_file() for p in (selection_path, rules_path, provenance_path)):
        raise PreparationError('missing frozen selection/rules/provenance file')
    selection_sha, rules_sha, provenance_sha = digest(selection_path), digest(rules_path), digest(provenance_path)
    selection = read_json(selection_path)
    provenance = read_json(provenance_path)
    rows = selection.get('selected')
    if not isinstance(rows, list) or not 0 <= index < len(rows):
        raise PreparationError(f'task index {index} is outside the frozen 80-input selection')
    selected = rows[index]
    ontology = selected.get('ontology')
    if not isinstance(ontology, str) or not ontology.startswith('ore_ont_'):
        raise PreparationError(f'bad frozen ontology row at index {index}')
    if provenance.get('frozen_selection_sha256') != selection_sha:
        raise PreparationError('selection hash differs from source-provenance pin')
    if provenance.get('transaction_rules_sha256') != rules_sha:
        raise PreparationError('transaction rules hash differs from source-provenance pin')

    status_path = panel_root / 'preparation-status' / f'{ontology}.json'
    prepared_root = panel_root / 'prepared' / ontology
    if not status_path.is_file():
        raise PreparationError(f'missing preparation status receipt for {ontology}')
    status = read_json(status_path)
    if status.get('status') != 'prepared':
        raise PreparationError(f'{ontology}: preparation status is {status.get("status")!r}: {status.get("error", "no error detail")}; refusing to omit fixture')
    if not prepared_root.is_dir():
        raise PreparationError(f'{ontology}: preparation receipt is present but prepared output directory is missing')
    fixed_fields = {
        'task_index': index,
        'ontology': ontology,
        'status': 'prepared',
        'frozen_selection_sha256': selection_sha,
        'transaction_rules_sha256': rules_sha,
        'source_provenance_sha256': provenance_sha,
        'frozen_source_sha256': selected.get('sha256'),
        'actual_source_sha256': selected.get('sha256'),
        'source_bytes': selected.get('bytes'),
    }
    for key, expected in fixed_fields.items():
        if status.get(key) != expected:
            raise PreparationError(f'preparation receipt {key} mismatch: {status.get(key)!r} != {expected!r}')
    if status.get('actual_owlapi_runtime_sha256') != provenance.get('runtime', {}).get('actual_sha256'):
        raise PreparationError('recorded OWLAPI runtime does not match frozen provenance')
    if status.get('actual_owlapi_runtime_sha256') != status.get('owlapi_runtime_expected_sha256'):
        raise PreparationError('recorded OWLAPI runtime does not match task expected hash')
    if status.get('compile_process', {}).get('exit_code') != 0:
        raise PreparationError('preparation Java compilation did not exit zero')
    generation = status.get('generation_process', {})
    if generation.get('exit_code') != 0 or generation.get('timed_out') is not False or generation.get('group_absent') is not True:
        raise PreparationError('generation process was unsuccessful, timed out, or left a process group')
    source_pins = status.get('generator_source_sha256', {})
    if set(source_pins) != set(GENERATOR_NAMES) or any(
            not isinstance(row, dict) or row.get('matches') is not True or row.get('actual') != row.get('expected')
            for row in source_pins.values()):
        raise PreparationError('generator source hashes do not match their pins')

    output_files = status.get('output_files')
    if not isinstance(output_files, dict) or not output_files:
        raise PreparationError('preparation receipt has no output file manifest')
    required_outputs = {
        'COMPLETE', 'added-axioms.tsv', 'added-step-audit.tsv', 'added-step-verification.tsv',
        'deleted-axioms.tsv', 'historical-revisions.tsv', 'historical-selected-axioms.tsv',
        'historical-verification.tsv', 'revision-manifest.tsv', 'source.sha256',
        *(f'revisions/{revision}.ofn.gz' for revision in REVISION_IDS),
    }
    if set(output_files) != required_outputs:
        raise PreparationError('preparation output manifest is not the exact required 19-file set')
    mismatches = []
    for rel, expected in output_files.items():
        path = safe_output_path(prepared_root, rel)
        if path.stat().st_size != expected.get('bytes') or digest(path) != expected.get('sha256'):
            mismatches.append(rel)
    if mismatches:
        raise PreparationError(f'prepared output hash/size mismatch: {mismatches}')
    if (prepared_root / 'source.sha256').read_text(encoding='ascii').strip() != selected['sha256']:
        raise PreparationError('prepared source.sha256 does not match frozen input selection')
    if len([name for name in output_files if name.startswith('revisions/') and name.endswith('.ofn.gz')]) != 9:
        raise PreparationError('prepared output manifest does not contain exactly nine compressed revisions')

    rev_path = prepared_root / 'revision-manifest.tsv'
    if status.get('revision_manifest_sha256') != output_files['revision-manifest.tsv'].get('sha256'):
        raise PreparationError('preparation receipt does not bind revision-manifest.tsv')
    rev_rows = read_tsv(rev_path)
    if [row.get('revision') for row in rev_rows] != REVISION_IDS or any(row.get('status') != 'prepared' for row in rev_rows):
        raise PreparationError('revision manifest has missing, extra, reordered, or unsupported revisions')
    for row in rev_rows:
        rel = f"revisions/{row['revision']}.ofn.gz"
        meta = output_files.get(rel, {})
        if row.get('gzip_sha256') != meta.get('sha256') or row.get('gzip_bytes') != str(meta.get('bytes')):
            raise PreparationError(f'{row["revision"]}: revision manifest gzip binding mismatch')
        if not row.get('raw_sha256') or not row.get('raw_bytes', '').isdigit():
            raise PreparationError(f'{row["revision"]}: missing raw snapshot hash/size')

    hist = read_tsv(prepared_root / 'historical-verification.tsv')
    hist_by_id = {row.get('revision'): row for row in hist}
    hist_revision_rows = [hist_by_id.get(str(i), hist_by_id.get(f'{i:03d}')) for i in range(5)]
    if any(row is None or row.get('missing_axioms') != '0' or row.get('extra_axioms') != '0'
           or row.get('ontology_annotations_equal') != 'true' for row in hist_revision_rows):
        raise PreparationError('historical 000-004 snapshot verification is incomplete or failed')
    historical_revisions = read_tsv(prepared_root / 'historical-revisions.tsv')
    if [row.get('revision') for row in historical_revisions] != ['0', '1', '2', '3', '4']:
        raise PreparationError('historical revision ledger is incomplete, extra, or reordered')
    original_count = int(historical_revisions[0]['logical_axioms'])
    batch_k = min(32, max(1, (original_count + 99) // 100))
    if [int(row['removed_from_original']) for row in historical_revisions] != [0, min(1, original_count), 0,
                                                                                min(batch_k, original_count), 0]:
        raise PreparationError('historical deletion/restore sequence differs from frozen protocol')
    historical_selected = read_tsv(prepared_root / 'historical-selected-axioms.tsv')
    if len(historical_selected) != min(batch_k, original_count) or [int(row['rank']) for row in historical_selected] != list(range(min(batch_k, original_count))):
        raise PreparationError('historical ranked deletion selection is incomplete or reordered')
    historical_hashes = {row['revision']: row['sha256'] for row in historical_revisions}
    if any(historical_hashes[f'{i}'] != rev_rows[i]['raw_sha256'] for i in range(5)):
        raise PreparationError('historical raw revision hashes differ from the unchanged producer ledger')
    add_audit = read_tsv(prepared_root / 'added-step-audit.tsv')
    add_verify = read_tsv(prepared_root / 'added-step-verification.tsv')
    if [row.get('revision') for row in add_audit] != ['005', '006', '007', '008']:
        raise PreparationError('added-step audit missing/reordered revisions; refusing to omit steps')
    if [row.get('revision') for row in add_verify] != ['005', '006', '007', '008']:
        raise PreparationError('added-step verification missing/reordered revisions; refusing to omit steps')
    if any(row.get('status') != 'prepared' or row.get('reason') for row in add_audit):
        raise PreparationError('an added revision is unsupported or has a recorded generation reason')
    if any(row.get('status') != 'passed' or row.get('missing_axioms') != '0'
           or row.get('extra_axioms') != '0' or row.get('ontology_annotations_equal') != 'true'
           for row in add_verify):
        raise PreparationError('added revisions do not pass exact ontology/annotation verification')
    expected_removed = [int(add_audit[0]['removed_from_original']),
                        int(add_audit[1]['removed_from_original']),
                        int(add_audit[2]['removed_from_original']),
                        int(add_audit[3]['removed_from_original'])]
    if expected_removed != [min(batch_k + 1, original_count), min(batch_k + 2, original_count),
                            min(batch_k + 2, original_count), min(batch_k + 3, original_count)]:
        raise PreparationError('added transaction delete counts are not ordered k+1, k+2, k+2, k+3')
    if [row.get('additions_relative_to_original') for row in add_audit] != ['0', '0', '1', '2']:
        raise PreparationError('added transaction axiom counts differ from the frozen sequence')
    if [row.get('new_additions_in_step') for row in add_audit] != ['0', '0', '1', '1']:
        raise PreparationError('added transaction sequence is unsupported or incomplete')
    additions = read_tsv(prepared_root / 'added-axioms.tsv')
    if [row.get('revision') for row in additions] != ['007', '008'] or any(
            row.get('subclass_in_source_signature') != 'true'
            or row.get('superclass_in_source_signature') != 'true' for row in additions):
        raise PreparationError('added axioms do not bind named classes present in the original signature')
    if additions[0].get('axiom_sha256') == additions[1].get('axiom_sha256') or additions[0].get('axiom') == additions[1].get('axiom'):
        raise PreparationError('revisions 007 and 008 do not contain distinct added axioms')

    return {'panel_root': str(panel_root), 'task_index': index, 'selection_path': str(selection_path),
            'selection_sha256': selection_sha, 'rules_sha256': rules_sha,
            'source_provenance_sha256': provenance_sha, 'selected': selected,
            'status_path': str(status_path), 'status_sha256': digest(status_path),
            'prepared_root': str(prepared_root), 'prepared_output_files': output_files,
            'prepared_output_hashes_all_match': True, 'revision_manifest_path': str(rev_path),
            'revision_manifest_sha256': digest(rev_path), 'revisions': rev_rows,
            'historical_verification': hist, 'added_step_audit': add_audit,
            'added_step_verification': add_verify, 'added_axioms': additions}


def expand_revisions(validated, scratch_dir, durable_dir):
    scratch_dir, durable_dir = Path(scratch_dir), Path(durable_dir)
    revisions = []
    snapshot = {'schema': 1, 'ontology': validated['selected']['ontology'],
                'task_index': validated['task_index'],
                'preparation_status_path': validated['status_path'],
                'preparation_status_sha256': validated['status_sha256'],
                'selection_sha256': validated['selection_sha256'],
                'transaction_rules_sha256': validated['rules_sha256'],
                'source_provenance_sha256': validated['source_provenance_sha256'],
                'revision_manifest_sha256': validated['revision_manifest_sha256'],
                'revisions': []}
    for index, row in enumerate(validated['revisions']):
        rid = row['revision']
        compressed = Path(validated['prepared_root']) / 'revisions' / f'{rid}.ofn.gz'
        destination = scratch_dir / f'{rid}.ofn'
        h = hashlib.sha256()
        size = 0
        try:
            with gzip.open(compressed, 'rb') as source, destination.open('xb') as target:
                for block in iter(lambda: source.read(1024 * 1024), b''):
                    target.write(block)
                    h.update(block)
                    size += len(block)
        except Exception as error:
            raise PreparationError(f'{rid}: decompression failed: {error}') from error
        if h.hexdigest() != row['raw_sha256'] or size != int(row['raw_bytes']):
            raise PreparationError(f'{rid}: decompressed raw size/hash does not match revision manifest')
        revision = {'revision': index, 'label': f'revision-{rid}', 'operation': 'init' if index == 0 else 'replace',
                    'path': str(destination), 'sha256': h.hexdigest(), 'bytes': size,
                    'expected_valid': True, 'expected_response_status': 'ok'}
        revisions.append(revision)
        snapshot['revisions'].append({'revision_id': rid, 'compressed_path': str(compressed),
                                      'compressed_sha256': row['gzip_sha256'], 'compressed_bytes': int(row['gzip_bytes']),
                                      'raw_sha256': h.hexdigest(), 'raw_bytes': size,
                                      'expanded_path': str(destination), 'operation': revision['operation']})
        json_write(durable_dir / 'prepared-snapshot-manifest.json', snapshot)
    fixture = {'schema': 1, 'fixtures': [{'id': validated['selected']['ontology'], 'revisions': revisions}]}
    json_write(durable_dir / 'fixture-manifest.json', fixture)
    return fixture, snapshot


def make_scratch(parent, job, task):
    parent = Path(parent).resolve()
    if not parent.is_dir():
        raise PreparationError(f'scratch parent does not exist: {parent}')
    path = Path(tempfile.mkdtemp(prefix=f'km-v151-{job}-{task}-', dir=str(parent))).resolve()
    if path.parent != parent or not path.name.startswith(f'km-v151-{job}-{task}-'):
        raise PreparationError('scratch directory did not resolve under its exact unique parent')
    return path


def run_driver(command, cwd, log_path, timeout_s=None):
    """Run only the pinned driver, with signal/timeout cleanup limited to its group."""
    def group_exists(pgid):
        try:
            os.killpg(pgid, 0)
            return True
        except ProcessLookupError:
            return False

    def reap_group(pgid):
        if not group_exists(pgid):
            return True
        try:
            os.killpg(pgid, signal.SIGTERM)
        except ProcessLookupError:
            return True
        time.sleep(0.1)
        if group_exists(pgid):
            try:
                os.killpg(pgid, signal.SIGKILL)
            except ProcessLookupError:
                pass
        for _ in range(10):
            if not group_exists(pgid):
                return True
            time.sleep(0.05)
        return not group_exists(pgid)

    with Path(log_path).open('wb') as log:
        process = subprocess.Popen(command, cwd=cwd, stdout=log, stderr=subprocess.STDOUT,
                                   start_new_session=True, env=os.environ.copy())
        old_handlers = {}
        def stop_child(signum, _frame):
            try:
                os.killpg(process.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
        for signum in (signal.SIGTERM, signal.SIGINT):
            old_handlers[signum] = signal.signal(signum, stop_child)
        started = time.monotonic()
        timed_out = False
        try:
            try:
                exit_code = process.wait(timeout=timeout_s)
            except subprocess.TimeoutExpired:
                timed_out = True
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                exit_code = process.wait()
            group_absent = reap_group(process.pid)
        except BaseException:
            # If the Slurm task receives a signal or the adapter is interrupted,
            # clean only this driver's process group before leaving the task.
            try:
                os.killpg(process.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
            try:
                process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                process.wait()
            reap_group(process.pid)
            raise
        finally:
            for signum, handler in old_handlers.items():
                signal.signal(signum, handler)
        return {'pid': process.pid, 'pgid': process.pid, 'exit_code': exit_code,
                'timed_out': timed_out, 'group_absent': group_absent,
                'elapsed_s': time.monotonic() - started,
                'log_sha256': digest(log_path), 'log_bytes': Path(log_path).stat().st_size}


def selected_scratch_parent(explicit):
    choices = [explicit, os.environ.get('SLURM_TMPDIR'), os.environ.get('TMPDIR'), '/tmp']
    for value in choices:
        if value and Path(value).is_dir() and os.access(value, os.W_OK | os.X_OK):
            return Path(value).resolve()
    raise PreparationError('no writable private scratch parent found (explicit, SLURM_TMPDIR, TMPDIR, /tmp)')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--panel-root', required=True, type=Path)
    parser.add_argument('--task-index', required=True, type=int)
    parser.add_argument('--protocol', required=True, type=Path)
    parser.add_argument('--protocol-sha256', required=True)
    parser.add_argument('--binary-inventory', required=True, type=Path)
    parser.add_argument('--binary-inventory-sha256', required=True)
    parser.add_argument('--run-panel', required=True, type=Path)
    parser.add_argument('--run-panel-sha256', required=True)
    parser.add_argument('--run-panel-provenance', required=True, type=Path)
    parser.add_argument('--run-panel-provenance-sha256', required=True)
    parser.add_argument('--output-root', required=True, type=Path)
    parser.add_argument('--scratch-parent', type=Path, default=None)
    parser.add_argument('--driver-timeout-s', type=int, default=None,
                        help='optional whole fixture adapter limit, distinct from each call limit')
    args = parser.parse_args()
    panel_root = args.panel_root.resolve()
    output_root = args.output_root.resolve()
    output_root.mkdir(parents=True, exist_ok=True)
    selection = read_json(panel_root / 'workload-selection.json')
    rows = selection.get('selected', [])
    if not 0 <= args.task_index < len(rows):
        raise SystemExit(f'task index outside frozen selection: {args.task_index}')
    selected = rows[args.task_index]
    fixture_id = selected['ontology']
    task_out = output_root / f'task-{args.task_index:03d}-{fixture_id}'
    task_out.mkdir(parents=True, exist_ok=False)
    record_path = task_out / 'wrapper-record.json'
    record = {'schema': 1, 'task_index': args.task_index, 'fixture_id': fixture_id,
              'status': 'starting', 'panel_root': str(panel_root), 'output_root': str(output_root),
              'protocol_path': str(args.protocol.resolve()), 'protocol_sha256_expected': args.protocol_sha256,
              'binary_inventory_path': str(args.binary_inventory.resolve()),
              'binary_inventory_sha256_expected': args.binary_inventory_sha256,
              'run_panel_path': str(args.run_panel.resolve()), 'run_panel_sha256_expected': args.run_panel_sha256,
              'run_panel_provenance_path': str(args.run_panel_provenance.resolve()),
              'run_panel_provenance_sha256_expected': args.run_panel_provenance_sha256,
              'slurm_job_id': os.environ.get('SLURM_JOB_ID'),
              'slurm_array_task_id': os.environ.get('SLURM_ARRAY_TASK_ID'),
              'revision_count_expected': 9, 'driver_invoked': False}
    json_write(record_path, record)
    scratch = None
    try:
        for label, path, expected in (('protocol', args.protocol, args.protocol_sha256),
                                      ('binary inventory', args.binary_inventory, args.binary_inventory_sha256),
                                      ('run_panel driver', args.run_panel, args.run_panel_sha256),
                                      ('run_panel provenance', args.run_panel_provenance, args.run_panel_provenance_sha256)):
            if not path.is_file() or digest(path) != expected:
                raise PreparationError(f'{label} missing or hash mismatch')
        runner_bundle = validate_runner_bundle(args.run_panel, args.run_panel_provenance,
                                               args.run_panel_provenance_sha256, args.protocol_sha256)
        # Fail closed on pinned executable/receipt validation before decompressing any revision.
        runner_dir = args.run_panel.resolve().parent
        sys.path.insert(0, str(runner_dir))
        import run_panel
        protocol = run_panel.load_json(args.protocol)
        environment = run_panel.validate_protocol(protocol)
        binaries = run_panel.validate_binaries(run_panel.load_json(args.binary_inventory), args.binary_inventory)
        record.update(protocol_sha256=digest(args.protocol), binary_inventory_sha256=digest(args.binary_inventory),
                      run_panel_sha256=digest(args.run_panel), run_panel_runtime_bundle=runner_bundle,
                      pinned_km_environment=environment,
                      validated_binary_bindings={name: {key: binaries[name].get(key) for key in
                          ('path', 'sha256', 'source_manifest_sha256', 'build_receipt_sha256')} for name in binaries})
        json_write(record_path, record)

        validated = validate_preparation(panel_root, args.task_index)
        record['preparation_validation'] = {
            'status_path': validated['status_path'], 'status_sha256': validated['status_sha256'],
            'selection_sha256': validated['selection_sha256'], 'rules_sha256': validated['rules_sha256'],
            'source_provenance_sha256': validated['source_provenance_sha256'],
            'revision_manifest_sha256': validated['revision_manifest_sha256'],
            'prepared_output_files': len(validated['prepared_output_files']),
            'all_prepared_output_hashes_match': validated['prepared_output_hashes_all_match'],
            'revision_ids': REVISION_IDS,
        }
        json_write(record_path, record)

        scratch_parent = selected_scratch_parent(args.scratch_parent)
        scratch = make_scratch(scratch_parent, os.environ.get('SLURM_JOB_ID', 'local'), args.task_index)
        record['scratch'] = {'parent': str(scratch_parent), 'path': str(scratch), 'cleaned': False,
                             'source': 'explicit' if args.scratch_parent else
                                       'SLURM_TMPDIR' if os.environ.get('SLURM_TMPDIR') and scratch_parent == Path(os.environ['SLURM_TMPDIR']).resolve() else
                                       'TMPDIR' if os.environ.get('TMPDIR') and scratch_parent == Path(os.environ['TMPDIR']).resolve() else 'system_tmpdir'}
        output_bytes = sum(int(row['raw_bytes']) for row in validated['revisions'])
        available_bytes = shutil.disk_usage(scratch).free
        record['scratch'].update(required_raw_bytes=output_bytes, available_bytes_before_expansion=available_bytes)
        json_write(record_path, record)
        if available_bytes < int(output_bytes * 1.2):
            raise PreparationError(f'insufficient private scratch: need {int(output_bytes * 1.2)} bytes, have {available_bytes}')
        snapshot_path = task_out / 'prepared-snapshot-manifest.json'
        fixture_manifest_path = task_out / 'fixture-manifest.json'
        record.update(prepared_snapshot_manifest_path=str(snapshot_path),
                      fixture_manifest_path=str(fixture_manifest_path))
        json_write(record_path, record)
        fixture, snapshot = expand_revisions(validated, scratch, task_out)
        record.update(fixture_manifest_path=str(fixture_manifest_path),
                      fixture_manifest_sha256=digest(fixture_manifest_path),
                      prepared_snapshot_manifest_sha256=digest(snapshot_path),
                      expanded_revision_count=len(fixture['fixtures'][0]['revisions']))
        json_write(record_path, record)
        output_dir = task_out / 'four-arm-panel'
        command = [sys.executable, str(args.run_panel.resolve()), '--protocol', str(args.protocol.resolve()),
                   '--binary-inventory', str(args.binary_inventory.resolve()),
                   '--fixture-manifest', str(fixture_manifest_path), '--output', str(output_dir)]
        if args.driver_timeout_s is not None:
            if args.driver_timeout_s <= 0:
                raise PreparationError('driver timeout must be positive')
        record.update(status='driver_running', driver_invoked=True, driver_command=command,
                      driver_log_path=str(task_out / 'driver.log'))
        json_write(record_path, record)
        result = run_driver(command, runner_dir, task_out / 'driver.log', args.driver_timeout_s)
        panel_path = output_dir / 'panel.json'
        record['driver_process'] = result
        record['driver_panel_path'] = str(panel_path) if panel_path.is_file() else None
        record['driver_panel_sha256'] = digest(panel_path) if panel_path.is_file() else None
        if panel_path.is_file():
            panel = read_json(panel_path)
            record['driver_panel_status'] = panel.get('status')
            record['driver_attempt_count'] = len(panel.get('attempts', []))
        record['status'] = ('driver_complete' if result['exit_code'] == 0 and not result['timed_out']
                            and result['group_absent']
                            and record.get('driver_panel_status') == 'complete_execution_and_semantic_audit'
                            else 'driver_finished_with_failures_or_incomplete_output')
        json_write(record_path, record)
    except Exception as error:
        record.update(status='preparation_or_driver_error', error_type=type(error).__name__, error=str(error))
        failed_status = panel_root / 'preparation-status' / f'{fixture_id}.json'
        if failed_status.is_file():
            failed = read_json(failed_status)
            failed_files = failed.get('output_files') or {}
            record['preparation_status_receipt'] = {
                'path': str(failed_status), 'sha256': digest(failed_status),
                'status': failed.get('status'), 'error': failed.get('error'),
                'generation_process': failed.get('generation_process'),
                'output_file_count': len(failed_files),
                'output_files': failed_files,
            }
        snapshot_path = task_out / 'prepared-snapshot-manifest.json'
        if snapshot_path.is_file():
            record['prepared_snapshot_manifest_path'] = str(snapshot_path)
            record['prepared_snapshot_manifest_sha256'] = digest(snapshot_path)
            record['expanded_revision_count'] = len(read_json(snapshot_path).get('revisions', []))
        fixture_path = task_out / 'fixture-manifest.json'
        if fixture_path.is_file():
            record['fixture_manifest_path'] = str(fixture_path)
            record['fixture_manifest_sha256'] = digest(fixture_path)
        json_write(record_path, record)
        raise
    finally:
        if scratch is not None and scratch.exists():
            if scratch.name.startswith(f"km-v151-{os.environ.get('SLURM_JOB_ID', 'local')}-{args.task_index}-"):
                shutil.rmtree(scratch)
                record['scratch']['cleaned'] = True
            else:
                record['scratch']['cleaned'] = False
                record['scratch']['cleanup_error'] = 'refused deletion because scratch path no longer has expected unique prefix'
            json_write(record_path, record)
    print(json.dumps({'task_index': args.task_index, 'fixture_id': fixture_id,
                      'status': record.get('status'), 'driver_invoked': record.get('driver_invoked')}))


if __name__ == '__main__':
    main()
