"""Verify retained execution evidence without replacing raw harness outcomes."""
import hashlib
import json


def inspect_execution(stdout_path, ontology, raw_outcome):
    record_path = stdout_path.with_suffix('.execution.json')
    if not record_path.exists():
        # External timeout/memory termination can prevent the wrapper finishing.
        # Missing evidence cannot establish an invalid-input refusal.
        return dict(reported_outcome=raw_outcome, execution_record_present=False)
    record = json.loads(record_path.read_text())
    if record['ontology'] != ontology:
        raise ValueError('Execution record belongs to a different ontology')
    stdout = stdout_path.read_bytes()
    stderr = stdout_path.with_suffix('.stderr').read_bytes()
    for stream, raw in [('stdout', stdout), ('stderr', stderr)]:
        if hashlib.sha256(raw).hexdigest() != record[stream + '_sha256']:
            raise ValueError('Execution ' + stream + ' hash mismatch')
    reported = raw_outcome
    if record['status'] == 'invalid_input':
        diagnostic = record.get('diagnostic')
        if (record['exit_code'] != 2 or stdout or raw_outcome == 'ok'
                or not isinstance(diagnostic, str)
                or not diagnostic.startswith('invalid OWL 2 DL input')
                or diagnostic not in stderr.decode(errors='replace').splitlines()):
            raise ValueError('Invalid-input verdict lacks matching refusal evidence')
        reported = 'invalid_input'
    elif record['status'] == 'ok' and (record['exit_code'] != 0 or raw_outcome != 'ok'):
        raise ValueError('Successful execution record contradicts harness outcome')
    return dict(reported_outcome=reported, execution_record_present=True,
                execution_status=record['status'], exit_code=record['exit_code'],
                diagnostic=record.get('diagnostic'))
