"""Expose shared preparation and baseline conversion costs without amortizing them."""
import argparse
import csv
import json
from pathlib import Path

from measure_classification import digest
from run_set import load


def receipt(path):
    if not path.exists():
        return {'status': 'missing_receipt', 'path': str(path)}
    data = json.loads(path.read_text())
    return {'path': str(path), 'sha256': digest(path), 'record': data, 'status': data['status']}


def report(root, runs, manifest):
    root = Path(root)
    selection = json.loads((root / 'workload-selection.json').read_text())['selected']
    sources = []
    for source in selection:
        ontology = source['ontology']
        update_dir = root / ('prepared-updates-' + runs['updates_preparation']) / ontology
        query_dir = root / ('prepared-queries-' + runs['queries_preparation']) / ontology
        row = {'ontology': ontology, 'source_sha256': source['sha256'], 'source_bytes': source['bytes'],
               'updates': receipt(update_dir / 'receipt.json'), 'queries': receipt(query_dir / 'receipt.json'),
               'modules': [], 'konclude_update_conversions': []}
        for kind in ('updates', 'queries'):
            if 'record' in row[kind]:
                assert row[kind]['record']['source_sha256'] == source['sha256'], 'prepared source differs'
        update_record = row['updates'].get('record', {})
        rss = update_dir / 'max-rss-kib.txt'
        if rss.exists():
            values = [int(s) for s in rss.read_text().splitlines() if s.isdigit()]
            row['updates']['preparation_peak_bytes'] = max(values) * 1024 if values else None
            row['updates']['rss_receipt_sha256'] = digest(rss)
        row['updates']['wall_time_scope'] = 'compilation and preparation; seconds field in original receipt'
        if update_record.get('status') == 'prepared':
            row['updates']['revisions'] = []
            for index in range(5):
                path = update_dir / 'revisions' / f'{index:03}.ofn'
                assert digest(path) == update_record['files'][path.name], 'revision changed'
                row['updates']['revisions'].append({'revision': index, 'bytes': path.stat().st_size,
                                                   'sha256': update_record['files'][path.name]})
                converted = root / ('konclude-updates-' + runs['updates_konclude']) / ontology / 'conversion' / f'{index:03}' / 'record.json'
                row['konclude_update_conversions'].append(receipt(converted))
        query_record = row['queries'].get('record', {})
        if query_record.get('status') == 'prepared':
            path = query_dir / 'queries/queries.tsv'
            assert digest(path) == query_record['files']['queries.tsv']['sha256'], 'queries changed'
            with path.open() as stream:
                queries = list(csv.DictReader(stream, delimiter='\t'))
            for query in queries:
                module = query_dir / 'queries' / (query['query'] + '.ofn')
                assert digest(module) == query['module_sha256'], 'module changed'
                module_row = {'query': query['query'], 'module_bytes': module.stat().st_size,
                              'module_sha256': query['module_sha256'], 'query_metadata': query}
                consistency = root / ('java-justifications-' + runs['justifications_external']) / ontology / 'more' / 'module-consistency' / query['query'] / 'record.json'
                module_row['more_consistency_preparation'] = receipt(consistency)
                row['modules'].append(module_row)
        sources.append(row)
    conversions = []
    for source in json.loads(Path(manifest).read_text())['inputs']:
        path = root / ('classification-konclude-' + runs['classification_konclude']) / 'conversion' / source['ontology'] / 'record.json'
        data = receipt(path)
        if 'record' in data:
            assert data['record']['source_sha256'] == source['sha256'], 'conversion source differs'
        conversions.append({'ontology': source['ontology'], **data})
    return {'schema': 1, 'run_set': runs, 'reporter_sha256': digest(__file__),
            'selection_sha256': digest(root / 'workload-selection.json'), 'manifest_sha256': digest(manifest),
            'accounting': 'Shared preparation is reported once per source or module, separately from all repetitions. '
                          'Reused reference stages retain their original timing. No costs are silently amortized.',
            'sources': sources, 'konclude_classification_conversions': conversions}


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('root', type=Path)
    parser.add_argument('run_set')
    parser.add_argument('manifest', type=Path)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    result = report(args.root, load(args.root, args.run_set), args.manifest)
    with args.output.open('x') as stream:
        json.dump(result, stream, indent=2)
        stream.write('\n')
