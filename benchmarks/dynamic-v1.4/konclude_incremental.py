#!/usr/bin/env python3
"""Konclude OWLlink fresh-rebuild comparator; no retained deletion API claimed."""
import argparse
import hashlib
import gzip
import shutil
import json
import os
from pathlib import Path
import signal
import subprocess
import time
import xml.etree.ElementTree as ET

OWL = 'http://www.w3.org/2002/07/owl#'
TOP, BOTTOM = OWL + 'Thing', OWL + 'Nothing'
LINK = 'http://www.owllink.org/owllink-xml#'


def sha(path):
    h = hashlib.sha256()
    with open(path, 'rb') as stream:
        for block in iter(lambda: stream.read(1 << 20), b''):
            h.update(block)
    return h.hexdigest()


def request(source, target):
    ET.register_namespace('', LINK)
    ET.register_namespace('owl', OWL)
    root = ET.Element('{' + LINK + '}RequestMessage')
    kb = 'urn:km:dynamic:konclude'
    ET.SubElement(root, 'CreateKB', kb=kb)
    load = ET.SubElement(root, 'LoadOntologies', kb=kb)
    ET.SubElement(load, 'OntologyIRI', IRI=source.resolve().as_uri())
    test = ET.SubElement(root, 'IsClassSatisfiable', kb=kb)
    ET.SubElement(test, '{' + OWL + '}Class', IRI=TOP)
    ET.SubElement(root, 'GetSubClassHierarchy', kb=kb)
    ET.SubElement(root, 'ReleaseKB', kb=kb)
    ET.ElementTree(root).write(target, encoding='utf-8', xml_declaration=True)


def canonical(response):
    root = ET.parse(response).getroot()
    # Konclude response namespace differs from its request namespace.
    for e in root.iter():
        e.tag = e.tag.rsplit('}', 1)[-1]
    if root.findall('UnsatisfiableKBError'):
        errors = [e for e in root if 'Error' in e.tag]
        if any(e.tag != 'UnsatisfiableKBError' for e in errors):
            raise ValueError('mixed errors alongside inconsistent KB')
        return ['C\tfalse']
    values = root.findall('BooleanResponse')
    if len(values) != 1 or values[0].get('result') not in ('true', 'false'):
        raise ValueError('missing or ambiguous consistency response')
    consistent = values[0].get('result') == 'true'
    if not consistent:
        return ['C\tfalse']
    if any('Error' in e.tag for e in root.iter()):
        raise ValueError('OWLlink error in consistent classification')
    hierarchy = root.find('ClassHierarchy')
    if hierarchy is None:
        raise ValueError('missing class hierarchy')
    graph = {}
    def synset(node):
        if node is None:
            raise ValueError('missing class synset')
        names = {c.attrib['IRI'] for c in node.findall('Class')}
        if not names:
            raise ValueError('empty class synset')
        for name in names:
            graph.setdefault(name, set()).update(names - {name})
        return names
    bottom = synset(hierarchy.find('ClassSynset'))
    if BOTTOM not in bottom:
        raise ValueError('bottom synset absent')
    unsat = bottom - {BOTTOM}
    for pair in hierarchy.findall('ClassSubClassesPair'):
        parents = synset(pair.find('ClassSynset'))
        children = pair.find('SubClassSynsets')
        if children is None:
            raise ValueError('missing subclass synsets')
        for child in children.findall('ClassSynset'):
            for c in synset(child):
                graph[c].update(parents)
    rows = {'C\ttrue'} | {'U\t' + c for c in unsat}
    for c in graph:
        if c in unsat or c in (TOP, BOTTOM):
            continue
        seen, todo = set(), list(graph[c])
        while todo:
            s = todo.pop()
            if s in seen:
                continue
            seen.add(s)
            todo.extend(graph.get(s, ()))
        rows.update('S\t' + c + '\t' + s for s in seen if s not in (c, TOP, BOTTOM))
    return sorted(rows)


def main():
    p = argparse.ArgumentParser()
    p.add_argument('binary', type=Path)
    p.add_argument('states', type=Path)
    p.add_argument('out', type=Path)
    p.add_argument('--timeout', type=float, default=240)
    p.add_argument('--reference', type=Path)
    a = p.parse_args()
    a.out.mkdir(parents=True, exist_ok=True)
    if any(a.out.glob('[0-9]*.json')) or (a.out / 'COMPLETE').exists():
        raise SystemExit('refusing to overwrite existing run')
    states = [Path(s) for s in a.states.read_text().splitlines() if s.strip()]
    records = []
    timing=['revision\tprepare_decompress_request_s\tprocess_e2e_s\textract_write_s']
    for i, source in enumerate(states):
        base = a.out / f'{i:03d}'
        req, response = base.with_suffix('.request.xml'), base.with_suffix('.response.xml')
        start = time.monotonic()
        input_source = source
        if source.suffix == '.gz':
            input_source = base.with_suffix('.input.ofn')
            with gzip.open(source, 'rb') as src, input_source.open('wb') as dst:
                shutil.copyfileobj(src, dst)
        request(input_source, req)
        prepare_s = time.monotonic() - start
        cmd = ['/usr/bin/time', '-v', '-o', str(base.with_suffix('.time')),
               str(a.binary), 'owllinkfile', '-w', '1', '-i', str(req), '-o', str(response)]
        row = dict(revision=i, reasoner='konclude', arm='fresh', input_sha256=sha(source),
                   binary_sha256=sha(a.binary), prepare_decompress_request_s=prepare_s, command=cmd)
        start = time.monotonic()
        with base.with_suffix('.stdout').open('w') as stdout, base.with_suffix('.stderr').open('w') as stderr:
            proc = subprocess.Popen(cmd, stdout=stdout, stderr=stderr, start_new_session=True)
            try:
                rc = proc.wait(timeout=a.timeout)
                row['status'] = 'ok' if rc == 0 else 'process_error'
                row['exit_code'] = rc
            except subprocess.TimeoutExpired:
                os.killpg(proc.pid, signal.SIGKILL)
                proc.wait()
                row['status'] = 'timeout'
        row['process_e2e_s'] = time.monotonic() - start
        if row['status'] == 'ok':
            try:
                start = time.monotonic()
                rows = canonical(response)
                sig = base.with_suffix('.sig')
                data=('\n'.join(rows)+'\n').encode()
                digest=hashlib.sha256(data).hexdigest()
                if os.environ.get('DYNAMIC_DIGEST_ONLY')=='1':
                    sig=base.with_suffix('.sig.sha256');sig.write_text(digest+'\n')
                elif os.environ.get('DYNAMIC_COMPACT')=='1':
                    sig=base.with_suffix('.sig.gz')
                    with gzip.open(sig,'wb') as stream:stream.write(data)
                else:sig.write_bytes(data)
                row['extract_write_s'] = time.monotonic() - start
                row['signature_sha256'] = digest
                if a.reference:
                    ref = a.reference / sig.name
                    row['reference_sha256'] = sha(ref)
                    row['matches_reference'] = data == ref.read_bytes()
                    if not row['matches_reference']:
                        row['status'] = 'incorrect'
            except Exception as e:
                row['status'] = 'output_error'
                row['error'] = str(e)
        if input_source != source:
            input_source.unlink()
        base.with_suffix('.json').write_text(json.dumps(row, indent=2) + '\n')
        records.append(row)
        timing.append(str(i)+'\t'+'\t'.join(str(row.get(k,0)) for k in ('prepare_decompress_request_s','process_e2e_s','extract_write_s')))
        (a.out/'timings.tsv').write_text('\n'.join(timing)+'\n')
        if row['status']=='ok' and os.environ.get('DYNAMIC_DIGEST_ONLY')=='1':
            response.unlink()
            req.unlink()
        if row['status']!='ok':break
    (a.out / 'results.json').write_text(json.dumps(records, indent=2) + '\n')
    (a.out / 'COMPLETE').write_text(f'states={len(records)}\n')
    if any(row['status'] != 'ok' for row in records):
        raise SystemExit(1)

if __name__ == '__main__':
    main()
