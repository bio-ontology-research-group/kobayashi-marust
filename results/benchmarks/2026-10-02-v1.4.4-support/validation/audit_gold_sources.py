import hashlib,json,pathlib,sys
root=pathlib.Path('/ibex/scratch/projects/c2014/hohndor/km/v144-support-recovery-20261003')
rows=json.loads((root/'final-gold-source-inputs.json').read_text());results=[]
for r in rows:
    p=pathlib.Path('/ibex/scratch/hohndor/km/corpus')/r['ontology'];h=hashlib.sha256()
    with p.open('rb') as f:
        for block in iter(lambda:f.read(1024*1024),b''):h.update(block)
    results.append(dict(r,actual_sha256=h.hexdigest(),matches=h.hexdigest()==r['expected_sha256']))
report={'cases':len(results),'all_sources_match_inventory':all(r['matches'] for r in results),'results':results}
(root/('final-gold-source-audit-'+sys.argv[1]+'.json')).write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='results'}));assert report['all_sources_match_inventory']
