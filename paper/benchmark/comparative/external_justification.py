"""Classification-oracle source deletion, run under the outer generation watchdog.

All subprocesses inherit the supervised process group. No per-oracle timeout
extends the single generation deadline. Successful supports still require an
independent VerifyJustification run.
"""
import json
import os
from pathlib import Path
import subprocess
import sys
from external_deletion import load_export, render, minimize
from measure_classification import digest
from taxonomy import parse, TOP, BOTTOM


def generate(config):
    row=config['generator']; runtime=config['owlapi_runtime']; module=Path(config['module'])
    output=Path(config['output']);output.mkdir(parents=True,exist_ok=False)
    assert digest(module)==config['module_sha256'],'module changed'
    for artifact in [row,runtime]:assert digest(artifact['path'])==artifact['sha256'],'runtime changed'
    if row['id']=='sequoia':
        for item in row['runtime_files']:
            assert digest(Path(row['runtime_root'])/item['path'])==item['sha256'],'Sequoia runtime changed'
    java=['java','-Xms256m','-Xmx16g','-XX:ActiveProcessorCount=1']
    def run(command, name, env=None):
        with (output/(name+'.stdout')).open('wb') as stdout,(output/(name+'.stderr')).open('wb') as stderr:
            subprocess.run(command,check=True,stdout=stdout,stderr=stderr,stdin=subprocess.DEVNULL,env=env)
    cp=str(config['classes'])+':'+runtime['path']
    run(java+['-cp',cp,'org.kmbenchmark.ExportExplanationAxioms',str(module),str(output/'export')],'export')
    run(java+['-cp',cp,'org.kmbenchmark.SourceSignature',str(module),str(output/'signature.tsv')],'signature')
    signature=(output/'signature.tsv').read_text().splitlines()
    assert signature[-1]=='Z\tcomplete','incomplete source signature'
    classes={line[2:] for line in signature if line.startswith('C\t')}
    background,axioms=load_export(output/'export')
    sub,sup=config['sub'],config['sup']
    assert sub in classes and sup in classes,'query outside module signature'
    certified_consistent=False
    if row['id']=='more':
        # Certificate is produced separately by a pinned independent reasoner.
        # Consistency of a module implies consistency of every deleted subset.
        cert=config['consistency_certificate']
        assert cert['module_sha256']==config['module_sha256'],'consistency certificate input mismatch'
        assert cert['verifier']!='more' and digest(cert['taxonomy'])==cert['taxonomy_sha256'],'invalid consistency certificate'
        checked=parse(Path(cert['taxonomy']).read_text(),cert['format'],expected_classes=classes)
        assert checked['consistent'] is True,'module consistency not established'
        certified_consistent=True
    records=[]
    def oracle(indices):
        number=len(records);prefix=f'oracle-{number:06}'
        source=output/(prefix+'.ofn');source.write_text(render(background,axioms,indices))
        taxonomy=output/(prefix+'.taxonomy')
        env=dict(os.environ)
        if row['id']=='konclude':
            xml=output/(prefix+'.owlxml');receipt=output/(prefix+'.conversion.tsv')
            converter=digest(Path(config['classes'])/'org/kmbenchmark/ConvertSyntax.class')
            run(java+['-Dkm.converter.sha256='+converter,'-cp',cp,'org.kmbenchmark.ConvertSyntax',str(source),str(xml),str(receipt),'owlxml'],prefix+'-convert')
            lines=receipt.read_text().splitlines();assert lines[-1]=='Z\tcomplete','incomplete conversion'
            fields=dict(line.split('\t',2)[1:] for line in lines if line.startswith('M\t'))
            expected={'source_sha256':digest(source),'output_sha256':digest(xml),'roundtrip_logical_axioms_equal':'true','roundtrip_signature_equal':'true','serialization':'owlxml'}
            assert all(fields.get(k)==v for k,v in expected.items()),'conversion changed oracle input'
            env['LD_LIBRARY_PATH']=str(Path(row['path']).parent/'runtime-lib')
            command=[row['path'],'classification','-w','1','-v','-i',str(xml),'-o',str(taxonomy)];fmt='owlxml'
        elif row['id']=='sequoia':
            command=[row['path'],'-no-version-check','-main','com.sequoiareasoner.cli.Sequoia','classify','--output',str(taxonomy),str(source)];fmt='functional'
        elif row['id']=='more':
            command=java+['-cp',row['path'],'org.kmbenchmark.FullIriClassifier3',row['factory'],str(source),str(taxonomy)];fmt='owlapi-tsv'
        else:raise ValueError('unsupported external generator')
        run(command,prefix,env)
        data=parse(taxonomy.read_text(),fmt,expected_classes=classes)
        used={x for edge in data['subsumptions'] for x in edge}|set(data['unsatisfiable'])
        assert not used-classes-{TOP,BOTTOM},'oracle returned unrelated class'
        if data['consistent'] is None and not certified_consistent:raise ValueError('unknown oracle consistency')
        if data['consistent'] is False or sub in data['unsatisfiable'] or sup==TOP or sub==sup:answer=True
        else:
            edges={}
            for a,b in data['subsumptions']:edges.setdefault(a,set()).add(b)
            seen=set();todo=[sub]
            while todo:
                node=todo.pop()
                if node in seen:continue
                seen.add(node);todo.extend(edges.get(node,()))
            answer=sup in seen
        records.append({'index':number,'source_sha256':digest(source),'taxonomy_sha256':digest(taxonomy),'axiom_indices':list(indices),'entailed':answer})
        (output/'oracle-checks.json').write_text(json.dumps(records,indent=2)+'\n')
        return answer
    indices,checks=minimize(len(axioms),oracle)
    support=output/'support.ofn';support.write_text(render(background,axioms,indices))
    record={'status':'generated_requires_independent_verification','method':'external-classification-source-axiom-deletion','baseline':row['id'],'checks':checks,'axiom_count':len(indices),'support_sha256':digest(support),'module_sha256':config['module_sha256'],'runner_sha256':digest(__file__)}
    (output/'generation.json').write_text(json.dumps(record,indent=2)+'\n')
    return record

if __name__=='__main__':
    print(json.dumps(generate(json.loads(Path(sys.argv[1]).read_text()))))
