import json,subprocess
from pathlib import Path
root=Path('/home/leechuck/Public/software/kobayashi-marust')
art=root/'.work/artifacts';inp=root/'.work/inputs/v143-harness'
remote='dragon:/ibex/scratch/hohndor/km/v143-harness-20260918/candidate-v143-rc2/'
subprocess.run(['rsync','-a','-e','ssh -q','--include=*/','--include=results.jsonl','--include=COMPLETE','--include=environment.txt','--include=lscpu.txt','--include=*.stderr','--exclude=*',remote,str(art/'v143-final-rc2')+'/'],check=True)
subprocess.run(['python3',str(inp/'summarize.py'),str(art/'v143-baseline'),str(art/'v143-final-rc2'),'--output',str(art/'v143-diagnostics/rc2-progress.json')],check=True)
s=json.loads((art/'v143-diagnostics/rc2-progress.json').read_text());p=s['panels']['v143-final-rc2'];q=s['paired']['v143-final-rc2']
print(json.dumps(dict(observed=p['observed'],complete_chunks=p['complete_chunks'],outcomes=p['outcomes'],new=q['new_completions'],lost=q['lost_completions'],changed=q['changed_output_hashes'])),flush=True)
files=[]
for chunk in (art/'v143-final-rc2').iterdir():
 if not (chunk/'results.jsonl').exists():continue
 for line in (chunk/'results.jsonl').read_text().splitlines():
  try:r=json.loads(line)
  except json.JSONDecodeError:continue
  if r.get('kind')!='case':continue
  if r['ont']in q['new_completions']:
   files.append(chunk.name+'/output/'+r['ont']+'.json')
(inp/'rc2-evidence-files.txt').write_text('\n'.join(files)+'\n')
subprocess.run(['rsync','-a','-e','ssh -q','--files-from='+str(inp/'rc2-evidence-files.txt'),remote,str(art/'v143-final-rc2')+'/'],check=True)
