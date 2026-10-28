#!/bin/bash
q=$(python3 -c "import urllib.parse,sys;print(urllib.parse.quote(sys.argv[1]))" "$1")
curl -sS -m 40 "https://api.crossref.org/works?query.bibliographic=$q&rows=${2:-4}&mailto=robert.hoehndorf@kaust.edu.sa" | python3 -I -c "
import json,sys;d=json.load(sys.stdin)
for it in d['message']['items']:
  au=', '.join((a.get('given','')+' '+a.get('family','')).strip() for a in it.get('author',[]))
  yr=(it.get('issued',{}).get('date-parts') or [[None]])[0][0]
  print(it.get('DOI'),'|',yr,'|',(it.get('title') or [''])[0],'|',(it.get('container-title') or [''])[0],'|',au)
"
