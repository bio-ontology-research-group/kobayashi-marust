#!/bin/bash
q=$(python3 -c "import urllib.parse,sys;print(urllib.parse.quote(sys.argv[1]))" "$1")
for i in 1 2 3 4; do
 out=$(curl -sS -m 30 -A "Mozilla/5.0 research-bot" "https://dblp.org/search/publ/api?q=$q&format=json&h=${2:-6}")
 if echo "$out" | head -c1 | grep -q '{'; then
  echo "$out" | python3 -I -c "import json,sys;d=json.load(sys.stdin);[print('|'.join(str(h['info'].get(k,'')) for k in ('key','year','venue','doi','title')), '|', ', '.join(a['text'] for a in (h['info'].get('authors',{}).get('author',[]) if isinstance(h['info'].get('authors',{}).get('author',[]),list) else [h['info']['authors']['author']]))) for h in d['result']['hits'].get('hit',[])]"
  exit 0
 fi
 sleep 3
done
echo "FAIL: $(echo "$out"|head -c 200)"
