#!/bin/bash
r=$1
link=$(curl -sSI "https://api.github.com/repos/$r/commits?per_page=1" | grep -i '^link:')
last=$(echo "$link" | grep -o 'page=[0-9]*>; rel="last"' | grep -o '[0-9]*' | head -1)
echo "$r total_commits~${last:-1}"
curl -sS "https://api.github.com/repos/$r/commits?per_page=1&page=${last:-1}" | python3 -I -c "import json,sys;d=json.load(sys.stdin);c=d[0]['commit'];print(' first:',c['author']['date'],c['author']['name'],'|',c['message'][:100].replace(chr(10),' '))"
curl -sS "https://api.github.com/repos/$r/commits?per_page=1" | python3 -I -c "import json,sys;d=json.load(sys.stdin);c=d[0]['commit'];print(' last:',c['author']['date'],c['author']['name'])"
