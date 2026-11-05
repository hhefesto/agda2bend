import json,collections,re,sys
c=collections.defaultdict(lambda:[0,0,0,0,0])  # bytes files cubical_files stdlib_imports files_with_postulate
for l in open('/home/hhefesto/src/ana/run/v2/raw/agda.jsonl',errors='ignore'):
    try:d=json.loads(l)
    except:continue
    i=d['id']
    if not i.startswith('repo:'):continue
    r=i[5:].split('/')[0]
    t=d['text']
    head=t[:2000]
    cub=bool(re.search(r'OPTIONS[^#]*--(cubical|erased-cubical)(?!-)',head)) or 'import Cubical.' in t
    e=c[r]
    e[0]+=len(t);e[1]+=1;e[2]+=cub
    if re.search(r'open import (Data|Relation|Function|Algebra|Level)\b',t):e[3]+=1
rows=[(v[0]*(1-v[2]/v[1]),r,v) for r,v in c.items()]
rows.sort(reverse=True)
with open('repos.tsv','w') as o:
    for s,r,v in rows:
        o.write(f"{r}\t{int(s)}\t{v[0]}\t{v[1]}\t{v[2]}\t{v[3]}\n")
print(len(rows),sum(s for s,_,_ in rows)/1e6)
for s,r,v in rows[:30]:print(int(s/1000),r,v[1],v[2],v[3])
