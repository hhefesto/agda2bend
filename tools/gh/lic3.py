# lic3.py: repositories whose licence text forbids what training does, whatever GitHub calls them: left out of the shards (assigned.tsv, "-"), with the reason in licout.tsv.
# The user's OK covers GPL and AGPL and public code with no licence, not a licence that says non-commercial or no-derivatives, or a proprietary one.
import os,re,csv
PAT=re.compile(r'non-?\s?commercial|proprietary software|no-?derivatives|anti-capitalist|all rights reserved\.?\s*$|NC-QGE|PROPRIETARY',re.I|re.M)
GOOD={'MIT','BSD-3-Clause','BSD-2-Clause','Apache-2.0','GPL-3.0','GPL-2.0','AGPL-3.0','LGPL-3.0','LGPL-2.1','MPL-2.0','Unlicense','CC0-1.0','ISC','BSL-1.0','Zlib','UPL-1.0','WTFPL','CC-BY-4.0','CC-BY-SA-4.0'}
rows=[l.rstrip('\n').split('\t') for f in ('pick.tsv','pick2.tsv') for l in open(f)]
out=[]
for r in rows:
    R,lic=r[0],r[2]
    if lic in GOOD: continue
    d=f'src/{R}'; hits=[]
    for root,ds,fs in os.walk(d):
        if root.count('/')-d.count('/')>1: ds[:]=[]; continue
        for f in fs:
            if re.search(r'licen[cs]e|copying',f,re.I):
                try: t=open(os.path.join(root,f),errors='ignore').read()
                except OSError: continue
                m=re.search(r'non-?\s?commercial|no-?\s?derivatives|anti-capitalist|NC-QGE|proprietary software license',t,re.I)
                if m: hits.append((f,' '.join(m.group(0).split())[:40])); continue
                if re.search(r'GNU (AFFERO |LESSER )?GENERAL PUBLIC LICENSE|Mozilla Public License|Redistribution and use|Permission is hereby granted|Permission to use|Apache License',t,re.I): continue
                m=re.search(r'all rights reserved\.?\s*$|PROPRIETARY',t,re.I|re.M)
                if m: hits.append((f,' '.join(m.group(0).split())[:40]))
    if hits: out.append((R,lic,hits[0][0],hits[0][1]))
print(len(rows),len(out))
open('licout.tsv','w').write(''.join('\t'.join(x)+'\n' for x in out))
