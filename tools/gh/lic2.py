import json,subprocess,sys
rows=[l.rstrip('\n').split('\t') for l in open('repos.tsv')]
rows=[r for r in rows if int(r[1])<30000]
out=open('lic2.tsv','w')
B=60
for k in range(0,len(rows),B):
    part=rows[k:k+B]
    q=[]
    for i,r in enumerate(part):
        if '__' not in r[0]: continue
        o,n=r[0].split('__',1)
        q.append('r%d: repository(owner:%s,name:%s){licenseInfo{spdxId} isFork stargazerCount pushedAt diskUsage defaultBranchRef{name target{oid}} parent{nameWithOwner}}'%(i,json.dumps(o),json.dumps(n)))
    query='query{'+' '.join(q)+'}'
    p=subprocess.run(['gh','api','graphql','-f','query='+query],capture_output=True,text=True)
    try: d=json.loads(p.stdout).get('data') or {}
    except Exception as e: d={}
    for i,r in enumerate(part):
        v=d.get('r%d'%i)
        if not v:
            out.write('\t'.join([r[0],r[1],'GONE','','','','','',''])+'\n'); continue
        b=v.get('defaultBranchRef') or {}
        out.write('\t'.join([r[0],r[1],(v.get('licenseInfo') or {}).get('spdxId') or 'NONE',str(v['isFork']),str(v['stargazerCount']),v['pushedAt'] or '',str(v['diskUsage']),(b.get('name') or ''),((b.get('target') or {}).get('oid') or '')])+'\t'+((v.get('parent') or {}).get('nameWithOwner') or '')+'\n')
    out.flush()
