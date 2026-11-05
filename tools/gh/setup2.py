import os,re,sys,json,collections
SRC='/tmp/bx/gh/src'
EXT=('.lagda.md','.lagda','.agda')
known={}  # library name -> agda-lib path
for l in open('/home/hhefesto/src/agda2bend/run/a2b/libs/agda-dir/libraries'):
    l=l.strip()
    if not l: continue
    n=None
    try:
        for x in open(l):
            m=re.match(r'\s*name\s*:\s*(\S+)',x)
            if m: n=m.group(1);break
    except OSError: continue
    if n: known[n]=l
print(known.keys())
deps=collections.Counter(); plans={}
modre=re.compile(r'^\s*(?:\\begin\{code\}\s*)?module\s+([^\s(]+)',re.M)
for R in sorted(l.split('\t')[0] for l in open('pick2.tsv')):
    d=os.path.join(SRC,R)
    libs=[];files=[]
    for root,dirs,fs in os.walk(d):
        dirs[:]=[x for x in dirs if x not in ('_build','.git','dist-newstyle','node_modules')]
        for f in fs:
            p=os.path.join(root,f)
            if f.endswith('.agda-lib') : libs.append(p)
            elif f.endswith(EXT): files.append(p)
    inc=[];dp=set();libinfo=[]
    for lp in libs:
        name=None;includes=[];dep=[];k=None
        for x in open(lp,errors='ignore'):
            x=x.split('--')[0].rstrip() if not x.lstrip().startswith('flags') else x.rstrip()
            m=re.match(r'^(\w[\w-]*)\s*:\s*(.*)$',x)
            if m:
                k=m.group(1);v=m.group(2)
                if k=='name':name=v.strip()
                elif k=='include':includes+=v.split()
                elif k=='depend':dep+=[z.strip() for z in re.split(r'[,\s]+',v) if z.strip()]
            elif k in('include','depend') and x.strip():
                if k=='include':includes+=x.split()
                else:dep+=[z.strip() for z in re.split(r'[,\s]+',x) if z.strip()]
        libinfo.append((lp,name,includes or ['.'],dep))
        for i in includes or ['.']:inc.append(os.path.normpath(os.path.join(os.path.dirname(lp),i)))
        for z in dep:dp.add(z);deps[z]+=1
    # modules: a file's module name off its text, its root the path less the name
    mods={};roots=collections.Counter();cub=0;bad=0
    for p in files:
        t=open(p,errors='ignore').read()
        if re.search(r'--(cubical|erased-cubical|allow-exec)\b',t[:4000]) or 'import Cubical.' in t: cub+=1;continue
        m=modre.search(t)
        if not m: bad+=1;continue
        M=m.group(1)
        if M=='_': bad+=1;continue
        rel=M.replace('.','/')
        stem=p
        for e in EXT:
            if p.endswith(e): stem=p[:-len(e)];break
        if not stem.endswith('/'+rel): bad+=1;continue
        root=stem[:-len(rel)-1]
        roots[root]+=1
        mods.setdefault(M,[]).append(root)
    plans[R]=dict(libs=libinfo,inc=inc,deps=sorted(dp),mods={k:v for k,v in mods.items()},roots=roots.most_common(),cub=cub,bad=bad,files=len(files))
json.dump(plans,open('plans2.json','w'))
print(deps.most_common(40))
n0=sum(1 for p in plans.values() if not p['libs']);print('no lib',n0,'of',len(plans))
print('mods',sum(len(p['mods']) for p in plans.values()),'cubical',sum(p['cub'] for p in plans.values()),'bad',sum(p['bad'] for p in plans.values()))
print('multi-root',sum(1 for p in plans.values() if len(p['roots'])>1))
