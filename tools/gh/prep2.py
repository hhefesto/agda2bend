# prep.py: units of export from plans2.json: a repository's libraries that depend on each other, its other roots each alone.  u/UNIT/{agda-dir,mods.txt,roots.txt,flags.txt}, units2.tsv
import os,re,json,collections,sys
plans=json.load(open('plans2.json'))
A='/home/hhefesto/src/agda2bend/run/a2b'
STD='/nix/store/rih0lapv6s60scaq0c4bkaw13jqpdwbv-standard-library-2.3/standard-library.agda-lib'
KNOWN={}
for l in open(A+'/libs/agda-dir/libraries'):
    l=l.strip()
    if l: KNOWN[os.path.basename(l)[:-len('.agda-lib')]]=l
have=set(f[:-5] for f in os.listdir(A+'/export4') if f.endswith('.sexp') and not f.endswith('.erasure.sexp'))
libmap={'agda-categories':'agda-categories','agdarsec':'agdarsec','generics':'generics','agda-prelude':'agda-prelude','functional-linear-algebra':'functional-linear-algebra','agda2hs-base':'base','base':'base'}
def rewrite(lp,keep):
    k=None;res=[];seen=False
    for x in open(lp,errors='ignore').read().split('\n'):
        m=re.match(r'^(\w[\w-]*)\s*:(.*)$',x)
        if m:k=m.group(1)
        if k=='depend':
            if not seen:res.append('depend: '+' '.join(keep));seen=True
            continue
        res.append(x)
    if not seen:res.append('depend: '+' '.join(keep))
    open(lp,'w').write('\n'.join(res)+'\n')
def flags_of(lp):
    fl=[];k=None
    for x in open(lp,errors='ignore'):
        m=re.match(r'^(\w[\w-]*)\s*:(.*)$',x)
        if m:
            k=m.group(1);v=m.group(2)
        else:v=x
        if k=='flags':fl+=[z for z in v.split() if z.startswith('--')]
    return fl
units=[];skip=collections.Counter();vend=[]
def emit(U,kind,rs,ms,comp):
    ms=sorted(set(ms))
    c=[M for M in ms if M in have]
    if c:
        skip['vendors a library module']+=1;vend.append((U,len(ms),len(c)));return
    d=f'/tmp/bx/gh/u/{U}';os.makedirs(d+'/agda-dir',exist_ok=True);os.makedirs(d+'/out',exist_ok=True)
    ls=[STD];df=['standard-library-2.3'];fl=[]
    if comp:
        names={n for _,n,_,_ in comp}
        for lp,name,inc,dep in comp:
            keep=['standard-library-2.3']
            for z in dep:
                if z in names:keep.append(z)
                elif z in libmap:
                    keep.append(z if z!='agda2hs-base' else 'base')
                    q=KNOWN.get(libmap[z])
                    if q and q not in ls:ls.append(q)
            rewrite(lp,keep);ls.append(lp);df.append(name);fl+=flags_of(lp)
    else:
        r=rs[0];lp=os.path.join(r,'gh-u.agda-lib')
        if [f for f in os.listdir(r) if f.endswith('.agda-lib') and f!='gh-u.agda-lib']:
            skip['a library file at an unincluded root']+=1;return
        open(lp,'w').write(f'name: gh-u\ninclude: .\ndepend: standard-library-2.3\n')
        ls.append(lp);df.append('gh-u')
    open(d+'/agda-dir/libraries','w').write('\n'.join(ls)+'\n')
    open(d+'/agda-dir/defaults','w').write('\n'.join(df)+'\n')
    open(d+'/mods.txt','w').write('\n'.join(ms)+'\n')
    open(d+'/roots.txt','w').write('\n'.join(rs)+'\n')
    open(d+'/flags.txt','w').write(' '.join(sorted(set(fl)))+'\n')
    units.append((U,len(ms)))
for R,p in sorted(plans.items()):
    libs=[];names=set();cub=[]
    for lp,name,inc,dep in p['libs']:
        if name is None or name in names or os.path.basename(lp).startswith('gh-u'):continue
        if re.match(r'^(standard-library|stdlib|agda-stdlib|cubical)',name):
            continue
        fl=flags_of(lp)
        if any(f in('--cubical','--erased-cubical','--allow-exec') for f in fl):
            cub.append(lp);skip['a cubical library']+=1;continue
        names.add(name);libs.append((lp,name,inc,dep))
    # the libraries' components, by depend
    par={n:n for _,n,_,_ in libs}
    def find(x):
        while par[x]!=x:x=par[x]
        return x
    for lp,n,inc,dep in libs:
        for z in dep:
            if z in par:par[find(z)]=find(n)
    comps=collections.defaultdict(list)
    for L in libs:comps[find(L[1])].append(L)
    byroot=collections.defaultdict(list)
    for M,rs in p['mods'].items():
        for r in rs:byroot[r].append(M)
    cubinc=set(os.path.normpath(os.path.join(os.path.dirname(lp),i)) for lp in cub for i in ['.'])
    k=0;used=set()
    groups=[]
    for comp in sorted(comps.values(),key=lambda c:c[0][1]):
        inc=set(os.path.normpath(os.path.join(os.path.dirname(lp),i)) for lp,name,I,dep in comp for i in (I or ['.']))
        rs=[r for r in byroot if r in inc]
        ms=[M for r in rs for M in byroot[r]]
        used|=set(rs)
        if ms:groups.append((rs,ms,comp))
    for r in sorted(byroot,key=lambda r:-len(byroot[r])):
        if r in used:continue
        if any(r==c or r.startswith(c+'/') for c in cubinc):continue
        groups.append(([r],byroot[r],None))
    groups.sort(key=lambda g:-len(g[1]))
    for rs,ms,comp in groups:
        U=R if k==0 else f'{R}@{k}';k+=1
        emit(U,None,rs,ms,comp)
units.sort(key=lambda x:-x[1])
open('units2.tsv','w').write(''.join(f'{u}\t{n}\n' for u,n in units))
open('vend2.tsv','w').write(''.join(f'{u}\t{n}\t{c}\n' for u,n,c in vend))
print(len(units),sum(n for _,n in units),dict(skip))
print(units[:30])
