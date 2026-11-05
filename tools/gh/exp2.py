# exp2.py UNIT: agda-export a unit's modules into u/UNIT/out, its own files only at the end.
# agda-export writes nothing unless the whole run checks, so one bad module cost a chunk of 30, and the next
# 30 single runs: on the biggest units 18% of the modules came out.  Here a run that fails names what failed:
# that module goes, and what imports it, and the chunk runs again (Agda's interfaces keep what checked).
import os,re,subprocess,sys,time,collections
U=sys.argv[1]; G=os.environ.get('GH','/tmp/bx/gh'); d=f'{G}/u/{U}'; out=d+'/out'; ev=d+'/ev'
if os.path.exists(d+'/DONE'): sys.exit(0)
os.makedirs(out,exist_ok=True); os.makedirs(ev,exist_ok=True); os.chdir(ev)
X=os.environ.get('X') or os.path.expanduser('~/src/agda2bend/run/a2b/gcroot-agda-export-t/bin/agda-export')
MEMG=os.environ.get('MEMG','3'); SECS=int(os.environ.get('SECS','600'))
env=dict(os.environ,AGDA_DIR=d+'/agda-dir',AGDA_EXPORT_ATTEMPT_SECS='20',AGDA_EXPORT_MAX_BYTES='20000000',AGDA_EXPORT_MAX_DEF_BYTES='2000000')
mods=[m for m in open(d+'/mods.txt').read().split('\n') if m]
roots=[r for r in open(d+'/roots.txt').read().split('\n') if r]
flags=set(open(d+'/flags.txt').read().split()) if os.path.exists(d+'/flags.txt') else set()
flags-={'--safe'}
budget=max(SECS,min(3*len(mods),2700)); t0=time.time()
left=lambda: budget-(time.time()-t0)
subprocess.run(['cp','-a',G+'/tmpl/.',out+'/'])
EXT=('agda','lagda','lagda.md')
def src(m):
    fp=m.replace('.','/')
    for r in roots:
        for e in EXT:
            p=f'{r}/{fp}.{e}'
            if os.path.exists(p): return p
    return None
IM=re.compile(r'^\s*(?:open\s+)?import\s+([^\s(;{}]+)',re.M)
imp={};rev=collections.defaultdict(set)
for m in mods:
    p=src(m)
    t=open(p,errors='ignore').read() if p else ''
    imp[m]=set(IM.findall(t))
    for x in imp[m]:
        rev[x].add(m)
bad={}
def drop(m,why):
    st=[m]
    while st:
        x=st.pop()
        if x in bad: continue
        bad[x]=why if x==m else 'imports '+m
        st+=list(rev.get(x,()))
def mod_of(p):
    for r in roots:
        if p.startswith(r+'/'):
            q=p[len(r)+1:]
            for e in EXT:
                if q.endswith('.'+e): return q[:-len(e)-1].replace('/','.')
    return None
ERR=re.compile(r'^(/[^:\n]+?\.(?:lagda\.md|lagda|agda)):(\d+)[.,][^\n]*error: \[([\w.]+)\]',re.M)
log=open('log','a'); errs=open('log.err','a'); runs=0
def run(ms,k):
    global runs
    runs+=1
    n=f'Chunk{k}'
    head=f'{{-# OPTIONS {" ".join(sorted(flags))} #-}}\n' if flags else ''
    open(n+'.agda','w').write(head+f'module {n} where\n'+''.join(f'import {m}\n' for m in ms))
    t=max(10,int(min(left(),900)))
    with open('last.log','w') as o:
        r=subprocess.run(['timeout',str(t),'nice','-n','5',X,f'--export-dir={out}','--export-skip-existing',n+'.agda','+RTS',f'-M{MEMG}g','-RTS'],stdout=o,stderr=subprocess.STDOUT,env=env).returncode
    for f in os.listdir(out):
        if f.endswith('.part') or f.startswith('Chunk'):
            try: os.unlink(os.path.join(out,f))
            except OSError: pass
    return r,open('last.log',errors='ignore').read(),len(head.split('\n'))-1
def have(m): return os.path.exists(f'{out}/{m}.sexp') or os.path.exists(f'{out}/{m}.sexp.skip')
def chunk(ms,k):
    # what can be asked for by this chunk, until it passes or nothing is left
    while left()>10:
        ms=[m for m in ms if m not in bad and not have(m)]
        if not ms: return
        r,txt,hl=run(ms,k)
        log.write(f'{k} n={len(ms)} rc={r} t={int(time.time()-t0)}\n'); log.flush()
        if r==0: return
        if r in(124,251) or 'Heap exhausted' in txt:
            if len(ms)==1: drop(ms[0],f'rc={r}'); return
            h=len(ms)//2
            chunk(ms[:h],k+'a'); chunk(ms[h:],k+'b'); return
        e=ERR.search(txt)
        if not e:
            errs.write(txt[-400:]+'\n')
            if len(ms)==1: drop(ms[0],f'rc={r}'); return
            h=len(ms)//2
            chunk(ms[:h],k+'a'); chunk(ms[h:],k+'b'); return
        p,line,kind=e.group(1),int(e.group(2)),e.group(3)
        errs.write(f'{os.path.basename(p)}:{line} {kind} {txt[e.end():e.end()+200]!r}\n'); errs.flush()
        if '/Chunk' in p:
            tx=' '.join(txt[e.end():e.end()+600].split())
            f1=re.search(r'using the (--[\w-]+) flag from a module which does not',tx)
            f2=re.search(r'not using the (--[\w-]+) flag from a module which does',tx)
            if kind.endswith('InfectiveImport') and f2 and f2.group(1) in flags: flags.discard(f2.group(1)); continue
            if kind.endswith('InfectiveImport') and f1 and f1.group(1) not in flags: flags.add(f1.group(1)); continue
            i=line-1-hl-1
            if 0<=i<len(ms): drop(ms[i],kind); continue
            if len(ms)==1: drop(ms[0],kind); return
            h=len(ms)//2
            chunk(ms[:h],k+'a'); chunk(ms[h:],k+'b'); return
        m=mod_of(p)
        if m in imp and m not in bad: drop(m,kind); continue
        # an error in a file not of this unit's modules
        if len(ms)==1: drop(ms[0],kind); return
        h=len(ms)//2
        chunk(ms[:h],k+'a'); chunk(ms[h:],k+'b'); return
i=0
for j in range(0,len(mods),30):
    if left()<=10: break
    chunk(mods[j:j+30],f'{i:03d}'); i+=1
for f in os.listdir(out):
    p=os.path.join(out,f)
    if os.path.islink(p): os.unlink(p)
n=sum(1 for f in os.listdir(out) if f.endswith('.sexp'))
open('bad.tsv','w').write(''.join(f'{m}\t{w}\n' for m,w in bad.items()))
kinds=collections.Counter(w.split(' ')[0] for w in bad.values())
print(f'{U} own={n} of {len(mods)} secs={int(time.time()-t0)} runs={runs} bad={len(bad)} {dict(kinds.most_common(4))}',flush=True)
open(d+'/DONE','w').close()
