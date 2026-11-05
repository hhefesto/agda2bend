# shard.py K [MAXMODS] [MINMODS]: the next shard, from the units whose export ended: export-ghK (export4's links, the units' own files), ev-ghK/own.txt, units.txt.
# No two modules of a shard share a name; a unit whose files are the same as an earlier unit's (a fork) is left out.  Prints the module count, 0 if under MINMODS.
import os,sys,hashlib,json,collections
K=sys.argv[1]; MAX=int(sys.argv[2]) if len(sys.argv)>2 else 800; MIN=int(sys.argv[3]) if len(sys.argv)>3 else 300
A='/home/hhefesto/src/agda2bend/run/a2b'; G='/tmp/bx/gh'
done=set()
if os.path.exists(G+'/assigned.tsv'):
    for l in open(G+'/assigned.tsv'): done.add(l.split('\t')[0])
hashes=set()
if os.path.exists(G+'/hashes.txt'): hashes=set(open(G+'/hashes.txt').read().split())
order=[l.split('\t')[0] for l in open(G+'/units.tsv')]
names=set();pick=[];new=[];skipped=[]
for U in order:
    if U in done or not os.path.exists(f'{G}/u/{U}/DONE'): continue
    d=f'{G}/u/{U}/out'
    own=[f[:-5] for f in os.listdir(d) if f.endswith('.sexp') and not f.endswith('.erasure.sexp') and f!='_index.sexp']
    if not own:
        skipped.append((U,'nothing exported'));continue
    if len(pick) and sum(len(x[1]) for x in pick)+len(own)>MAX: continue
    if any(m in names for m in own): continue
    hs=[hashlib.md5(open(f'{d}/{m}.sexp','rb').read()).hexdigest() for m in own]
    if sum(h in hashes for h in hs)>=0.7*len(hs):
        skipped.append((U,'a fork'));continue
    pick.append((U,own));names|=set(own);new+=hs;hashes|=set(hs)
n=sum(len(x[1]) for x in pick)
final=os.path.exists(G+'/export.ended')
if n==0 or (n<MIN and not final):
    # the nothing-exported and fork units are settled all the same
    with open(G+'/assigned.tsv','a') as o:
        for U,w in skipped:o.write(f'{U}\t-\t{w}\n')
    print(0);sys.exit(0)
E=f'{A}/export-gh{K}';V=f'{A}/ev-gh{K}'
os.makedirs(E,exist_ok=True);os.makedirs(V,exist_ok=True)
for f in os.listdir(G+'/tmpl'):
    if not os.path.lexists(f'{E}/{f}'): os.symlink(os.readlink(f'{G}/tmpl/{f}'),f'{E}/{f}')
for U,own in pick:
    d=f'{G}/u/{U}/out'
    for f in os.listdir(d):
        if f=='_index.sexp': continue
        if os.path.lexists(f'{E}/{f}'): os.unlink(f'{E}/{f}')
        os.link(f'{d}/{f}',f'{E}/{f}')
open(V+'/own.txt','w').write('\n'.join(sorted(names))+'\n')
open(V+'/units.txt','w').write(''.join(f'{U}\t{len(o)}\n' for U,o in pick))
with open(G+'/assigned.tsv','a') as o:
    for U,own in pick:o.write(f'{U}\tgh{K}\t{len(own)}\n')
    for U,w in skipped:o.write(f'{U}\t-\t{w}\n')
with open(G+'/hashes.txt','a') as o:
    for h in new:o.write(h+'\n')
print(n)
