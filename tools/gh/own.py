# own.py CORPUS OWN.txt OUT: OUT holds (hard links) the files of CORPUS whose Agda module is in OWN.txt, off each file's first line
import os,sys
C,O,T=sys.argv[1:4]
own=set(open(O).read().split())
n=k=0
for root,ds,fs in os.walk(C):
    for f in fs:
        if not f.endswith('.bend'):continue
        p=os.path.join(root,f);n+=1
        with open(p,errors='ignore') as h:head=h.readline()
        M=head.rsplit(' ',1)[-1].strip()
        if M in own:
            q=os.path.join(T,os.path.relpath(p,C));os.makedirs(os.path.dirname(q),exist_ok=True)
            if not os.path.exists(q):os.link(p,q)
            k+=1
print(f'own: {k} of {n} files')
