# SCRIPT: COBND-WITNESS-08b  incremental exact SA at k=8, Sym(3)
import itertools, random, time, math, sys
from fractions import Fraction
import numpy as np
seed=int(sys.argv[1]); random.seed(seed); np.random.seed(seed)
n=3; P=[tuple(p) for p in itertools.permutations(range(n))]; idx={p:i for i,p in enumerate(P)}; m=6; e_id=idx[(0,1,2)]
comp=np.array([[idx[tuple(a[b[t]] for t in range(n))] for b in P] for a in P],dtype=np.int32)
inv=np.array([idx[tuple(sorted(range(n),key=lambda t:a[t]))] for a in P],dtype=np.int32)
Dm=np.array([[sum(1 for t in range(n) if a[t]!=b[t]) for b in P] for a in P],dtype=np.int32)
T=comp[:,inv]; k=8; V=range(k)
E=[(u,v) for u in V for v in V if u<v]; Tri=[(u,v,w) for u in V for v in V for w in V if u<v<w]
G=np.array(list(itertools.product(range(m),repeat=k-1)),dtype=np.int32)
G=np.concatenate([np.full((len(G),1),e_id,dtype=np.int32),G],axis=1)
Gedge={ed:T[G[:,ed[0]],G[:,ed[1]]] for ed in E}
DmG={ed:Dm[:,Gedge[ed]] for ed in E}  # 6 x NG per edge
tri_of={ed:[t for t in Tri if ed[0] in t and ed[1] in t] for ed in E}
def val(a,u,v): return a[(u,v)] if u<v else inv[a[(v,u)]]
def tdef(a,t):
    u,v,w=t; return int(Dm[comp[comp[val(a,u,v),val(a,v,w)],val(a,w,u)],e_id])
target=Fraction(8,3); best=None; bestA=None
for restart in range(40):
    a={ed:random.randrange(m) for ed in E}
    cost=np.zeros(len(G),dtype=np.int32)
    for ed in E: cost+=DmG[ed][a[ed]]
    tri={t:tdef(a,t) for t in Tri}; num=sum(tri.values()); den=int(cost.min())
    curv=num/den if den else 1e9; Temp=0.15
    for s in range(6000):
        ed=random.choice(E); old=a[ed]; new=random.randrange(m)
        if new==old: continue
        cost2=cost-DmG[ed][old]+DmG[ed][new]; a[ed]=new
        newtri={t:tdef(a,t) for t in tri_of[ed]}
        num2=num+sum(newtri.values())-sum(tri[t] for t in tri_of[ed]); den2=int(cost2.min())
        if den2==0: a[ed]=old; continue
        v2=num2/den2
        if v2<=curv or random.random()<math.exp(-(v2-curv)/Temp):
            cost,num,den,curv=cost2,num2,den2,v2; tri.update(newtri)
            fr=Fraction(num,den)
            if fr<target: print("KILL: below bound",fr); sys.exit()
            if best is None or fr<best: best,bestA=fr,dict(a)
            if fr==target: break
        else: a[ed]=old
        Temp=max(0.01,Temp*0.9995)
    print(f"restart {restart} best so far {best} = {float(best):.5f}",flush=True)
    if best==target: break
print("BEST",best, "ATTAINED" if best==target else "not found")
if best==target:
    for ed in E:
        if bestA[ed]!=e_id: print(ed,P[bestA[ed]])
