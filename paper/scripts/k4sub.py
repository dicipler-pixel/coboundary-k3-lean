# SCRIPT: COBND-K4-SUBGROUPS  k=4 exhaustive, restricted to Z/3 (3-cycles+id) and to one Sym(2)
import itertools, numpy as np
from fractions import Fraction
n=3; P=[tuple(p) for p in itertools.permutations(range(n))]; idx={p:i for i,p in enumerate(P)}; e_id=idx[(0,1,2)]
comp=np.array([[idx[tuple(a[b[t]] for t in range(n))] for b in P] for a in P]); inv=np.array([idx[tuple(sorted(range(n),key=lambda t:a[t]))] for a in P])
Dm=np.array([[sum(1 for t in range(n) if a[t]!=b[t]) for b in P] for a in P])
k=4; E=[(u,v) for u in range(k) for v in range(k) if u<v]; Tri=list(itertools.combinations(range(k),3))
G=[(e_id,)+g for g in itertools.product(range(6),repeat=3)]
Z3=[e_id,idx[(1,2,0)],idx[(2,0,1)]]; S2=[e_id,idx[(1,0,2)]]
for name,S in (("Sym(3)",range(6)),("Z/3",Z3),("Sym(2)",S2)):
    best=None;arg=None
    for vals in itertools.product(S,repeat=6):
        a=dict(zip(E,vals)); val=lambda u,v: a[(u,v)] if u<v else inv[a[(v,u)]]
        num=sum(int(Dm[comp[comp[val(u,v),val(v,w)],val(w,u)],e_id]) for u,v,w in Tri)
        den=min(sum(Dm[comp[comp[inv[b[u]],a[(u,v)]],b[v]],e_id] for (u,v) in E) for b in G)
        if den and (best is None or Fraction(num,den)<best): best,arg=Fraction(num,den),vals
    print(f"k=4 coefficients {name:7s}: min ratio {best}  (k/3 = 4/3)  minimiser {[(E[i],P[v]) for i,v in enumerate(arg) if v!=e_id]}")
