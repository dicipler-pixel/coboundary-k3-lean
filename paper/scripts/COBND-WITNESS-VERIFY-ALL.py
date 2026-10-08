# SCRIPT: COBND-WITNESS-VERIFY-ALL  independent plain-loop check of every witness k=5..8
import itertools, numpy as np
from fractions import Fraction
n=3; P=[tuple(p) for p in itertools.permutations(range(n))]; idx={p:i for i,p in enumerate(P)}; e_id=idx[(0,1,2)]
comp=np.array([[idx[tuple(a[b[t]] for t in range(n))] for b in P] for a in P]); inv=np.array([idx[tuple(sorted(range(n),key=lambda t:a[t]))] for a in P])
Dm=np.array([[sum(1 for t in range(n) if a[t]!=b[t]) for b in P] for a in P])
tr=(1,0,2)
WIT={5:{(0,1):tr,(1,2):tr,(2,3):tr},
 6:{(0,1):(1,0,2),(0,4):(2,1,0),(1,2):(0,2,1),(1,3):(1,0,2),(1,5):(1,0,2),(2,3):(1,2,0),(2,4):(0,2,1),(3,4):(2,1,0),(3,5):(2,0,1),(4,5):(1,0,2)},
 7:{(0,1):tr,(0,3):tr,(0,4):tr,(1,2):tr,(1,5):tr,(2,3):tr},
 8:{(0,1):(0,2,1),(0,2):(1,2,0),(0,3):(1,0,2),(0,4):(0,2,1),(0,5):(2,0,1),(0,6):(1,0,2),(0,7):(2,0,1),(1,2):(2,1,0),(1,4):(2,1,0),(1,5):(2,0,1),(1,7):(1,0,2),(2,4):(2,1,0),(2,5):(0,2,1),(2,6):(0,2,1),(2,7):(1,2,0),(3,4):(2,1,0),(3,5):(2,1,0),(3,7):(1,0,2),(4,6):(2,1,0),(4,7):(1,0,2),(5,6):(2,1,0),(5,7):(2,1,0)}}
for k,W in WIT.items():
    E=[(u,v) for u in range(k) for v in range(k) if u<v]; Tri=list(itertools.combinations(range(k),3))
    a={ed:idx[W.get(ed,(0,1,2))] for ed in E}
    val=lambda u,v: a[(u,v)] if u<v else inv[a[(v,u)]]
    num=sum(int(Dm[comp[comp[val(u,v),val(v,w)],val(w,u)],e_id]) for u,v,w in Tri)
    best=None;bb=None
    for g in itertools.product(range(6),repeat=k-1):
        b=(e_id,)+g;c=0
        for (u,v) in E:
            c+=Dm[comp[comp[inv[b[u]],a[(u,v)]],b[v]],e_id]
            if best is not None and c>=best: break
        else:
            if best is None or c<best: best,bb=c,b
    res={}
    for (u,v) in E:
        r=comp[comp[inv[bb[u]],a[(u,v)]],bb[v]]
        if r!=e_id: res[(u,v)]=P[r]
    ntr=sum(1 for p in res.values() if sum(x!=i for i,x in enumerate(p))==2)
    print(f"k={k}: defect {num} / gauge-min {best} = {Fraction(num,best)}  (k/3={Fraction(k,3)})  h_norm={Fraction(num*len(E),best*len(Tri))} vs {Fraction(k,k-2)}  residual {len(res)} edges: {ntr} transp, {len(res)-ntr} 3-cycles")
    print("   residual:",sorted(res.items()))
