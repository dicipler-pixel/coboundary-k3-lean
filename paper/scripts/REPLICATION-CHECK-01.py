# SCRIPT: REPLICATION-CHECK-01
# Independent exhaustive check of the balanced-replication lemma at q=2 (k=4 -> k=8).
# Seed: K4, edges 01,02,03 = Id; 12,13,23 = the three distinct transpositions of Sym(3).
# Claim: replicated K8 has raw N = 8*q^3 = 64, raw D = 6*q^2 = 24, ratio 8/3.
# Cost = moved-point count. Gauge minimum found by EXHAUSTIVE enumeration over all
# 6^7 root-fixed gauges (vertex 0 fixed to Id, WLOG). No sampling, no trust in the PDF.
import itertools
from sympy.combinatorics import Permutation
S3 = [Permutation(p) for p in itertools.permutations(range(3))]
Id = Permutation([0,1,2])
def cost(p): return sum(1 for i in range(3) if p(i)!=i)
def inv(p): return p**-1
# the three transpositions
a = Permutation([1,0,2]); b = Permutation([2,1,0]); c = Permutation([0,2,1])
seed = {(0,1):Id,(0,2):Id,(0,3):Id,(1,2):a,(1,3):b,(2,3):c}
def get(al,u,v):
    if u<v: return al[(u,v)]
    return inv(al[(v,u)])
def N_of(al, k):
    n=0
    for u,v,w in itertools.combinations(range(k),3):
        n += cost(get(al,u,v)*get(al,v,w)*get(al,w,u))
    return n
def D_exhaustive(al, k):
    best=None
    for g in itertools.product(S3, repeat=k-1):
        beta=(Id,)+g
        c_=0
        for u,v in itertools.combinations(range(k),2):
            c_ += cost(inv(beta[u])*al[(u,v)]*beta[v])
            if best is not None and c_>=best: break
        if best is None or c_<best: best=c_
    return best
print("SEED k=4:  N =", N_of(seed,4), " D(exhaustive) =", D_exhaustive(seed,4))
q=2; k=4*q
def rep(al,q):
    out={}
    verts=[(i,x) for i in range(4) for x in range(q)]
    idx={v:n for n,v in enumerate(verts)}
    for (i,x),(j,y) in itertools.combinations(verts,2):
        u,v=idx[(i,x)],idx[(j,y)]
        if i==j: out[(u,v)]=Id
        else: out[(u,v)]=al[(i,j)] if i<j else inv(al[(j,i)])
    return out
r=rep(seed,q)
N=N_of(r,k); D=D_exhaustive(r,k)
print(f"REPLICATED k={k} (q={q}):  N = {N}  (lemma predicts {8*q**3});  D(exhaustive over 6^7) = {D}  (lemma predicts {6*q**2})")
print(f"ratio N/D = {N}/{D} = {N/D:.6f}   vs k/3 = {k/3:.6f}")
print("LEMMA HOLDS at q=2" if (N==8*q**3 and D==6*q**2) else "LEMMA FAILS at q=2")
