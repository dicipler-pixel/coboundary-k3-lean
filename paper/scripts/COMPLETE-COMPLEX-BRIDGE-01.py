#!/usr/bin/env python3
# SCRIPT: COMPLETE-COMPLEX-BRIDGE-01  replication, retraction, cross-degree, Gram/projector/Cayley, entropy repair, isospectral probe
"""Exact complete-complex witnesses and explicit projector/Smith bridges.

Requires Python 3.10+, numpy, sympy. Run without editing:
    python COMPLETE-COMPLEX-BRIDGE-01.py

Status: the general blow-up statement is proved in the companion note.
This program exhausts gauges only where explicitly reported (k <= 8).
Larger gauge minima below are THEOREM VALUES, not enumerated values.
No claim of a Lean compilation or of an optical material identification.
Original inputs: Beasley's complete_complex_k3_permutation.pdf, Appendix A.
Checks fixed in advance: exact agreement of original witnesses; all 216 K4
root-fixed gauge costs >= 6; doubled K4 minimum = 24 over all 6^7 gauges;
triangle counts scale cubically; Gram/graph-projector/Cayley identities;
negative controls for max-normalized entropy and scalar spectral blindness.
"""
from __future__ import annotations
import itertools as it
from fractions import Fraction
import math
import numpy as np
import sympy as sp

P = list(it.permutations(range(3)))
IDX = {p:i for i,p in enumerate(P)}
ID = IDX[(0,1,2)]
COM = np.array([[IDX[tuple(p[q[j]] for j in range(3))] for q in P] for p in P], dtype=np.int16)
INV = np.array([IDX[tuple(p.index(j) for j in range(3))] for p in P],dtype=np.int16)
MOV = np.array([sum(p[j]!=j for j in range(3)) for p in P],dtype=np.int16)
BASE = {(1,2):(0,2,1),(1,3):(1,0,2),(2,3):(2,1,0)}
WITNESSES = {
 4: BASE,
 5: {(0,1):(1,0,2),(1,2):(1,0,2),(2,3):(1,0,2)},
 6: {(0,1):(1,2,0),(1,3):(1,2,0),(0,3):(2,0,1),(0,4):(2,0,1),(1,5):(2,0,1),(4,5):(2,0,1)},
 7: {(0,1):(1,0,2),(0,3):(1,0,2),(0,4):(1,0,2),(1,2):(1,0,2),(1,5):(1,0,2),(2,3):(1,0,2)},
 8: {(0,1):(0,2,1),(0,7):(0,2,1),(1,2):(0,2,1),(2,5):(0,2,1),(2,7):(0,2,1),
     (1,3):(1,0,2),(1,4):(1,0,2),(1,6):(1,0,2),(3,7):(1,0,2),
     (0,4):(2,1,0),(2,3):(2,1,0),(2,4):(2,1,0),(4,7):(2,0,1)}
}
EXPECTED = {4:(8,6),5:(10,6),6:(36,18),7:(28,12),8:(72,27)}

def edge_dict(k: int, W: dict) -> dict:
    return {(u,v): IDX[W.get((u,v),(0,1,2))] for u,v in it.combinations(range(k),2)}

def numerator(k: int, W: dict) -> int:
    a=edge_dict(k,W)
    return sum(int(MOV[COM[COM[a[u,v],a[v,w]],INV[a[u,w]]]]) for u,v,w in it.combinations(range(k),3))

def gauges(k: int) -> np.ndarray:
    if k>8: raise ValueError('Exhaustive gauge enumeration deliberately limited to k<=8.')
    b=np.full((6**(k-1),k),ID,dtype=np.int16)
    x=np.arange(len(b),dtype=np.int64)
    for j in range(1,k): b[:,j]=x%6; x//=6
    return b

def gauge_costs(k: int, W: dict) -> np.ndarray:
    b=gauges(k); cost=np.zeros(len(b),dtype=np.int32)
    for (u,v),a in edge_dict(k,W).items():
        cost+=MOV[COM[COM[INV[b[:,u]],a],b[:,v]]]
    return cost

def lift(k: int, W: dict, q: int) -> dict:
    if q<1: raise ValueError('q must be positive')
    return {(u,v):W[(u//q,v//q)] for u,v in it.combinations(range(k*q),2)
            if u//q!=v//q and (u//q,v//q) in W}

def permutation(cycles: list[list[int]], n: int | None=None) -> np.ndarray:
    if n is None: n=1+max(j for c in cycles for j in c)
    p=list(range(n))
    for c in cycles:
        for j,i in enumerate(c): p[i]=c[(j+1)%len(c)]
    U=np.zeros((n,n),dtype=int)
    for i,j in enumerate(p): U[j,i]=1
    return U

def gram(U: np.ndarray) -> np.ndarray:
    I=np.eye(len(U)); A=U-I
    return A.conj().T@A/2

def entropy(values: np.ndarray) -> float:
    a=np.clip(np.asarray(values,dtype=float),0,1)
    a=a[(a>1e-12)&(a<1-1e-12)]
    return float(np.sum(-a*np.log(a)-(1-a)*np.log1p(-a)))

print('COMPLETE-COMPLEX-BRIDGE-01')
print('Exact integers for all gauge costs. Float residuals only for spectral checks.\n')
print('1. ORIGINAL APPENDIX A WITNESSES, ALL ROOT-FIXED S3 GAUGES')
for k,W in WITNESSES.items():
    N=numerator(k,W); costs=gauge_costs(k,W); D=int(costs.min())
    assert (N,D)==EXPECTED[k]
    print(f'k={k}: N={N}, D={D}, ratio={Fraction(N,D)}, gauges={len(costs)}')
base_costs=gauge_costs(4,BASE)
unique,counts=np.unique(base_costs,return_counts=True)
print('K4 complete cost histogram:', dict(zip(map(int,unique),map(int,counts))))

print('\n2. BALANCED LIFT: ALL POWERS OF TWO AND EVERY MULTIPLE OF FOUR')
for q in [1,2,3,4,8,16]:
    W=lift(4,BASE,q); N=numerator(4*q,W); D_theorem=6*q*q
    assert N==8*q**3 and len(W)==3*q*q
    D_exhaust=int(gauge_costs(4*q,W).min()) if q<=2 else None
    if D_exhaust is not None: assert D_exhaust==D_theorem
    print(f'k={4*q}: support={len(W)}, N={N}, D(theorem)={D_theorem}, '
          f'D(exhaustive)={D_exhaust}, ratio={Fraction(N,D_theorem)}')

print('\n3. OPTIONAL DIFFERENT-DEGREE BASE AUDIT: HAMMING WITH ERRORS')
for n in [2,3,4]:
    pp=list(it.permutations(range(n))); inverses=[tuple(p.index(j) for j in range(n)) for p in pp]
    b=np.zeros((len(pp)**3,4),dtype=np.int32); x=np.arange(len(b))
    for j in range(1,4): b[:,j]=x%len(pp); x//=len(pp)
    costs=np.zeros(len(b),dtype=np.int32)
    for u,v in it.combinations(range(4),2):
        a=BASE.get((u,v),(0,1,2))
        tab=np.array([[max(n,3)-sum(a[j]==p[qinv[j]] for j in range(min(n,3)))
                       for qinv in inverses] for p in pp],dtype=np.int16)
        costs+=tab[b[:,u],b[:,v]]
    D=Fraction(int(costs.min()),max(n,3))
    assert D>=2
    print(f'comparison degree={n}, minimum edge-distance sum={D}, root-fixed gauges={len(b)}')
print('Degrees n>=5: elementary baseline is 6*(1-3/n)>=12/5>2.')

print('\n4. SIGN RETRACTION S3 -> {ID, FIXED TRANSPOSITION}')
def sign(p): return (-1)**sum(p[i]>p[j] for i in range(3) for j in range(i+1,3))
signs=np.array([sign(p) for p in P])
for i,j in it.product(range(6),repeat=2):
    assert signs[COM[i,j]]==signs[i]*signs[j]
    projected_distance=0 if signs[i]==signs[j] else 2
    original_distance=sum(P[i][t]!=P[j][t] for t in range(3))
    assert projected_distance<=original_distance
print('All 36 group-pair checks: homomorphism and nonexpansion pass.')

print('\n5. GRAM / GRAPH-PROJECTOR / HAMMING / CAYLEY IDENTITIES')
rng=np.random.default_rng(20260905)
max_g=max_graph=max_ham=max_cayley=0.0
for n in range(2,21):
    for _ in range(3):
        p=rng.permutation(n); U=np.eye(n)[:,p]; I=np.eye(n)
        G=gram(U); max_g=max(max_g,float(np.linalg.norm(G-(I-(U+U.T)/2))))
        QI=np.vstack((I,I))/math.sqrt(2); QU=np.vstack((I,U))/math.sqrt(2)
        PI=QI@QI.T; PU=QU@QU.T
        max_graph=max(max_graph,float(np.linalg.norm(QU.T@(np.eye(2*n)-PI)@QU-G/2)))
        dH=float(np.mean(p!=np.arange(n)))
        max_ham=max(max_ham,abs(np.linalg.norm(PU-PI,'fro')**2/n-dH))
        vals,V=np.linalg.eigh(G); V=V[:,vals>1e-10]
        if not V.shape[1]: continue
        Ur=V.T@U@V; Ir=np.eye(len(Ur)); Gr=V.T@G@V
        Z=(Ir+Ur)@np.linalg.inv(Ir-Ur)
        S=(Z-Ir)@np.linalg.inv(Z+Ir)
        X=-1j*Z
        res=max(np.linalg.norm(Z+Z.T),np.linalg.norm(S-Ur),
                np.linalg.norm(Gr/2-np.linalg.inv(Ir+X@X)))
        max_cayley=max(max_cayley,float(res))
assert max(max_g,max_graph,max_ham,max_cayley)<1e-10
print('57 permutations, n=2..20, three per size.')
print(f'max Gram={max_g:.3e}; graph={max_graph:.3e}; Hamming={max_ham:.3e}; Cayley={max_cayley:.3e}')

print('\n6. ENTROPY NEGATIVE CONTROL AND FIXED-SCALE REPAIR')
for ell in [2,3,4,5,6,8,16,64]:
    U=permutation([list(range(ell))]); vals=np.linalg.eigvalsh(gram(U))
    old=entropy(vals/vals.max()); new=entropy(vals/2)
    print(f'cycle={ell}: S(max-normalized)={old:.12f}, S(G/2)={new:.12f}, S(G/2)/ell={new/ell:.12f}')
    if ell==3: assert old<1e-12 and new>1
    if ell>2: assert new>0
print('Long-cycle limit:',2*math.log(2)-1)

print('\n7. ISOSPECTRAL PERMUTATION DEFECTS, DIFFERENT FIXED-PROBE RESPONSE')
Ua=sp.Matrix(permutation([[0,1],[2,3]])); Ub=sp.Matrix(permutation([[0,2],[1,3]])); I4=sp.eye(4)
Ga=(Ua-I4).T*(Ua-I4)/2; Gb=(Ub-I4).T*(Ub-I4)/2
# b=(e0+e1)/sqrt(2); work with an integer vector and divide quadratic forms by 2.
b=sp.Matrix([1,1,0,0]); A=I4+Ga; B=I4+Gb
ma=(b.T*A.inv()*b)[0]/2; mb=(b.T*B.inv()*b)[0]/2
ra=sp.cancel((1-ma)/(1+ma)); rb=sp.cancel((1-mb)/(1+mb))
assert Ga.charpoly().as_expr()==Gb.charpoly().as_expr()
assert (A.det(),B.det(),ma,mb,ra,rb)==(9,9,1,sp.Rational(2,3),0,sp.Rational(1,5))
print('Both Gram characteristic polynomials:',Ga.charpoly().as_expr())
print(f'det(I+Ga)={A.det()}, det(I+Gb)={B.det()}, identical scalar logdet')
print(f'probe responses Ma={ma}, Mb={mb}; dimensionless Smith values={ra}, {rb}')
t=sp.symbols('t')
for G,M in [(Ga,ma),(Gb,mb)]:
    K=I4+G
    assert sp.expand((K+t*b*b.T/2).det()-K.det()*(1+t*M))==0
print('Rank-one determinant perturbation identity checked exactly for both probes.')
print('\nPASS: all specified checks. No large-k gauge enumeration or Lean certification claimed.')
