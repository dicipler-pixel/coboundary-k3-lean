# SCRIPT: K3-V7-ADVERSARIAL  independent attacks on the load-bearing steps of the k/3 paper, with code sharing nothing with the paper's scripts
import itertools, random, numpy as np
rng=random.Random(2026)
def comp(p,q): return tuple(p[i] for i in q)            # (p o q)(i) = p(q(i))
def inv(p):
    r=[0]*len(p)
    for i,x in enumerate(p): r[x]=i
    return tuple(r)
def mv(p): return sum(1 for i,x in enumerate(p) if x!=i)
def ident(n): return tuple(range(n))
def full(k,ed,n):
    a={}
    for u in range(k):
        for v in range(k):
            if u!=v: a[(u,v)]=ident(n)
    for (u,v),p in ed.items(): a[(u,v)]=p; a[(v,u)]=inv(p)
    return a
def Ncount(k,a): return sum(mv(comp(comp(a[(u,v)],a[(v,w)]),a[(w,u)])) for u,v,w in itertools.combinations(range(k),3))
def cost(k,a,b): return sum(mv(comp(comp(b[u],a[(u,v)]),inv(b[v]))) for u,v in itertools.combinations(range(k),2))
def Dmin(k,a,G):                                       # exhaustive, root fixed (constant left factor conjugates every edge term)
    best=10**9
    for rest in itertools.product(G,repeat=k-1):
        c=cost(k,a,(ident(len(G[0])),)+rest)
        if c<best: best=c
    return best
S3=list(itertools.permutations(range(3)))
# A1: star-gauge identity sum_x cost(beta_x) = 3N, in Sym(4) and Sym(5), random cochains
bad=0
for n in (4,5):
    Sn=list(itertools.permutations(range(n)))
    for _ in range(60):
        k=rng.randint(4,7); ed={(u,v):rng.choice(Sn) for u,v in itertools.combinations(range(k),2)}; a=full(k,ed,n)
        st=sum(cost(k,a,tuple(ident(n) if u==x else a[(x,u)] for u in range(k))) for x in range(k))
        bad+= st!=3*Ncount(k,a)
print("A1 star identity sum_x cost = 3N, 120 random cochains in Sym(4), Sym(5) on K_4..K_7: failures =",bad)
# A2: replication on random cochains (not the seed), K_4 -> K_8, exhaustive both sides
def replicate(k,a,q,n):
    K=k*q; cl=lambda v: v//q; ed={}
    for u,v in itertools.combinations(range(K),2):
        if cl(u)!=cl(v): ed[(u,v)]=a[(cl(u),cl(v))]
    return K, full(K,ed,n)
P=np.array(S3); idx={p:i for i,p in enumerate(S3)}
MT=np.array([[idx[comp(p,q)] for q in S3] for p in S3]); IV=np.array([idx[inv(p)] for p in S3]); MV=np.array([mv(p) for p in S3])
def Dfast(K,a):
    g=np.array(list(itertools.product(range(6),repeat=K-1)),dtype=np.int8); g=np.hstack([np.zeros((len(g),1),dtype=np.int8),g])
    tot=np.zeros(len(g),dtype=np.int32)
    for u,v in itertools.combinations(range(K),2):
        e=idx[a[(u,v)]]
        tot+=MV[MT[MT[g[:,u],e],IV[g[:,v]]]]
    return int(tot.min())
ok=0; rows=[]
for _ in range(6):
    ed={(u,v):rng.choice(S3) for u,v in itertools.combinations(range(4),2)}; a=full(4,ed,3)
    N1,D1=Ncount(4,a),Dmin(4,a,S3)
    if D1==0: continue
    K,b=replicate(4,a,2,3); N2,D2=Ncount(K,b),Dfast(K,b)
    rows.append((N1,D1,N2,D2)); ok+= (N2==8*N1 and D2==4*D1)
print("A2 replication on random K_4 cochains, q=2, exhaustive 6^7 gauges:",rows," all N->8N, D->4D:",ok==len(rows))
# A3: parity retraction: for random H-valued cochains (H={Id,t}), S3 gauge minimum == H gauge minimum
t=(1,0,2); H=[ident(3),t]; bad=0; cnt=0
for k in (4,5,6):
    for _ in range(8 if k<6 else 3):
        ed={(u,v):rng.choice(H) for u,v in itertools.combinations(range(k),2)}; a=full(k,ed,3)
        bad+= Dmin(k,a,H)!=Dfast(k,a); cnt+=1
print(f"A3 parity retraction, {cnt} random binary cochains on K_4..K_6: S3 minimum != H minimum in {bad} cases")
# A4: Kozlov k=6 witness K_{2,2} inside Sym(3)
ed={(u,v):t for u in (0,1) for v in (2,3)}; a=full(6,ed,3)
print("A4 K_{2,2} at k=6 in Sym(3): N, D, N/D =",Ncount(6,a),Dfast(6,a),Ncount(6,a)/Dfast(6,a)," (k/3 = 2)")
# A5: cross-degree seed minima, fresh distance code
def derr(s,tau):
    n,m=len(s),len(tau); return 1-sum(1 for j in range(min(n,m)) if s[j]==tau[j])/max(n,m)
seed=full(4,{(1,2):(0,2,1),(1,3):(1,0,2),(2,3):(2,1,0)},3)
from fractions import Fraction
res={}
for m in (2,3,4):
    Sm=list(itertools.permutations(range(m))); best=None
    for rest in itertools.product(Sm,repeat=3):
        b=(ident(m),)+rest
        c=sum(Fraction(derr(seed[(u,v)],comp(inv(b[u]),b[v]))).limit_denominator(100) for u,v in itertools.combinations(range(4),2))
        best=c if best is None or c<best else best
    res[m]=best
print("A5 cross-degree seed minima m=2,3,4:",{m:str(v) for m,v in res.items()}," (paper: 10/3, 2, 3)")
