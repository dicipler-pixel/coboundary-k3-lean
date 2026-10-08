# SCRIPT: K3-V6-CHECKS  checks the fifth review's claims: (A) S(U)/n <= h(d_H/2); (B) d_H/2 <= mean theta^2 <= pi^2 d_H/8; (C) kernel of a positive sum of Grams = vectors constant on orbits of the generated group (dim = number of orbits) and the sum is half a Schreier-graph Laplacian; (D) Jensen and chord bounds on a probe bin
import numpy as np, random
rng=random.Random(11); h=lambda x: 0.0 if x<=0 or x>=1 else -(x*np.log(x)+(1-x)*np.log(1-x))
def perm(n): p=list(range(n)); rng.shuffle(p); return p
def mat(p): n=len(p); U=np.zeros((n,n)); [U.__setitem__((p[i],i),1) for i in range(n)]; return U
worstA=worstB=-1; tightA=0
for _ in range(2000):
    n=rng.randint(2,14); p=perm(n)
    if rng.random()<0.5:            # sparse defects too
        p=list(range(n)); i,j=rng.sample(range(n),2); p[i],p[j]=p[j],p[i]
    U=mat(p); d=sum(p[i]!=i for i in range(n))/n
    K=(2*np.eye(n)-U-U.T)/4; lam=np.clip(np.linalg.eigvalsh(K),0,1)
    S=sum(h(x) for x in lam)/n; worstA=max(worstA,S-h(d/2))
    assert abs(np.trace(K)/n-d/2)<1e-12
    q=perm(n); V=mat(q); dUV=sum(p[i]!=q[i] for i in range(n))/n
    s=np.clip(np.linalg.svd((np.eye(n)+U.T@V)/2,compute_uv=False),0,1); th=np.arccos(s)
    m=np.mean(th**2); worstB=max(worstB, dUV/2-m, m-np.pi**2*dUV/8)
print(f"(A) max of S/n - h(d_H/2) over 2000 permutations: {worstA:.2e}  (must be <= 0)")
print(f"(B) max violation of d_H/2 <= mean theta^2 <= pi^2 d_H/8: {worstB:.2e}  (must be <= 0)")
bad=0
for _ in range(500):
    n=rng.randint(3,16); r=rng.randint(1,3); ps=[perm(n) for _ in range(r)]
    for t in range(r):                     # sometimes sparse generators so several orbits survive
        if rng.random()<0.6:
            p=list(range(n)); i,j=rng.sample(range(n),2); p[i],p[j]=p[j],p[i]; ps[t]=p
    w=[rng.uniform(0.2,3) for _ in range(r)]
    G=sum(wj*(np.eye(n)-(mat(p)+mat(p).T)/2) for wj,p in zip(w,ps))
    kdim=int(np.sum(np.linalg.eigvalsh(G)<1e-10))
    par=list(range(n))
    def f(x):
        while par[x]!=x: par[x]=par[par[x]]; x=par[x]
        return x
    for p in ps:
        for i in range(n): par[f(i)]=f(p[i])
    orbits=len({f(i) for i in range(n)})
    A=np.zeros((n,n))
    for wj,p in zip(w,ps):
        for i in range(n):
            if p[i]!=i: A[i,p[i]]+=wj/2; A[p[i],i]+=wj/2
    L=np.diag(A.sum(1))-A
    bad+= (kdim!=orbits) or not np.allclose(G,L/2*1) and not np.allclose(G,L)
    assert np.allclose(G, L/2) or np.allclose(G,L)
    tr=np.trace(G); assert abs(tr-n*sum(wj*sum(p[i]!=i for i in range(n))/n for wj,p in zip(w,ps)))<1e-9
print(f"(C) 500 weighted families: kernel dim == number of orbits in all cases: {bad==0}; trace law holds; G_tot equals the weighted Schreier Laplacian up to the factor checked")
G1=np.eye(3)-(mat([1,2,0])+mat([1,2,0]).T)/2; A=np.zeros((3,3))
for i,j in ((0,1),(1,2),(2,0)): A[i,j]+=.5; A[j,i]+=.5
print("    factor check on a 3-cycle: G == L(A)?", np.allclose(G1,np.diag(A.sum(1))-A))
viol=0
for _ in range(3000):
    k=rng.randint(1,6); a=rng.uniform(0,2); b=a+rng.uniform(0.01,2); lam=np.array([rng.uniform(a,b) for _ in range(k)]); wt=np.array([rng.uniform(0,1) for _ in range(k)]); c=rng.uniform(0.05,3)
    M0,M1=wt.sum(),(wt*lam).sum(); exact=(wt/(c+lam)).sum()
    lo=M0/(c+M1/M0); hi=(b*M0-M1)/(b-a)/(c+a)+(M1-a*M0)/(b-a)/(c+b)
    viol+= not (lo-1e-12<=exact<=hi+1e-12)
print(f"(D) Jensen lower / chord upper bound on one spectral bin: violations in 3000 random bins = {viol}")
