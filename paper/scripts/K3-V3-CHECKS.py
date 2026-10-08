# SCRIPT: K3-V3-CHECKS  extra checks for v3: entropy deficit law by parity, flat profiles, Chebyshev-Mobius cycle recovery
import numpy as np, itertools, math
from fractions import Fraction
h=lambda x: 0.0 if x<=0 or x>=1 else -(x*math.log(x)+(1-x)*math.log(1-x))
L=2*math.log(2)-1
print('ell  S/ell  deficit  deficit*ell^3')
for l in [3,4,5,6,7,8,9,10,12,15,16,31,32,63,64,127,128]:
    lam=[2*math.sin(math.pi*j/l)**2 for j in range(l)]
    s=sum(h(x/2) for x in lam)/l
    print(l, f'{s:.10f} {L-s:+.3e} {(L-s)*l**3:.4f}')
# flat threshold profiles: C(eps)=#{lam/lmax>=eps}, eps in (0,1]
def prof(cyc):
    lam=[]
    for l in cyc: lam+= [2*math.sin(math.pi*j/l)**2 for j in range(l)]
    m=max(lam); return [sum(1 for x in lam if x/m>=e-1e-12) for e in np.linspace(0.01,1,100)]
def parts(n,mx=None):
    if n==0: yield []; return
    mx=mx or n
    for p in range(min(n,mx),1,-1):
        for r in parts(n-p,p): yield [p]+r
for n in (12,18,24):
    flat=[c for c in parts(n) if len(set(prof(c)))==1]
    print('moved',n,'flat profiles:',[(c[:3],'...',prof(c)[0]/n) for c in flat])
    ps={}
    dup=0
    for c in parts(n):
        key=tuple(prof(c)); dup+= key in ps; ps[key]=c
    print('  cycle types',sum(1 for _ in parts(n)),'distinct profiles',len(ps),'collisions',dup)
# Chebyshev/Mobius: F_r = Tr T_r(I-G) = Tr U^r = sum_{l|r} l a_l ; recover a_l
def mob(n):
    r=1;p=2;m=n
    while p*p<=m:
        if m%p==0:
            m//=p
            if m%p==0: return 0
            r=-r
        p+=1
    return -r if m>1 else r
rng=np.random.default_rng(1); ok=0; T=0
for trial in range(200):
    n=int(rng.integers(2,30)); perm=rng.permutation(n)
    U=np.zeros((n,n)); U[perm,np.arange(n)]=1
    G=np.eye(n)-(U+U.T)/2; A=np.eye(n)-G
    F={}
    Tm,Tc=np.eye(n),A
    for r in range(1,n+1):
        F[r]=round(np.trace(Tc)); Tm,Tc=Tc,2*A@Tc-Tm
    a={l:sum(mob(l//d)*F[d] for d in range(1,l+1) if l%d==0)//l for l in range(1,n+1)}
    seen=[0]*n; true={}
    for i in range(n):
        if not seen[i]:
            l=0;j=i
            while not seen[j]: seen[j]=1;j=perm[j];l+=1
            true[l]=true.get(l,0)+1
    T+=1; ok+= all(a[l]==true.get(l,0) for l in range(1,n+1))
print('Chebyshev-Mobius cycle recovery:',ok,'/',T)
# high-precision deficit law: ell^3 (2ln2-1 - S/ell) -> 2 zeta(3) (even ell), zeta(3)/4 (odd ell)
from mpmath import mp, sin as msin, log as mlog, pi as mpi, zeta
mp.dps=40
hh=lambda x: 0 if x<=0 or x>=1 else -(x*mlog(x)+(1-x)*mlog(1-x))
LL=2*mlog(2)-1
for l in (256,257,1024,1025,4096,4097):
    print(l, mp.nstr((LL-sum(hh(msin(mpi*j/l)**2) for j in range(l))/l)*l**3,12))
print('2zeta(3) =',mp.nstr(2*zeta(3),12),'  zeta(3)/4 =',mp.nstr(zeta(3)/4,12))
