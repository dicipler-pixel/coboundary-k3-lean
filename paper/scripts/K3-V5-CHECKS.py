# SCRIPT: K3-V5-CHECKS  (1) all-orders zeta expansion of the entropy deficit; (2) probe response as a spectral-measure sum and its Stieltjes uniqueness on the isospectral pair; (3) Hamming distance = (2/n) sum sin^2 of principal angles between graph subspaces
from mpmath import mp, mpf, sin, log, pi, zeta, nsum, inf
import numpy as np, itertools, random
mp.dps=40
h=lambda y: mpf(0) if y<=0 or y>=1 else -(y*log(y)+(1-y)*log(1-y))
c0=2*log(2)-1; worst=0
for l in (2,3,4,5,7,8,9,16,17,63,64,255,256):
    D=c0-sum(h(sin(pi*mpf(j)/l)**2) for j in range(l))/l
    ser=(nsum(lambda r: zeta(2*r+3)/(4**r*mpf(l)**(2*r)),[0,inf])/4) if l%2 else 2*nsum(lambda r: zeta(2*r+3)/mpf(l)**(2*r),[0,inf])
    worst=max(worst,abs(l**3*D-ser)/ser)
print("(1) max rel. error, l^3 D_l vs zeta expansion, l in {2..256}:", mp.nstr(worst,4))
# (2) probe
def gram(p):
    n=len(p); U=np.zeros((n,n)); [U.__setitem__((p[i],i),1) for i in range(n)]; return np.eye(n)-(U+U.T)/2
Ga,Gb=gram([1,0,3,2]),gram([2,3,0,1]); b=np.array([1,1,0,0])/np.sqrt(2)
print("    spectra equal:",np.allclose(np.linalg.eigvalsh(Ga),np.linalg.eigvalsh(Gb)))
for G,name in ((Ga,"pi_a"),(Gb,"pi_b")):
    lam,V=np.linalg.eigh(G); w=(V.T@b)**2
    for c in (0.5,1.0,3.0):
        direct=b@np.linalg.solve(c*np.eye(4)+G,b); meas=sum(w/(c+lam))
        assert abs(direct-meas)<1e-14
    mu={round(float(l),9):0.0 for l in lam}
    for l,x in zip(lam,w): mu[round(float(l),9)]+=x
    print(f"(2) {name}: m_b(1)={b@np.linalg.solve(np.eye(4)+G,b):.12f}  spectral measure seen by b: {{ {', '.join(f'{k:g}: {v:.3f}' for k,v in mu.items() if v>1e-12)} }}")
# (3) principal angles
rng=random.Random(5); worst3=0
for trial in range(300):
    n=rng.randint(2,12); p=list(range(n)); q=list(range(n)); rng.shuffle(p); rng.shuffle(q)
    U=np.eye(n)[:,p]; V=np.eye(n)[:,q]
    dH=sum(1 for i in range(n) if p[i]!=q[i])/n
    QU=np.vstack([np.eye(n),U])/np.sqrt(2); QV=np.vstack([np.eye(n),V])/np.sqrt(2)
    s=np.linalg.svd(QU.T@QV,compute_uv=False); sin2=1-np.clip(s,0,1)**2
    ph=np.angle(np.linalg.eigvals(U.T@V)); sin2b=np.sin(ph/2)**2
    worst3=max(worst3,abs(dH-2*sin2.sum()/n),abs(np.sort(sin2).sum()-sin2b.sum()))
print("(3) 300 random pairs, max |d_H - (2/n) sum sin^2 theta| and |sum sin^2 theta - sum sin^2(phi/2)|:",f"{worst3:.2e}")
