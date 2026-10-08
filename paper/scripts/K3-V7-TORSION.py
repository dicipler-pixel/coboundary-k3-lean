# SCRIPT: K3-V7-TORSION  independent replay of the padded-family torsion identity: Wada/Fox matrix of a two-bridge knot group in a permutation representation padded by fixed points; one generator perturbed by a transposition inside the padding; checks Delta T_eta = (1/2n) log R_eta with R_eta independent of n, so |Delta T_eta| = (|log R_eta|/4) d_H exactly
import numpy as np, sympy as sp
def word(p,q):          # two-bridge word in Schubert form (q odd): w = a^e1 b^e2 a^e3 ..., length p-1, e_i = (-1)^floor(i q / p); relation w a = b w
    return [("a" if i%2 else "b", (-1)**((i*q)//p)) for i in range(1,p)]
def relator(p,q):
    w=word(p,q); winv=[(g,-e) for g,e in reversed(w)]
    return w+[("a",1)]+winv+[("b",-1)]
def fox_a(rel,Phi,n):   # Phi(g, e): image of g^e ; returns image of d rel / d a
    acc=np.zeros((n,n),dtype=complex); pref=np.eye(n,dtype=complex)
    for g,e in rel:
        if g=="a": acc+= pref if e==1 else -pref@Phi("a",-1)
        pref=pref@Phi(g,e)
    return acc
def perm_mat(p):
    n=len(p); M=np.zeros((n,n)); [M.__setitem__((p[i],i),1.0) for i in range(n)]; return M
def build(rho_a,rho_b,t,tau=None):
    A=perm_mat(rho_a); B=perm_mat(rho_b)
    if tau is not None: A=A@perm_mat(tau)
    def Phi(g,e):
        M=A if g=="a" else B
        return (t*M) if e==1 else np.linalg.inv(t*M)
    return Phi, len(rho_a)
# control: trivial rep returns the Alexander polynomial up to a unit
T=sp.symbols("t")
for name,(p,q),Delta in (("3_1",(3,1),T**2-T+1),("4_1",(5,3),T**2-3*T+1),("5_2",(7,3),2*T**2-3*T+2)):
    vals=[]
    for tv in (2.0,3.0,5.0):
        Phi,n=build([0],[0],tv); f=fox_a(relator(p,q),Phi,1)[0,0]
        vals.append(f/complex(Delta.subs(T,tv)))
    ratio=[abs(v) for v in vals]; logs=[np.log(abs(v))/np.log(abs(tv)) for v,tv in zip(vals,(2.0,3.0,5.0))]
    print(f"control {name}: Fox(trivial)/Delta = unit * t^k ; k estimates {np.round(logs,6)}")
reps={"3_1":((3,1),[1,0,2],[0,2,1]),     # a -> (0 1), b -> (1 2): surjective onto Sym(3)
      "4_1":((5,3),[1,0,2],[1,0,2]),     # abelian rep through one transposition
      "5_2":((7,3),[1,0,2],[1,0,2])}     # det 7: no surjective Sym(3) rep, so the abelian one
t0=1.07; out={}
for name,((p,q),ra,rb) in reps.items():
    rel=relator(p,q)
    # check the representation is a homomorphism (relator maps to identity)
    Phi,n0=build(ra,rb,1.0); M=np.eye(n0)
    for g,e in rel: M=M@Phi(g,e)
    hom=np.allclose(M,np.eye(n0))
    for eta in (1e-2,1e-3,1e-4,1e-5):
        Cs=[]
        for n in (6,12,24,48,96):
            pa=ra+list(range(3,n)); pb=rb+list(range(3,n)); tau=list(range(n)); tau[n-1],tau[n-2]=tau[n-2],tau[n-1]
            T0=lambda P: np.linalg.slogdet(P.conj().T@P+eta**2*np.eye(n))[1]/(2*n)
            P0=fox_a(rel,*build(pa,pb,t0)); P1=fox_a(rel,*build(pa,pb,t0,tau))
            dT=T0(P1)-T0(P0); dH=2/n; Cs.append(abs(dT)/dH)
            # the same change from the 2x2 padding block alone
            Q0=fox_a(rel,*build([0,1],[0,1],t0)); Q1=fox_a(rel,*build([0,1],[0,1],t0,[1,0]))
            R=np.exp(np.linalg.slogdet(Q1.conj().T@Q1+eta**2*np.eye(2))[1]-np.linalg.slogdet(Q0.conj().T@Q0+eta**2*np.eye(2))[1])
            assert abs(abs(dT)/dH-abs(np.log(R))/4)<1e-10
        out[(name,eta)]=Cs
    print(f"{name}: homomorphism {hom}; C = |Delta T|/d_H over n=6..96 at eta=1e-2: {np.round(out[(name,1e-2)],9)}; spread over eta 1e-2..1e-5: {max(max(v) for k,v in out.items() if k[0]==name)-min(min(v) for k,v in out.items() if k[0]==name):.2e}")
print("identity |Delta T| = (|log R_eta|/4) d_H held in every case (assert)")
