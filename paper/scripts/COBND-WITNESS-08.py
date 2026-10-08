import itertools, random, time
from fractions import Fraction
import numpy as np
random.seed(20260824); np.random.seed(20260824)
n = 3
P = [tuple(p) for p in itertools.permutations(range(n))]
idx = {p: i for i, p in enumerate(P)}; m = len(P); e_id = idx[tuple(range(n))]
comp = np.array([[idx[tuple(a[b[t]] for t in range(n))] for b in P] for a in P], dtype=np.int32)
inv  = np.array([idx[tuple(sorted(range(n), key=lambda t: a[t]))] for a in P], dtype=np.int32)
Dm   = np.array([[sum(1 for t in range(n) if a[t] != b[t]) for b in P] for a in P], dtype=np.int32)
T = comp[:, inv]
def setup(k):
    V = range(k)
    E = [(u, v) for u in V for v in V if u < v]
    Tri = [(u, v, w) for u in V for v in V for w in V if u < v < w]
    G = np.array(list(itertools.product(range(m), repeat=k - 1)), dtype=np.int32)
    G = np.concatenate([np.full((len(G), 1), e_id, dtype=np.int32), G], axis=1)
    Gedge = {ed: T[G[:, ed[0]], G[:, ed[1]]] for ed in E}
    return E, Tri, Gedge
def val(alpha, u, v):
    return alpha[(u, v)] if u < v else inv[alpha[(v, u)]]
def evaluate(alpha, E, Tri, Gedge):
    num = 0
    for (u, v, w) in Tri:
        h = comp[comp[val(alpha, u, v), val(alpha, v, w)], val(alpha, w, u)]
        num += int(Dm[h, e_id])
    cost = np.zeros(len(next(iter(Gedge.values()))), dtype=np.int32)
    for ed in E:
        cost += Dm[alpha[ed]][Gedge[ed]]
    den = int(cost.min())
    if den == 0: return num, den, None
    return num, den, Fraction(num, den)
def hill_climb(k, E, Tri, Gedge, alpha, steps, target):
    _, _, best = evaluate(alpha, E, Tri, Gedge)
    if best is None: best = Fraction(10**9)
    cur = dict(alpha); curv = best; bestalpha = dict(alpha)
    for s in range(steps):
        trial = dict(cur)
        ed = random.choice(E); trial[ed] = random.randrange(m)
        if random.random() < 0.3:
            ed2 = random.choice(E); trial[ed2] = random.randrange(m)
        _, _, r = evaluate(trial, E, Tri, Gedge)
        if r is None: continue
        if r < target:
            print(f"  !!! KILL: ratio {r} < {target} violates the proven lower bound."); raise SystemExit
        if r <= curv or random.random() < 0.02:
            cur, curv = trial, r
            if r < best: best, bestalpha = r, dict(trial)
            if best == target: break
    return best, bestalpha
def seeds(k, E):
    out = []
    tr = idx[(1, 0, 2)]; c3 = idx[(1, 2, 0)]
    shapes = {"path P4":[(0,1),(1,2),(2,3)],"4-cycle":[(0,1),(1,2),(2,3),(0,3)],
              "4-cycle+2 pend":[(0,1),(1,2),(2,3),(0,3),(0,4),(1,5)],
              "star":[(0,j) for j in range(1,k)],"triangle":[(0,1),(1,2),(0,2)]}
    for name, edges in shapes.items():
        for g, gname in ((tr,"transp"),(c3,"3-cycle")):
            a = {ed: e_id for ed in E}
            for ed in edges:
                if ed in a: a[ed] = g
            out.append((f"{name}/{gname}", a))
    for r in range(6):
        out.append((f"random {r}", {ed: random.randrange(m) for ed in E}))
    return out
print("="*90); print("COBND-WITNESS-08  Sym(3) witnesses for h_1(K_k) = k/3, exact arithmetic"); print("="*90)
k = 4; E, Tri, Gedge = setup(k); t0 = time.time(); best = None
for vals in itertools.product(range(m), repeat=len(E)):
    a = dict(zip(E, vals)); _, _, r = evaluate(a, E, Tri, Gedge)
    if r is not None and (best is None or r < best): best = r
print(f"k=4 exhaustive: h_1(K_4, Sym3) = {best}   expected 4/3   {'PASS' if best == Fraction(4,3) else 'FAIL - STOP'}   ({time.time()-t0:.1f}s)", flush=True)
for k, steps in ((5,300),(6,400),(7,400),(8,1500)):
    E, Tri, Gedge = setup(k); target = Fraction(k,3); t0 = time.time()
    print(f"\nk={k}: target {target}, gauges enumerated per cochain = {6**(k-1)}", flush=True)
    overall, winner, wname = None, None, None
    for name, a in seeds(k, E):
        b, ba = hill_climb(k, E, Tri, Gedge, a, steps, target)
        print(f"  seed {name:22s} best ratio {str(b):>8s}  (= {float(b):.6f})", flush=True)
        if overall is None or b < overall: overall, winner, wname = b, ba, name
        if overall == target: break
    hit = overall == target
    print(f"  k={k} RESULT: best ratio {overall} vs k/3 = {target}  ->  {'ATTAINED (equality proven for this k)' if hit else 'not found (search failure, not a refutation)'}   ({time.time()-t0:.0f}s)", flush=True)
    if hit:
        num, den, _ = evaluate(winner, E, Tri, Gedge)
        nz = [(ed, P[winner[ed]]) for ed in E if winner[ed] != e_id]
        print(f"  witness from seed '{wname}': triangle defect {num}, min gauge cost {den}, {len(nz)} non-identity edges:")
        for ed, p in nz: print(f"     edge {ed} -> {p}")
print("\nEND: COBND-WITNESS-08")
