# SCRIPT: K3-V4-STAR  for every printed witness: the k star-gauge costs, their sum (= 3N), and whether each equals the gauge minimum D
from itertools import combinations
def comp(p,q): return tuple(p[q[i]] for i in range(3))      # (p*q)(i)=p(q(i))
def inv(p):
    r=[0]*3
    for i,x in enumerate(p): r[x]=i
    return tuple(r)
I=(0,1,2); mv=lambda p: sum(1 for i in range(3) if p[i]!=i)
def cochain(k,edges):
    a={}
    for u in range(k):
        for v in range(k):
            if u!=v: a[(u,v)]=I
    for (u,v),p in edges.items(): a[(u,v)]=p; a[(v,u)]=inv(p)
    return a
def N(k,a): return sum(mv(comp(comp(a[(u,v)],a[(v,w)]),a[(w,u)])) for u,v,w in combinations(range(k),3))
def star(k,a,x):
    b={u:(I if u==x else a[(x,u)]) for u in range(k)}
    return sum(mv(comp(comp(b[u],a[(u,v)]),inv(b[v]))) for u,v in combinations(range(k),2))
P=lambda s: tuple(int(c) for c in s.split())
W={4:({(1,2):P("0 2 1"),(1,3):P("1 0 2"),(2,3):P("2 1 0")},6),
   5:({e:P("1 0 2") for e in [(0,1),(1,2),(2,3)]},6),
   6:({**{e:P("1 2 0") for e in [(0,1),(1,3)]},**{e:P("2 0 1") for e in [(0,3),(0,4),(1,5),(4,5)]}},18),
   7:({e:P("1 0 2") for e in [(0,1),(0,3),(0,4),(1,2),(1,5),(2,3)]},12),
   8:({**{e:P("0 2 1") for e in [(0,1),(0,7),(1,2),(2,5),(2,7)]},**{e:P("1 0 2") for e in [(1,3),(1,4),(1,6),(3,7)]},
       **{e:P("2 1 0") for e in [(0,4),(2,3),(2,4)]},(4,7):P("2 0 1")},27)}
cl={0:0,1:0,2:1,3:1,4:2,5:2,6:3,7:3}; seed={(1,2):P("1 0 2"),(1,3):P("2 1 0"),(2,3):P("0 2 1")}
W["8rep"]=({(u,v):seed[(cl[u],cl[v])] for u in range(8) for v in range(u+1,8) if (cl[u],cl[v]) in seed},24)
for key,(ed,D) in W.items():
    k=8 if key=="8rep" else key; a=cochain(k,ed); n=N(k,a); st=[star(k,a,x) for x in range(k)]
    print(f"k={key}: N={n} D={D} star costs={st} sum={sum(st)} (3N={3*n}) all optimal: {all(c==D for c in st)}")
