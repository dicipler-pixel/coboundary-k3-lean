# SCRIPT: K3-V4-FIGS  figures for v4: the ladder to k=16, the replication blow-up, the entropy deficit law
import matplotlib; matplotlib.use("pgf")
import matplotlib.pyplot as plt
plt.rcParams.update({"pgf.texsystem":"pdflatex","pgf.rcfonts":False,"font.family":"serif","pgf.preamble":r"\usepackage[T1]{fontenc}\usepackage{lmodern}\usepackage{amsmath,amssymb}"})
import matplotlib.pyplot as plt, numpy as np, math
from mpmath import mp, sin as msin, log as mlog, pi as mpi, zeta
plt.rcParams.update({"font.family":"serif","font.size":11,"font.serif":["Latin Modern Roman"]})

BLUE="#1f4e9c"; RED="#b8322a"; GOLD="#c58a1a"; GREY="#777777"
# ---- ladder to k=16
fig,ax=plt.subplots(figsize=(6.6,3.8))
ks=np.linspace(3.6,16.5,80); ax.plot(ks,ks/3,color=BLUE,lw=2,label=r"lower bound $k/3$ (Chapman--Lubotzky)")
comp=[(k,k/3) for k in range(4,9)]; thm=[(k,k/3) for k in range(9,17)]
ax.scatter(*zip(*comp),s=90,color=BLUE,zorder=5,label=r"$h_1(K_k,\mathrm{Sym})$, witness computed ($k\leq 8$)")
ax.scatter(*zip(*thm),s=70,facecolor="white",edgecolor=BLUE,lw=1.8,zorder=5,label=r"$h_1(K_k,\mathrm{Sym})=k/3$, proved for all $k$ ($k\geq 9$ shown)")
f2=[(k,k/3) for k in range(5,17) if k not in (8,16)]+[(4,2),(8,20/7)]
ax.scatter(*zip(*f2),s=40,marker="s",facecolor="none",edgecolor=RED,lw=1.4,zorder=6,label=r"$h_1(K_k,\mathbb{F}_2)$ (Meshulam--Wallach, Kozlov)")
ax.plot([16.32,16.32],[16/3,16/3+8/93],color=RED,lw=2.2,solid_capstyle="butt",zorder=6); ax.plot([16.22,16.42],[16/3,16/3],color=RED,lw=1.2); ax.plot([16.22,16.42],[16/3+8/93,16/3+8/93],color=RED,lw=1.2)
ax.annotate(r"$\mathbb{F}_2=2$",xy=(4,2),xytext=(4.3,2.35),color=RED)
ax.annotate(r"$\mathbb{F}_2=\frac{20}{7}$",xy=(8,20/7),xytext=(8.4,2.05),color=RED,arrowprops=dict(arrowstyle="->",color=RED))
ax.annotate(r"$\mathbb{F}_2\in[\frac{16}{3},\frac{16}{3}+\frac{8}{93}]$",xy=(16.2,16/3+8/93),xytext=(10.2,5.55),color=RED,fontsize=9,arrowprops=dict(arrowstyle="->",color=RED))
for k in (4,8,16): ax.axvline(k,color=GREY,ls=":",lw=1)
ax.set_xlabel(r"vertices $k$ of the complete 2-complex"); ax.set_ylabel(r"$h_1^{\rm count}$")
ax.set_xticks(range(4,17)); ax.set_ylim(1,6.0); ax.legend(loc="upper left",fontsize=8,frameon=False)
for s in ("top","right"): ax.spines[s].set_visible(False)
fig.tight_layout(); fig.savefig("fig_ladder_v4.pdf")
# ---- replication blow-up: K4 seed -> K8
fig,axs=plt.subplots(1,2,figsize=(6.8,3.2))
col={(1,2):RED,(1,3):BLUE,(2,3):GOLD}
P4={0:(0,1.0),1:(-0.95,-0.55),2:(0.95,-0.55),3:(0,-0.05)}
ax=axs[0]
for u in range(4):
    for v in range(u+1,4):
        c=col.get((u,v),"#cccccc"); ax.plot([P4[u][0],P4[v][0]],[P4[u][1],P4[v][1]],color=c,lw=3 if (u,v) in col else 1,zorder=2)
for i,(x,y) in P4.items(): ax.scatter([x],[y],s=240,color="white",edgecolor="black",zorder=5); ax.text(x,y,str(i),ha="center",va="center",zorder=6)
ax.set_title("seed $K_4$:\n$N=8$, $D=6$",fontsize=10); ax.set_aspect("equal"); ax.axis("off"); ax.set_xlim(-1.4,1.4); ax.set_ylim(-1.1,1.35)
ax=axs[1]; off=0.22
P8={}
for i,(x,y) in P4.items():
    for a in (0,1):
        ang=math.atan2(y-0.2,x)+math.pi/2 if i!=3 else math.pi/4
        P8[(i,a)]=(x+(a-0.5)*2*off*math.cos(ang),y+(a-0.5)*2*off*math.sin(ang))
for (i,a) in P8:
    for (j,b) in P8:
        if (i,a)<(j,b):
            if i==j: c,lw="#888888",1.2
            else:
                key=(min(i,j),max(i,j)); c=col.get(key,"#dddddd"); lw=2.2 if key in col else 0.6
            ax.plot([P8[(i,a)][0],P8[(j,b)][0]],[P8[(i,a)][1],P8[(j,b)][1]],color=c,lw=lw,zorder=2)
for (i,a),(x,y) in P8.items(): ax.scatter([x],[y],s=110,color="white",edgecolor="black",zorder=5)
ax.set_title("replicated $K_8$ ($q=2$):\n$N=8q^3=64$, $D=6q^2=24$",fontsize=10); ax.set_aspect("equal"); ax.axis("off"); ax.set_xlim(-1.4,1.4); ax.set_ylim(-1.1,1.35)
fig.tight_layout(); fig.savefig("fig_replication.pdf")
# ---- entropy deficit law
mp.dps=30
h=lambda x: 0 if x<=0 or x>=1 else -(x*mlog(x)+(1-x)*mlog(1-x))
L=2*mlog(2)-1
ev=[4,6,8,12,16,24,32,48,64,96,128,256]; od=[5,7,9,13,17,25,33,49,65,97,129,257]
def dl(l): return float((L-sum(h(msin(mpi*j/l)**2) for j in range(l))/l)*l**3)
fig,ax=plt.subplots(figsize=(6.6,3.4))
ax.semilogx(ev,[dl(l) for l in ev],"o-",color=BLUE,label=r"even $\ell$")
ax.semilogx(od,[dl(l) for l in od],"s-",color=GOLD,label=r"odd $\ell$")
ax.axhline(float(2*zeta(3)),color=BLUE,ls="--",lw=1); ax.axhline(float(zeta(3)/4),color=GOLD,ls="--",lw=1)
ax.text(300,float(2*zeta(3))+0.05,r"$2\zeta(3)$",color=BLUE,ha="right"); ax.text(300,float(zeta(3)/4)+0.05,r"$\zeta(3)/4$",color=GOLD,ha="right")
ax.set_xlabel(r"cycle length $\ell$"); ax.set_ylabel(r"$\ell^3\,(2\ln2-1-S_\ell/\ell)$")
ax.legend(frameon=False,fontsize=9,loc="center right")
for s in ("top","right"): ax.spines[s].set_visible(False)
fig.tight_layout(); fig.savefig("fig_entropy_deficit.pdf")
print("ok")
