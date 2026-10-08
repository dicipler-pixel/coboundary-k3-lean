# SCRIPT: K3-V6-SCHREIER-FIG  two permutations of 8 points, their Schreier multigraph, and the spectrum of G_1+G_2: two orbits, two zero eigenvalues
import matplotlib; matplotlib.use("pgf")
import matplotlib.pyplot as plt, numpy as np, math
plt.rcParams.update({"pgf.texsystem":"pdflatex","pgf.rcfonts":False,"font.family":"serif","font.size":10,
  "pgf.preamble":r"\usepackage[T1]{fontenc}\usepackage{lmodern}\usepackage{amsmath,amssymb}"})
BLUE="#1f4e9c"; RED="#b8322a"; GREY="#777777"
p1=[1,2,0,3,5,4,6,7]      # (0 1 2)(4 5)
p2=[0,2,1,4,3,6,7,5]      # (1 2)(3 4)(5 6 7)
n=8
def mat(p): U=np.zeros((n,n)); [U.__setitem__((p[i],i),1) for i in range(n)]; return U
G=sum(np.eye(n)-(mat(p)+mat(p).T)/2 for p in (p1,p2)); lam=np.sort(np.linalg.eigvalsh(G)); lam[np.abs(lam)<1e-12]=0
pos={0:(0,1.0),1:(-0.85,-0.35),2:(0.85,-0.35)}
ring=[3,4,5,6,7]
for k,v in enumerate(ring): a=math.pi/2+2*math.pi*k/5; pos[v]=(3.4+1.15*math.cos(a),0.25+1.15*math.sin(a))
fig,(ax,bx)=plt.subplots(1,2,figsize=(6.8,2.9),gridspec_kw={"width_ratios":[1.55,1]})
def edges(p,col,bend):
    for i in range(n):
        j=p[i]
        if j==i or (p[j]==i and i>j): continue
        (x1,y1),(x2,y2)=pos[i],pos[j]
        ax.annotate("",xy=(x2,y2),xytext=(x1,y1),arrowprops=dict(arrowstyle="-",color=col,lw=1.8,connectionstyle=f"arc3,rad={bend}",shrinkA=7,shrinkB=7))
edges(p1,BLUE,0.18); edges(p2,RED,-0.18)
for v,(x,y) in pos.items():
    ax.scatter([x],[y],s=170,color="white",edgecolor="black",zorder=5); ax.text(x,y,str(v),ha="center",va="center",fontsize=8,zorder=6)
ax.text(0,-1.15,"orbit $\\{0,1,2\\}$",ha="center",color=GREY,fontsize=9); ax.text(3.4,-1.15,"orbit $\\{3,\\dots,7\\}$",ha="center",color=GREY,fontsize=9)
ax.plot([],[],color=BLUE,lw=1.8,label="$\\pi_1=(0\\,1\\,2)(4\\,5)$"); ax.plot([],[],color=RED,lw=1.8,label="$\\pi_2=(1\\,2)(3\\,4)(5\\,6\\,7)$")
ax.legend(loc="upper center",bbox_to_anchor=(0.5,1.16),ncol=2,frameon=False,fontsize=8)
ax.set_aspect("equal"); ax.axis("off"); ax.set_xlim(-1.3,4.8); ax.set_ylim(-1.35,1.55)
bx.stem(range(1,n+1),lam,linefmt=BLUE,markerfmt="o",basefmt=" ")
for i in range(2): bx.plot([i+1],[0],"o",color=RED,ms=7,zorder=5)
bx.set_xlabel("eigenvalue index"); bx.set_ylabel("eigenvalue of $G_{\\pi_1}+G_{\\pi_2}$")
bx.text(1.0,0.8,"2 zeros\n= 2 orbits",color=RED,fontsize=9,ha="left")
bx.set_xticks(range(1,n+1)); [bx.spines[s].set_visible(False) for s in ("top","right")]
fig.tight_layout(); fig.savefig("fig_schreier.pdf"); print("spectrum",np.round(lam,4))
