# SCRIPT: K3-FIGS-V2BASE  the k=8 witness and k=4 subgroup figures (v2 layout), rendered with LaTeX text
import matplotlib; matplotlib.use("pgf")
import matplotlib.pyplot as plt
plt.rcParams.update({"pgf.texsystem":"pdflatex","pgf.rcfonts":False,"font.family":"serif","pgf.preamble":r"\usepackage[T1]{fontenc}\usepackage{lmodern}\usepackage{amsmath,amssymb}"})
import matplotlib.pyplot as plt, numpy as np, math
plt.rcParams.update({"font.family":"serif","font.size":11,"font.serif":["Latin Modern Roman"]})

BLUE="#1f4e9c"; RED="#b8322a"; GOLD="#c58a1a"; GREY="#777777"
# ---- Fig 1: the ladder
fig,ax=plt.subplots(figsize=(6.6,3.8))
ks=np.linspace(3.6,8.5,50); ax.plot(ks,ks/3,color=BLUE,lw=2,label=r"lower bound $k/3$ (Chapman--Lubotzky)")
ax.fill_between(ks,0.9,ks/3,color=BLUE,alpha=0.07)
sym=[(4,4/3),(5,5/3),(6,2),(7,7/3),(8,8/3)]
ax.scatter([k for k,_ in sym],[v for _,v in sym],s=95,color=BLUE,zorder=5,label=r"$h_1(K_k,\mathrm{Sym})$: attained, $k=4\ldots8$")
f2=[(4,2),(5,5/3),(6,2),(7,7/3)]
ax.scatter([k for k,_ in f2],[v for _,v in f2],s=60,marker="s",facecolor="none",edgecolor=RED,lw=1.8,zorder=6,label=r"$h_1(K_k,\mathbb{F}_2)$ (Meshulam--Wallach, Kozlov)")
ax.annotate(r"$\mathbb{F}_2$: 2",xy=(4,2),xytext=(4.25,2.12),color=RED)
ax.annotate(r"$\mathbb{F}_2 > 8/3$ (Kozlov)",xy=(8,2.667),xytext=(6.55,2.95),color=RED,arrowprops=dict(arrowstyle="->",color=RED))
for k in (4,8): ax.axvline(k,color=GREY,ls=":",lw=1)
ax.text(4,1.02,"power of 2",ha="center",color=GREY,fontsize=9); ax.text(8,1.02,"power of 2",ha="center",color=GREY,fontsize=9)
ax.set_xlabel(r"vertices $k$ of the complete 2-complex"); ax.set_ylabel(r"$h_1^{\rm count}$")
ax.set_xticks([4,5,6,7,8]); ax.set_ylim(0.95,3.15); ax.legend(loc="upper left",fontsize=8.5,frameon=False)
for s in ("top","right"): ax.spines[s].set_visible(False)
plt.close(fig)
# ---- Fig 2: k=8 witness residual
res={(0,1):"b",(0,4):"c",(0,7):"b",(1,2):"b",(1,3):"a",(1,4):"a",(1,6):"a",(2,3):"c",(2,4):"c",(2,5):"b",(2,7):"b",(3,7):"a",(4,7):"3"}
col={"a":BLUE,"b":RED,"c":GOLD,"3":"black"}; lab={"a":"(0 1)","b":"(1 2)","c":"(0 2)","3":"3-cycle"}
fig,ax=plt.subplots(figsize=(6.6,4.2)); k=8
pos={i:(math.cos(2*math.pi*i/k+math.pi/2),math.sin(2*math.pi*i/k+math.pi/2)) for i in range(k)}
for u in range(k):
    for v in range(u+1,k):
        if (u,v) not in res: ax.plot([pos[u][0],pos[v][0]],[pos[u][1],pos[v][1]],color="#dddddd",lw=0.8,zorder=1)
for (u,v),c in res.items():
    ax.plot([pos[u][0],pos[v][0]],[pos[u][1],pos[v][1]],color=col[c],lw=3.2 if c!="3" else 4.5,zorder=3,ls="-" if c!="3" else (0,(3,1.5)))
for i,(x,y) in pos.items():
    ax.scatter([x],[y],s=260,color="white",edgecolor="black",zorder=5); ax.text(x,y,str(i),ha="center",va="center",zorder=6)
for c in ("a","b","c","3"): ax.plot([],[],color=col[c],lw=3,ls="-" if c!="3" else (0,(3,1.5)),label=lab[c])
ax.legend(loc="upper left",frameon=False,fontsize=9,title="residual edge value",title_fontsize=9,bbox_to_anchor=(-0.02,1.02))

ax.text(0,-1.3,r"defect 72 / gauge cost 27 $= 8/3$",ha="center",fontsize=11,color=BLUE)
ax.set_aspect("equal"); ax.axis("off"); ax.set_xlim(-1.7,1.4); ax.set_ylim(-1.42,1.4)
fig.tight_layout(); fig.savefig("fig_witness8.pdf")
# ---- Fig 3: k=4 mechanism
fig,axs=plt.subplots(1,3,figsize=(6.6,2.6))
tri={0:(0,0.15),1:(-0.9,-0.55),2:(0.9,-0.55),3:(0,1.05)}
def draw(ax,edges,title,val):
    for u in range(4):
        for v in range(u+1,4):
            ax.plot([tri[u][0],tri[v][0]],[tri[u][1],tri[v][1]],color="#dddddd",lw=1,zorder=1)
    for (u,v),c in edges.items():
        ax.plot([tri[u][0],tri[v][0]],[tri[u][1],tri[v][1]],color=c,lw=3.2,zorder=3)
    for i,(x,y) in tri.items(): ax.scatter([x],[y],s=120,color="white",edgecolor="black",zorder=5)
    ax.set_title(title,fontsize=8.5); ax.text(0,-0.95,val,ha="center",fontsize=11,color=BLUE if "4/3" in val else RED)
    ax.set_aspect("equal"); ax.axis("off"); ax.set_xlim(-1.2,1.2); ax.set_ylim(-1.1,1.25)
draw(axs[0],{(2,3):RED},r"Sym(2) $=\mathbb{F}_2$:"+"\none transposition","ratio 2")
draw(axs[1],{(1,3):"black",(2,3):"black"},r"$\mathbb{Z}/3$:"+"\ntwo 3-cycles","ratio 3/2")
draw(axs[2],{(1,2):RED,(1,3):BLUE,(2,3):GOLD},"Sym(3): three distinct\ntranspositions","ratio 4/3 = k/3")
fig.tight_layout(); fig.savefig("fig_k4.pdf")
print("ok")
