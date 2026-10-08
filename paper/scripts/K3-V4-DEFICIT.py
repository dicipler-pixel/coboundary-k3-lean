# SCRIPT: K3-V4-DEFICIT  checks the Fourier series of h(sin^2 pi x) and the exact deficit sum D_l = sum_{l | 2m} 1/(m(4m^2-1))
from mpmath import mp, mpf, sin, cos, log, pi, zeta, nsum, inf
mp.dps=40
h=lambda y: mpf(0) if y<=0 or y>=1 else -(y*log(y)+(1-y)*log(1-y))
f=lambda x: h(sin(pi*x)**2)
c0=2*log(2)-1
print("sum 1/(m(4m^2-1)) - (2ln2-1) =", nsum(lambda m: 1/(m*(4*m**2-1)),[1,inf])-c0)
for x in (mpf('0.1'),mpf('0.237'),mpf('0.5')):
    ser=c0-nsum(lambda m: cos(4*pi*m*x)/(m*(4*m**2-1)),[1,inf])
    print(f"x={x}: f-series = {f(x)-ser}")
worst=0
for l in list(range(2,40))+[63,64,126,127,1000,1001,4096,4097]:
    S=sum(f(mpf(j)/l) for j in range(l)); lhs=c0-S/l
    step=l//2 if l%2==0 else l          # l | 2m  <=>  m multiple of step
    rhs=nsum(lambda t: 1/((step*t)*(4*(step*t)**2-1)),[1,inf])
    worst=max(worst,abs(lhs-rhs)/rhs)
print("max relative error, direct sum vs exact series, l=2..39 and large l:", mp.nstr(worst,5))
for l in (63,):
    S1=sum(f(mpf(j)/l) for j in range(l)); S2=sum(f(mpf(j)/(2*l)) for j in range(2*l))
    print("D_63 - D_126 =", mp.nstr((c0-S1/l)-(c0-S2/(2*l)),5))
print("limits: 2zeta(3) =",mp.nstr(2*zeta(3),12)," zeta(3)/4 =",mp.nstr(zeta(3)/4,12))
