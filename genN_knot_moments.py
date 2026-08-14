import sympy as sp
pi = sp.pi
D, xi = sp.symbols('D xi')
si, sk, sl, rl, v = sp.symbols('si sk sl rl v')
def R(a,b): return (a+b)/2
def lam(a,b): return (b-a)/2
def Q0(a,b): return (2*pi/D)*( R(a,b) + pi*xi*a*b/(4*D) )
def Qpp(b):  return (2*pi/D)*( 1 + pi*xi*b/(2*D) )
def q0poly(a,b,tt): return (-Q0(a,b)*R(a,b) + Qpp(b)*R(a,b)**2/2) + (Q0(a,b)-Qpp(b)*R(a,b))*tt + (Qpp(b)/2)*tt**2
t=sp.symbols('t')
P1=q0poly(si,sl,t); s2=v+R(sk,sl)
P2=(-Q0(sk,sl)*s2+Qpp(sl)*s2**2/2)+(Q0(sk,sl)-Qpp(sl)*s2)*t+(Qpp(sl)/2)*t**2
Ilup=sp.integrate(sp.expand(P1*P2),(t,v+lam(sk,sl),R(si,sl)))
Illow=sp.integrate(sp.expand(P1*P2),(t,lam(si,sl),R(si,sl)))
lamik=(sk-si)/2
# per-species DCF difference h(sl) = (cCorrUp - cCorrLow) / rho_l  at v=lam
cCorrUp = sp.diff(Ilup,v)/(2*pi*v)   # /rho_l (drop rl factor)
cCorrLow= sp.diff(Illow,v)/(2*pi*v)
h = sp.expand((cCorrUp - cCorrLow).subs(v,lamik))
h = sp.simplify(h)
hpoly = sp.Poly(sp.expand(h), sl)
print("h(sl) degree in sl:", hpoly.degree())
for n in range(hpoly.degree()+1):
    c = hpoly.coeff_monomial(sl**n)
    if c != 0:
        print(f"  sl^{n}: nonzero")
# Leading difference at lam
cLeadUp = (-sp.diff(q0poly(si,sk,v),v)/(2*pi*v)).subs(v,lamik)
q0md_ki = Q0(sk,si) + Qpp(si)*(-v - R(sk,si))
cLeadLow= (q0md_ki/(2*pi*v)).subs(v,lamik)
Dlead = sp.simplify(cLeadUp - cLeadLow)
print("Dlead computed")
# The identity: Dlead + sum_l rho_l h(sl) = 0.  sum_l rho_l sl^n = M_n.
# h has xi=M2 and D=1-(pi/6)M3 as constants. Substitute and check as poly in M0..M5.
M0,M1,M2,M3,M4,M5 = sp.symbols('M0 M1 M2 M3 M4 M5')
Msym=[M0,M1,M2,M3,M4,M5]
sumh = sum(hpoly.coeff_monomial(sl**n)*Msym[n] for n in range(hpoly.degree()+1))
total = Dlead + sumh
# substitute xi -> M2 ; D stays (D=vacMix, encodes M3 via D=1-(pi/6)M3, but keep D symbolic and add relation)
total = total.subs(xi, M2)
# Now total should be 0 using D = 1 - (pi/6) M3.  Substitute M3 = (6/pi)(1-D):
total = sp.simplify(total.subs(M3, (6/pi)*(1-D)))
total = sp.expand(sp.together(total))
print("total (should be 0 if closes via M2=xi2, M3=vac, and M0/M1/M4/M5 coeffs vanish):")
tp = sp.Poly(sp.numer(sp.together(total)), M0,M1,M4,M5)
print("  as poly in M0,M1,M4,M5 -> is it 0?", sp.simplify(total)==0)
for mon in [M0,M1,M4,M5]:
    print(f"  coeff {mon}:", sp.simplify(total.coeff(mon)))

# extract coeffH2 = sl^2 coefficient of h ; also verify per-species and leading identities
h2 = sp.expand(hpoly.coeff_monomial(sl**2))
print("\n=== coeffH2 (the σₗ² slope) ===")
# express over 768 D^4?  h2 is the coeff such that (cCorrUp-cCorrLow)(λ) = h2 * rho_l * sl^2 (with rho_l factored)
# check: cCorrPieceN(l)(λ) - cLowerCorrPieceN(l)(λ) should = h2 * (rho_l sl^2), with cCorr including /768D^4
# our cCorrUp/cCorrLow above dropped rho_l AND the /768D^4? No — cCorrUp=diff(Ilup)/(2πv) is the FULL DCF piece /rho_l
# Actually cCorrPieceN(l)(v) = rho_l Ilup'(v)/(2πv). So (cCorrUp-cCorrLow) here = [Ilup'-Illow']/(2πv) = h(σl) (per rho_l).
# So cCorrPieceN(l)(λ)-cLowerCorrPieceN(l)(λ) = rho_l * h(σl) = rho_l h2 σl^2. coeffH2=h2.
TOK={'D':'‹D›','xi':'‹xi›','pi':'‹pi›','si':'‹si›','sk':'‹sk›','sl':'‹sl›','rl':'‹rl›'}
SUB={'‹D›':'vacMix rho sigma','‹xi›':'xi2 rho sigma','‹pi›':'Real.pi',
     '‹si›':'sigma i','‹sk›':'sigma k','‹sl›':'sigma l','‹rl›':'rho l'}
import re
def lean(ex):
    s=str(ex).replace('**','^').replace('*',' * ')
    for k,tk in TOK.items(): s=re.sub(r'(?<![A-Za-z])'+k+r'(?![A-Za-z])',tk,s)
    for tk,val in SUB.items(): s=s.replace(tk,val)
    return s
def wrap(body, indent='    ', first='  ', width=96):
    toks=re.split(r'(?= [+\-] )', body); lines=[]; cur=first
    for i,tk in enumerate(toks):
        if len(cur)+len(tk)>width and cur.strip(): lines.append(cur.rstrip()); cur=indent+tk.lstrip()
        else: cur+=tk
    lines.append(cur.rstrip()); return '\n'.join(lines)
open('genN_knotslope.txt','w').write(wrap(lean(h2)))
print("h2 =", h2)
print("wrote genN_knotslope.txt")
# sanity: verify leading diff = -h2*xi2  (with xi=M2 substituted -> here xi is xi2 symbol)
Dlead_check = sp.simplify(Dlead + h2*xi)   # should be 0
print("Dlead + h2*xi2 == 0 ?", Dlead_check == 0)
