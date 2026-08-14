import sympy as sp

# atoms: D=vacMix, xi=xi2 (global, opaque); diameters/densities of species i,k and generic l
D, xi, pi = sp.symbols('D xi pi', positive=True)
si, sk, sl = sp.symbols('si sk sl', positive=True)
ri, rk, rl = sp.symbols('ri rk rl', positive=True)
v, t = sp.symbols('v t', real=True)

def R(a,b): return (a+b)/2
def lam(a,b): return (b-a)/2           # X.lam a b = (sigma_b - sigma_a)/2
def Q0(a,b): return (2*pi/D)*( R(a,b) + pi*xi*a*b/(4*D) )
def Qpp(b):  return (2*pi/D)*( 1 + pi*xi*b/(2*D) )     # independent of first index

# forward Baxter quadratic q0MixEntry(a,b)(t), uses Qpp(second index)
def q0poly(a,b,t):
    return (-Q0(a,b)*R(a,b) + Qpp(b)*R(a,b)**2/2) + (Q0(a,b)-Qpp(b)*R(a,b))*t + (Qpp(b)/2)*t**2

# ---- LEADING term: rg_ik * q0poly(i,k)(v) ; factor rg_ik removed ----
L  = q0poly(si,sk,v)
Lp = sp.diff(L, v)
# L'(v) = -2*pi*(cLeadA*v + cLeadB)/(768 D^4)  ->  W = 768 D^4 /(2 pi) * L'(v) = -(cLeadA v + cLeadB)
Wl = sp.expand( sp.Rational(768,1)*D**4/(2*pi) * Lp )
Wl = sp.Poly(Wl, v)
cLeadA = sp.simplify(-Wl.coeff_monomial(v))
cLeadB = sp.simplify(-Wl.coeff_monomial(1))
print("cLeadC2? (v^2 coeff of Wl, must be 0):", sp.simplify(Wl.coeff_monomial(v**2)))

# ---- per-species l correlation term: I_l(v) = ∫_{v+lam(k,l)}^{R(i,l)} P1(t) P2(t,v) dt ----
P1 = q0poly(si, sl, t)                                  # pair (i,l), Qpp(l)
# P2(t,v): second factor of qpConv_upper_intervalForm with (x+R(k,l)) shift, Qpp(l)
s2 = v + R(sk,sl)
P2 = (-Q0(sk,sl)*s2 + Qpp(sl)*s2**2/2) + (Q0(sk,sl)-Qpp(sl)*s2)*t + (Qpp(sl)/2)*t**2
a_lo = v + lam(sk,sl)
b_hi = R(si,sl)
Il  = sp.integrate(sp.expand(P1*P2), (t, a_lo, b_hi))
Ilp = sp.diff(Il, v)
# cCorrPiece_l = rho_l * I_l'(v)/(2 pi v);  W_c*v = 768 D^4/(2pi) * rho_l * I_l'(v)
Wc = sp.expand( sp.Rational(768,1)*D**4/(2*pi) * rl * Ilp )
Wc = sp.Poly(Wc, v)
cCorrB  = sp.simplify(Wc.coeff_monomial(1))
cCorrA  = sp.simplify(Wc.coeff_monomial(v))
cCorrC2 = sp.simplify(Wc.coeff_monomial(v**2))
cCorrE  = sp.simplify(Wc.coeff_monomial(v**4))
print("no-v^3 in Wc (must be 0):", sp.simplify(Wc.coeff_monomial(v**3)))
print("derived per-species coefficients OK")

# ================= VALIDATION vs verified binary cUpperANum/BNum/C2Num/ENum =================
# binary coefficients (exact Lean transcription, D=vac, ri,rk,si,sk, xi expanded)
def bindefs():
    ANum = (-768*D**3 - 448*D**2*pi*ri*si**3 - 192*D**2*pi*ri*si**2*sk - 192*D**2*pi*ri*si*sk**2
     - 64*D**2*pi*ri*sk**3 - 64*D**2*pi*rk*si**3 - 192*D**2*pi*rk*si**2*sk - 192*D**2*pi*rk*si*sk**2
     - 448*D**2*pi*rk*sk**3 - 160*D*pi**2*ri**2*si**6 - 96*D*pi**2*ri**2*si**4*sk**2
     - 64*D*pi**2*ri**2*si**3*sk**3 - 64*D*pi**2*ri*rk*si**5*sk - 256*D*pi**2*ri*rk*si**4*sk**2
     - 256*D*pi**2*ri*rk*si**2*sk**4 - 64*D*pi**2*ri*rk*si*sk**5 - 64*D*pi**2*rk**2*si**3*sk**3
     - 96*D*pi**2*rk**2*si**2*sk**4 - 160*D*pi**2*rk**2*sk**6 - 16*pi**3*ri**3*si**9
     - 16*pi**3*ri**3*si**6*sk**3 - 48*pi**3*ri**2*rk*si**7*sk**2 - 48*pi**3*ri**2*rk*si**4*sk**5
     - 48*pi**3*ri*rk**2*si**5*sk**4 - 48*pi**3*ri*rk**2*si**2*sk**7 - 16*pi**3*rk**3*si**3*sk**6
     - 16*pi**3*rk**3*sk**9)
    BNum = (108*D**2*pi*ri*si**4 - 144*D**2*pi*ri*si**3*sk - 24*D**2*pi*ri*si**2*sk**2
     + 48*D**2*pi*ri*si*sk**3 + 12*D**2*pi*ri*sk**4 + 12*D**2*pi*rk*si**4 + 48*D**2*pi*rk*si**3*sk
     - 24*D**2*pi*rk*si**2*sk**2 - 144*D**2*pi*rk*si*sk**3 + 108*D**2*pi*rk*sk**4
     + 36*D*pi**2*ri**2*si**7 - 24*D*pi**2*ri**2*si**6*sk - 48*D*pi**2*ri**2*si**5*sk**2
     + 24*D*pi**2*ri**2*si**4*sk**3 + 12*D*pi**2*ri**2*si**3*sk**4 + 12*D*pi**2*ri*rk*si**6*sk
     + 60*D*pi**2*ri*rk*si**5*sk**2 - 72*D*pi**2*ri*rk*si**4*sk**3 - 72*D*pi**2*ri*rk*si**3*sk**4
     + 60*D*pi**2*ri*rk*si**2*sk**5 + 12*D*pi**2*ri*rk*si*sk**6 + 12*D*pi**2*rk**2*si**4*sk**3
     + 24*D*pi**2*rk**2*si**3*sk**4 - 48*D*pi**2*rk**2*si**2*sk**5 - 24*D*pi**2*rk**2*si*sk**6
     + 36*D*pi**2*rk**2*sk**7 + 3*pi**3*ri**3*si**10 - 6*pi**3*ri**3*si**8*sk**2
     + 3*pi**3*ri**3*si**6*sk**4 + 9*pi**3*ri**2*rk*si**8*sk**2 - 18*pi**3*ri**2*rk*si**6*sk**4
     + 9*pi**3*ri**2*rk*si**4*sk**6 + 9*pi**3*ri*rk**2*si**6*sk**4 - 18*pi**3*ri*rk**2*si**4*sk**6
     + 9*pi**3*ri*rk**2*si**2*sk**8 + 3*pi**3*rk**3*si**4*sk**6 - 6*pi**3*rk**3*si**2*sk**8
     + 3*pi**3*rk**3*sk**10)
    C2Num = (480*D**2*pi*ri*si**2 + 192*D**2*pi*ri*si*sk + 96*D**2*pi*ri*sk**2 + 96*D**2*pi*rk*si**2
     + 192*D**2*pi*rk*si*sk + 480*D**2*pi*rk*sk**2 + 192*D*pi**2*ri**2*si**5
     + 96*D*pi**2*ri**2*si**4*sk + 96*D*pi**2*ri**2*si**3*sk**2 + 96*D*pi**2*ri*rk*si**4*sk
     + 288*D*pi**2*ri*rk*si**3*sk**2 + 288*D*pi**2*ri*rk*si**2*sk**3 + 96*D*pi**2*ri*rk*si*sk**4
     + 96*D*pi**2*rk**2*si**2*sk**3 + 96*D*pi**2*rk**2*si*sk**4 + 192*D*pi**2*rk**2*sk**5
     + 24*pi**3*ri**3*si**8 + 24*pi**3*ri**3*si**6*sk**2 + 72*pi**3*ri**2*rk*si**6*sk**2
     + 72*pi**3*ri**2*rk*si**4*sk**4 + 72*pi**3*ri*rk**2*si**4*sk**4 + 72*pi**3*ri*rk**2*si**2*sk**6
     + 24*pi**3*rk**3*si**2*sk**6 + 24*pi**3*rk**3*sk**8)
    ENum = (-64*D**2*pi*ri - 64*D**2*pi*rk - 64*D*pi**2*ri**2*si**3 - 64*D*pi**2*ri*rk*si**2*sk
     - 64*D*pi**2*ri*rk*si*sk**2 - 64*D*pi**2*rk**2*sk**3 - 16*pi**3*ri**3*si**6
     - 48*pi**3*ri**2*rk*si**4*sk**2 - 48*pi**3*ri*rk**2*si**2*sk**4 - 16*pi**3*rk**3*sk**6)
    return ANum,BNum,C2Num,ENum
binA,binB,binC2,binE = bindefs()

# build general-N summed coeffs for binary: sum over l in {i,k}, then xi -> ri si^2 + rk sk^2
def sub_l(expr, sl_val, rl_val):
    return expr.subs({sl:sl_val, rl:rl_val})
xi_bin = ri*si**2 + rk*sk**2
def assemble(cLead, cCorr):
    tot = cLead + sub_l(cCorr, si, ri) + sub_l(cCorr, sk, rk)   # l=i and l=k
    return sp.expand(tot.subs(xi, xi_bin))
def assemble_corr_only(cCorr):
    tot = sub_l(cCorr, si, ri) + sub_l(cCorr, sk, rk)
    return sp.expand(tot.subs(xi, xi_bin))

gA  = assemble(cLeadA, cCorrA)
gB  = assemble(cLeadB, cCorrB)
gC2 = assemble_corr_only(cCorrC2)
gE  = assemble_corr_only(cCorrE)

print("A match:",  sp.simplify(gA  - sp.expand(binA))  == 0)
print("B match:",  sp.simplify(gB  - sp.expand(binB))  == 0)
print("C2 match:", sp.simplify(gC2 - sp.expand(binC2)) == 0)
print("E match:",  sp.simplify(gE  - sp.expand(binE))  == 0)

print("\n===== explicit forms (D=vac, xi=xi2 atomic) =====")
for nm,ex in [("cLeadANum",cLeadA),("cLeadBNum",cLeadB),
              ("cCorrANum",cCorrA),("cCorrBNum",cCorrB),
              ("cCorrC2Num",cCorrC2),("cCorrENum",cCorrE)]:
    p = sp.Poly(sp.expand(ex), D, pi, xi, si, sk, sl, rl)
    print(f"\n--- {nm} ({len(p.terms())} terms) ---")
    print(sp.expand(ex))
