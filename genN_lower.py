import sympy as sp, re
D, xi, pi = sp.symbols('D xi pi', positive=True)
si, sk, sl, rl, ri, rk = sp.symbols('si sk sl rl ri rk', positive=True)
v, t = sp.symbols('v t', real=True)
def R(a,b): return (a+b)/2
def lam(a,b): return (b-a)/2
def Q0(a,b): return (2*pi/D)*( R(a,b) + pi*xi*a*b/(4*D) )
def Qpp(b):  return (2*pi/D)*( 1 + pi*xi*b/(2*D) )
def q0poly(a,b,tt): return (-Q0(a,b)*R(a,b) + Qpp(b)*R(a,b)**2/2) + (Q0(a,b)-Qpp(b)*R(a,b))*tt + (Qpp(b)/2)*tt**2

# ---- LOWER piece ----
# reflected leading: rg_ik * q0poly(k,i)(-v)  ; factor rg_ik removed -> Lref(v)=q0poly(k,i)(-v)
Lref = q0poly(sk, si, -v)
Lrefp = sp.diff(Lref, v)
# matDCFreCore_lower' (per rg_ik) = Lref'(v) - sum_l rho_l * Il_lower'(v)
# Il_lower(x) = ∫_{lam(i,l)}^{R(i,l)} P1(t) P2(t,x) dt  (FIXED limits)
P1 = q0poly(si, sl, t); s2 = v + R(sk,sl)
P2 = (-Q0(sk,sl)*s2 + Qpp(sl)*s2**2/2) + (Q0(sk,sl)-Qpp(sl)*s2)*t + (Qpp(sl)/2)*t**2
Illow = sp.integrate(sp.expand(P1*P2), (t, lam(si,sl), R(si,sl)))
Illowp = sp.diff(Illow, v)
# match: Lref'(v) - sum_l rho_l Il_low'(v) = -2π v cLowerPieceN  (constant cLowerPieceN)
# leading: Lref'(v) = -2π v cLowerLead  -> cLowerLead = -Lref'(v)/(2π v)
cLowerLead = sp.simplify(-Lref/1) # placeholder
# Actually cLowerPieceN is constant: check -matDCFreCore'/(2π v) is v-independent
# per-species: rho_l Il_low'(v) = 2π v cLowerCorr_l -> cLowerCorr_l = rho_l Il_low'(v)/(2π v)
lead_expr = sp.simplify(-Lrefp/(2*pi*v))
corr_expr = sp.simplify(rl*Illowp/(2*pi*v))
print("lead constant in v?", sp.simplify(sp.diff(lead_expr,v))==0)
print("corr constant in v?", sp.simplify(sp.diff(corr_expr,v))==0)
cLowerLead = sp.expand(lead_expr)
cLowerCorr = sp.expand(corr_expr)
# cLowerPieceN = cLowerLead + sum_l cLowerCorr_l ; as /(768 D^4): multiply
# express numerators over 768 D^4
cLowerLeadNum = sp.expand(cLowerLead*768*D**4)
cLowerCorrNum = sp.expand(cLowerCorr*768*D**4)
print("leadNum terms:", len(sp.Add.make_args(cLowerLeadNum)))
print("corrNum terms:", len(sp.Add.make_args(cLowerCorrNum)))

# validate vs binary cLowerPiece (constant): -numL/(24 D^4), xi -> ri si^2 + rk sk^2, sum l in {i,k}
numL = (24*D**3 + pi*D**2*(28*ri*si**3 + 4*rk*si**3 + 12*rk*si**2*sk + 12*rk*si*sk**2)
 + pi**2*D*(10*ri**2*si**6 + 4*ri*rk*si**5*sk + 16*ri*rk*si**4*sk**2 + 4*rk**2*si**3*sk**3
   + 6*rk**2*si**2*sk**4)
 + pi**3*(ri**3*si**9 + 3*ri**2*rk*si**7*sk**2 + 3*ri*rk**2*si**5*sk**4 + rk**3*si**3*sk**6))
binLowerNum = sp.expand(-numL*32)   # cLowerPiece = -numL/(24D^4) = (-32 numL)/(768 D^4)
xi_bin = ri*si**2 + rk*sk**2
tot = cLowerLeadNum + cLowerCorrNum.subs({sl:si,rl:ri}) + cLowerCorrNum.subs({sl:sk,rl:rk})
tot = sp.expand(tot.subs(xi, xi_bin))
print("LOWER match:", sp.simplify(tot - binLowerNum) == 0)
