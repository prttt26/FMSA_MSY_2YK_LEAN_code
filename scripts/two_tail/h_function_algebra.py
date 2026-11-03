"""The algebraic steps of the pure-fluid positivity proof, by exact computer algebra in the symbols (EXTERNAL symbolic check, NOT a Lean proof).

Each step is an identity with T nowhere in it: a single tail enters linearly, or only Laurent coefficients at x = 0 appear, so the checks hold for every T.
 A. F(x) = P(x) + e^(-x) Shat(x) for the BH factors, Shat = rho S/x, one tail in general position (F, S are linear in the tails, so one suffices).
 B. P0(x) P0(-x) - Shat0(x) Shat0(-x) = 1, the hard-sphere matrix is unimodular.
 C. With U, g regular at 0 (arbitrary coefficients), P = (U - g/x) P0(x) + (g/x) Shat0(-x), Shat = (U - g/x) Shat0(x) + (g/x) P0(-x): the polar parts have the required form,
    and the two relations a = a0 (1 + Mv) + b4 Nc, q = q0 (1 + Mv) + a0 Nc hold identically, Mv and Nc read from the Laurent coefficients.
 D. F0(z) - e^-z F0(-z) = (1 - e^-z) + A (z (1 + e^-z) - 2 (1 - e^-z))/z^2, A = 6 eta/(1 - eta).
 E. G - G0 = g/(2 pi rho F0 F): Shat - (Shat0/F0) F = (g/x)/F0, from B.
"""
import sys
import sympy as sp
x, eta, z, D, C, W = sp.symbols('x eta z D C W', positive=True)
print('cmd:', ' '.join(sys.argv), '(EXTERNAL symbolic check, NOT a Lean proof)', flush=True)
rho = 6*eta/sp.pi; d = 2*sp.pi/(1 - eta)**2
A0, B0, QP0 = d*((1 - eta) + 3*eta), d*(-sp.Rational(3, 2)*eta), d*(sp.Rational(3, 2)*eta + (1 - eta))
a0, q0, b4 = sp.simplify(rho*A0), sp.simplify(rho*QP0), sp.simplify(-4*rho*B0)
print('a0, q0, b4 =', sp.factor(a0), sp.factor(q0), sp.factor(b4), '; q0 - a0/2 =', sp.factor(q0 - a0/2), flush=True)

# A. one tail
Mv = -rho*(W + (1 + z)*C)/z; Nc = rho*(W/z**2 + (1 + z + z**2/2)/z**2*C)
A = A0*(1 + Mv) - 4*B0*Nc; qp = QP0*(1 + Mv) + A0*Nc
phi1 = (1 - x - sp.exp(-x))/x**2; phi2 = (1 - x + x**2/2 - sp.exp(-x))/x**3; ex = (1 - sp.exp(-x))/x
Q = phi1*qp + phi2*A + W/(x + z) + C*(sp.exp(-x)/(x + z) + ex)
F = 1 - rho*Q; S = (A + x*qp + x**2*z/(x + z)*C)/x**2
a, q, c = rho*A, rho*qp, rho*C
Shat = a/x**3 + q/x**2 + c/x - rho*C/(x + z)
P = 1 - a/x**3 + (a - q)/x**2 + (q - a/2 - c)/x - rho*W/(x + z)
print('A. F - (P + e^-x Shat):', sp.simplify(F - P - sp.exp(-x)*Shat), '; rho S/x - Shat:', sp.simplify(rho*S/x - Shat), flush=True)

# B.
P0 = lambda y: 1 - a0/y**3 + (a0 - q0)/y**2 + (q0 - a0/2)/y
S0 = lambda y: a0/y**3 + q0/y**2
print('B. det Theta0 - 1:', sp.simplify(P0(x)*P0(-x) - S0(x)*S0(-x) - 1), flush=True)

# C. Laurent identities, with a0, q0 kept as symbols where possible
a0s, q0s, b4s = sp.symbols('a0 q0 b4'); u0, u1, u2, g0, g1, g2, g3 = sp.symbols('u0 u1 u2 g0 g1 g2 g3')
U = u0 + u1*x + u2*x**2; g = g0 + g1*x + g2*x**2 + g3*x**3
Pa = lambda y: 1 - a0s/y**3 + (a0s - q0s)/y**2 + (q0s - a0s/2)/y
Sa = lambda y: a0s/y**3 + q0s/y**2
D12 = g/x; D11 = U - D12
Pc = sp.expand(D11*Pa(x) + D12*Sa(-x)); Sc = sp.expand(D11*Sa(x) + D12*Pa(-x))
co = lambda e, k: e.coeff(x, k)
ac, qc, cc = co(Sc, -3), co(Sc, -2), co(Sc, -1)
print('C. x^-4 of Shat, P:', co(Sc, -4), co(Pc, -4), '; P polar minus required form:', sp.simplify(co(Pc, -3) + ac), sp.simplify(co(Pc, -2) - (ac - qc)), sp.simplify(co(Pc, -1) - (qc - ac/2 - cc)), flush=True)
p1, p2, s1, s2 = -co(Sc, 0), co(Sc, 1), 1 - co(Pc, 0), co(Pc, 1)
Mvc = -s1 - p1 - cc; Ncc = s2 + p2 + p1 + cc/2       # the sums over tails, read from the Laurent coefficients at 0
ra = sp.simplify((ac - a0s*(1 + Mvc) - b4s*Ncc).subs({a0s: a0, q0s: q0, b4s: b4})); rq = sp.simplify((qc - q0s*(1 + Mvc) - a0s*Ncc).subs({a0s: a0, q0s: q0, b4s: b4}))
print('   residual of a = a0 (1 + Mv) + b4 Nc:', ra, '; of q = q0 (1 + Mv) + a0 Nc:', rq, flush=True)

# D.
e = sp.exp(-z); AA = 6*eta/(1 - eta)
F0 = lambda y: P0(y) + sp.exp(-y)*S0(y)
print('D. difference from the closed form:', sp.simplify(F0(z) - e*F0(-z) - ((1 - e) + AA*(z*(1 + e) - 2*(1 - e))/z**2)), flush=True)

# E.
G12 = sp.Symbol('D12'); G11 = sp.Symbol('D11'); ee = sp.exp(-x)
Pd = G11*P0(x) + G12*S0(-x); Sd = G11*S0(x) + G12*P0(-x); Fd = Pd + ee*Sd; F00 = P0(x) + ee*S0(x)
print('E. Shat - (Shat0/F0) F - D12/F0:', sp.simplify(Sd - S0(x)/F00*Fd - G12/F00), flush=True)
