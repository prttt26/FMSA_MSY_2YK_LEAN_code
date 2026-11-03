"""M1 endgame for two_tail_fiber_diag: polish, in 40-digit mpmath Newton at t = 1, the homotopy
paths that stopped (step underflow) within 2e-3 of the traced endpoint root, and compare their
limits with the traced root.  The literal Lean residual is re-evaluated in mpmath (same formulas
as two_tail_fiber_diag.make_residual).  FLOAT/high-precision diagnostic, not a certificate.

Usage: two_tail_fiber_m1_endgame.py DIAG.json
"""
import sys, json
import mpmath as mp
mp.mp.dps = 40
print('#', ' '.join(sys.orig_argv))
d = json.load(open(sys.argv[1]))
c = next(c for c in d['controls'] if c['name'].startswith('M1'))
sys.path.insert(0, '.')
from two_tail_margin import state
from two_tail_scan import w0
st0 = state(c['z'][0], c['z'][1], c['w'], c['eta'])
rho, sig = mp.mpf(float(st0.rho[0])), mp.mpf(float(st0.sigma[0]))
z = [mp.mpf(float(x)) for x in st0.z]
Kt = [mp.mpf(float(k))*mp.mpf(c['beta']) for k in st0.K[:, 0, 0]]
PI = mp.pi
eta = PI/6*rho*sig**3; vac = 1 - eta; xi2 = rho*sig**2
Qpp0 = 2*PI/vac*(1 + PI*xi2*sig/(2*vac)); Q0p0 = 2*PI/vac*(sig + PI*xi2*sig**2/(4*vac)); cN = 2*PI**2*xi2/vac**2

def f(u):
    Dt, G = u[:2], u[2:]
    gam = [1 - 2*PI*rho*G[a]*mp.exp(-z[a]*sig)/z[a] for a in range(2)]
    Ct = [gam[a]*Dt[a] for a in range(2)]; Wt = [2*PI/z[a]*rho*G[a]*Dt[a] for a in range(2)]
    Mj = sum(-(1/z[a])*rho*(Wt[a] + (1 + z[a]*sig)*Ct[a]) for a in range(2))
    Nj = sum(rho*(Wt[a]/z[a]**2 + (1 + z[a]*sig + (z[a]*sig)**2/2)/z[a]**2*Ct[a]) for a in range(2))
    A = Qpp0 + Qpp0*Mj + cN*Nj; Qp = Q0p0 + Q0p0*Mj + Qpp0*Nj
    out = []
    for a in range(2):
        s = z[a]; x = s*sig; e = mp.exp(-x)
        Qh = ((1 - x - e)/s**2*Qp + (1 - x + x**2/2 - e)/s**3*A
              + sum(Wt[t]/(s + z[t]) + Ct[t]*(1 - e)/s for t in range(2)) + sum(Ct[t]*e/(s + z[t]) for t in range(2)))
        out.append(Dt[a]*(1 - rho*Qh) - 2*PI*Kt[a]/s)
        out.append(None)
        src = (A + s*Qp + sum(s**2*z[t]/(s + z[t])*Ct[t] for t in range(2)))/s**2
        out[-1] = 2*PI*G[a]*(1 - rho*Qh) - src
    return mp.matrix([out[0], out[2], out[1], out[3]])

def newton(u):
    u = mp.matrix(u)
    for it in range(80):
        F = f(u); J = mp.matrix(4, 4); h = mp.mpf('1e-20')
        for j in range(4):
            e = mp.matrix(4, 1); e[j] = h
            J[:, j] = (f(u + e) - f(u - e))/(2*h)
        du = mp.lu_solve(J, -F); u = u + du
        if mp.norm(du) < mp.mpf('1e-30')*(1 + mp.norm(u)):
            break
    return u, it, mp.norm(f(u)), J

us = mp.matrix([mp.mpf(x) for x in c['u_traced']])
ut, it, rt, Jt = newton(us)
print(f"traced root polished: |f|={mp.nstr(rt, 3)} it={it}; moved {mp.nstr(mp.norm(ut - us), 3)} from float u*")
sv = mp.svd_r(mp.matrix([[mp.re(Jt[i, j]) for j in range(4)] for i in range(4)]), compute_uv=False)
print('  singular values of J at traced root:', [mp.nstr(x, 4) for x in sv])
near = [p for p in c['paths'] if p['status'] == 'step underflow' and p['dist_to_traced'] < 2e-3]
lims = []
for k, p in enumerate(near):
    x0 = mp.matrix([mp.mpc(a, b) for a, b in p['u']])
    u, it, r, J = newton(x0)
    dist = max(abs(u[i] - ut[i])/max(1, abs(ut[i])) for i in range(4))
    im = max(abs(mp.im(u[i])) for i in range(4))
    lims.append(u)
    print(f"path {k}: start dist {p['dist_to_traced']:.2e} -> limit |f|={mp.nstr(r, 3)} it={it} "
          f"dist to traced {mp.nstr(dist, 4)} max|Im|={mp.nstr(im, 3)}  u={[mp.nstr(u[i], 12) for i in range(4)]}")
