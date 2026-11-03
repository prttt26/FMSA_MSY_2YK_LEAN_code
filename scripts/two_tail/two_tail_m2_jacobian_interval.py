"""External interval regularity certificate for the BH amplitude Jacobian at Codex's M2 control
(handoff 137).  NOT a Lean proof; not a root-existence or first-loss claim.

Root box: read-only from MSA_and_1st_Truncation/results/coupling_singularities/
codex_m2_zero_mode_firstness.json (handoff 011), entries 0..3 = (D1, D2, G1, G2) in the Lean IsRoot
convention (Dt, G); entry 4 = tau, 5 = w.  Its sha256 is recorded.

Jacobian: forward-mode automatic differentiation of the literal N = 1 two-tail Lean residual
(as in two_tail_fiber_diag.make_residual), carried out in mpmath interval arithmetic
(outward rounding, 192 bits).  The derivative is the analytic one, evaluated over the whole
amplitude box; no finite differences, and no interval wrapper around a float Jacobian.  The
residual's tau*K term does not depend on the amplitudes, so J depends only on (D, G) and on the
exact data: eta = 1/10, rho = 6 eta/pi, sigma = 1, z = (9/5, 12).

Certificate: an exact dyadic-rational C (the float inverse of the midpoint Jacobian, whose
entries are exact binary rationals) with ||I - C J(box)||_inf < 1 (upper row-sum bound).  That
implies C J(u) is invertible, hence J(u) is invertible, for every u in the box.
Checks: (i) the interval residual over the full root box (with its tau, w intervals) contains 0;
(ii) the AD Jacobian at the box midpoint agrees with a SymPy symbolic Jacobian.

Usage: two_tail_m2_jacobian_interval.py OUT.json
"""
import sys, json, hashlib
from fractions import Fraction
from pathlib import Path
import numpy as np
import mpmath
from mpmath import iv

iv.prec = 192
LO = lambda x: mpmath.mp.make_mpf(x._mpi_[0])     # exact endpoints of an iv interval
HI = lambda x: mpmath.mp.make_mpf(x._mpi_[1])
ROOT = Path(__file__).resolve().parents[3]/'MSA_and_1st_Truncation'/'results'/'coupling_singularities'/'codex_m2_zero_mode_firstness.json'


class D:
    """Dual number over mpmath intervals: value v and gradient g (list of 4 intervals)."""
    def __init__(self, v, g=None):
        self.v = v; self.g = g if g is not None else [iv.mpf(0)]*4
    @staticmethod
    def c(x):
        return D(x if isinstance(x, type(iv.mpf(0))) else iv.mpf(x))
    def _o(self, o):
        return o if isinstance(o, D) else D.c(o)
    def __add__(self, o): o = self._o(o); return D(self.v + o.v, [a + b for a, b in zip(self.g, o.g)])
    __radd__ = __add__
    def __sub__(self, o): o = self._o(o); return D(self.v - o.v, [a - b for a, b in zip(self.g, o.g)])
    def __rsub__(self, o): return self._o(o) - self
    def __neg__(self): return D(-self.v, [-a for a in self.g])
    def __mul__(self, o):
        o = self._o(o); return D(self.v*o.v, [self.v*b + o.v*a for a, b in zip(self.g, o.g)])
    __rmul__ = __mul__
    def __truediv__(self, o):
        o = self._o(o)
        return D(self.v/o.v, [(a*o.v - self.v*b)/(o.v*o.v) for a, b in zip(self.g, o.g)])
    def __rtruediv__(self, o): return self._o(o)/self
    def __pow__(self, n):
        r = D.c(1)
        for _ in range(n):
            r = r*self
        return r


def residual(u, rho, sig, z, Kt):
    """Literal Lean residual, N = 1, two tails (same formulas as two_tail_fiber_diag); u are D.
    All constants are lifted to D first (mpmath iv does not defer to foreign operands); exp is only
    ever applied to constants, so E() takes the exponential of the value and asserts zero gradient."""
    def E(x):
        assert all(gi.a == 0 and gi.b == 0 for gi in x.g)
        return D.c(iv.exp(x.v))
    PI = D.c(iv.pi); rho = D.c(rho); sig = D.c(sig); z = [D.c(x) for x in z]
    Kt = [k if isinstance(k, D) else D.c(k) for k in Kt]
    eta = PI/6*rho*sig**3; vac = 1 - eta; xi2 = rho*sig**2
    Qpp0 = 2*PI/vac*(1 + PI*xi2*sig/(2*vac))
    Q0p0 = 2*PI/vac*(sig + PI*xi2*sig**2/(4*vac))
    cN = 2*PI**2*xi2/vac**2
    Dt, G = u[:2], u[2:]
    gam = [1 - 2*PI*rho*G[a]*E(-z[a]*sig)/z[a] for a in range(2)]
    Ct = [gam[a]*Dt[a] for a in range(2)]
    Wt = [2*PI/z[a]*rho*G[a]*Dt[a] for a in range(2)]
    Mj = sum((-(1/z[a])*rho*(Wt[a] + (1 + z[a]*sig)*Ct[a]) for a in range(2)), D.c(0))
    Nj = sum((rho*(Wt[a]/z[a]**2 + (1 + z[a]*sig + (z[a]*sig)**2/2)/z[a]**2*Ct[a]) for a in range(2)), D.c(0))
    A = Qpp0 + Qpp0*Mj + cN*Nj
    Qp = Q0p0 + Q0p0*Mj + Qpp0*Nj
    out = [None]*4
    for a in range(2):
        s = z[a]; x = s*sig; e = E(-x)
        Qh = ((1 - x - e)/s**2*Qp + (1 - x + x**2/2 - e)/s**3*A
              + sum((Wt[t]/(s + z[t]) + Ct[t]*(1 - e)/s for t in range(2)), D.c(0))
              + sum((Ct[t]*e/(s + z[t]) for t in range(2)), D.c(0)))
        out[a] = Dt[a]*(1 - rho*Qh) - 2*PI*Kt[a]/s
        src = (A + s*Qp + sum((s**2*z[t]/(s + z[t])*Ct[t] for t in range(2)), D.c(0)))/s**2
        out[2 + a] = 2*PI*G[a]*(1 - rho*Qh) - src
    return out


WIDEN = float(__import__('os').environ.get('WIDEN', '0'))     # relative outward widening of the JSON endpoints


def box(lo, hi):
    """Outward box from JSON doubles.  The widening is done in iv (outward rounding), not in plain
    mpmath.mpf, whose 53-bit default precision is unaffected by iv.prec (point raised in handoff 139)."""
    w = iv.mpf(WIDEN)*max(abs(iv.mpf(lo)), abs(iv.mpf(hi))).b
    return iv.mpf([(iv.mpf(lo) - w).a, (iv.mpf(hi) + w).b])


def main():
    out_path = sys.argv[1]
    cmd = ' '.join([sys.executable] + sys.orig_argv[1:]); print('# ' + cmd, flush=True)
    print('# EXTERNAL interval regularity certificate (mpmath iv, 192 bits); not a Lean proof', flush=True)
    raw = ROOT.read_bytes(); sha = hashlib.sha256(raw).hexdigest(); cert = json.loads(raw)
    assert cert['model'] == {'eta': '0.1', 'z': ['1.8', '12'], 'sigma': '1'}, cert['model']
    assert cert['status'] == 'PASS_FIRST_ZERO_MODE_CONTACT'
    rb = cert['root_box']
    print(f"# root box: {ROOT}  sha256={sha}  status={cert['status']}", flush=True)
    eta = iv.mpf(1)/10; rho = 6*eta/iv.pi; sig = iv.mpf(1); z = [iv.mpf(9)/5, iv.mpf(12)]
    # w0 = -(1/z1 + 1/z1^2)/(1/z2 + 1/z2^2): only to check w against f; K = (1, w)
    Ubox = [box(*rb[i]) for i in range(4)]
    tau, wbox = box(*rb[4]), box(*rb[5])

    def as_dual(us):
        return [D(us[i], [iv.mpf(1) if j == i else iv.mpf(0) for j in range(4)]) for i in range(4)]

    # (i) residual over the full root box contains 0 (convention check)
    r = residual(as_dual(Ubox), rho, sig, z, [tau*1, tau*wbox])
    contains0 = [bool(0 in ri.v) for ri in r]
    print('residual over root box:', [str(ri.v) for ri in r], 'contains 0:', contains0, flush=True)

    # interval Jacobian over the amplitude box
    Jb = [[ri.g[j] for j in range(4)] for ri in r]
    # midpoint Jacobian (degenerate intervals) and float inverse
    mid = [iv.mpf(mpmath.mpf((rb[i][0] + rb[i][1])/2)) for i in range(4)]
    rm = residual(as_dual(mid), rho, sig, z, [tau*1, tau*wbox])
    Jm = np.array([[float(rm[i].g[j].mid) for j in range(4)] for i in range(4)])
    C = np.linalg.inv(Jm)
    Cq = [[Fraction(float(C[i, j])) for j in range(4)] for i in range(4)]      # exact dyadic rationals
    Civ = [[iv.mpf(mpmath.mpf(Cq[i][j].numerator)/mpmath.mpf(Cq[i][j].denominator)) for j in range(4)] for i in range(4)]
    for i in range(4):
        for j in range(4):
            assert Civ[i][j].a == Civ[i][j].b, 'C entry not exactly representable'
    # E = I - C J(box), interval
    E = [[(iv.mpf(1) if i == j else iv.mpf(0)) - sum((Civ[i][k]*Jb[k][j] for k in range(4)), iv.mpf(0))
          for j in range(4)] for i in range(4)]
    rows = [HI(sum((abs(E[i][j]) for j in range(4)), iv.mpf(0))) for i in range(4)]   # exact upper endpoints (mpf)
    bound = max(rows)
    passed = bound < 1
    # (ii) SymPy symbolic Jacobian at the midpoint, float, as an independent derivative check
    import sympy as sp
    Ds = sp.symbols('D1 D2 G1 G2'); r_s, s_s, z1s, z2s, ts, ws = sp.symbols('rho sigma z1 z2 tau w')
    PI = sp.pi
    def sres(u):
        rho_, sig_ = r_s, s_s; zz = [z1s, z2s]; Kt = [ts, ts*ws]
        eta_ = PI/6*rho_*sig_**3; vac = 1 - eta_; xi2 = rho_*sig_**2
        Qpp0 = 2*PI/vac*(1 + PI*xi2*sig_/(2*vac)); Q0p0 = 2*PI/vac*(sig_ + PI*xi2*sig_**2/(4*vac)); cN = 2*PI**2*xi2/vac**2
        Dt, G = u[:2], u[2:]
        gam = [1 - 2*PI*rho_*G[a]*sp.exp(-zz[a]*sig_)/zz[a] for a in range(2)]
        Ct = [gam[a]*Dt[a] for a in range(2)]; Wt = [2*PI/zz[a]*rho_*G[a]*Dt[a] for a in range(2)]
        Mj = sum(-(1/zz[a])*rho_*(Wt[a] + (1 + zz[a]*sig_)*Ct[a]) for a in range(2))
        Nj = sum(rho_*(Wt[a]/zz[a]**2 + (1 + zz[a]*sig_ + (zz[a]*sig_)**2/2)/zz[a]**2*Ct[a]) for a in range(2))
        A = Qpp0 + Qpp0*Mj + cN*Nj; Qp = Q0p0 + Q0p0*Mj + Qpp0*Nj
        o = []
        for a in range(2):
            s = zz[a]; x = s*sig_; e = sp.exp(-x)
            Qh = ((1 - x - e)/s**2*Qp + (1 - x + x**2/2 - e)/s**3*A
                  + sum(Wt[t]/(s + zz[t]) + Ct[t]*(1 - e)/s for t in range(2)) + sum(Ct[t]*e/(s + zz[t]) for t in range(2)))
            o.append(Dt[a]*(1 - rho_*Qh) - 2*PI*Kt[a]/s)
        for a in range(2):
            s = zz[a]; x = s*sig_; e = sp.exp(-x)
            Qh = ((1 - x - e)/s**2*Qp + (1 - x + x**2/2 - e)/s**3*A
                  + sum(Wt[t]/(s + zz[t]) + Ct[t]*(1 - e)/s for t in range(2)) + sum(Ct[t]*e/(s + zz[t]) for t in range(2)))
            src = (A + s*Qp + sum(s**2*zz[t]/(s + zz[t])*Ct[t] for t in range(2)))/s**2
            o.append(2*PI*G[a]*(1 - rho_*Qh) - src)
        return o
    Jsym = sp.Matrix(sres(list(Ds))).jacobian(sp.Matrix(Ds))
    subs = {r_s: sp.Rational(6, 10)/sp.pi, s_s: 1, z1s: sp.Rational(9, 5), z2s: 12}
    subs.update({Ds[i]: sp.Float((rb[i][0] + rb[i][1])/2, 30) for i in range(4)})
    Js = np.array(Jsym.subs(subs).evalf(30).tolist(), dtype=float)
    sym_diff = float(np.max(np.abs(Js - Jm)/np.maximum(1, np.abs(Jm))))
    print('AD-vs-SymPy Jacobian at midpoint, max rel diff:', f'{sym_diff:.2e}', flush=True)
    print('interval Jacobian J(box):', flush=True)
    for i in range(4):
        print('  ', [mpmath.nstr(Jb[i][j], 12) for j in range(4)], flush=True)
    print('rational C (exact dyadic, as fractions):', flush=True)
    for i in range(4):
        print('  ', [str(Cq[i][j]) for j in range(4)], flush=True)
    print('row sums of |I - C J(box)| (upper):', [mpmath.nstr(x, 6) for x in rows], flush=True)
    print(f"||I - C J(box)||_inf <= {mpmath.nstr(bound, 8)}  ->  {'PASS' if passed else 'FAIL'}", flush=True)
    res = dict(command=cmd, label='EXTERNAL interval certificate (mpmath iv, 192 bits); not a Lean proof',
               scope='Uniform invertibility of the BH amplitude Jacobian dR/d(D1,D2,G1,G2) over the amplitude '
                     'projection of the certified root box. Not a root-existence, first-loss or canonicity claim.',
               root_box_source=str(ROOT), root_box_sha256=sha, root_box_status=cert['status'],
               root_box_source_hashes=cert.get('source_sha256'),
               amplitude_box=[rb[i] for i in range(4)], tau_box=rb[4], w_box=rb[5],
               data=dict(eta='1/10', rho='6*eta/pi', sigma='1', z=['9/5', '12'], K='(1, w)'),
               residual_over_root_box=[[mpmath.nstr(LO(ri.v), 17), mpmath.nstr(HI(ri.v), 17)] for ri in r],
               residual_contains_zero=contains0,
               J_box=[[[mpmath.nstr(LO(Jb[i][j]), 20), mpmath.nstr(HI(Jb[i][j]), 20)] for j in range(4)] for i in range(4)],
               C_rational=[[str(Cq[i][j]) for j in range(4)] for i in range(4)],
               row_sums_upper=[mpmath.nstr(x, 12) for x in rows], inf_norm_bound=mpmath.nstr(bound, 12),
               passed=bool(passed), ad_vs_sympy_rel_diff=sym_diff, precision_bits=iv.prec, widen_rel=WIDEN,
               mpmath_version=mpmath.__version__)
    json.dump(res, open(out_path, 'w'), indent=1)


if __name__ == '__main__':
    main()
