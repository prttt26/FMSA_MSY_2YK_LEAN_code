#!/usr/bin/env python3
"""
Symbolic proof that the BRK.16 per-`l` real-space Baxter convolution
    ∫_ℝ Q'_il(t+r) · Q_jl(t) dt
decomposes into three regions whose sum equals the `matCoreUneq` per-`l` kernel
(`MSAMixtureCoreUneq.lean`) — with the σ_l dependence CANCELLING.

This underwrites the axiom-free BRK.16 Lean route (`MSAMixtureBreakpointConvDirect.lean`):
it shows the Lean identity `baxterConvCore = matCoreUneq` is TRUE (hence `ring`-closable),
region by region, and pins the interval decomposition:

  edges:  Li=(σl-σi)/2  Hi=(σi+σl)/2   Lj=(σl-σj)/2  Hj=(σj+σl)/2
  INNER (0<r<|λ_ij|):   Lj<Hj<Hi-r  → [Lj,Hj] core·core, [Hj,Hi-r] core_i·tail_j, [Hi-r,∞) tail·tail
  OUTER (|λ_ij|<r<σ_ij): Lj<Hi-r<Hj → [Lj,Hi-r] core·core, [Hi-r,Hj] tail_i·core_j, [Hj,∞) tail·tail

Run: python3 scripts/verify_baxterconv_decomposition.py   (needs sympy)
Expected output: INNER diff = 0 / OUTER diff = 0.
"""
import sympy as sp

z, r, si, sj, sl, t = sp.symbols('z r si sj sl t', positive=True)
qi, Al, Wi, Ci, qj, Wj, Cj = sp.symbols('qi Al Wi Ci qj Wj Cj', real=True)
Li = (sl - si) / 2; Hi = (si + sl) / 2; Lj = (sl - sj) / 2; Hj = (sj + sl) / 2
a, b = si, sj


def Qj_core(t): return qj*(t-Lj-sj) + Al/2*(t-Lj-sj)**2 + Wj*sp.exp(-z*(t-Lj)) + Cj
def Qj_tail(t): return Wj*sp.exp(-z*(t-Lj)) + Cj*sp.exp(-z*(t-Hj))
def Qip_core(t): return qi + Al*(t+r-Li-si) - z*Wi*sp.exp(-z*(t+r-Li))
def Qip_tail(t): return -z*Wi*sp.exp(-z*(t+r-Li)) - z*Ci*sp.exp(-z*(t+r-Hi))


def inner_conv():
    I1 = sp.integrate(Qip_core(t)*Qj_core(t), (t, Lj, Hj))
    I2 = sp.integrate(Qip_core(t)*Qj_tail(t), (t, Hj, Hi-r))
    I3 = sp.integrate(Qip_tail(t)*Qj_tail(t), (t, Hi-r, sp.oo))
    return sp.simplify(I1 + I2 + I3)


def outer_conv():
    I1 = sp.integrate(Qip_core(t)*Qj_core(t), (t, Lj, Hi-r))
    I2 = sp.integrate(Qip_tail(t)*Qj_core(t), (t, Hi-r, Hj))
    I3 = sp.integrate(Qip_tail(t)*Qj_tail(t), (t, Hj, sp.oo))
    return sp.simplify(I1 + I2 + I3)


def inner_target():
    cC0i = ((-b**2/2)*(qi*qj) + (b**3/6)*(qi*Al) + (b**2*(3*a+b)/12)*(Al*qj)
            + (-b**3*(2*a+b)/24)*(Al*Al) + ((-a*b*z**2+z*(-a+b)+2)/(2*z**2))*(Al*Cj)
            + ((-z*(a+b)+2)/(2*z**2))*(Al*Wj) + (b+1/z)*(Cj*qi) + (1/z)*(Wj*qi))
    cC1i = ((-b**2/2)*(Al*qj) + (b**3/6)*(Al*Al) + (b+1/z)*(Al*Cj) + (1/z)*(Al*Wj))
    cEmi = (((-b**2*z**2*sp.exp(b*z)/2+b*z*sp.exp(b*z)-sp.exp(b*z)+1)*sp.exp(-z*(a+b)/2)/z**2)*(Al*Wi)
            + ((b*z*sp.exp(b*z)-sp.exp(b*z)+1)*sp.exp(-z*(a+b)/2)/z)*(Wi*qj)
            + ((sp.Rational(1, 2)-sp.exp(b*z))*sp.exp(-z*(a+b)/2))*(Cj*Wi)
            + (-sp.exp(-z*(a-b)/2)/2)*(Wi*Wj))
    cEpi = ((-sp.exp(-z*(a-b)/2)/z**2)*(Al*Cj) + (-sp.exp(-z*(a+b)/2)/z**2)*(Al*Wj)
            + (-sp.exp(-z*(a-b)/2)/z)*(Cj*qi) + (-sp.exp(-z*(a+b)/2)/z)*(Wj*qi)
            + (-sp.exp(-z*(a+b)/2)/2)*(Ci*Wj) + (-sp.exp(-z*(a-b)/2)/2)*(Ci*Cj))
    return cC0i + cC1i*r + cEmi*sp.exp(-z*r) + cEpi*sp.exp(z*r)


def outer_target():
    cC0o = ((a**2/8-a*b/4-3*b**2/8)*(qi*qj) + (a**3/48-a**2*b/16+a*b**2/16+7*b**3/48)*(qi*Al)
            + (-a**3/48+a**2*b/16+3*a*b**2/16+5*b**3/48)*(Al*qj)
            + (-a**4/384+a**3*b/96-a**2*b**2/64-7*a*b**3/96-17*b**4/384)*(Al*Al)
            + ((z**2*(-a**2+2*a*b-b**2)+4*z*(-a+b)-8)/(8*z**2))*(Al*Ci)
            + (-a**2/8-a*b/4-b**2/8)*(Al*Cj) + ((-z*(a+b)+2)/(2*z**2))*(Al*Wj)
            + ((z*(-a+b)-2)/(2*z))*(Ci*qj) + ((a+b)/2)*(Cj*qi) + (1/z)*(Wj*qi) + (-1)*(Ci*Cj))
    cC1o = (((-a+b)/2)*(qi*qj) + (-a**2/8+a*b/4-b**2/8)*(qi*Al) + (a**2/8-a*b/4-3*b**2/8)*(Al*qj)
            + (a**3/48-a**2*b/16+a*b**2/16+7*b**3/48)*(Al*Al) + ((z*(a-b)+2)/(2*z))*(Al*Ci)
            + ((a+b)/2)*(Al*Cj) + (1/z)*(Al*Wj) + (1)*(Ci*qj) + (-1)*(Cj*qi))
    cC2o = ((sp.Rational(1, 2))*(qi*qj) + ((a-b)/4)*(qi*Al) + ((-a+b)/4)*(Al*qj)
            + (-a**2/16+a*b/8-b**2/16)*(Al*Al) + (-sp.Rational(1, 2))*(Al*Ci)
            + (-sp.Rational(1, 2))*(Al*Cj))
    cC3o = (((a-b)/12)*(Al*Al) + (-sp.Rational(1, 6))*(qi*Al) + (sp.Rational(1, 6))*(Al*qj))
    cC4o = (-sp.Rational(1, 24))*(Al*Al)
    cEmo = ((sp.exp(z*(a-b)/2)/z**2)*(Al*Ci)
            + ((-b**2*z**2*sp.exp(b*z)/2+b*z*sp.exp(b*z)-sp.exp(b*z)+1)*sp.exp(-z*(a+b)/2)/z**2)*(Al*Wi)
            + (sp.exp(z*(a-b)/2)/z)*(Ci*qj)
            + ((b*z*sp.exp(b*z)-sp.exp(b*z)+1)*sp.exp(-z*(a+b)/2)/z)*(Wi*qj)
            + ((sp.Rational(1, 2)-sp.exp(b*z))*sp.exp(-z*(a+b)/2))*(Cj*Wi)
            + (-sp.exp(-z*(a-b)/2)/2)*(Wi*Wj) + (sp.exp(z*(a-b)/2)/2)*(Ci*Cj))
    cEpo = ((-sp.exp(-z*(a+b)/2)/z**2)*(Al*Wj) + (-sp.exp(-z*(a+b)/2)/z)*(Wj*qi)
            + (-sp.exp(-z*(a+b)/2)/2)*(Ci*Wj))
    return (cC0o + cC1o*r + cC2o*r**2 + cC3o*r**3 + cC4o*r**4
            + cEmo*sp.exp(-z*r) + cEpo*sp.exp(z*r))




def atom_basis_check():
    """The final-match `ring` feasibility: R1+R2+R3 - inner_target, with every exp rewritten to the
    half-atom basis {Ei=e^(zσi/2), Ej, El, Er=e^(zr/2)}, is a Laurent identity that simplifies to 0
    (a genuine polynomial identity), so Lean `field_simp; ring` closes the assembly's final match."""
    import sympy as _sp
    Ei, Ej, El, Er = _sp.symbols('Ei Ej El Er', positive=True)
    diff = _sp.expand(inner_conv() - inner_target())
    subs = {}
    for at in diff.atoms(_sp.exp):
        arg = _sp.expand(at.args[0])
        pi = _sp.nsimplify(arg.coeff(si) / (z / 2)); pj = _sp.nsimplify(arg.coeff(sj) / (z / 2))
        pl = _sp.nsimplify(arg.coeff(sl) / (z / 2)); pr = _sp.nsimplify(arg.coeff(r) / (z / 2))
        subs[at] = Ei**pi * Ej**pj * El**pl * Er**pr
    return _sp.simplify(_sp.expand(diff.subs(subs)))


if __name__ == '__main__':
    di = sp.simplify(inner_conv() - inner_target())
    do = sp.simplify(outer_conv() - outer_target())
    print("INNER diff =", di)
    print("OUTER diff =", do)
    assert di == 0 and do == 0, "decomposition MISMATCH"
    ab = atom_basis_check()
    print("ATOM-BASIS final-match diff =", ab)
    assert ab == 0, "atom-basis identity MISMATCH"
    print("OK: decomposition == kernel (both pieces); final match is a ring-closable atom identity.")
