"""Audit strict coupling truncations against Exact MSA on one PY reference.

The series are constructed by coefficient arithmetic and repeated solves of the
same HS Jacobian. No finite-coupling nonlinear solve constructs a Taylor jet.
Nonlinear solves are used only for the independent exact-MSA/fold comparison
and for thermodynamic coexistence. Supports scalar fluids with fixed multiple
Yukawa rates; it does not establish a theorem for arbitrary mixtures.

Run from any directory:
  python Lean_code/MSA_and_1st_Truncation/scripts/msa_finite_order_thermo_check.py --out /tmp/msa_thermo
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

import numpy as np
from scipy.integrate import quad
from scipy.interpolate import CubicSpline
from scipy.optimize import brentq, root, minimize_scalar

sys.path.insert(0, str(Path(__file__).resolve().parents[3]))
import msa_exact_mix as exact

PI = np.longdouble(str(np.pi))


def mul(a, b):
    return np.convolve(a, b)[:len(a)]


class ScalarSeries:
    """Polynomial BH residual, with the order on the last array axis."""

    def __init__(self, rho, z=(1.8,), K=(1.0,)):
        self.rho = np.longdouble(rho)
        self.z = np.asarray(z, dtype=np.longdouble)
        self.K = np.asarray(K, dtype=np.longdouble)
        self.tails = len(z)
        eta = PI * self.rho / 6
        d = 2 * PI / (1 - eta)**2
        self.A0 = d * (1 + 2 * eta)
        self.B0 = -d * np.longdouble('1.5') * eta
        self.qp0 = d * (1 + eta / 2)

    def pieces(self, x):
        D, G = x[:self.tails], x[self.tails:]
        products = np.asarray([mul(g, d) for g, d in zip(G, D)])
        W = (2 * PI * self.rho / self.z)[:, None] * products
        C = D - np.exp(-self.z)[:, None] * W
        M = -self.rho * np.sum((W + (1 + self.z)[:, None] * C)
                              / self.z[:, None], axis=0)
        Nc = self.rho * np.sum((W + (1 + self.z + self.z**2/2)[:, None] * C)
                              / self.z[:, None]**2, axis=0)
        one_M = M.copy()
        one_M[0] += 1
        A = self.A0 * one_M - 4 * self.B0 * Nc
        qp = self.qp0 * one_M + self.A0 * Nc
        return A, qp, C, W

    def qhat(self, p, s):
        A, qp, C, W = p
        if s == 0:
            f1, f2, er = -np.longdouble('.5'), np.longdouble(1)/6, 1
        else:
            em = np.exp(-s)
            f1 = (1 - s - em) / s**2
            f2 = (1 - s + s**2/2 - em) / s**3
            er = -np.expm1(-s) / s
        return f1 * qp + f2 * A + np.sum(
            W/(s + self.z)[:, None]
            + C * (np.exp(-s)/(s + self.z) + er)[:, None], axis=0)

    def residual(self, x, forcing=True):
        p = self.pieces(x)
        A, qp, C, W = p
        degree = x.shape[1] - 1
        out = np.zeros_like(x)
        for t, z in enumerate(self.z):
            F = -self.rho * self.qhat(p, z)
            F[0] += 1
            out[t] = mul(x[t], F)
            if forcing and degree >= 1:
                out[t, 1] -= 2 * PI * self.K[t] / z
            source = (A + z * qp + np.sum(
                (z**2 * self.z/(z + self.z))[:, None] * C, axis=0))/z**2
            out[self.tails + t] = 2 * PI * mul(x[self.tails + t], F) - source
        return out

    def jacobian(self, state):
        dimension = len(state)
        J = np.zeros((dimension, dimension), dtype=np.longdouble)
        for k in range(dimension):
            trial = np.zeros((dimension, 2), dtype=np.longdouble)
            trial[:, 0] = state
            trial[k, 1] = 1
            J[:, k] = self.residual(trial, forcing=False)[:, 1]
        return J

    def construct(self, order):
        x = np.zeros((2 * self.tails, order + 1), dtype=np.longdouble)
        for t, z in enumerate(self.z):
            Q0 = self.qhat(self.pieces(x[:, :1]), z)[0]
            x[self.tails+t, 0] = (self.A0 + z*self.qp0)/(2*PI*z**2*(1-self.rho*Q0))
        J = self.jacobian(x[:, 0])
        scale = np.max(np.abs(J), axis=1)
        Js = np.asarray(J / scale[:, None], dtype=float)
        inverse = np.linalg.inv(Js)
        max_defect = 0.0
        for n in range(1, order + 1):
            rn = self.residual(x[:, :n+1])[:, n]
            rhs = -rn/scale
            # Double solve with long-double iterative refinement of the small J.
            xn = np.asarray(inverse @ np.asarray(rhs, float), dtype=np.longdouble)
            for _ in range(2):
                defect = rhs - (J/scale[:, None]) @ xn
                xn += np.asarray(inverse @ np.asarray(defect, float), dtype=np.longdouble)
            x[:, n] = xn
            max_defect = max(max_defect, float(np.max(np.abs(J @ xn + rn))
                                             / max(1, np.max(np.abs(rn)))))
        A = self.pieces(x)[0] / (2*PI)
        a = mul(A, A)
        F = -self.rho * self.qhat(self.pieces(x), np.longdouble(0))
        F[0] += 1
        gate = float(np.max(np.abs(F-A)) / max(1, np.max(np.abs(A))))
        return dict(x=x, A=A, a=a, J=J,
                    condition=float(np.linalg.cond(Js)), coefficient_defect=max_defect,
                    zero_wavevector_identity_defect=gate)


def at_tau(coeff, tau):
    return np.polynomial.polynomial.polyval(np.longdouble(tau), coeff)


def isotherm_summary(rho, a):
    """All thermodynamics use the same a=d(beta p)/d rho."""
    spl = CubicSpline(rho, a)
    roots = spl.roots(extrapolate=False)
    roots = roots[(roots > rho[0]) & (roots < rho[-1])]
    P = spl.antiderivative()
    excess_mu = CubicSpline(rho, (a-1)/rho).antiderivative()
    p = lambda r: float(rho[0] + P(r)-P(rho[0]))
    mu = lambda r: float(np.log(r) + excess_mu(r)-excess_mu(rho[0]))
    candidates = []
    boundaries = np.r_[rho[0], roots, rho[-1]]
    stable = [(lo,hi) for lo,hi in zip(boundaries[:-1],boundaries[1:])
              if spl((lo+hi)/2) > 0]
    for gas_index,(gas_lo,gas_hi) in enumerate(stable):
      for liq_lo,liq_hi in stable[gas_index+1:]:
        plo, phi = max(p(gas_lo), p(liq_lo)), min(p(gas_hi), p(liq_hi))
        if phi > plo:
            def pair(pressure):
                return (brentq(lambda r:p(r)-pressure, gas_lo, gas_hi, xtol=1e-13),
                        brentq(lambda r:p(r)-pressure, liq_lo, liq_hi, xtol=1e-13))
            def difference(pressure):
                rg, rl = pair(pressure)
                return mu(rl)-mu(rg)
            margin = (phi-plo)*1e-10
            lo, hi = plo+margin, phi-margin
            if difference(lo)*difference(hi) < 0:
                pc = brentq(difference, lo, hi, xtol=1e-13)
                rg, rl = pair(pc)
                muc = mu(rg)
                tangent_gap = np.asarray([r*(mu(r)-muc)-(p(r)-pc) for r in rho])
                candidates.append(dict(rho_g=rg, rho_l=rl, beta_p=pc,
                            pressure_defect=abs(p(rl)-p(rg)),
                            chemical_potential_defect=abs(mu(rl)-mu(rg)),
                            minimum_sampled_tangent_gap=float(np.min(tangent_gap)),
                            supporting_tangent=bool(np.min(tangent_gap) >= -1e-7)))
    admissible = [c for c in candidates if c['supporting_tangent']]
    coex = admissible[0] if len(admissible) == 1 else None
    return dict(min_derivative=float(np.min(a)),
                minimum_density=float(rho[np.argmin(a)]), spinodal_roots=roots.tolist(),
                coexistence=coex, coexistence_candidates=candidates,
                supporting_tangent_count=len(admissible),
                finite=bool(np.isfinite(a).all())), np.asarray([p(r) for r in rho])


def critical_temperatures(rho, coefficients, orders):
    """Upper onset of the negative-slope interval, for these scalar models."""
    interpolator = CubicSpline(rho, np.asarray(coefficients, float), axis=0)
    rows = []
    for n in orders:
        def minimum(T):
            values = np.asarray([at_tau(c[:n+1],1/T) for c in coefficients],float)
            idx = int(np.argmin(values))
            lo,hi = rho[max(0,idx-2)],rho[min(len(rho)-1,idx+2)]
            result = minimize_scalar(lambda r:float(at_tau(interpolator(r)[:n+1],1/T)),
                                     bounds=(lo,hi),method='bounded',
                                     options={'xatol':1e-12})
            return result.fun,result.x
        tc = brentq(lambda T:minimum(T)[0],.8,1.5,xtol=2e-12)
        ac,rc = minimum(tc)
        rows.append(dict(order=n,Tc=tc,rho_c=rc,min_derivative=ac))
    return rows


def exact_comparison(z, K, rho, order=40):
    model = ScalarSeries(rho, z, K)
    jet = model.construct(order)
    st = exact.HCYMix([1.0], [rho], z, np.asarray(K)[:, None, None])
    trace = exact.trace_coupling_mix(st, lam_max=8.0)
    last_tau, last_solution = trace[-1]
    fold_x = np.r_[last_solution.Dt.ravel(), last_solution.Gt.ravel()]
    scale = np.max(np.abs(jet['J']), axis=1)
    # Refine the augmented fold with the polynomial's exact coefficient Jacobian.
    def augmented(v):
        state, tau = v[:-1], v[-1]
        r = model.residual(np.asarray(state, dtype=np.longdouble)[:, None], False)[:, 0]
        r[:len(z)] -= 2*PI*tau*model.K/model.z
        J = model.jacobian(np.asarray(state, dtype=np.longdouble))
        return np.r_[np.asarray(r/scale, float),
                     np.linalg.det(np.asarray(J/scale[:,None], float))]
    refined = root(augmented, np.r_[fold_x, last_tau], tol=1e-11)
    if np.linalg.norm(augmented(refined.x)) > 1e-8:
        raise RuntimeError(f'Could not refine reference fold at rho={rho}')
    fold_tau = float(refined.x[-1])
    rows = []
    orders = [1, 2, 3, 4, 6, 8, 12, 20, order]
    for fraction in [.5, .9, .99, 1.01, 1.10, 1.25]:
        tau = fraction*fold_tau
        sol = exact.solve_bh_mix(exact.HCYMix([1.0], [rho], z,
                    (tau*np.asarray(K))[:, None, None]), tol=1e-10)
        ae = None if sol is None else float((sol.p['A'][0]/(2*np.pi))**2)
        rows.append(dict(tau=tau, fraction_of_fold=fraction, exact_branch_exists=sol is not None,
                         exact_compressibility=ae,
                         strict={str(n):float(at_tau(jet['a'][:n+1], tau)) for n in orders},
                         square_of_truncated_factor={str(n):float(at_tau(jet['A'][:n+1], tau)**2)
                                                     for n in orders}))
        rows[-1]['exact_residual_of_truncated_state'] = {}
        for n in orders:
            state = np.asarray([at_tau(c[:n+1],tau) for c in jet['x']])
            residual = model.residual(state[:,None],False)[:,0]
            residual[:len(z)] -= 2*PI*tau*model.K/model.z
            rows[-1]['exact_residual_of_truncated_state'][str(n)] = float(
                np.linalg.norm(np.asarray(residual/scale,float)))
    return dict(rho=rho, z=list(z), K=list(K), fold_tau=fold_tau,
                augmented_fold_defect=float(np.linalg.norm(augmented(refined.x))),
                HS_jacobian_condition=jet['condition'], rows=rows)


def precision_checks():
    """Independent 70-digit jets from the existing mpmath BH transcription."""
    import mpmath as mp
    import fmsa_first_order_exact as high
    mp.mp.dps = 70
    rows = []
    for z, K, rho in [(['1.8'], ['1'], '.3'), (['1.8'], ['1'], '.7'),
                       (['1.8','4'], ['1','-.3'], '.3')]:
        st = high.State(['1'], [rho], z, [[[k]] for k in K])
        seed = high.u0_of(st)
        J, _ = high.jacobian_and_dlam(st, seed)
        J = mp.matrix(J)
        jets = [mp.matrix(seed)]
        order = 40 if rho == '.3' else 8
        for n in range(1, order+1):
            def residual(t):
                state = sum((v*t**k for k,v in enumerate(jets)), mp.zeros(len(seed), 1))
                return mp.matrix(high.residuals(list(state), st.scaled(t)))
            rn = mp.diff(residual, 0, n)/mp.factorial(n)
            jets.append(mp.lu_solve(J, -rn))
        def amplitude(t):
            state = sum((v*t**k for k,v in enumerate(jets)), mp.zeros(len(seed), 1))
            tails = len(z)
            D = [[[state[k]]] for k in range(tails)]
            G = [[[state[tails+k]]] for k in range(tails)]
            return high.pieces(st, D, G)['A'][0]/(2*mp.pi)
        ref = [mp.diff(lambda t:amplitude(t)**2, 0, n)/mp.factorial(n) for n in range(order+1)]
        model = ScalarSeries(float(rho), list(map(float,z)), list(map(float,K)))
        jet = model.construct(order)
        errors = [abs(float(ref[n])-float(jet['a'][n]))/max(1,abs(float(ref[n])))
                  for n in range(order+1)]
        # Independent first-order Fourier/factorization check.
        u0,u1 = high.first_order_u(st)
        q0 = high.qhat0_hs(st,u0)[0,0]
        q1 = high.qhat_prime0(st,u0,u1)[0,0]
        first = -2*mp.mpf(rho)*(1-mp.mpf(rho)*q0)*q1
        rows.append(dict(rho=float(rho), z=list(map(float,z)), K=list(map(float,K)), order=order,
                         max_scaled_coefficient_difference=max(errors),
                         first_order_identity_defect=abs(float(first)-float(jet['a'][1]))))
    return rows


def verify_coexistence(report):
    """Validate grid-based coexistence with independent adaptive quadrature."""
    checks = []
    selected = [('HSY',1.006,1),('HSY',1.006,2),('HSY',1.006,3),
                ('HSY',1.006,12),('HSY',1.006,40),('HSY',1.1,3),('2YK',.9,2)]
    for label,T,n in selected:
        model = next(m for m in report['models'] if m['model'] == label)
        state = next(s for s in model['isotherms'] if s['T'] == T)
        candidate = state['orders'][str(n)]['coexistence']
        if candidate is None:
            continue
        def derivative(r):
            jet = ScalarSeries(r,model['z'],model['K']).construct(n)
            return float(at_tau(jet['a'],1/T))
        def differences(pair):
            rg,rl = pair
            return np.array([quad(derivative,rg,rl,epsabs=2e-11,epsrel=2e-11)[0],
                         quad(lambda r:derivative(r)/r,rg,rl,epsabs=2e-11,epsrel=2e-11)[0]])
        seed = [candidate['rho_g'],candidate['rho_l']]
        initial = differences(seed)
        refined = root(differences,seed,tol=1e-10)
        checks.append(dict(model=label,T=T,order=n,
                           initial_quadrature_defect=float(np.max(np.abs(initial))),
                           refined_densities=refined.x.tolist(),
                           density_refinement_max=float(np.max(np.abs(refined.x-seed))),
                           refined_quadrature_defect=float(np.max(np.abs(differences(refined.x))))))
    return checks


def factor_diagnostics(report,out):
    """The truncated A is not a real factor of the strict truncated DCF."""
    for model in report['models']:
        data = np.load(out/f"{model['model']}_coefficients.npz")
        rho,A,a = data['rho'],data['A'],data['a']
        for state in model['isotherms']:
            T = state['T']
            for n,summary in state['orders'].items():
                n = int(n)
                factors = np.asarray([at_tau(c[:n+1],1/T) for c in A],float)
                derivatives = np.asarray([at_tau(c[:n+1],1/T) for c in a],float)
                inside = derivatives < 0
                summary['normalized_factor_range_inside_negative_slope'] = (
                    [float(np.min(factors[inside])),float(np.max(factors[inside]))]
                    if np.any(inside) else None)
        idx = int(np.argmin(np.abs(rho-.3)))
        model['factor_at_density_near_point3'] = dict(rho=float(rho[idx]),
            values={str(T):{str(n):float(at_tau(A[idx,:n+1],1/T))
                           for n in [1,2,3,6,12,20,40]} for T in [.8,1.006,1.03]})


def validate_result(report):
    assert max(r['max_scaled_coefficient_difference'] for r in report['precision_checks']) < 2e-12
    assert max(m['coefficient_equation_defect_max'] for m in report['models']) < 2e-12
    assert max(m['zero_wavevector_identity_defect_max'] for m in report['models']) < 2e-10
    assert max(r['augmented_fold_defect'] for r in report['fold_comparisons']) < 1e-8
    assert all(q['finite'] for m in report['models'] for s in m['isotherms'] for q in s['orders'].values())
    assert max(r['refined_quadrature_defect'] for r in report['coexistence_quadrature_checks']) < 5e-9
    assert report['binary_crossing_check']['coefficient_equation_defect_max'] < 1e-50


def binary_crossing_check():
    """Unequal-diameter binary check of finite evaluation, not a binodal scan."""
    import mpmath as mp
    import fmsa_first_order_exact as high
    mp.mp.dps = 70
    sigma,rho,z = ['1','2'],['.1','.04'],['1.8']
    K = [[['.5','.3'],['.3','.4']]]
    st = high.State(sigma,rho,z,K)
    seed = high.u0_of(st)
    J,_ = high.jacobian_and_dlam(st,seed)
    J = mp.matrix(J)
    jets = [mp.matrix(seed)]
    defects = []
    for n in range(1,7):
        def residual(t):
            state = sum((v*t**k for k,v in enumerate(jets)),mp.zeros(len(seed),1))
            return mp.matrix(high.residuals(list(state),st.scaled(t)))
        rn = mp.diff(residual,0,n)/mp.factorial(n)
        xn = mp.lu_solve(J,-rn)
        jets.append(xn)
        defects.append(float(mp.norm(J*xn+rn)))
    def derivative(t):
        state = sum((v*t**k for k,v in enumerate(jets)),mp.zeros(len(seed),1))
        D = [[[state[2*i+j] for j in range(2)] for i in range(2)]]
        G = [[[state[4+2*i+j] for j in range(2)] for i in range(2)]]
        A = high.pieces(st,D,G)['A']
        return sum(st.rho[j]*(A[j]/(2*mp.pi))**2 for j in range(2))/sum(st.rho)
    coeff = [mp.diff(derivative,0,n)/mp.factorial(n) for n in range(7)]
    external = exact.HCYMix([1,2],[.1,.04],[1.8],np.array([[[.5,.3],[.3,.4]]]))
    fold_tau,fold_state = exact.fold_coupling(external)
    if fold_tau is None:
        raise RuntimeError('Binary reference fold not located')
    rows = []
    for fraction in [.5,.9,.99,1.01,1.10,1.25]:
        tau = mp.mpf(str(fraction*fold_tau))
        sol = exact.solve_bh_mix(exact.HCYMix(external.sigma,external.rho,external.z,
                                             float(tau)*external.K),tol=1e-10)
        rows.append(dict(fraction_of_fold=fraction,tau=float(tau),
                         exact_branch_exists=sol is not None,
                         strict={str(n):float(sum(coeff[k]*tau**k for k in range(n+1)))
                                 for n in [1,2,3,6]}))
    return dict(sigma=[1,2],rho=[.1,.04],z=[1.8],K=[[[.5,.3],[.3,.4]]],
                construction='same 70-digit HS Jacobian for orders 1 through 6',
                coefficient_equation_defect_max=max(defects),fold_tau=fold_tau,rows=rows,
                limitation='fixed-composition mechanical derivative; not the full mixture stability matrix')


def render(report, out):
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    curves = np.load(out/'curves.npz')
    rho = curves['rho']
    fig,axes = plt.subplots(2,2,figsize=(10.2,7.6),constrained_layout=True)
    colors = plt.get_cmap('viridis')(np.linspace(.05,.9,6))
    selected = [1,2,3,6,12,40]
    for color,n in zip(colors,selected):
        axes[0,0].plot(rho,curves[f'HSY_T1.006_N{n}_a'],color=color,label=f'N={n}')
    # Independent real-branch curve; never connect across the fold gap.
    exact_rho,exact_a = [],[]
    for r in np.linspace(.12,.62,161):
        sol = exact.solve_bh_mix(exact.HCYMix([1.],[r],[1.8],np.array([[[1/1.006]]])),tol=1e-10)
        exact_rho.append(r)
        exact_a.append(np.nan if sol is None else sol.dbetaP_drho)
    axes[0,0].plot(exact_rho,exact_a,'k--',lw=1.5,label='Exact MSA')
    axes[0,0].axhline(0,color='.5',lw=.8)
    axes[0,0].set(xlim=(.12,.62),ylim=(-.7,.45),xlabel=r'$\rho^*$',
                  ylabel=r'$a=\partial(\beta p)/\partial\rho$',title='HSY: strict truncations, T*=1.006')
    axes[0,0].legend(ncol=2,fontsize=8)
    comparison = report['fold_comparisons'][1]
    coefficients = ScalarSeries(.3).construct(40)
    fractions = np.linspace(.7,1.25,300)
    for color,n in zip(colors,selected):
        vals = [at_tau(coefficients['a'][:n+1],f*comparison['fold_tau']) for f in fractions]
        axes[0,1].plot(fractions,vals,color=color,label=f'N={n}')
    xe,ae = [],[]
    for fraction in np.linspace(.7,.999,80):
        tau = fraction*comparison['fold_tau']
        sol = exact.solve_bh_mix(exact.HCYMix([1.],[.3],[1.8],np.array([[[tau]]])),tol=1e-10)
        xe.append(fraction); ae.append(np.nan if sol is None else sol.dbetaP_drho)
    axes[0,1].plot(xe,ae,'k--',lw=1.5)
    axes[0,1].axvline(1,color='k',ls=':',lw=1)
    axes[0,1].axhline(0,color='.5',lw=.8)
    axes[0,1].set(ylim=(-1,1),xlabel=r'$\tau/\tau_{\rm fold}$',ylabel=r'$a$',
                  title=r'HSY: finite values across the fold, $\rho^*=0.3$')
    model = report['models'][0]
    for T in [1.006,1.03,1.1]:
        state = next(s for s in model['isotherms'] if s['T'] == T)
        ns = [int(n) for n in state['orders']]
        values = [state['orders'][str(n)]['min_derivative'] for n in ns]
        axes[1,0].plot(ns,values,'o-',ms=4,label=f'T*={T}')
    axes[1,0].axhline(0,color='.5',lw=.8)
    axes[1,0].set(xlabel='Truncation order N',ylabel=r'$\min_\rho a_N$',
                  title='A loop is not guaranteed at higher order')
    axes[1,0].legend(fontsize=8)
    for color,n in zip(colors,[1,2,3,12,20,40]):
        axes[1,1].plot(rho,curves[f'HSY_T0.8_N{n}_a'],color=color,label=f'N={n}')
    axes[1,1].axhline(0,color='.5',lw=.8)
    axes[1,1].set(xlim=(.08,.72),ylim=(-2.1,1.4),xlabel=r'$\rho^*$',ylabel=r'$a_N$',
                  title='T*=0.8: extra turning points at N=20,40')
    axes[1,1].legend(ncol=3,fontsize=8)
    fig.savefig(out/'finite_order_thermo.png',dpi=180)
    fig.savefig(out/'finite_order_thermo.svg')
    plt.close(fig)
    report['plotted_exact_isotherm'] = dict(T=1.006,rho=exact_rho,a=[None if not np.isfinite(v) else v
                                                                 for v in exact_a])
    # A at each approximation's own spinodal, alongside actual pressure loops.
    factors = np.load(out/'HSY_coefficients.npz')['A']
    factor_interpolator = CubicSpline(rho,np.asarray(factors,float),axis=0)
    state = next(s for s in model['isotherms'] if s['T']==1.006)
    fig,axes = plt.subplots(1,2,figsize=(10.2,4.0),constrained_layout=True)
    for color,n in zip(colors,selected):
        An = np.asarray([at_tau(c[:n+1],1/1.006) for c in factors],float)
        axes[0].plot(rho,An,color=color,label=f'N={n}')
        sp = state['orders'][str(n)]['spinodal_roots']
        asp = [at_tau(factor_interpolator(r)[:n+1],1/1.006) for r in sp]
        axes[0].plot(sp,asp,'o',color=color,ms=4)
        axes[1].plot(rho,curves[f'HSY_T1.006_N{n}_p'],color=color)
        co = state['orders'][str(n)]['coexistence']
        if co:
            axes[1].plot([co['rho_g'],co['rho_l']],[co['beta_p']]*2,':',color=color,lw=1)
            axes[1].plot([co['rho_g'],co['rho_l']],[co['beta_p']]*2,'o',color=color,ms=3)
    axes[0].axhline(0,color='.5',lw=.8)
    axes[0].set(xlim=(.12,.5),ylim=(-.2,1.5),xlabel=r'$\rho^*$',ylabel=r'$A_N/(2\pi)$',
                title='Truncated A: dots are each strict spinodal')
    axes[0].legend(ncol=2,fontsize=8)
    axes[1].set(xlim=(.02,.65),ylim=(-.04,.16),xlabel=r'$\rho^*$',ylabel=r'$\beta p_N$',
                title='Pressure loops and coexistence tie lines')
    fig.savefig(out/'factor_and_coexistence.png',dpi=180)
    fig.savefig(out/'factor_and_coexistence.svg')
    plt.close(fig)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, default=Path('/tmp/msa_finite_order_thermo'))
    parser.add_argument('--grid', type=int, default=601)
    parser.add_argument('--max-order', type=int, default=40)
    args = parser.parse_args()
    if args.max_order != 40:
        parser.error('This specified audit uses --max-order 40.')
    args.out.mkdir(parents=True, exist_ok=True)
    report = dict(reference='Percus-Yevick for all orders and Exact MSA; sigma=1',
                  construction='same HS Jacobian; strict coefficient truncation of A(tau)^2/(2*pi)^2',
                  precision='long-double coefficient arithmetic; double solves with iterative refinement',
                  limitations='scalar fixed-rate models; no general mixture or positivity theorem',
                  max_order=args.max_order, grid=args.grid)
    print('Independent 70-digit coefficient checks...', flush=True)
    report['precision_checks'] = precision_checks()
    print(json.dumps(report['precision_checks']), flush=True)
    print('Fold crossings and convergence...', flush=True)
    report['fold_comparisons'] = [exact_comparison([1.8], [1.0], r, args.max_order)
                                  for r in [.15, .3, .65]]
    report['fold_comparisons'].append(exact_comparison([1.8,4.0], [1.0,-.3], .3, args.max_order))
    report['binary_crossing_check'] = binary_crossing_check()
    print('Computing density grid...', flush=True)
    rho = np.unique(np.r_[np.geomspace(1e-7, .02, 121), np.linspace(.02, 1.15, args.grid)])
    orders = [1,2,3,4,5,6,8,12,20,args.max_order]
    curves = []
    for label,z,K in [('HSY',[1.8],[1.0]), ('2YK',[1.8,4.0],[1.0,-.3])]:
        coefficients, factors, conditions, defects, identities = [],[],[],[],[]
        for i,r in enumerate(rho):
            jet = ScalarSeries(r,z,K).construct(args.max_order)
            coefficients.append(jet['a'])
            factors.append(jet['A'])
            conditions.append(jet['condition'])
            defects.append(jet['coefficient_defect'])
            identities.append(jet['zero_wavevector_identity_defect'])
            if i % 150 == 0:
                print(f'{label}: density {i+1}/{len(rho)}', flush=True)
        coefficients, factors = np.asarray(coefficients), np.asarray(factors)
        factor_interpolator = CubicSpline(rho,np.asarray(factors,float),axis=0)
        np.savez(args.out/f'{label}_coefficients.npz', rho=rho, a=coefficients, A=factors,
                 HS_condition=conditions)
        model = dict(model=label, z=z, K=K, HS_jacobian_condition_max=max(conditions),
                     coefficient_equation_defect_max=max(defects),
                     zero_wavevector_identity_defect_max=max(identities), isotherms=[])
        model['critical_temperatures'] = critical_temperatures(rho,coefficients,orders)
        for temperature in [.8, .9, 1.006, 1.0177, 1.03, 1.1, 1.25, 1.5]:
            state = dict(T=temperature, orders={})
            for n in orders:
                a = np.asarray([at_tau(c[:n+1], 1/temperature) for c in coefficients], float)
                summary,p = isotherm_summary(rho,a)
                square = np.asarray([at_tau(c[:n+1],1/temperature)**2 for c in factors],float)
                summary['min_square_of_truncated_factor'] = float(np.min(square))
                summary['normalized_truncated_factor_at_spinodal'] = [
                    float(at_tau(factor_interpolator(r)[:n+1],1/temperature))
                    for r in summary['spinodal_roots']]
                state['orders'][str(n)] = summary
                curves.append((label,temperature,n,a,p))
            model['isotherms'].append(state)
            print(label, temperature, [(n, round(state['orders'][str(n)]['min_derivative'],5),
                    state['orders'][str(n)]['supporting_tangent_count']) for n in orders], flush=True)
        report.setdefault('models', []).append(model)
    np.savez(args.out/'curves.npz', rho=rho,
             **{f'{label}_T{t}_N{n}_a':a for label,t,n,a,p in curves},
             **{f'{label}_T{t}_N{n}_p':p for label,t,n,a,p in curves})
    print('Independent coexistence quadrature and figures...',flush=True)
    report['coexistence_quadrature_checks'] = verify_coexistence(report)
    factor_diagnostics(report,args.out)
    render(report,args.out)
    validate_result(report)
    (args.out/'results.json').write_text(json.dumps(report, indent=2))
    print(f'Saved {args.out}/results.json', flush=True)


if __name__ == '__main__':
    main()
