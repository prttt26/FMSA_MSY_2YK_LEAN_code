"""Locate interior positive-island births in strict finite-order isotherms.

The event a_N=partial_rho a_N=0 is a thermodynamic topology bifurcation,
distinct from a fold of the nonlinear BH amplitude equations. This script
does not prove that any additional homogeneous phase is a physical phase.
"""
from __future__ import annotations

import json
from pathlib import Path

import numpy as np
from scipy.integrate import quad
from scipy.interpolate import CubicSpline
from scipy.optimize import root

from msa_finite_order_thermo_check import ScalarSeries, at_tau, isotherm_summary
from msa_maxwell_finite_k_check import audit_endpoint

RESULTS = Path(__file__).resolve().parents[1]/'results'


def render(rows,out):
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    fig,ax = plt.subplots(figsize=(8,4))
    labels = [f'{v["model"]}, N={v["order"]}' for v in rows]
    for i,v in enumerate(rows):
        birth = v['T_over_own_Tc'];triple = v['triple_support_onset']['T_over_own_Tc']
        ax.plot([triple,birth],[i,i],color='gray',linewidth=2)
    ax.scatter([v['T_over_own_Tc'] for v in rows],range(len(rows)),
               marker='o',label='Positive island: two new spinodal roots')
    ax.scatter([v['triple_support_onset']['T_over_own_Tc'] for v in rows],range(len(rows)),
               marker='s',label='Third phase supports the common tangent')
    ax.set(yticks=range(len(rows)),yticklabels=labels,xlabel=r'$T/T_{c,N}$',
           title='Distinct topology thresholds on cooling')
    ax.invert_yaxis();ax.grid(axis='x',alpha=.25);ax.legend(fontsize=8)
    fig.tight_layout()
    for suffix in ['png','svg']:fig.savefig(out/f'topology_onsets.{suffix}',dpi=180)
    plt.close(fig)


def triple_onset(model, order, rho, coeff, cs, island_T, tc, minimum_T=None):
    """A third phase first supports the old gas-liquid common tangent."""
    previous_T = island_T*.99
    floor = .35*tc if minimum_T is None else minimum_T
    for T in np.linspace(previous_T, floor, 70)[1:]:
        a = np.asarray(np.polynomial.polynomial.polyval(1/T, coeff.T), float)
        summary, _ = isotherm_summary(rho, a)
        support = [c for c in summary['coexistence_candidates'] if c['supporting_tangent']]
        if len(support)==2:
            break
        previous_T = T
    else:
        raise RuntimeError('No third supporting phase in search window')
    P = cs.antiderivative()
    excess = coeff.copy();excess[:,0] -= 1
    M = CubicSpline(rho,np.asarray(excess/rho[:,None],float),axis=0).antiderivative()
    def equations(v):
        rg, rm, rl, temperature = v
        p = [float(at_tau(P(r),1/temperature)) for r in [rg,rm,rl]]
        mu = [float(np.log(r)+at_tau(M(r),1/temperature)) for r in [rg,rm,rl]]
        return [p[1]-p[0],p[2]-p[0],mu[1]-mu[0],mu[2]-mu[0]]
    first, second = support
    seed = [first['rho_g'],(first['rho_l']+second['rho_g'])/2,second['rho_l'],(previous_T+T)/2]
    fitted = root(equations,seed,tol=1e-10)
    if not fitted.success or max(abs(np.asarray(equations(fitted.x))))>1e-8:
        raise RuntimeError('Triple common tangent solve failed')
    def independent(v):
        rg, rm, rl, temperature = v
        def a(r):
            return float(at_tau(ScalarSeries(r,model['z'],model['K']).construct(order)['a'],1/temperature))
        return np.array([quad(a,rg,rm,epsabs=2e-10,epsrel=2e-10)[0],
                         quad(a,rg,rl,epsabs=2e-10,epsrel=2e-10)[0],
                         quad(lambda r:a(r)/r,rg,rm,epsabs=2e-10,epsrel=2e-10)[0],
                         quad(lambda r:a(r)/r,rg,rl,epsabs=2e-10,epsrel=2e-10)[0]])
    direct = root(independent,fitted.x,tol=1e-9)
    if not direct.success or max(abs(independent(direct.x)))>1e-8:
        raise RuntimeError('Independent triple tangent check failed')
    rg, rm, rl, temperature = direct.x
    if not rho[0]<rg<rm<rl<rho[-1] or not 0<temperature<island_T:
        raise RuntimeError('Collapsed or out-of-window triple solution')
    pressure = np.asarray(np.polynomial.polynomial.polyval(1/temperature,P(rho).T),float)
    chemical = np.log(rho)+np.asarray(np.polynomial.polynomial.polyval(1/temperature,M(rho).T),float)
    pg = float(at_tau(P(rg),1/temperature))
    mug = float(np.log(rg)+at_tau(M(rg),1/temperature))
    gap = rho*(chemical-mug)-(pressure-pg)
    if min(gap) < -2e-8:
        raise RuntimeError('Triple tangent fails sampled global support check')
    spectra = [dict(phase=label,**audit_endpoint(float(r),model['z'],model['K'],float(temperature),order))
               for label,r in [('gas',rg),('middle',rm),('liquid',rl)]]
    return dict(T=float(temperature),T_over_own_Tc=float(temperature/tc),
                densities=[float(rg),float(rm),float(rl)],
                independent_integral_defect=float(max(abs(independent(direct.x)))),
                interpolation_correction=float(max(abs(direct.x-fitted.x))),
                minimum_sampled_tangent_gap=float(min(gap)),
                sampled_density_window=[float(rho[0]),float(rho[-1])],spectral_checks=spectra)


def locate(model, order):
    data = np.load(RESULTS/'range_multitail_thermo'/f'{model["name"]}.npz')
    rho, coeff = data['rho'], data['a'][:, :order+1]
    cs = CubicSpline(rho, np.asarray(coeff, float), axis=0)
    tc = next(r['Tc'] for r in model['critical_temperatures'] if r['order']==order)
    samples = np.linspace(.995, .35, 260)*tc
    previous = None
    for T in samples:
        a = np.asarray(np.polynomial.polynomial.polyval(1/T, coeff.T), float)
        sp = CubicSpline(rho, a).roots(extrapolate=False)
        sp = sp[(sp>rho[0]) & (sp<rho[-1])]
        if previous is not None and len(previous[1])==2 and len(sp)==4:
            upper = previous[0]
            break
        previous = (T, sp)
    else:
        raise RuntimeError(f'No 2-to-4 root event in searched range: {model["name"]}, {order}')
    def equations(v):
        r, temperature = v
        return [float(at_tau(cs(r), 1/temperature)),
                float(at_tau(cs(r, 1), 1/temperature))]
    seed = [(sp[1]+sp[2])/2, (upper+T)/2]
    fit = root(equations, seed, tol=1e-10)
    if not fit.success or max(abs(np.asarray(equations(fit.x))))>1e-7:
        raise RuntimeError('Topology onset solve failed')
    # Refine against coefficients constructed at each density, rather than the
    # density interpolator. A central difference only estimates the derivative.
    def exact_a(r, temperature):
        return np.longdouble(at_tau(ScalarSeries(r, model['z'], model['K']).construct(order)['a'],
                                    1/np.longdouble(temperature)))
    def direct_equations(v, h=2e-5):
        r, temperature = v
        value = exact_a(r, temperature)
        derivative = (exact_a(r-2*h, temperature)-8*exact_a(r-h, temperature)
                      +8*exact_a(r+h, temperature)-exact_a(r+2*h, temperature))/(12*h)
        return np.asarray([value, derivative], float)
    direct = root(direct_equations, fit.x, tol=1e-10)
    if not direct.success or max(abs(direct_equations(direct.x)))>1e-7:
        raise RuntimeError('Direct topology onset refinement failed')
    rstar, tstar = direct.x
    h = 1e-4
    curvature = float((exact_a(rstar+h,tstar)-2*exact_a(rstar,tstar)+exact_a(rstar-h,tstar))/h**2)
    after_T = tstar*.99
    after_a = np.asarray(np.polynomial.polynomial.polyval(1/after_T,coeff.T),float)
    after, _ = isotherm_summary(rho, after_a)
    before_a = np.asarray(np.polynomial.polynomial.polyval(1/(tstar*1.01),coeff.T),float)
    before, _ = isotherm_summary(rho, before_a)
    return dict(model=model['name'], z=model['z'], K=model['K'], order=order,
                rho_onset=float(rstar), T_onset=float(tstar), T_over_own_Tc=float(tstar/tc),
                density_curvature=curvature,
                direct_equation_defect=float(max(abs(direct_equations(direct.x)))),
                derivative_step_refinement_defect=float(max(abs(direct_equations(direct.x,h=1e-5)))),
                interpolation_correction=float(max(abs(direct.x-fit.x))),
                before=dict(T=float(tstar*1.01),summary=before),
                after=dict(T=float(after_T),summary=after),
                positive_island_a_after=float(exact_a(rstar, after_T)),
                triple_support_onset=triple_onset(model,order,rho,coeff,cs,tstar,tc))


def main():
    report = json.loads((RESULTS/'range_multitail_thermo'/'results.json').read_text())
    rows = []
    for name, n in [('HSY_z1.8',6), ('HSY_z1.8',12), ('HSY_z5',6),
                    ('HSY_z12',6), ('2YK_short_repulsion',6)]:
        model = next(m for m in report['models'] if m['name']==name)
        rows.append(locate(model,n))
        print({k:v for k,v in rows[-1].items() if k not in ['before','after']},flush=True)
    # Fixed-density second-order reentrance is an exact quadratic criterion for
    # prescribed coefficients; it is not a global disappearance-of-binodal claim.
    jet = ScalarSeries(.3,[1.8],[1.]).construct(2)
    roots = np.polynomial.polynomial.polyroots(np.asarray(jet['a'],float))
    quadratic = dict(model='HSY_z1.8',rho=.3,order=2,
                     a_coefficients=list(map(float,jet['a'])),tau_roots=list(map(float,roots)),
                     lower_reentrant_temperature=float(1/roots[1]),
                     a_at_tau_25=float(at_tau(jet['a'],25)),
                     first_order_a_at_tau_25=float(at_tau(jet['a'][:2],25)),
                     scope='Fixed density only; tau=25 extrapolates far beyond the Exact MSA fold')
    out = RESULTS/'phase_topology_onset';out.mkdir(parents=True,exist_ok=True)
    (out/'results.json').write_text(json.dumps(dict(
        construction='Strict compressibility-route truncations on the same scalar PY reference',
        event='a_N=0 and partial_rho a_N=0, with negative density curvature',
        limitations='Selected cases, finite density window; no universal onset or physical phase identification',
        onsets=rows,second_order_fixed_density=quadratic),indent=2)+'\n')
    render(rows,out)


if __name__ == '__main__':
    main()
