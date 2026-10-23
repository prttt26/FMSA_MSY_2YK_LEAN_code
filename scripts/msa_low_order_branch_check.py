"""Check the earliest tested normal-tail pressure-topology changes.

Extends the formal homogeneous-fluid density window to rho=1.4. This is not
an equilibrium-fluid validity claim: freezing and dense-fluid accuracy are
not checked. Very low temperatures may lie outside Taylor convergence.
"""
from __future__ import annotations

import json
from pathlib import Path

import numpy as np
from scipy.integrate import quad
from scipy.interpolate import CubicSpline
from scipy.optimize import root

from msa_finite_order_thermo_check import ScalarSeries, at_tau, isotherm_summary, PI
from msa_maxwell_finite_k_check import audit_endpoint
from msa_phase_topology_onset_check import triple_onset

RESULTS=Path(__file__).resolve().parents[1]/'results'


def exact_domain_check():
    import msa_exact_mix as exact
    rows=[]
    for T,mode in [(1.006,'fold'),(1.02,'spinodal')]:
        for sr in [.25,.4]:
            q=exact.solve_bh_mix(exact.HCYMix([1],[sr],[1.8],np.array([[[1/T]]])))
            scale=np.max(abs(ScalarSeries(.3,[1.8],[1/T]).construct(1)['J']),axis=1)
            def equations(v):
                x,r=v[:-1],v[-1]
                md=ScalarSeries(r,[1.8],[1/T]);x=np.asarray(x,np.longdouble)
                res=md.residual(x[:,None],False)[:,0]
                res[0]-=2*PI*md.K[0]/md.z[0]
                condition=(float(np.linalg.det(np.asarray(md.jacobian(x)/scale[:,None],float)))
                           if mode=='fold' else float(md.pieces(x[:,None])[0][0]/(2*PI)))
                return np.r_[np.asarray(res/scale,float),condition]
            fit=root(equations,np.r_[q.Dt.ravel(),q.Gt.ravel(),sr],tol=1e-11)
            defect=float(np.linalg.norm(equations(fit.x)))
            if defect>1e-9:raise RuntimeError('Exact domain boundary refinement')
            md=ScalarSeries(fit.x[-1],[1.8],[1/T])
            A=float(md.pieces(np.asarray(fit.x[:-1],np.longdouble)[:,None])[0][0]/(2*PI))
            rows.append(dict(T=T,event=mode,rho=float(fit.x[-1]),normalized_A=A,a=A*A,residual=defect))
    if len(set(round(r['rho'],8) for r in rows))!=4:
        raise RuntimeError('Boundary seeds converged to duplicate roots')
    for T in [1.1,1.03,1.025,1.02,1.017,1.006]:
        q=exact.solve_bh_mix(exact.HCYMix([1],[.3],[1.8],np.array([[[1/T]]])))
        rows.append(dict(T=T,event='fixed_density_state',rho=.3,
                         normalized_A=None if q is None else float(q.p['A'][0]/(2*np.pi)),
                         a=None if q is None else float(q.dbetaP_drho)))
    return rows


def negative_spectrum_precision(rows):
    import mpmath as mp
    import fmsa_first_order_exact as high
    mp.mp.dps=70
    case=next(c for c in rows if c['model']=='HSY_z1.8' and c['order']==3)
    pair=case['two_supporting_pairs'][1];end=pair['spectral_checks'][0]
    rho,T,k=end['rho'],pair['T'],end['k_min']
    st=high.State(['1'],[str(rho)],['1.8'],[[['1']]])
    seed=high.u0_of(st);J,_=high.jacobian_and_dlam(st,seed);jets=[mp.matrix(seed)]
    for degree in range(1,4):
        def residual(t):
            state=sum((v*t**j for j,v in enumerate(jets)),mp.zeros(len(seed),1))
            return mp.matrix(high.residuals(list(state),st.scaled(t)))
        jets.append(mp.lu_solve(mp.matrix(J),-mp.diff(residual,0,degree)/mp.factorial(degree)))
    def spectrum(t):
        state=sum((v*t**j for j,v in enumerate(jets)),mp.zeros(len(seed),1))
        p=high.pieces(st,[[[state[0]]]],[[[state[1]]]])
        s=mp.j*mp.mpf(str(k))
        return ((1-st.rho[0]*high.qhat(st,p,s)[0][0])*
                (1-st.rho[0]*high.qhat(st,p,-s)[0][0])).real
    value=sum(mp.diff(spectrum,0,j)/mp.factorial(j)*(1/mp.mpf(str(T)))**j for j in range(4))
    error=abs(float(value)-end['minimum_D'])
    if error>1e-8 or value>=0:raise RuntimeError('Independent negative spectrum check')
    return dict(model=case['model'],order=3,rho=rho,T=T,k=k,reference_D=float(value),
                computed_D=end['minimum_D'],absolute_error=error,digits=70)


def run_case(model,n):
    previous=np.load(RESULTS/'range_multitail_thermo'/f'{model["name"]}.npz')
    extra=np.linspace(1.251,1.4,201)
    rho=np.r_[previous['rho'],extra]
    coeff=np.r_[previous['a'][:,:n+1],np.asarray([
        ScalarSeries(r,model['z'],model['K']).construct(n)['a'] for r in extra])]
    cs=CubicSpline(rho,np.asarray(coeff,float),axis=0)
    tc=next(c['Tc'] for c in model['critical_temperatures'] if c['order']==n)
    last_T=None
    for T in tc*np.linspace(.99,.02,350):
        a=np.asarray(np.polynomial.polynomial.polyval(1/T,coeff.T),float)
        sp=CubicSpline(rho,a).roots(extrapolate=False)
        sp=sp[(sp>rho[0])&(sp<rho[-1])]
        if len(sp)==4:
            break
        last_T=T
    else:
        raise RuntimeError('No four-root example')
    def interpolated(v):
        r,t=v
        return [float(at_tau(cs(r),1/t)),float(at_tau(cs(r,1),1/t))]
    initial=root(interpolated,[(sp[1]+sp[2])/2,(T+last_T)/2],tol=1e-10)
    def direct_a(r,t):
        return np.longdouble(at_tau(ScalarSeries(r,model['z'],model['K']).construct(n)['a'],
                                    1/np.longdouble(t)))
    def direct(v,h=2e-5):
        r,t=v
        slope=(direct_a(r-2*h,t)-8*direct_a(r-h,t)+8*direct_a(r+h,t)-direct_a(r+2*h,t))/(12*h)
        return np.asarray([direct_a(r,t),slope],float)
    refined=root(direct,initial.x,tol=1e-10)
    if not refined.success or max(abs(direct(refined.x)))>1e-8:
        raise RuntimeError('Low-order onset refinement failed')
    rstar,tstar=refined.x
    T=.99*tstar
    a=np.asarray(np.polynomial.polynomial.polyval(1/T,coeff.T),float)
    summary,_=isotherm_summary(rho,a)
    spinodals=[]
    for r in summary['spinodal_roots']:
        fit=root(lambda v:[float(direct_a(v[0],T))],[r],tol=1e-10)
        if abs(direct_a(fit.x[0],T))>1e-8:raise RuntimeError('Spinodal residual')
        spinodals.append(float(fit.x[0]))
    row=dict(model=model['name'],z=model['z'],K=model['K'],order=n,
             T_onset=float(tstar),T_over_own_Tc=float(tstar/tc),rho_onset=float(rstar),
             direct_onset_defect=float(max(abs(direct(refined.x)))),
             derivative_refinement_defect=float(max(abs(direct(refined.x,h=1e-5)))),
             example=dict(T=float(T),spinodals=spinodals,
                          sampled_supporting_tangent_count=summary['supporting_tangent_count'],
                          positive_island_a=float(direct_a(rstar,T))))
    if n==3:
        # A longer cooling interval than in the moderate-order onset audit.
        triple=triple_onset(model,n,rho,coeff,cs,tstar,tc,minimum_T=.035*tc)
        row['triple_support_onset']=triple
        test_T=.99*triple['T']
        test_a=np.asarray(np.polynomial.polynomial.polyval(1/test_T,coeff.T),float)
        coexist,_=isotherm_summary(rho,test_a)
        checks=[]
        for c in coexist['coexistence_candidates']:
            if not c['supporting_tangent']:continue
            def equalities(v):
                rg,rl=v
                return [quad(lambda r:float(direct_a(r,test_T)),rg,rl,epsabs=1e-10,epsrel=1e-10)[0],
                        quad(lambda r:float(direct_a(r,test_T))/r,rg,rl,epsabs=1e-10,epsrel=1e-10)[0]]
            fit=root(equalities,[c['rho_g'],c['rho_l']],tol=1e-9)
            if not fit.success or max(abs(np.asarray(equalities(fit.x))))>1e-8:
                raise RuntimeError('Independent low-order coexistence check')
            checks.append(dict(T=float(test_T),rho_g=float(fit.x[0]),rho_l=float(fit.x[1]),
                               independent_integral_defect=float(max(abs(np.asarray(equalities(fit.x))))),
                               spectral_checks=[audit_endpoint(float(r),model['z'],model['K'],float(test_T),n)
                                                for r in fit.x]))
        if len(checks)!=2:raise RuntimeError('Expected two supporting pairs')
        row['two_supporting_pairs']=checks
    return row


def main():
    report=json.loads((RESULTS/'range_multitail_thermo'/'results.json').read_text())
    rows=[]
    for name,n in [('HSY_z1.8',2),('HSY_z5',2),('HSY_z12',2),('HSY_z20',2),
                   ('HSY_z1.8',3),('HSY_z5',3)]:
        model=next(m for m in report['models'] if m['name']==name)
        rows.append(run_case(model,n))
        print(name,n,rows[-1]['T_onset'],rows[-1]['T_over_own_Tc'],flush=True)
    out=RESULTS/'low_order_normal_tail';out.mkdir(parents=True,exist_ok=True)
    (out/'results.json').write_text(json.dumps(dict(
        reference='Scalar sigma=1 PY; strict compressibility-route coupling truncation',
        density_window=[1e-7,1.4],
        limitations='Selected low-T fluid-ansatz tests; no freezing check or convergence certificate; '
                    'no proof for every N>1 and no proof that order two excludes extra binodals',
        cases=rows),indent=2)+'\n')
    (out/'exact_domain_check.json').write_text(json.dumps(exact_domain_check(),indent=2)+'\n')
    (out/'spectral_precision.json').write_text(json.dumps(negative_spectrum_precision(rows),indent=2)+'\n')


if __name__=='__main__':main()
