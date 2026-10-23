"""Extend the finite-order audit to short-range and competing multi-tail fluids.

Uses the scalar PY/BH series engine in msa_finite_order_thermo_check. A pressure
loop is assessed independently of finite-wavevector instability. The k grid is
a numerical screen, not a positivity certificate over every wavevector.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np
from scipy.interpolate import CubicSpline
from scipy.integrate import quad
from scipy.optimize import brentq, minimize_scalar, root

from msa_finite_order_thermo_check import ScalarSeries, at_tau, mul, isotherm_summary

MODELS = [(f'HSY_z{z:g}',[z],[1.0]) for z in [1.8,3.,5.,8.,12.,20.]] + [
    ('2YK_attractive',[1.8,5.],[.7,.3]),
    ('2YK_short_repulsion',[5.,12.],[1.,-.3]),
    ('2YK_long_repulsion',[5.,.5],[1.,-.05]),
    ('3YK_competing',[1.8,4.,8.],[1.,-.35,.15])]
ORDERS = [1,2,3,4,6,8,12,20,40]
RATIOS = [.8,.9,.97,1.05]
WAVES = np.unique(np.r_[0.,np.linspace(.025,8,240),np.linspace(8,30,100)])


def spectral_coefficients(model, jet, waves=WAVES):
    p = model.pieces(jet['x'])
    out = []
    defect = 0.0
    for k in waves:
        F = -model.rho*model.qhat(p,np.clongdouble(1j*k))
        F[0] += 1
        squared = mul(F,np.conjugate(F))
        defect = max(defect,float(np.max(np.abs(squared.imag))/max(1,np.max(np.abs(squared)))))
        out.append(squared.real)
    return np.asarray(out),defect


def scalar_critical_temperatures(rho, coefficients):
    cs = CubicSpline(rho,np.asarray(coefficients,float),axis=0)
    def first_critical(r):
        c = cs(r)
        return -c[1]/c[0]
    ratios = -coefficients[:,1]/coefficients[:,0]
    idx = int(np.argmax(ratios))
    optimum = minimize_scalar(lambda r:-first_critical(r),
             bounds=(rho[max(0,idx-2)],rho[min(len(rho)-1,idx+2)]),method='bounded',
             options={'xatol':1e-12})
    tc1,rc1 = -optimum.fun,optimum.x
    if tc1 <= 0:
        raise RuntimeError('No first-order k=0 critical scale for this model')
    rows = []
    for n in ORDERS:
        def minimum(T):
            values = np.asarray(np.polynomial.polynomial.polyval(1/T,coefficients[:,:n+1].T),float)
            idx = int(np.argmin(values))
            result = minimize_scalar(lambda r:float(at_tau(cs(r)[:n+1],1/T)),
                  bounds=(rho[max(0,idx-2)],rho[min(len(rho)-1,idx+2)]),
                  method='bounded',options={'xatol':1e-11})
            return result.fun,result.x
        # The upper onset when cooling; lower reentrant roots are not conflated.
        samples = tc1*np.geomspace(1.5,.25,81)
        mins = [minimum(T)[0] for T in samples]
        crossing = next((i for i in range(len(samples)-1) if mins[i]>=0 and mins[i+1]<0),None)
        if crossing is None:
            rows.append(dict(order=n,Tc=None,rho_c=None))
        else:
            tc = brentq(lambda T:minimum(T)[0],samples[crossing+1],samples[crossing],xtol=1e-11)
            rows.append(dict(order=n,Tc=tc,rho_c=minimum(tc)[1],Tc_over_Tc1=tc/tc1))
    return tc1,rc1,rows


def first_positive_root(c):
    roots = np.polynomial.polynomial.polyroots(np.asarray(c,float))
    accepted = []
    for r in roots:
        if r.real>0 and abs(r.imag)<1e-7*max(1,abs(r.real)):
            s = float(r.real)
            residual = abs(float(at_tau(c,s)))
            scale = max(1,float(sum(abs(v)*s**n for n,v in enumerate(c))))
            if residual/scale < 2e-8:
                accepted.append(s)
    accepted.sort()
    for i,s in enumerate(accepted):
        trial = (s+accepted[i+1])/2 if i+1<len(accepted) else s*1.01
        if at_tau(c,trial)<0:
            return s
    return None


def stability_screen(z,K,tc1,rho):
    # Normalize the coupling coefficients before polynomial root calculations.
    model = ScalarSeries(rho,z,np.asarray(K)/tc1)
    jet = model.construct(12)
    coefficients,defect = spectral_coefficients(model,jet)
    states = []
    for n in [1,2,3,6,12]:
        roots = [first_positive_root(c[:n+1]) for c in coefficients]
        temps = np.asarray([tc1/r if r is not None else 0. for r in roots])
        idx = int(np.argmax(temps))
        states.append(dict(order=n,T_instability=float(temps[idx]),k_instability=float(WAVES[idx]),
                           T_k0=float(temps[0]),finite_k_preempts_k0=bool(idx!=0 and temps[idx]>temps[0]*(1+1e-5))))
    return dict(rho=rho,orders=states,spectral_imaginary_defect=defect),coefficients


def endpoint_screen(z,K,T,n,candidates):
    checks = []
    for candidate in candidates:
        ends = []
        for label,r in [('gas',candidate['rho_g']),('liquid',candidate['rho_l'])]:
            model = ScalarSeries(r,z,K)
            jet = model.construct(n)
            coeff,defect = spectral_coefficients(model,jet)
            S = np.asarray([at_tau(c,1/T) for c in coeff],float)
            idx = int(np.argmin(S))
            ends.append(dict(endpoint=label,rho=r,k0=float(S[0]),
                             min_sampled_inverse_structure_factor=float(S[idx]),
                             k_min=float(WAVES[idx]),
                             finite_k_unstable=bool(idx!=0 and S[idx]<-1e-8)))
        checks.append(dict(rho_g=candidate['rho_g'],rho_l=candidate['rho_l'],endpoints=ends))
    return checks


def precision_checks():
    import mpmath as mp
    import fmsa_first_order_exact as high
    mp.mp.dps = 70
    rows = []
    for z,K,rho,order in [(['12'],['1'],'.5',40),(['20'],['1'],'.54',40),
                          (['5','.5'],['1','-.05'],'.4',40),
                          (['1.8','4','8'],['1','-.35','.15'],'.3',16)]:
        st = high.State(['1'],[rho],z,[[[k]] for k in K])
        seed = high.u0_of(st)
        J,_ = high.jacobian_and_dlam(st,seed)
        J = mp.matrix(J)
        jets = [mp.matrix(seed)]
        for n in range(1,order+1):
            def residual(t):
                state = sum((v*t**k for k,v in enumerate(jets)),mp.zeros(len(seed),1))
                return mp.matrix(high.residuals(list(state),st.scaled(t)))
            rn = mp.diff(residual,0,n)/mp.factorial(n)
            jets.append(mp.lu_solve(J,-rn))
        def pressure_derivative(t):
            state = sum((v*t**k for k,v in enumerate(jets)),mp.zeros(len(seed),1))
            D = [[[state[k]]] for k in range(len(z))]
            G = [[[state[len(z)+k]]] for k in range(len(z))]
            return (high.pieces(st,D,G)['A'][0]/(2*mp.pi))**2
        reference = [mp.diff(pressure_derivative,0,n)/mp.factorial(n) for n in range(order+1)]
        jet = ScalarSeries(float(rho),list(map(float,z)),list(map(float,K))).construct(order)
        errors = [abs(float(reference[n])-float(jet['a'][n]))/max(1,abs(float(reference[n])))
                  for n in range(order+1)]
        relative = [abs((mp.mpf(str(jet['a'][n]))-reference[n])/reference[n])
                    for n in range(order+1) if abs(reference[n])>mp.mpf('1e-100')]
        rows.append(dict(z=list(map(float,z)),K=list(map(float,K)),rho=float(rho),order=order,
                         maximum_scaled_coefficient_error=max(errors),
                         maximum_relative_coefficient_error=float(max(relative))))
        print(rows[-1],flush=True)
    return rows


def own_critical_comparison(model,rho,coefficients):
    """Distinguish a shifted critical temperature from loss of phase topology."""
    rows = []
    for n in [1,2,3,6,12,40]:
        critical = next(r for r in model['critical_temperatures'] if r['order']==n)
        if critical['Tc'] is None:continue
        T = .8*critical['Tc']
        values = np.asarray(np.polynomial.polynomial.polyval(1/T,coefficients[:,:n+1].T),float)
        summary,_ = isotherm_summary(rho,values)
        candidates=[c for c in summary['coexistence_candidates'] if c['supporting_tangent']]
        summary['coexistence_endpoint_spectral_screen']=endpoint_screen(
            model['z'],model['K'],T,n,candidates)
        rows.append(dict(order=n,T=T,T_over_own_Tc=.8,summary=summary))
    return rows


def spectral_precision_check():
    import mpmath as mp
    import fmsa_first_order_exact as high
    mp.mp.dps = 70
    st = high.State(['1'],['.3'],['5','.5'],[[['1']],[['-.05']]])
    seed = high.u0_of(st); J,_ = high.jacobian_and_dlam(st,seed);J=mp.matrix(J)
    jets = [mp.matrix(seed)]
    for n in range(1,7):
        def residual(t):
            state=sum((v*t**k for k,v in enumerate(jets)),mp.zeros(len(seed),1))
            return mp.matrix(high.residuals(list(state),st.scaled(t)))
        jets.append(mp.lu_solve(J,-mp.diff(residual,0,n)/mp.factorial(n)))
    def inverse_structure(t,k):
        state=sum((v*t**n for n,v in enumerate(jets)),mp.zeros(len(seed),1))
        D=[[[state[i]]] for i in range(2)];G=[[[state[2+i]]] for i in range(2)]
        p=high.pieces(st,D,G)
        s=mp.j*k
        return ((1-st.rho[0]*high.qhat(st,p,s)[0][0])*
                (1-st.rho[0]*high.qhat(st,p,-s)[0][0])).real
    model=ScalarSeries(.3,[5,.5],[1,-.05]);jet=model.construct(6)
    errors=[];states=[]
    for k in [0,1,6.7]:
        ref=[mp.diff(lambda t:inverse_structure(t,mp.mpf(str(k))),0,n)/mp.factorial(n)
             for n in range(7)]
        comp,_=spectral_coefficients(model,jet,np.asarray([k]))
        errors.extend(abs(float(ref[n])-float(comp[0,n]))/max(1,abs(float(ref[n]))) for n in range(7))
        states.append(dict(k=k,strict_at_T_point2={str(n):float(sum(ref[i]*mp.mpf(5)**i for i in range(n+1)))
                                                 for n in [1,2,3,6]}))
    return dict(kind='spectral',rho=.3,z=[5,.5],K=[1,-.05],order=6,
                maximum_scaled_coefficient_error=max(errors),states=states)


def verify_extended_coexistence(report):
    selected=[('HSY_z12',2),('HSY_z12',6),('HSY_z20',2),
              ('2YK_attractive',2),('3YK_competing',3),('2YK_long_repulsion',1)]
    checks=[]
    for name,n in selected:
        model=next(m for m in report['models'] if m['name']==name)
        state=next(s for s in model['own_critical_comparison'] if s['order']==n)
        T=state['T']
        for candidate in state['summary']['coexistence_candidates']:
            if not candidate['supporting_tangent']:continue
            def derivative(r):
                return float(at_tau(ScalarSeries(r,model['z'],model['K']).construct(n)['a'],1/T))
            def differences(pair):
                rg,rl=pair
                return np.asarray([quad(derivative,rg,rl,epsabs=2e-10,epsrel=2e-10)[0],
                    quad(lambda r:derivative(r)/r,rg,rl,epsabs=2e-10,epsrel=2e-10)[0]])
            seed=np.asarray([candidate['rho_g'],candidate['rho_l']])
            refined=root(differences,seed,tol=1e-10)
            checks.append(dict(model=name,order=n,T=T,initial_densities=seed.tolist(),
                               refined_densities=refined.x.tolist(),
                               density_correction=float(np.max(np.abs(refined.x-seed))),
                               independent_integral_defect=float(np.max(np.abs(differences(refined.x))))))
    return checks


def render(report,out):
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    fig,axes = plt.subplots(1,2,figsize=(11,4.4),constrained_layout=True)
    for model in report['models'][:6]:
        rows = model['critical_temperatures']
        flags={(f['model'],f['order']) for f in report.get('quality_flags',[])}
        axes[0].plot([r['order'] for r in rows],[np.nan if (model['name'],r['order']) in flags
                                               else r['Tc_over_Tc1'] for r in rows],
                     'o-',ms=3,label=f"z={model['z'][0]:g}")
    axes[0].set(xlabel='Order N',ylabel=r'$T_{c,N}/T_{c,1}$',
                title='HSY: the pressure-loop onset depends on range')
    axes[0].legend(ncol=2,fontsize=8)
    counts = [[len(m['isotherms'][0]['orders'][str(n)]['spinodal_roots'])//2 for n in ORDERS]
              for m in report['models']]
    im = axes[1].imshow(counts,aspect='auto',vmin=0,vmax=3,cmap='viridis')
    axes[1].set(xticks=range(len(ORDERS)),xticklabels=ORDERS,
                yticks=range(len(MODELS)),yticklabels=[m[0] for m in MODELS],
                xlabel='Order N',title=r'Negative-slope intervals at $T=0.8T_{c,1}$')
    for i,row in enumerate(counts):
        for j,v in enumerate(row):axes[1].text(j,i,str(v),ha='center',va='center',color='white')
    fig.savefig(out/'range_and_multitail.png',dpi=180)
    fig.savefig(out/'range_and_multitail.svg')
    plt.close(fig)
    salr = next(m for m in report['models'] if m['name']=='2YK_long_repulsion')
    density = .3
    screen = next(s for s in salr['stability_screens'] if s['rho']==density)
    first = screen['orders'][0]
    T = (first['T_instability']+first['T_k0'])/2
    model = ScalarSeries(density,salr['z'],salr['K'])
    coeff,_ = spectral_coefficients(model,model.construct(12))
    fig,ax = plt.subplots(figsize=(6.2,4.2),constrained_layout=True)
    for n in [1,2,3,6,12]:
        vals = [at_tau(c[:n+1],1/T) for c in coeff]
        ax.plot(WAVES,vals,label=f'N={n}')
    ax.axhline(0,color='.5',lw=.8)
    ax.set(xlim=(0,8),ylim=(-1,4),xlabel=r'$k\sigma$',ylabel=r'$1-\rho\widehat c_N(k)$',
           title=f'Long-range repulsion: rho*={density}, T*={T:.4f}')
    ax.legend(fontsize=8)
    fig.savefig(out/'finite_wavevector_screen.png',dpi=180)
    fig.savefig(out/'finite_wavevector_screen.svg')
    plt.close(fig)
    report['plotted_spectral_state'] = dict(model='2YK_long_repulsion',rho=density,T=T)
    fig,axes=plt.subplots(1,2,figsize=(11,4.4),constrained_layout=True)
    for ax,field,title in [(axes[0],'spinodal_roots','Negative-slope intervals'),
                           (axes[1],'supporting_tangent_count','Common-tangent candidates')]:
        counts=[]
        for model in report['models']:
            values=[]
            for state in model['own_critical_comparison']:
                value=state['summary'][field]
                value=len(value)//2 if isinstance(value,list) else value
                values.append(np.nan if (model['name'],state['order']) in flags else value)
            counts.append(values)
        im=ax.imshow(np.ma.masked_invalid(counts),aspect='auto',vmin=0,vmax=3,cmap='viridis')
        ax.set(xticks=range(6),xticklabels=[1,2,3,6,12,40],yticks=range(len(MODELS)),
               yticklabels=[m[0] for m in MODELS],xlabel='Order N',title=title+' at 0.8 own Tc')
        for i,row in enumerate(counts):
            for j,v in enumerate(row):ax.text(j,i,'?' if np.isnan(v) else str(int(v)),
                                              ha='center',va='center',color='white' if np.isfinite(v) else 'black')
    fig.savefig(out/'own_critical_phase_topology.png',dpi=180)
    fig.savefig(out/'own_critical_phase_topology.svg')
    plt.close(fig)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out',type=Path,default=Path('/tmp/msa_range_multitail'))
    parser.add_argument('--grid',type=int,default=801)
    parser.add_argument('--precision-only',action='store_true')
    parser.add_argument('--refine',action='store_true',help='Only z=12, z=20 and long-range repulsion.')
    args = parser.parse_args()
    args.out.mkdir(parents=True,exist_ok=True)
    if args.precision_only:
        checks = precision_checks()
        checks.append(spectral_precision_check())
        (args.out/'precision.json').write_text(json.dumps(checks,indent=2))
        assert max(r['maximum_scaled_coefficient_error'] for r in checks)<2e-12
        assert max(r.get('maximum_relative_coefficient_error',0) for r in checks)<2e-12
        return
    rho = np.unique(np.r_[np.geomspace(1e-7,.02,121),np.linspace(.02,1.25,args.grid)])
    report = dict(reference='PY, scalar fixed-rate multi-Yukawa',max_order=40,
                  sampled_orders=ORDERS,temperature_ratios=RATIOS,rho_min=float(rho[0]),
                  rho_max=float(rho[-1]),rho_points=len(rho),linear_grid=args.grid,
                  wavevector_screen=dict(min=0,max=30,points=len(WAVES)),models=[])
    report['quality_flags']=[dict(model='HSY_z20',order=40,
        issue='critical temperature and own-critical phase topology unresolved at this floating/interpolation accuracy; excluded from quantitative figure')]
    selected_models=([m for m in MODELS if m[0] in ['HSY_z12','HSY_z20','2YK_long_repulsion']]
                     if args.refine else MODELS)
    for name,z,K in selected_models:
        coefficients,factors,conditions,defects,identity = [],[],[],[],[]
        for r in rho:
            jet = ScalarSeries(r,z,K).construct(40)
            coefficients.append(jet['a']);factors.append(jet['A']);conditions.append(jet['condition'])
            defects.append(jet['coefficient_defect']);identity.append(jet['zero_wavevector_identity_defect'])
        coefficients,factors = np.asarray(coefficients),np.asarray(factors)
        tc1,rc1,critical = scalar_critical_temperatures(rho,coefficients)
        model = dict(name=name,z=z,K=K,Tc1=tc1,rho_c1=rc1,critical_temperatures=critical,
                     HS_condition_max=max(conditions),coefficient_defect_max=max(defects),
                     zero_wavevector_identity_defect_max=max(identity),isotherms=[])
        curves = {}
        factor_cs = CubicSpline(rho,np.asarray(factors,float),axis=0)
        for ratio in RATIOS:
            T = ratio*tc1
            state = dict(T=T,T_over_Tc1=ratio,orders={})
            for n in ORDERS:
                a = np.asarray([at_tau(c[:n+1],1/T) for c in coefficients],float)
                summary,p = isotherm_summary(rho,a)
                summary['normalized_factor_at_spinodal'] = [float(at_tau(factor_cs(r)[:n+1],1/T))
                                                           for r in summary['spinodal_roots']]
                if name=='2YK_long_repulsion' and n in [1,2,3,6,12,40]:
                    candidates = [c for c in summary['coexistence_candidates'] if c['supporting_tangent']]
                    summary['coexistence_endpoint_spectral_screen'] = endpoint_screen(z,K,T,n,candidates)
                state['orders'][str(n)] = summary
                curves[f'R{ratio}_N{n}_a'] = a
                curves[f'R{ratio}_N{n}_p'] = p
            model['isotherms'].append(state)
        model['stability_screens'] = [stability_screen(z,K,tc1,r)[0] for r in [.15,.3,.6]]
        model['own_critical_comparison'] = own_critical_comparison(model,rho,coefficients)
        report['models'].append(model)
        np.savez_compressed(args.out/f'{name}.npz',rho=rho,a=coefficients,A=factors,**curves)
        (args.out/'results.json').write_text(json.dumps(report,indent=2))
        print(name,'Tc1',round(tc1,7),'Tc2/Tc1',round(critical[1]['Tc_over_Tc1'],5),
              'roots at .8Tc1',[(n,len(model['isotherms'][0]['orders'][str(n)]['spinodal_roots']))
                                for n in [1,2,3,12,20,40]],flush=True)
    assert max(m['coefficient_defect_max'] for m in report['models'])<2e-12
    assert max(m['zero_wavevector_identity_defect_max'] for m in report['models'])<2e-10
    assert all(q['finite'] for m in report['models'] for s in m['isotherms'] for q in s['orders'].values())
    if not args.refine:
        report['coexistence_quadrature_checks']=verify_extended_coexistence(report)
        assert max(q['independent_integral_defect'] for q in report['coexistence_quadrature_checks'])<1e-8
        render(report,args.out)
    (args.out/'results.json').write_text(json.dumps(report,indent=2))
    print('Saved',args.out,flush=True)


if __name__=='__main__':main()
