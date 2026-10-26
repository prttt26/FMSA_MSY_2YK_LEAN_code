"""Exclude every nonzero real wave number on the M2 control branch.

Small k: signed moments plus rigorous Taylor bounds. Middle k: exact-point
acb enclosures plus the global first-moment Lipschitz bound. Large |k|:
integration by parts for the actual continuous piecewise Baxter kernel.
Does not compute a Taylor radius or prove an all-density parameter condition.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
from importlib.metadata import version
import json
import math
from pathlib import Path
import sys
import time

import numpy as np
from flint import arb, acb, ctx

from codex_m2_tangency import (
    PACKAGE, TwoTail, branch_link, enclosing_endpoints, interval_record, krawczyk,
)


class Kernel:
    def __init__(self, model, u):
        self.model = model
        self.z = [arb(z) for z in model.label['z']]
        self.rho, k = model.k['rho'], model.k
        d, g = u[:2], u[2:]
        gam = [1-k['cg'][i]*g[i] for i in range(2)]
        self.d = d
        self.c = [gam[i]*d[i] for i in range(2)]
        self.w = [2*arb.pi()*self.rho*g[i]*d[i]/self.z[i] for i in range(2)]
        M = -sum((d[i]*(gam[i]*k['mA'][i]+g[i]*k['mB'][i]) for i in range(2)), arb(0))
        N = sum((d[i]*(g[i]*k['nB'][i]+gam[i]*k['nA'][i]) for i in range(2)), arb(0))
        self.A = (1+M)*k['A0']-4*k['B0']*N
        self.qp = (1+M)*k['qp0']+k['A0']*N
        self.f0 = model.zero_mode(u)

    def moment(self, p, absolute=False):
        norm = abs if absolute else lambda a: a
        first = norm(self.qp) if absolute else -self.qp
        value = first/((p+1)*(p+2))+norm(self.A)/((p+1)*(p+2)*(p+3))
        for i, z in enumerate(self.z):
            E = math.factorial(p)/z**(p+1)*(1-(-z).exp()*sum(
                (z**j/math.factorial(j) for j in range(p+1)), arb(0)))
            T = sum((math.comb(p,j)*math.factorial(j)/z**(j+1)
                     for j in range(p+1)), arb(0))
            assert E > 0 and T > 0
            value += norm(self.c[i])/(p+1)+norm(self.w[i])*E+norm(self.d[i])*T
        return value

    def high_frequency_bound(self):
        Q0 = -self.qp+self.A/2+sum((c+w for c,w in zip(self.c,self.w)), arb(0))
        return self.rho*(abs(Q0)+abs(self.qp)+abs(self.A)/2+sum(
            (abs(self.w[i])*(1-(-z).exp())+abs(self.d[i]) for i,z in enumerate(self.z)), arb(0)))

    def factor_at(self, k):
        s = acb(0,k)
        assert not s.contains(0)
        ex = (-s).exp()
        phi1,phi2 = (1-s-ex)/(s*s),(1-s+s*s/2-ex)/(s*s*s)
        qh = self.qp*phi1+self.A*phi2
        delta = self.qp*(phi1+arb(1)/2)+self.A*(phi2-arb(1)/6)
        for i,z in enumerate(self.z):
            tail = ex/(s+z)+(1-ex)/s
            qh += self.w[i]/(s+z)+self.c[i]*tail
            delta += self.w[i]*(1/(s+z)-1/z)+self.c[i]*(tail-(1+1/z))
        direct,stable = 1-self.rho*qh,self.f0-self.rho*delta
        return acb(direct.real.intersection(stable.real),direct.imag.intersection(stable.imag))


def small_k(kernel, k0):
    real_gap = kernel.f0-kernel.rho*k0*k0*kernel.moment(2,True)/2
    m1, error = kernel.moment(1), k0*k0*kernel.moment(3,True)/6
    if real_gap > 0:
        return {'method':'positive_real_part','gap':interval_record(real_gap)}
    if m1-error > 0:
        return {'method':'positive_imaginary_part_over_k','moment_gap':interval_record(m1-error)}
    if m1+error < 0:
        return {'method':'negative_imaginary_part_over_k','moment_gap':interval_record(m1+error)}
    raise RuntimeError('Small-k moment exclusion unresolved')


def distance_gap(F, lipschitz_bound, interval, center):
    error = lipschitz_bound*abs(interval-arb(center))
    return abs(F)-error,error


def middle_k(kernel, k0, cap):
    pending = [(k0,cap)]
    cover = []
    L = kernel.rho*kernel.moment(1,True)
    while pending:
        lo,hi = pending.pop()
        center = (lo+hi)/2
        K = enclosing_endpoints(lo,hi)
        F = kernel.factor_at(arb(center))
        gap,error = distance_gap(F,L,K,center)
        if gap > 0:
            cover.append({'k':[lo,hi],'center':center,'factor_real':interval_record(F.real),
                          'factor_imag':interval_record(F.imag),'lipschitz_error':interval_record(error),
                          'distance_gap':interval_record(gap)})
        else:
            assert hi-lo > 1e-8, f'Middle-k enclosure unresolved at k={center}'
            pending.extend([(center,hi),(lo,center)])
    cover.sort(key=lambda s:s['k'][0])
    assert cover[0]['k'][0]==k0 and cover[-1]['k'][1]==cap
    assert all(a['k'][1]==b['k'][0] for a,b in zip(cover,cover[1:]))
    return cover


def actual_model_crosscheck():
    sys.path.insert(0,str(PACKAGE.parent.parent))
    import msa_exact_mix as actual
    count,worst = 0,0.0
    for eta in ('0.1','0.3','0.49'):
        for zs in (('1.8','12'),('2.9637','14.0167'),('0.6','0.84')):
            model = TwoTail(eta,*zs)
            rho = 6*float(eta)/np.pi
            st = actual.HCYMix([1.], [rho], [float(z) for z in zs], np.array([1.,-1.]).reshape(2,1,1))
            for ds,gs in (((0.,0.),(.2,.4)),((.02,-.03),(.7,.8)),((.3,-.6),(-.1,.6))):
                D,G = np.asarray(ds),np.asarray(gs)
                pieces = actual._pieces(st,D.reshape(2,1,1),G.reshape(2,1,1))
                kernel = Kernel(model,[arb(v) for v in ds+gs])
                for wave in (.1,.3,1.,4.,16.):
                    observed = complex(1-rho*actual.qhat(st,pieces,1j*wave)[0,0])
                    predicted = kernel.factor_at(arb(wave))
                    predicted = complex(float(predicted.real.mid()),float(predicted.imag.mid()))
                    err = abs(observed-predicted)/max(1.,abs(observed))
                    # The actual float implementation uses a degree-seven
                    # phi Taylor approximation for small arguments. At k=.3
                    # its truncation is visible at high eta; it is not used
                    # in any Arb/acb proof inequality here.
                    assert err < 1e-9,(eta,zs,ds,gs,wave,err)
                    worst = max(worst,err)
                    count += 1
    return {'status':'PASS','cases':count,'max_scaled_abs_error':worst,
            'scope':'Off-root float64 transcription comparison only; actual small-argument phi uses a degree-seven Taylor approximation. Proof inequalities use Arb/acb.',
            'actual_model_source_sha256':hashlib.sha256(Path(actual.__file__).read_bytes()).hexdigest()}


def kernel_identities():
    import sympy as sp
    t,s,z = sp.symbols('t s z',nonzero=True)
    C,W,E = sp.symbols('C W E')
    phi1,phi2 = (1-s-sp.exp(-s))/s**2,(1-s+s*s/2-sp.exp(-s))/s**3
    assert sp.simplify(sp.integrate((t-1)*sp.exp(-s*t),(t,0,1))-phi1)==0
    assert sp.simplify(sp.integrate((t-1)**2*sp.exp(-s*t)/2,(t,0,1))-phi2)==0
    for p in range(4):
        assert sp.integrate(t**p*(t-1),(t,0,1))==-sp.Rational(1,(p+1)*(p+2))
        assert sp.integrate(t**p*(t-1)**2/2,(t,0,1))==sp.Rational(1,(p+1)*(p+2)*(p+3))
        Ep = sp.factorial(p)/z**(p+1)*(1-E*sum(z**j/sp.factorial(j) for j in range(p+1)))
        Tp = sum(sp.binomial(p,j)*sp.factorial(j)/z**(j+1) for j in range(p+1))
        assert sp.cancel(Ep+E*Tp-sp.factorial(p)/z**(p+1))==0
        assert sp.cancel(C/(p+1)+W*Ep+(C+W*E)*Tp-
                         (W*sp.factorial(p)/z**(p+1)+C*(Tp+sp.Rational(1,p+1))))==0
    eta,D,G = sp.symbols('eta D G')
    rho = 6*eta/sp.pi
    A0,B0,qp0 = (2*sp.pi*(1+2*eta)/(1-eta)**2,
                 -3*sp.pi*eta/(1-eta)**2,2*sp.pi*(1+eta/2)/(1-eta)**2)
    W = 2*sp.pi*rho*G*D/z
    C = (1-2*sp.pi*rho*G*E/z)*D
    assert sp.expand(C+W*E-D)==0
    M,N = -rho*(W+(1+z)*C)/z,rho*(W+(1+z+z*z/2)*C)/z**2
    A,qp = (1+M)*A0-4*B0*N,(1+M)*qp0+A0*N
    qh0 = -qp/2+A/6+W/z+C*(1+1/z)
    assert sp.cancel(1-rho*qh0-A/(2*sp.pi))==0
    return {'status':'PASS','sympy_version':sp.__version__,
            'identities':['polynomial core Laplace blocks','core/tail moments p=0,1,2,3',
                          'kernel continuity C+W*exp(-z)=D','F0=1-rho*Qhat(0)=A/(2*pi), additive in tails']}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--predictor',default=str(PACKAGE/'results/coupling_singularities/codex_m2_zero_mode_firstness.json'))
    ap.add_argument('--out',default=str(PACKAGE/'results/coupling_singularities/codex_m2_finite_k.json'))
    args = ap.parse_args()
    ctx.prec = 192
    started = time.monotonic()
    predictor_path = Path(args.predictor)
    predictor = json.loads(predictor_path.read_text())
    label = predictor['model']
    model = TwoTail(label['eta'],*label['z'])
    root = [enclosing_endpoints(*v) for v in predictor['root_box']]
    center = np.array([float(v.mid()) for v in root])
    ok,root,_,_,root_q = krawczyk(model.augmented,center,[1.]*10,X=root)
    assert ok,'Augmented root box replay failed'
    identities = kernel_identities()
    linkage = branch_link(model,root)
    crosscheck = actual_model_crosscheck()
    k0,cap = .1,16.
    records,count,worstH = [],0,0.
    for i,slab in enumerate(linkage['chain']):
        U = [enclosing_endpoints(*v) for v in slab['u_box']]
        kernel = Kernel(model,U)
        small = small_k(kernel,arb(k0))
        H = kernel.high_frequency_bound()
        assert H < cap,('High-frequency exclusion unresolved',slab['tau'],H)
        mid = middle_k(kernel,k0,cap)
        count += len(mid)
        worstH = max(worstH,math.nextafter(float(H.upper()),math.inf))
        records.append({**slab,'small_k':small,'high_frequency_H':interval_record(H),
                        'middle_k':mid})
        if (i+1)%50==0:
            print(f'  finite k: {i+1}/{len(linkage["chain"])} tau slabs, {count} wave intervals',flush=True)

    # A known synthetic zero must defeat the same distance-gap test.
    K = enclosing_endpoints(.75,1.125)
    kc = .9375
    gap,_ = distance_gap(acb(0,arb(kc-1)),arb(1),K,kc)
    assert not gap>0,'Known zero of i*(k-1) was excluded'
    positive,_ = distance_gap(acb(1,arb(kc-1)),arb(1),K,kc)
    assert positive>0,'Nonzero control 1+i*(k-1) was unresolved'
    seed = Kernel(model,model.seed)
    assert seed.A>0 and seed.qp-seed.A/2>0
    seed_l1 = seed.rho*(seed.qp/2-seed.A/6)
    assert seed_l1<1,'Seed half-plane zero-free L1 bound unresolved'
    cover_path = Path(args.out).with_suffix('.cover.json.gz')
    cover_bytes = gzip.compress(json.dumps(records,separators=(',',':')).encode(),mtime=0)
    cover_path.write_bytes(cover_bytes)
    result = {
        'status':'PASS_FINITE_K_EXCLUSION','model':model.label,
        'claim':'F(i*k) is nonzero for every real k!=0 and every enclosed coupling 0<=tau<=tau_end, uniformly over the touching w box.',
        'root_box':[interval_record(v) for v in root], 'augmented_root_contraction':root_q,
        'tau_end':linkage['tau_end'],'tau_slabs':len(records),'wave_intervals':count,
        'small_k_max':k0,'high_frequency_min':cap,'uniform_H_upper':worstH,
        'cover':{'file':cover_path.name,'sha256':hashlib.sha256(cover_bytes).hexdigest()},
        'small_k_argument':'Re F(k)>=F0-rho*k^2*M2abs/2, or |Im F(k)/k|>=rho*(|M1|-k^2*M3abs/6)>0, with a certified sign for M1.',
        'middle_k_argument':'|F(k)-F(kc)|<=rho*M1abs*|k-kc|; every interval has a strict positive distance gap.',
        'high_frequency_argument':'Continuity at t=1 and integration by parts give |rho*Qhat(s)|<=H/|s| for Re s>=0. H<16 excludes all |s|>=16 in that half-plane.',
        'negative_k_argument':'The kernel is real, so F(-i*k)=conj(F(i*k)).',
        'negative_control_known_zero_not_excluded':True,'actual_model_float_crosscheck':crosscheck,
        'kernel_symbolic_identities':identities,
        'seed_half_plane_L1_bound':interval_record(seed_l1),
        'firstness_summary_sha256':hashlib.sha256(predictor_path.read_bytes()).hexdigest(),
        'combination':'With the separate first-zero-mode-contact certificate at the same augmented root, the first real-wave-number zero occurs at k=0, tau=tau_touch. This file alone does not prove the k=0 firstness claim.',
        'canonical_homotopy_argument':'For every compact coupling interval before contact, F(s) is analytic on Re s>0, nonzero on its imaginary boundary, and uniformly nonzero for |s|>=16 in Re s>=0. The seed L1 bound excludes seed zeros there. The argument principle keeps the number of right-half-plane zeros zero. This is an elementary complex-analysis paper argument, not Lean.',
        'scope':'One control point, not an all-density theorem, no Taylor-radius comparison, not Lean.',
        'precision_bits':ctx.prec,'dependencies':{'python_flint':version('python-flint'),'numpy':np.__version__},
        'source_sha256':{str(p.relative_to(PACKAGE)):hashlib.sha256(p.read_bytes()).hexdigest()
                         for p in [Path(__file__).resolve(),PACKAGE/'scripts/coupling_singularities/codex_m2_tangency.py',
                                   PACKAGE/'formalization/certificates/f5_competing_tails.py']},
        'seconds':round(time.monotonic()-started,3)}
    Path(args.out).write_text(json.dumps(result,indent=2)+'\n')
    print('PASS: all nonzero real wave numbers excluded on the PY-linked control branch',flush=True)
    print(args.out)


if __name__=='__main__':
    main()
