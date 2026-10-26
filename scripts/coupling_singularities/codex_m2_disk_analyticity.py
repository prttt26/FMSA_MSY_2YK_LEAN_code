"""A complete implicit-function atlas on a complex coupling disk.

Every quadtree cell intersecting the disk is certified. Shared cell edges
and corners have a certified common root, fixing the global PY branch.
Floating continuation supplies centers only; all proof bounds use Arb/acb.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
from importlib.metadata import version
import json
import math
from pathlib import Path
import time

import numpy as np
from flint import arb,acb,ctx

from codex_m2_tangency import PACKAGE,TwoTail,enclosing_endpoints,interval_record


class Polynomial:
    """Untruncated polynomial ring in the four amplitudes, with Arb coefficients."""
    def __init__(self,terms):
        self.terms=terms

    @staticmethod
    def of(value):
        return value if isinstance(value,Polynomial) else Polynomial({(0,0,0,0):arb(value)})

    def __add__(self,other):
        terms=self.terms.copy()
        for power,c in self.of(other).terms.items():
            terms[power]=terms.get(power,arb(0))+c
        return Polynomial(terms)

    __radd__=__add__

    def __neg__(self):
        return Polynomial({p:-c for p,c in self.terms.items()})

    def __sub__(self,other):
        return self+-self.of(other)

    def __rsub__(self,other):
        return self.of(other)+-self

    def __mul__(self,other):
        terms={}
        for p,c in self.terms.items():
            for q,d in self.of(other).terms.items():
                power=tuple(a+b for a,b in zip(p,q))
                terms[power]=terms.get(power,arb(0))+c*d
        return Polynomial(terms)

    __rmul__=__mul__

    def derivative(self,j):
        terms={}
        for p,c in self.terms.items():
            if p[j]:
                q=list(p);q[j]-=1
                terms[tuple(q)]=p[j]*c
        return Polynomial(terms)

    def evaluate(self,point):
        value=acb(0)
        for p,c in self.terms.items():
            term=acb(c)
            for v,n in zip(point,p):
                if n:term*=v**n
            value+=term
        return value


def prepare_polynomial(model):
    variables=[Polynomial({tuple(int(i==j) for j in range(4)):arb(1)}) for i in range(4)]
    P=model.P(variables)
    assert all(max(map(sum,p.terms))<=3 for p in P)
    model.atlas_J=[[p.derivative(j) for j in range(4)] for p in P]
    model.atlas_H=[[[p.derivative(k) for k in range(4)] for p in row] for row in model.atlas_J]
    # The quadratic part of J is unchanged by shifting the center.
    model.atlas_quadratic={p for row in model.atlas_J for q in row for p in q.terms if sum(p)==2}


def cball_record(v):
    return {'real':interval_record(v.real),'imag':interval_record(v.imag)}


def tau_box(bounds):
    xl,xh,yl,yh=bounds
    return acb(enclosing_endpoints(xl,xh),enclosing_endpoints(yl,yh))


def midpoint(bounds):
    return complex((bounds[0]+bounds[1])/2,(bounds[2]+bounds[3])/2)


def complex_newton(model,t,w,u):
    u=np.array(u,dtype=complex)
    b=np.asarray(model.forcing(w,True),complex)
    for _ in range(35):
        p,J=model.PJ(list(u),True)
        f=np.asarray(p,complex)-t*b
        du=np.linalg.solve(np.asarray(J,complex),-f)
        if max(abs(du)/(1+abs(u)))<2e-13 and max(abs(f))<1e-9:
            return u+du
        old=np.linalg.norm(f)
        for scale in (1.,.5,.25,.125,.0625):
            un=u+scale*du
            fn=np.asarray(model.P(list(un),True),complex)-t*b
            if np.linalg.norm(fn)<old:
                u=un
                break
        else:
            raise RuntimeError('Complex Newton failed')
    raise RuntimeError('Complex Newton iteration limit')


def float_predictor(model,target,w):
    u=model.seedf.astype(complex)
    if target==0:
        return u
    s,h=0.,min(1.,.2/abs(target))
    b=np.asarray(model.forcing(w,True),complex)
    while s<1.:
        hn=min(h,1.-s)
        _,J=model.PJ(list(u),True)
        v=np.linalg.solve(np.asarray(J,complex),b)
        pred=u+hn*target*v
        try:
            un=complex_newton(model,(s+hn)*target,w,pred)
            acceptable=np.linalg.norm(un-pred)<=.25*max(np.linalg.norm(un-u),1e-10)
        except (RuntimeError,np.linalg.LinAlgError):
            acceptable=False
        if not acceptable:
            h/=2
            assert h>1e-10,'Floating radial predictor stalled'
            continue
        u,s=un,s+hn
        h=min(h*1.4,.2/abs(target))
    return u


def complex_krawczyk(model,T,W,center,radii,X=None):
    point=[acb(float(z.real),float(z.imag)) for z in center]
    U=([acb(arb(float(z.real),float(radii[i])),arb(float(z.imag),float(radii[i+4])))
        for i,z in enumerate(center)] if X is None else X)
    P,Jp=model.PJ(point)
    Cf=np.linalg.inv(np.asarray([[complex(float(v.real.mid()),float(v.imag.mid()))
                                  for v in row] for row in Jp]))
    C=[[acb(float(v.real),float(v.imag)) for v in row] for row in Cf]
    # Combine polynomial coefficients before interval evaluation. J is
    # quadratic, so this is its exact Taylor expansion about point.
    # It preserves shared amplitude increments in C*J and avoids wrapping
    # from multiplying separately enclosed Jacobian entries.
    H=[[[p.evaluate(point) for p in row] for row in block] for block in model.atlas_H]
    du=[a-b for a,b in zip(U,point)]
    monomials={p:math.prod([du[k]**n for k,n in enumerate(p) if n],start=acb(1))
               for p in model.atlas_quadratic}
    E4=[[acb(0) for _ in range(4)] for _ in range(4)]
    for i in range(4):
        for j in range(4):
            value=acb(int(i==j))-sum((C[i][k]*Jp[k][j] for k in range(4)),acb(0))
            for l in range(4):
                value-=sum((C[i][k]*H[k][j][l] for k in range(4)),acb(0))*du[l]
            for p,monomial in monomials.items():
                value-=sum((C[i][k]*model.atlas_J[k][j].terms.get(p,arb(0))
                            for k in range(4)),acb(0))*monomial
            E4[i][j]=value
    E=[[None]*8 for _ in range(8)]
    for i in range(4):
        for j in range(4):
            E[i][j],E[i][j+4]=E4[i][j].real,-E4[i][j].imag
            E[i+4][j],E[i+4][j+4]=E4[i][j].imag,E4[i][j].real
    b=model.forcing(W)
    CF=[sum((C[i][j]*P[j] for j in range(4)),acb(0))-
        T*sum((C[i][j]*b[j] for j in range(4)),acb(0)) for i in range(4)]
    Y=[v.real for v in U]+[v.imag for v in U]
    y=[v.real for v in point]+[v.imag for v in point]
    cf=[v.real for v in CF]+[v.imag for v in CF]
    K=[y[i]-cf[i]+sum((E[i][j]*(Y[j]-y[j]) for j in range(8)),arb(0)) for i in range(8)]
    weights=[v.rad() for v in Y]
    q=[sum((abs(E[i][j])*weights[j]/weights[i] for j in range(8)),arb(0)) for i in range(8)]
    ok=all(a.contains_interior(v) for a,v in zip(Y,K)) and all(v<1 for v in q)
    bound=max(math.nextafter(float(v.upper()),math.inf) for v in q)
    return ok,U,bound


def proposed_radii(model,u,t,bounds,w,W):
    _,J=model.PJ(list(u),True)
    J=np.asarray(J,complex)
    v=np.linalg.solve(J,np.asarray(model.forcing(w,True),complex))
    uw=np.linalg.solve(J,t*np.array([0.,model.kf['kt'][1],0.,0.],complex))
    hx=(bounds[1]-bounds[0])/2
    hy=(bounds[3]-bounds[2])/2
    real=2.5*(abs(v.real)*hx+abs(v.imag)*hy)
    imag=2.5*(abs(v.imag)*hx+abs(v.real)*hy)
    floor=.1*(1+abs(u))*max(hx,hy)
    real=np.maximum(real,floor)+4*abs(uw.real)*float(W.rad())+1e-11*(1+abs(u.real))
    imag=np.maximum(imag,floor)+4*abs(uw.imag)*float(W.rad())+1e-11*(1+abs(u.imag))
    return np.r_[real,imag]


def children(bounds):
    xl,xh,yl,yh=bounds
    xm,ym=(xl+xh)/2,(yl+yh)/2
    return [(xl,xm,yl,ym),(xm,xh,yl,ym),(xl,xm,ym,yh),(xm,xh,ym,yh)]


def outside(bounds,R):
    xl,xh,yl,yh=bounds
    dx=xl if xl>0 else -xh if xh<0 else 0.
    dy=yl if yl>0 else -yh if yh<0 else 0.
    return arb(dx)**2+arb(dy)**2>R*R


def adjacent_pairs(cells):
    vertical,horizontal={},{}
    for i,c in enumerate(cells):
        xl,xh,yl,yh=c['bounds']
        vertical.setdefault(xl,[[],[]])[0].append((yl,yh,i))
        vertical.setdefault(xh,[[],[]])[1].append((yl,yh,i))
        horizontal.setdefault(yl,[[],[]])[0].append((xl,xh,i))
        horizontal.setdefault(yh,[[],[]])[1].append((xl,xh,i))
    pairs=set()
    for groups in (vertical,horizontal):
        for left,right in groups.values():
            for al,ah,i in left:
                for bl,bh,j in right:
                    if i!=j and max(al,bl)<=min(ah,bh):
                        pairs.add(tuple(sorted((i,j))))
    return sorted(pairs)


def common_root(model,W,a,b):
    overlap=[max(a['bounds'][0],b['bounds'][0]),min(a['bounds'][1],b['bounds'][1]),
             max(a['bounds'][2],b['bounds'][2]),min(a['bounds'][3],b['bounds'][3])]
    assert overlap[0]<=overlap[1] and overlap[2]<=overlap[3]
    t=midpoint(overlap)
    u=complex_newton(model,t,float(W.mid()),a['center_u'])
    _,J=model.PJ(list(u),True)
    uw=np.linalg.solve(np.asarray(J,complex),t*np.array([0.,model.kf['kt'][1],0.,0.],complex))
    radii=4*np.r_[abs(uw.real),abs(uw.imag)]*float(W.rad())+1e-10*(1+np.r_[abs(u.real),abs(u.imag)])
    for _ in range(10):
        ok,U,q=complex_krawczyk(model,acb(t.real,t.imag),W,u,radii)
        if ok and all(x.contains(y) and z.contains(y) for x,z,y in zip(a['U'],b['U'],U)):
            return {'tau':[t.real,t.imag],'u_box':[cball_record(v) for v in U],'contraction':q}
        radii*=2
    raise RuntimeError(f'Common-root validation failed for {a["bounds"]}, {b["bounds"]}')


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--radius',default='5.614')
    ap.add_argument('--max-depth',type=int,default=18)
    ap.add_argument('--max-cells',type=int,default=50000)
    ap.add_argument('--predictor',default=str(PACKAGE/'results/coupling_singularities/codex_m2_zero_mode_firstness.json'))
    ap.add_argument('--out',default=str(PACKAGE/'results/coupling_singularities/codex_m2_disk_analyticity.json'))
    args=ap.parse_args()
    ctx.prec=192
    start=time.monotonic()
    source=Path(args.predictor)
    old=json.loads(source.read_text())
    model=TwoTail(old['model']['eta'],*old['model']['z'])
    prepare_polynomial(model)
    W=enclosing_endpoints(*old['root_box'][5]);wm=float(W.mid())
    R=arb(args.radius)
    extent=math.nextafter(float(R.upper()),math.inf)
    pending=[([-extent,extent,-extent,extent],0,0j,model.seedf.astype(complex))]
    cells,pruned=[],[]
    attempted=0
    while pending:
        bounds,depth,parent_t,parent_u=pending.pop()
        if outside(bounds,R):
            pruned.append({'bounds':bounds,'depth':depth})
            continue
        attempted+=1
        t=midpoint(bounds)
        u=None
        try:
            _,J=model.PJ(list(parent_u),True)
            pred=parent_u+(t-parent_t)*np.linalg.solve(np.asarray(J,complex),model.forcing(wm,True))
            try:
                un=complex_newton(model,t,wm,pred)
                good=np.linalg.norm(un-pred)<=.25*max(np.linalg.norm(un-parent_u),1e-10)
            except (RuntimeError,np.linalg.LinAlgError):
                good=False
            u=un if good else float_predictor(model,t,wm)
            radii=proposed_radii(model,u,t,bounds,wm,W)
            ok,U,q=complex_krawczyk(model,tau_box(bounds),W,u,radii)
        except (RuntimeError,AssertionError,ValueError,np.linalg.LinAlgError,ZeroDivisionError):
            ok=False
        if ok:
            if bounds[0]<=0<=bounds[1] and bounds[2]<=0<=bounds[3]:
                assert all(a.contains(acb(v)) for a,v in zip(U,model.seed)), 'PY seed outside zero cell'
            cells.append({'bounds':bounds,'depth':depth,'center_u':u,'U':U,'contraction':q})
        else:
            assert depth<args.max_depth, f'Atlas refinement limit at {bounds}'
            pt,pu=(t,u) if u is not None else (parent_t,parent_u)
            pending.extend((b,depth+1,pt,pu) for b in children(bounds))
        assert len(cells)<args.max_cells,'Atlas cell limit'
        if attempted%500==0:
            print(f'  atlas: {attempted} attempted, {len(cells)} certified, {len(pending)} pending, depth {depth}',flush=True)
    print(f'All disk cells certified: {len(cells)}; checking common roots',flush=True)
    pairs=adjacent_pairs(cells)
    overlaps=[]
    for n,(i,j) in enumerate(pairs):
        record=common_root(model,W,cells[i],cells[j])
        overlaps.append({'cells':[i,j],**record})
        if (n+1)%1000==0:
            print(f'  overlaps: {n+1}/{len(pairs)}',flush=True)
    assert any(c['bounds'][0]<=0<=c['bounds'][1] and c['bounds'][2]<=0<=c['bounds'][3] for c in cells)
    cover={'initial_square':[-extent,extent,-extent,extent],
           'cells':[{'bounds':c['bounds'],'depth':c['depth'],'u_box':[cball_record(v) for v in c['U']],
                     'contraction':c['contraction']} for c in cells],
           'pruned_outside_disk':pruned,'overlaps':overlaps}
    cover_path=Path(args.out).with_suffix('.cover.json.gz')
    raw=gzip.compress(json.dumps(cover,separators=(',',':')).encode(),mtime=0)
    cover_path.write_bytes(raw)
    result={'status':'PASS_COMPLEX_DISK_ATLAS','model':model.label,'radius':args.radius,
            'w_parameter_box':interval_record(W),'cells':len(cells),'overlaps':len(overlaps),
            'pruned_cells':len(pruned),'max_depth':max(c['depth'] for c in cells),
            'worst_cell_contraction':max(c['contraction'] for c in cells),
            'tau_touch_upper':old['root_box'][4][1],
            'radius_strictly_above_touch':bool(R>enclosing_endpoints(*old['root_box'][4])),
            'claim':'For every enclosed fixed real w, the PY-seeded BH germ extends as one holomorphic regular root over an open neighborhood of the entire closed complex disk of the stated radius.',
            'gluing_argument':'Every retained quadtree cell has a unique regular holomorphic root. Each intersecting pair has a certified common root at one point of its connected intersection. Local implicit uniqueness and continuation along the common edge identify both maps there. The finite maps glue to a neighborhood of the covered closed disk, fixing the germ at the enclosed PY seed.',
            'scope':'An interval/complex-analysis certificate, not Lean; a radius lower bound, not the exact nearest singularity or an all-density theorem.',
            'cover':{'file':cover_path.name,'sha256':hashlib.sha256(raw).hexdigest()},
            'firstness_summary_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
            'source_sha256':{str(p.relative_to(PACKAGE)):hashlib.sha256(p.read_bytes()).hexdigest()
                             for p in [Path(__file__).resolve(),PACKAGE/'scripts/coupling_singularities/codex_m2_tangency.py',
                                       PACKAGE/'formalization/certificates/f5_competing_tails.py']},
            'precision_bits':ctx.prec,'dependencies':{'python_flint':version('python-flint'),'numpy':np.__version__},
            'seconds':round(time.monotonic()-start,3)}
    Path(args.out).write_text(json.dumps(result,indent=2)+'\n')
    print('PASS: holomorphic PY branch on the complete complex disk',flush=True)
    print(args.out)


if __name__=='__main__':
    main()
