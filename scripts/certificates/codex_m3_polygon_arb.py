"""External M3 polynomial monodromy witness generator; independent replay required.
All acceptance uses Arb enclosures and exact Fraction comparisons.
Sparse polynomial residual/Jacobian are derived from literal BH expressions.
"""
import gzip,hashlib,json,sys,time
from fractions import Fraction as Q
from functools import lru_cache
from pathlib import Path
import sympy as sp
import flint
from flint import arb,acb,acb_mat,ctx,fmpq
if not __debug__:raise RuntimeError('Assertions must remain enabled.')
ROOT=Path(__file__).resolve().parents[2]
# Freeze provenance before importing/evaluating the parameter model.
_prior_path=ROOT/'results/certificates/codex_first_loss_arb_audit.json'
_prior=json.loads(_prior_path.read_text())
assert _prior['status']=='PASS_EXTERNAL_FIRST_LOSS_AUDIT' and len(_prior['inputs_sha256'])==25
INPUT_PINS=dict(_prior['inputs_sha256'])
for _p in (_prior_path,Path(__file__),ROOT.parent/'MSA_and_1st_Truncation/formalization/certificates/f5_competing_tails.py'):
 INPUT_PINS[str(_p.relative_to(ROOT.parent))]=hashlib.sha256(_p.read_bytes()).hexdigest()
for _p,_h in INPUT_PINS.items():assert hashlib.sha256((ROOT.parent/_p).read_bytes()).hexdigest()==_h,_p
sys.path.insert(0,str(ROOT/'scripts/two_tail'))
from two_tail_m3_arb_recheck import symbolic
ctx.prec=384
BITS=128
GRID_BITS=40
START=time.monotonic()
def digest(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def pt(q):
 q=Q(q);return arb(fmpq(q.numerator,q.denominator))
def exact(a):
 assert a.is_exact() and a.is_finite();m,e=map(int,a.man_exp());return Q(m)*Q(2)**e
def bounds(a):return exact(a.lower()),exact(a.upper())
def quant(q,bits=BITS):
 q=Q(q);return Q((q*2**bits).numerator//(q*2**bits).denominator,2**bits)
def grid_floor(v):return quant(v,GRID_BITS)
def cpoint(v):return acb(pt(v[0]),pt(v[1]))
def ctuple(a):return quant(exact(a.real.mid())),quant(exact(a.imag.mid()))
def cp(a):return cpoint(ctuple(a))
def realball(lo,hi):
 assert lo<=hi
 c,r=pt((lo+hi)/2),pt((hi-lo)/2)
 a=arb(c,r);l,h=bounds(a);assert l<=lo<=hi<=h
 return a
def cb(B):return acb(realball(*B[0]),realball(*B[1]))
def rect(y,r):
 a,b=ctuple(y);return ((a-r,a+r),(b-r,b+r))
def zero_rect():return ((Q(0),Q(0)),(Q(0),Q(0)))
def point_rect(v):return ((v[0],v[0]),(v[1],v[1]))
def contains(outer,inner,strict=False):
 return all((o[0]<i[0]<=i[1]<o[1]) if strict else (o[0]<=i[0]<=i[1]<=o[1]) for o,i in zip(outer,inner))
def enclosed(a,X,margin=Q(1,10**6)):
 for B,b in zip(X,(a.real,a.imag)):
  lo,hi=bounds(b);pad=(B[1]-B[0])*margin
  if not(B[0]+pad<lo<=hi<B[1]-pad):return False
 return True
def magnitude(a):return exact(a.abs_upper())
def maxdist(a,b):return max(abs(q-r) for q,r in zip(ctuple(a),ctuple(b)))
def scale(a):return 1+max(map(abs,ctuple(a)))
@lru_cache(None)
def ev(e):
 if e.is_Rational:return pt(Q(int(e.p),int(e.q)))
 if e==sp.pi:return arb.pi()
 if e.func==sp.exp:return ev(e.args[0]).exp()
 if e.is_Add:return sum(map(ev,e.args),arb(0))
 if e.is_Mul:
  v=arb(1)
  for a in e.args:v*=ev(a)
  return v
 if e.is_Pow and e.exp.is_Integer:return ev(e.base)**int(e.exp)
 raise ValueError(('unsupported exact coefficient',e))
class Poly:
 def __init__(self,e,V):
  assert not e.atoms(sp.Float)
  self.terms=[(m,acb(ev(c))) for m,c in sp.Poly(e,*V).terms()]
 def __call__(self,x):
  powers=[[acb(1),v,v*v,v*v*v] for v in x]
  out=acb(0)
  for m,c in self.terms:
   v=c
   for j,p in enumerate(m):
    if p:v*=powers[j][p]
   out+=v
  return out
ETA=sp.Rational(49,100);RATES=[sp.Integer(7),sp.Integer(14)];WEIGHT=sp.Rational(-419,384)
V,R,J,A=symbolic(ETA,RATES,WEIGHT)
P=[Poly(r,V) for r in R];JP=[[Poly(j,V[:4]) for j in row] for row in J]
def F(y,t):return [p([*y,t]) for p in P]
def Jac(y):return [[p(y) for p in row] for row in JP]
rho=6*ETA/sp.pi;vac=1-ETA
qp=2*sp.pi/vac*(1+sp.pi*rho/(4*vac));AA=2*sp.pi/vac*(1+sp.pi*rho/(2*vac))
GS=[]
for z in RATES:
 ph1=(1-z-sp.exp(-z))/z**2;ph2=(1-z+z*z/2-sp.exp(-z))/z**3
 GS.append((AA+z*qp)/(2*sp.pi*z*z*(1-rho*(ph1*qp+ph2*AA))))
seed_symbolic=[sp.Integer(0),sp.Integer(0),*GS]
assert all(sp.cancel(r.subs(dict(zip(V,[*seed_symbolic,sp.Integer(0)]))))==0 for r in R)
seedballs=[acb(ev(g)) for g in seed_symbolic]
seedbox=[(bounds(g.real),bounds(g.imag)) for g in seedballs]
seed=[cp(g) for g in seedballs]
def newton(y,t):
 y=list(y)
 for iteration in range(16):
  f=F(y,t)
  if all(magnitude(v)<Q(1,2**100) for v in f):return y
  try:c=acb_mat(Jac(y)).inv()
  except (ValueError,ZeroDivisionError):return None
  if not all(c[i,j].is_finite() for i in range(4) for j in range(4)):return None
  step=[sum((c[i,j]*f[j] for j in range(4)),acb(0)) for i in range(4)]
  y=[cp(a-b) for a,b in zip(y,step)]
 return None
ATTEMPTS=0

def certify(y,T,radii):
 global ATTEMPTS
 ATTEMPTS+=1
 X=[rect(a,r) for a,r in zip(y,radii)]
 xb=list(map(cb,X));tb=cb(T)
 try:ci=acb_mat(Jac(y)).inv()
 except (ValueError,ZeroDivisionError):return False,None,None,None,None
 if not all(ci[i,j].is_finite() for i in range(4) for j in range(4)):return False,None,None,None,None
 C=[[cp(ci[i,j]) for j in range(4)] for i in range(4)]
 fv=F(y,tb);jj=Jac(xb)
 E=[[acb(int(i==j))-sum((C[i][k]*jj[k][j] for k in range(4)),acb(0)) for j in range(4)] for i in range(4)]
 qi=[sum((abs(E[i][j])*pt(radii[j])/pt(radii[i]) for j in range(4)),arb(0)) for i in range(4)]
 q=max(exact(a.upper()) for a in qi)
 dx=[a-b for a,b in zip(xb,y)]
 K=[y[i]-sum((C[i][j]*fv[j] for j in range(4)),acb(0))+sum((E[i][j]*dx[j] for j in range(4)),acb(0)) for i in range(4)]
 ok=q<Q(3,4) and all(enclosed(a,x) for a,x in zip(K,X))
 witness=dict(center=[list(map(str,ctuple(a))) for a in y],preconditioner=[[list(map(str,ctuple(a))) for a in row] for row in C],X=[[[str(v) for v in I] for I in B] for B in X],weights=list(map(str,radii)),q_bound='3/4')
 return ok,X,K,q,witness

VERT=[(Q(-333,16),Q(5185,64)),(Q(-329,16),Q(5185,64)),(Q(-329,16),Q(5201,64)),(Q(-333,16),Q(5201,64))]
assert all(x*x+y*y<84**2 for x,y in VERT)
PATH=[(Q(0),Q(0)),*VERT,VERT[0]]
# Every rectangle of every affine path slab is inside the same radius84.
def path_rect(a,b):return tuple((min(x,y),max(x,y)) for x,y in zip(a,b))
def at(a,b,s):return tuple(x+(y-x)*s for x,y in zip(a,b))
def dist_rect(B,y):return max(abs(v-c) for I,c in zip(B,ctuple(y)) for v in I)
segments=[];previous=seedbox;y=seed;loop_start=None;worst=Q(0)
for edge,(a,b) in enumerate(zip(PATH,PATH[1:])):
 s=Q(0);h=Q(1,64);records=[]
 while s<1:
  end=min(Q(1),s+h);mid=(s+end)/2
  ta,tb,tm=at(a,b,s),at(a,b,end),at(a,b,mid);T=path_rect(ta,tb)
  assert all(x*x+z*z<84**2 for x in T[0] for z in T[1])
  um=newton(y,cpoint(tm));ub=newton(um,cpoint(tb)) if um is not None else None
  accepted=False
  if ub is not None:
   radii=[2*max(maxdist(u,v),maxdist(w,u))+Q(1,2**80)*scale(u) for u,v,w in zip(um,y,ub)]
   for inflation in range(10):
    ok,X,K,q,w=certify(um,T,radii)
    if X is None:break
    link=all(contains(x,prev,True) for x,prev in zip(X,previous))
    if ok and link:
     accepted=True;break
    if q>=Q(3,4):break
    radii=[max(r,Q(5,4)*max(dist_rect(prev,u),max(abs(v-c) for z,c in zip((kb.real,kb.imag),ctuple(u)) for v in bounds(z)))) for r,prev,u,kb in zip(radii,previous,um,K)]
  if accepted:
   rY=[Q(1,2**70)*scale(u) for u in ub]
   for inflation in range(8):
    okY,Y,KY,qY,wy=certify(ub,point_rect(tb),rY)
    if okY and all(contains(x,v,True) for x,v in zip(X,Y)):break
    rY=[r*4 for r in rY]
   else:accepted=False
  if not accepted:
   h=grid_floor(h/2)
   if h<Q(1,2**40):raise RuntimeError(('Arb step underflow',edge,str(s),ATTEMPTS))
   continue
  w['s']=[str(s),str(end)];w['T']=[list(map(str,I)) for I in T];w['endpoint']=wy
  records.append(w);previous=Y;y=ub;s=end;worst=max(worst,q)
  h=grid_floor(min(h*Q(3,2),Q(1,8)))
  if len(records)%50==0:print('edge',edge,'s',float(s),'slabs',len(records),'attempts',ATTEMPTS,'seconds',time.monotonic()-START,flush=True)
 segments.append(dict(a=list(map(str,a)),b=list(map(str,b)),slabs=records))
 if edge==0:loop_start=previous
 print('EDGE COMPLETE',edge,'slabs',len(records),'seconds',time.monotonic()-START,flush=True)
assert loop_start is not None
disjoint=any(U[1]<V[0] or V[1]<U[0] for a,b in zip(loop_start,previous) for U,V in zip(a,b))
pins=INPUT_PINS
for p,hsh in pins.items():assert digest(ROOT.parent/p)==hsh,p
out=dict(status='EXTERNAL_M3_MONODROMY_CANDIDATE_PENDING_INDEPENDENT_REPLAY',precision_bits=ctx.prec,parameter_grid_bits=GRID_BITS,versions=dict(flint=flint.__version__,sympy=sp.__version__),parameters=dict(eta='49/100',rates=['7','14'],strengths=['1','-419/384'],sigma='1'),radius_bound='84',seed_box=[[[str(v) for v in I] for I in B] for B in seedbox],segments=segments,loop_start=[[[str(v) for v in I] for I in B] for B in loop_start],loop_end=[[[str(v) for v in I] for I in B] for B in previous],disjoint=disjoint,total_slabs=sum(len(s['slabs']) for s in segments),attempts=ATTEMPTS,seconds=time.monotonic()-START,inputs_sha256=pins,scope='Candidate only. Every Krawczyk/endpoint/link/path/seed/source assertion requires fresh independent replay before claiming any Taylor-radius bound.')
dest=ROOT/'results/certificates/codex_m3_polygon_arb_witness.json.gz';dest.write_bytes(gzip.compress((json.dumps(out,separators=(',',':'))+'\n').encode(),mtime=0))
print('CANDIDATE DONE',disjoint,'slabs',out['total_slabs'],'seconds',out['seconds'],'witness',str(dest),flush=True)
