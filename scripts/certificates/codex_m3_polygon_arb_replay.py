"""Independent EXTERNAL replay of exact M3 complex-path witnesses, not Lean.
Frozen F5 constructor/residual AST is evaluated without importing its module.
A separately transcribed literal BH model is checked identically. Fresh512-bit
centered polynomial Taylor enclosures replace the generator's sparse evaluator.
"""
import ast,copy,gzip,hashlib,json,sys,time,types
from argparse import ArgumentParser
from datetime import datetime,timezone
from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
from math import comb
from pathlib import Path
import sympy as sp
import flint
from flint import arb,acb,ctx,fmpq
if not __debug__:raise RuntimeError('Assertions must remain enabled; do not use python -O.')
ROOT=Path(__file__).resolve().parents[2]
F5=ROOT.parent/'MSA_and_1st_Truncation/formalization/certificates/f5_competing_tails.py'
WITNESS=ROOT/'results/certificates/codex_m3_polygon_arb_witness.json.gz'
FIRST=ROOT/'results/certificates/codex_first_loss_arb_audit.json'
VERT=[(Q(-333,16),Q(5185,64)),(Q(-329,16),Q(5185,64)),(Q(-329,16),Q(5201,64)),(Q(-333,16),Q(5201,64))]
PATH=[(Q(0),Q(0)),*VERT,VERT[0]]
def digest(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def rational(v):
 assert isinstance(v,str),'Inexact JSON number';return Q(v)
def pt(v):
 v=Q(v);return arb(fmpq(v.numerator,v.denominator))
def exact(a):
 assert a.is_exact() and a.is_finite(),'Nonfinite enclosure'
 m,e=map(int,a.man_exp());return Q(m)*Q(2)**e
def ends(a):return exact(a.lower()),exact(a.upper())
def complex_point(v):
 assert len(v)==2;return acb(pt(rational(v[0])),pt(rational(v[1])))
def point_tuple(v):
 assert len(v)==2;return tuple(map(rational,v))
def box(B,strict=False):
 assert len(B)==2
 out=[]
 for I in B:
  assert len(I)==2
  lo,hi=map(rational,I);assert lo<hi if strict else lo<=hi
  out.append((lo,hi))
 return tuple(out)
def rect_ball(B):
 def part(I):
  lo,hi=I;a=arb(pt((lo+hi)/2),pt((hi-lo)/2));l,h=ends(a)
  assert l<=lo<=hi<=h
  return a
 return acb(part(B[0]),part(B[1]))
def inside(outer,inner):return all(a[0]<b[0]<=b[1]<a[1] for a,b in zip(outer,inner))
def maxabs(I):return max(abs(I[0]),abs(I[1]))
def path_at(a,b,t):return tuple(x+(y-x)*t for x,y in zip(a,b))
def path_box(a,b):return tuple((min(x,y),max(x,y)) for x,y in zip(a,b))
def compare_provenance(d):
 pins=d['inputs_sha256'];assert len(pins)==28,'Incomplete generation source context'
 for p,h in pins.items():
  path=Path(p);assert not path.is_absolute() and '..' not in path.parts
  assert path.parts[0] in {'MSA_Convergence','MSA_and_1st_Truncation'}
  assert digest(ROOT.parent/path)==h,'Input pin changed: '+p
 first=json.loads(FIRST.read_text());assert first['status']=='PASS_EXTERNAL_FIRST_LOSS_AUDIT'
 assert len(first['inputs_sha256'])==25
 for p,h in first['inputs_sha256'].items():assert pins[p]==h==digest(ROOT.parent/p)
 assert pins[str(FIRST.relative_to(ROOT.parent))]==digest(FIRST)
 assert pins[str(F5.relative_to(ROOT.parent))]==digest(F5)
 return first

@lru_cache(None)
def value(e):
 if e.is_Rational:return pt(Q(int(e.p),int(e.q)))
 if e==sp.pi:return arb.pi()
 if e.func==sp.exp:return value(e.args[0]).exp()
 if e.func==sp.Add:return sum((value(v) for v in e.args),arb(0))
 if e.func==sp.Mul:
  v=arb(1)
  for a in e.args:v*=value(a)
  return v
 if e.is_Pow and e.exp.is_Integer:return value(e.base)**int(e.exp)
 raise AssertionError(('Unsupported mathematical coefficient',e))

def literal_bh(V):
 D=V[:2];G=V[2:4];tau=V[4];z=[sp.Integer(7),sp.Integer(14)]
 eta=sp.Rational(49,100);rho=6*eta/sp.pi;vac=1-eta
 Q0=2*sp.pi/vac*(1+sp.pi*rho/(4*vac));Qpp=2*sp.pi/vac*(1+sp.pi*rho/(2*vac))
 gam=[1-2*sp.pi*rho*sp.exp(-z[t])*G[t]/z[t] for t in range(2)]
 W=[2*sp.pi*rho*G[t]*D[t]/z[t] for t in range(2)]
 C=[gam[t]*D[t] for t in range(2)]
 M=[-rho*(W[t]+(1+z[t])*C[t])/z[t] for t in range(2)]
 N=[rho*(W[t]+(1+z[t]+z[t]**2/2)*C[t])/z[t]**2 for t in range(2)]
 A=Qpp+sum(Qpp*M[t]+2*sp.pi**2*rho*N[t]/vac**2 for t in range(2))
 qp=Q0+sum(Q0*M[t]+Qpp*N[t] for t in range(2))
 def F(s):
  E=sp.exp(-s)
  ph=qp*(1-s-E)/s**2+A*(1-s+s*s/2-E)/s**3
  ph+=sum(W[t]/(s+z[t])+C[t]*((1-E)/s+E/(s+z[t])) for t in range(2))
  return 1-rho*ph
 first=[D[t]*F(z[t])-2*sp.pi*tau*k/z[t] for t,k in enumerate((sp.Integer(1),sp.Rational(-419,384)))]
 second=[2*sp.pi*G[t]*F(z[t])-(A+z[t]*qp+sum(z[t]**2*z[u]*C[u]/(z[t]+z[u]) for u in range(2)))/z[t]**2 for t in range(2)]
 return [sp.expand(r) for r in first+second]

def build_model():
 raw=F5.read_bytes();tree=ast.parse(raw)
 cls=next(n for n in tree.body if isinstance(n,ast.ClassDef) and n.name=='Model')
 init=next(n for n in cls.body if isinstance(n,ast.FunctionDef) and n.name=='__init__')
 residual=next(n for n in cls.body if isinstance(n,ast.FunctionDef) and n.name=='residual')
 cut=next(i for i,n in enumerate(init.body) if isinstance(n,ast.Assign) and any(isinstance(t,ast.Attribute) and t.attr=='seed_mp' for t in n.targets))+1
 init=copy.deepcopy(init);init.body=init.body[:cut]
 class ExactFour(ast.NodeTransformer):
  def visit_Constant(self,n):
   if isinstance(n.value,float):
    assert n.value==4.0
    return ast.copy_location(ast.Constant(value=4),n)
   return n
 residual=ExactFour().visit(copy.deepcopy(residual))
 future=ast.ImportFrom(module='__future__',names=[ast.alias(name='annotations')],level=0)
 module=ast.fix_missing_locations(ast.Module(body=[future,init,residual],type_ignores=[]))
 def make(adapter,exact_decimal):
  ns={'mpmath':adapter,'mp_exact':exact_decimal}
  exec(compile(module,'read_only_F5_constructor_prefix_and_residual','exec'),ns)
  obj=types.SimpleNamespace();ns['__init__'](obj,'49/100',['7','14'],['1','-419/384'])
  return obj,ns['residual']
 obj,fn=make(types.SimpleNamespace(pi=sp.pi,exp=sp.exp,mpf=sp.Rational),sp.Rational)
 V=sp.symbols('D1 D2 G1 G2 tau')
 R=[sp.expand(r) for r in fn(obj,list(V[:4]),V[4],obj.mpk)]
 actual=literal_bh(V);assert all(sp.expand(a-b)==0 for a,b in zip(R,actual)),'Original BH dictionary mismatch'
 assert all(not r.atoms(sp.Float) for r in R)
 assert all(sp.cancel(r.subs(dict(zip(V,[*obj.seed_mp,sp.Integer(0)]))))==0 for r in R),'False HS seed'
 aobj,afn=make(types.SimpleNamespace(pi=arb.pi(),exp=lambda x:x.exp(),mpf=lambda v:pt(Q(v))),lambda s:pt(Q(s)))
 seed=[acb(v) for v in aobj.seed_mp]
 J=[[sp.diff(r,v) for v in V[:4]] for r in R]
 assert all(not (v.free_symbols&{V[4]}) for row in J for v in row)
 return aobj,afn,seed,[[CenteredPoly(v,V[:4]) for v in row] for row in J]

class CenteredPoly:
 def __init__(self,e,V):self.terms=[(m,acb(value(c))) for m,c in sp.Poly(e,*V).terms()]
 def enclose(self,y,xb):
  h=[b-a for a,b in zip(y,xb)];terms={}
  for exponent,c in self.terms:
   for beta in product(*(range(n+1) for n in exponent)):
    a=c
    for j,(n,b) in enumerate(zip(exponent,beta)):
     a*=comb(n,b)
     if n>b:a*=y[j]**(n-b)
    terms[beta]=terms.get(beta,acb(0))+a
  out=acb(0)
  for beta,a in terms.items():
   for j,b in enumerate(beta):
    if b:a*=h[j]**b
   out+=a
  return out

def structural(d,seed):
 assert d['status']=='EXTERNAL_M3_MONODROMY_CANDIDATE_PENDING_INDEPENDENT_REPLAY'
 assert d['parameters']==dict(eta='49/100',rates=['7','14'],strengths=['1','-419/384'],sigma='1')
 radius=rational(d['radius_bound']);assert radius>0 and d['parameter_grid_bits']==40
 sb=list(map(box,d['seed_box']));assert len(sb)==4
 for s,B in zip(seed,sb):
  for a,I in zip((s.real,s.imag),B):
   lo,hi=ends(a);assert I[0]<=lo<=hi<=I[1],'False actual seed enclosure'
 assert len(d['segments'])==5,'Incomplete closed path'
 previous=sb;loop_start=None;n=0
 for edge,(seg,a,b) in enumerate(zip(d['segments'],PATH,PATH[1:])):
  assert point_tuple(seg['a'])==a and point_tuple(seg['b'])==b,'Wrong geometric path'
  assert seg['slabs'],'Missing path segment'
  expected=Q(0)
  for rec in seg['slabs']:
   sa,sb=map(rational,rec['s']);assert sa==expected and sa<sb<=1,'Path coverage gap'
   assert (sa*2**40).denominator==(sb*2**40).denominator==1,'Non-grid path parameter'
   T=box(rec['T']);assert T==path_box(path_at(a,b,sa),path_at(a,b,sb)),'False affine parameter enclosure'
   assert all(x*x+y*y<radius**2 for x in T[0] for y in T[1]),'Path is not inside claimed disk'
   X=list(map(lambda B:box(B,True),rec['X']));Y=list(map(lambda B:box(B,True),rec['endpoint']['X']))
   assert len(X)==len(Y)==4
   assert all(inside(x,p) for x,p in zip(X,previous)),'Broken previous-root link'
   assert all(inside(x,p) for x,p in zip(X,Y)),'Endpoint not in slab root box'
   previous=Y;expected=sb;n+=1
  assert expected==1,'Segment stops early'
  if edge==0:loop_start=previous
 assert n==d['total_slabs'] and loop_start is not None
 assert loop_start==list(map(box,d['loop_start'])) and previous==list(map(box,d['loop_end']))
 assert d['disjoint'] is True
 assert any(a[1]<b[0] or b[1]<a[0] for U,V in zip(loop_start,previous) for a,b in zip(U,V)),'No certified sheet change'
 return n

def analytic(w,T,model):
 obj,fn,seed,JP=model
 assert len(w['center'])==len(w['X'])==len(w['weights'])==4
 center=[point_tuple(v) for v in w['center']];y=list(map(complex_point,w['center']))
 X=[box(B,True) for B in w['X']];xb=list(map(rect_ball,X));weights=list(map(rational,w['weights']))
 assert all(a>0 for a in weights),'Invalid weighted norm'
 for p,B in zip(center,X):assert all(I[0]<c<I[1] for c,I in zip(p,B)),'Center is outside domain'
 assert len(w['preconditioner'])==4 and all(len(row)==4 for row in w['preconditioner'])
 C=[[complex_point(v) for v in row] for row in w['preconditioner']]
 J=[[poly.enclose(y,xb) for poly in row] for row in JP]
 E=[[acb(int(i==j))-sum((C[i][k]*J[k][j] for k in range(4)),acb(0)) for j in range(4)] for i in range(4)]
 assert rational(w['q_bound'])==Q(3,4)
 q=max(exact(sum((abs(E[i][j])*pt(weights[j])/pt(weights[i]) for j in range(4)),arb(0)).upper()) for i in range(4))
 assert q<Q(3,4),'Fresh analytic contraction failed'
 # Values use frozen factored residual arithmetic, not sparse polynomials.
 R=fn(obj,y,rect_ball(T),obj.mpk)
 dx=[a-b for a,b in zip(xb,y)]
 K=[y[i]-sum((C[i][j]*R[j] for j in range(4)),acb(0))+sum((E[i][j]*dx[j] for j in range(4)),acb(0)) for i in range(4)]
 for a,B in zip(K,X):
  for v,I in zip((a.real,a.imag),B):
   lo,hi=ends(v);assert I[0]<lo<=hi<I[1],'Fresh analytic self-map inclusion failed'
 qreal=max(sum(((maxabs(ends(E[i][j].real))+maxabs(ends(E[i][j].imag)))*weights[j]/weights[i] for j in range(4)),Q(0)) for i in range(4))
 return q,qreal

def controls(d,model):
 rejected=[]
 def reject(label,fn):
  try:fn()
  except (AssertionError,ValueError,KeyError,IndexError,ZeroDivisionError):rejected.append(label)
  else:raise AssertionError('Accepted mathematical corruption: '+label)
 seed=model[2]
 def first_edit(edit):
  bad=dict(d);bad['segments']=list(d['segments']);s=dict(d['segments'][0]);s['slabs']=list(s['slabs']);r=copy.deepcopy(s['slabs'][0]);edit(r);s['slabs'][0]=r;bad['segments'][0]=s;return bad
 bad=dict(d);bad['segments']=list(d['segments'][1:]);reject('missing prefix segment',lambda:structural(bad,seed))
 bad=dict(d);bad['segments']=list(d['segments']);seg=dict(bad['segments'][0]);seg['slabs']=seg['slabs'][1:];bad['segments'][0]=seg;reject('missing initial slab',lambda:structural(bad,seed))
 bad=first_edit(lambda r:r.__setitem__('T',[['0','0'],['0','0']]))
 reject('false affine parameter enclosure',lambda:structural(bad,seed))
 bad=dict(d);bad['radius_bound']='80';reject('false smaller radius',lambda:structural(bad,seed))
 bad=dict(d);bad['seed_box']=copy.deepcopy(d['seed_box']);bad['seed_box'][2]=[['0','0'],['0','0']]
 reject('false actual HS seed box',lambda:structural(bad,seed))
 rec=copy.deepcopy(d['segments'][0]['slabs'][0]);T=box(rec['T'])
 rec['preconditioner']=[[['0','0'] for _ in range(4)] for _ in range(4)]
 reject('zero complex preconditioner',lambda:analytic(rec,T,model))
 rec=copy.deepcopy(d['segments'][0]['slabs'][0]);rec['center'][0][0]=str(rational(rec['center'][0][0])+1000)
 reject('false amplitude center',lambda:analytic(rec,box(rec['T']),model))
 last=d['segments'][-1]['slabs'][-1];X=list(map(box,last['X']));wrong=list(map(box,d['segments'][0]['slabs'][-1]['endpoint']['X']))
 def badlink():assert all(inside(x,y) for x,y in zip(X,wrong)),'Endpoint not in slab root box'
 reject('unlinked switched endpoint root',badlink)
 bad=dict(d);bad['loop_end']=copy.deepcopy(d['loop_start']);reject('forged loop endpoint',lambda:structural(bad,seed))
 bad=dict(d);bad['inputs_sha256']=dict(d['inputs_sha256']);k=next(iter(bad['inputs_sha256']));bad['inputs_sha256'][k]='0'*64
 reject('corrupted provenance pin',lambda:compare_provenance(bad))
 assert len(rejected)==10
 return rejected


def canonical_prefix_endpoint(control):
 # Use the endpoint actually covered by the all-wave parent certificate,
 # never the nearby historical diagnostic control['taus']['tau_lo'].
 lo=rational(control['rigorous_bracket']['lo']['tau'])
 chain=json.loads(gzip.decompress((ROOT/'results/two_tail/two_tail_py_chain_M3.json.gz').read_bytes()))
 record=json.loads(gzip.decompress((ROOT/'results/two_tail/two_tail_first_loss_M3.json.gz').read_bytes()))
 def chain_number(v):
  assert isinstance(v,str)
  if 'p' in v:
   m,e=v.split('p');return Q(int(m))*Q(2)**int(e)
  return rational(v)
 assert chain['p_star'] is None and all(s['w']['k']==4 for s in chain['slabs'])
 required=[j for j,s in enumerate(chain['slabs']) if chain_number(s['w']['P'][1])<=lo]
 assert required==record['required_slabs']==list(range(len(required))) and required,'Wrong canonical prefix slabs'
 end=Q(0)
 for j in required:
  slab=chain['slabs'][j];a,b=map(chain_number,slab['w']['P'])
  assert slab['A_required'] is True and a==end and a<b,'Gap in canonical prefix'
  end=b
 assert end==lo,'Canonical prefix does not reach rigorous endpoint'
 return str(lo),len(required)

def main():
 ap=ArgumentParser(description=__doc__);ap.add_argument('--witness',type=Path,default=WITNESS);ap.add_argument('--precision',type=int,default=512);ap.add_argument('--negative-controls',action='store_true');ap.add_argument('--output',type=Path);args=ap.parse_args()
 assert args.precision>=448
 if args.output:
  assert args.negative_controls,'Receipt requires all corruption controls'
  assert args.output.resolve().parent==ROOT/'results/certificates' and args.output.name=='codex_m3_polygon_arb_audit.json'
 args.witness=args.witness.resolve()
 ctx.prec=args.precision;t0=time.monotonic();raw=args.witness.read_bytes();d=json.loads(gzip.decompress(raw));first=compare_provenance(d)
 pins=dict(d['inputs_sha256']);pins[str(args.witness.relative_to(ROOT.parent))]=hashlib.sha256(raw).hexdigest();pins[str(Path(__file__).relative_to(ROOT.parent))]=digest(__file__)
 model=build_model();n=structural(d,model[2]);checks=0;worst=Q(0);worstreal=Q(0)
 for edge,seg in enumerate(d['segments']):
  a,b=point_tuple(seg['a']),point_tuple(seg['b'])
  for j,w in enumerate(seg['slabs']):
   T=box(w['T']);q,qr=analytic(w,T,model);worst=max(worst,q);worstreal=max(worstreal,qr);checks+=1
   end=rational(w['s'][1]);tb=path_at(a,b,end);TP=((tb[0],tb[0]),(tb[1],tb[1]))
   q,qr=analytic(w['endpoint'],TP,model);worst=max(worst,q);worstreal=max(worstreal,qr);checks+=1
   if (j+1)%200==0:print('fresh replay edge',edge,'slabs',j+1,'checks',checks,'seconds',time.monotonic()-t0,flush=True)
  print('FRESH EDGE PASS',edge,'checks',checks,flush=True)
 bad=controls(d,model) if args.negative_controls else []
 assert checks==2*n and n>0
 # The separately fully replayed first-loss record supplies its existing scope.
 ep=json.loads((ROOT/'results/two_tail/two_tail_endpoint_interval_exact.json').read_text())
 c=next(c for c in ep['controls'] if c['name'].startswith('M3:'))
 assert c['eta']=='49/100' and c['z']==['7','14'] and c['w']=='-419/384'
 lo,required_slabs=canonical_prefix_endpoint(c)
 assert Q(lo)>Q(337,4)>rational(d['radius_bound'])
 assert first['results']['M3']['analytic_steps_replayed']==47822
 for p,h in pins.items():assert digest(ROOT.parent/p)==h,'Input changed during replay: '+p
 out=dict(status='PASS_EXTERNAL_M3_MONODROMY_AUDIT',created_at_utc=datetime.now(timezone.utc).isoformat(),label='EXTERNAL Arb/Fraction certificate; NOT a Lean proof',precision_bits=ctx.prec,versions=dict(python=sys.version.split()[0],python_flint=flint.__version__,sympy=sp.__version__),inputs_sha256=pins,parameters=d['parameters'],path_slabs=n,krawczyk_checks=checks,weighted_complex_defect_upper_bound=str(worst),weighted_real_component_defect_upper_bound=str(worstreal),negative_controls_rejected=bad,actual_seed_and_BH_dictionary_symbolically_checked=True,exact_path_inside_disk=True,disjoint_loop_end_roots=True,common_amplitude_Taylor_radius_upper_bound=d['radius_bound'],canonical_real_coupling_outside_radius='337/4',canonical_prefix_dependency=str(FIRST.relative_to(ROOT)),first_loss_tau_lo=lo,first_loss_tau_lo_source='controls[M3].rigorous_bracket.lo.tau',canonical_prefix_required_slabs=required_slabs,seconds=time.monotonic()-t0,scope='The HS-seeded complexified ORIGINAL BH germ has monodromy on a seed-linked polygon contained in |tau|<'+d['radius_bound']+', so its common amplitude Taylor radius is <='+d['radius_bound']+'. Together with the separately audited all-wave PY prefix, tau=337/4 is real and fully canonical but the vector coupling series fails to converge there. No nearest singularity location, exact radius, all component divergence, first-loss frequency or Lean numerical instance is claimed.')
 if args.output:args.output.write_text(json.dumps(out,indent=2)+'\n')
 print(out['status'],'slabs',n,'checks',checks,'negative',len(bad),'pins',len(pins),'seconds',out['seconds'],flush=True)
if __name__=='__main__':main()
