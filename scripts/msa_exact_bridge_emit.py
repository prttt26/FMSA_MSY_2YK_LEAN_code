"""Emit rational and polynomial data used by the checked bridge theorem modules.

SymPy proposes formulas only: sparse_ring proves each emitted identity in Lean.
Use --cached-algebra during development; omission reconstructs the source prefix.
"""
import argparse,ast,pickle,hashlib,json,time
from pathlib import Path
import sympy as sp
from msa_exact_sparse_feasibility import encode
ROOT=Path(__file__).resolve().parents[3]
DEST=Path(__file__).resolve().parents[1]/'LeanCode/YukawaOZ'

def balance(op,args):
    if len(args)==1:return args[0]
    mid=len(args)//2
    return '('+balance(op,args[:mid])+' '+op+' '+balance(op,args[mid:])+')'

def lean(e):
    xi=sp.Symbol('xi',positive=True)
    z=sp.Symbol('z',positive=True)
    k=sp.Symbol('k',positive=True)
    if e==1-xi:return '(1 - xi)'
    if e==k**2+z**2:return '(z ^ 2 + k ^ 2)'
    if e.is_Integer:return '('+str(e)+')'
    if e.is_Rational:return '('+str(e.p)+' / '+str(e.q)+')'
    if e.is_Symbol:return str(e)
    if e.is_Add:return balance('+',[lean(a) for a in e.args])
    if e.is_Mul:return balance('*',[lean(a) for a in e.args])
    if e.is_Pow:
        assert e.exp.is_Integer
        n=int(e.exp)
        if n<0:return '(1 / ('+lean(e.base)+' ^ '+str(-n)+'))'
        return '('+lean(e.base)+' ^ '+str(n)+')'
    raise ValueError(e)

ARGS='xi z k G C S Ez p Dt K'
PHYS='xi z k G (Real.cos k) (Real.sin k) (Real.exp (-z)) Real.pi Dt K'
HEADER='''import LeanCode.YukawaOZ.SparseRingTactic
import LeanCode.YukawaOZ.ExactMSASparseReassembly
import LeanCode.YukawaOZ.MSABaxterKSpace
namespace FMSA.ExactMSA.RationalBridge
open Real SparseCertificate SparseCheckpoints
set_option maxRecDepth 100000
set_option maxHeartbeats 0
'''


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--cached-algebra',type=Path)
    parser.add_argument('--output',type=Path,default=DEST/'ExactMSARationalData.lean')
    parser.add_argument('--metadata',type=Path)
    started=time.perf_counter()
    options=parser.parse_args()
    if options.cached_algebra:
        e=pickle.loads(options.cached_algebra.read_bytes())
    else:
        prefix=[]
        source=ROOT/'msaexact6_scaletest.py'
        for node in ast.parse(source.read_text()).body:
            if isinstance(node,ast.FunctionDef) and node.name=='lean':break
            prefix.append(node)
        e={}
        exec(compile(ast.Module(body=prefix,type_ignores=[]),str(source),'exec'),e)
    trig=e['S']**2+e['C']**2-1
    reduction_cache=Path('/tmp/msa_exact_bridge_reduction.pkl')
    if options.cached_algebra and reduction_cache.exists():
        mu=pickle.loads(reduction_cache.read_bytes())
    else:
        quotient,rem=sp.div(sp.Poly(e['numR']-e['num'],e['S']),sp.Poly(trig,e['S']))
        assert rem.as_expr()==0
        mu=quotient.as_expr()
    rden=sp.denom(sp.together(e['r33']))
    expressions={
        'fSource':e['bhF'],'pSource':e['bhP'],'deltaSource':sp.together(e['Delta']),
        'm29Source':e['m29'],'denSource':e['denR'],
        'r33DenSource':rden,
    }
    definitions=HEADER
    for name,expression in expressions.items():
        definitions+=f'noncomputable def {name} ({ARGS} : ℝ) : ℝ :=\n  {lean(expression)}\n\n'
    idx={e[name]:i for i,name in enumerate(ARGS.split())}
    for name,expression in [('rawSource',e['numR']),('muSource',mu)]:
        definitions+=f'def {name}Expr : Expr :=\n  {encode(expression,idx)}\n\n'
        definitions+=f'noncomputable def {name} ({ARGS} : ℝ) : ℝ :=\n  eval {name}Expr (fun i => ([{",".join(ARGS.split())}] : List ℝ).getD i 0)\n\n'
    for name,encoded in [('n1Source','dt1Left'),('n2Source','dt2Left'),
                         ('q1Source','quotientCoefficient'),
                         ('r0Source','residualConstant'),('r1Source','residualLinear')]:
        definitions+=f'noncomputable def {name} ({ARGS} : ℝ) : ℝ :=\n  eval {encoded} (fun i => ([xi,z,k,G,C,S,Ez,p,Dt,K] : List ℝ).getD i 0)\n\n'
    definitions+='end FMSA.ExactMSA.RationalBridge\n'
    options.output.write_text(definitions)
    if options.metadata:
        source=ROOT/'msaexact6_scaletest.py'
        options.metadata.write_text(json.dumps({
            'source':str(source),'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
            'generated_sha256':hashlib.sha256(definitions.encode()).hexdigest(),
            'expression_variables':ARGS.split(),'cached_algebra':bool(options.cached_algebra),
            'elapsed_seconds':time.perf_counter()-started,
            'scope':'scalar one-component one-Yukawa exact closure; data proposals require Lean checks'
        },indent=2)+'\n')
    print('Generated rational bridge data; theorem modules are maintained separately.',flush=True)

if __name__=='__main__':main()
