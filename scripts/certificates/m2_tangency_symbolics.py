"""UNTRUSTED expression candidates for the ten-variable M2 contact system.

The kernel proves all polynomial/formula identities. No SymPy result or
external interval is a mathematical premise of the Lean theorems.
"""
import sympy as sp
from codex_m2_jacobian_arb import symbolic_residual

def symbolic_system():
    amp,(tau,w),R,J=symbolic_residual()
    vel=sp.symbols('v0:4');variables=amp+(tau,w)+vel
    eta=sp.Rational(1,10);rho=6*eta/sp.pi;vac=1-eta
    z=[sp.Rational(9,5),sp.Integer(12)]
    alpha=[sp.expand(rho*(6*eta+(4*eta-1)*u+(eta-1)*u*u)/(vac*vac*u*u)) for u in z]
    beta=[sp.expand(12*eta*rho/(vac*vac*u**3)*(-(1+2*eta)*u*(1-(1+u)*sp.exp(-u))+
          6*eta*(1-(1+u+u*u/2)*sp.exp(-u)))) for u in z]
    zero=sp.Rational(40,27)+sum(amp[i]*(alpha[i]+beta[i]*amp[i+2]) for i in range(2))
    grad=[sp.diff(zero,a) for a in amp]
    forcing=[10*sp.pi/9,sp.pi*w/6,sp.Integer(0),sp.Integer(0)]
    S=list(R)+[sp.expand(sum(J[i][j]*vel[j] for j in range(4))-forcing[i]) for i in range(4)]+[
        sp.expand(zero),sp.expand(sum(a*b for a,b in zip(grad,vel)))]
    assert len(variables)==len(S)==10 and not any(e.atoms(sp.Float) for e in S)
    return variables,S,sp.Matrix(S).jacobian(variables)

def lean_real(e,variables=(),variable_name='y'):
    if e in variables:return f'{variable_name} {variables.index(e)}'
    if e==sp.pi:return 'Real.pi'
    if e.is_Integer:return f'({int(e)} : ℝ)'
    if e.is_Rational:return f'(({int(e.p)} : ℝ)/{int(e.q)})'
    if e.func==sp.exp:return '(Real.exp '+lean_real(e.args[0],variables,variable_name)+')'
    if e.func==sp.Add:return '('+'+'.join(lean_real(x,variables,variable_name) for x in e.args)+')'
    if e.func==sp.Mul:return '('+'*'.join(lean_real(x,variables,variable_name) for x in e.args)+')'
    if e.func==sp.Pow and e.exp.is_Integer:
        return '('+lean_real(e.base,variables,variable_name)+f'^{abs(int(e.exp))})'+('⁻¹' if e.exp<0 else '')
    raise ValueError(e)

def lean_polynomial(e,variables):
    terms=[]
    for exponents,coefficient in sp.Poly(e,*variables).terms():
        assert not coefficient.free_symbols
        coefficient=sp.expand(coefficient)
        factors=['MvPolynomial.C '+lean_real(coefficient)]
        factors += [f'(MvPolynomial.X {i})^{n}' for i,n in enumerate(exponents) if n]
        terms.append('('+'*'.join(factors)+')')
    return '('+'+'.join(terms)+')'
