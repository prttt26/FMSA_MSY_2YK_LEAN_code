"""Actual scalar BH coefficient recursion and Fourier/WH B distinction.

High precision numerical evidence; parameter roots/signs are not Lean certificates.
The scalar model uses sigma=1, eta=.15, positive real Yukawa rate z=2.45.
"""
from pathlib import Path
import json
import mpmath as mp
mp.mp.dps=65
OUT=Path(__file__).resolve().parents[1]/'results/msa_b_hierarchy_physical'


def data(eta,z):
    pi=mp.pi;rho=6*eta/pi
    A0=2*pi*(1+2*eta)/(1-eta)**2
    qp0=2*pi*(1+eta/2)/(1-eta)**2
    B0=-3*pi*eta/(1-eta)**2
    def hsQ(s):
        return 1-rho*((1-s-mp.exp(-s))/s**2*qp0+(1-s+s*s/2-mp.exp(-s))/s**3*A0)
    def moments(G):
        gamma=1-2*pi*rho*G*mp.exp(-z)/z
        M=-rho/z*(gamma*(1+z)+2*pi*rho*G/z)
        N=rho/z**2*(2*pi*rho*G/z+gamma*(1+z+z*z/2))
        return gamma,M,N
    def amps(D,G):
        gamma,M,N=moments(G)
        return A0*(1+D*M)-4*B0*D*N, qp0*(1+D*M)+A0*D*N, 2*pi*rho*G*D/z, gamma*D
    def Q(s,D,G):
        A,b,W,C=amps(D,G)
        return 1-rho*((1-s-mp.exp(-s))/s**2*b+(1-s+s*s/2-mp.exp(-s))/s**3*A
            +W/(s+z)+C*(1-mp.exp(-s))/s+C*mp.exp(-s)/(s+z))
    def f(s,D,G):
        A,b,W,C=amps(D,G)
        return (A/s**2+b/s+z*C/(s+z))/(2*pi)
    F0=hsQ(z);P0=(A0+z*qp0)/z**2;G0=P0/(2*pi*F0)
    def Frest(G):
        gamma,M,N=moments(G)
        tail=(2*pi*rho*G/z+gamma*(2-mp.exp(-z)))/(2*z)
        return -rho*(M*(1-F0)/rho+N*((1-z-mp.exp(-z))/z**2*A0
            -4*B0*(1-z+z*z/2-mp.exp(-z))/z**3)+tail)
    def Prest(G):
        gamma,M,N=moments(G)
        return ((A0*M-4*B0*N)+z*(qp0*M+A0*N)+z*z*gamma/2)/z**2
    return locals()


def main():
    eta,z=mp.mpf('.15'),mp.mpf('2.45');d=data(eta,z)
    hsQ,Q,f=d['hsQ'],d['Q'],d['f'];F0,G0=d['F0'],d['G0'];rho=d['rho']
    pole=mp.findroot(hsQ,mp.mpc('-2.55','5.36'));s0=-pole
    K=mp.mpf(1)
    def paperB(s):return 2*mp.pi*rho*K*mp.exp(-s)/(F0**2*(s+z))
    def C1(s):return (hsQ(s)**2*paperB(-s)-hsQ(-s)**2*paperB(s))/s
    def eff(s):return C1(s)/hsQ(-s)**2
    lead=C1(s0)/(mp.diff(lambda s:hsQ(-s),s0)**2)
    rates=[]
    for h in ('1e-3','1e-5','1e-7'):
        e=mp.mpf(h);value=e*e*eff(s0+e)
        rates.append({'offset':h,'scaled_eff_B':[float(value.real),float(value.imag)],
                      'relative_double_pole_limit_error':float(abs(value-lead)/abs(lead))})
    assert abs(hsQ(pole))<mp.mpf('1e-55')
    assert abs(C1(s0))>mp.mpf('.1')
    assert rates[-1]['relative_double_pole_limit_error']<1e-6
    # Exact finite scalar BH coefficient recurrence, keeping every lower product.
    L=6;D=[mp.mpf(0)]*(L+1);G=[G0]+[mp.mpf(0)]*L
    Fs=[F0]+[mp.mpf(0)]*L;Ps=[d['P0']]+[mp.mpf(0)]*L
    aF=d['Frest'](G0);bF=d['Frest'](G0+1)-aF
    aP=d['Prest'](G0);bP=d['Prest'](G0+1)-aP
    for n in range(1,L+1):
        lowerDG=sum(D[j]*G[n-j] for j in range(1,n))
        D[n]=((2*mp.pi*K/z if n==1 else 0)-sum(D[j]*Fs[n-j] for j in range(1,n)))/F0
        Fs[n]=aF*D[n]+bF*lowerDG;Ps[n]=aP*D[n]+bP*lowerDG
        G[n]=(Ps[n]/(2*mp.pi)-G0*Fs[n]-sum(G[j]*Fs[n-j] for j in range(1,n)))/F0
    def root(t):
        return mp.findroot(lambda a,b:(a*(F0+a*d['Frest'](b))-2*mp.pi*t*K/z,
            2*mp.pi*b*(F0+a*d['Frest'](b))-d['P0']-a*d['Prest'](b)),
            (0,G0),tol=mp.mpf('1e-60'))
    jet_errors=[]
    for n in range(1,4):
        gotD=mp.diff(lambda t:root(t)[0],0,n,method='quad',radius=mp.mpf('.001'))/mp.factorial(n)
        gotG=mp.diff(lambda t:root(t)[1],0,n,method='quad',radius=mp.mpf('.001'))/mp.factorial(n)
        err=max(abs(gotD-D[n]),abs(gotG-G[n]))
        assert err<mp.mpf('1e-40'),(n,err)
        jet_errors.append({'order':n,'absolute_error':float(err)})
    # Source kernel is constructed from the actual f,Q amplitude jets, not H_n.
    source=[]
    for n in range(1,4):
        probe=mp.mpc('.4','1.3')
        fn=mp.diff(lambda t:f(probe,*root(t)),0,n,method='quad',radius=mp.mpf('.001'))/mp.factorial(n)
        qn=mp.diff(lambda t:Q(probe,*root(t)),0,n,method='quad',radius=mp.mpf('.001'))/mp.factorial(n)
        theta=2*mp.pi*rho*mp.exp(-probe)*(hsQ(probe)*fn-f(probe,0,G0)*qn)
        hjet=lambda j:mp.diff(lambda t:mp.exp(-probe)*f(probe,*root(t))/Q(probe,*root(t)),0,j,method='quad',radius=mp.mpf('.001'))/mp.factorial(j)
        lower=sum(2*mp.pi*rho*hjet(j)*hsQ(probe)*
            mp.diff(lambda t:Q(probe,*root(t)),0,n-j,method='quad',radius=mp.mpf('.001'))/mp.factorial(n-j) for j in range(1,n))
        reconstructed=hsQ(probe)**2*(2*mp.pi*rho*hjet(n))+lower
        error=abs(theta-reconstructed)
        assert error<mp.mpf('1e-40'),(n,error)
        if n==1:assert abs(theta-paperB(probe))<mp.mpf('1e-40'),abs(theta-paperB(probe))
        source.append({'order':n,'actual_source_identity_error':float(error)})
    report={'status':'PASS','scope':'High precision physical scalar evidence; not a Lean certificate for the reported zero.',
        'parameters':{'eta':float(eta),'sigma':1.,'z':float(z),'rho':float(rho),'pair_strength':1.},
        'Q_seed_zero':[float(pole.real),float(pole.imag)],'Q_minus_zero':[float(s0.real),float(s0.imag)],
        'seed_zero_residual':str(abs(hsQ(pole))),
        'nonzero_C1_at_Q_minus_zero':[float(C1(s0).real),float(C1(s0).imag)],
        'double_pole_coefficient':[float(lead.real),float(lead.imag)],'double_pole_checks':rates,
        'BH_jet_crosschecks':jet_errors,'one_sided_source_crosschecks':source,
        'Dt_coefficients':[str(v) for v in D],'G_coefficients':[str(v) for v in G]}
    OUT.mkdir(parents=True,exist_ok=True);(OUT/'physical_checks.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__=='__main__':main()
