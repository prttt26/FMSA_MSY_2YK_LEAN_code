import sys, numpy as np
sys.path.insert(0, str(__import__('pathlib').Path(__file__).resolve().parent)); sys.path.insert(0, str(__import__('pathlib').Path(__file__).resolve().parents[1]))
from dw_system import series, Mx
from baxter_F_signs import F_affine
nmax = 48
for w in (0.0, -0.5, -1.0, -1.5, -2.0, -2.5, -3.0, -3.5, -4.0, -5.0, -6.0):
    st = Mx.HCYMix([1.0], [6*0.3/np.pi], [1.8, 12.0], np.array([1.0, w]).reshape(2, 1, 1))
    tr = Mx.trace_coupling_mix(st, lam_max=8.0); lend = tr[-1][0]; fold = lend < 8 - 1e-9
    sc = lend if fold else 2.0
    D, W, _ = series(st, nmax, sc)
    # F(s) coefficient sign at several s: first order where a coefficient > 0
    first_pos = []
    for s in (1e-9, 1.8, 6.0, 12.0):
        F0, gD, gW = F_affine(st, s); Fc = (D@gD + W@gW)[1:]
        tol = 1e-10*np.max(np.abs(Fc)); idx = np.where(Fc > tol)[0]
        first_pos.append(int(idx[0])+1 if len(idx) else 0)
    # root test radius on all components, in units of tau_f (or of 2 if no fold)
    allc = np.abs(np.concatenate([D, W], axis=1))[1:]; cm = allc.max(axis=1); n = np.arange(1, nmax+1)
    r = cm[1:]/cm[:-1]; x = 1/n[1:]; a, b0 = np.polyfit(x[-14:], r[-14:], 1)
    print(f"w={w:+.1f}: {'fold tau_f=%.5f' % lend if fold else 'no fold<=8   '}  first order with F_n(s)>0 at s=0,1.8,6,12: {first_pos}"
          f"   DombSykes R/scale={1/b0:.4f} exp={-a/b0-1:+.3f}   root R/scale(n=48)={cm[-1]**(-1/nmax):.4f}", flush=True)
