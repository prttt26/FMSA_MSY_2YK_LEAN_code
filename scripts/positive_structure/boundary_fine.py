import sys, numpy as np
sys.path.insert(0, str(__import__('pathlib').Path(__file__).resolve().parent)); sys.path.insert(0, str(__import__('pathlib').Path(__file__).resolve().parents[1]))
from dw_system import series, Mx
nmax = 70; SC = 4.0
for w in np.arange(-2.50, -3.01, -0.05):
    st = Mx.HCYMix([1.0], [6*0.3/np.pi], [1.8, 12.0], np.array([1.0, w]).reshape(2, 1, 1))
    tr = Mx.trace_coupling_mix(st, lam_max=30.0); lend = tr[-1][0]; fold = lend < 30 - 1e-9
    D, W, _ = series(st, nmax, SC)
    allc = np.concatenate([D, W], axis=1)[1:]
    last = []
    for c in range(allc.shape[1]):
        col = allc[:, c]; sg = np.sign(col); tol = 1e-12*np.max(np.abs(col))
        fl = [i+2 for i in range(nmax-1) if sg[i] != sg[i+1] and abs(col[i+1]) > tol]
        last.append(fl[-1] if fl else 0)
    cm = np.abs(allc).max(axis=1)
    R = [SC*cm[k-1]**(-1/k) for k in (40, 55, 70)]
    # the square-root correction n^{3/2/n} for a real fold
    corr = [r/np.exp(1.5*np.log(k)/k) for r, k in zip(R, (40, 55, 70))]
    print(f"w={w:+.2f}: {'tau_f=%.4f' % lend if fold else 'no fold<=30 '}  last sign flip per component {last}  root R(40,55,70)={np.round(R,3)}  /n^1.5 corr={np.round(corr,3)}", flush=True)
