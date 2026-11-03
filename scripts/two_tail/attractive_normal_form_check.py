"""Near-tie branch pairs: Lam, direction and amplitude ratios of real states (float64 evidence, NOT a Lean proof).

If a fold and a pair nearly coincide the curve is locally tau_c - tau = y^2 + a y + beta/y (normal_form_sign), whose three critical
values form an equilateral triangle at a = 0. Seen from the fold the pair then lies at +-30 degrees, Lam = ln(rho)/theta -> sqrt 3, and
a_s = sqrt(2 tau/p''(y_s)) gives |a_p/a_f| -> 1, with phases 180 and -60 degrees. The script prints the measured Lam, |A|, phase, and the lowest value
of the three-term Darboux form y(n) = 1 + 2 |A| exp(-Lam theta n) cos(n theta + phi). That form holds only for n >> 1/gap, so its lowest value
is not a statement about low orders; normal_form_sign compares the coefficients themselves.
Reads the smallest-Lam state of each worker from attractive_sign_margin.log.

Usage: attractive_normal_form_check.py LOG
"""
import sys, re, json
import numpy as np
sys.path.insert(0, '/home/rpan/YK_tail_FMSA/Lean_code/MSA_Convergence/scripts/two_tail')
import attractive_sign_margin as SM

if __name__ == '__main__':
    print('cmd:', ' '.join(sys.argv), '(float64 evidence, NOT a Lean proof)', flush=True)
    seen = []
    for l in open(sys.argv[1]):
        if not l.startswith('worker'): continue
        m = re.search(r'smallest Lam ([0-9.]+) .*? at z=(\[.*?\]) K=(\[.*?\]) eta=([0-9.e-]+)', l)
        if m: seen.append((float(m.group(1)), json.loads(m.group(2)), json.loads(m.group(3)), float(m.group(4))))
    for lam, z, K, e in sorted(seen, key=lambda s: s[0]):
        M = SM.margin(z, K, e)
        t, ap = min(M['terms'], key=lambda q: abs(q[0])); tf = M['tf']
        A = ap/M['af']; th = abs(np.angle(t)); L = np.log(abs(t)/tf)/th
        nth = np.linspace(0, 40, 400001)
        lows = [float(np.min(1 + 2*abs(a)*np.exp(-L*nth)*np.cos(nth + np.angle(a)))) for a in A]
        print(f'Lam {L:.5f} (sqrt 3 + {L - np.sqrt(3):+.5f}) gap {M["gap"]:.3e} ratio {abs(t)/tf:.6f} direction {np.degrees(np.angle(t/tf - 1)):.3f} deg; '
              f'|A| {np.round(np.abs(A), 4).tolist()} phase/deg {np.round(np.degrees(np.angle(A)), 2).tolist()}; lowest y {np.round(lows, 4).tolist()}; consistency {M["cons"]:.1e}; z={np.round(z, 4).tolist()} K={[float(f"{v:.4g}") for v in K]} eta={e:.4f}', flush=True)
