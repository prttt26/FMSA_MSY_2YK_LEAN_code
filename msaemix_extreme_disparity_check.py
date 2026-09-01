#!/usr/bin/env python3
"""Task #70 — is there an extreme size-disparity corner for the mixture g-side (33')?

MP6's overlap hypothesis (hcond) is  -edgeHi_il < edgeLo_lj  with the Lean orientation
  edgeHi sig a b = (sig_a + sig_b)/2 ,  edgeLo sig a b = (sig_b - sig_a)/2 .
So  -edgeHi_il < edgeLo_lj  <=>  -(sig_i+sig_l)/2 < (sig_j-sig_l)/2  <=>  sig_i + sig_j > 0
(the sig_l CANCELS).  Claim: this holds for ALL triples & ALL positive diameters => NO corner;
MP6 already closes the g-side for every unequal-sigma case.  (My earlier 'sig_j < sig_i+2sig_l'
used a flipped edgeLo_lj=(sig_l-sig_j)/2 and is spurious.)

Random sweep over extreme diameter ratios confirms the physical Baxter support floor
edgeLo_lj never dips below the RDF hard-core reach -edgeHi_il.
"""
import numpy as np

def edgeLo(sig, a, b):  # Lean: (sig_b - sig_a)/2
    return (sig[b] - sig[a]) / 2.0
def edgeHi(sig, a, b):  # Lean: (sig_a + sig_b)/2
    return (sig[a] + sig[b]) / 2.0

rng = np.random.default_rng(0)
worst_margin = np.inf
n_triples = 0
n_violation = 0
for trial in range(200000):
    N = rng.integers(2, 5)
    # extreme ratios: diameters spanning up to ~1000x
    sig = 10.0 ** rng.uniform(-1.5, 1.5, size=N)
    for i in range(N):
        for j in range(N):
            for l in range(N):
                margin = edgeLo(sig, l, j) - (-edgeHi(sig, i, l))   # want > 0
                worst_margin = min(worst_margin, margin)
                n_triples += 1
                if margin <= 0:
                    n_violation += 1

print(f"random sweep: {n_triples} triples over 200k mixtures, diameter ratios up to ~1000x")
print(f"  min margin  edgeLo_lj - (-edgeHi_il)  = {worst_margin:.6e}   (> 0 everywhere)")
print(f"  violations (margin <= 0): {n_violation}")
print()
# the algebraic identity: margin = (sig_i + sig_j)/2, independent of sig_l
sig = np.array([1.0, 4.0, 0.3])
for (i, j, l) in [(0, 1, 0), (0, 1, 1), (2, 1, 0), (1, 0, 2)]:
    m = edgeLo(sig, l, j) + edgeHi(sig, i, l)
    print(f"  sig={list(sig)} (i,j,l)=({i},{j},{l}): margin={m:.4f}  == (sig_i+sig_j)/2={(sig[i]+sig[j])/2:.4f}")
print()
print("=> hcond (-edgeHi_il < edgeLo_lj) == (sig_i + sig_j > 0), ALWAYS true for positive diameters.")
print("=> NO extreme-disparity corner. MP6 closes the g-side (33') for ALL unequal sigma.")
