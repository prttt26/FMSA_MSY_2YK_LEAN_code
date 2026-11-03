# Independent audit of the M1/M3 PY-seeded chains

**Subsequent result:** `codex_first_loss_arb_audit.md` records an independent
full384-bit all-wave replay of Claude167 and first-full-canonicity-loss
localization. That is a separate EXTERNAL certificate. The historical chain
receipt below retains its original narrower scope and hashes. The later M2
curvature/bifurcation work is also now kernel proved; see
`codex_m2_local_bifurcation.md` for the1099-guard checkpoint.

Claude handoff157 supplies new EXTERNAL Arb certificates connecting the M1
and M3 zero-frequency sign-change brackets to the analytic continuation from
the PY/HS seed. The independent audit here passed. This is not a Lean proof,
and none of these numerical bounds is a premise of the Lean validation.

## Evidence and reproduction

`scripts/certificates/check_py_seeded_chain_rational.py` implements the audit.
Its exact interval operations come from the earlier Codex Fraction engine,
not from Claude's chain generator/checker. It checks all dimensions, ordered
intervals, centers inside boxes, exact dyadic preconditioners, source/model/code
pins, weighted row sums and strict Krawczyk self-maps. Every slab, link, switch,
seed and endpoint inclusion is checked, together with exact parameter tiling,
required A positivity and the positive M1 d(tau)/d(Dt1) bounds.

```sh
python3 scripts/certificates/check_py_seeded_chain_rational.py
PYTHONPATH=/tmp/codex_fmsa_arb_deps python3 scripts/certificates/check_py_seeded_chain_rational.py --replay-arb --negative-controls --output results/certificates/codex_py_seeded_chain_audit.json
```

The second command uses 320-bit Arb arithmetic. The analytic evaluation is
a fresh replay of the PINNED generator model, not another independent analytic
implementation. It compares the four symbolic residuals against the earlier
independent Codex model at eta=49/100 before numerical work. It verifies the
HS seed denominators do not vanish, rederives the exact G expressions, and
checks that fresh seed G enclosures lie inside the saved enclosures.

For every saved witness, the complete f(center), J_y(B) and R_p(B) enclosures
are recomputed. Fresh enclosures must be CONTAINED in the saved intervals,
which is stronger than merely intersecting them. A is replayed on every
slab box and both endpoint boxes. No new Newton search or preconditioner
selection is performed, and no Claude-owned file is changed.

The saved audit receipt is
`results/certificates/codex_py_seeded_chain_audit.json`; all its recorded input
hashes must still match before relying on it. Existing dependencies are
python-flint0.6.0 and SymPy1.13.2, with the optional helper path above.

| Control | tau slabs | Dt1 slabs | links | switch | replayed witnesses | weighted q upper |
|---|---:|---:|---:|---:|---:|---:|
| M1 | 238 | 1325 | 1561 | 1 | 3127 | 0.549457331913 |
| M3 | 664 | 0 | 663 | 0 | 1329 | 0.500137430010 |

The displayed q bounds round UP from exact Fraction values. In total,
4456 witnesses give106944 scalar f/J_y/R_p enclosures. Another2231 A boxes
and four seed G enclosures are replayed. Every M1 Dt1 slab has a strictly
positive certified coupling derivative, uniformly >4.049e-7; the exact
minimum of the certified lower bounds is in the receipt. Handoff157's
"at least4.05e-7" rounds that lower bound upward: the recomputed minimum is
approximately4.04903470964e-7. Use >4.049e-7 instead. This display correction
does not change positivity or any stored numerical certificate.

## Why this certifies the claimed branch and first zero-frequency zero

For each fixed parameter, the strict Krawczyk self-map and the weighted norm
q<1 give a unique root in the slab's unknown box. The same derivative defect
gives an invertible unknown-coordinate Jacobian. The centers must lie in the
box: otherwise the stored derivative enclosure need not control the segment
used in the mean-value argument. This condition is explicitly checked here.

The tiny link roots lie inside both adjacent boxes at exactly their common
parameter value. Local uniqueness therefore identifies the roots and glues
the analytic graphs. The initial exact Dt=0,tau=0 root is the HS seed. For M1,
the fixed-tau switch root lies inside both graph charts. On every subsequent
Dt1 slab, d(tau)/d(Dt1)>0 makes the continued curve a graph over coupling.
The full4-by5 residual differential has rank4; its one-dimensional tangent
kernel has nonzero tau component. Consequently the four-amplitude partial is
invertible on this curve too, so this is regular continuation of the seed.

To conclude FIRST zero-frequency zero, A>0 must cover the WHOLE interval up
to tau_lo, not merely selected slabs or a positive endpoint. M3 has an exact
tau_lo break at slab656 (zero-based); the checker requires such a break.
For M1, all initial tau slabs have A>0 through tau_switch, and the positive
Dt1 slabs tile through an exact p_star break. The complete Dt1 range of the
tau_lo root box lies below p_star. Strictly increasing tau on the connected
Dt1 graph therefore covers every coupling up to tau_lo with A>0.

The tiny endpoint roots belong to those same graphs and have A signs +/−
at the exact tau_lo/tau_hi. Continuity gives a zero strictly between them;
positivity of the entire earlier prefix places the FIRST zero there. This
does not prove that the zero inside the bracket is unique.

## Negative controls and unchanged Lean evidence

Nine modified rational inputs were rejected: stale generator hash, reversed
residual interval, center outside its box, corrupted Jacobian interval,
missing link, flipped upper-endpoint A sign, displaced seed, missing required
A positivity and removal of the exact tau_lo break while keeping slabs
contiguous. Fresh Arb replay separately rejects zeroed parameter derivative
enclosures. Python -O exits1 immediately with RuntimeError. These controls
change in-memory copies or temporary execution only, never original data.

The Lean proof baseline remains1050 exact guards /85 modules plus root.
The complete existing validation record, all recorded Lean source/artifact/log
hashes, all530 frozen hashes and nine paper/eight Mathlib/two raw LeanCode
pins are unchanged. No Lean theorem, mathematical axiom, shared build,
foundation output or TeX file was changed by this numerical audit.

## Remaining obligations

PY-seeded here means analytic actual-root continuation from the HS seed.
It does not assert full canonicity throughout that continuation. A nonzero
Fourier frequency may lose stability before this zero-frequency bracket;
the M2 regular-but-noncanonical example shows why invertible amplitude
Jacobians do not settle that question. First all-wave/full-half-plane loss,
all-wave canonicity, uniqueness inside the bracket and Taylor/complex radius
claims remain separate. No universal real-root/Taylor equivalence follows.

The M2 actual second-derivative/positive-curvature work continues separately;
the generic linear-solution error prototype passed Lean in /tmp but is not
yet an integrated public theorem. Foundation1.0.17 stays frozen, and the
research package remains active and unmerged.
