# Independent all-wave audit of the M1/M3 first-loss brackets

Claude handoff173 / commit d8efa3a regenerated the EXTERNAL Fourier
certificates from167 with a compressed march on the same PY-seeded chains.
The new independent full replay passed at 384-bit Arb precision. This is
**not a Lean proof**; no saved numerical enclosure is a premise of a Lean
theorem or validation command. The current receipt binds 25 current inputs,
including the independent replayer and the separate rational checker.

## Result and exact scope

The physical scalar Fourier factor is nonzero for EVERY real wave number on
EVERY saved required slab box covering the seeded branch through tau_lo.
Combined with the separately audited continuous root chain, the actual
canonical HS seed and the proved path-to-canonicity interface, this certifies
full canonicity on [0,tau_lo] and places its first loss in (tau_lo,tau_hi).
The conclusion remains an external analytic certificate for these two controls.

| Control | required slabs | hull records | frequency steps fully replayed |
|---|---:|---:|---:|
| M1 | 1560 | 75 | 10327 |
| M3 | 657 | 481 | 47822 |
| Total | 2217 | 556 | 58149 |

The earlier uncompressed checkpoint replayed 456510 steps and remains
reproducible at commit3471b0c. Its old receipt verifies those historical
bytes; it does not verify the regenerated173 files. The new receipt replaces
it for the current compressed data and includes ten negative controls per
state, with all 58149 point enclosures recomputed.

The brackets and physical data are the exact rationals in the pinned source
records, not rounded display values. No first-loss frequency, uniqueness of
the bracketed zero, RDF positivity or Taylor/complex radius is certified.
In particular, invertibility of the amplitude Jacobian alone is not used as
a replacement for full canonicity, and F0>0 alone is not the criterion here.

## Actual physical dictionaries and the independent computation

The source mapping is to `BHResidualPolynomials.eval_qpPoly`, `eval_aPoly`,
`eval_wPoly` and `eval_cPoly`, and the frozen MatrixQ0 physical coefficients.
For one species, sigma=1, rho=6*eta/pi, the literal six polynomials
(qp,A,W1,W2,C1,C2) have support {1,D1,D2,D1*G1,D2*G2}. The new script
independently derives their coefficient rows; it imports NO `two_tail`
implementation. Exact symbolic checks verify this support and the genuine
zero-moment identity F(0)=A/(2*pi). Numerical coefficient overlaps are only
consistency diagnostics, not a claimed formal polynomial-identity proof.

The frozen `MSAMultiTailMixtureBaxter.q`, specialized to this geometry, is

    r<0: q=0;
    0<=r<=1: q=qp*(r-1)+A*(r-1)^2/2+sum(W*exp(-z*r)+C);
    r>1: q=sum(W*exp(-z*r)+C*exp(-z*(r-1))).

Integrating these literal terms gives the saved Fourier closed form for
s=i*k at k!=0 (`fourierQ_eq_QhatComplex`). At k=0 the integrated moments,
not division by zero in that quotient expression, give the correct value.
The real q also gives F(-k)=conj(F(k)), so k>=0 suffices.

For each exact rational hull U, the independent evaluator expands every
bilinear polynomial about its EXACT midpoint. It bounds the four linear
terms and two mixed terms by their full triangle radius. This is separate
from the generator's generic multivariate Taylor evaluator and96-bit
rounded center. Coefficient budgets use exact Fraction endpoint arithmetic;
per-frequency polynomial bounds use Arb at384 bits, with rho multiplied
into the coefficients before interval evaluation.

For k<=1/2, the integral exponential series is truncated after n=99; both
values and genuine k derivatives receive a common rigorous2^-500 error.
The exact check 2/(2^99*99!)<2^-500 bounds the worst derivative tail by its
geometric majorant. For larger k the direct closed forms and their actual
k derivatives are used. Exact symbolic differentiation checks these formulas
and their removable zero limits. The generator used70 terms/256 bits and
a looser remainder; its implementation is not used by this replay.

Every stored lower bound m<=|F| is checked against the Euclidean distance
of the recomputed Re/Im rectangle from zero. Every stored d>=|F'| is checked
against the L1 sum of the recomputed derivative component magnitudes. All
six coefficient upper bounds, q(0+) upper bounds and density enclosures are
also recomputed, rather than accepted from the input JSON.

## Why the finite records cover all wave numbers

The triangle second-moment bound follows directly from the piecewise q:

    sup |F''| <= rho*integral r^2*|q(r)| dr
      <= rho*(|qp|/12+|A|/60
           +sum(2*|W|/z^3+|C|*(1/3+1/z+2/z^2+2/z^3))) <= L2.

The middle inequality, rather than equality with the absolute moment, is
the safe statement when the terms have different signs. Finite exponential
moments justify differentiation under the Fourier integral. Taylor's
integral remainder then gives |F(k+h)|>=m-d*h-Li*h^2/2>0 throughout each
saved frequency step. Here Li=L2 at k=0, and Li=min(L2,H2(k)) at k>0.
Both candidates uniformly bound the true second derivative throughout the
whole forward step. Independent Fraction arithmetic checks every step,
dimensions, positive budgets and coverage from0 without gaps.

The independent replay derives the new decreasing curvature bound in a
grouped positive inverse-power form. Put ZC=sum(z*|C|), Z2C=sum(z^2*|C|):

    H2(k)=rho_upper*((|qp|+ZC)/k^2
      +(6|qp|+2|A|+2sum|W|+6sum|C|+4ZC)/k^3
      +(12|qp|+12|A|+2Z2C)/k^4+24|A|/k^5).

Every coefficient is nonnegative, so H2(k_left) is an upper bound at every
larger positive frequency. Four exact symbolic second-derivative identities
are checked independently. For the C basis, its four displayed terms give
z/k^2+2z(2k+z)/k^4+2/k^3+4/k^3, using |exp(-ik)|=1,
|ik+z|>=k and |2ik+z|<=2k+z. Exact algebra reduces this to
z/k^2+(6+4z)/k^3+2z^2/k^4. The qp/A/W terms follow their separately checked
second derivatives. This is a global triangle argument at every k,z>0;
a random floating test is not used. The171 alternative C bound is not
assumed to dominate or be dominated by this one.

At high frequency collect the1/s terms of the actual Fourier expression.
Their coefficient is q0=-qp+A/2+sum(W+C). The remaining terms give

    |F-1| <= rho*(|q0|/k+B2/k^2+2*|A|/k^3),
    B2=2*|qp|+|A|+sum(z*(|W|+|C|)).

Here |i*k+z|>=k and |exp(-i*k)|=1. Each final cutoff K satisfies the bound
strictly below1/2, and the positive terms decrease for k>=K. Every required
slab has complete frequency coverage ending in such a tail. Required slabs
are reconstructed from exact tau_lo/p_star comparisons, not trusted labels;
every saved hull must contain all its member amplitude boxes.

## Seeded branch and strict first-loss localization

`results/certificates/codex_py_seeded_chain_audit.json` remains a separate
dependency. Every one of its input hashes is rechecked. Its validated scope
includes actual original BH roots, continuity, seed/link/chart matching,
positive M1 coupling derivative, and the same-branch zero-frequency sign
change in (tau_lo,tau_hi). Its old receipt is NOT silently widened here.

`ScalarCanonicalSeed.actual_scalar_hs_canonical` discharges the actual seed.
`CanonicalFirstLoss.canonical_path_of_physical_factor_units` takes the
connected continuous path and all-real-wave-number factor units; its
hypotheses now have external numerical evidence on [0,tau_lo]. Full
canonicity is open in amplitudes, so continuity extends this canonical
prefix slightly beyond tau_lo. The later actual zero at some tau_z<tau_hi
is noncanonical. The first exit of the initial canonical component therefore
lies strictly between tau_lo and tau_hi. This does not identify its wave
number or exclude additional zero contacts inside the bracket.

No kernel numerical instance is claimed. That still requires kernel proofs
of the analytic bounds AND the PY chain, not merely a JSON import or a
conditional theorem restating those bounds as hypotheses.

## Reproduction and controls

From the research package, with python-flint0.6.0 and SymPy1.13.2:

```sh
PYTHONPATH=/tmp/codex_fmsa_arb_deps /opt/anaconda3/bin/python3 scripts/certificates/codex_first_loss_arb_audit.py --controls M3 M1 --negative-controls --output results/certificates/codex_first_loss_arb_audit.json
```

The receipt records exact hashes of its script, all input certificates,
the prior audit, generator/model sources and relevant actual Lean definitions.
Every input is checked again before writing PASS. `--sample` is diagnostic
only and cannot write a receipt. All reported counts above are full replay.

Each control rejects ten modified inputs: a missing required slab, a
missing final record, an inflated march step, understated L2, negative q0,
coverage starting above zero, an inflated actual |F| lower bound, zero actual
|F'| budget, an understated actual |C1| upper bound and a tripled H2-limited
step. The false point/coefficient budgets fail the fresh analytic computation;
the selected tripled step fails its exact quadratic margin before a later
ordering check. Python -O refuses execution and writes no receipt.

The full numerical replay ran in an isolated temporary tree while the Lean
compiler inputs were locked. Its script and receipt were promoted byte for
byte only after both processes actually exited0. All 25 input hashes were
then independently checked against the real tree; the script's self hash
matches the exact promoted bytes. No sampled run or rewritten provenance
record was used, and no numerical replay was repeated just for promotion.

The accompanying actual Fourier derivative/moment/closed-step extension
passed 1127 exact guards /103 research modules plus root /104 commands.
Independent auditing verifies every source/input/artifact/raw-log hash,
ALL100 prior module fingerprints,530 frozen hashes and all9paper/2raw/9Mathlib
pins unchanged. The external replayer builds no Lean dependency. No new
mathematical axiom, frozen-foundation/TeX write, Claude-owned file edit or
merge-back. General matrix escape, nonisolated relevant endpoints and
multitailed Taylor LOWER bounds/classification remain open.
