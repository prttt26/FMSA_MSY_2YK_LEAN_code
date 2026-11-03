# Independent audit of the M3 Arb recheck (2026-10-29)

This is EXTERNAL SymPy/Arb evidence and exact rational certificate checking,
not a Lean proof. No new mathematical axiom, Lean source or compiler artifact
is introduced. The existing 966 exact theorem guards remain unchanged.

## Model and reproducible inputs

Claude 147, commit `788dece`, supplies
`scripts/two_tail/two_tail_m3_arb_recheck.py` and
`results/two_tail/two_tail_m3_arb_recheck.json`. Physical data are exactly
eta=49/100, sigma=1, z=(7,14), K=(1,-419/384), rho=6*eta/pi.
The four unknowns are the ORIGINAL (Dt1,Dt2,G1,G2). No residual rescaling,
finite differences or substitution X=Dt*G is used.

The generator differentiates its literal residual symbolically and encloses
the resulting polynomials by centered Taylor expansion of degree at most
three. This finite polynomial expansion has no omitted remainder. Arb encloses
pi and exponentials; subsequent matrix and Krawczyk arithmetic uses exact
Fractions from outward dyadic endpoints. The exact certificate from 142 is
used to choose boxes, centers and rational preconditioners, rather than as
the source of analytic f/J/A enclosures.

The new independent checker
`scripts/certificates/check_m3_arb_witness_rational.py` checks source JSON,
generator and both Lean model hashes, all matrix/vector dimensions, ordered
intervals, centers in box interiors, exact physical data, parameter matching,
all eight Krawczyk expressions, strict inclusions and norms. It uses Codex's
earlier exact interval implementation, not Claude's generator/checker.
The six original witnesses must have precisely their original boxes, centers,
C matrices and coupling intervals. The two NEW tiny endpoint witnesses must
have the exact bracket couplings and lie strictly inside the common box.

With `--symbolic`, the checker also compares the generator against Codex's
previous independent residual construction specialized to these M3 data:
all four residuals, all 16 amplitude derivatives and A agree EXACTLY under
SymPy expansion. The independent construction also checks the true removable
block limits and the honest zero-frequency identity F0=A/(2*pi). This does
not substitute s=0 into totalized rational expressions with removable poles.
These symbolic computations also remain external.

## Results and the precise conclusion

Fresh 256-bit replay agrees with the committed report in EVERY field except
the command string. A separate 384-bit run passes the same independent
checker. The maximal norm among all eight witnesses is bounded above by
0.0209422532074 (rounded UP), hence is strictly below 0.020943. The shortened
bound "<=0.02094" in 147 is too small to be a rigorous upper bound.
The original AD bound was at most 0.354549856640 (rounded UP).

The tiny endpoint boxes have relative radius 1e-40 and newly prove root
existence, rather than relying on root preservation through the original
unrecorded shrinking iterations. On those boxes A is strictly positive at
the lower exact coupling and strictly negative at the upper exact coupling.
Their magnitudes are approximately 1.084334e-12 and 4.468191e-12. The rational
endpoints in the JSON, rather than these displayed decimals, are authoritative.

The common parameter box carries a unique root for EVERY coupling in the
exact bracket. The uniform contraction and joint continuity give a continuous
root curve. Each tiny endpoint root is the unique root of that common box at
its own coupling. Thus the sign change is on ONE continuous root curve, and
there exists an interior coupling with A=0, hence physical F0=0.
This proves existence of a zero; uniqueness of the zero does not follow.

Intersection of the old AD enclosures with the new Arb enclosures is a
consistency check. Such intersection alone would not prove analytic validity
or root identity. The new analytic computation and the common-box uniqueness
are what establish this conclusion. No connection to the PY seed, first-loss
statement, canonicity, all-wave conclusion or Taylor radius follows.

## Reproduce

From the research package root, with python-flint 0.6.0 and SymPy 1.13.2 in
the existing read-only dependency directory:

```sh
python3 scripts/certificates/check_m3_arb_witness_rational.py
PYTHONPATH=/tmp/codex_fmsa_arb_deps python3 scripts/certificates/check_m3_arb_witness_rational.py --symbolic
PYTHONPATH=/tmp/codex_fmsa_arb_deps python3 scripts/two_tail/two_tail_m3_arb_recheck.py /tmp/m3_replay_256.json
python3 scripts/certificates/check_m3_arb_witness_rational.py /tmp/m3_replay_256.json
PYTHONPATH=/tmp/codex_fmsa_arb_deps python3 - <<'PY'
import sys
sys.path.insert(0, 'scripts/two_tail')
import two_tail_m3_arb_recheck as m
m.PREC = 384
sys.argv = [m.__file__, '/tmp/m3_replay_384.json']
m.main()
PY
python3 scripts/certificates/check_m3_arb_witness_rational.py /tmp/m3_replay_384.json
```

Ten ad hoc corrupted-report controls were rejected: endpoint A sign,
Jacobian entry, center residual, parameter interval, generator hash, Lean
model hash, matrix shape, reversed interval, physical weight, missing endpoint.
The strengthened checker has no Arb dependency unless `--symbolic` is used.
At the initial 147 audit the generator returned exit status zero even if its
computed PASS flag was false. Claude 149, commit `92c27f1`, fixes this and
rounds norm displays upward. Exact comparison with `788dece` shows that the
saved JSON changes ONLY the eight norm displays and generator hash; all exact
analytic bounds, rational witnesses and other fields are unchanged. Every
new display is at least its exact rational bound. Fresh 256-bit replay agrees
with the corrected report except for its command string and passes the
independent checker. Injecting false Krawczyk outcomes in a temporary process
(without editing either source) produces `passed=false`, exit status 1, and
a report rejected by the independent checker. This supersedes the original
exit-status warning. The checker should still be run after generation.

The analytic enclosure computation, SymPy algebra and the numerical-to-Lean
interface are not kernel checked. Foundation 1.0.17 and TeX remain untouched.
