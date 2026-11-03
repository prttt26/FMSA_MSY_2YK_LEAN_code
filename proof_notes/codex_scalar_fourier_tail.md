# Actual scalar Fourier tail bounds

Full guarded validation AND independent post-run audit passed:
**1104 exact standard-three guards /100 research modules plus root
/101 pinned compiler commands.** All five actual new queries use only
propext, Classical.choice and Quot.sound. ALL99 prior module sources,
artifacts and footprints,530 frozen hashes and all9paper/2raw/9Mathlib pins
are unchanged. No new mathematical axiom is used.

## Mathematical statement

`ScalarFourierTail.lean` treats one species of unit diameter, any finite tail
set, strictly positive rates, arbitrary signed real coefficients qp,A,W,C,
and nonnegative density rho. Rates may repeat and tails may be inactive.
No root, amplitude inverse, positivity of coefficients, canonicity, density
cap or external analytic enclosure is assumed.

Write

    q0 = -qp+A/2+sum(W+C),
    B2 = 2*abs(qp)+abs(A)+sum(z*(abs(W)+abs(C))).

For the HONEST actual Fourier integral and every k!=0 the proof establishes

    abs(F(k)-1) <= rho*(abs(q0)/abs(k)+B2/abs(k)^2+2*abs(A)/abs(k)^3).

This is the explicit high-frequency estimate used by the independently
audited M1/M3 external certificates. Its leading term retains q(0+).
The derivation uses the frozen integral identification at NONZERO k;
the quotient formula is never evaluated at zero.

Five public declarations, in source order:

1. `fourierQ_norm_le`: the explicit three-term bound for the actual integral.
2. `factor_norm_sub_one_le`: the physical density-weighted scalar factor,
   including both signs of k and vacuum rho=0.
3. `factor_ne_zero_of_cutoff`: ANY K>0 whose actual coefficient budget is<1
   excludes every |k|>=K. The budget inequality remains explicit in this
   configurable certificate interface; no numerical instance is implied.
4. `factor_norm_lt_quarter_of_explicit_cutoff`: the DATA-CONSTRUCTED radius

       K = 1+4*rho*(abs(q0)+B2+2*abs(A))

   gives abs(F(k)-1)<1/4 for every |k|>=K, with no supplied bound or cutoff
   inequality. K>=1 follows from the computed nonnegative budgets.
5. `actual_tail_units_outside_explicit_cutoff`: substitutes the ORIGINAL
   actual BH amplitudeA, amplitudeQp, W and C and concludes MATRIX IsUnit
   for the actual physical1-by1 Fourier factor. No BH root is supplied.

## Actual dictionary and proof route

The scalar wrapper `factor` is definitionally an entry of the existing
`fourierFactor`, not a replacement observable. The squared sqrt-density
factors reduce to rho using nonnegative physical density. At the final
interface, one-species extensionality identifies all original amplitude
functions with their scalar coefficients, and the determinant/unit theorem
turns entry nonvanishing into an actual matrix unit.

For s=i*k and E=exp(-s), the exact algebraic decomposition is

    Phi(s) = q0/s + qp*(1-E)/s^2 - A/s^2 + A*(1-E)/s^3
      - sum((z*W+z*C*E)/(s*(s+z))).

The proof retains the original finite sums, without independence of
exponential bases. On the Fourier axis, abs(E)=1, abs(1-E)<=2 and
abs(s+z)>=abs(k). Triangle and quotient inequalities give the stated B2
budget. Positive rates are used by the actual Fourier-integral identification;
real-axis denominators are proved nonzero directly. Monotonicity of the
positive inverse powers gives the configurable cutoff theorem. For the
constructed cutoff, |k|>=K>=1 lets all inverse powers be bounded by1/|k|;
the explicit formula then gives the strict1/4 bound. This is an actual
computed tail, not an assumed frequency bound or finite-grid check.

## Validation and limits

All five ACTUAL axiom queries gave exactly propext, Classical.choice and
Quot.sound. Those compiler messages, including their exact wrapping, were
used to insert the guards. Three modified copied sources fail at mathematical
proof bodies before guard discrepancies: remove A/2 from q0, replace
2*abs(qp) by abs(qp) in B2, or replace the proved<1/4 target by<0.

The full checker discovers the new module from the root import and records
its actual footprints. No new external import or expression-generation
receipt is needed; the9 generated prefixes/37 pins remain unchanged.
The complete checker exited0, and the independent post-run audit verified
EVERY source/input/artifact/raw-log hash, all99 prior module fingerprints,
all530 frozen hashes and all existing import pins. The same9 generated
prefixes/37 pins and the external all-wave receipt's24 pins are unchanged.
Evidence: `results/lean/validation.json` and `results/lean/build.log`.
The pinned direct compiler commands are recorded there; no shared/Lake build
or foundation-cache write was invoked.

This closes the generic high-frequency analytic estimate for this scalar
geometry. It does NOT kernel-instantiate the M1/M3 coefficient enclosures,
finite-frequency m/d/L2 bounds, required slab boxes or PY root chains. Those
remain external, independently replayed certificates. High-frequency units
alone do not imply full canonicity, locate first loss or bound Taylor radius.
No new statement of universal real-root/Taylor equivalence follows.

General finite-mixture escape, positive-density fiber certificates,
nonisolated endpoint limits and multitailed complex Taylor LOWER bounds remain
open. Foundation1.0.17 and TeX stay untouched; research remains unmerged.
