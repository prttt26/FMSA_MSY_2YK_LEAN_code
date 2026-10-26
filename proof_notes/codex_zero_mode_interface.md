# Actual zero-frequency Baxter and radial interfaces

Date: 2026-10-26. Codex ownership. No manuscript TeX was edited.

## Definitions and scope

The actual `fourierQ` is a full-line Lebesgue integral and is meaningful at
zero wave number. In contrast, `QhatComplex` is a raw quotient expression,
and `HardSphere.radial_fourier` contains division by k. Their totalized Lean
values at zero need not be physical zero-frequency limits. Their definitions
and existing nonzero-frequency theorems are preserved byte for byte.

`FMSAPaper/BaxterZeroMode.lean` evaluates the actual integral at zero.
`FMSAPaper/RadialZeroMode.lean` defines the continuous physical symbol

    radialSymbol(c,k) = 4*pi * integral_(0,infinity) r^2*c(r)*sinc(k*r) dr.

It agrees with the existing radial Fourier expression when k!=0. At zero
it is the second radial moment, with no quotient convention. This is an
actual-model connection, not an assumption identifying a proxy with a DCF.

## Finite mixtures and finite tails

For positive tail rates and nonnegative diameters, with arbitrary real
amplitudes and arbitrary finite species/tail sets, `fourierQ_zero` proves

    integral q_ij(r) dr
      = -qp_ij*sigma_i^2/2 + A_j*sigma_i^3/6
        + sum_t [W_tij/z_t + C_tij*(sigma_i+1/z_t)].

The unequal lower and upper shifts cancel at zero frequency. The support
width is sigma_i. `core_zero_integral` and `row_zero_integral` separately
prove the polynomial and Yukawa pieces; existing L1 bounds justify all
finite integral sums. `fourierFactor_zero_entry` gives the actual
density-weighted matrix entry, without requiring a root.

`fourierQ_continuous` and `spectralBaxterC_continuous` prove continuity at
every real wave number for these actual finite-tail kernels. The dominating
function is |q|, since the Fourier phase has norm one.

At every actual BH root, `correlation_radius_sq_integrable_of_root` and its
ordered version prove absolute integrability of r^2*c. On the finite core,
the already proved L1 bound for r*c is multiplied by a bounded r. Outside
contact, the actual root closure gives a finite sum of exponentially
weighted linear terms, whose L1 integrability is proved. No moment premise
is left to the caller. The bound |sinc|<=1 then proves continuity of the
actual physical radial symbol by dominated convergence.

With strictly positive diameters, nonzero free volume and symmetric tail
strengths, `root_radial_symbol` identifies the actual spectral Baxter DCF
with this symbol for every real k. Existing nonzero-k identification gives
the equality away from zero; uniqueness of limits along k down to zero gives
the value at zero. `root_zero_moment` states this value explicitly.
`root_factor_gram_radial` substitutes it into the actual density-weighted
Gram identity for all real k, including zero, when densities are nonnegative.
No inverse structure factor, canonical uniqueness or Jacobian regularity is
assumed or concluded by this identity.

## One species, arbitrary finite tails

Substituting the actual `amplitudeA`, `amplitudeQp`, `W` and `C` into the
zero moment gives

    1 - rho * integral q = A/(2*pi).

`scalar_HS_balance` and `scalar_tail_balance` prove the hard-sphere and each
tail contribution algebraically; `scalar_zeroMoment_balance` sums them.
This identity needs nonzero rates and free volume, but no BH root or sign
assumption. `scalar_fourierFactor_zero` then gives the actual scalar F(0)
when rates are positive and density/diameter nonnegative.
`scalar_fourierFactor_zero_iff` proves F(0)=0 iff actual A=0.

The spectral denominator is the square `(A/(2*pi))^2` by
`scalar_spectral_den_zero`. At an actual one-species root, symmetry of the
strength matrix is automatic. `scalar_radial_den_zero` and its iff theorem
therefore give

    1 - rho * radialSymbol(c,0) = (A/(2*pi))^2,
    1 - rho * radialSymbol(c,0) = 0  iff  A = 0.

## One attractive tail: witness strictly inside the Taylor radius

`single_tail_amplitudeA_eq` checks the actual finite-mixture amplitude
normalization against the scalar AS used by `SingleTailSpinodal`.
`actual_single_tail_zero_before_radius` consequently produces a zero of the
actual determinant F(0) at a positive coupling strictly inside the common
Taylor radius, for every positive rate/density/diameter state with positive
free volume and positive attractive strength, and any continuous actual
PY-seeded root germ.

`actual_single_tail_zero_moment_before_radius` gives the same type of
witness entirely in terms of the actual ordered DCF:

    0 < tau < R_common,
    actual BH root on physBranch(tau),
    4*pi*rho * integral_(0,infinity) r^2*c(r;tau) dr = 1.

This uses the all-state 1.0.13 single-tail proof, not numerical evidence.
It does not identify the first zero or its wave number, prove RDF positivity,
or prove the general canonical-to-Jacobian implication. If the first
physical instability is defined by the initial canonical interval and its
first real-wave-number zero, the existence of this witness gives the
corresponding upper bound; that definition and firstness are separate.

## Reproduction and audit

Run from the package root:

    lake build
    python3 formalization/check.py
    python3 formalization/audit_downstream_imports.py --output /tmp/zero_mode_downstream_imports.json

The two modules add 28 exact theorem footprint guards. Every new theorem
has exactly `propext`, `Classical.choice`, `Quot.sound`; no new axiom is
introduced. Baseline 1.0.14 records the complete root import, 60 modules and
413 guards. Versioned build and compatibility evidence is recorded under
`formalization/results/baseline_1_0_14/`. The default foundation build passed
9072 jobs, the workspace and three compatibility targets passed 9193 jobs,
and the source/configuration audit passed 522 hashes. The manifest SHA256 is
`4a25e48e56e7ee49a879830e544883ee3d212a39963afcb74279829acc2ba709`. Independent
downstream proof builds are not represented as rerun by a dependency lock
check; their actual import impact and existing proof-source preservation
are audited separately.
