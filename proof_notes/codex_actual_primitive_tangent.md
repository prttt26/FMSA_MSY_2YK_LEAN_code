# Actual primitive and ordered radial DCF tangent bridge

Research package: `Lean_code/MSA_Convergence`, over the immutable foundation
1.0.17. Modules: `MSAConvergence/ActualPrimitiveTangent.lean` (19 theorems)
and `MSAConvergence/RadialDCFTangent.lean` (15 theorems). No foundation or
TeX file is changed. The research remains outside the SI.

## Mathematical scope

Write p=(Dt,G) for the actual amplitudes and v for an arbitrary amplitude
direction. P(p,r) is the existing full reflected Baxter primitive, represented
by `BaxterWeakJetBasis.actualPrimitive` as a real field. Its finite dictionary
includes the two linear factor terms and every density-weighted quadratic
cross-correlation. Neither tails nor the lower-edge jump are discarded.

`primitiveVariation` is D_p P(p,r)[v], using Lean's genuine real Frechet
derivative. `primitiveVariation_complex_fderiv` identifies its complex cast
with the derivative of the existing full complex `baxterPrimitive`. The
radial derivative is the existing `JacobianExterior.correlationVariation`;
the all-pair physical convention is the existing
`JacobianExterior.orderedVariation`, the derivative of
`orderedRadialCorrelation`. No new surrogate DCF is introduced.

At arbitrary amplitudes, positive rates and nonnegative diameters:

- `actualPrimitive_contDiff` proves actual amplitude regularity at every r.
  `primitiveVariation_eq_basis` differentiates the full dictionary, and
  `primitiveVariation_integrable` proves the genuine primitive variation is
  L1 on the whole real line.
- `actualPrimitive_fourier_basis` identifies the full Fourier integral with
  the actual spectral Baxter C. `actualFourierC_all_frequency_contDiff` and
  `primitiveVariation_fourier` prove genuine derivative/integral interchange
  at every real k, including zero. `primitiveVariation_fourier_transform`
  retains exactly the convention k=2*pi*w for mathlib's Fourier transform.
- Every basis function is continuous away from the possible lower-edge jump;
  the quadratic cross-correlations are continuous everywhere.
  `primitiveVariation_ae_continuous` supplies the regularity required by the
  frozen Fourier injectivity theorem, rather than assuming it.
- `correlationVariation_radius_eq_basis` and
  `correlationVariation_radius_integrable` prove the actual r*delta c is L1
  on the positive axis. The DCF scalar amplitude derivative exists at every
  nonzero radius, as proved in `rootCorrelation_contDiff`.

At an actual symmetric-strength BH root with nonzero free volume and a
vector in the actual fixed-coupling amplitude Jacobian kernel:

- `actual_kernel_primitiveVariation_reciprocity` combines the established
  nonzero-frequency spectral C tangent symmetry with whole-line L1 Fourier
  injectivity. Continuity of the Fourier transforms supplies the missing
  frequency zero; no rational source is evaluated at its pole.
- `actual_kernel_fourierC_fderiv_symmetric_all` extends the actual spectral C
  derivative symmetry to every real frequency, including zero.
- The full primitive reflection law holds off-root and survives genuine
  amplitude differentiation. Combined with reciprocity it gives
  `actual_kernel_primitiveVariation_even`, an almost-everywhere evenness
  theorem for the actual primitive tangent.

## Why radial differentiation is legitimate

The frozen root-only radial Fourier theorem cannot simply be differentiated
along an arbitrary Jacobian-kernel vector: such a vector need not integrate
to a curve of roots. The new proof first establishes the needed integrated
identity at **every amplitude**.

For an ordered pair sigma_j <= sigma_i, `correlation_radius_integrable_offroot`
uses the complete fixed radial dictionary to establish positive-axis L1 of
r*c(p,r). The existing right primitive is L1 and has derivative
-2*pi*r*c(p,r) off contact, so integrability of both the function and its
derivative on a tail gives `rightPrimitive_tendsto_zero_offroot`. Contact
continuity and this decay prove `actualPrimitive_cosine_offroot`:

    integral_(r>0) P(p,r)*cos(k*r)
      = (2*pi/k) * integral_(r>0) r*c(p,r)*sin(k*r),   k != 0.

No root premise is used. The finite dictionaries, with fixed integrable
cosine/sine weighted basis functions, prove smoothness and actual
Frechet differentiation under both integrals. Thus
`primitiveVariation_cosine` gives the same identity for delta P and delta c
at arbitrary amplitudes. This is a first amplitude derivative statement;
it does not assert arbitrary coupling-order Fourier interchange.

At a root/kernel vector the actual delta P is a.e. even and globally L1.
The whole-line Fourier/cosine identity then supplies the second factor of 2.
Consequently `actual_kernel_fourierC_fderiv_eq_radial_ordered_pair` proves

    D_p spectralBaxterC(p,k)[v]
      = (4*pi/k) * integral_(r>0) r*delta c(p,v,r)*sin(k*r),  k != 0,

with the real radial integral cast into the complex codomain. For every
species pair, `actual_kernel_fourierC_fderiv_eq_ordered_radial` selects the
existing ordered DCF variation; in the other ordering it uses the proved
spectral C tangent symmetry and applies the ordered-pair theorem to (j,i).

## Exact assumptions and limits

The final all-pair radial theorem requires finite species and tails, positive
rates and **positive diameters**, nonzero free volume, symmetric prescribed
strengths K, an actual root at t*K and an actual amplitudeJacobian kernel
vector. It permits repeated rates, zero component densities and arbitrary
coupling t. It assumes no Jacobian inverse, root curve, unknown-amplitude
symmetry, canonical-state property or small-kernel budget.

The radial identity is for k!=0: the existing `radial_fourier` definition is
(4*pi/k) times a sine integral and does not encode the physical k=0 limit.
The primitive Fourier identity and spectral C symmetry separately include
zero frequency. For unordered pairs the result uses the existing ordered
radial variation; it does not assert an unproved identity for the unselected
raw correlation variation.

The primitive's global L1 and the positive-axis L1 of r*delta c do **not**
prove global L1/L2 of the actual h tangent. Full tangent spectral OZ, global
actual h-tangent L2, canonical factor recovery/amplitude uniqueness, general
no-fold continuation and tail-shape/global Taylor-convergence classification
remain open. Real-root existence is not asserted to imply universal Taylor
convergence.

## Reproducible validation

Use `python3 scripts/check_project.py`; it runs the pinned installed Lean
compiler directly, never a shared dependency build. Every theorem carries
an exact `#guard_msgs`/`#print axioms` report read from the compiler. The 34
new reports use only propext, Classical.choice and Quot.sound. Full package
results, source/artifact/command/log hashes and foundation before/after audits
are in `results/lean/validation.json` and `results/lean/build.log`.

Verified isolated checkpoint (2026-10-28): PASS, 150 exact std3 guards
across eleven research modules plus the root. All source/artifact/log hashes
match the validation ledger; the foundation before/after audits are identical.

The foundation lock covers 530 source/configuration hashes; the current
research imports six directly validated FMSAPaper artifacts. Frozen manifest:
`09ade0691482098319e832c6c721b77ef70d99bb76cec5bc84b498357dd9219c`.
The coordinated merge back remains deferred until research is finished and
the session is about to close.
