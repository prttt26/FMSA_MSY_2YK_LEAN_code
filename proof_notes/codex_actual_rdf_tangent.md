# Actual RDF tangent renewal and local Lp

The user froze the foundation at 1.0.17 / 06e3268 on 2026-10-26. These
research declarations live in `MSAConvergence/ActualRDFTangent.lean`, under
`FMSA.Convergence.ActualRDFTangent`. They have not been merged into the
foundation. The single merge-back is deferred until research ends.

Let U be the existing `nonlinearCausalG`, K the existing
`nonlinearCausalKernel` (already containing its row-density factor), and F
the existing `nonlinearGSource`. All rates, densities and diameters are fixed;
p and v denote actual BH amplitude data and an arbitrary amplitude direction.

`actual_tangent_renewal_integral` proves, for every finite r >= 0,

    delta-U_ij(r) = delta-F_ij(r)
      + sum_m integral_0^r [K_mj(r-t) delta-U_im(t)
                            + delta-K_mj(r-t) U_im(t)] dt.

Each delta is the actual Frechet derivative at p applied to v. The proof
needs no BH root, residual-kernel premise, root curve, or small-kernel norm.
It uses the unconditional compact Volterra inverse proved in foundation
1.0.17. `parametrized_solve_fderiv` applies the genuine chain rule to the
actual kernel and source families. Bounded radial evaluation identifies the
compact Banach derivatives with the original scalar actual constructors.
Matrix multiplication order and the transpose used by the existing renewal
are preserved. Both summands are proved interval-integrable; no derivative
of a nonintegrable default integral is treated as physical information.

For pair contact a = edgeHi sigma i j > 0, the actual existing
`JacobianExterior.hVariation` satisfies

    r * delta-h_ij(r) = 0                         (0 < r < a),
    r * delta-h_ij(r) = delta-U_ij(r-a)            (r >= a).

The causal and excess derivatives agree because their affine background is
fixed in p. The actual h derivative exists by foundation 1.0.17; it is not
postulated here. Varying amplitudes does not move the hard-core breakpoint.

`actual_weighted_hVariation_memLp_compact` proves radius-weighted delta-h
belongs to every Lp on [0,R], for every finite R >= 0, including exponent 2 and
infinity. A bounded scalar continuous function obtained from the compact
Banach derivative supplies the bound internally. The fixed core indicator
is measurable, and equality to the actual h tangent is proved a.e. No
canonical-state or integrability hypothesis is supplied for this local result.

## Remaining analytic steps

This is a linearized Baxter renewal theorem, not the tangent spectral OZ
identity. The actual causal G and its genuine amplitude tangent now have internally
computed global exponential order and honest Laplace integrals in a far
right half-plane; `RDFExponentialOrder` also proves the integrated actual
matrix tangent renewal. See `codex_rdf_exponential_order.md`. This allows
growth: Fourier boundary control and global actual h-tangent L2 remain open. The finite Yukawa-pole errors now have an actual off-root residual
factorization and genuine Jacobian-kernel cancellation in `PoleResidual`
and `ResidualJets`; see `codex_pole_residual.md`. The complete finite Wronskian coefficient tangent is now proved in
`NormalizedWronskianJets` under positive rates and nonzero free volume. Its
complex rational/source part and actual spectral C tangent symmetry are now
proved in `ComplexWronskianJets`. The genuine ordered-radial DCF
variation/Fourier identification is now proved in `RadialDCFTangent`; see
`codex_actual_primitive_tangent.md` (fe7c940). Full actual h-tangent spectral
OZ remains open: knowing OZ at isolated roots does not determine derivatives
in arbitrary Jacobian-kernel directions. Canonical tangent-factor uniqueness, amplitude
recovery and general canonical continuation remain open. No universal
real-root/Taylor-convergence equivalence or physical positivity is asserted.

Validation entry: `python3 scripts/check_project.py`. It compiles only this
package, against read-only validated foundation imports, and records exact
compiler footprint guards plus source/artifact hashes in `results/lean/`.
No foundation files or shared dependency build artifacts are written. No TeX
is written. The actual compiler result is recorded in `results/lean/validation.json`.

Verified checkpoint (package 0.1.0): 21 exact std3 theorem guards; the
research module and root compiled successfully. The independent validator
reports PASS and foundation_unchanged=true, with no shared dependency
build invoked. Foundation pin:
`09ade0691482098319e832c6c721b77ef70d99bb76cec5bc84b498357dd9219c`.
The default foundation build was not rerun or rewritten.
