# Genuine amplitude derivatives of actual global Laplace families

Research file: `MSAConvergence/ActualLaplaceJets.lean` (30 theorems), over
immutable foundation 1.0.17. This closes the whole-Laplace parameter-derivative
identification left open after `RDFExponentialOrder`, in a computed sufficiently
far right half-plane. It does not close the Fourier-boundary or global h-L2 gap.

## Fixed actual functions

Let Y be `nonlinearCausalG`, q be `nonlinearCausalKernel` including its
row-density factor, and F be `nonlinearGSource`. The parameters p=(Dt,G)
are the existing real BH amplitudes, with rates, densities and diameters
fixed. Every spatial delta is the existing genuine real amplitude Frechet
derivative at p applied to v. Neither a curve of roots nor a small physical
kernel budget is supplied.

## Source and kernel integral derivatives

`finite_complex_integral`, `finite_complex_integral_contDiff` and
`finite_complex_integral_fderiv` give exact integration and genuine parameter
differentiation of finite fixed complex L1 dictionaries. Actual basis
integrability is discharged internally on the open right half-plane:
kernel bases are bounded on r>=0, source bases have at most affine growth,
and the exponential damping controls both the constant and first moment.

`source_laplace_basis` and `kernel_laplace_basis` are off-root identities at
all amplitudes. `source_laplace_contDiff` and `kernel_laplace_contDiff` prove
the entire actual F/q Laplace families are C-infinity in the real amplitudes
at every fixed s with Re(s)>0. `sourceVariation_laplace` and
`kernelVariation_laplace` identify the integrals of the genuine spatial
amplitude derivatives with the true parameter derivatives of these global
Laplace families. There is no caller-supplied differentiation-under-integral
premise.

The explicit existing complex factor interfaces retain their normalization:

    Laplace(delta F)_ij = D_p J_ij(s)[v] / (2*pi),
    s * Laplace(delta q)_ij
      = rho_i * (D_p L_ij(s)[v] - exp(-s*sigma_i) * D_p J_ij(s)[v]).

These are `sourceVariation_laplace_eq_J_fderiv` and
`kernelVariation_laplace_rational`, valid for every Re(s)>0. Their integrated
inputs hold off-root before differentiation. Row density and fixed contact
phase are not commuted or omitted.

## A neighbourhood of honest G Laplace integrals

Pointwise exponential-order estimates with a direction-dependent rate alone
would not justify parameter differentiation of the whole integral. The new
proof constructs a common amplitude neighbourhood first.

`coefficients_locally_bounded` uses genuine smoothness of the full finite
BH coefficient vector to bound every coefficient in a neighbourhood of p.
`matrix_dictionary_uniform_bound` turns one coefficient envelope and fixed
basis bounds into one constant for every array in that envelope.
`actual_kernel_source_local_bounds` gives M,C>=0 such that, uniformly over
nearby amplitudes a and all r>=0,

    absSum(q_a(r)) <= M,
    absSum(F_a(r)) <= C*(1+r).

The already proved finite-interval maximum estimate then supplies one
computed exponential growth rate for every nearby Y_a. This is
`actual_causal_local_exponential_order`. No global supremum is presumed
finite; the underlying weighted renewal estimate obtains its maximum on
[0,R] before proving the bound independent of R.

`bounded_matrix_laplace_norm_sum` gives

    sum_ij norm(Laplace(q_a)_ij(s)) <= M/Re(s).

Consequently the actual renewal factor I-Laplace(q_a)(s) is a unit after
sufficiently strong computed damping. `actual_local_laplace_renewal_unit`
proves, in one parameter neighbourhood and a common far right half-plane,

    Laplace(Y_a)(s) * (I-Laplace(q_a)(s)) = Laplace(F_a)(s),

with every integral justified by the uniform bound and the proved complex
convolution/Fubini rule. These are actual global integrals, not merely
algebraic symbols or an identity restricted to BH roots.

## Genuine whole-family differentiation

The off-root identity and unit factor identify the actual Y Laplace family
locally with Laplace(F)*(I-Laplace(q)) inverse. The inverse is proved smooth
entrywise from the finite permutation determinant, finite adjugate and
scalar reciprocal determinant. No norm instance on the amplitude space is
changed. `actual_causal_laplace_contDiffAt` proves C-infinity in amplitudes
for every actual Y transform entry throughout a constructed right half-plane.
The result is local at p; no claim is made about amplitudes outside that
neighbourhood, where a fixed transform may fail to be integrable.

`matrix_renewal_family_fderiv` differentiates the genuine local off-root
identity, keeping the two matrix orders:

    D_p Laplace(Y)[v] * (I-Laplace(q))
      = D_p Laplace(F)[v] + Laplace(Y) * D_p Laplace(q)[v].

The earlier actual integrated spatial tangent satisfies exactly this equation.
Source/kernel derivative interchange identifies both right sides; the unit
fixed renewal factor makes the two responses equal. Thus
`actual_causalVariation_laplace_fderiv` proves the desired global integral
parameter-derivative interchange in a constructed right half-plane, without
assuming any derivative of a nonintegrable default integral is physical.

Finally `actual_causal_laplace_fderiv_all_directions` takes a finite basis of
the actual amplitude space, chooses cutoffs for its basis directions and
combines them with the smoothness cutoff. Linearity of the genuine spatial
and global Frechet derivatives, plus L1 integration of the finite sum, gives
**one cutoff depending on p, not on v**. For every s beyond it, the actual Y
Laplace family is smooth at p and every direction v has both:

- actual complex Laplace integrability of its genuine spatial tangent;
- integral of that tangent equal to the genuine whole-family derivative.

The prefactor in a pointwise growth estimate need not be uniform over
unbounded v; only the frequency cutoff is common to every direction.

## Exact scope and remaining obligations

The actual results require finite species/tails, positive rates and
nonnegative diameters. They allow repeated rates, signed/zero densities and
arbitrary amplitudes. No actual BH root, residual-kernel direction,
nonzero-free-volume, canonical state, root curve or physical small-kernel
budget is used. These are first amplitude derivative integral identities,
not an all-coupling-orders Fourier interchange theorem.

The G results hold in a computed sufficiently far right half-plane; source
and kernel identities hold on the whole open right half-plane. None proves
integrability at Re(s)=0, decay, actual h-tangent global L2, full Fourier-boundary
tangent OZ, canonical factor/amplitude recovery or general no-fold. Those
remain open, as does the general tail-shape/Taylor-convergence classification.
No Wiener inverse axiom or universal real-root/Taylor equivalence is used.

## Reproduction

Use `python3 scripts/check_project.py`. The checker invokes the pinned Lean
binary directly, never a shared dependency build; all theorem footprints
are guarded against the actual compiler reports. It audits the 530 frozen
source/configuration hashes and six direct validated FMSAPaper artifact pins
before/after and records source/artifact/command/log hashes in `results/lean/`.
Foundation and TeX remain untouched; the research stays outside the SI.

Verified isolated checkpoint (2026-10-28): PASS, 212 exact standard-three-axiom
guards across thirteen research modules plus root, including 30 new guards
here. Every source/artifact/log hash matches the ledger; the 530 frozen
source/configuration hashes and six direct validated import artifact pins
are unchanged before/after. No shared dependency build. Foundation manifest:
`09ade0691482098319e832c6c721b77ef70d99bb76cec5bc84b498357dd9219c`.
