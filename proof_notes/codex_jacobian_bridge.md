# Actual BH Jacobian support and matrix Parseval bridge

Date: 2026-10-26. Codex ownership. This note records partial progress toward
the general canonical-to-Jacobian implication, without assuming that
implication or adding an axiom. No manuscript TeX is edited.

## Why a root curve is insufficient

At a possibly singular solution, a vector in the residual Jacobian kernel
need not be the velocity of a differentiable curve of solutions. Even the
scalar residual R(x)=x^2 at x=0 has every direction in its Jacobian kernel,
while its only real root is zero. Therefore a theorem that identifies an
OZ/closure quantity on actual roots cannot, by itself, be differentiated
along every Jacobian kernel vector. The needed differential transcription
must be derived from off-root operator identities, or another argument that
does not already require Jacobian regularity.

`PhysicalExteriorJets` proves exterior identities along root families.
The new `JacobianExterior` module instead proves an identity at arbitrary
amplitudes, then differentiates that identity. It requires no root family,
canonical factor, tail signs, distinct rates, density positivity, free-volume
sign or actual BH root. Positive rates and nonnegative diameters suffice
for its integral identities. This addresses the exterior support part of
step 2 in the paper's instability-before-fold argument.

## Actual off-root exterior identity

Write p=(Dt,G), R(t,p) for the existing full BH residual, and

    L_ij,r(D) = sum_u [z_u*exp(-z_u*(r-R_ij))/(2*pi*r)] * D_uij.

`exteriorFunctional` is this finite continuous linear functional. For every
r>R_ij, `exterior_factorization` proves

    c_ij(r;p) = L_ij,r(firstLHS(p)),

where c is the existing convolution-defined actual DCF. The proof uses the
full-line actual convolution's exterior integral, the exact W/C cancellation
and unequal-edge geometry. No root equation is used.

`exterior_residual_decomposition` gives the corresponding defect identity

    c_ij(r;p) = t * sum_u K_uij*exp(-z_u*(r-R_ij))/r
               + L_ij,r(R(t,p).first).

Define J(t,p) by the actual `fderiv` of R composed with the amplitude
inclusion (delta-t=0). `exterior_hasFDerivAt` differentiates this identity:

    delta-c_ij(r) = L_ij,r((J(t,p)v).first).

Thus `kernel_exterior_zero` and the ordered variant prove delta-c=0 at every
r>R_ij whenever Jv=0. `kernel_curve_exterior_hasDerivAt` proves the same
zero derivative along every differentiable amplitude curve with velocity v;
that curve is not required to consist of roots.
`kernel_positive_variation_support` puts the zero extension of the positive
radial variation inside the compact interval [0,R_ij].

## Actual disjoint-support spatial pairing

The existing `nonlinearH` construction is identically -1 for 0<r<R_ij for
all amplitudes. `nonlinearH_core_hasFDerivAt` proves its amplitude derivative
there is the zero continuous linear map, so `hVariation_core_zero` holds for
every direction. This uses only the actual definition's hard core, not its
global OZ interpretation.

For a Jacobian kernel direction, delta-c*delta-h therefore vanishes off
contact on the positive radial axis. Contact is a Lebesgue null set.
`kernel_pairing_ae_zero` and `kernel_spatial_pairing_zero` prove

    sum_ij rho_i*rho_j * integral_0^infinity r^2*delta-c_ij(r)*delta-h_ij(r) dr = 0.

The product is genuinely a.e. zero; the result is not obtained from Lean's
zero convention for nonintegrable functions. The global differentiability,
L2 membership and OZ identity for this constructed h variation are NOT
established by the core calculation. Outside the core, `hVariation` denotes
the totalized Fréchet derivative; a later bridge must prove the relevant
actual differentiability and spectral identity rather than interpreting a
possibly zero default as a physical tangent.

## Matrix algebra and strict positivity

`MatrixOZPairing.linearized_OZ_solution` starts with

    (1+H)(1-C)=1,
    delta-H(1-C)-(1+H)delta-C=0,
    IsUnit(1-C),

and proves delta-H=S*delta-C*S with S=(1-C)^(-1), in the displayed order.
It never assumes matrix commutation.

For arbitrary complex D, define

    energy(S,D) = Re trace(D^* S D S).

`energy_eq_kronecker` identifies this with the quadratic form for
S^transpose tensor S on vec(D). Positive definiteness is preserved by
transpose and Kronecker product. `energy_nonneg`, `energy_pos` and
`energy_zero_iff` consequently prove nonnegativity and strict positivity
unless D=0. No Hermitian premise on D is needed. This also covers the common
imaginary phase of the one-dimensional odd radial Fourier lift. If D is
Hermitian, `energy_of_hermitian` recovers Re trace(D S D S) in the paper.

`ae_zero_of_integral_energy_zero` proves a.e. cancellation from pointwise
positive S, actual energy integrability and zero integral. A continuous
spectral matrix is then identically zero. Uniform coercivity is not needed
for this cancellation once the L2/integrability hypotheses are available.

`radialDenominator` uses the continuous actual radial symbol from 1.0.14,
including k=0. At actual symmetric-strength BH roots, nonnegative densities,
positive diameters/rates and nonzero free volume, its Gram factorization
implies it is positive definite whenever the actual Fourier factor at that
wave number is a unit. Its inverse `structureMatrix` is positive definite
as well. These two positivity theorems do not conclude Jacobian regularity.

## Matrix L2 Plancherel closes the positivity/Parseval engine

`MatrixOZParseval` works on any finite-dimensional real inner-product space
with its canonical volume, so it covers physical three-space and the
one-dimensional odd radial representation. Matrix entries U_ij,W_ij belong
to L2 of that space; `fourierMatrix` applies Mathlib's actual L2 Fourier
isometry entrywise. `integral_fourier_trace_pair` proves

    integral trace((Fourier U)^* (Fourier W))
      = sum_ij inner_L2(U_ij,W_ij).

Pointwise products are integrable by the L2 Cauchy-Schwarz theorem; finite
matrix sums commute with the integral under these proved L1 conditions.
The real-part version and `spatialPair_zero_of_disjoint` supply the exact
spatial/Fourier pairing transport.

`positive_OZ_pairing_injective` proves U=0 entrywise from:

- actual L2 entries U,W;
- pointwise-a.e. positive definite S;
- Fourier W=S*(Fourier U)*S a.e.;
- zero spatial L2 pairing.

Energy integrability is derived internally from the two L2 fields and their
spectral relation. No bound on S, simultaneous diagonalization, matrix
commutation or Fourier injectivity axiom is assumed. Mathlib's Plancherel
isometry gives zero Fourier norm and then U=0 in L2.
The actual-radial specialization discharges S positivity using the actual
BH root and Fourier factor. It retains the actual tangent spectral OZ
identity and L2 fields as explicit premises; it is not a no-fold theorem.

## Remaining obligations for the requested general theorem

1. Prove actual global differentiability/L2 control of the constructed h
   variation on a canonical BH state, and identify its weighted radial
   variation with the remaining L2 field. The c-side numerator bounds,
   radial Lp membership, exact odd L2 lift, L1/L2 Fourier agreement and
   physical k=2*pi*w normalization are now proved in baseline 1.0.16; see
   `proof_notes/codex_radial_variation_l2.md`.
2. Derive the tangent spectral OZ identity from the actual residual kernel,
   using a valid off-root/operator transcription. Merely knowing an OZ
   identity at actual roots does not discharge this step at a singular root.
   Current foundation nonlinear OZ results still require finite admissibility
   certificates and a sufficient kernel norm budget, not arbitrary canonicity.
3. Prove canonical factor uniqueness for the actual tangent and recover all
   BH amplitude variations. Unequal-diameter kernels have shifted lower
   supports; bounded half-plane arguments must use the correct diagonal
   recentering, not assume all original factor entries are bounded.
4. Supply the initial canonical branch continuation/endpoint argument for
   the general mixture, without relying on the historical mixture
   no-spinodal axiom. The single-tail and certified two-tail control results
   have their separately recorded scopes.

No universal real-root/Taylor-convergence equivalence is asserted. The full
general canonical-to-Jacobian implication is still incomplete, and the new
lemmas must not be cited as its completion.

## Actual c-side L2/Fourier connection (1.0.16)

`JacobianL2` proves the exact finite expression of arbitrary Fréchet DCF
variations, measurable bounded radial numerators, and every radial Lp
membership for Jacobian kernel directions. Both integral r^2*delta-c^2 and
integral |r^2*delta-c| are finite. `FourierL1L2` proves that the actual
integral Fourier transform and Mathlib's abstract L2 transform agree a.e.
on L1 intersect L2, without a supplied Fourier integrability premise.

`RadialVariationL2` constructs the actual density-weighted odd L2 field U,
proves its exact representatives and Fourier matrix

    Fourier U(w) = -i*w * radialVariationMatrix(2*pi*w).

The physical variation symbol is continuous, including k=0. Its spatial
pairing with an L2 representation of the constructed h variation is zero
internally. `actual_kernel_DCF_ae_zero_of_L2_OZ` proves actual delta-c=0 a.e.
on each positive-density pair from the two still-explicit premises: an L2
representation of the constructed h variation and the tangent spectral OZ
identity, evaluated at the correct physical frequency 2*pi*w. It does not
supply those remaining premises or prove the full no-fold theorem.

## Reproduction

From the package root, run `lake build` and `python3 formalization/check.py`.
Baseline 1.0.15 records the new modules and exact per-theorem standard-axiom
guards; its final build and compatibility evidence is archived under
`formalization/results/baseline_1_0_15/`. All 32 new exact guards passed using
only `propext`, `Classical.choice`, `Quot.sound`; the collection has 63 modules
and 445 guards. The default foundation build passed 9075 jobs, the workspace
plus three compatibility targets passed 9198 jobs, and 525 source/config
hashes passed the freeze audit. Boundary/Git-ownership and three downstream
dependency locks passed. Independent full downstream proof builds were
explicitly NOT_RERUN. The manifest SHA256 is
`378d478e193756ee198399da00612695f8517c4f967a166b0461c95c97b08c93`.
The complete 1.0.14 manifest is preserved byte for byte, and all its existing
proof modules are unchanged.

The 1.0.16 c-side L2/Fourier extension is validated separately under
`formalization/results/baseline_1_0_16/`: 66 modules, 485 exact std3 guards,
528 source/config hashes, foundation 9078 jobs and workspace/compatibility
9201 jobs. Its reproduction and precise remaining h/OZ scope are in
`proof_notes/codex_radial_variation_l2.md`.
