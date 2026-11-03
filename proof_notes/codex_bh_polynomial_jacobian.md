# Literal BH polynomial Jacobian and actual endpoint regularity

The new `MSAConvergence/BHPolynomialJacobian.lean` connects formal partials
of the ALREADY PROVED literal BH polynomials to the ORIGINAL amplitude
partial used by the analytic implicit-function theorem. No physical
coefficient is rationalized, no residual is rescaled, and no reduced X=Dt*G
coordinate is used. This is a Lean proof, separate from the external
M1/M2/M3 analytic enclosure computations.

## Exact derivative identification

`polynomial_line_hasDerivAt` proves for any finite variable family, polynomial
P over the REALS, and arbitrary v,w:

    d/dt eval(v+t*w,P) at t=0 = sum_j eval(v,pderiv_j P)*w_j.

The proof is polynomial induction: constants, sums and multiplication by a
variable. This is an analytic derivative theorem, not a definition of a
surrogate derivative or an assumed symbolic/analytic compatibility axiom.

`amplitudeEquiv` is the exact linear equivalence between the original pair
of finite Dt/G matrices and functions on Bool x tails x species x species.
False labels Dt, true labels G. Its continuous version supplies actual
coordinate projections. No norm equality between unrelated spaces is
assumed, and no nonempty-index hypothesis is introduced.

The matrix `jacobian` has entries

    J_ij = eval(amplitudeValues(a), pderiv_j(endpointPoly(b,i))).

`actual_partial_coordinates` proves, using the real-line derivative theorem,
the known actual polynomial evaluation identity and the genuine chain rule,

    amplitudeValues(actualPartial(b,a)(h))_i
      = sum_j J_ij*amplitudeValues(h)_j.

This holds at EVERY amplitude point and all fixed real physical data. It
does not require a root, positive rates/densities/diameters, nonzero vacancy,
symmetry, canonicity or a regularity assumption. Fixed-data divisions remain
the exact totalized real operations in the original residual.

`actual_partial_mulVec` and `actual_partial_injective_iff` identify the whole
linear map, rather than just selected entries. Finite dimensionality then
proves that actual `EndpointRegular` is equivalent to matrix invertibility
and to det(J) being nonzero. Empty species/tail families are included.

## Exact preconditioned row certificate

`matrix_injective_of_row_defect` proves the finite-dimensional criterion

    for every i, sum_j abs((1-C*J)_ij) < 1  ==>  J is injective.

C is an arbitrary real matrix; its inverse is NOT supplied. If J*x=0 and
x is nonzero, choose a coordinate of maximal positive magnitude. From
x=(1-C*J)*x, that coordinate is bounded by a strict factor below one times
itself, a contradiction. This proof requires no operator-norm convention,
Neumann-series axiom or nonempty-index premise.

`endpoint_regular_of_row_defect` feeds that criterion through the exact
polynomial/actual derivative correspondence. `actual_cluster_limit_of_row_defect`
then supplies the existing full left limit for ANY continuous actual root
prefix with an approaching endpoint cluster, without prefix canonicity or
a supplied global path bound. The row inequalities remain explicit goals.

## A fully constructed concrete instance: ALL vacuum amplitude points

`vacuum_multiplier_pderiv` proves that the explicit vacuum elimination
multipliers from `VacuumFiberCertificate` have zero formal partials. The
already proved unit-saturation ideal identity is

    X_i - rootPoint_i = sum_k multiplier_ik * endpointPoly_k.

Differentiating THIS POLYNOMIAL IDENTITY, then evaluating at an arbitrary
amplitude point, gives

    vacuumPreconditioner(z) * J(z,0,sigma,K,b,a) = 1.

This is `vacuum_jacobian_left_inverse`. All entries of the preconditioner
are constructed from the explicit constant multipliers, not assumed or
provided by an oracle. The resulting `vacuum_endpoint_regular` proves
actual amplitude regularity for arbitrary finite mixtures/tails at zero
density, positive rates, arbitrary real coupling, signed/inactive strengths
and arbitrary unequal diameters, at EVERY amplitude point. A root, canonical
seed, numerical enclosure and inverse premise are all unnecessary.

This is a concrete application of the new bridge, rather than only a
conditional API. It does not imply a positive-density certificate.

## Exact remaining boundary

The M1/M2/M3 Arb reports have not been imported as kernel proofs. Establishing
their physical pi/exp enclosures and interval arithmetic INSIDE Lean, with
an exact coordinate-order translation, remains necessary to obtain numerical
`EndpointRegular` instances from those reports. An external PASS flag or
JSON hash does not discharge the new row inequalities. Nor do these theorems
identify a PY prefix, prove first loss, or bound a multitailed complex Taylor
radius from below. Generic positive-density fiber certificates, nonisolated
singular endpoint control and matrix escape also remain open.

No mathematical axiom, frozen foundation file or TeX file is added/edited.
All 12 public theorems have actual queried axiom reports and exact guards.
The reproducible compiler and full-validation evidence is recorded in
`results/lean/validation.json` and `results/lean/build.log` after validation.

## Verification (2026-10-29)

PASS: 978 exact standard-three theorem guards, 66 research modules plus the
root, 67 direct pinned compiler commands. The 12 new axiom reports were
queried before writing exact guards; they contain only propext,
Classical.choice and Quot.sound. The guarded module and root also passed
individual direct compilation before the full run.

Independent post-run audit checked every validation input, module source,
artifact and raw compiler-log hash. ALL 65 prior module source/artifact/axiom
footprint records remain unchanged. All 530 frozen foundation hashes, nine
validated paper imports, seven direct Mathlib imports and two locked raw
LeanCode imports are unchanged. No external import or shared/Lake build is
introduced. Existing M1/M2/M3 external rational checks still pass against
their unchanged literal-model/source pins.
