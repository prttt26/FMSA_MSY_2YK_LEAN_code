# General finite-mixture HS canonicity without a physics axiom

2026-10-28. Six new modules, 52 theorems. Every theorem has compiled and its
ACTUAL axiom report was queried before guards were generated: each contains
exactly propext, Classical.choice and Quot.sound. Full-package validation and
independent hash auditing have PASSED. Foundation 1.0.17 and all TeX stay untouched.

## Exact actual results

`MixtureHSCanonicity.seed_factor_closed_right_isUnit` proves the actual HS
factor I-rdfMatrixLaplace(seedKernel)(s) is a unit for EVERY complex Re(s)>=0,
for arbitrary finite species count, nonnegative densities and diameters, and
etaMix<1. Unequal diameters, repeated diameters, zero-density tracer faces,
vacuum and empty species sets are included. No initial canonicity, inverse,
root path, density-path escape radius or no-spinodal/homotopy axiom is supplied.
The empty-tail kernel presentation is proved identical to the existing
nonlinearCausalKernel at Dt=0, for ANY finite tail representation and ANY G.

`actual_mixture_hs_canonical` transfers that conclusion to the original actual
MSA amplitude interface. `exists_mixture_hs_maximal_branch`, with positive
rates/diameters and symmetric finite K, constructs the positive maximal INITIAL
analytic canonical branch from physical data alone at every physical mixture
density eta<1. This closes the general unequal-diameter HS seed gap beyond
the previously proved low-density ball. The endpoint can be infinite.

`MixtureHSNoSpinodal.pyhs_mixture_no_spinodal` has the EXACT logical statement
of the frozen `FMSA.MixtureNoSpinodal.pyhs_mixture_no_spinodal` physics axiom,
now proved independently for arbitrary finite N. The original declaration is
neither used nor modified. Its stronger nonnegative-density version includes
tracers. This statement remains punctured at k=0 because the legacy literal
rational matrix has a junk origin; the true actual kernel result includes zero.
No explicit formula for the static determinant has been formally proved here.

## Collective identity, with the actual core convention

Write c=pi/vac, m2=sum rho_i*sigma_i^2, and

    A_j = 2*c+c^2*m2*sigma_j,
    Qp_ij = sigma_i*A_j/2+c*sigma_j.

The TRUE recentered compact core is

    q_ij(t)=Qp_ij*(t-sigma_i)+A_j*(t-sigma_i)^2/2
           =A_j*t*(t-sigma_i)/2+c*sigma_j*(t-sigma_i).

For an arbitrary complex vector y define U=sum rho_i*y_i,
V=sum rho_i*sigma_i*y_i, A=2*c*U+c^2*m2*V, B=c*V. At s=i*k let

    N_i=A*(1-i*k*sigma_i/2)+B*(i*k+k^2*sigma_i),
    D_i=A*(1+i*k*sigma_i/2)+B*i*k.

The exact arbitrary-finite-N collective identity is

    sum_i rho_i*(normSq(N_i+i*k^3*y_i)-normSq(D_i))
      = k^6*sum_i rho_i*normSq(y_i).

The per-row correction is NOT zero. The physical moment relations cancel it
AFTER summation; no phase or determinant exponential term is discarded.
The cleared factor-kernel equation gives
N_i+i*k^3*y_i=exp(-i*k*sigma_i)*D_i. For k!=0 every row norm difference is
zero, so nonnegative rho implies rho_i*y_i=0. Both moments vanish, then the
cleared row equation gives EVERY y_i=0, including tracers. No density division
occurs. Matrix kernel injectivity gives the column-density factor unit;
Sylvester transfers it to the actual row-density factor.

The origin is handled separately, through true compact polynomial integrals:

    staticCore_ij=-sigma_i^3*A_j/12-c*sigma_i^2*sigma_j/2.

A static kernel vector has y_i=-sigma_i^3*A/12-c*sigma_i^2*V/2.
With m3=sum rho_i*sigma_i^3>=0, moment cancellation gives
(1+c*m3/6)*A=0, then (1+c*m3/2)*V=0, hence y=0.
This does not substitute s=0 into a rational 1/s formula.
`MixtureHSKernel` identifies both formulas with HONEST actual integrals before
asserting actual axis units.

## Whole half-plane: clopen on the physical density region

At fixed diameters the physical density region

    P={rho | rho_i>=0 for all i, etaMix(rho,sigma)<1}

is convex, hence connected, with vacuum in it. Let G be its subset at which
the actual HS factor is a unit for EVERY Re(s)>=0.

1. G is relatively open. The genuine weighted physical coefficients are
   continuous off vac=0. Their differences times the true compact basis L1
   masses give a finite nonnegative densityDistance, tending to zero at its
   base and controlling the entire closed-half-plane symbol difference.
   The already-proved actual canonical resolvent control supplies a uniform
   inverse bound at a canonical base. The proved inverse perturbation lemma
   gives actual nearby units uniformly in frequency, including the origin.
2. G is relatively closed. Honest coefficient distance and fixed-density
   frequency analyticity give joint density/frequency determinant continuity
   in Re(s)>0. At a limit density the determinant is holomorphic and nontrivial
   there by the already-proved fixed-density high-frequency unit theorem.
   The proved zero-free closure principle (reciprocal maximum modulus)
   excludes strictly-right zeros. Independent collective/static axis units
   exclude the boundary zeros. This uses no new Hurwitz/homotopy axiom.
3. Vacuum belongs to G since its true weighted kernel is zero. A nonempty
   clopen subset of connected P is P itself.

No global density-path escape radius, entire-function assertion or uniform
high-frequency density homotopy theorem is needed by this proof.

## Literal frozen physics interface

The legacy Q0_mat_c_phys contains sqrt(rho_i*rho_j) and contact edge phases.
For nonnegative densities sqrt(rho_i*rho_j)=sqrt(rho_i)*sqrt(rho_j).
`legacy_factor_phase` proves Q0_phys*P=P*(I-S*bareHS*S) with
P_ii=exp(s*sigma_i/2) and S_ii=sqrt(rho_i). P is a unit at every frequency.
Sylvester and S*S=diag(rho) give the same nonzero determinant as the proved
row-density core factor. Tracers require no inverse of S or rho. The new
`pyhs_mixture_no_spinodal` therefore has exactly the old statement without
consuming its physics axiom. It does NOT change the frozen downstream imports
or axiom footprints; a coordinated replacement is deferred until research ends.

## What remains open

This is a reference HS SEED theorem, not canonicity at every nonzero strength.
The constructed initial branch has the proved finite-endpoint amplitude-escape
OR physical-Fourier-zero-cluster alternative. Scalar escape exclusion remains
one-species only; general matrix normalized factors can be identically singular
at a limit. Finite MIXTURE amplitude escape, a unique full noncanonical endpoint
limit, complex Taylor-radius LOWER bounds and tail/all-density classification
remain open. An exact abstract obstruction to copying scalar normalization is
F_m(s)=I-m*L(s)*E12 in dimension two, with L any nonzero compact-kernel Laplace
symbol. E12^2=0 gives det(F_m)=1 and inverse I+m*L*E12 at every frequency,
whereas F_m/m tends to -L*E12, identically singular. The matrix arithmetic was
checked by exact SymPy expansion. This is ONLY an abstract canonical-factor
example, not an actual MSA-root counterexample or evidence of physical escape;
the actual coupled BH constraints must supply any stronger matrix conclusion.
The actual full-open-interval Taylor criterion remains beta<=R.
No beta=R, global existence among all real roots, RDF positivity, arbitrary-
observable convergence or universal real-root/Taylor equivalence is asserted.
Later stable islands are not appended to the user-chosen initial interval.

## Verification

PASS: 838 exact guards, 58 research modules plus root / 59 direct pinned
compiler commands. ALL 52 new actual axiom reports were queried before exact
guards, and every guard passed with exactly the standard three axioms.
Independent audit checks EVERY input/source/artifact/raw-log hash; all 52 prior
research module source/artifact/footprint records remain unchanged; all 530
frozen source/config hashes, nine validated-paper / seven Mathlib / two
separately locked LeanCode source-cache import pins remain unchanged. No new
direct dependency import, shared/Lake build, foundation/TeX edit or merge-back.
Evidence: `results/lean/validation.json`, `results/lean/build.log`, and the
reproducible isolated verifier `python3 scripts/check_project.py`.

The main Markdown TODO records exact theorem names, assumptions, limitations
and proposed SI correspondence. No TeX or paper build was run.
