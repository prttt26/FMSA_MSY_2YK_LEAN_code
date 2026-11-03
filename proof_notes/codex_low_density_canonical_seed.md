# Actual HS initial canonicity near vacuum

Date: 2026-10-28. Isolated research over frozen foundation 1.0.17 / 06e3268.
New module: `MSAConvergence/LowDensityCanonicalSeed.lean`, 19 theorems.
No new mathematical axiom, foundation/TeX/numerical edit or merge-back.

## Precise scope and the already-existing analytic seed

The frozen `ActualAnalyticTaylor.exists_analytic_seed_positive_radius` ALREADY
constructs a true analytic BH root germ through `(0,baseSeed)` with a positive
common amplitude Taylor radius, for any finite positive rates, positive
diameters, nonnegative densities and positive vacancy. K symmetry is not
needed for that local algebraic construction. It uses the physically proved
positive-REAL-frequency HS block inverses, which suffice for the zero-coupling
triangular amplitude Jacobian. They do not imply full half-plane canonicity.
We REUSE this theorem; its analytic-root content is not a new result here.

The new result discharges initial full half-plane canonicity unconditionally
in a real density neighbourhood of vacuum, then constructs a common local
interval of canonical roots to which all their amplitude Taylor series sum.
It does not establish arbitrary-density HS canonicity.

The frozen `MixtureNoSpinodal.pyhs_mixture_no_spinodal` is a physics AXIOM;
it is NEVER consumed by these proofs. Every new actual footprint was queried
from Lean, and contains exactly propext, Classical.choice and Quot.sound.

## Exact genuine kernel and the sufficient finite budget

At Dt=0, the actual W and C amplitudes vanish and the two remaining actual
coefficients are `Q0phys rho sigma i j` and `Qppphys rho sigma j j`.
`hs_coefficient` and `hs_kernel_symbol` prove this directly in the genuine
finite dictionary and the honest Laplace integrals, including s=0. No rational
expression is assigned to a removable pole. The unused G, tail rates and even
the number/type of finite tails do not affect the actual initial kernel:
`hs_kernel_independent_tails` proves equality of kernels.

For sigma_i>=0, the two fixed compact basis masses are exactly

    integral_(0,infinity) abs(min(r,sigma_i)-sigma_i) dr = sigma_i^2/2,
    integral_(0,infinity) (min(r,sigma_i)-sigma_i)^2/2 dr = sigma_i^3/6.

`hs_linear_basis_mass` and `hs_quadratic_basis_mass` prove these by a true
support cutoff and the fundamental theorem of calculus. The definition
`hsKernelBudget` first uses the genuine L1 masses; `hs_kernel_budget_eq`
evaluates it to the finite expression

    B(rho,sigma) = sum_i sum_j [
      abs(rho_i*Q0phys_ij)*sigma_i^2/2
      + abs(rho_i*Qppphys_jj)*sigma_i^3/6 ].

Thus B depends only on density and diameters, independently of the positive
finite-tail representation (`hs_kernel_budget_independent_tails`). The
triangle inequality and abs(exp(-s*r))<=1 for Re(s)>=0 give

    complexNormSum(qhat_HS(s)) <= B(rho,sigma), every Re(s)>=0.

When B<1, the existing finite-matrix Neumann/unit theorem gives full actual
canonicity. `hs_canonical_of_explicit_budget` exposes exactly that finite
physical-data sufficient condition. There is no root, inverse, density-sign
or vacancy premise for this off-root implication. Nonnegative diameter data
and positive rates are explicit. Frequency zero and every tracer species are
included. The criterion is SUFFICIENT only: B>=1 proves nothing about actual
canonicity, and B is a coefficient majorant, not an equality for the norm of
the combined kernel. High-density states may be canonical despite failing B<1.

## An actual nonempty low-density region

At every nonzero-vacancy density, the physical HS coefficients are rational
continuous functions of density. The basis masses are fixed, so
`hs_kernel_budget_continuousAt` proves continuity of B in the ORIGINAL density
norm. At vacuum B=0 and vacancy=1, exactly. Therefore
`exists_hs_canonical_density_ball` constructs epsilon>0 such that every
rho with norm(rho)<epsilon has positive vacancy, B<1 and full HS canonicity
for every G. The norm here is the existing finite-product density norm;
no new norm instance or density inverse is introduced.

This proves the low-density hypothesis is satisfiable on a whole open set,
including arbitrary nonnegative compositions with any number of exact-zero
density species. It is not a numerical sample or a conditional seed axiom.

## Constructed branch and actual Taylor sums

`exists_analytic_canonical_hs_seed_of_budget` combines the frozen genuine
analytic HS seed with the newly established initial full canonicity. Proved
canonical openness and continuity give canonicity on a two-sided coupling
neighbourhood. The caller supplies physical data and B<1, never a root curve,
Jacobian inverse or canonical root. No symmetry/sign assumption on K or
distinctness of rates is needed for this local result.

`exists_low_density_analytic_canonical_hs_branch` further discharges B<1 and
positive vacancy throughout the constructed density ball, for EVERY finite
strength array K at each such nonnegative density. It constructs the branch,
its seed value, analyticity, positive common Taylor radius and local roots /
canonicity. Empty finite tails and all-zero density are permitted.

`analytic_amplitudes_eventually_hasSum` uses the actual component jets of
an analytic amplitude germ and finiteness of all indices to obtain ONE common
coupling neighbourhood for every Dt/G component series. It does not replace
series values by a formal definition.
`exists_convergent_canonical_hs_interval_of_budget` extracts b>0 and constructs
p with its physical seed such that for every real abs(t)<b the branch is
analytic, an actual MSA root, fully canonical, and all amplitude Taylor series
sum TO p(t). Positive and negative small t are both covered.

This b is local; the theorem does not compare its Taylor radius with the
entire positive stability interval, prove global continuation or assert
uniqueness of all real MSA roots. It does not establish an arbitrary observable
series, RDF positivity or amplitude-family global-L2 differentiability.

## Next interfaces: density homotopy and the scalar seed

Claude 104 suggests extending from a low-density canonical seed along the
HS density path. This is viable for one species, but 102's existing connected
path theorem fixes density, so it cannot simply be applied to a density path.
A genuine variable-density kernel/coefficient continuity and canonicity path
bridge remains to be formalized. The all-density mixture Fourier-axis result
cannot be borrowed from the frozen physics axiom.

For ONE species the pinned foundation already proves the nonzero real-axis
statement without physics axioms: `BaxterNoSpinodalEquiv.qhat_complex_ne_one_of_real`
inside namespace `FMSA.HardSphere`, via the exact k^6 norm dominance identity
in `BaxterPoles`. Thus a float scan is unnecessary to prove that axis premise.
At zero frequency the genuine integral must be used, rather than the frozen
rational expression's encoding at s=0. Terminology correction after checking
`MSAMultiTailMixtureSpectral.fourierFactor`: the actual physical factor is
the density-weighted Baxter factor I-S*Qhat*S, not its Gram product. For the
one-species HS seed it agrees with the physical scalar 1-Qhat_complex under
the proved dictionary. A Gram product requires the additional conjugate-
transpose multiplication. Positivity of the real part of the Baxter factor
is not an available all-density shortcut. This corrects handoff 105's wording;
the Lean proofs always used the actual factor definition.


A further read-only audit finds a more direct scalar route. The pinned
`BaxterLowerHalfPlane.lean` already assembles the entire scalar density
homotopy (joint continuity, entire symbols, all-real boundary nonvanishing,
uniform escape radius and dilute seed), but its final theorem CONSUMES
`FMSA.Analysis.zeroFree_lowerHalfPlane_of_homotopy`, a pure-analysis AXIOM.
Thus the scalar half-plane theorem's `theorem` keyword does not make it an
admissible standard-three result. `BaxterExteriorRegularityGeneral` and
`BaxterHermiteBiehler` still inherit that axiom. Do not use them as proofs here.
The next research route is to prove the SAME abstract homotopy statement
using our already-proved reciprocal-maximum-modulus zero-free closure
principle, then reuse the frozen scalar inputs without that axiom. This can
avoid a full general variable-density actual-kernel theorem for the scalar
case; the arbitrary-mixture density bridge remains a separate open interface.

## Validation

Use `python3 scripts/check_project.py`, with the installed pinned Lean 4.31.0
and read-only validated imports. The resulting research validation record
must cover all 43 modules plus root, 670 exact theorem guards / 44 direct
compiler commands, every source/input/artifact/raw-log hash, the frozen 530
source/configuration hashes, and unchanged nine foundation / six Mathlib
direct artifact pins. No new direct dependency is introduced by this module.
The raw 19 actual footprint reports were queried before adding their exact
compiler guards. Full validation and independent audit: PASS, 670 exact
standard-three guards, all 43 modules plus root / 44 fixed compiler commands,
EVERY input/source/artifact/raw-log hash, all 530 frozen source/configuration
hashes and all previous nine foundation / six Mathlib direct artifact pins.
Results are recorded in `results/lean/validation.json` and `results/lean/build.log`.
