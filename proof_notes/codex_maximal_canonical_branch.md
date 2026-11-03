# Construction of the actual maximal initial canonical MSA branch

2026-10-28. Research only, in `MSA_Convergence`; frozen foundation 1.0.17
and TeX are untouched. No mathematical axiom is added.

## Actual statement and seed assumptions

`MaximalCanonicalBranch.lean` constructs a maximal initial canonical branch
for the actual finite mixture BH residual, with the original amplitude norm.
Assume positive finite tail rates and diameters, nonnegative species densities
(including arbitrary tracers), symmetric strength matrices K, nonzero vacancy,
and an actual canonical zero-coupling seed. No root curve, Jacobian inverse,
global existence, bound on amplitudes or endpoint regularity is supplied.

`CanonicalPrefix` is a continuous actual canonical root path on [0,c), c>0,
through that seed. The actual Jacobian inverse and analytic IFT from the
previous modules give at least one such prefix. Any two prefixes agree on
ALL their overlap by actual connected root uniqueness. Their lengths have a
positive supremum beta in ENNReal; beta may be finite or infinity.

`maximalBound` is this supremum. At each t in [0,beta), some prefix reaches
strictly beyond t. Coherence makes the chosen union path agree with EVERY
old prefix, and gives continuity, actual root equations and full canonicity
on its entire domain. Its arbitrary outside-domain values are placeholders,
never Taylor data. `exists_maximal_branch` constructs a TRUE analytic
representative equal to this union throughout the maximal nonnegative domain,
with genuine two-sided actual root and canonical germs at zero.

The resulting `MaximalBranch` records universal inclusion of every admissible
prefix. A longer finite canonical prefix would contradict the supremum, so
finite-endpoint nonextendability is PROVED, not assumed. Conversely, restricting
any such branch to finite prefixes proves that every maximal representative
has exactly the defined supremum as its bound. Its endpoint and all domain
values are unique. Actual root-germ uniqueness also proves equality of the
Taylor coefficients and the common amplitude radius for any representatives.

## Physical HS specializations

`MaximalMSAConvergence.lean` supplies these actual seed data as follows.

- `exists_hs_maximal_branch_of_initial_canonicity` internally discharges the
  frozen actual HS root equation; only full initial canonicity remains as a
  seed premise for a general physical mixture.
- `exists_scalar_hs_maximal_branch` constructs the branch from ONE-species
  physical data ALONE at EVERY eta<1, with arbitrary nonnegative density and
  positive diameter/rates, and every finite K. One-species symmetry is
  automatic. The earlier scalar canonicity proof supplies the full seed
  half-plane condition, including zero frequency and vacuum.
- `exists_low_density_hs_maximal_branch` constructs the branch for every
  nonnegative mixture density in the previously proved whole norm ball
  around vacuum, uniformly for all symmetric finite K. Positive vacancy and
  initial full canonicity are conclusions on that ball.

Thus initial real-branch existence and maximality are now genuine results
under those seed hypotheses. This is not a construction of an infinite
real domain, nor maximality among arbitrary noncanonical real roots.

## Exact Taylor and finite endpoint conclusions

For the TRUE analytic representative g, its intrinsic common amplitude
radius R is positive, and `maximal_branch_taylor_criterion` proves exactly

    all amplitude Taylor sums equal g throughout [0,beta) iff beta <= R.

No real-axis argument proves beta<=R automatically. Even beta=infinity
would imply whole-interval Taylor convergence only when R=infinity.
No claim about the excluded endpoint follows from this open-interval iff.

For finite beta, `maximal_finite_endpoint_boundary` derives beta>0 and the
actual alternative: arbitrarily large amplitudes arbitrarily near beta,
OR an actual endpoint cluster root with a zero of the physical Fourier
factor at a real wave number. This uses the previous continuation theorem
and the NOW PROVED nonextendability. No endpoint value or full limit is given.
The physical factor is the density-weighted Baxter factor I-S*Qhat*S, not a
Gram product; zero frequency and zero-density species are retained.

`maximal_bounded_endpoint_cluster` retains the approaching sequence, its
actual residual root at beta, its norm bound, canonical closure membership,
and the genuine physical Fourier determinant zero. A canonical cluster would
force a longer prefix, but a noncanonical cluster need not have a unique full
limit. Boundedness is still an explicit premise, not a hidden conclusion.

`maximal_escape_taylor_obstruction` proves R<=beta in the unbounded case,
excludes simultaneous all-component Taylor sums to ANY finite vector at
EVERY r>beta, and deduces

    convergence throughout the whole OPEN [0,beta) iff R=beta.

The equality is NOT asserted. Escape is arbitrarily large values arbitrarily
near the endpoint, not a claimed full norm limit to infinity. A bounded
Fourier-zero cluster alone is not a Taylor obstruction: the algebraic root
can remain regular after loss of canonicity.

## Remaining paper claims and limits

This gives a precise maximal INITIAL canonical domain. It cannot yet be
identified with a first physical Fourier zero without excluding finite
amplitude escape. Later stable islands do not extend this initial domain.
General unequal-diameter HS seed canonicity beyond low density, exclusion of
finite escape/properness, a full noncanonical endpoint limit, parameter-wide
all-wave certificates, and complex Taylor-radius LOWER bounds / tail and
all-density classification remain open. No universal real-root/Taylor iff
is recovered. No physics axiom or frozen homotopy axiom is consumed.

Suggested manuscript correspondence: cite `exists_maximal_branch`,
`maximal_branch_bound_eq_supremum`, `maximal_branches_agree` and
`maximal_branch_coefficients_and_radius_unique` for existence and intrinsic
choice independence; the scalar and dilute specialization names above for
physical hypotheses; `maximal_finite_endpoint_boundary`,
`maximal_bounded_endpoint_cluster`, `maximal_escape_taylor_obstruction` and
`maximal_branch_taylor_criterion` for the exact endpoint/radius statements.
This note only proposes correspondence; no TeX is edited.

## Verification

PASS: 722 exact guards across 49 research modules plus root, using 50 direct
pinned-compiler commands. All 27 new actual axiom reports were queried before
guards; each uses exactly propext, Classical.choice and Quot.sound.

Independent auditing checks every validation input, source, artifact and raw
log hash, all 47 prior module source/artifact/axiom records unchanged, all
530 frozen source/configuration hashes unchanged, and all nine validated
paper / seven Mathlib / two separately locked LeanCode source-cache import
pins unchanged. No new direct import, Lake/shared build or merge-back.
Evidence: `results/lean/validation.json` and `results/lean/build.log`.
The main Markdown TODO records the exact claims and proposed SI correspondence;
TeX and Claude-owned notes/numerics are untouched.
