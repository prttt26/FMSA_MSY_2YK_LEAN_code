# Exact MSA real roots and the HS Taylor vector: the proved implication

Let `p` be a smooth local root of the original finite-mixture BH/Exact
MSA equations at zero coupling, with original amplitude coefficient
vector `cₙ = branchCoefficients p n`. For a real coupling `τ`, the new
Lean theorem

`ActualSeriesRootImplication.summable_at_real_coupling_implies_exact_root`

proves that if `Σₙ τⁿ cₙ` converges as a finite-dimensional real vector,
then its sum `(D,G)` satisfies `MultiTailMixture.IsRoot z rho sigma
(τ • K) D G`. This includes convergence exactly on the Taylor circle;
`Summable` does not demand absolute convergence. The contrapositive
`no_real_root_at_real_coupling_implies_divergence` proves that an
absence of *any* real root forces the complete amplitude vector series
to diverge at `τ`.

The proof uses the frozen `StrengthScaling.jet_rescale` to replace
`cₙ` by the coefficients of `t ↦ p(τt)`. The frozen
`TaylorRoot.actual_endpoint_of_smooth_root` then uses the polynomial
MSA residual, interior analytic identity and Abel's endpoint theorem.
Continuous linear coordinate projections transfer vector summability
to every original `Dt` and `G` component. This supplies an actual MSA
interface rather than an abstract power-series statement. The theorem
`exists_physical_seed_with_no_root_divergence` constructs a suitable
PY-seeded germ for every finite mixture with positive rates and
diameters, nonnegative densities and positive `vacMix`; the strength
matrix is arbitrary.

The reverse implication fails. In
`SingleTailNegativeCouplingCounterexample`, a negative real coupling
has an exact one-tail root beyond the HS Taylor radius, and reflection
gives a positive real coupling with a repulsive tail and the same
failure. Thus the precise logical status is:

| Claim | Status |
| --- | --- |
| Complete HS amplitude series converges at `τ` ⇒ a real Exact MSA root exists there | Lean proved, including boundary convergence |
| No real Exact MSA root at `τ` ⇒ complete HS amplitude series diverges there | Lean proved |
| A real Exact MSA root exists at `τ` ⇒ complete HS amplitude series converges there | False in general; Lean one-tail signed counterexample |
| Complete HS amplitude series diverges at `τ` ⇒ no real Exact MSA root exists there | False in general; same counterexample |

This does not classify the radius for all-attractive mixtures or prove
that the root produced by a convergent series is canonical. It also
does not identify any remote real root with the HS-seeded analytic
continuation. Those are separate claims requiring their own hypotheses.

Validation: `LEAN_BIN="$PWD/scripts/lean_memory_limited.py"
PYTHONDONTWRITEBYTECODE=1 python3 scripts/check_project.py -j 1`
PASS, 2377 exact axiom guards across 261 research modules. Every new
theorem depends only on `propext`, `Classical.choice`, `Quot.sound`.
One Lean process was capped at 30 GiB RSS. Frozen foundation 1.0.17
and TeX were unchanged.

## Repulsive one-tail closed boundary

`SingleTailNegativeCouplingCounterexample.negative_exact_root_at_every_coupling`
uses the quartic's unbounded left side and the intermediate value
theorem to construct an original BH root at **every** negative
coupling of a positive tail. Reflection gives a root at every positive
coupling of the repulsive tail. `scalar_radius_reflected` and
`amplitudeRadius_reflected` prove exact equality of the attractive
and repulsive coefficient radii; the frozen one-tail theorem identifies
this common radius with `foldCoupling`.

`RepulsiveOneTailBoundary` proves the strict alternatives, and
`NonnegativeAbelConverse` settles the fold equality:

| Positive repulsive coupling | Complete original amplitude series | Exact MSA real root |
| --- | --- | --- |
| `0 ≤ τ < foldCoupling` | Converges, and its sum is a root | Yes |
| `τ > foldCoupling` | Diverges | Yes |
| `τ = foldCoupling` | Converges absolutely; its sum is a root | Yes |

The generic `summable_endpoint_of_nonnegative_coefficients` lemma
uses bounded partial sums and the finite radial limit. The attractive
physical one-tail branch reaches a finite quartic fold, while every
positive-order original amplitude coefficient is nonnegative. This
gives attractive endpoint summability, and its vector sum is an
original Exact MSA root. Exact parity of the reflected
coefficients then gives absolute summability of the repulsive vector
at the same fold. The original MSA root implication identifies its
sum. Thus for `τ ≥ 0`, the repulsive series is summable exactly when
`τ ≤ foldCoupling`; throughout the closed interval its sum is a root.
The result does not classify the corresponding all-attractive
multi-tail boundary or canonicity of remote roots.

Validation after this extension: PASS, 2397 exact axiom guards across
263 research modules, one 30 GiB-capped Lean process, standard three
axioms only. Frozen foundation 1.0.17 and TeX unchanged.

## Complete real-axis one-tail convergence set

`SingleTailFullRealBoundary` now proves the stronger, sign-symmetric
statement for the **original** one-tail `(Dt,G)` vector. For any
admissible positive strength `K`, the HS-seeded series of `K`, and the
reflected HS-seeded series of `-K`, are summable at real `τ` exactly
when `|τ| ≤ foldCoupling`. At every such coupling their sums satisfy
the corresponding original Exact MSA equation. Strict interior
convergence follows from the Mathlib component radii, both endpoints
from the fold/Abel proof, and exterior nonconvergence from the radius
upper bound for a summable vector. The coefficient-reflection theorem
transfers the entire statement between signs. This classifies the
one-tail real axis; multi-tail attractive radii remain open.

Full validation: PASS, 2402 exact axiom guards / 264 research modules,
one Lean process capped at 30 GiB RSS, standard three axioms only.
Frozen foundation 1.0.17 and TeX unchanged.
