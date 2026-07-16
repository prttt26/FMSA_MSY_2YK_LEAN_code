# General-Purpose Math Axioms (`LeanCode/Analysis/`)

Central registry for **general-purpose mathematical axioms** — classical, textbook-citable facts
absent from the pinned Mathlib (`v4.31.0`, commit `fabf563a`) that the project assumes by name.
These are deliberately distinct from the project's **physics axioms** (`oz_core_closure`,
`oz_fixed_pt_unique`, `oz_h_exterior_regularity`, `Q0_moment_det_pos` — domain-specific claims
about the OZ/PY system, documented in their own groups' proof notes): everything here is
project-independent pure mathematics, stated in Mathlib's own vocabulary, no
`FMSA.HardSphere`/`FMSA.YukawaDCF` dependency, reusable by any consumer. Complete axiom inventory
(both kinds) lives in `todo_lean.md`'s Axioms table.

**Axiomatization discipline** (established 2026-07-15, during the `OZFIX.6` Route B effort): an
axiom is admissible here only if it is (a) a *named, independently-recognized* classical theorem
(citable in any complex-analysis textbook, true regardless of which project uses it), (b) confirmed
genuinely absent from Mathlib by a dedicated reconnaissance pass (source search + Mathlib's own
`docs/1000.yaml` unformalized-theorems tracker), and (c) the *narrowest* statement that closes the
gap — with everything derivable from already-proved Mathlib content split off as genuine theorems,
not folded into the axiom. Counter-example deliberately **rejected** under this discipline: an
"arc-vanishing" axiom for `h_explicit`'s specific `Ĥ` (see `proof_notes_ozfix.md` `OZFIX.10`) —
that would assume the hardest part of the very theorem being proved rather than cite established
mathematics.

## Axiom 1 — `circleIntegral_eq_sum_of_small_circles`

**File:** `LeanCode/Analysis/ContourDeformation.lean`. **Added:** 2026-07-15 (Phase 1 of the
`OZFIX.6` axiomatization plan).

**Statement (informal).** For `f : ℂ → E` continuous on the closed big disk minus finitely many
pairwise-disjoint open small disks, and complex differentiable (off a countable exceptional set)
on the closed big disk minus the small closed disks, the big circle's contour integral equals the
sum of the small circles' integrals.

**Why it's an axiom.** The classical keyhole/slit-contour deformation argument. Reconnaissance
confirmed Mathlib has no residue theorem, no winding numbers (hence no argument principle/Rouché),
no general Mittag-Leffler, no contour-based Fourier/Laplace inversion — corroborated by
`docs/1000.yaml` listing all of these as tracked-but-unformalized. Mathlib's own annulus theorem
(`Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable`) covers only a *single
concentric* hole.

**What's derived from it (genuine theorems, no further axiom):**
`circleIntegral_eq_sum_two_pi_I_mul_of_simple_poles` — the finite simple-pole residue-sum formula
`∮_{C(c,R)} f = ∑ i, 2πi·g i (c'ᵢ)`, obtained by evaluating each small-circle integral with
Mathlib's *existing* disk Cauchy integral formula
(`circleIntegral_div_sub_of_differentiable_on_off_countable`). `#print axioms` = this one axiom +
the standard three.

**Consumers.** `OZFIX.6` Route B (`proof_notes_ozfix.md` `OZFIX.10`); Group MZERO's Route B
(`proof_notes_yukawa_wh.md`, `MZERO.9`–`MZERO.11`) hit the identical gap independently.

**Retirement condition.** Delete when Mathlib gains a residue theorem / general contour
deformation (tracked in `docs/1000.yaml`, so likely eventually).

## Axiom 2 — `halfDiskBoundary_eq_sum_of_small_circles`

**File:** `LeanCode/Analysis/ContourDeformation.lean`. **Added:** 2026-07-15 (during the `OZFIX.6`
Route B continuation, user-approved mid-implementation scope addition).

**Statement (informal).** Same deformation fact for the **upper half-disk boundary** — the
`[-R,R]` diameter plus the upper semicircular arc (parametrized to compose directly with
`jordan_lemma_arc_bound`, below) — with the small disks strictly inside the open upper half-disk.

**Why a separate axiom.** Fourier-inversion arguments close a *semicircular* contour, not a full
circle; Axiom 1 was deliberately scoped to circles only (narrowest-statement discipline), and the
half-disk boundary is a genuinely different outer shape for which Mathlib has equally no
machinery. Same keyhole/slit topological content, so the same admissibility case applies.

**What's derived from it:** `halfDiskBoundary_eq_sum_two_pi_I_mul_of_simple_poles` — the
residue-sum formula over the half-disk boundary, mirroring Axiom 1's derivation exactly.
`#print axioms` = this one axiom + the standard three.

**Consumers / retirement.** Same as Axiom 1.

## Companion (NOT an axiom) — `jordan_lemma_arc_bound`

**File:** `LeanCode/Analysis/JordanLemma.lean`. **Proved outright, 2026-07-15 — zero new axioms**
(`#print axioms` = the standard three).

Quantitative Jordan's lemma: for `g : ℂ → ℂ` bounded by `M` on the upper-half circle of radius
`R`, and `a > 0`, the semicircular arc integral of `g(z)·e^{iaz}` (Jacobian included) is `≤ πM/a`.
Listed here because it is the natural companion to Axiom 2 (the arc estimate one combines with the
half-disk residue theorem), and as a **worked example of the discipline**: a dedicated research
pass checked axiomatize-vs-prove *before* assuming anything, and found every step of the classical
proof available — most notably `Real.mul_le_sin`, literally docstringed *"One half of Jordan's
inequality"* in Mathlib, plus the ML inequality (`intervalIntegral.norm_integral_le_of_norm_le`),
`Complex.norm_exp`, an interval reflection (`Real.sin_pi_sub`), and a `zeta0_formula`-style
`HasDerivAt`+FTC antiderivative. When the mathematics is actually available, prove it — axioms are
the last resort, not the default.

## Axiom 3 — `mittagLeffler_expansion_of_bounded_on_circles`

**File:** `LeanCode/Analysis/MittagLeffler.lean`. **Added:** 2026-07-15 (Group MA, task `MA.2`).

**Statement (informal).** The classical **Mittag-Leffler expansion theorem** (Whittaker–Watson
§7.4 / Titchmarsh §3.2): for `f` with simple poles exactly at `p n` (local representation
`f = gₙ(z)/(z-pₙ)`, residue `gₙ(pₙ)`), enumerated by nondecreasing modulus, differentiable
elsewhere, and uniformly bounded on a sequence of circles `‖z‖ = R_N → ∞`:
`f(z) - f(0) = Σₙ resₙ·(1/(z-pₙ) + 1/pₙ)`, partial sums in enumeration order (ordered-`Tendsto`
conclusion, not `HasSum` — matching the classical statement; consumers with absolutely-summable
tails upgrade via `Summable`).

**Why it's an axiom.** Tracked as unformalized in Mathlib's `docs/1000.yaml`; classically proved
via the residue theorem applied to `f(w)/(w(w-z))` on the expanding circles — machinery Mathlib
lacks (see Axiom 1).

**Numerical pre-check** (scratch `ml_expansion_check.py`, 2026-07-15): against this project's
`Ĥ(k)=Ĉ/(1-ρĈ)` at η∈{0.3, 0.45} (σ=1): `sup‖Ĥ‖` on the expanding pole-avoiding midpoint circles
is *constant* (1.7453 / 1.1636 resp., N=5→59), and the expansion (4 poles per quadruple
`±kₙ,±k̄ₙ`, residues via `Ĉ(p)/(-ρĈ'(p))`) converges pointwise to `Ĥ(k)` at real and complex test
points, errors ~1e-6–1e-7 by N=60.

**Consumers.** `OZFIX.10` Route B (with Axiom-4-free `fourier_kernel_one_pole`, below, this
decomposes the previously-blocked monolithic arc estimate); `OZFIX.9` Route A (`oz_forcing`
expansion); potentially `MML.3`/`GA.4` (mixture inner-DCF assembly).

**Retirement condition.** Delete when Mathlib gains Mittag-Leffler / a residue theorem.

## Companion (NOT an axiom) — `fourier_kernel_one_pole`

**File:** `LeanCode/Analysis/MittagLeffler.lean`. **Proved outright, 2026-07-15** (Group MA, task
`MA.3`) — `#print axioms` = `halfDiskBoundary_eq_sum_of_small_circles` + the standard three (in
particular, **no** dependence on Axiom 3).

`∫_{-R}^{R} e^{ixr}/(x-k₀) dx → 2πi·e^{ik₀r}` as `R→∞`, for `Im k₀ > 0`, `r > 0` — the elementary
building block for Fourier-inverting a Mittag-Leffler expansion termwise. Proof: half-disk
residue-sum theorem (Axiom 2's derived theorem) at the single pole `k₀`, plus
`jordan_lemma_arc_bound` with amplitude `1/(z-k₀)` (bound `1/(R-‖k₀‖) → 0` — exactly the
decaying-amplitude case Jordan's lemma serves; contrast the *inadmissible* monolithic arc estimate
rejected in the preamble, whose amplitude grows `O(R)`).

## Axiom 4 — `sokhotski_plemelj_upper`

**File:** `LeanCode/Analysis/SokhotskiPlemelj.lean`. **Added:** 2026-07-15 (Group MA, task `MA.7`,
user-requested pre-placement — no current task blocks on it).

**Statement (informal).** The classical **Sokhotski–Plemelj formula** (integrated, upper-boundary
form): for `f` integrable and continuous at `x₀`, *given* the symmetric-truncation principal value
exists with value `L`, `lim_{ε→0⁺} ∫ f(x)/(x-x₀-iε) dx = L + iπ·f(x₀)`.

**Why it's an axiom / scope.** Mathlib has no Hilbert transform, no P.V. API, no distributional
boundary values (Y1.3 was re-routed entirely around this gap, `proof_notes_yukawa_wh.md`). The
P.V.'s *existence* is a hypothesis (a plain `Tendsto` of symmetric truncations — no new
definitions), so the axiom asserts only the boundary-value *relation*, not Hölder existence
theory. Only the upper (`+iπ`) version is stated (narrowest form); add the mirror when a consumer
needs it.

**Numerical pre-check** (scratch `sp_check.py`, 2026-07-15): Gaussian at `x₀∈{0, 0.7}` +
oscillatory-modulated Gaussian at `x₀=-1.2`, `ε∈{0.1,0.01,0.001}` — convergence to `P.V.+iπf(x₀)`
linear in `ε`.

**Consumers.** None current ([LN] §6.3-style Wiener–Hopf derivations, potentially `MML.3`).
**Retirement:** when Mathlib gains a Hilbert-transform/P.V. API.

## Axiom 5 — `vanDerCorput_first_derivative_test`

**File:** `LeanCode/Analysis/VanDerCorput.lean`. **Added:** 2026-07-15 (Group MA, task `MA.4`,
user-requested).

**Statement (informal).** The classical **van der Corput lemma** (first-derivative /
non-stationary-phase test with amplitude; Stein, *Harmonic Analysis*, Prop. VIII.1.2 + corollary):
for phase `φ` with monotonic derivative (either direction), `|φ'| ≥ λ > 0`, and `C¹` amplitude
`ψ`: `‖∫_a^b e^{iφ}ψ‖ ≤ (3/λ)·(‖ψ(b)‖ + ∫‖ψ'‖)`.

**Why it's an axiom / retirement.** No oscillatory-integral estimates in Mathlib. Plausibly
*provable* via `intervalIntegral.integral_mul_deriv_eq_deriv_mul` (IBP) — the preferred follow-up;
retire this axiom when proved.

**Numerical pre-check** (scratch `ma45_check.py`, 2026-07-15): monotone-increasing
(`φ=λθ+θ²`, `λ∈{1..500}`) and antitone (`φ=-(λθ+θ²/2)`, `λ∈{2..300}`) branches, two amplitudes —
bound holds with wide margin everywhere, LHS decaying `~1/λ`.

**Consumers.** None current (the once-intended consumer, `OZFIX.10`'s monolithic arc, was shown to
defeat plain VdC — amplitude `O(R)` × gain `1/(rR)` = `O(1)` — and was resolved by the MA.2+MA.3
decomposition instead). General toolbox.

## Companion (NOT an axiom) — `circleAverage_log_norm_le_of_finite_zeros`

**File:** `LeanCode/Analysis/JensenCounting.lean`. **Proved outright, 2026-07-15** (Group MA,
task `MA.5`) — `#print axioms` = the standard three. *Was briefly an axiom earlier the same day;
upgraded to a theorem — and its original statement corrected — when the user asked to attempt the
proof. See the cautionary tale below.*

**Statement.** Jensen counting bound (classical corollary of Jensen's formula; the trivial case
of Nevanlinna's First Main Theorem): `f` meromorphic on `ℂ`, no poles (`divisor ≥ 0`), **finite
divisor support** ⇒ `circleAverage (log‖f·‖) 0 R ≤ M·log R + C` eventually.

**⚠ Cautionary tale — the axiom version was FALSE as first stated.** The first (axiom) version
hypothesized finiteness of the *literal* zero set `{s | f s = 0}` instead of the divisor support.
Counterexample under Lean's junk-value semantics: redefine `sin` to equal `1` at every `nπ` — the
result is still `MeromorphicOn ℂ univ` (meromorphy is a `𝓝[≠]`-germ property, blind to isolated
value changes), still has `divisor ≥ 0`, its literal zero set is *empty* (trivially finite), yet
its circle average grows like `R`. Caught while attempting the proof — the counting hypothesis
must be about *orders* (divisor support), not values. **Lesson recorded**: for meromorphic
functions in Lean, never state value-set hypotheses where the classical theorem means order-set
ones; and prove-first beats axiomatize-first precisely because proving *finds* these bugs.

**Proof.** Mathlib's Jensen formula (`MeromorphicOn.circleAverage_log_norm`) at each `R` large
enough that the closed ball contains the (finite) divisor support; the finsum collapses to a fixed
`Finset` sum (`finsum_eq_sum_of_support_subset`); each term bounded via `divisor ≥ 0`
(`Function.locallyFinsuppWithin.le_def`) by `Dᵤ·log R + Dᵤ·|log‖u‖|`; constants
`M = Σ Dᵤ + D₀`, `C = Σ Dᵤ·|log‖u‖| + log‖meromorphicTrailingCoeffAt f 0‖`. Confirms
`MixtureHSCounting.lean`'s own "mechanical" assessment (`MZERO.9` notes).

**Numerical pre-check** (scratch `ma45_check.py`, 2026-07-15): three entire test functions (2, 0,
5 zeros; exponential factors of varying growth) — circle averages match `m·log R + C` to 4
decimals.

**Consumers.** MZERO Route B: discharges `hJensen` (`infinite_zeros_of_growth`, `MZERO.11`) for
`f := detC`, with one consumer-side bridge: `hJensen` is triggered by *literal*-zero-set
finiteness, so the application needs "literal zeros finite → divisor support finite" for `detC` —
follows from `detC`'s honest analyticity away from `s=0` (`Q0_det_c_differentiableAt`; at analytic
points positive order ⇔ value zero) + at most one extra support point at the origin. Left to the
MZERO owner. After the discharge, Route B's only open input is `DetBoundaryGrowth` (MZERO.10).

## Group MA — MathAxioms task records

*The task group managing this registry: survey the project for missing-Mathlib-machinery gaps,
pre-place admissible axioms (numerics first), prove what's provable. Task table in
`todo_lean.md` (Group MA, top of the Task Status section). One `###` per task below.*

### Task MA.1 — Retroactive re-filing of the OZFIX.10-era pieces

✓ **DONE (bookkeeping, no Lean change).** The three pieces landed during the `OZFIX.6`/`OZFIX.10`
Route B effort — Axiom 1 (`circleIntegral_eq_sum_of_small_circles`), Axiom 2
(`halfDiskBoundary_eq_sum_of_small_circles`), and the axiom-free `jordan_lemma_arc_bound` — are
re-filed under Group MA as its founding content (registry entries above; `todo_lean.md` Axioms
table rows re-tagged). Cross-reference: `proof_notes_ozfix.md` `OZFIX.10` for the application-side
narrative that motivated them.

### Task MA.2 — Mittag-Leffler expansion axiom

✓ **DONE.** Axiom 3 above (`mittagLeffler_expansion_of_bounded_on_circles`,
`Analysis/MittagLeffler.lean`). Numerical pre-check passed at two state points BEFORE the
statement was committed (per group discipline; details in the registry entry). Statement mirrors
`circleIntegral_eq_sum_two_pi_I_mul_of_simple_poles`'s simple-pole encoding (local `g n z/(z-pₙ)`
representation on disjoint closed balls) so the two compose naturally. Key design choices:
ordered-`Tendsto` conclusion (classical grouping, not `HasSum` — honest about conditional
convergence); pole enumeration by nondecreasing modulus (`hpmono`) standing in for the classical
"circles contain initial segments" bookkeeping.

### Task MA.3 — One-pole Fourier kernel (genuine theorem)

✓ **DONE, no new axiom** — `fourier_kernel_one_pole` (`Analysis/MittagLeffler.lean`), companion
entry above. Three-step proof: (1) `fourier_kernel_halfdisk` (private) instantiates the half-disk
residue-sum theorem at the single pole (`ι := Fin 1`, `g z = e^{izr}`, ball radius `Im k₀/2` keeps
it in the open upper half-disk); (2) `fourier_kernel_arc_bound` (private) rewrites the arc
integrand into `jordan_lemma_arc_bound`'s exact shape (`integral_congr` + `ring`) and applies it
with `M = 1/(R-‖k₀‖)`; (3) Tendsto assembly: `squeeze_zero_norm'` on the arc (bound → 0 via
`tendsto_inv_atTop_zero`), `Filter.Tendsto.congr'` against the eventually-valid finite-`R`
identity. **Lean pitfall for the record:** applying `jordan_lemma_arc_bound` via bare `apply`
caused a `whnf` heartbeat timeout (higher-order unification searching for `g`); fixed by supplying
the implicits explicitly — `refine jordan_lemma_arc_bound (g := fun z => 1/(z-k₀)) (a := r)
(M := …) … ?_ ?_`.

### Task MA.4 — First-derivative oscillatory test (Van der Corput style)

✓ **DONE (as axiom, user-requested; previously parked).** Axiom 5 above
(`vanDerCorput_first_derivative_test`, `Analysis/VanDerCorput.lean`), numerically pre-checked in
both monotone branches before statement. Design: `hmono` accepts `MonotoneOn ∨ AntitoneOn`
(classical "φ' monotonic"); constant `3` per Stein. Preferred follow-up recorded in the registry
entry: prove via Mathlib IBP and retire — this is the one Group-MA axiom assessed as genuinely
provable with bounded effort. Note the historical insufficiency finding (plain VdC gives only
`O(1)` for OZFIX.10's monolithic arc) stands — this is toolbox, not that consumer's solution.

### Task MA.5 — Jensen counting bound (narrow argument-principle substitute)

✓ **DONE — PROVED, no axiom** (upgraded same-day from an axiom at user request; see the companion
registry entry above for the full story). Two-stage history worth recording:
1. **First landed as an axiom with a FALSE statement** — literal-zero-set finiteness instead of
   divisor-support finiteness; falsified by the junk-value `sin`-modification counterexample
   (found *while attempting the proof*, not by review — the strongest argument for the
   prove-first discipline this group's charter now enforces).
2. **Corrected + proved outright** from Mathlib's `MeromorphicOn.circleAverage_log_norm`
   (~90 lines: divisor restriction ball↔univ via `divisor_apply`, finsum → `Finset` sum, termwise
   `log(R‖u‖⁻¹) ≤ log R + |log‖u‖|` with `divisor ≥ 0`). `#print axioms` = standard three.
Consumer-side note: the `hJensen` discharge for `detC` now additionally needs the (mechanical)
"literal zeros finite → divisor support finite" bridge via `detC`'s analyticity away from `0`;
recorded in the registry entry. Left to the MZERO owner.

### Task MA.6 — Relocate misfiled pure-math files to `Analysis/`

✓ **DONE.** `ResidueAtSimplePole.lean` and `BanachPoleFamily.lean` moved
`LeanCode/HardSphere/ → LeanCode/Analysis/` (survey confirmed both are `import Mathlib`-only, zero
project-definition usage — project names appeared in docstring prose only). Import paths updated
in `LeanCode.lean` + 5 consumers (`BaxterPoles`, `BaxterResidue`, `YukawaPoleResidue`,
`MixtureHSPoles`, `MixtureHSZeros`); namespaces (`FMSA.HardSphere`, `FMSA.BanachPoleFamily`)
deliberately kept to avoid touching proof bodies; doc references updated across
`proof_notes_pole.md`/`proof_notes_yukawa_wh.md`/`todo_lean.md`. Full `lake build` green.

### Task MA.7 — Sokhotski–Plemelj boundary values

✓ **DONE.** Axiom 4 above (`sokhotski_plemelj_upper`, `Analysis/SokhotskiPlemelj.lean`),
user-requested pre-placement. Numerical pre-check passed before statement (registry entry).
Design: P.V. existence as hypothesis (no new definitions, no Hölder theory), upper version only.
