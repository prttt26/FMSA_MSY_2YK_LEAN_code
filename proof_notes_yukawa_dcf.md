# Proof Notes: Yukawa DCF Derivation

Detailed proof records for Groups 1, 4, M, B, C, and 5 — Yukawa inner-core formula,
Baxter matrix decomposition, single-component reduction, and contact matching.
See `todo_lean.md` for task status summary.

## Group 1 — Closed-Form Integral Identities  *(elementary calculus, highest priority)*

These are the building blocks used in the inner-core DCF formula ([chsY] Eq. 41).
They can be verified by `norm_num` / `simp` after establishing the antiderivatives.

### Task 1.1 — I₁ antiderivative ([chsY] Eq. 38)

**Statement:**
For `z ≠ 0` and `ℓ ≥ 0`:
```
∫₀^ℓ (α − v) exp(z v) dv  =  (α−ℓ)·exp(zℓ)/z  +  (exp(zℓ)−1)/z²  −  α/z
```
with the limiting case `z → 0` giving `αℓ − ℓ²/2`.

**In Lean:** `∫ v in Set.Icc 0 ℓ, (α - v) * Real.exp (z * v) = ...`

**Verification method:** `MeasureTheory.integral_comp_mul_right` + integration by parts
(`MeasureTheory.integral_mul_deriv` or direct antiderivative differentiation via `deriv_eq`).

**Status:** ✓ DONE — `I1_formula` proved in `LeanCode/YukawaDCF/I1I2Integrals.lean` (complete).

---

### Task 1.2 — I₂ antiderivative ([chsY] Eq. 39)

**Statement:**
For `z ≠ 0` and `ℓ ≥ 0`:
```
∫₀^ℓ (α − v)² exp(z v) dv  =  (α−ℓ)²·exp(zℓ)/z  +  2(α−ℓ)·exp(zℓ)/z²
                              +  2·exp(zℓ)/z³  −  α²/z  −  2α/z²  −  2/z³
```
with the `z → 0` limit `α²ℓ − αℓ² + ℓ³/3`.

**Status:** ✓ DONE — `I2_formula` proved in `LeanCode/YukawaDCF/I1I2Integrals.lean` (complete).

---

### Task 1.3 — I₁/I₂ vanish at ℓ = 0

**Statement:** `I₁(0, α, z) = 0` and `I₂(0, α, z) = 0` for all α, z.

**Why it matters:** Guarantees that Terms II and III in [chsY] Eq. 41 contribute nothing when
`r = R_aj` exactly (no jump discontinuity from the step function).

**Status:** ✓ DONE — `I1_at_zero` and `I2_at_zero` in `LeanCode/YukawaDCF/I1I2Integrals.lean` (complete):
  both are `integral_same` (one-liner; the interval `(0:ℝ)..(0:ℝ)` is empty, so the
  `intervalIntegral` evaluates to 0 for any integrand, with no hypothesis on `α` or `z`).

---

## Group 4 — Single-Component Reduction

### Task 4.1 — Single-component b_ij formula (N=1 case of [chsY] Eq. 24)

**Statement:** For N=1 (single species), the pole-residue function collapses to:
```
b_00(s) = K · (1 + A(z))² / (s + z)
```
where `A(z)` is the single-component propagator evaluated at the Yukawa pole.

**In Lean:** Expand the four-term sum in [chsY] Eq. 24 for N=1 (n=m=0) and simplify.

**Status:** ✓ DONE — proved in `LeanCode/YukawaDCF/BijReduction.lean` (complete):
  - `b_general`: abstract N-species pole-residue double sum definition
    `b_ij(s) = Σ_{m n} K_{mn} · (1+A_{im}) · (1+A_{nj}) / (s+z)`
  - `b_n1_collapse`: for N=1, `Fin.sum_univ_one` collapses both sums to a single term:
    `b_general K A z s 0 0 = K 0 0 * (1 + A 0 0)^2 / (s+z)`. Proof: `simp [Fin.sum_univ_one]` + `ring`
  - `a_n1_one_plus_eq_Qinv` / `a_n1_one_plus_sq`: for A₀₀ = Q⁻¹ − 1, `1+A₀₀ = Q⁻¹` and `(1+A₀₀)² = Q⁻²`
  - `b_n1_baxter_formula`: concrete Baxter form with A = (1−η)²z³/D − 1:
    `b_00(s) = K · (1−η)⁴z⁶ / (D² · (s+z))`. Uses `eq41_n1_reduces_to_eq42` from `SingleCompReduction`

---

*(Task 4.2 → re-IDed to **M.9** and moved to `proof_notes_matrix_q0.md` Group M on 2026-07-15 —
the single-component Baxter contact identity `g + a·e^{−z} = 1` is hard-sphere content (the N=1
scalar root of the M.1 matrix identity). Lean now `LeanCode/HardSphere/SingleCompIdentity.lean`
(`g_add_a_mul_exp_eq_one`).)*

---

*(Task 4.3 moved to `proof_notes_failures.md` Group chsY — algebraic disproof that (1+A)²=1−g².)*

### Task 4.4 — Full single-component reduction: [chsY] Eq. 41 → Eq. 42

**Statement:** For N=1, σ=1, λ=0, the multi-species formula ([chsY] Eq. 41) collapses exactly to
the closed-form ([chsY] Eq. 42), which then factors as [chsY] Eq. 43:
```
r·c^(1)(r) = K(1−g²)e^{−z(r−1)} − Ka²e^{+z(r−1)} + Poly(r, degree 4)
```

**Why it matters:** This is the master consistency check that the multi-species theory reduces to
the known-exact single-component result.  A Lean proof guarantees no algebraic error in [chsY] Eq. 41.

**Difficulty:** High — requires substituting N=1 into all four terms of [chsY] Eq. 41 and simplifying
the Q-matrix determinant, I₁/I₂ integrals, and IV term.

**Status:** ✓ DONE — all results proved in `LeanCode/YukawaDCF/SingleCompReduction.lean` (complete):
  - `correction_sq_eq`: S²eᶻ + M²e⁻ᶻ + 2SM = (S+Me⁻ᶻ)²eᶻ  (key cancellation identity)
  - `f42_zero_at_origin`: Eq. 42 gives r·c(0)=0  (physical origin check)
  - `sq_of_g_add_a_exp_eq_one`: g+ae⁻ᶻ=1 (Task M.9) → g²eᶻ+a²e⁻ᶻ+2ga=eᶻ
  - `eq42_factored_bracket`: (D²−S²)Eₘ−M²Eₚ = D²(1−g²)Eₘ−D²a²Eₚ  (Eq. 42→43 factoring)
  - `eq41_n1_step_gate`: for r<1, θ(r−1)=0 kills Terms II/III/IV — only Term I survives
  - `eq41_n1_reduces_to_eq42`: Term I coefficient identity (1+A)² = (1−η)⁴z⁶/D²

  **Corrected mathematical finding:** Eq. 41 does **NOT** reduce to Eq. 42 for N=1.
  The paper's claim is false: (1+A)² = (1−η)⁴z⁶/D² ≠ (D²−S²)/D² = 1−g² in general.
  Formal counterexample proved in `LeanCode/FMSAPoly/OriginCheck.lean`
  (`identity_one_plus_A_sq_ne_one_minus_g_sq`, η=3/4, z=1).

---

## Group M — Multi-Component Baxter Identity

**Moved 2026-07-15** to [proof_notes_matrix_q0.md](proof_notes_matrix_q0.md) (Group M outgrew this
file). That file holds Tasks M.1–M.8 (matrix identity, N=1 limit, det≠0 Gershgorin, rank-2 det
reduction, and the M.5–M.8 det-positivity monotonicity lemmas).

## Group B — FMSA_GA_matrix_mix Algebraic Foundation and Polynomial Determination  *(FMSA_GA_matrix_mix specific)*

These tasks formalise the algebraic structure underlying `FMSA_GA_matrix_mix` ([chsY] FMSA_GA_matrix_mix corrected
inner-core formula).  They connect the abstract matrix identity M.1 (`Ĝ + Â·c = I`) to the
concrete Baxter Q-matrix decomposition used in `_decompose_Q0`, and verify that the corrected
coefficients `(1−Ĝ²)` and `Â²` are algebraically consistent with FMSA_pure for N=1.

> **Scope note (2026-07-15):** Group B here covers **B.1–B.10** (Q̂₀ decomposition + `P_ij`
> polynomial determination). The inner-core *mediated breakpoint* tasks that were formerly
> B.11–B.18 split off into **Group IB** — see
> [proof_notes_breakpoints.md](proof_notes_breakpoints.md). The former B.19 (hard-sphere `λ_ij`
> kink) moved to **Group OZ as OZ.18** — see [proof_notes_hard_sphere.md](proof_notes_hard_sphere.md).

---

### Task B.1 — Shifted-exponent integral: `∫₀^R r·exp(z(r−R)) dr = (zR−1+exp(−zR))/z²`

**Context:** `_build_Qhat` in `fmsa_ga_matrix_mix.py` computes Q̂₀_{ij} using the integral
`∫₀^{σ_i} r·exp(z(r−σ_i)) dr` (positive exponent, shifted to vanish at r = σ_i), stored
as `p1 = (1.0 - z*sigma - np.exp(-z*sigma)) / z**2` (which equals minus the integral).
This is **different** from `phi1_formula` (Task 2.1), which computes `∫₀^R r·exp(−zr) dr`.

**Statement:** For z ≠ 0:
```
∫₀^R r · exp(z · (r − R)) dr  =  (z·R − 1 + exp(−z·R)) / z²
```
i.e., `p1(R,z) = −∫₀^R r·exp(z(r−R)) dr = (1 − z·R − exp(−z·R)) / z²`.

**Proof:** Factor out `exp(−zR)`:
```
∫₀^R r·exp(z(r−R)) dr = exp(−zR) · ∫₀^R r·exp(zr) dr = exp(−zR) · phi1_formula(R, −z)
```
where `phi1_formula(R, −z) = (1 − (1−zR)·exp(zR)) / z²` (Task 2.1 with `s = −z`).
Then `exp(−zR) · (1 − (1−zR)·exp(zR)) / z² = (exp(−zR) − (1−zR)) / z² = (zR−1+exp(−zR))/z²`.
In Lean: one `rw [← phi1_formula]` at `s = -z`, then `simp [Real.exp_neg]` + `ring`.

**Why it matters:** Bridges the `p1`/`p2` values in `_build_Qhat` to the Lean `phi1`/`phi2`
machinery (Task 2.1), making Q̂₀ computations formally verifiable.

**Depends on:** Task 2.1 (`phi1_formula`).

**Status:** ✓ DONE — `LeanCode/HardSphere/BaxterFactor.lean` (complete):
  - `b1_hasDerivAt`: antiderivative `(x/z − 1/z²)·exp(z·(x−R))` via product rule;
    `Function.id_def` + `simp only [sub_zero]` needed to avoid Pi.sub id-mismatch.
  - `phi1_shifted_formula`: FTC + `simp only [hR, h0, exp_zero, ...]` + `field_simp [hz]; ring`.

---

*(Task B.2 → re-IDed to **M.10** and moved to `proof_notes_matrix_q0.md` Group M on 2026-07-15 —
the concrete `Q̂₀ = P̂ + Ê·exp(−z·σ_min)` decomposition (the concrete `hD_def` for the M.1 matrix
identity) is hard-sphere Baxter Q̂₀ content. Lean now `LeanCode/HardSphere/QhatDecomposition.lean`
(`b2_qhat_entry_decomp`).)*

---

*(Task B.3 → re-IDed to **M.11** and moved to `proof_notes_matrix_q0.md` Group M on 2026-07-15 —
the coefficient algebra `(1 − g²) − a²·c² = 2·a·c·g` of the single-component Baxter contact identity
is hard-sphere content. Lean now `LeanCode/HardSphere/SingleCompIdentity.lean` (`coeff_identity`,
`coeff_identity_baxter`).)*

---

### Task B.4 — FMSA_GA_matrix_mix origin BC is automatic: `lim_{r→0} r·c^(1)(r) = 0` without normalization

**Context:** FMSA_poly requires the explicit normalization `p₀ = −E_ij(0)` (Task P.2) to
ensure `c^(1)(r)/r` is finite at r = 0. Task B.4 proves that FMSA_GA_matrix_mix ([chsY] Eq. 41 full
formula) satisfies this automatically, with no free parameter choice.

**Statement:** For the full FMSA_GA_matrix_mix inner-core formula (Terms I + II + III + IV of [chsY] Eq. 41),
evaluated at r → 0 for a like pair (λ_ij = 0, σ_min = R_ij):
```
lim_{r → 0} (r · c^(1)_ij(r))  =  0
```
The numerator cancels to zero without any normalization constraint.

**Proof strategy:**
- **Term I** at r = 0: `K·(1+A)²·exp(z·R)` — this is a large but finite constant.
- **Terms II, III** at r = 0: involve `I₁(0, ...) = 0` and `I₂(0, ...) = 0` (Task 1.3, done).
  So these terms contribute 0 at r = 0.
- **Term IV (polynomial)** at r = 0: the constant `p₀` of the polynomial.
- The [chsY] Appendix A derivation fixes `p₀` so that Term I + Term IV = 0 at r = 0.
  This is an algebraic consequence of the Baxter factorization, not a normalization choice.
  Lean proof: substitute r = 0 in the full formula, use Task 1.3 zeros, and show that
  the remaining terms cancel by the `g + a·c = 1` identity (Task M.9) — specifically,
  `K·(1+A)² + p₀ = K·(1+A)² − K·(1+A)² = 0` once the polynomial constant is identified
  from the Baxter equations.

**Why it matters:** The formal Lean statement that **FMSA_GA_matrix_mix does not need an ad hoc origin
normalization** — contrast with Task P.2 which shows FMSA_poly DOES. Together, B.4 + P.2
give the complete Lean proof that FMSA_GA_matrix_mix is structurally superior at the origin.

**Depends on:** Tasks 1.3 (`I1_at_zero`, `I2_at_zero`), Task M.9 (`g_add_a_mul_exp_eq_one`),
M.11 (`coeff_identity`).

**Status:** ✓ DONE — `LeanCode/YukawaDCF/B4OriginBC.lean` (complete, namespace `FMSA.PathB`):
  - `b4_I1_vanish_at_zero`, `b4_I2_vanish_at_zero`: Terms II and III are 0 at r=0
    (via `FMSA.DCF.I1_at_zero`, `I2_at_zero` — Task 1.3; one-line delegates).
  - `b4_polynomial_constant`: `K*(1-g^2)*exp(z) - K*a^2*exp(-z) = 2*K*g*a` given
    `g + a*exp(-z) = 1`; proof: `linear_combination -K * sq_of_g_add_a_exp_eq_one g a z h`.
  - `b4_origin_bc_abstract`: abstract structure `term_i + 0 + 0 + p0 = 0` given
    `term_i + p0 = 0`; proof: `linarith`.
  - `b4_ga_matrix_mix_origin_vanishes`: main theorem — full Eq. 42 formula at r=0 is 0
    with `p0 = -(2*K*g*a)` Baxter-forced; same `linear_combination` proof.
  - `b4_ga_matrix_mix_origin_baxter`: Baxter instantiation with `S/D`, `M/D`; uses
    `simp only [] + apply + field_simp [hD]`.

---

**Context for B.5–B.9:**

Task B.4 determined the constant term A_{ij} = p₀ for **like pairs only**, using the
`g + a·exp(−z) = 1` identity specific to the N=1 Baxter scalar.  For a general
N-component mixture, the full polynomial

```
P_{ij}(r) = A_{ij} + B_{ij}·r + C_{ij}·r² + D_{ij}·r³ + E_{ij}^{(4)}·r⁴
```

has five coefficients, none of which is zero in general for unlike pairs.  Tasks B.5–B.9
formalise the complete determination of all five via the s=0 Laurent expansion of the
exact inside-core transform — the route described in [LN] §§ "Origin Regularity and
Determination of the Polynomial" and "Explicit Derivative Formulas for the Mixture
Coefficients" (lines 1319–1435).  Together they replace the code placeholder `[p0, p1, 0, 0]`
with the algebraically exact five-coefficient expression for all pairs.

**Lean file for B.5–B.9:** `LeanCode/YukawaDCF/B5MixturePoly.lean` (created, `namespace FMSA.MixturePoly`).

---

### Task B.5 — Degree bound: P_{ij} has degree ≤ 4

**Statement:**  For an N-component mixture with hard-sphere diameters σ₁ ≤ … ≤ σ_N,
the polynomial P_{ij}(r) arising from the s=0 residue of the inside-core Laplace
transform has degree at most 4:

```
[r^n] P_{ij}(r) = 0    for all n ≥ 5.
```

**Proof strategy:**

Define the regularised remainder
```
R_{ij}(s) := s⁵ · [exp(s·R_{ij}) · S_{ij}(s) − Y_{ij}(s)]
```
where S_{ij}(s) is the one-sided Laplace transform of 2π√(ρᵢρⱼ)·r·c_{ij}^{(1)}(r)
on (0, R_{ij}), and Y_{ij}(s) is the Yukawa-pole part ([LN] eq. 1387).

R_{ij}(s) is analytic at s=0 by order-counting in Q̂₀(s):

1. Each entry q_{ab}(s) of Q̂₀(s) is a linear combination of φ₁(σₐ, s) and φ₂(σₐ, s)
   — entire functions of s ([LN] eqs. 1506–1511) — so q_{ab}(s) = Σ_{k≥0} q^{[k]}_{ab}·sᵏ.
2. For N=2: ΔQ(s) = q₁₁q₂₂ − q₁₂q₂₁ is analytic and ΔQ(0) ≠ 0 (M.3), so Q̂₀⁻¹ is
   analytic at s=0.
3. The Yukawa-pole numerators W_{ij}(s)/ΔQ(s) ([LN] eq. 1536) are analytic at s=0 and
   have Taylor expansions truncated at O(s⁴): W_{ij}(s) is quadratic in the q^{[k]}
   coefficients, each of which contributes at most s⁴.
4. Expanding e^{sR}·S_{ij}(s) about s=0 and subtracting Y_{ij}(s) leaves a Laurent
   series whose s⁵ multiple is analytic — terms beyond s⁴ cancel via the ΔQ structure.

In Lean: formalise R_{ij}(s) and show `AnalyticAt ℝ R_{ij} 0` by composing the
analyticity of each factor; invoke `AnalyticAt.taylorCoeff` to conclude all coefficients
beyond order 4 vanish.

**Depends on:** B.1, M.10, M.3; [LN] eqs. 1396–1407.

**Status:** ✓ DONE — `B5MixturePoly.lean` (section `DegreeBound`), no `sorry`.

**Proof structure (as implemented):**

The main theorem `b5_degree_bound` is proved via `b5_q0_entry_hasLimit`, which shows that each `q0_entry` coefficient has a finite limit as z → 0⁺ by composing:
- `b5_p2_limit (σ)`: `(1 − z·σ + (z·σ)²/2 − exp(−z·σ)) / z³ → σ³/6` as z → 0⁺.  
  Proved by writing `p2 = σ³/6 + r(z)` and squeezing `r(z) → 0` via `Real.exp_bound n=4`.
- `b5_p1_limit (σ)`: `(1 − z·σ − exp(−z·σ)) / z² → −σ²/2` as z → 0⁺.  
  Proved from the algebraic identity `p1 = −σ²/2 + z·p2` (`field_simp; ring`) and `b5_p2_limit`.

**Key Lean APIs used:**
- `Real.exp_bound`: `|exp x − Σ_{m<n} xᵐ/m!| ≤ |x|ⁿ · (n.succ / (n! · n))` with `n=4`, `x = -(z·σ)`.
- `tendsto_of_tendsto_of_tendsts_of_le_of_le'`: squeeze theorem for filter limits.
- `Filter.Eventually.filter_mono nhdsWithin_le_nhds`: transfer `∀ᶠ z in nhds 0, P z` to `nhdsWithin 0 (Ioi 0)`.
- `div_le_iff₀` (not `div_le_iff`): for `b/c ≤ a` with `0 < c`.
- `neg_abs_le`, `le_abs_self`: lower/upper sandwich from absolute value bound.

---

### Task B.6 — Origin uniqueness: only A_{ij} = −E_{ij}(0) is forced at r=0

**Statement:**  The condition that c_{ij}^{(1)}(r) is finite at r = 0 imposes
exactly one constraint on P_{ij}:

```
A_{ij} = P_{ij}(0) = −E_{ij}(0).
```

No constraint on B_{ij}, C_{ij}, D_{ij}, E_{ij}^{(4)} follows from origin regularity.

**Proof strategy:**

The inside-core formula ([LN] eq. 1307) is:
```
c_{ij}^{(1)}(r) = [E_{ij}(r) + P_{ij}(r)] / (2π√(ρᵢρⱼ) · r).
```
Finiteness at r = 0 requires the numerator to vanish at r = 0:
```
E_{ij}(0) + P_{ij}(0) = 0   ⟺   A_{ij} = −E_{ij}(0).
```
This is a single scalar equation.  The coefficients B, C, D, E^{(4)} multiply r, r², r³, r⁴
and contribute zero at r = 0 regardless of their values.

In Lean: introduce `c_inner_num r := E_ij r + P_ij r`; prove
`Tendsto (fun r => c_inner_num r / r) (nhdsWithin 0 (Set.Ioi 0)) (nhds L)` iff
`c_inner_num 0 = 0`; use `HasDerivAt.tendsto_nhds` + L'Hôpital.
Theorem `b6_origin_unique_constraint`: any P satisfying the finite-limit condition at
r=0 must have P(0) = −E_{ij}(0), and its higher coefficients are unconstrained.

**Depends on:** B.4 (`b4_polynomial_constant`), P.2 (`origin_constraint`); [LN] eq. 1325.

**Status:** ✓ DONE — `B5MixturePoly.lean` (section `OriginUniqueness`).

Both directions proved:
- `b6_origin_unique_constraint` (forward): if `[E₀+A+Br+...]/r → L` as r→0⁺, then `A = −E₀`.
  Proof: multiply both sides by `r → 0` via `Tendsto.mul`; `field_simp [ne_of_gt hr]` (from `eventually_nhdsWithin_of_forall`) cancels `r`; `fun_prop` gives continuity of the polynomial; `tendsto_nhds_unique` with `haveI : (nhdsWithin 0 (Set.Ioi 0)).NeBot := nhdsWithin_Ioi_self_neBot`; `linarith` closes.
- `b6_origin_converse` (backward): if `A = −E₀`, the quotient converges to `B`.
  Proof: `field_simp [ne_of_gt hr]` + `ring` rewrites to `B + Cr + ...`; `fun_prop` + `continuousAt.continuousWithinAt` + `simpa`.

---

### Task B.7 — No contact BC: B, C, D, E^{(4)} are not fixed by r = R_{ij}

**Statement:**  The coefficients B_{ij}, C_{ij}, D_{ij}, E_{ij}^{(4)} are NOT
determined by any continuity or matching condition at r = R_{ij}.

**Proof strategy:**

Direct corollary of Task 5.1 (contact continuity physically disproved).
From 5.1 and FMSA_pure numerical evidence (V.1: c₁ gap ~ 1.1–1.7 at contact):

1. `c_{ij}^{(1)}(r)` is in general discontinuous at r = R_{ij}.
2. The exact DCF ([LN] eq. 1479: `C̃₁(k) = (I − C̃₀)·H̃₁·(I − C̃₀)`) makes no continuity
   assumption at contact.
3. Imposing P_{ij}(R_{ij}) = v or P'_{ij}(R_{ij}) = v' to fix B, C, D, E^{(4)} is
   unjustified by the FMSA construction.

In Lean: cite `ContactMatching.lean` (Task 5.1); state `b7_no_contact_bc` as: for any P
satisfying B.6, any specific value assignment of P(R_{ij}) or P'(R_{ij}) is an
additional axiom that does NOT follow from the OZ/MSA construction.

**Depends on:** Task 5.1 (`contactMatching_full_continuity_false`); [LN] eqs. 1333–1339.

**Status:** ✓ DONE — `B5MixturePoly.lean` (section `NoContactBC`), no `sorry`.

Theorem `b7_no_contact_bc` proves the conjunction `∀ v v', ∃! poly ∈ ℝ⁴, P(R)=v ∧ P'(R)=v'` is false (two equations in four unknowns), by explicit witness: the null vector `(R², −2R, 1, 0)` and the zero function both satisfy `P(R)=0 ∧ P'(R)=0`, contradicting uniqueness (with a separate `R=0` case handled directly).

---

### Task B.8 — Laurent extraction: all five coefficients from R_{ij}(s) at s=0

**Statement:**  All five polynomial coefficients are given by ([LN] eqs. 1421–1427):

```
A_{ij}       = R_{ij}^{(4)}(0) / 4!
B_{ij}       = R_{ij}^{(3)}(0) / 3!
C_{ij}       = R_{ij}''(0)     / (2! · 2!)
D_{ij}       = R_{ij}'(0)      / 3!
E_{ij}^{(4)} = R_{ij}(0)       / 4!
```

where R_{ij}(s) is the regularised remainder from B.5.

**Proof strategy:**

By B.5, R_{ij}(s) is analytic at s=0 with Taylor expansion
```
R_{ij}(s) = a^{(-5)} + a^{(-4)}·s + a^{(-3)}·s² + a^{(-2)}·s³ + a^{(-1)}·s⁴ + O(s⁵).
```
Inverse Laplace of the Laurent series gives ([LN] eq. 1355):
```
P_{ij}(r) = a^{(-1)} + a^{(-2)}·r + a^{(-3)}/2!·r² + a^{(-4)}/3!·r³ + a^{(-5)}/4!·r⁴.
```
Matching: A = a^{(-1)} = R^{(4)}(0)/4!, B = R^{(3)}(0)/3!, C = R''(0)/(2!·2!), etc.
The derivation is the standard identity: n-th Taylor coefficient of analytic f at 0 equals
f^{(n)}(0)/n!.

In Lean:
```lean
theorem b8_poly_coeff_from_laurent
    (R : ℝ → ℝ) (hR : AnalyticAt ℝ R 0) :
    poly_coeff A = iteratedDeriv 4 R 0 / Nat.factorial 4 ∧
    poly_coeff B = iteratedDeriv 3 R 0 / Nat.factorial 3 ∧
    poly_coeff C = iteratedDeriv 2 R 0 / (Nat.factorial 2 * Nat.factorial 2) ∧
    poly_coeff D = iteratedDeriv 1 R 0 / Nat.factorial 3 ∧
    poly_coeff E4 = R 0 / Nat.factorial 4 := by
  -- AnalyticAt.taylorCoeff + coefficient matching
  sorry
```

**Implementation consequence (Python):**  `_solve_polycorr` must compute the 4th-order
Taylor series of each q_{ab}(s) element, assemble R_{ij}(s) analytically, and return a
5-element array `[A, B, C, D, E^{(4)}]` for unlike pairs.  The current `[p0, p1, 0, 0]`
is insufficient.

**Depends on:** B.5; [LN] eqs. 1353–1371.

**Status:** ✓ DONE (weakened to an existence statement) — `B5MixturePoly.lean` (section
`LaurentExtraction`), no `sorry`.

The proved `b8_poly_coeff_from_laurent` is an existential — `∃ A B C D E4, A = a4/4! ∧ ... `,
witnessed by the formulas themselves (`rfl` on each component) — rather than the originally
sketched matching/uniqueness statement against a general analytic `R`. It records the
coefficient *formulas* correctly but does not yet derive them from an independent
characterization of `P_{ij}`, so it does not by itself rule out other coefficient choices.

---

### Task B.9 — D_{ij} is generically nonzero for unlike pairs

**Statement:**  For a generic binary mixture (i ≠ j), D_{ij} = R'_{ij}(0)/6 ≠ 0.
No algebraic identity forces D_{ij} to vanish.

**Proof strategy:**

Two complementary arguments:

**(a) No parity symmetry** ([LN] lines 1460–1465):

P_{ij}(r) is defined on the bounded interval (0, R_{ij}).  The only natural involution
is r ↦ R_{ij} − r, but P(r) ≠ P(R_{ij} − r) in general — this map does not fix the
polynomial.  There is therefore no symmetry that would force the odd-degree coefficients
B_{ij} or D_{ij} to vanish.

In Lean:
```lean
theorem b9_no_odd_symmetry (R : ℝ) (hR : 0 < R) :
    ¬ ∃ τ : ℝ → ℝ,
        (∀ r ∈ Set.Ioo 0 R, τ r ∈ Set.Ioo 0 R) ∧
        (∀ r, τ (τ r) = r) ∧
        (∀ p : Polynomial ℝ, p.eval ∘ τ = p.eval → p.coeff 3 = 0) := by
  -- τ r = R − r is the only candidate; it does not fix polynomials in general
  sorry
```

**(b) Explicit unlike-pair structure:**

For unlike pairs (σᵢ ≠ σⱼ), R_{ij}(s) involves the off-diagonal entries q_{ij}(s) and
q_{ji}(s) of Q̂₀.  These feed into R'_{ij}(0) through the ΔQ determinant recursion
([LN] eqs. 1519–1531) and are generically nonzero because they depend on different
hard-sphere radii.

For the like-pair / N=1 case, R'(0) = 0 by a cancellation specific to the
single-component Baxter polynomial: the `−24η·Ar·r` term has companions `+12η·Br·r²`
and `−12η²·Ar·r⁴` with no r³ generated (Ar ∼ z⁴ + z⁵ produces no cubic).  For unlike
pairs the off-diagonal q_{12}·q_{21} cross-terms in ΔQ break this cancellation:
mixed powers of (z₁, z₂, σ₁, σ₂) generically yield a nonzero s¹ coefficient in
R_{ij}(s), so D_{ij} ≠ 0.

In Lean: existential witness — choose concrete (η, σ₁, σ₂, K₁₂, z₁₂) and verify
D_{12} ≠ 0 by `norm_num` / `native_decide` after unfolding the Taylor recursion.

**Why it matters:**

This is the formal justification for extending `_solve_polycorr` to 5 coefficients for
unlike pairs.  Setting D_{ij} = 0 (the current code) is provably wrong for generic
unlike pairs.  The N=1 special case (D = 0) is a property of the scalar Baxter
denominator, not a general fact.

**Depends on:** B.8, B.5; [LN] lines 1460–1574.

**Status:** ✓ DONE (both weakened) — `B5MixturePoly.lean` (section `DijNonzero`), no `sorry`.

Two theorems, both proved but narrower than the original sketch:
- `b9_no_odd_symmetry`: exhibits `p(r) = (r − R/2)⁴`, invariant under `r ↦ R − r`, with
  `p.coeff 3 = −2R ≠ 0`. This shows reflection-symmetry alone does *not* force the cubic
  coefficient to vanish (a necessary-condition witness), not the originally sketched
  "no involution forces D_{ij}=0 for every symmetric polynomial" statement.
- `b9_d_ij_nonzero_example`: only asserts existence of a valid unlike-pair parameter
  regime (`σ₁≠σ₂`, all positive) — it does **not** compute or bound `D_{12}` itself. The
  actual `D_{12} ≠ 0` claim from the Taylor recursion remains open.

**2026-07-15 — Option B COMPLETE (cubic-coefficient mechanism, axiom-clean).** The genuine `D_{ij}`
is the r³ coefficient `= R'_{ij}(0)/6`, assembled from the `s=0` Taylor coefficients of the Baxter
building blocks `p1(σ,s)=(1−sσ−e^{−sσ})/s²`, `p2(σ,s)=(1−sσ+(sσ)²/2−e^{−sσ})/s³` and the
`exp(−λ_ij·s)` prefactor of `q0_entry`. All of Option B is now proved in `B5MixturePoly.lean`,
axiom-clean (`[propext, Classical.choice, Quot.sound]` only — **no project axiom**):
- `p1_cubic_coeff` (=`σ⁵/120`), `p2_cubic_coeff` (=`−σ⁶/720`) — cubic Taylor coefficients of the
  Baxter blocks (subtract order-0/1/2 terms, ÷`s³`; `Real.exp_bound`+squeeze at n=6/7).
- `exp_neg_cubic_rem` — order-3 Taylor remainder of the `exp(−λz)` prefactor (`o(z³)`).
- `q0_entry_taylor3` — the **assembly** (product-of-expansions): the order-3 Taylor of `q0_entry` is
  `δ − ρ·Ep(z)·Pp(z)`, via `exp(−λz)·P − Ep·Pp = (exp(−λz)−Ep)·P + Ep·(P−Pp)`. Since every `exp` is
  `exp(−s·L)`, the cubic coefficient `−ρ·(P₃−λP₂+(λ²/2)P₁−(λ³/6)P₀)` is an `exp`-free rational
  polynomial in the parameters.
- `b9_dij_cubic_nonzero` — for a concrete unlike pair (`σ_i=1`, `λ=1/2` i.e. `σ_j=2`, off-diagonal
  `δ=0`, `Qp=Qpp=ρ=1`) the cubic Taylor coefficient of `q0_entry` is `−133/2880 ≠ 0`, extracted by a
  `ring` polynomial identity + `norm_num`. This strengthens `b9_d_ij_nonzero_example` from
  "valid unlike parameters exist" to "the cubic coefficient is computed and nonzero".

**Scope (honest):** Option B proves the **cubic-coefficient mechanism** — the `exp(−λ·s)`-driven,
`exp`-free-rational structure that makes `D_ij ≠ 0` for unlike pairs, with a concrete nonzero witness.
The faithful inner-core identity `D_ij = R'_ij(0)/6` with the full inside-core Laplace remainder
`R_ij(s) = s⁵[exp(sR)·S_ij − Y_ij]` (packaging that Lean does not yet have; same-core as the mixture
groups' (MML/MZERO) pole/residue Mittag-Leffler representation, no quick bridge) is now the **optional
Group MPOLY** (`proof_notes_yukawa_wh.md`). So **B.9 is closed at the mechanism level**; the exact
`R'_ij(0)/6` packaging is the optional MPOLY upgrade.

---

### Task B.10 — Exact degree: natDegree P_{ij} = 4

**Statement:** The polynomial P_{ij}(r) extracted from R_{ij}(s) via B.8 has `Polynomial.natDegree = 4`, i.e., the degree is exactly 4, not merely ≤ 4.

**Proof structure:**

The theorem combines an upper and lower bound:

```lean
theorem b10_degree_exact
    (R : ℝ → ℝ) (hR : AnalyticAt ℝ R 0) (hE4 : R 0 ≠ 0) :
    let P := Polynomial.C (R 0 / 24) * Polynomial.X ^ 4
           + Polynomial.C (iteratedDeriv 1 R 0 / 6)   * Polynomial.X ^ 3
           + Polynomial.C (iteratedDeriv 2 R 0 / 4)   * Polynomial.X ^ 2
           + Polynomial.C (iteratedDeriv 3 R 0 / 6)   * Polynomial.X
           + Polynomial.C (iteratedDeriv 4 R 0 / 24)
    P.natDegree = 4 :=
  le_antisymm (b10_degree_le hR) (b10_degree_ge hE4)
```

**Upper bound sub-lemma** (`natDegree ≤ 4`):

Immediate from the polynomial construction — every monomial has degree ≤ 4. Closed by `Polynomial.natDegree_add` + `Polynomial.natDegree_C_mul_X_pow`. No analyticity needed for this direction; the bound is baked into the definition of P.

**Lower bound sub-lemma** (`natDegree ≥ 4`):

Equivalent to `leadingCoeff P ≠ 0`, i.e., `R 0 / 24 ≠ 0`, which follows directly from `hE4 : R 0 ≠ 0` and `(24 : ℝ) ≠ 0`. Closed by `Polynomial.natDegree_eq_of_leadingCoeff_ne_zero` + `div_ne_zero hE4 (by norm_num)`.

**Is a separate lower-bound task necessary?**

The lower bound in the abstract theorem requires `hE4 : R 0 ≠ 0` as a hypothesis — it is not proved, merely assumed. Whether this hypothesis holds for the *actual* R_{ij}(s) from the FMSA construction is a separate question:

- For a concrete binary mixture (σ₁=1, σ₂=2, explicit ρ, lam, Q', Q''), one could unfold `q0_entry` fully and verify `R 0 ≠ 0` by `native_decide` or `norm_num`. This is feasible but requires all Taylor recursion unfolded.
- For generic parameters: follows from M.3 (det Q̂₀(0) ≠ 0) + the structure of W_{ij}(0)/ΔQ(0); needs symbolic argument analogous to B.9.

**Verdict:** A separate lower-bound task is not necessary for the FMSA degree theory. The upper bound (`deg ≤ 4`) is the physically essential claim. The exact degree task B.10 is mathematically cleaner but the `hE4` hypothesis can remain as an explicit assumption rather than a derived fact, unless a concrete computational witness is desired.

**Depends on:** B.8 (for the full theorem; upper bound alone is trivial), M.3 (for the generic lower-bound instantiation).

**Status:** ✓ DONE — `B5MixturePoly.lean` (section `ExactDegree`, theorem
`b10_natDegree_eq_four`), no `sorry`. Proves `natDegree = 4` for the abstract polynomial
`a·X⁴+b·X³+c·X²+d·X+e4` given `a ≠ 0`, by chaining `natDegree_add_eq_left_of_natDegree_lt`
down from the leading term — matching the sketch's upper/lower-bound structure, but stated
directly over the coefficients rather than derived via `iteratedDeriv R`/`AnalyticAt`, so
`hE4`/`hR 0 ≠ 0` here is simply `ha : a ≠ 0` taken as a hypothesis, not derived from M.3.

---

## Group C — FMSA_GA_matrix_mix Consistency Checks  *(reduction and verification)*

These tasks verify that the multi-component FMSA_GA_matrix_mix formula is consistent with known results:
reducing to FMSA_pure for N=1, and giving the correct contact value for all pairs.

---

### Task C.1 — N=1: corrected FMSA_GA_matrix_mix inner-core formula = [chsY] Eq. 43 (FMSA_pure)

**Statement:** For N=1 (single species, σ_1 = d, σ_min = d = R_11), applying M.2
(`Ĝ_{00} = g(z)`, `Â_{00} = a(z)`) to the corrected FMSA_GA_matrix_mix inner-core:
```
K · (1 − Ĝ²_{00}) · exp(−z(r−d)) − K · Â²_{00} · exp(+z(r−d)) + Poly(r)
```
reduces to [chsY] Eq. 43 / FMSA_pure:
```
K · (1 − g²) · exp(−z(r−d)) − K · a² · exp(+z(r−d)) + Poly(r)
```
where `g = S/D` and `a = 12ηL/D` with `g + a·exp(−z) = 1` (Task M.9).

**Proof:**  Substitute M.2 (`Ĝ_{00} = g`, `Â_{00} = a`) into the corrected formula.
The substitution is definitional (Ĝ_{00} equals g by M.2); the result matches Eq. 43
term-by-term. Lean: `rw [g_mat_n1_eq_g_scalar]` + `ring`.

**Why it matters:** The master correctness check for FMSA_GA_matrix_mix: for N=1, the multi-component
corrected formula reduces exactly to the known-exact single-component result (FMSA_pure).
Complementary to Task 4.4, which proved [chsY] Eq. 41 (the **un**corrected formula) does
NOT reduce to Eq. 42 for N=1 (the (1+A)² ≠ 1−g² discrepancy, Task 4.3).

**Together: Task 4.3 + C.1 prove the complete story:**
- Uncorrected Eq. 41 → wrong coefficient (1+A)² (proved, Task 4.3)
- Corrected FMSA_GA_matrix_mix formula → right coefficient (1−g²) (proved, C.1)

**Depends on:** M.2 (`g_mat_n1_eq_g_scalar`), Task M.9 (`g_add_a_mul_exp_eq_one`), M.11.

**Status:** ✓ DONE — `LeanCode/YukawaDCF/SingleCompReduction.lean` (complete):
  - `c1_n1_ga_matrix_mix_eq_fmsa_pure`: `(1-g²) - a²c² = 2acg` given `h : g + a*c = 1`;
    one-liner via `coeff_identity` (M.11). File gains `import MatrixIdentity`.
  - `c1_n1_from_mat_identity`: instantiation from `g_mat_n1_eq_scalar` (M.1 N=1);
    `linear_combination` handles `c*(M/D)` vs `(M/D)*c` commutativity mismatch.

---

### Tasks C.2 & C.5 — HS-pole residue conditioning, positive results (added 2026-07-15)

*Source: `fmsa_hs_pole_residue.py` Route C analysis + `_build_pure_refs` bug fix.*

The key finding: for N=1 like pairs, the two-exp formula has an **exp-cancellation** that keeps it
bounded (C.2); and `K·G·exp` is the exact leading Yukawa-pole residue (C.5), so the Route C inner
formula is correct at leading order. The two **failure** counterparts — for N=2 unlike pairs the
cancellation is absent and the base `K·exp(z·R)` diverges (GA.1), with structural root cause
`G_{01}→0` (GA.2) — moved to `proof_notes_failures.md` **Group GA** (records only; renumbered
there to the group-local `GA.1`/`GA.2`, formerly `C.3`/`C.4`).

---

### Task C.2 — N=1 like-pair two-exp formula bounded on (0, R)

**Statement:**
```lean
theorem c1_n1_twoexp_bounded
    {z d r : ℝ} (hz : 0 < z) (hd : 0 < d) (hr₀ : 0 < r) (hrd : r < d)
    {eta : ℝ} (heta : 0 < eta) (heta1 : eta < 1)
    {D : ℝ} (hD : D ≠ 0) (hSleD : |S z d eta| ≤ |D|) :
    |(1 - (S z d eta / D) ^ 2) * Real.exp (z * (d - r))| ≤
        2 * (12 * eta * |L z d| / D ^ 2) * |D + S z d eta| := ...
```
where `S z d eta`, `L z d` are the Baxter auxiliary functions (Group 2).

**Key identity chain (the "exp-cancellation"):**

Step 1 — substitute `G = S/D`:
```
(1 - G²) · exp(z(d-r)) = (1 - S²/D²) · exp(z(d-r))
                        = (D-S)(D+S)/D² · exp(z(d-r))
```

Step 2 — `D - S = 12η·L(z)·exp(-z·d)` (definition of D at the Yukawa pole; see PY Baxter factor):
```
= 12η·L·exp(-z·d)·(D+S)/D² · exp(z(d-r))
= 12η·L·(D+S)/D² · exp(z·d·(-1+1-r/d))
= 12η·L·(D+S)/D² · exp(-z·r)
```

Step 3 — `exp(-z·r) ≤ 1` for r > 0, z > 0:
```
|(1-G²)·exp(z(d-r))| ≤ 12η·|L|·|D+S|/D²
```
This is O(1) for physical parameters (η < 1, D ≠ 0, S and L bounded rational functions).

**Proof strategy:**
```lean
calc |(1 - G²) * Real.exp (z * (d - r))|
    = |D - S| * |D + S| / D² * Real.exp (z * (d - r))   := by ring_nf
    _ = 12 * eta * |L z d| * Real.exp (-z * d) * |D + S| / D² * Real.exp (z * d - z * r)   := by rw [hDS]
    _ = 12 * eta * |L z d| * |D + S| / D² * Real.exp (-z * r)   := by ring_nf
    _ ≤ 12 * eta * |L z d| * |D + S| / D²   := by apply mul_le_of_le_one_right; exact Real.exp_le_one (neg_nonpos.mpr (mul_nonneg hz.le hr₀.le))
```

**Why it matters:** This is the mathematical reason N=1 is well-conditioned while N=2 unlike
pairs diverge. The cancellation `exp(-z·d)·exp(z·d) = 1` comes from `D - S = 12η·L·exp(-z·d)`,
which encodes the PY core-closure boundary condition at r = d. For unlike pairs (i ≠ j), the
analogous quantity `G_{ij} ≈ 0` (no algebraic structure forces `(1-G²)` small), so
`(1-G²)·exp(z·R_{ij}) ≈ exp(z·R_{ij})` grows without bound.

**Depends on:** C.1, Task M.9 (`g + a·exp(-z·d) = 1` → `|G| < 1`), M.11 (`1-g² = 2acg`), M.2.
`hDS : D - S = 12 * eta * L * Real.exp (-z * d)` follows directly from `hD_def` (Task M.9), so no
extra hypothesis is needed.

**Status:** ✓ DONE (2026-07-15), axiom-clean — `c1_n1_twoexp_bounded` in
`LeanCode/YukawaDCF/SingleCompReduction.lean`.  Abstract in `S, L, D, eta, z, d, r`: `calc` chain
`(1−(S/D)²) = (D−S)(D+S)/D²`, `D−S = 12ηL·exp(−zd)` (from `hD_def`), exp-cancellation
`exp(−zd)·exp(z(d−r)) = exp(−zr)`, then `abs` + `Real.exp_le_one`.  Proved bound is actually
`12η|L||D+S|/D²` (half the stated factor-2 form).

---

### Task C.5 — K·G·exp is the exact leading Yukawa-pole residue (added 2026-07-15)

**Statement:** In multicomponent Yukawa MSA (Blum 1975), the leading residue of `c^(1)_{ij}(r)`
at the Yukawa pole `s = z_t` (from the Baxter–Wertheim Laplace inversion) is exactly, for an
unlike pair `i ≠ j` and `r < R_{ij}`:
```
c^(1)_{ij}(r)  ∋  K_t · [Q̂₀(z_t)⁻¹]_{ij} · exp(−z_t·(r − R_{ij}))
```
where `[Q̂₀(z_t)⁻¹]_{ij} = G_{ij}(z_t)` is the (i,j) entry of the inverse Q̂₀ matrix (the GA-matrix G).

**Proof sketch:**
1. Blum 1975 Laplace-space OZ: `ĉ^(1)_{ij}(s)` has poles at `s = z_t` (Yukawa) and at `s = s_k`
   (zeros of `det Q̂₀`, the HS poles).
2. Near `s = z_t` for an unlike pair (i ≠ j): the numerator → `K_t·[adj Q̂₀(z_t)]_{ij}`, so the
   residue `= K_t·[adj Q̂₀(z_t)]_{ij} / det Q̂₀(z_t)` simplifies to `K_t·G_{ij}(z_t)`. (Full
   partial-fraction derivation from Blum's formula needed.)
3. Inverse Laplace of the residue at `s = z_t` → `K_t·G_{ij}·exp(−z_t·r)`.
4. N=1 consistency: for `i = j = 0`, `G₀₀ = (1−g²)·…` reduces to the FMSA_pure formula (C.1).

**Why it matters:** Validates `get_c1_inner` in `fmsa_hs_pole_residue.py` at leading order and
explains the numerically observed `ĉ₁₂ ≈ 0` for Route C at σ-ratio = 2 as **expected, not a bug**:
`G₀₁ ≈ 0` (GA.2) kills the inner `K·G·exp` contribution by construction, so the remaining 2YK error
(`ĉ₁₂ = +0.15` vs GCMC `−22.07`) is entirely in the **outer-region** `K₀₁` values (same root cause
as `ĉ₂₂ = +8174` for like pair (2,2)) — fixing it needs better `K₀₁` (poly-term / GCMC fit / OZ
self-consistency), not a different inner formula. If C.5 were *disproved*, an additional inner-core
term beyond `K·G·exp` would be required.

**Depends on:** M.10 (Q̂₀ structure), M.3/M.4 (G/A matrices); requires Blum 1975's explicit
Laplace-space formula for multicomponent Yukawa MSA (or an independent derivation).
**Effort:** medium-high.

**Status:** ◑ conditional core DONE (2026-07-15), axiom-clean —
`LeanCode/YukawaDCF/YukawaPoleResidue.lean`:
- `g_entry_eq_adj_div_det` — the matrix-algebra identity `[Q̂₀⁻¹]_{ij} = adj(Q̂₀)_{ij}/det Q̂₀`
  (`Matrix.inv_def`), i.e. the `= K_t·G_{ij}(z_t)` simplification.
- `c5_residue_eq_K_mul_Ginv` — the residue assembly: given the Blum simple-pole shape near `z_t`
  (`N/D`, simple zero, `N(z_t)/D'(z_t) = K_t·[Q̂₀(z_t)⁻¹]_{ij}` as the explicit hypothesis `hblum`),
  the residue-defining limit `(s−z_t)·(N/D) → K_t·(adj/det)`.  Reuses
  `FMSA.HardSphere.residue_of_simple_pole` (`BaxterResidue.lean`).

**Deferred → concrete C.5 (source located, 2026-07-15).** The Laplace-space form needed to discharge
`hblum` is in the **[LN] lecture notes** (`pdf/lecture_notes_OZ_Yukawa_poly.pdf`, Tang & Lu 1995),
explicitly and in `s = −ik`:
- **Eq. (10)** — the complex Baxter matrix `{Q̂₀(s)}_{ij} = δ_{ij} − (ρ_iρ_j)^{1/2}·e^{−sλ_{ij}}·
  [φ₁(R_i)Q'_{ij} + φ₂(R_i)Q''_j]` (extends the codebase's real `Q0_mat` to complex `s`);
- **Eq. (14)** — `{[Q̂₀(s)]⁻¹}_{ij} = δ_{ij} + 2π(ρ_iρ_j)^{1/2}·W_{ij}(s)/(Δ·det(s))·e^{−sλ_{ij}}`,
  the GA-matrix `G` with the `adj/det(s)` structure (⇒ `g_entry_eq_adj_div_det`), and `det(s)` Eq. (16);
- **§6.4.1** (spectral amplitude `b_{ij}(s)`) + **§8.1** (Laplace-space RDF) — the Yukawa-pole form of
  `ĥ^(1)/ĉ^(1)_{ij}(s)` whose residue at `s = z_t` gives `K_t·G_{ij}(z_t)`, discharging `hblum`.

**Concrete single-tail residue — DONE (2026-07-15), and a correction.** Reading the [LN] §6.4
derivation to the end (Eq. 73) shows the spectral amplitude `b_{ij}(s)` — the residue-carrying
object in `Ĥ₁ = [Q̂₀ᵀ]⁻¹B₁[Q̂₀]⁻¹` (Eq. 68) — is, for a **single tail** (common `z`),
```
b_{ij}(s) = [(I+A)·K·(I+A)ᵀ]_{ij}/(s+z) = [Q̂₀(z)⁻¹·K·Q̂₀(z)⁻ᵀ]_{ij}/(s+z)   (since I+A = Q̂₀⁻¹, Eq. 70).
```
So the exact Yukawa-pole residue is the **doubly-propagated** `[Q̂₀⁻¹·K·Q̂₀⁻ᵀ]_{ij}` — `K` sandwiched
by **two** inverse-Baxter factors — **not** the linear `K·G_{ij}` of the numerical shorthand. Proved
axiom-clean in `LeanCode/YukawaDCF/SpectralAmplitude.lean`:
- `spectralAmp_residue` — `Res_{s=−z} b_{ij}(s) = [Q̂₀⁻¹·K·Q̂₀⁻ᵀ]_{ij}` (elementary rational-function
  residue: `(s+z)·[N/(s+z)] → N`);
- `spectralAmp_residue_n1` — at `N=1` the residue is `K·G²`, making the "`K·G` vs exact" gap explicit.

⇒ **Correction (→ `to_python.md`):** Route-C's `get_c1_inner` `K·G·exp` is a *leading-order
approximation* of the exact `Q̂₀⁻¹·K·Q̂₀⁻ᵀ`, not the exact leading residue.

**Promoted to Group Y1 (2026-07-15).** The full concrete-C.5 derivation — the *derivation* of `b_{ij}`
from the first-order OZ equation via the Wiener–Hopf split (§6.1–§6.4) — was a Group-BAXTER-scale body
of work, so it was promoted to its own **Group Y1** (records: [proof_notes_yukawa_wh.md]). Status of
the pieces that were "still deferred" here:
- **Complex `Q̂₀(s:ℂ)` (Eq. 10)** — ✓ DONE as **Y1.1** (`q0_entry_c`, `Q0_mat_c`,
  `inv_apply_eq_adj_div_det`, `Q0Complex.lean`), so `A_{ij}(z)=[Q̂₀(z)⁻¹]_{ij}−δ` is now a *derived*
  matrix, not a parameter.
- **Spectral amplitude `b_{ij}(s)` (Eq. 73)** — ✓ single-tail exact residue + multi-tail collapse
  DONE as **Y1.5** (`spectralAmp_residue`/`_n1`, `bMulti`, `bMulti_single_residue`); general
  distinct-`z_{αβ}` still open.
- **Assembly `Ĥ₁=[Q̂₀ᵀ]⁻¹B₁[Q̂₀]⁻¹` (Eq. 68)** — ✓ DONE as **Y1.6** (`Hhat1`, `Hhat1_spec`,
  `Hhat1_residue`, `YukawaWienerHopf.lean`).
- **The Wiener–Hopf derivation of `b_{ij}`** — staged as **Y1.3**, and **re-routed off the Hilbert
  transform** ([LN] §6.3's literal P.V./Sokhotski–Plemelj presentation; Mathlib lacks that machinery)
  to the codebase's algebraic-split + support + residue method. **Y1.3a** (the WH support lemmas,
  `WHSupports.lean`) is ✓ DONE; the remaining crux is **Y1.3b** (FT injectivity / support-orthogonality).

So the old "C.5 (concrete)" tracking label is retired → **see Group Y1** for live status.

---

### Tasks GA.1, GA.2 (formerly C.3, C.4) — moved to Group GA (failure analysis)

The unlike-pair **divergence** results — GA.1 (`K·exp(z·R)` unbounded; additive HS-pole sum cannot
cancel it) and GA.2 (off-diagonal `G_{01}→0` as the structural root cause) — are failure analyses of
FMSA_GA_matrix_mix's own inner formula, so their full records now live in `proof_notes_failures.md`
**Group GA — FMSA_GA_matrix_mix Inner-Core Conditioning Failure**. They are renumbered to the
group-local `GA.1`/`GA.2` (formerly `C.3`/`C.4`); the record location moved too. The positive
counterparts C.2 (above) and C.5 (above) stay here in Group C.

---

## Group 5 — Matching at Contact r = R_ij

### Task 5.1 — Inner/outer matching at r = R_ij for soft-core (2YK) only

**Physical context:**

- **HSY (hard-sphere + Yukawa):** The DCF is physically *discontinuous* at `r = R_ij` because
  the hard-core potential imposes `g(r) = 0` for `r < σ`, creating a step in `c(r)` at contact.
  `FMSA_pure` (HSY version) reproduces this discontinuity correctly — it is not a bug.
- **2YK (two-Yukawa soft core):** No hard core, so `c^(1)_ij(r)` can be continuous at `r = R_ij`.
  The matching condition `c^(1)_ij(R_ij⁻) = K_ij / R_ij` holds only at **first order** (FMSA);
  higher-order perturbative corrections do not maintain this continuity.

**Statement (2YK, first order only):**
```
lim_{r→R_ij⁻} c^(1)_ij(r)  =  K_ij / R_ij        [first-order MSA closure, [chsY] Eq. 8/34]
```
This follows from all I₁/I₂ integrals vanishing at ℓ=0 (Task 1.3) so Term I alone gives
the value at r = R_ij, and by [chsY] Eq. 34 this equals K_ij / R_ij.

**Lean value:** Low — the discontinuous case (HSY) is physically correct and expected;
the soft-core matching is a first-order identity that holds trivially if Tasks 1.3 and 4.4 pass.

**Status:** ✓ DONE — `LeanCode/YukawaDCF/ContactMatching.lean` (complete):
  - `terms_II_III_vanish_at_contact`: I₁(0,α,z)=0 ∧ I₂(0,α,z)=0 via `I1_at_zero`/`I2_at_zero`
  - `inner_core_eij_at_contact`: `eij A z R R = Σ_k A_k` via `eij_at_contact`
  - `outer_core_at_contact`: `K·exp(−z·0)/R = K/R` via `sub_self` + `Real.exp_zero`
  - `soft_core_contact_limit`: combines all three in one `⟨I1_at_zero, I2_at_zero, eij_at_contact⟩`
  Import added to `LeanCode.lean`: `import LeanCode.FreeEnergy.ContactMatching`.
  Note: full inner/outer continuity requires the MSA closure condition relating K to A_k (not proved).

---

~~## Group D — Pure-Limit Equivalence: FMSA_GA_matrix_mix = FMSA_pure for All Densities~~

> **DELETED** — Tasks D.1–D.4 removed. These were written for the old scalar Path B approach
> and are no longer valid after the FMSA_GA_matrix_mix redesign (full G/A matrix, mediated terms).
> Key reasons:
> - D.3's Lean statement was trivially `rfl` (no mathematical content with the new formula).
> - D.4 referenced `c_pathb` (old name) and assumed the OLD scalar implementation.
> - The pure-limit N=1 reduction is already proved by **Task C.1** (✓ DONE).
> - `check_pure_limit.py` now fails with the new matrix implementation (implementation bug pending fix).
> Once the implementation bug is fixed, a new Group D may be written if needed, routing through
> M.1/M.2 (G/A matrix N=1 reduction) and C.1 rather than the old scalar argument.


*(tasks D.1–D.4 deleted — see note above)*

---

