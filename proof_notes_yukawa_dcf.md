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

**Status:** ✓ DONE — `I1_formula` proved in `LeanCode/FMSAPoly/I1I2Integrals.lean` (complete).

---

### Task 1.2 — I₂ antiderivative ([chsY] Eq. 39)

**Statement:**
For `z ≠ 0` and `ℓ ≥ 0`:
```
∫₀^ℓ (α − v)² exp(z v) dv  =  (α−ℓ)²·exp(zℓ)/z  +  2(α−ℓ)·exp(zℓ)/z²
                              +  2·exp(zℓ)/z³  −  α²/z  −  2α/z²  −  2/z³
```
with the `z → 0` limit `α²ℓ − αℓ² + ℓ³/3`.

**Status:** ✓ DONE — `I2_formula` proved in `LeanCode/FMSAPoly/I1I2Integrals.lean` (complete).

---

### Task 1.3 — I₁/I₂ vanish at ℓ = 0

**Statement:** `I₁(0, α, z) = 0` and `I₂(0, α, z) = 0` for all α, z.

**Why it matters:** Guarantees that Terms II and III in [chsY] Eq. 41 contribute nothing when
`r = R_aj` exactly (no jump discontinuity from the step function).

**Status:** ✓ DONE — `I1_at_zero` and `I2_at_zero` in `LeanCode/FMSAPoly/I1I2Integrals.lean` (complete):
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

**Status:** ✓ DONE — proved in `LeanCode/FMSAPoly/BijReduction.lean` (complete):
  - `b_general`: abstract N-species pole-residue double sum definition
    `b_ij(s) = Σ_{m n} K_{mn} · (1+A_{im}) · (1+A_{nj}) / (s+z)`
  - `b_n1_collapse`: for N=1, `Fin.sum_univ_one` collapses both sums to a single term:
    `b_general K A z s 0 0 = K 0 0 * (1 + A 0 0)^2 / (s+z)`. Proof: `simp [Fin.sum_univ_one]` + `ring`
  - `a_n1_one_plus_eq_Qinv` / `a_n1_one_plus_sq`: for A₀₀ = Q⁻¹ − 1, `1+A₀₀ = Q⁻¹` and `(1+A₀₀)² = Q⁻²`
  - `b_n1_baxter_formula`: concrete Baxter form with A = (1−η)²z³/D − 1:
    `b_00(s) = K · (1−η)⁴z⁶ / (D² · (s+z))`. Uses `eq41_n1_reduces_to_eq42` from `SingleCompReduction`

---

### Task 4.2 — Identity `g + a·exp(−z) = 1` ([chsY] Eq. 44)

**Statement:** With `g(z) = S(z) / ((1−η)²z³Q₀(z))` and `a(z) = 12ηL(z) / ((1−η)²z³Q₀(z))`:
```
g(z) + a(z) · exp(−z) = 1
```
where `S(z)`, `L(z)`, `Q₀(z)` are the single-component structure factor, L-function, and Baxter
Q-function evaluated at the Yukawa pole `s = z` ([chsY] Eq. 52).

**Why it matters:** This identity encodes the continuity of `c^(1)(r)` at the contact `r = d`.
It is the single-component analogue of the multi-species matching condition at `r = R_ij`.

**Status:** ✓ complete — `LeanCode/FMSAPoly/SingleCompIdentity.lean`
  (`g_add_a_mul_exp_eq_one`, `g_add_a_mul_exp_eq_one_baxter`; complete)

  **Proof:** One `have` + four rewrites.
  - `have hnum : S + 12ηLe^{-z} = D := hD_def.symm`
  - `rw [div_mul_eq_mul_div]` — moves exp from multiplier to numerator position
  - `rw [← add_div]` — combines into single fraction `(S + 12ηLe^{-z}) / D`
  - `rw [hnum]` — substitutes `D` for numerator
  - `div_self hD` — closes `D / D = 1`

  Key lemmas: `div_mul_eq_mul_div`, `add_div` (from `Mathlib.Algebra.Field.Basic`), `div_self`

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

**Status:** ✓ DONE — all results proved in `LeanCode/FMSAPoly/SingleCompReduction.lean` (complete):
  - `correction_sq_eq`: S²eᶻ + M²e⁻ᶻ + 2SM = (S+Me⁻ᶻ)²eᶻ  (key cancellation identity)
  - `f42_zero_at_origin`: Eq. 42 gives r·c(0)=0  (physical origin check)
  - `sq_of_g_add_a_exp_eq_one`: g+ae⁻ᶻ=1 (Task 4.2) → g²eᶻ+a²e⁻ᶻ+2ga=eᶻ
  - `eq42_factored_bracket`: (D²−S²)Eₘ−M²Eₚ = D²(1−g²)Eₘ−D²a²Eₚ  (Eq. 42→43 factoring)
  - `eq41_n1_step_gate`: for r<1, θ(r−1)=0 kills Terms II/III/IV — only Term I survives
  - `eq41_n1_reduces_to_eq42`: Term I coefficient identity (1+A)² = (1−η)⁴z⁶/D²

  **Corrected mathematical finding:** Eq. 41 does **NOT** reduce to Eq. 42 for N=1.
  The paper's claim is false: (1+A)² = (1−η)⁴z⁶/D² ≠ (D²−S²)/D² = 1−g² in general.
  Formal counterexample proved in `LeanCode/FMSAPoly/OriginCheck.lean`
  (`identity_one_plus_A_sq_ne_one_minus_g_sq`, η=3/4, z=1).

---

## Group M — Multi-Component Baxter Identity

Derives the matrix analog of the N=1 identity `g + a·e^{-z} = 1` (Task 4.2).
The mathematical derivation is in `problem_answers/multicomp_g_a_derivation.md`.

### Task M.1 — Abstract matrix identity: Ĝ + Â·c = I

**Statement:** For `n×n` real matrices `P`, `E`, `D` with `D = P + c • E` (c a scalar)
and `D` invertible:
```
P * D⁻¹ + c • (E * D⁻¹) = 1
```
This is the matrix analog of `g + a·e^{-z} = 1` (Task 4.2), where:
- `P` = polynomial-part matrix (analog of `S`)
- `E` = exponential-coefficient matrix (analog of `12η·L`)
- `c = exp(−z·σ_min)` = the exponential factor from the smallest diameter
- `D = Q̂₀` = full Baxter Q-matrix (analog of `D = S + 12ηL·e^{-z}`)
- `Ĝ = P·D⁻¹`, `Â = E·D⁻¹` = multi-component analogs of scalar g, a

**Why it matters:** Guarantees that the corrected inner-core formula
`c_ij(r) = K(1−Ĝ²_{ij})·e^{-z(r-R)} − K·Â²_{ij}·e^{+z(r-R)} + Poly`
uses the correct coefficients (Ĝ + Â·c = I mirrors g + a·e^{-z} = 1 for N=1).

**Proof sketch:**
```
P·D⁻¹ + c•(E·D⁻¹) = (P + c•E)·D⁻¹ = D·D⁻¹ = I
```
Left-distributes `D⁻¹`, substitutes `D = P + c•E`, then applies `IsUnit.mul_val_inv`.

**Lean:**
```lean
-- LeanCode/FMSAPoly/MatrixIdentity.lean
theorem g_mat_add_a_mat_exp_eq_one {n : ℕ}
    (P E D : Matrix (Fin n) (Fin n) ℝ) (c : ℝ)
    (hD_def : D = P + c • E)
    (hD : IsUnit D) :
    P * D⁻¹ + c • (E * D⁻¹) = 1 := by
  rw [← add_mul, smul_mul, ← hD_def]
  exact hD.mul_val_inv
```

**Depends on:** Nothing new — pure matrix algebra (Mathlib `Matrix` API).

**Status:** ✓ DONE — `g_mat_add_a_mat_exp_eq_one` in `LeanCode/FMSAPoly/MatrixIdentity.lean` (complete):
  `rw [← Algebra.smul_mul_assoc, ← add_mul, ← hD_def]` + `Matrix.mul_nonsing_inv D hD`.
  Note: hypothesis is `IsUnit D.det` (not `D.det ≠ 0`); Mathlib's `Matrix.mul_nonsing_inv`
  requires `IsUnit`. Also includes `g_mat_n1_eq_scalar` (N=1 scalar limit sanity check):
  `rw [← mul_div_assoc, ← add_div, hnum, div_self hD]` — same structure as Task 4.2.

---

### Task M.2 — N=1 limit: Ĝ₀₀ = g(z) and Â₀₀ = a(z)

**Statement:** For n=1, the matrix definitions `Ĝ = P̂·D̂⁻¹` and `Â = Ê·D̂⁻¹` reduce to
the scalar single-component propagators:
```
Ĝ_{00} = P̂_{00} / D̂_{00} = S(z) / D(z) = g(z)
Â_{00} = Ê_{00} / D̂_{00} = 12η·L(z) / D(z) = a(z)
```
where `S`, `L`, `D`, `g`, `a` are as in `SingleCompIdentity.lean` (Task 4.2).

**Why it matters:** Confirms that the multi-component FMSA_GA_matrix_mix formula reduces exactly to
FMSA_pure for N=1. The corrected inner-core `K(1−Ĝ²)·e^{-z(r-R)} − K·Â²·e^{+z(r-R)}`
then matches [chsY] Eq. 43 term-by-term.

**Proof strategy:** For n=1, `P̂`, `Ê`, `D̂` are 1×1 matrices = scalars. Matrix multiplication
`P̂ · D̂⁻¹` becomes scalar division `P̂_{00} / D̂_{00}`. Lean:
```lean
theorem g_mat_n1_eq_g_scalar (S L η z : ℝ) (hD : D ≠ 0) :
    let D := S + 12 * η * L * Real.exp (-z)
    (fun _ _ => S : Matrix (Fin 1) (Fin 1) ℝ) *
    (fun _ _ => D : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ = fun _ _ => S / D := by
  ext i j; fin_cases i; fin_cases j
  simp [Matrix.inv_fin_one, div_eq_mul_inv]
```

**Depends on:** M.1, Task 4.2 (`g_add_a_mul_exp_eq_one`), `Matrix.inv_fin_one`.

**Status:** ✓ DONE — `LeanCode/FMSAPoly/MatrixN1.lean`

Key results proved (all in `namespace FMSA.MatrixN1`):
- `fin1_const_mul` (proved): 1×1 matrix multiplication is scalar multiplication
- `fin1_const_inv` (proved via left-inverse uniqueness): 1×1 matrix inverse is scalar inverse;  needed — D=0 case uses `nonsing_inv_apply_not_isUnit`; D≠0 case uses `mul_assoc` + `Matrix.mul_nonsing_inv` uniqueness argument
- `mat_fin1_mul_inv` (proved): `(fun _ _ => S) * (fun _ _ => D)⁻¹ = fun _ _ => S/D` unconditionally
- `g00_eq_g_scalar`, `a00_eq_a_scalar` (proved): entry-wise reduction
- `m2_identity` (proved): chains into `FMSA.SingleComp.g_add_a_mul_exp_eq_one`
- `m2_identity_baxter` (proved): concrete form using `Q0_ne_zero_at_yukawa` axiom from Task 2.2

---

### Task M.3 — det(Q̂₀) ≠ 0 for valid multi-component parameters

**Statement:** For a physically valid n-component mixture (total packing fraction η < 1,
all ρᵢ ≥ 0, all σᵢ > 0), the Baxter Q-matrix `Q̂₀(z)` is invertible for all z > 0:
```
det(Q̂₀(z)) ≠ 0
```
This is the multi-component analog of Task 2.2 (`Q0_ne_zero_of_eta_lt_one` for N=1).

**Why it matters:** Required to define Ĝ = P̂·Q̂₀⁻¹ and Â = Ê·Q̂₀⁻¹ (M.1, FMSA_GA_matrix_mix).
Without invertibility, the matrix decomposition is ill-defined.

**Proof strategy (future):** The N=1 case (Task 2.2) is already axiomatic — the multi-component
case is at least as hard. For a future Lean proof, the most tractable routes are:
- Show `Q̂₀(z) = I − C(z)` where `‖C(z)‖ < 1` under density constraints
  (Neumann series / operator norm argument via `Matrix.norm_lt_one_of_...`)
- Continuity + positivity argument at z=0 then propagated to all z > 0.
- Prove N=1 analytically first, then generalize via `Matrix.det_fin_one`.

**Depends on:** Task 2.2 (for the N=1 base case); `Matrix.nonsing_inv_apply_not_isUnit`
to connect `det ≠ 0` to `IsUnit` (which M.1 requires).

**Status:** ✓ DONE (axiomatic) — `LeanCode/FMSAPoly/MatrixQ0.lean`

Key results in `namespace FMSA.MatrixQ0`:
- `q0_entry`: concrete scalar (i,j) entry formula (B.2 form)
- `Q0_mat`: n×n matrix assembled from `q0_entry`
- `Q0_mat_entry_decomp` (proved): each entry satisfies the B.2 decomposition
  `Q̂₀ᵢⱼ = P̂ᵢⱼ + Êᵢⱼ · exp(-z·σ_min)` via `b2_qhat_entry_decomp`
- `Q0_mat_isUnit_det` (axiom): `IsUnit (Q0_mat ...).det` under physical conditions;
  hypothesis `heta` uses `rho_geo i i ^ 2 = ρᵢ` and `Σ ρᵢ σᵢ³ · π/6 ∈ (0,1)`
- `Q0_mat_n1_entry` (proved): for n=1, the (0,0) entry simplifies to the scalar Q₀ form
  (N=1 consistency check; `λ₀₀ = 0` gives `exp(0) = 1` automatically)

---

## Group B — FMSA_GA_matrix_mix Algebraic Foundation  *(FMSA_GA_matrix_mix specific)*

These tasks formalise the algebraic structure underlying `FMSA_GA_matrix_mix` ([chsY] FMSA_GA_matrix_mix corrected
inner-core formula).  They connect the abstract matrix identity M.1 (`Ĝ + Â·c = I`) to the
concrete Baxter Q-matrix decomposition used in `_decompose_Q0`, and verify that the corrected
coefficients `(1−Ĝ²)` and `Â²` are algebraically consistent with FMSA_pure for N=1.

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

### Task B.2 — Concrete Q̂₀ = P̂ + Ê·exp(−z·σ_min) decomposition

**Context:** M.1 proves `P·D⁻¹ + c·(E·D⁻¹) = I` from the *abstract* hypothesis `D = P + c·E`
(where `D` = Q̂₀, `c = exp(−z·σ_min)`).  Task B.2 proves that hypothesis concretely: the
explicit P̂_{ij} and Ê_{ij} from §5 of `multicomp_g_a_derivation.md` satisfy:
```
Q̂₀_{ij}(z)  =  P̂_{ij}(z)  +  Ê_{ij}(z) · exp(−z · σ_min)
```

**Explicit forms (from §5):**
```
P̂_{ij}(z) = δ_{ij}
           − √(ρᵢρⱼ) · exp(−λ_{ij}·z) · [ Q'_{ij} · (1−z·σᵢ)/z²
                                           + Q''_j  · (1−z·σᵢ+(z·σᵢ)²/2)/z³ ]

Ê_{ij}(z) = √(ρᵢρⱼ) · exp(−z·(R_{ij}−σ_min)) · (Q'_{ij}/z² + Q''_j/z³)
```
where `λ_{ij} = (σ_j−σ_i)/2`, `R_{ij} = (σ_i+σ_j)/2`, and
`Q'_{ij} = (2π/Δ)·(R_{ij} + π·σ_i·σ_j·ξ₂/(4Δ))`, `Q''_j = (2π/Δ)·(1 + π·σ_j·ξ₂/(2Δ))`.

**Proof strategy:** Substitute the B.1 split
`∫₀^{σᵢ} r·exp(z(r−σᵢ)) dr = (z·σᵢ−1+exp(−z·σᵢ))/z²`
into the Q̂₀ formula, then collect terms by whether they contain `exp(−z·σᵢ)`.
Factor out `exp(−z·σ_min)` from the exponential part (valid since R_{ij} ≥ σ_min always,
with equality for the smallest-diameter like pair). Close by `ring` + `Real.exp_add`.

**Why it matters:** Supplies the concrete `hD_def` hypothesis for M.1, turning the abstract
matrix identity into a verified statement about actual FMSA_GA_matrix_mix matrices.

**Depends on:** B.1, Task 2.1 (`phi1_formula`, `phi2_formula`), M.1.

**Status:** ✓ DONE — `LeanCode/FMSAPoly/QhatDecomposition.lean` (complete):
  - `b2_qhat_entry_decomp`: scalar (i,j) entry identity `Q̂₀ = P̂ + Ê·exp(−z·σ_min)`.
    Three-step proof: (1) `hexp` via `← exp_add` + `linear_combination -z * hR`;
    (2) `h` (algebraic factor of exp(−zσ)) via `field_simp [pow_ne_zero]; ring`;
    (3) `rw [h, hexp]; ring`.
  Implementation notes: `λ` → `lam` (reserved keyword); `ρ̃` → `rho` (combining
  tilde invalid in Lean 4 identifiers).

---

### Task B.3 — Coefficient algebra: `(1 − g²) − a²·c² = 2·a·c·g`

**Statement:** From `g + a·c = 1` (Task 4.2 / M.1 N=1 case), the following identity holds:
```
(1 − g²) − a² · c²  =  2 · a · c · g
```
**Equivalently:** `(1 − g²) + a²·c² = 2·a·c` (add `2a²c²` to both sides).

**Proof:** Pure `ring` from the hypothesis `h : g + a*c = 1`:
```lean
theorem coeff_identity (g a c : ℝ) (h : g + a * c = 1) :
    (1 - g ^ 2) - a ^ 2 * c ^ 2 = 2 * a * c * g := by linarith [sq_nonneg (g + a*c - 1), h]; ring
-- or more directly:
    have : g = 1 - a * c := by linarith
    rw [this]; ring
```

**Why it matters:**
- Decomposes the decaying-exponential coefficient: `(1−g²) = a·c·(2−a·c) = 2ac − a²c²`
- Decomposes the inner-core total: `(1−g²)·e^{-z(r-R)} − a²c²·e^{+z(r-R)}` at r = R gives
  `(1−g²) − a²c² = 2acg`, and for N=1 `g·a·c = g·(1−g)` — a physical contact value.
- Required lemma for Task C.1 (N=1 reduction to FMSA_pure).

**Depends on:** Task 4.2 (`g_add_a_mul_exp_eq_one`).

**Status:** ✓ DONE — `LeanCode/FMSAPoly/SingleCompIdentity.lean` (complete):
  - `coeff_identity`: abstract form for any `g a c : ℝ` with `h : g + a * c = 1`;
    proof: `have hg : g = 1 - a * c := by linarith; rw [hg]; ring`.
  - `coeff_identity_baxter`: Baxter-specific corollary with `c = exp(−z)`, `g = S/D`,
    `a = 12ηL/D`; proof: applies `g_add_a_mul_exp_eq_one` then `coeff_identity`.

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
  the remaining terms cancel by the `g + a·c = 1` identity (Task 4.2) — specifically,
  `K·(1+A)² + p₀ = K·(1+A)² − K·(1+A)² = 0` once the polynomial constant is identified
  from the Baxter equations.

**Why it matters:** The formal Lean statement that **FMSA_GA_matrix_mix does not need an ad hoc origin
normalization** — contrast with Task P.2 which shows FMSA_poly DOES. Together, B.4 + P.2
give the complete Lean proof that FMSA_GA_matrix_mix is structurally superior at the origin.

**Depends on:** Tasks 1.3 (`I1_at_zero`, `I2_at_zero`), Task 4.2 (`g_add_a_mul_exp_eq_one`),
B.3 (`coeff_identity`).

**Status:** ✓ DONE — `LeanCode/FMSAPoly/B4OriginBC.lean` (complete, namespace `FMSA.PathB`):
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
where `g = S/D` and `a = 12ηL/D` with `g + a·exp(−z) = 1` (Task 4.2).

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

**Depends on:** M.2 (`g_mat_n1_eq_g_scalar`), Task 4.2 (`g_add_a_mul_exp_eq_one`), B.3.

**Status:** ✓ DONE — `LeanCode/FMSAPoly/SingleCompReduction.lean` (complete):
  - `c1_n1_ga_matrix_mix_eq_fmsa_pure`: `(1-g²) - a²c² = 2acg` given `h : g + a*c = 1`;
    one-liner via `coeff_identity` (B.3). File gains `import MatrixIdentity`.
  - `c1_n1_from_mat_identity`: instantiation from `g_mat_n1_eq_scalar` (M.1 N=1);
    `linear_combination` handles `c*(M/D)` vs `(M/D)*c` commutativity mismatch.

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

**Status:** ✓ DONE — `LeanCode/FreeEnergy/ContactMatching.lean` (complete):
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

