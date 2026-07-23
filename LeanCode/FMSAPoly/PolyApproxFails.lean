/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib

/-!
# Task P.3 — Polynomial approximation failure for large z

The inner-core DCF term `E_ij(r) = Σ_k A_k · exp(-z_k·(R-r))` contains exponentials that,
for large inverse ranges `z_k`, cannot be well approximated by any low-degree polynomial on
`[0, R]`.

The target function `f(r) = exp(z·(R-r))` satisfies:
- `f(0) = exp(z·R)` — exponentially large (e.g., exp(14) ≈ 1.2 × 10^6 for z = 14, R = 1)
- `f(R) = 1`

For any polynomial `p` with `p(0) ≤ exp(z·R)/2` — a condition satisfied in FMSA_poly by
the origin normalisation `P_ij(0) = -E_ij(0)` (Task P.2) when amplitudes are non-negative —
the L∞ approximation error on `[0, R]` is at least `exp(z·R)/2`.

**Why it matters:** For `z2 ≈ 14` (repulsive 2YK second Yukawa), the lower bound on the
approximation error is `exp(14)/2 ≈ 600 000`, explaining the numerical spike observed in
`c(r)` within `~1/z2 ≈ 0.07sigma` of contact.

## Note on the todo hypothesis

The todo statement used `exp(z·R) - p(0) ≥ 0` (i.e., `p(0) ≤ exp(z·R)`) as the hypothesis.
This is insufficient: a polynomial with `p(0) = exp(z·R)/2 + ε` has error `< exp(z·R)/2` at
r = 0, and recovering the bound at an interior point requires Chebyshev degree constraints not
available in Mathlib. The corrected hypothesis `p(0) ≤ exp(z·R)/2` makes r = 0 an explicit
witness, matching the physically relevant FMSA_poly regime where p(0) ≈ -E_ij(0) ≈ 0.

## Main results

- `poly_approx_fails` : `p(0) ≤ exp(z·R)/2` implies ∃ r ∈ [0,R] with error ≥ exp(z·R)/2
- `poly_approx_fails_origin` : FMSA_poly case `p(0) ≤ 0` gives error ≥ exp(z·R) at r = 0
- `poly_approx_fails_two_endpoints` : `p(0) ≤ p(R)` (wrong direction) gives error ≥ (exp(z·R)-1)/2
  at whichever of r = 0 or r = R is worse; complementary to `poly_approx_fails` (Task P.C2)
-/

set_option linter.style.longLine false
set_option linter.style.whitespace false

namespace FMSA.PolyApproxFails

/-- **Polynomial approximation lower bound (Task P.3):**
For any polynomial `p` with `p(0) ≤ exp(z·R)/2`, the L∞ error on `[0, R]` for the target
`f(r) = exp(z·(R-r))` is at least `exp(z·R)/2`.

Proof: the witness is `r = 0`, where `f(0) = exp(z·R)` and
`|f(0) - p(0)| = exp(z·R) - p(0) ≥ exp(z·R) - exp(z·R)/2 = exp(z·R)/2`. -/
theorem poly_approx_fails (z R : ℝ) (hR : 0 < R) (_hz : 0 < z) (p : Polynomial ℝ)
    (h : p.eval 0 <= Real.exp (z * R) / 2) :
    ∃ r ∈ Set.Icc 0 R, |Real.exp (z * (R - r)) - p.eval r| >= Real.exp (z * R) / 2 := by
  refine ⟨0, Set.mem_Icc.mpr ⟨le_refl 0, hR.le⟩, ?_⟩
  simp only [sub_zero]
  have hpos : (0 : ℝ) < Real.exp (z * R) := Real.exp_pos _
  rw [abs_of_nonneg (by linarith)]
  linarith

/-- **FMSA_poly case (Task P.3):**
In FMSA_poly, the origin normalisation (Task P.2) forces `P_ij(0) = -E_ij(0)`.
When amplitudes `A_k ≥ 0` (attractive Yukawa), `E_ij(0) ≥ 0` so `p(0) ≤ 0`.
With this stronger hypothesis the error at `r = 0` is at least the full `exp(z·R)`. -/
theorem poly_approx_fails_origin (z R : ℝ) (hR : 0 < R) (_hz : 0 < z) (p : Polynomial ℝ)
    (h : p.eval 0 <= 0) :
    ∃ r ∈ Set.Icc 0 R, |Real.exp (z * (R - r)) - p.eval r| >= Real.exp (z * R) := by
  refine ⟨0, Set.mem_Icc.mpr ⟨le_refl 0, hR.le⟩, ?_⟩
  simp only [sub_zero]
  have hpos : (0 : ℝ) < Real.exp (z * R) := Real.exp_pos _
  rw [abs_of_nonneg (by linarith)]
  linarith

/-- **Tighter two-endpoint bound (Task P.C2):**
For any polynomial `p` with `p(0) ≤ p(R)` (non-decreasing, i.e. going in the OPPOSITE
direction to the strictly decreasing target `f(r) = exp(z·(R-r))`), at least one of the
endpoints `r = 0` or `r = R` carries error ≥ `(exp(z·R) - 1)/2`.

**Proof by case split on whether `p(0) ≤ (exp(zR)+1)/2`:**
- Case 1: `p(0) ≤ (exp(zR)+1)/2 < exp(zR)` → error at r = 0 ≥ (exp(zR)-1)/2.
- Case 2: `p(0) > (exp(zR)+1)/2` and `p(R) ≥ p(0)` → `p(R) > 1` → error at r = R ≥ (exp(zR)-1)/2.

**Complements `poly_approx_fails`:** that theorem covers `p(0) ≤ exp(zR)/2`; this one covers the
"wrong-direction" regime `p(0) ≤ p(R)`. Together they bound all polynomials except those with
`p(0) ∈ (exp(zR)/2, exp(zR)]` AND `p(0) > p(R)` (the Chebyshev gap, not yet formalised). -/
theorem poly_approx_fails_two_endpoints (z R : ℝ) (hR : 0 < R) (hz : 0 < z) (p : Polynomial ℝ)
    (hmono : p.eval 0 <= p.eval R) :
    ∃ r ∈ Set.Icc 0 R, |Real.exp (z * (R - r)) - p.eval r| >= (Real.exp (z * R) - 1) / 2 := by
  -- exp(z*R) > 1 since z*R > 0
  have hexp : 1 < Real.exp (z * R) := by
    have := Real.add_one_le_exp (z * R)
    linarith [mul_pos hz hR]
  by_cases h : p.eval 0 <= (Real.exp (z * R) + 1) / 2
  · -- Case 1: p(0) ≤ (exp(zR)+1)/2 < exp(zR), so error at r = 0 ≥ (exp(zR)-1)/2
    refine ⟨0, Set.mem_Icc.mpr ⟨le_refl 0, hR.le⟩, ?_⟩
    simp only [sub_zero]
    rw [abs_of_nonneg (by linarith)]
    linarith
  · -- Case 2: p(0) > (exp(zR)+1)/2 and p(R) ≥ p(0) > 1, so error at r = R ≥ (exp(zR)-1)/2
    push Not at h
    refine ⟨R, Set.mem_Icc.mpr ⟨hR.le, le_refl R⟩, ?_⟩
    simp only [sub_self, mul_zero, Real.exp_zero]
    rw [abs_of_nonpos (by linarith)]
    linarith

/-!
## Group GA — FMSA_GA_matrix_mix unlike-pair conditioning failure

These extend the Group-P "no polynomial fixes it" story (`poly_approx_fails`) to the
FMSA_GA_matrix_mix two-exponential base: for unlike pairs at large σ-ratio the growing base
`K·exp(z·R)` has no exp-cancellation (unlike the N=1 like pair, Task C.2), and a bounded additive
HS-pole residue sum cannot rescue it.
-/

/-- **Task GA.1 (part A) — the two-exponential base is unbounded.**  For any amplitude `K > 0`
and any target `M`, there is a state point `(z, R)` with `K·exp(z·R) ≥ M`.  Witness `z = 1`,
`R = max 0 (log (M/K)) + 1`.  This is the exponential analog of `poly_approx_fails`: the growing
factor `exp(z·R)` outruns every bound as `z·R → ∞`. -/
theorem unlike_pair_twoexp_unbounded (K : ℝ) (hK : 0 < K) (M : ℝ) :
    ∃ z R : ℝ, 0 < z ∧ 0 < R ∧ M ≤ K * Real.exp (z * R) := by
  refine ⟨1, max 0 (Real.log (M / K)) + 1, one_pos, ?_, ?_⟩
  · have := le_max_left (0:ℝ) (Real.log (M / K)); linarith
  · rw [one_mul]
    by_cases hM : M ≤ 0
    · have hpos : 0 < K * Real.exp (max 0 (Real.log (M / K)) + 1) :=
        mul_pos hK (Real.exp_pos _)
      linarith
    · have hMpos : 0 < M := lt_of_not_ge (fun h => hM h)
      have hMK : 0 < M / K := div_pos hMpos hK
      have h2 : M / K ≤ Real.exp (max 0 (Real.log (M / K)) + 1) := by
        rw [Real.exp_add]
        calc M / K = Real.exp (Real.log (M / K)) := (Real.exp_log hMK).symm
          _ ≤ Real.exp (max 0 (Real.log (M / K))) :=
              Real.exp_le_exp.mpr (le_max_right _ _)
          _ = Real.exp (max 0 (Real.log (M / K))) * 1 := (mul_one _).symm
          _ ≤ Real.exp (max 0 (Real.log (M / K))) * Real.exp 1 := by
              apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
              rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by norm_num)
      calc M = K * (M / K) := by field_simp
        _ ≤ K * Real.exp (max 0 (Real.log (M / K)) + 1) :=
            mul_le_mul_of_nonneg_left h2 hK.le

/-- **GA.1 (part B, helper) — the HS-pole residue bound follows from the propagator, not numerics.**

The Route-C residues are (`fmsa_hs_pole_residue.py:17`)
`B_k = A_k · K / (z² − s_k²)`, where `A_k := [adj Q̂₀(s_k)]_ij / det′Q̂₀(s_k)` and the `s_k` are the
zeros of `det Q̂₀`.  Both `A_k` and `s_k` are built from the **hard-sphere** Baxter matrix alone, so
they carry **no `z`-dependence**: all of it sits in `K` and the propagator `1/(z² − s_k²)`.  Hence the
`O(K/z²)` shape needs no numerical input — only that `z` outruns the poles.  Away from resonance
(`2‖s_k‖ ≤ z`) the reverse triangle inequality gives `‖z² − s_k²‖ ≥ z² − ‖s_k‖² ≥ (3/4)z²`, so
```
‖B_k‖ ≤ C·K / ((3/4)·z²) = (4/3)·C·K/z²,      C := max_k ‖A_k‖.
```
`C` exists because GA.1's pole set is **finite** (`Fin n`); this is why no `POLE.5`/`MML.5`-style
per-pole magnitude machinery is needed here — that is only required for *infinite* pole sums.

⚠ The **sharp** constant (`‖B_k‖ ≤ K/z²`, i.e. `C = 1`) is *not* a theorem: it would force
`‖A_k‖ ≤ ‖1 − s_k²/z²‖ → 1`, a numerical accident of the HS Baxter matrix.  This is why
`hs_pole_additive_insufficient` below quantifies over an arbitrary `C` — the GA.1 argument only
needs `n·C·K/z²` to be **fixed** while `K·exp(z·R) → ∞`. -/
theorem residue_propagator_bound {n : ℕ} (A s : Fin n → ℂ) {C K z : ℝ}
    (hK : 0 ≤ K) (hz : 0 < z) (hA : ∀ k, ‖A k‖ ≤ C)
    (hsep : ∀ k, 2 * ‖s k‖ ≤ z) (k : Fin n) :
    ‖A k * K / ((z : ℂ) ^ 2 - (s k) ^ 2)‖ ≤ 4 / 3 * C * K / z ^ 2 := by
  have hC : 0 ≤ C := le_trans (norm_nonneg _) (hA k)
  -- `‖s k‖² ≤ z²/4`
  have hs4 : ‖s k‖ ^ 2 ≤ z ^ 2 / 4 := by
    have h := hsep k
    have h0 : 0 ≤ ‖s k‖ := norm_nonneg _
    nlinarith [h, h0]
  -- reverse triangle: `‖z² − s_k²‖ ≥ z² − ‖s_k‖² ≥ (3/4)z²`
  have hden : 3 / 4 * z ^ 2 ≤ ‖(z : ℂ) ^ 2 - (s k) ^ 2‖ := by
    have h1 : ‖((z : ℂ) ^ 2)‖ - ‖(s k) ^ 2‖ ≤ ‖(z : ℂ) ^ 2 - (s k) ^ 2‖ := norm_sub_norm_le _ _
    have h2 : ‖((z : ℂ) ^ 2)‖ = z ^ 2 := by
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hz]
    have h3 : ‖(s k) ^ 2‖ = ‖s k‖ ^ 2 := by rw [norm_pow]
    rw [h2, h3] at h1; linarith [hs4, h1]
  have hzpos : (0 : ℝ) < z ^ 2 := by positivity
  have hdpos : (0 : ℝ) < ‖(z : ℂ) ^ 2 - (s k) ^ 2‖ := lt_of_lt_of_le (by linarith) hden
  -- numerator
  have hnum : ‖A k * (K : ℂ)‖ ≤ C * K := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hK]
    exact mul_le_mul_of_nonneg_right (hA k) hK
  rw [norm_div]
  rw [div_le_div_iff₀ hdpos (by positivity : (0:ℝ) < z ^ 2)]
  calc ‖A k * (K : ℂ)‖ * z ^ 2 ≤ (C * K) * z ^ 2 :=
        mul_le_mul_of_nonneg_right hnum (le_of_lt hzpos)
    _ ≤ 4 / 3 * C * K * ‖(z : ℂ) ^ 2 - (s k) ^ 2‖ := by
        have h := mul_le_mul_of_nonneg_left hden (by positivity : (0:ℝ) ≤ 4 / 3 * C * K)
        nlinarith [h]

/-- **Task GA.1 (part B) — a bounded additive HS-pole sum cannot cancel the base.**  If every
residue coefficient obeys `|B k| ≤ C·K/z²` (the `O(K/z²)` propagator bound, discharged structurally
by `residue_propagator_bound` above with `C := max_k ‖A_k‖`), then the corrected base can drop by at
most `n·C·K/z²`:
```
K·exp(z·R) − n·(C·K/z²) ≤ K·exp(z·R) + ∑ₖ B k.
```
Since `n·C·K/z²` is fixed while `K·exp(z·R) → ∞` (part A), no finite HS-pole set rescues the
divergence.  The bound is stated with an arbitrary `C` because the sharp `C = 1` is not provable —
see `residue_propagator_bound`.  The argument is insensitive to `C`. -/
theorem hs_pole_additive_insufficient
    {C K z R : ℝ} (_hK : 0 < K) (_hz : 0 < z) {n : ℕ} (B : Fin n → ℝ)
    (hB : ∀ k, |B k| ≤ C * K / z ^ 2) :
    K * Real.exp (z * R) - (n : ℝ) * (C * K / z ^ 2) ≤ K * Real.exp (z * R) + ∑ k, B k := by
  have hlb : - ((n : ℝ) * (C * K / z ^ 2)) ≤ ∑ k, B k := by
    have hab : |∑ k, B k| ≤ (n : ℝ) * (C * K / z ^ 2) := by
      calc |∑ k, B k| ≤ ∑ k, |B k| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _k : Fin n, (C * K / z ^ 2) := Finset.sum_le_sum (fun k _ => hB k)
        _ = (n : ℝ) * (C * K / z ^ 2) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    linarith [neg_abs_le (∑ k, B k), hab]
  linarith [hlb]

/-- **Task GA.3 — the FMSA unlike-pair perturbation ratio is unbounded.**

The ratio of the **GA-matrix split's** growing branch `K·exp(z·R)` (GA.1) to a fixed, `z`-independent
hard-sphere reference bound `M_HS > 0` on `‖c_HS,01‖` grows without bound as `z·R → ∞`: for any target
`M` there is a state point `(z, R)` making the ratio `≥ M` (e.g. 2YK `z₂≈9.3`, `R_{01}≈1.43`,
`|K₂|≈2.32` gives ratio `≳ 3.5·10⁶`).

**Scope (corrected 2026-07-17).** This says the **GA-matrix `(1−G²)/A²` split** is unusable at large
`z·R` — it is *not* a statement that first-order perturbation theory fails. The **true** `c^(1)` is
O(1)-bounded (max `|c^(1)|` = 0.332 for pair (1,2), vs this split's 1.78×10⁸) and first order at full
coupling is 1–2% accurate in `ĉ(0)`; the exponential ratio measures the split's catastrophic
cancellation. See `numerical_notes/results/true_first_order_probe.md` and the Task GA.3 scope box in
`proof_notes_failures.md`. (The unscoped reading is what retired GA.4.)

`M_HS` is taken as an explicit hypothesis (rather than derived): `c_HS,01` is a piecewise polynomial
in `r` whose coefficients depend only on packing fractions/diameters, not on `z`, so a `z`-independent
sup bound `‖c_HS,01‖_∞ ≤ M_HS(η,σ)` exists — matching the codebase's style of threading such bounds
(cf. `hs_pole_additive_insufficient`'s `hB`). Direct corollary of `unlike_pair_twoexp_unbounded`
(GA.1): apply it at target `M·M_HS`. -/
theorem perturbation_ratio_unbounded (K : ℝ) (hK : 0 < K) (M_HS : ℝ) (hM_HS : 0 < M_HS) (M : ℝ) :
    ∃ z R : ℝ, 0 < z ∧ 0 < R ∧ M ≤ (K * Real.exp (z * R)) / M_HS := by
  obtain ⟨z, R, hz, hR, hbound⟩ := unlike_pair_twoexp_unbounded K hK (M * M_HS)
  exact ⟨z, R, hz, hR, by rw [le_div_iff₀ hM_HS]; linarith [hbound]⟩

end FMSA.PolyApproxFails
