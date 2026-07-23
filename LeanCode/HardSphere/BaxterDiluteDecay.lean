/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HardSphere.BaxterRenewal

/-!
# Dilute-regime decay of the Baxter Volterra solution `baxterPsi`

`baxterPsiOuter` is the solution of the renewal (Volterra second-kind) equation on `[σ,∞)`

  `ψ(r) = baxterForcing(r) + ∫_σ^r q0_poly(r-t)·ψ(t) dt`   (`baxterPsiOuter_spec`),

with the compactly-supported (`[0,σ]`) polynomial kernel `q0_poly` and a forcing
`baxterForcing` that itself vanishes for `r ≥ 2σ`.  In the **dilute regime** where the kernel is a
contraction in `L¹`,

  `M := ∫₀^σ |q0_poly| < 1`   (⟺ `η < (3-√7)/2 ≈ 0.177`, `q0AbsL1_lt_one_of_dilute`),

the Volterra solution is globally bounded and **decays to 0** — an elementary renewal/Grönwall
argument, with NO spectral (pole-location) input.  This supplies, *unconditionally in the dilute
regime*, exactly the two load-bearing analytic clauses of the theorem `baxter_exterior_regularity`
(`OzCoreClosure.lean`):

* **exterior boundedness** `∃ C, ∀ r ≥ σ, |baxterPsi r| ≤ C` — `baxterPsi_bounded_of_dilute`;
* **exterior decay** `Tendsto (fun r => r·ozBaxterFixedPt r) atTop (𝓝 0)` (= `baxterPsi → 0`) —
  `r_mul_ozBaxterFixedPt_tendsto_zero_of_dilute`.

This is the elementary base case of Task `POLE.11` (the general-`η` version needs the genuinely
Wiener–Hopf spectral input — `∫₀^σ|q0| ≥ 1` for `η ≳ 0.177`, so no `L¹`-contraction reaches it).

## Key facts about the kernel `q0_poly`
* `q0_poly_nonpos_of_nonneg` — `q0_poly ≤ 0` on `[0,∞)` (in fact on `[0,σ]`; `= 0` beyond).
* `q0_poly_eq_zero_of_ge` — `q0_poly = 0` on `[σ,∞)` (closed).
* `q0AbsL1` — `∫₀^σ |q0_poly|`; monotone/saturating truncations + closed form `η(4-η)/(1-η)²`.
-/

open MeasureTheory Set Real Filter Topology intervalIntegral

namespace FMSA.HardSphere

noncomputable section

/-! ### Positivity of the PY `q'`, `q''` coefficients (local re-proofs; the originals are
`private` to `BaxterPoles.lean`). -/

private theorem q_prime_py_pos' {eta sigma : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) : 0 < q_prime_py eta sigma := by
  unfold q_prime_py
  have h1 : (0:ℝ) < 1 - eta := by linarith
  positivity

private theorem q_doubleprime_py_pos' {eta : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1) :
    0 < q_doubleprime_py eta := by
  unfold q_doubleprime_py
  have h1 : (0:ℝ) < 1 - eta := by linarith
  positivity

/-! ### Sign and support of the kernel `q0_poly` -/

/-- The kernel vanishes on the **closed** exterior `[σ,∞)`: `q0_poly = 0` for `σ ≤ r`. Extends
`q0_poly_outer` (which needs `σ < r`) to include the endpoint, where `q0_poly σ = 0` directly. -/
theorem q0_poly_eq_zero_of_ge {eta sigma rho r : ℝ} (hr : sigma ≤ r) :
    q0_poly eta sigma rho r = 0 := by
  rcases eq_or_lt_of_le hr with h | h
  · subst h
    rw [q0_poly_inner le_rfl]; ring
  · exact q0_poly_outer h

/-- On `[0,σ]`, `q0_poly r = ρ·(r-σ)·(π/(1-η)²)·(σ(1-η)+r(1+2η))`.  Both non-`ρ,(r-σ)` factors are
positive, so with `ρ ≥ 0` and `r ≤ σ` the kernel is `≤ 0`.  Beyond `σ` it is exactly `0`. -/
theorem q0_poly_nonpos_of_nonneg {eta sigma rho r : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (hrho : 0 ≤ rho) (hr0 : 0 ≤ r) :
    q0_poly eta sigma rho r ≤ 0 := by
  rcases le_total r sigma with hr | hr
  · rw [q0_poly_inner hr]
    -- factor as ρ·(r-σ)·bracket with bracket ≥ 0
    have h1e : (0:ℝ) < 1 - eta := by linarith
    have hbracket : (0:ℝ) ≤ q_prime_py eta sigma + q_doubleprime_py eta * (r - sigma) / 2 := by
      have heq : q_prime_py eta sigma + q_doubleprime_py eta * (r - sigma) / 2
          = Real.pi * (sigma * (1 - eta) + r * (1 + 2 * eta)) / (1 - eta) ^ 2 := by
        rw [q_prime_py, q_doubleprime_py]
        field_simp
        ring
      rw [heq]
      have hnum : (0:ℝ) ≤ sigma * (1 - eta) + r * (1 + 2 * eta) := by
        have : (0:ℝ) ≤ sigma * (1 - eta) := by positivity
        have : (0:ℝ) ≤ r * (1 + 2 * eta) := by positivity
        positivity
      positivity
    have hfactor : rho * q_prime_py eta sigma * (r - sigma)
        + rho * q_doubleprime_py eta * (r - sigma) ^ 2 / 2
        = rho * (r - sigma) * (q_prime_py eta sigma + q_doubleprime_py eta * (r - sigma) / 2) := by
      ring
    rw [hfactor]
    have hrs : r - sigma ≤ 0 := by linarith
    have : rho * (r - sigma) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hrho hrs
    exact mul_nonpos_of_nonpos_of_nonneg this hbracket
  · rw [q0_poly_eq_zero_of_ge hr]

/-! ### The `L¹` mass `q0AbsL1 = ∫₀^σ |q0_poly|` -/

/-- `q0AbsL1 = ∫₀^σ |q0_poly|`, the `L¹` mass of the renewal kernel — the Volterra contraction
constant. -/
def q0AbsL1 (eta sigma rho : ℝ) : ℝ := ∫ u in (0:ℝ)..sigma, |q0_poly eta sigma rho u|

/-- `|q0_poly|` is interval-integrable on every interval (it is continuous). -/
theorem q0_abs_intervalIntegrable (eta sigma rho a b : ℝ) :
    IntervalIntegrable (fun u => |q0_poly eta sigma rho u|) volume a b :=
  ((q0_poly_continuous eta sigma rho).abs).intervalIntegrable a b

theorem q0AbsL1_nonneg {eta sigma rho : ℝ} (hsigma : 0 < sigma) :
    0 ≤ q0AbsL1 eta sigma rho := by
  unfold q0AbsL1
  exact intervalIntegral.integral_nonneg hsigma.le (fun u _ => abs_nonneg _)

/-- The tail `∫_σ^a |q0_poly| = 0` for `a ≥ σ`, since `q0_poly = 0` on `[σ,∞)`. -/
theorem q0_abs_integral_tail_zero {eta sigma rho a : ℝ} (ha : sigma ≤ a) :
    ∫ u in sigma..a, |q0_poly eta sigma rho u| = 0 := by
  have heqon : Set.EqOn (fun u => |q0_poly eta sigma rho u|) (fun _ => (0:ℝ))
      (Set.uIcc sigma a) := by
    intro u hu
    rw [Set.uIcc_of_le ha] at hu
    simp [q0_poly_eq_zero_of_ge hu.1]
  rw [intervalIntegral.integral_congr heqon, intervalIntegral.integral_zero]

/-- For `a ≥ σ`, the truncated mass **equals** the full mass `q0AbsL1` (the tail is `0`). -/
theorem q0_abs_integral_eq_L1_of_ge {eta sigma rho a : ℝ} (ha : sigma ≤ a) :
    ∫ u in (0:ℝ)..a, |q0_poly eta sigma rho u| = q0AbsL1 eta sigma rho := by
  unfold q0AbsL1
  rw [← intervalIntegral.integral_add_adjacent_intervals
      (q0_abs_intervalIntegrable eta sigma rho 0 sigma)
      (q0_abs_intervalIntegrable eta sigma rho sigma a),
    q0_abs_integral_tail_zero ha, add_zero]

/-- Truncated mass `∫₀^a |q0_poly|` is bounded by the full mass `q0AbsL1`, for every `a`
(nonnegative integrand; the tail beyond `σ` contributes `0`). -/
theorem q0_abs_integral_le_L1 {eta sigma rho a : ℝ} :
    ∫ u in (0:ℝ)..a, |q0_poly eta sigma rho u| ≤ q0AbsL1 eta sigma rho := by
  rcases le_total sigma a with hge | hle
  · exact le_of_eq (q0_abs_integral_eq_L1_of_ge hge)
  · -- 0 ≤ a ≤ σ: split [0,σ] = [0,a] ∪ [a,σ], the second piece is nonnegative
    have hadj : (∫ u in (0:ℝ)..a, |q0_poly eta sigma rho u|)
        + (∫ u in a..sigma, |q0_poly eta sigma rho u|)
        = q0AbsL1 eta sigma rho :=
      intervalIntegral.integral_add_adjacent_intervals
        (q0_abs_intervalIntegrable eta sigma rho 0 a)
        (q0_abs_intervalIntegrable eta sigma rho a sigma)
    have hnn : 0 ≤ ∫ u in a..sigma, |q0_poly eta sigma rho u| :=
      intervalIntegral.integral_nonneg hle (fun u _ => abs_nonneg _)
    linarith

/-! ### Closed form of the mass and the dilute threshold -/

/-- **Closed form** `∫₀^σ |q0_poly| = η(4-η)/(1-η)²` — the exact `L¹` mass of the renewal kernel,
independent of `σ` once `η = πρσ³/6`.  Uses `|q0_poly| = -q0_poly` on `[0,σ]` (`q0_poly ≤ 0`) and
one FTC evaluation of the cleared quadratic, then `π ρ σ³ = 6η`. -/
theorem q0AbsL1_eq {eta sigma rho : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1) (hsigma : 0 < sigma)
    (hrho : 0 ≤ rho) (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) :
    q0AbsL1 eta sigma rho = eta * (4 - eta) / (1 - eta) ^ 2 := by
  set α : ℝ := rho * q_prime_py eta sigma with hαdef
  set β : ℝ := rho * q_doubleprime_py eta with hβdef
  -- Step 1: |q0_poly| = -q0_poly on [0,σ]
  have habs : q0AbsL1 eta sigma rho = -∫ u in (0:ℝ)..sigma, q0_poly eta sigma rho u := by
    unfold q0AbsL1
    have hcongr0 : ∫ u in (0:ℝ)..sigma, |q0_poly eta sigma rho u|
        = ∫ u in (0:ℝ)..sigma, -q0_poly eta sigma rho u := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [Set.uIcc_of_le hsigma.le] at hu
      exact abs_of_nonpos (q0_poly_nonpos_of_nonneg heta0 heta1 hsigma hrho hu.1)
    rw [hcongr0, intervalIntegral.integral_neg]
  -- Step 2: rewrite q0_poly as its cleared quadratic on [0,σ], then FTC
  have hcongr : ∫ u in (0:ℝ)..sigma, q0_poly eta sigma rho u
      = ∫ u in (0:ℝ)..sigma, (α * (u - sigma) + β * (u - sigma) ^ 2 / 2) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le hsigma.le] at hu
    rw [q0_poly_inner hu.2]
  have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) sigma,
      HasDerivAt (fun u => α * (u - sigma) ^ 2 / 2 + β * (u - sigma) ^ 3 / 6)
        (α * (x - sigma) + β * (x - sigma) ^ 2 / 2) x := by
    intro x _
    have hin : HasDerivAt (fun u : ℝ => u - sigma) 1 x := (hasDerivAt_id x).sub_const sigma
    have h2 : HasDerivAt (fun u : ℝ => (u - sigma) ^ 2) (2 * (x - sigma)) x :=
      (hin.pow 2).congr_deriv (by push_cast; ring)
    have h3 : HasDerivAt (fun u : ℝ => (u - sigma) ^ 3) (3 * (x - sigma) ^ 2) x :=
      (hin.pow 3).congr_deriv (by push_cast; ring)
    have hA : HasDerivAt (fun u : ℝ => α * (u - sigma) ^ 2 / 2) (α * (2 * (x - sigma)) / 2) x :=
      (h2.const_mul α).div_const 2
    have hB : HasDerivAt (fun u : ℝ => β * (u - sigma) ^ 3 / 6) (β * (3 * (x - sigma) ^ 2) / 6) x :=
      (h3.const_mul β).div_const 6
    exact (hA.add hB).congr_deriv (by ring)
  have hintF : ∫ u in (0:ℝ)..sigma, (α * (u - sigma) + β * (u - sigma) ^ 2 / 2)
      = -(α * sigma ^ 2 / 2) + β * sigma ^ 3 / 6 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv]
    · simp; ring
    · apply Continuous.intervalIntegrable
      fun_prop
  -- Step 3: assemble and substitute π ρ σ³ = 6η
  rw [habs, hcongr, hintF, hαdef, hβdef, q_prime_py, q_doubleprime_py]
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hσ : sigma ≠ 0 := hsigma.ne'
  have h1e : (1 : ℝ) - eta ≠ 0 := by intro h; apply absurd heta1; linarith [h]
  have hrho_eq : rho = 6 * eta / (Real.pi * sigma ^ 3) := by
    rw [heta_def]; field_simp
  rw [hrho_eq]
  field_simp
  ring

/-- **The dilute threshold.** `∫₀^σ|q0_poly| < 1 ⟺ 2η²-6η+1 > 0 ⟺ η < (3-√7)/2 ≈ 0.177`.  This is
the regime in which the Volterra kernel is an `L¹` contraction. -/
theorem q0AbsL1_lt_one_of_dilute {eta sigma rho : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (hrho : 0 ≤ rho) (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6)
    (hdilute : eta < (3 - Real.sqrt 7) / 2) :
    q0AbsL1 eta sigma rho < 1 := by
  rw [q0AbsL1_eq heta0 heta1 hsigma hrho heta_def]
  have h1e : (0 : ℝ) < (1 - eta) ^ 2 := by
    have : (0:ℝ) < 1 - eta := by linarith
    positivity
  rw [div_lt_one h1e]
  have hs7 : Real.sqrt 7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  have hs7nn : (0:ℝ) ≤ Real.sqrt 7 := Real.sqrt_nonneg 7
  have hpos : Real.sqrt 7 < 3 - 2 * eta := by nlinarith [hdilute]
  have hpos2 : (0:ℝ) < 3 - 2 * eta + Real.sqrt 7 := by nlinarith [hs7nn, hpos]
  nlinarith [hpos, hpos2, hs7]

/-! ### Support and bound of the forcing `baxterForcing` -/

/-- **The forcing has compact support `[σ,2σ]` on the exterior**: `baxterForcing r = 0` for
`r ≥ 2σ`.  For `s ∈ [0,σ]` and `r ≥ 2σ`, `r - s ≥ σ`, so `q0_poly (r-s) = 0`. -/
theorem baxterForcing_eq_zero_of_two_sigma_le {eta sigma rho r : ℝ} (hsigma : 0 < sigma)
    (hr : 2 * sigma ≤ r) : baxterForcing eta sigma rho r = 0 := by
  unfold baxterForcing
  have hzero : ∫ s in (0:ℝ)..sigma, q0_poly eta sigma rho (r - s) * (-s)
      = ∫ s in (0:ℝ)..sigma, (0:ℝ) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le hsigma.le] at hs
    have hrs : sigma ≤ r - s := by linarith [hs.2, hr]
    change q0_poly eta sigma rho (r - s) * (-s) = 0
    rw [q0_poly_eq_zero_of_ge hrs, zero_mul]
  rw [hzero, intervalIntegral.integral_zero]

/-- **The forcing is bounded on `[σ,∞)`** by its max on the compact support `[σ,2σ]` (it vanishes
beyond `2σ`).  Gives the constant `Φ` feeding the Volterra bound. -/
theorem baxterForcing_bounded_on_Ici {eta sigma rho : ℝ} (hsigma : 0 < sigma) :
    ∃ Φ, 0 ≤ Φ ∧ ∀ r, sigma ≤ r → |baxterForcing eta sigma rho r| ≤ Φ := by
  have hcont : ContinuousOn (fun r => |baxterForcing eta sigma rho r|)
      (Set.Icc sigma (2 * sigma)) :=
    ((baxterForcing_continuous eta sigma rho).abs).continuousOn
  have hne : (Set.Icc sigma (2 * sigma)).Nonempty := ⟨sigma, ⟨le_rfl, by linarith⟩⟩
  obtain ⟨x₀, hx₀mem, hx₀max⟩ := (isCompact_Icc).exists_isMaxOn hne hcont
  refine ⟨|baxterForcing eta sigma rho x₀|, abs_nonneg _, fun r hr => ?_⟩
  rcases le_total r (2 * sigma) with hle | hge
  · exact hx₀max ⟨hr, hle⟩
  · rw [baxterForcing_eq_zero_of_two_sigma_le hsigma hge, abs_zero]
    exact abs_nonneg _

/-! ### Global boundedness of the Volterra solution in the dilute regime -/

/-- **Exterior boundedness of the Baxter Volterra solution, dilute regime.**  If the renewal kernel
is an `L¹` contraction (`q0AbsL1 < 1`), then `baxterPsiOuter` is bounded on `[σ,∞)` by
`Φ/(1-M)`, where `Φ = sup_{[σ,2σ]}|baxterForcing|` and `M = q0AbsL1`.

Max-point argument (no spectral input): on any `[σ,b]`, the continuous `|ψ|` attains its max `S` at
some `rs`; the renewal equation at `rs` gives `S ≤ Φ + M·S` (the kernel integral is bounded by
`M·S` since `∫₀^a|q0| ≤ M`), hence `S ≤ Φ/(1-M)`.  Uniform in `b`, so global. -/
theorem baxterPsi_bounded_of_dilute {eta sigma rho : ℝ} (hsigma : 0 < sigma)
    (hL1 : q0AbsL1 eta sigma rho < 1) :
    ∃ C, ∀ r, sigma ≤ r → |baxterPsiOuter eta sigma rho r| ≤ C := by
  obtain ⟨Φ, hΦ0, hΦ⟩ := baxterForcing_bounded_on_Ici (eta := eta) (rho := rho) hsigma
  set qL1 := q0AbsL1 eta sigma rho with hqL1def
  have hqL10 : 0 ≤ qL1 := q0AbsL1_nonneg hsigma
  have h1q : 0 < 1 - qL1 := by linarith
  set ψ := baxterPsiOuter eta sigma rho with hψdef
  refine ⟨Φ / (1 - qL1), fun r hr => ?_⟩
  -- max of |ψ| on [σ,r]
  have hcontψ : ContinuousOn (fun x => |ψ x|) (Set.Icc sigma r) :=
    (baxterPsiOuter_continuousOn hr).abs
  have hne : (Set.Icc sigma r).Nonempty := ⟨sigma, ⟨le_rfl, hr⟩⟩
  obtain ⟨rs, hrsmem, hrsmax0⟩ := isCompact_Icc.exists_isMaxOn hne hcontψ
  have hrsmax : ∀ y ∈ Set.Icc sigma r, |ψ y| ≤ |ψ rs| := isMaxOn_iff.mp hrsmax0
  have hσrs : sigma ≤ rs := hrsmem.1
  -- integrability of the renewal integrand and its abs on [σ,rs]
  have hq0comp : Continuous (fun t => q0_poly eta sigma rho (rs - t)) :=
    (q0_poly_continuous eta sigma rho).comp (continuous_const.sub continuous_id)
  have hgcont : ContinuousOn (fun t => q0_poly eta sigma rho (rs - t) * ψ t) (Set.Icc sigma rs) :=
    hq0comp.continuousOn.mul (baxterPsiOuter_continuousOn hσrs)
  -- the kernel integral bound |∫ q0(rs-t)ψ(t)| ≤ M·|ψ rs|
  have hintbound : |∫ t in sigma..rs, q0_poly eta sigma rho (rs - t) * ψ t| ≤ qL1 * |ψ rs| := by
    have hstep1 : |∫ t in sigma..rs, q0_poly eta sigma rho (rs - t) * ψ t|
        ≤ ∫ t in sigma..rs, |q0_poly eta sigma rho (rs - t) * ψ t| := by
      have := intervalIntegral.norm_integral_le_integral_norm (μ := volume) hσrs
        (f := fun t => q0_poly eta sigma rho (rs - t) * ψ t)
      simpa only [Real.norm_eq_abs] using this
    have hstep2 : ∫ t in sigma..rs, |q0_poly eta sigma rho (rs - t) * ψ t|
        ≤ ∫ t in sigma..rs, |ψ rs| * |q0_poly eta sigma rho (rs - t)| := by
      apply intervalIntegral.integral_mono_on hσrs
      · exact (hgcont.abs).intervalIntegrable_of_Icc hσrs
      · exact ((continuous_const.mul hq0comp.abs)).intervalIntegrable _ _
      · intro t ht
        rw [abs_mul, mul_comm]
        apply mul_le_mul_of_nonneg_right (hrsmax t ⟨ht.1, le_trans ht.2 hrsmem.2⟩) (abs_nonneg _)
    have hstep3 : ∫ t in sigma..rs, |ψ rs| * |q0_poly eta sigma rho (rs - t)|
        = |ψ rs| * ∫ t in sigma..rs, |q0_poly eta sigma rho (rs - t)| :=
      intervalIntegral.integral_const_mul _ _
    have hstep4 : ∫ t in sigma..rs, |q0_poly eta sigma rho (rs - t)|
        = ∫ u in (0:ℝ)..(rs - sigma), |q0_poly eta sigma rho u| := by
      have := intervalIntegral.integral_comp_sub_left
        (fun u => |q0_poly eta sigma rho u|) rs (a := sigma) (b := rs)
      simpa using this
    have hstep5 : ∫ u in (0:ℝ)..(rs - sigma), |q0_poly eta sigma rho u| ≤ qL1 :=
      q0_abs_integral_le_L1
    calc |∫ t in sigma..rs, q0_poly eta sigma rho (rs - t) * ψ t|
        ≤ ∫ t in sigma..rs, |q0_poly eta sigma rho (rs - t) * ψ t| := hstep1
      _ ≤ ∫ t in sigma..rs, |ψ rs| * |q0_poly eta sigma rho (rs - t)| := hstep2
      _ = |ψ rs| * ∫ t in sigma..rs, |q0_poly eta sigma rho (rs - t)| := hstep3
      _ = |ψ rs| * ∫ u in (0:ℝ)..(rs - sigma), |q0_poly eta sigma rho u| := by rw [hstep4]
      _ ≤ |ψ rs| * qL1 := by apply mul_le_mul_of_nonneg_left hstep5 (abs_nonneg _)
      _ = qL1 * |ψ rs| := by ring
  -- renewal equation at rs ⇒ S ≤ Φ + M·S
  have hmain : |ψ rs| ≤ Φ + qL1 * |ψ rs| := by
    have hspec : ψ rs = baxterForcing eta sigma rho rs
        + ∫ t in sigma..rs, q0_poly eta sigma rho (rs - t) * ψ t := baxterPsiOuter_spec hσrs
    calc |ψ rs|
        = |baxterForcing eta sigma rho rs
            + ∫ t in sigma..rs, q0_poly eta sigma rho (rs - t) * ψ t| := by rw [hspec]
      _ ≤ |baxterForcing eta sigma rho rs|
            + |∫ t in sigma..rs, q0_poly eta sigma rho (rs - t) * ψ t| := abs_add_le _ _
      _ ≤ Φ + qL1 * |ψ rs| := add_le_add (hΦ rs hσrs) hintbound
  -- solve for |ψ rs| and transfer to r
  have hpsirs : |ψ rs| ≤ Φ / (1 - qL1) := by
    rw [le_div_iff₀ h1q]; nlinarith [hmain]
  calc |ψ r| ≤ |ψ rs| := hrsmax r ⟨hr, le_rfl⟩
    _ ≤ Φ / (1 - qL1) := hpsirs

/-! ### Decay to zero of the Volterra solution in the dilute regime -/

/-- **Exterior decay** `baxterPsiOuter → 0` in the dilute regime.  Beyond `2σ` the forcing
vanishes, so `|ψ(r)| ≤ M·sup_{[r-σ,r]}|ψ|`; iterating across `σ`-windows gives
`|ψ(r)| ≤ M^n·Cb` for `r ≥ 2σ + nσ`, and `M^n → 0`. -/
theorem baxterPsi_tendsto_zero_of_dilute {eta sigma rho : ℝ} (hsigma : 0 < sigma)
    (hL1 : q0AbsL1 eta sigma rho < 1) :
    Tendsto (baxterPsiOuter eta sigma rho) atTop (𝓝 0) := by
  obtain ⟨Cb, hCb⟩ := baxterPsi_bounded_of_dilute hsigma hL1
  have hCb0 : 0 ≤ Cb := le_trans (abs_nonneg _) (hCb sigma le_rfl)
  set qL1 := q0AbsL1 eta sigma rho with hqL1def
  have hqL10 : 0 ≤ qL1 := q0AbsL1_nonneg hsigma
  -- window induction: |ψ r| ≤ M^n · Cb for r ≥ 2σ + nσ
  have Hn : ∀ n : ℕ, ∀ r, 2 * sigma + (n : ℝ) * sigma ≤ r →
      |baxterPsiOuter eta sigma rho r| ≤ qL1 ^ n * Cb := by
    intro n
    induction n with
    | zero =>
      intro r hr
      simp only [Nat.cast_zero, zero_mul, add_zero] at hr
      have hrσ : sigma ≤ r := by linarith
      simpa using hCb r hrσ
    | succ n ih =>
      intro r hr
      push_cast at hr
      have hexp : ((n : ℝ) + 1) * sigma = (n : ℝ) * sigma + sigma := by ring
      have hnσ : 0 ≤ (n : ℝ) * sigma := mul_nonneg (Nat.cast_nonneg n) hsigma.le
      have hr2σ : 2 * sigma ≤ r := by linarith [hr, hexp, hnσ]
      have hrσ : sigma ≤ r := by linarith
      have hφ0 : baxterForcing eta sigma rho r = 0 :=
        baxterForcing_eq_zero_of_two_sigma_le hsigma hr2σ
      have hspec : baxterPsiOuter eta sigma rho r
          = ∫ t in sigma..r, q0_poly eta sigma rho (r - t) * baxterPsiOuter eta sigma rho t := by
        rw [baxterPsiOuter_spec hrσ, hφ0, zero_add]
      have hcontψr : ContinuousOn (baxterPsiOuter eta sigma rho) (Set.Icc sigma r) :=
        baxterPsiOuter_continuousOn hrσ
      have hq0compr : Continuous (fun t => q0_poly eta sigma rho (r - t)) :=
        (q0_poly_continuous eta sigma rho).comp (continuous_const.sub continuous_id)
      rw [hspec]
      calc |∫ t in sigma..r, q0_poly eta sigma rho (r - t) * baxterPsiOuter eta sigma rho t|
          ≤ ∫ t in sigma..r, |q0_poly eta sigma rho (r - t) * baxterPsiOuter eta sigma rho t| := by
            have := intervalIntegral.norm_integral_le_integral_norm (μ := volume) hrσ
              (f := fun t => q0_poly eta sigma rho (r - t) * baxterPsiOuter eta sigma rho t)
            simpa only [Real.norm_eq_abs] using this
        _ ≤ ∫ t in sigma..r, |q0_poly eta sigma rho (r - t)| * (qL1 ^ n * Cb) := by
            apply intervalIntegral.integral_mono_on hrσ
            · exact ((hq0compr.continuousOn.mul hcontψr).abs).intervalIntegrable_of_Icc hrσ
            · exact (hq0compr.abs.mul continuous_const).intervalIntegrable _ _
            · intro t ht
              rw [abs_mul]
              rcases eq_or_ne (q0_poly eta sigma rho (r - t)) 0 with hq | hq
              · rw [hq]; simp
              · have hrt : r - t < sigma := by
                  by_contra h
                  exact hq (q0_poly_eq_zero_of_ge (not_lt.mp h))
                have htlow : 2 * sigma + (n : ℝ) * sigma ≤ t := by linarith [hr, hexp, hrt]
                exact mul_le_mul_of_nonneg_left (ih t htlow) (abs_nonneg _)
        _ = (qL1 ^ n * Cb) * ∫ t in sigma..r, |q0_poly eta sigma rho (r - t)| := by
            rw [intervalIntegral.integral_mul_const]; ring
        _ = (qL1 ^ n * Cb) * ∫ u in (0:ℝ)..(r - sigma), |q0_poly eta sigma rho u| := by
            congr 1
            have := intervalIntegral.integral_comp_sub_left
              (fun u => |q0_poly eta sigma rho u|) r (a := sigma) (b := r)
            simpa using this
        _ = (qL1 ^ n * Cb) * qL1 := by
            rw [q0_abs_integral_eq_L1_of_ge (by linarith : sigma ≤ r - sigma)]
        _ = qL1 ^ (n + 1) * Cb := by ring
  -- M^n → 0 ⇒ the sequence of window bounds → 0 ⇒ ψ → 0
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hqpow : Tendsto (fun n : ℕ => qL1 ^ n * Cb) atTop (𝓝 0) := by
    have hp : Tendsto (fun n : ℕ => qL1 ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hqL10 hL1
    simpa using hp.mul_const Cb
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hqpow) ε hε
  refine ⟨2 * sigma + (N : ℝ) * sigma, fun r hr => ?_⟩
  have hlt : |qL1 ^ N * Cb| < ε := by
    have := hN N le_rfl
    simpa [Real.dist_eq] using this
  rw [Real.dist_eq, sub_zero]
  calc |baxterPsiOuter eta sigma rho r| ≤ qL1 ^ N * Cb := Hn N r hr
    _ ≤ |qL1 ^ N * Cb| := le_abs_self _
    _ < ε := hlt

/-! ### The clauses of the theorem `baxter_exterior_regularity`, discharged in the dilute regime -/

/-- **Boundedness clause** of `baxter_exterior_regularity` (clause 2), dilute regime: the glued
`baxterPsi` is bounded on `[σ,∞)`. -/
theorem baxterPsi_bounded_Ici_of_dilute {eta sigma rho : ℝ} (hsigma : 0 < sigma)
    (hL1 : q0AbsL1 eta sigma rho < 1) :
    ∃ C, ∀ r, sigma ≤ r → |baxterPsi eta sigma rho r| ≤ C := by
  obtain ⟨C, hC⟩ := baxterPsi_bounded_of_dilute hsigma hL1
  refine ⟨C, fun r hr => ?_⟩
  rw [baxterPsi_outer hr]
  exact hC r hr


/-! ### Unconditional decay for the physical dilute regime `η < (3-√7)/2 ≈ 0.177`

The three theorems above, with the `L¹`-contraction hypothesis discharged by the explicit dilute
threshold (`q0AbsL1_lt_one_of_dilute`).  These are the physically-parametrised statements: given the
hard-sphere relation `η = πρσ³/6` and `η < (3-√7)/2`, the constructed Baxter exterior solution
`baxterPsi` is bounded on `[σ,∞)` and decays to `0` — the two load-bearing analytic clauses of
`baxter_exterior_regularity`, proved unconditionally in this regime. -/

theorem baxterPsi_bounded_of_eta_dilute {eta sigma rho : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (hrho : 0 ≤ rho) (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6)
    (hdilute : eta < (3 - Real.sqrt 7) / 2) :
    ∃ C, ∀ r, sigma ≤ r → |baxterPsi eta sigma rho r| ≤ C :=
  baxterPsi_bounded_Ici_of_dilute hsigma
    (q0AbsL1_lt_one_of_dilute heta0 heta1 hsigma hrho heta_def hdilute)

theorem baxterPsi_tendsto_zero_of_eta_dilute {eta sigma rho : ℝ} (heta0 : 0 < eta)
    (heta1 : eta < 1) (hsigma : 0 < sigma) (hrho : 0 ≤ rho)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) (hdilute : eta < (3 - Real.sqrt 7) / 2) :
    Tendsto (baxterPsiOuter eta sigma rho) atTop (𝓝 0) :=
  baxterPsi_tendsto_zero_of_dilute hsigma
    (q0AbsL1_lt_one_of_dilute heta0 heta1 hsigma hrho heta_def hdilute)


end

end FMSA.HardSphere
