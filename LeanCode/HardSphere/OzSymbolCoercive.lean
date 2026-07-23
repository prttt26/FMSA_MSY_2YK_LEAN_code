/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HardSphere.BaxterOzStar
import LeanCode.HardSphere.RadialFourierCHS
import LeanCode.HardSphere.BaxterNoSpinodalEquiv

/-!
# Coercivity of the OZ symbol `1 − ρ·Ĉ(k)`

The PY hard-sphere structure factor `1 − ρ·Ĉ(k)` is not merely pointwise positive
(`one_sub_rho_radial_fourier_c_HS_pos`, from `pyhs_no_spinodal`) — it is **coercive**: bounded away
from `0` by a uniform `ε > 0`.  This is the hypothesis the bounded Wiener–Hopf injectivity fact
consumes.

The proof splits `ℝ` into three regions:
* **near `0`** (`|k| ≤ π/σ`): a *sign* argument — on `(0,σ)`, `c_HS < 0` and `sin(kr) ≥ 0`
  (since `kr ≤ kσ ≤ π`), so `∫₀^σ r·c_HS·sin(kr) ≤ 0`, giving `1 − ρĈ(k) ≥ 1`.  This sidesteps
  the `k = 0` discontinuity of `radial_fourier` (`4π/k` prefactor; junk value `Ĉ(0)=0`).
* **middle** (`π/σ ≤ |k| ≤ K`): a compact set on which `Ĉ` is continuous (away from `0`) and
  `1 − ρĈ > 0` pointwise, so it attains a positive minimum.
* **tail** (`|k| ≥ K`): `|Ĉ(k)| ≤ cHS_bound/k² → 0` (`radial_fourier_c_HS_le`), so `1 − ρĈ ≥ 1/2`.
-/

open MeasureTheory Set Real Filter Topology

namespace FMSA.HardSphere

noncomputable section

/-- `radial_fourier` is **even** in `k` (`sin` is odd, `1/k` is odd). -/
theorem radial_fourier_neg (f : ℝ → ℝ) (k : ℝ) :
    radial_fourier f (-k) = radial_fourier f k := by
  unfold radial_fourier
  have hint : (∫ r in Set.Ioi (0:ℝ), r * f r * Real.sin (-k * r))
      = -∫ r in Set.Ioi (0:ℝ), r * f r * Real.sin (k * r) := by
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi (fun r _ => ?_)
    rw [show -k * r = -(k * r) by ring, Real.sin_neg]; ring
  rw [hint, div_neg]; ring

/-- `|r·c_HS(r)|` is interval integrable on `[0,σ]` (measurable, bounded via `c_HS_bddOn`). -/
theorem cHS_r_abs_intervalIntegrable {eta sigma : ℝ} (hsigma : 0 < sigma) :
    IntervalIntegrable (fun r => |r * c_HS eta sigma r|) volume 0 sigma := by
  obtain ⟨Cc, hCc0, hCc⟩ := c_HS_bddOn (eta := eta) (sigma := sigma) hsigma
  refine intervalIntegrable_of_aesm_bddOn (C := sigma * Cc)
    (continuous_abs.comp_aestronglyMeasurable
      (measurable_id.mul (c_HS_measurable eta sigma)).aestronglyMeasurable) ?_
  intro r hr
  rw [Set.uIcc_of_le hsigma.le] at hr
  obtain ⟨hr0, hrσ⟩ := hr
  simp only [id_eq, abs_abs, abs_mul, abs_of_nonneg hr0]
  exact mul_le_mul hrσ (hCc r ⟨hr0, hrσ⟩) (abs_nonneg _) hsigma.le

/-- The sine transform integral `k ↦ ∫₀^σ r·c_HS(r)·sin(kr)` is continuous in `k`
(dominated convergence: integrand bounded by the integrable `|r·c_HS(r)|`). -/
theorem cHS_sine_intervalIntegral_continuous {eta sigma : ℝ} (hsigma : 0 < sigma) :
    Continuous (fun k => ∫ r in (0:ℝ)..sigma, r * c_HS eta sigma r * Real.sin (k * r)) := by
  refine intervalIntegral.continuous_of_dominated_interval
    (bound := fun r => |r * c_HS eta sigma r|) ?_ ?_
    (cHS_r_abs_intervalIntegrable hsigma) ?_
  · intro k
    exact ((measurable_id.mul (c_HS_measurable eta sigma)).mul
      (Real.measurable_sin.comp (measurable_const.mul measurable_id))).aestronglyMeasurable
  · intro k
    refine Filter.Eventually.of_forall (fun r _ => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have hsin : |Real.sin (k * r)| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
    calc |r * c_HS eta sigma r| * |Real.sin (k * r)|
        ≤ |r * c_HS eta sigma r| * 1 := mul_le_mul_of_nonneg_left hsin (abs_nonneg _)
      _ = |r * c_HS eta sigma r| := mul_one _
  · refine Filter.Eventually.of_forall (fun r _ => ?_)
    exact continuous_const.mul (Real.continuous_sin.comp (continuous_id.mul continuous_const))

/-- `radial_fourier (c_HS)` is continuous away from `0` (the only place its `4π/k` prefactor
misbehaves). -/
theorem radial_fourier_c_HS_continuousOn_ne_zero {eta sigma : ℝ} (hsigma : 0 < sigma) {s : Set ℝ}
    (hs : ∀ k ∈ s, k ≠ 0) : ContinuousOn (radial_fourier (c_HS eta sigma)) s := by
  have heq : ∀ k ∈ s, radial_fourier (c_HS eta sigma) k
      = (4 * Real.pi / k) * ∫ r in (0:ℝ)..sigma, r * c_HS eta sigma r * Real.sin (k * r) :=
    fun k _ => radial_fourier_c_HS_eq_intervalIntegral eta sigma k hsigma
  refine ContinuousOn.congr ?_ heq
  refine (continuousOn_const.div continuousOn_id hs).mul ?_
  exact (cHS_sine_intervalIntegral_continuous hsigma).continuousOn

/-- **Near-zero sign bound.** `1 ≤ 1 − ρ·Ĉ(k)` for `|k| ≤ π/σ`. -/
theorem one_sub_rho_radial_fourier_c_HS_ge_one {eta sigma rho : ℝ} (heta0 : 0 < eta)
    (heta1 : eta < 1) (hsigma : 0 < sigma) (hrho : 0 < rho) {k : ℝ} (hk : |k| ≤ Real.pi / sigma) :
    (1 : ℝ) ≤ 1 - rho * radial_fourier (c_HS eta sigma) k := by
  -- reduce to `0 ≤ k` by evenness
  wlog hk0 : 0 ≤ k generalizing k with H
  · have := H (k := -k) (by rwa [abs_neg]) (by linarith [not_le.mp hk0])
    rwa [radial_fourier_neg] at this
  rcases eq_or_lt_of_le hk0 with hk0' | hkpos
  · -- k = 0: `Ĉ(0) = 0`
    rw [← hk0']
    have hz : radial_fourier (c_HS eta sigma) 0 = 0 := by
      unfold radial_fourier; simp
    rw [hz, mul_zero, sub_zero]
  · -- 0 < k ≤ π/σ: sign argument
    have hkπ : k ≤ Real.pi / sigma := by rwa [abs_of_nonneg hk0] at hk
    have hnonpos : (∫ r in (0:ℝ)..sigma, r * c_HS eta sigma r * Real.sin (k * r)) ≤ 0 := by
      rw [intervalIntegral.integral_of_le hsigma.le]
      refine setIntegral_nonpos measurableSet_Ioc (fun r hr => ?_)
      obtain ⟨hr0, hrσ⟩ := hr
      rcases eq_or_lt_of_le hrσ with hrσ' | hrσ'
      · rw [hrσ', c_HS_contact]; simp
      · have hcHS : c_HS eta sigma r < 0 := c_HS_neg heta0 heta1 hsigma hr0 hrσ'
        have hkr : k * r ≤ Real.pi := by
          have h1 : k * r ≤ k * sigma := mul_le_mul_of_nonneg_left hrσ hk0
          have h2 : k * sigma ≤ Real.pi := by
            rw [← le_div_iff₀ hsigma]; exact hkπ
          linarith
        have hsin : 0 ≤ Real.sin (k * r) :=
          Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) hkr
        have hrc : r * c_HS eta sigma r ≤ 0 :=
          le_of_lt (mul_neg_of_pos_of_neg hr0 hcHS)
        calc r * c_HS eta sigma r * Real.sin (k * r)
            ≤ 0 * Real.sin (k * r) := mul_le_mul_of_nonneg_right hrc hsin
          _ = 0 := zero_mul _
    have hĈ : radial_fourier (c_HS eta sigma) k ≤ 0 := by
      rw [radial_fourier_c_HS_eq_intervalIntegral eta sigma k hsigma]
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hnonpos
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hrho.le hĈ]

/-- **Coercivity of the OZ symbol.**  `∃ ε > 0, ∀ k, ε ≤ 1 − ρ·Ĉ(k)`. -/
theorem one_sub_rho_radial_fourier_c_HS_coercive {eta sigma rho : ℝ} (heta0 : 0 < eta)
    (heta1 : eta < 1) (hsigma : 0 < sigma) (hrho : 0 < rho)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) :
    ∃ ε, 0 < ε ∧ ∀ k, ε ≤ 1 - rho * radial_fourier (c_HS eta sigma) k := by
  set g : ℝ → ℝ := fun k => 1 - rho * radial_fourier (c_HS eta sigma) k with hg
  have hgpos : ∀ k, 0 < g k :=
    fun k => one_sub_rho_radial_fourier_c_HS_pos heta0 heta1 hsigma hrho heta_def k
  -- tail threshold `K ≥ max(π/σ, 1)` with `ρ·cHS_bound/K² ≤ 1/2`
  set B := cHS_bound eta sigma with hB
  have hB0 : 0 ≤ B := cHS_bound_nonneg eta sigma hsigma
  set K := max (Real.pi / sigma) (max 1 (Real.sqrt (2 * rho * B) + 1)) with hKdef
  have hK1 : (1 : ℝ) ≤ K := le_trans (le_max_left _ _) (le_max_right _ _)
  have hKπ : Real.pi / sigma ≤ K := le_max_left _ _
  have hKsqrt : Real.sqrt (2 * rho * B) + 1 ≤ K :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have hKpos : 0 < K := lt_of_lt_of_le one_pos hK1
  -- tail bound: `|k| ≥ K ⟹ g k ≥ 1/2`
  have htail : ∀ k, K ≤ |k| → (1:ℝ)/2 ≤ g k := by
    intro k hk
    have hbound : |radial_fourier (c_HS eta sigma) k| ≤ B / K ^ 2 := by
      rcases le_or_gt 0 k with hk0 | hk0
      · have hkK : K ≤ k := by rwa [abs_of_nonneg hk0] at hk
        refine le_trans (radial_fourier_c_HS_le eta sigma k hsigma (le_trans hK1 hkK)) ?_
        apply div_le_div_of_nonneg_left hB0 (by positivity)
        exact pow_le_pow_left₀ hKpos.le hkK 2
      · have hkK : K ≤ -k := by rwa [abs_of_neg hk0] at hk
        rw [← radial_fourier_neg]
        refine le_trans (radial_fourier_c_HS_le eta sigma (-k) hsigma (le_trans hK1 hkK)) ?_
        apply div_le_div_of_nonneg_left hB0 (by positivity)
        exact pow_le_pow_left₀ hKpos.le hkK 2
    have hsmall : rho * B / K ^ 2 ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      have hsq : (Real.sqrt (2 * rho * B)) ^ 2 ≤ K ^ 2 := by
        have h0 : 0 ≤ Real.sqrt (2 * rho * B) := Real.sqrt_nonneg _
        nlinarith [pow_le_pow_left₀ h0 (by linarith [hKsqrt] : Real.sqrt (2 * rho * B) ≤ K) 2]
      have hsqval : (Real.sqrt (2 * rho * B)) ^ 2 = 2 * rho * B :=
        Real.sq_sqrt (by positivity)
      nlinarith [hsqval, hsq]
    have habs : rho * radial_fourier (c_HS eta sigma) k ≤ rho * B / K ^ 2 := by
      calc rho * radial_fourier (c_HS eta sigma) k
          ≤ rho * |radial_fourier (c_HS eta sigma) k| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) hrho.le
        _ ≤ rho * (B / K ^ 2) := mul_le_mul_of_nonneg_left hbound hrho.le
        _ = rho * B / K ^ 2 := by ring
    rw [hg]; linarith
  -- middle: `g` continuous & positive on the compact `[π/σ, K]`, attains positive min
  have hmidset : ((Set.Icc (Real.pi / sigma) K)).Nonempty := ⟨K, ⟨hKπ, le_refl K⟩⟩
  have hgcont : ContinuousOn g (Set.Icc (Real.pi / sigma) K) := by
    refine continuousOn_const.sub (continuousOn_const.mul ?_)
    refine radial_fourier_c_HS_continuousOn_ne_zero hsigma (fun k hk => ?_)
    have : 0 < Real.pi / sigma := by positivity
    exact ne_of_gt (lt_of_lt_of_le this hk.1)
  obtain ⟨k₀, hk₀mem, hk₀min⟩ := isCompact_Icc.exists_isMinOn hmidset hgcont
  set m := g k₀ with hm
  have hmpos : 0 < m := hgpos k₀
  refine ⟨min (1/2) m, lt_min (by norm_num) hmpos, fun k => ?_⟩
  rcases le_or_gt (|k|) (Real.pi / sigma) with hnear | hfar
  · -- near zero: `g k ≥ 1 ≥ min`
    have hge := one_sub_rho_radial_fourier_c_HS_ge_one heta0 heta1 hsigma hrho hnear
    exact le_trans (min_le_left _ _) (le_trans (by norm_num) hge)
  · rcases le_or_gt K (|k|) with htk | hmk
    · exact le_trans (min_le_left _ _) (htail k htk)
    · -- middle: `|k| ∈ (π/σ, K)`; reduce to `k ∈ [π/σ, K]` by evenness
      have hgeven : g (-k) = g k := by simp only [hg, radial_fourier_neg]
      rcases le_or_gt 0 k with hk0 | hk0
      · have hmem : k ∈ Set.Icc (Real.pi / sigma) K := by
          rw [abs_of_nonneg hk0] at hfar hmk; exact ⟨hfar.le, hmk.le⟩
        exact le_trans (min_le_right _ _) (isMinOn_iff.mp hk₀min k hmem)
      · have hmem : -k ∈ Set.Icc (Real.pi / sigma) K := by
          rw [abs_of_neg hk0] at hfar hmk; exact ⟨hfar.le, hmk.le⟩
        calc min (1/2) m ≤ m := min_le_right _ _
          _ ≤ g (-k) := isMinOn_iff.mp hk₀min (-k) hmem
          _ = g k := hgeven

end

end FMSA.HardSphere
