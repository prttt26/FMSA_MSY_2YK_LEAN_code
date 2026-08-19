/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.YukawaOZ.MSAFactorizationSplit
import LeanCode.YukawaOZ.MSABaxterTransform

/-!
# MSAEXACT.1 — the `c`-side, and the reduction to one core identity

Group **MSAEXACT** (`proof_notes_msa_exact.md`).  Numerical partner:
`msaexact1_cside_check.py`.

`MSAFactorizationSplit.lean` reduced MSAEXACT.1 to matching the `O(D)`/`O(D²)` increments of the
factorization's left side against `−ρ(ĉ_MSA − ĉ_HS)(k)`.  That match needs the right side, and the
right side has two halves of very different character:

* **the exterior**, which the MSA closure *gives* us: `c(r) = −βu(r) = K e^{−z(r−σ)}/r` for `r > σ`.
  The radial transform's `r` cancels the `1/r` exactly, so this half is an elementary integral —
  `yukawa_tail_sine_integral` below, and it is closed here;
* **the core**, which is Waisman's Eq. (2) and is *not* closed here.  ⚠ Eq. (2) is printed with its
  `v²` term missing a `1/x` (`waisman_msa_closed_form.md` §7f), so formalizing the printed form
  would be formalizing a false statement.

Hence the shape of this file: everything except the core transform is discharged, and what remains
is isolated as a **single scalar unknown** `cCore` in `msaexact1_iff_core`.  The identity that
`cCore` has to satisfy is fully explicit — no integrals of unknown functions on the right — so it
can be, and has been, checked numerically before anyone formalizes Eq. (2).

⭐ **That check is worth stating.**  `msaexact1_cside_check.py` evaluates the factorization
`F(ik)F(−ik) = 1 − ρĉ(k)` with the left side from the Baxter factor and the right side assembled
from Eq. (2) plus this file's tail.  With the `1/x` repair it holds to `1e-15` (`1e-10` at the
smallest `k`, which is the quadrature's own floor) across eight states; with Eq. (2) as printed it
fails by up to `5.1` **and drives `1 − ρĉ(k)` negative at three sampled points** — impossible for a
squared modulus.  So the repair is confirmed a second time, independently of the contact value `y₀`
that found it, and now at every `k` rather than at `r = σ`.

## Results

* `msaBaxter_cos_transform`, `msaBaxter_sin_transform` — the ansatz's transform really is
  `(hard-sphere) + D·(exponential)`, so `msa_lhs_split` applies to `msaBaxterFn` itself.
* `yukawa_tail_sine_integral` — `∫_σ^∞ e^{−z(r−σ)}sin(kr) dr = (k cos kσ + z sin kσ)/(z²+k²)`.
* `cMSAtail`, `radial_fourier_cMSAtail` — the exterior MSA DCF and its radial Fourier transform.
* ⭐ `msaexact1_iff_core` — **the reduction**: given the split of `ĉ_MSA` into hard-sphere, core
  correction, and exterior tail, the MSA factorization holds **iff** the core correction's transform
  equals an explicit closed form.  Nothing about the core is assumed; it is the one unknown.
* `msaexact1_core_at_zero_coupling` — at `K = 0`, `D = 0` the required core correction is `0`,
  i.e. the reduction is consistent with the hard-sphere case it must contain.
-/

open MeasureTheory intervalIntegral Real Set Filter Topology

namespace FMSA.MSAExact

open FMSA.HardSphere

/-! ### The ansatz's transform splits -/

/-- The MSA Baxter function's cosine transform is the hard-sphere one plus `D` times the
exponential one — the hypothesis under which `msa_lhs_split` is about `msaBaxterFn`. -/
theorem msaBaxter_cos_transform (eta sigma rho z Dq k : ℝ) :
    (∫ r in (0 : ℝ)..sigma, msaBaxterFn eta sigma rho z Dq r * Real.cos (k * r))
      = (∫ r in (0 : ℝ)..sigma, q0_poly eta sigma rho r * Real.cos (k * r))
        + Dq * ∫ r in (0 : ℝ)..sigma, Real.exp (-z * r) * Real.cos (k * r) := by
  have h1 : IntervalIntegrable (fun r => q0_poly eta sigma rho r * Real.cos (k * r))
      volume 0 sigma :=
    (((q0_poly_continuous eta sigma rho).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id)))).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun r => Dq * (Real.exp (-z * r) * Real.cos (k * r)))
      volume 0 sigma :=
    (continuous_const.mul
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
        (Real.continuous_cos.comp (continuous_const.mul continuous_id)))).intervalIntegrable _ _
  have hcongr : (fun r => msaBaxterFn eta sigma rho z Dq r * Real.cos (k * r))
      = fun r => q0_poly eta sigma rho r * Real.cos (k * r)
          + Dq * (Real.exp (-z * r) * Real.cos (k * r)) := by
    funext r; unfold msaBaxterFn; ring
  rw [hcongr, intervalIntegral.integral_add h1 h2, intervalIntegral.integral_const_mul]

/-- The sine partner of `msaBaxter_cos_transform`. -/
theorem msaBaxter_sin_transform (eta sigma rho z Dq k : ℝ) :
    (∫ r in (0 : ℝ)..sigma, msaBaxterFn eta sigma rho z Dq r * Real.sin (k * r))
      = (∫ r in (0 : ℝ)..sigma, q0_poly eta sigma rho r * Real.sin (k * r))
        + Dq * ∫ r in (0 : ℝ)..sigma, Real.exp (-z * r) * Real.sin (k * r) := by
  have h1 : IntervalIntegrable (fun r => q0_poly eta sigma rho r * Real.sin (k * r))
      volume 0 sigma :=
    (((q0_poly_continuous eta sigma rho).mul
      (Real.continuous_sin.comp (continuous_const.mul continuous_id)))).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun r => Dq * (Real.exp (-z * r) * Real.sin (k * r)))
      volume 0 sigma :=
    (continuous_const.mul
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
        (Real.continuous_sin.comp (continuous_const.mul continuous_id)))).intervalIntegrable _ _
  have hcongr : (fun r => msaBaxterFn eta sigma rho z Dq r * Real.sin (k * r))
      = fun r => q0_poly eta sigma rho r * Real.sin (k * r)
          + Dq * (Real.exp (-z * r) * Real.sin (k * r)) := by
    funext r; unfold msaBaxterFn; ring
  rw [hcongr, intervalIntegral.integral_add h1 h2, intervalIntegral.integral_const_mul]

/-! ### The exterior Yukawa tail -/

/-- The exterior integrand decays exponentially, so it is integrable on `(σ, ∞)`. -/
private theorem tail_integrableOn {z : ℝ} (hz : 0 < z) (k sigma : ℝ) :
    IntegrableOn (fun r => Real.exp (-z * (r - sigma)) * Real.sin (k * r)) (Ioi sigma) := by
  refine Integrable.mono' ((exp_neg_integrableOn_Ioi sigma hz).const_mul
    (Real.exp (z * sigma))) ?_ ?_
  · exact ((Real.continuous_exp.comp
      ((continuous_id.sub continuous_const).const_mul (-z))).mul
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun r => ?_
    have hs : ‖Real.sin (k * r)‖ ≤ 1 := by
      simpa using Real.abs_sin_le_one (k * r)
    have hsplit : Real.exp (-z * (r - sigma)) = Real.exp (z * sigma) * Real.exp (-z * r) := by
      rw [← Real.exp_add]; congr 1; ring
    calc ‖Real.exp (-z * (r - sigma)) * Real.sin (k * r)‖
        = Real.exp (-z * (r - sigma)) * ‖Real.sin (k * r)‖ := by
          rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      _ ≤ Real.exp (-z * (r - sigma)) * 1 :=
          mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le
      _ = Real.exp (z * sigma) * Real.exp (-z * r) := by rw [mul_one, hsplit]

/-- **The exterior sine integral.**  `∫_σ^∞ e^{−z(r−σ)}sin(kr) dr = (k cos kσ + z sin kσ)/(z²+k²)`.

This is the `c`-side partner of `yukawa_tail_laplace`: the Laplace version is what the Baxter
factor needs, this Fourier version is what the DCF needs.  Antiderivative
`−e^{−z(r−σ)}(z sin kr + k cos kr)/(z²+k²)`, which tends to `0` because the exponential does and the
trigonometric bracket is bounded — that boundedness is the only place `z > 0` is used. -/
theorem yukawa_tail_sine_integral {z : ℝ} (hz : 0 < z) (k sigma : ℝ) :
    (∫ r in Ioi sigma, Real.exp (-z * (r - sigma)) * Real.sin (k * r))
      = (k * Real.cos (k * sigma) + z * Real.sin (k * sigma)) / (z ^ 2 + k ^ 2) := by
  have hzk : z ^ 2 + k ^ 2 ≠ 0 := by positivity
  set F : ℝ → ℝ := fun r =>
    -(Real.exp (-z * (r - sigma)) * (z * Real.sin (k * r) + k * Real.cos (k * r)))
      / (z ^ 2 + k ^ 2) with hF
  have hderiv : ∀ r ∈ Ici sigma,
      HasDerivAt F (Real.exp (-z * (r - sigma)) * Real.sin (k * r)) r := by
    intro r _
    have hexp : HasDerivAt (fun t : ℝ => Real.exp (-z * (t - sigma)))
        (-z * Real.exp (-z * (r - sigma))) r := by
      have : HasDerivAt (fun t : ℝ => -z * (t - sigma)) (-z) r := by
        simpa using ((hasDerivAt_id r).sub_const sigma).const_mul (-z)
      simpa [mul_comm] using this.exp
    have hsin : HasDerivAt (fun t : ℝ => Real.sin (k * t)) (k * Real.cos (k * r)) r := by
      simpa [mul_comm] using ((hasDerivAt_id r).const_mul k).sin
    have hcos : HasDerivAt (fun t : ℝ => Real.cos (k * t)) (-(k * Real.sin (k * r))) r := by
      simpa [mul_comm] using ((hasDerivAt_id r).const_mul k).cos
    have hin : HasDerivAt (fun t : ℝ => z * Real.sin (k * t) + k * Real.cos (k * t))
        (z * (k * Real.cos (k * r)) + k * -(k * Real.sin (k * r))) r :=
      (hsin.const_mul z).add (hcos.const_mul k)
    refine (((hexp.mul hin).neg).div_const (z ^ 2 + k ^ 2)).congr_deriv ?_
    field_simp
    ring
  have htend : Tendsto F atTop (𝓝 0) := by
    have hbound : ∀ r : ℝ, ‖F r‖
        ≤ (Real.exp (z * sigma) * (|z| + |k|) / (z ^ 2 + k ^ 2)) * Real.exp (-z * r) := by
      intro r
      have hs : |Real.sin (k * r)| ≤ 1 := Real.abs_sin_le_one _
      have hc : |Real.cos (k * r)| ≤ 1 := Real.abs_cos_le_one _
      have htr : |z * Real.sin (k * r) + k * Real.cos (k * r)| ≤ |z| + |k| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul]
        have h1 : |z| * |Real.sin (k * r)| ≤ |z| * 1 :=
          mul_le_mul_of_nonneg_left hs (abs_nonneg _)
        have h2 : |k| * |Real.cos (k * r)| ≤ |k| * 1 :=
          mul_le_mul_of_nonneg_left hc (abs_nonneg _)
        linarith
      have hsplit : Real.exp (-z * (r - sigma)) = Real.exp (z * sigma) * Real.exp (-z * r) := by
        rw [← Real.exp_add]; congr 1; ring
      have hpos : (0 : ℝ) < z ^ 2 + k ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hzk)
      rw [hF]
      simp only [Real.norm_eq_abs, abs_div, abs_neg, abs_mul, abs_of_pos (Real.exp_pos _),
        abs_of_pos hpos]
      rw [hsplit, div_le_iff₀ hpos]
      have := mul_le_mul_of_nonneg_left htr
        (mul_pos (Real.exp_pos (z * sigma)) (Real.exp_pos (-z * r))).le
      calc Real.exp (z * sigma) * Real.exp (-z * r) * |z * Real.sin (k * r) + k * Real.cos (k * r)|
          ≤ Real.exp (z * sigma) * Real.exp (-z * r) * (|z| + |k|) := this
        _ = Real.exp (z * sigma) * (|z| + |k|) / (z ^ 2 + k ^ 2) * Real.exp (-z * r)
              * (z ^ 2 + k ^ 2) := by field_simp
    refine squeeze_zero_norm hbound ?_
    have : Tendsto (fun r : ℝ => Real.exp (-z * r)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith : -z < 0))
    simpa using this.const_mul (Real.exp (z * sigma) * (|z| + |k|) / (z ^ 2 + k ^ 2))
  rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' hderiv
      (tail_integrableOn hz k sigma) htend, hF]
  simp only [zero_sub, sub_self, mul_zero, Real.exp_zero, one_mul]
  field_simp
  ring

/-! ### The exterior MSA DCF and its radial transform -/

/-- The MSA closure's exterior direct correlation function: `c(r) = K e^{−z(r−σ)}/r` for `r > σ`,
and `0` inside — the *increment* over the hard-sphere DCF outside the core. -/
noncomputable def cMSAtail (K z sigma : ℝ) (r : ℝ) : ℝ :=
  if sigma < r then K * Real.exp (-z * (r - sigma)) / r else 0

/-- **The exterior tail's radial Fourier transform.**
`𝓕_r[c_tail](k) = (4πK/k)·(k cos kσ + z sin kσ)/(z² + k²)`.

The radial transform carries a factor `r` and the Yukawa a factor `1/r`; they cancel exactly, which
is why this half of the `c`-side is elementary while the core half is not. -/
theorem radial_fourier_cMSAtail {z sigma : ℝ} (hz : 0 < z) (hsigma : 0 < sigma) (K k : ℝ) :
    radial_fourier (cMSAtail K z sigma) k
      = 4 * Real.pi * K / k
        * ((k * Real.cos (k * sigma) + z * Real.sin (k * sigma)) / (z ^ 2 + k ^ 2)) := by
  have hind : ∀ r ∈ Ioi (0 : ℝ), r * cMSAtail K z sigma r * Real.sin (k * r)
      = (Ioi sigma).indicator
          (fun r => K * (Real.exp (-z * (r - sigma)) * Real.sin (k * r))) r := by
    intro r hr
    have hr0 : r ≠ 0 := ne_of_gt hr
    by_cases h : sigma < r
    · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr h)]
      unfold cMSAtail
      rw [if_pos h]
      field_simp
    · rw [Set.indicator_of_notMem (by simpa using h)]
      unfold cMSAtail
      rw [if_neg h]
      ring
  unfold radial_fourier
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hind,
    MeasureTheory.setIntegral_indicator measurableSet_Ioi,
    Set.Ioi_inter_Ioi, max_eq_right hsigma.le,
    MeasureTheory.integral_const_mul, yukawa_tail_sine_integral hz k sigma]
  ring

/-! ### The reduction -/

/-- ⭐ **MSAEXACT.1, reduced to one scalar identity about the core.**

Suppose the MSA direct correlation function's transform splits as

    ĉ_MSA(k) = ĉ_HS(k) + cCore + 𝓕_r[c_tail](k)

— hard sphere, plus a core correction whose transform is the single real number `cCore`, plus the
exterior Yukawa the MSA closure prescribes.  Then the Baxter factorization for the MSA ansatz
`q0_poly + D·e^{−zr}` holds **if and only if** `cCore` takes the explicit value below.

Everything on the right is closed form: the hard-sphere transforms `Re₀`, `Im₀` are
`q0poly_cos_integral_formula`/`q0poly_sin_integral_formula`, the exponential ones are
`exp_cos_integral`/`exp_sin_integral`, and the `D²` bracket is `msa_exp_sq_modulus`.  So the whole
of MSAEXACT.1 that is left is: *show Waisman's Eq. (2) has this transform.*

⚠ Which is why the statement is an `iff` and not a theorem about Eq. (2): Eq. (2) as printed does
**not** satisfy it — see the module docstring and `msaexact1_cside_check.py`. -/
theorem msaexact1_iff_core
    (eta sigma rho z K D k cCore chatMSA : ℝ)
    (hsigma : 0 < sigma) (hk : k ≠ 0) (hz : 0 < z)
    (heta : eta < 1) (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6)
    (hsplit : chatMSA = radial_fourier (c_HS eta sigma) k + cCore
        + radial_fourier (cMSAtail K z sigma) k) :
    (1 - (∫ r in (0 : ℝ)..sigma, msaBaxterFn eta sigma rho z D r * Real.cos (k * r))) ^ 2
        + (∫ r in (0 : ℝ)..sigma, msaBaxterFn eta sigma rho z D r * Real.sin (k * r)) ^ 2
        = 1 - rho * chatMSA
      ↔ rho * cCore
          = 2 * D * ((1 - ∫ r in (0 : ℝ)..sigma, q0_poly eta sigma rho r * Real.cos (k * r))
                * (∫ r in (0 : ℝ)..sigma, Real.exp (-z * r) * Real.cos (k * r))
              - (∫ r in (0 : ℝ)..sigma, q0_poly eta sigma rho r * Real.sin (k * r))
                * (∫ r in (0 : ℝ)..sigma, Real.exp (-z * r) * Real.sin (k * r)))
            - D ^ 2 * ((1 - 2 * Real.exp (-z * sigma) * Real.cos (k * sigma)
                + Real.exp (-z * sigma) ^ 2) / (z ^ 2 + k ^ 2))
            - rho * (4 * Real.pi * K / k
                * ((k * Real.cos (k * sigma) + z * Real.sin (k * sigma)) / (z ^ 2 + k ^ 2))) := by
  have hzk : z ^ 2 + k ^ 2 ≠ 0 := by positivity
  have hHS := baxter_wiener_hopf_factorization eta sigma rho k hsigma hk heta heta_def
  rw [hsplit, radial_fourier_cMSAtail hz hsigma,
    msaBaxter_cos_transform, msaBaxter_sin_transform,
    msa_lhs_split _ _ _ _ D, msa_exp_sq_modulus hzk, hHS]
  constructor <;> intro h <;> linarith

/-- Consistency: with no Yukawa (`K = 0`, `D = 0`) the required core correction is `0`, i.e. the
reduction contains the hard-sphere factorization rather than merely resembling it. -/
theorem msaexact1_core_at_zero_coupling
    (eta sigma rho z k cCore chatMSA : ℝ)
    (hsigma : 0 < sigma) (hk : k ≠ 0) (hz : 0 < z)
    (heta : eta < 1) (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) (hrho : rho ≠ 0)
    (hsplit : chatMSA = radial_fourier (c_HS eta sigma) k + cCore
        + radial_fourier (cMSAtail 0 z sigma) k) :
    (1 - (∫ r in (0 : ℝ)..sigma, msaBaxterFn eta sigma rho z 0 r * Real.cos (k * r))) ^ 2
        + (∫ r in (0 : ℝ)..sigma, msaBaxterFn eta sigma rho z 0 r * Real.sin (k * r)) ^ 2
        = 1 - rho * chatMSA
      ↔ cCore = 0 := by
  rw [msaexact1_iff_core eta sigma rho z 0 0 k cCore chatMSA hsigma hk hz heta heta_def hsplit]
  constructor
  · intro h
    have : rho * cCore = 0 := by rw [h]; ring
    exact (mul_eq_zero.mp this).resolve_left hrho
  · intro h; rw [h]; ring

end FMSA.MSAExact
