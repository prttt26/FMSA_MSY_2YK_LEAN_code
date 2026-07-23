/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HardSphere.OzFixedPtHExplicit
import LeanCode.HardSphere.OzFixedPtHExplicitFinal
import LeanCode.HardSphere.BaxterWienerHopfComplex

/-!
# Task OZFIX.11 — algebraic collapse for `r ≥ 2σ` (the per-pole half of `hcollapse`)

Proves `OZFIX.6`'s algebraic-collapse identity
`oz_forcing(r) + oz_linear_op[h_explicit](r) = h_explicit(r)` **for `2σ ≤ r`**, unconditionally
(no `sorry`, no new axiom, no contour machinery) — the tractable half of `OZFIX.8`'s `hcollapse`
hypothesis. On this region `oz_forcing = 0` (its indicator `r < σ+t` never fires for `t ≤ σ`) and
`max(r-t,σ) = r-t` throughout, so `OZFIX.5`'s outer-integral form collapses **per pole**:

* the `t`-integral of each pole's `Hterm` difference closes to
  `residue_term(r,k)·Chat_complex(k)/(2π)` — pure `Chat_F`/`Chat_J` moment algebra
  (`integral_Chat_poly_exp_pair`, `Chat_F_neg_sub_eq`), and
* the collapse factor is `ρ·Chat_complex(k_n) = 1` at every pole
  (`rho_mul_Chat_complex_eq_one_of_G_zero`): `G_baxter(k_n) = 0` gives `1 - Q̂(k_n) = 0`
  (`Qhat_pole_iff_G_baxter_zero`), and the complex Wiener–Hopf factorization
  `(1-Q̂(k))(1-Q̂(-k)) = 1 - ρĈ(k)` (`baxter_wiener_hopf_complex`, `OZFIX.2`) then forces
  `1 - ρĈ(k_n) = 0`. The mirror pole `-conj(k_n)` is a `G_baxter` zero too
  (`G_baxter_zero_mirror`), so the pole+mirror pair sums to exactly
  `h_explicit_term(n)(r)/(2πρ)` (`integral_Chat_poly_mul_Hterm_pair`).

The outer `t`-integral is interchanged with the pole sum by series dominated convergence
(`intervalIntegral.hasSum_integral_of_dominated_convergence`), powered by the uniform
`y ≥ σ`-valid summable bound `Hterm_uniform_summable_bound_of_pole_family` (`OZFIX.4`) — valid here
since both sample points satisfy `r+t ≥ r ≥ 2σ ≥ σ` and `r-t ≥ r-σ ≥ σ` (including the closed
endpoints `t = σ`, `r = 2σ`). `OZFIX.5`'s `hint` hypothesis (the open `σ`-boundary integrability
gap) is **vacuous** on this region (`r ≤ σ+t` with `t < σ` would force `r < 2σ`), and its
`hint1`/`hint2` side conditions are discharged outright — so the result carries no `hint`-family
hypothesis at all.

Numerically validated first (project discipline, `ozfix11_stage_check.py`, scratch):
`ρ·Ĉ(k_n) = 1` to ~1e-14 at poles and mirrors; the per-pole `t`-integral identity to ~1e-13
(η=0.3, σ=1, r ∈ {2.0, 2.5, 3.0}, n ∈ {0, 3, 8}); end-to-end aggregate to quadrature tolerance.

**New hypotheses** relative to `oz_h_eq_spliced_h_explicit`'s current pack: the physical coupling
`heta_def : eta = πρσ³/6` (consumed by `baxter_wiener_hopf_complex`) and `hkfam_ne` (already
required by `OZFIX.5`).

The complementary region `σ ≤ r < 2σ` (where `oz_forcing ≠ 0` and the collapse is genuinely
whole-series, Route B `OZFIX.12`) and the `r = σ` endpoint (`OZFIX.13`) are follow-on tasks; the
final `hcollapse` discharge composes this theorem with those via `le_or_lt (2*sigma) r`.

**Status:** ✓ DONE, no `sorry`/new axiom; `#print axioms` = standard three.
-/

open MeasureTheory Set Real intervalIntegral Filter Topology

namespace FMSA.HardSphere

noncomputable section

/-- **`oz_forcing` vanishes for `2σ ≤ r`**: the indicator `r < σ+t` never fires for `t ≤ σ`. -/
theorem oz_forcing_eq_zero_of_two_sigma_le {eta sigma rho r : ℝ} (hsigma : 0 < sigma)
    (hr : 2 * sigma ≤ r) : oz_forcing eta sigma rho r = 0 := by
  have hrpos : 0 < r := by linarith
  unfold oz_forcing
  rw [if_neg (not_le.mpr hrpos)]
  have hEq : Set.EqOn
      (fun t => t * c_HS eta sigma t * (sigma ^ 2 - (r - t) ^ 2) *
        if r < sigma + t then (1 : ℝ) else 0)
      (fun _ => (0 : ℝ)) (Set.uIoo 0 sigma) := by
    intro t ht
    rw [Set.uIoo_of_le hsigma.le] at ht
    have hind : ¬ (r < sigma + t) := not_lt.mpr (by linarith [ht.2])
    simp [hind]
  rw [intervalIntegral.integral_congr_uIoo hEq, intervalIntegral.integral_zero, mul_zero]

/-- Explicit sup bound for `Chat_poly` on `[0,σ]` — the `t`-independent constant for the
dominated-convergence interchange. -/
theorem Chat_poly_abs_bound (eta sigma : ℝ) (hsigma : 0 < sigma) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ t ∈ Set.Icc (0 : ℝ) sigma, |Chat_poly eta sigma t| ≤ P := by
  refine ⟨|py_a0 eta| * sigma + |py_a1 eta / sigma| * sigma ^ 2 +
    |py_a3 eta / sigma ^ 3| * sigma ^ 4, by positivity, ?_⟩
  intro t ht
  unfold Chat_poly
  rw [abs_neg]
  have h0 := ht.1
  have h1 := ht.2
  calc |py_a0 eta * t + py_a1 eta / sigma * t ^ 2 + py_a3 eta / sigma ^ 3 * t ^ 4|
      ≤ |py_a0 eta * t + py_a1 eta / sigma * t ^ 2| + |py_a3 eta / sigma ^ 3 * t ^ 4| :=
        abs_add_le _ _
    _ ≤ |py_a0 eta * t| + |py_a1 eta / sigma * t ^ 2| + |py_a3 eta / sigma ^ 3 * t ^ 4| := by
        linarith [abs_add_le (py_a0 eta * t) (py_a1 eta / sigma * t ^ 2)]
    _ = |py_a0 eta| * |t| + |py_a1 eta / sigma| * |t ^ 2| + |py_a3 eta / sigma ^ 3| * |t ^ 4| := by
        rw [abs_mul, abs_mul, abs_mul]
    _ ≤ |py_a0 eta| * sigma + |py_a1 eta / sigma| * sigma ^ 2 +
          |py_a3 eta / sigma ^ 3| * sigma ^ 4 := by
        rw [abs_of_nonneg h0, abs_of_nonneg (by positivity : (0:ℝ) ≤ t ^ 2),
          abs_of_nonneg (by positivity : (0:ℝ) ≤ t ^ 4)]
        gcongr

/-- `Hterm`'s series is summable at every `y ≥ σ` — packaging of
`Hterm_uniform_summable_bound_of_pole_family` (`OZFIX.4`). -/
theorem Hterm_summable_of_pole_family {eta sigma rho : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (hrho : 0 < rho)
    {kfam : ℕ → ℂ} {c d : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hkfam_zero : ∀ n, G_baxter eta sigma rho (kfam n) = 0)
    (hkfam_im : ∀ n, 0 ≤ (kfam n).im)
    (hkfam_re : ∀ n : ℕ, c * (n : ℝ) + d ≤ ‖kfam n‖)
    {y : ℝ} (hy : sigma ≤ y) :
    Summable (fun n => Hterm eta sigma rho kfam n y) := by
  obtain ⟨u, hu, hub⟩ := Hterm_uniform_summable_bound_of_pole_family heta0 heta1 hsigma hrho hc hd
    hkfam_zero hkfam_im hkfam_re
  exact Summable.of_norm_bounded hu (fun n => hub n hy)

/-- **The collapse factor: `ρ·Ĉ(k) = 1` at every `G_baxter` zero** — `Qhat_pole_iff_G_baxter_zero`
turns the zero into `1 - Q̂(k) = 0`, and the complex Wiener–Hopf factorization (`OZFIX.2`) then
forces `1 - ρĈ(k) = 0`. This is the entire mathematical content of the `r ≥ 2σ` collapse. -/
theorem rho_mul_Chat_complex_eq_one_of_G_zero {eta sigma rho : ℝ} (hsigma : 0 < sigma)
    (heta1 : eta < 1) (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6)
    {k : ℂ} (hk : k ≠ 0) (hzero : G_baxter eta sigma rho k = 0) :
    (rho : ℂ) * Chat_complex eta sigma k = 1 := by
  have h1 : 1 - Qhat_complex eta sigma rho k = 0 :=
    (Qhat_pole_iff_G_baxter_zero eta sigma rho hsigma hk).mpr hzero
  have h2 := baxter_wiener_hopf_complex hsigma heta1 heta_def hk
  rw [h1, zero_mul] at h2
  linear_combination h2

/-- The exponential-pair `t`-moment: `∫₀^σ Chat_poly(t)·(e^{ik(r+t)} - e^{ik(r-t)}) dt =
e^{ikr}·(Chat_F(-k) - Chat_F(k))` — the `r`-dependent phase factors out and the two
`t`-exponentials are `Chat_F`'s own integrand at `∓k`. -/
theorem integral_Chat_poly_exp_pair (eta sigma : ℝ) (k : ℂ) (r : ℝ) :
    ∫ t in (0:ℝ)..sigma, (Chat_poly eta sigma t : ℂ) *
        (Complex.exp (Complex.I * k * ((r + t : ℝ) : ℂ)) -
          Complex.exp (Complex.I * k * ((r - t : ℝ) : ℂ))) =
      Complex.exp (Complex.I * k * (r : ℂ)) *
        (Chat_F eta sigma (-k) - Chat_F eta sigma k) := by
  have hcongr : ∀ t ∈ Set.uIcc (0:ℝ) sigma,
      (Chat_poly eta sigma t : ℂ) *
        (Complex.exp (Complex.I * k * ((r + t : ℝ) : ℂ)) -
          Complex.exp (Complex.I * k * ((r - t : ℝ) : ℂ))) =
      Complex.exp (Complex.I * k * (r:ℂ)) *
          ((Chat_poly eta sigma t : ℂ) * Complex.exp (-Complex.I * -k * (t:ℂ))) -
        Complex.exp (Complex.I * k * (r:ℂ)) *
          ((Chat_poly eta sigma t : ℂ) * Complex.exp (-Complex.I * k * (t:ℂ))) := by
    intro t _
    have h1 : Complex.I * k * ((r + t : ℝ) : ℂ) =
        Complex.I * k * (r:ℂ) + -Complex.I * -k * (t:ℂ) := by push_cast; ring
    have h2 : Complex.I * k * ((r - t : ℝ) : ℂ) =
        Complex.I * k * (r:ℂ) + -Complex.I * k * (t:ℂ) := by push_cast; ring
    rw [h1, h2, Complex.exp_add, Complex.exp_add]
    ring
  have hi1 : IntervalIntegrable (fun t : ℝ => Complex.exp (Complex.I * k * (r:ℂ)) *
      ((Chat_poly eta sigma t : ℂ) * Complex.exp (-Complex.I * -k * (t:ℂ))))
      MeasureTheory.volume 0 sigma := by
    apply Continuous.intervalIntegrable
    exact continuous_const.mul ((Complex.continuous_ofReal.comp
      (Chat_poly_continuous eta sigma)).mul (Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal)))
  have hi2 : IntervalIntegrable (fun t : ℝ => Complex.exp (Complex.I * k * (r:ℂ)) *
      ((Chat_poly eta sigma t : ℂ) * Complex.exp (-Complex.I * k * (t:ℂ))))
      MeasureTheory.volume 0 sigma := by
    apply Continuous.intervalIntegrable
    exact continuous_const.mul ((Complex.continuous_ofReal.comp
      (Chat_poly_continuous eta sigma)).mul (Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal)))
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_sub hi1 hi2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  unfold Chat_F
  ring

/-- `Chat_F(-k) - Chat_F(k) = ik·Ĉ(k)/(2π)` — unfolding `Chat_complex = (4π/k)·Chat_J` and
`Chat_J = (Chat_F(-k) - Chat_F(k))/(2i)`. -/
theorem Chat_F_neg_sub_eq {eta sigma : ℝ} {k : ℂ} (hk : k ≠ 0) :
    Chat_F eta sigma (-k) - Chat_F eta sigma k =
      Complex.I * k * Chat_complex eta sigma k / (2 * (Real.pi : ℂ)) := by
  have hpi : ((Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  unfold Chat_complex Chat_J
  field_simp
  norm_num

/-- **Single-pole `t`-moment closed form**: the `t`-integral of one pole's `Hterm`-difference
integrand closes to `residue_term(r,k)·Ĉ(k)/(2π)` — no non-vanishing hypotheses beyond `k ≠ 0`
(the `residue_term = B·e^{ikx}` factorization is pure division-ring algebra). -/
theorem integral_Chat_poly_mul_residue_pair {eta sigma rho : ℝ} {k : ℂ} (hk : k ≠ 0) (r : ℝ) :
    ∫ t in (0:ℝ)..sigma, (Chat_poly eta sigma t : ℂ) *
        (residue_term eta sigma rho (r + t) k / (Complex.I * k) -
          residue_term eta sigma rho (r - t) k / (Complex.I * k)) =
      residue_term eta sigma rho r k * Chat_complex eta sigma k / (2 * (Real.pi : ℂ)) := by
  set B : ℂ := k ^ 7 * Chat_complex eta sigma k /
    (G_baxter eta sigma rho (-k) * G_baxter_deriv eta sigma rho k) with hBdef
  have hrt : ∀ x : ℝ, residue_term eta sigma rho x k =
      B * Complex.exp (Complex.I * k * (x:ℂ)) := by
    intro x
    rw [hBdef]
    unfold residue_term
    ring
  have hcongr : ∀ t ∈ Set.uIcc (0:ℝ) sigma,
      (Chat_poly eta sigma t : ℂ) *
        (residue_term eta sigma rho (r + t) k / (Complex.I * k) -
          residue_term eta sigma rho (r - t) k / (Complex.I * k)) =
      (B / (Complex.I * k)) * ((Chat_poly eta sigma t : ℂ) *
        (Complex.exp (Complex.I * k * ((r + t : ℝ) : ℂ)) -
          Complex.exp (Complex.I * k * ((r - t : ℝ) : ℂ)))) := by
    intro t _
    rw [hrt (r + t), hrt (r - t)]
    ring
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_const_mul,
    integral_Chat_poly_exp_pair, Chat_F_neg_sub_eq hk, hrt r]
  have hpi : ((Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  field_simp

/-- **Pole+mirror pair collapse**: the `t`-integral of pole `n`'s full `Hterm` difference equals
`h_explicit_term(n)(r)/(2πρ)` — the two `integral_Chat_poly_mul_residue_pair` closed forms with
`Ĉ = 1/ρ` substituted at both the pole (`hkfam_zero`) and its mirror (`G_baxter_zero_mirror`) via
`rho_mul_Chat_complex_eq_one_of_G_zero`. -/
theorem integral_Chat_poly_mul_Hterm_pair {eta sigma rho : ℝ} (hsigma : 0 < sigma)
    (heta1 : eta < 1) (hrho : 0 < rho)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6)
    {kfam : ℕ → ℂ} (hkfam_zero : ∀ n, G_baxter eta sigma rho (kfam n) = 0)
    (hkfam_ne : ∀ n, kfam n ≠ 0) (n : ℕ) (r : ℝ) :
    ∫ t in (0:ℝ)..sigma, (Chat_poly eta sigma t : ℂ) *
        (Hterm eta sigma rho kfam n (r + t) - Hterm eta sigma rho kfam n (r - t)) =
      h_explicit_term eta sigma rho r kfam n / ((2 * Real.pi * rho : ℝ) : ℂ) := by
  have hk : kfam n ≠ 0 := hkfam_ne n
  have hkm : -(starRingEnd ℂ) (kfam n) ≠ 0 := by
    simpa using hk
  have hzk : G_baxter eta sigma rho (kfam n) = 0 := hkfam_zero n
  have hzkm : G_baxter eta sigma rho (-(starRingEnd ℂ) (kfam n)) = 0 :=
    G_baxter_zero_mirror hzk
  have hcont_res : ∀ kk : ℂ, Continuous (fun s : ℝ => residue_term eta sigma rho s kk) := by
    intro kk
    unfold residue_term
    fun_prop
  have hi1 : IntervalIntegrable (fun t : ℝ => (Chat_poly eta sigma t : ℂ) *
      (residue_term eta sigma rho (r + t) (kfam n) / (Complex.I * kfam n) -
        residue_term eta sigma rho (r - t) (kfam n) / (Complex.I * kfam n)))
      MeasureTheory.volume 0 sigma := by
    apply Continuous.intervalIntegrable
    exact (Complex.continuous_ofReal.comp (Chat_poly_continuous eta sigma)).mul
      ((((hcont_res (kfam n)).comp (continuous_const.add continuous_id)).div_const _).sub
        (((hcont_res (kfam n)).comp (continuous_const.sub continuous_id)).div_const _))
  have hi2 : IntervalIntegrable (fun t : ℝ => (Chat_poly eta sigma t : ℂ) *
      (residue_term eta sigma rho (r + t) (-(starRingEnd ℂ) (kfam n)) /
          (Complex.I * -(starRingEnd ℂ) (kfam n)) -
        residue_term eta sigma rho (r - t) (-(starRingEnd ℂ) (kfam n)) /
          (Complex.I * -(starRingEnd ℂ) (kfam n))))
      MeasureTheory.volume 0 sigma := by
    apply Continuous.intervalIntegrable
    exact (Complex.continuous_ofReal.comp (Chat_poly_continuous eta sigma)).mul
      ((((hcont_res (-(starRingEnd ℂ) (kfam n))).comp
          (continuous_const.add continuous_id)).div_const _).sub
        (((hcont_res (-(starRingEnd ℂ) (kfam n))).comp
          (continuous_const.sub continuous_id)).div_const _))
  have hsplit : ∀ t ∈ Set.uIcc (0:ℝ) sigma,
      (Chat_poly eta sigma t : ℂ) *
        (Hterm eta sigma rho kfam n (r + t) - Hterm eta sigma rho kfam n (r - t)) =
      (Chat_poly eta sigma t : ℂ) *
        (residue_term eta sigma rho (r + t) (kfam n) / (Complex.I * kfam n) -
          residue_term eta sigma rho (r - t) (kfam n) / (Complex.I * kfam n)) +
      (Chat_poly eta sigma t : ℂ) *
        (residue_term eta sigma rho (r + t) (-(starRingEnd ℂ) (kfam n)) /
            (Complex.I * -(starRingEnd ℂ) (kfam n)) -
          residue_term eta sigma rho (r - t) (-(starRingEnd ℂ) (kfam n)) /
            (Complex.I * -(starRingEnd ℂ) (kfam n))) := by
    intro t _
    unfold Hterm
    ring
  rw [intervalIntegral.integral_congr hsplit, intervalIntegral.integral_add hi1 hi2,
    integral_Chat_poly_mul_residue_pair hk r, integral_Chat_poly_mul_residue_pair hkm r]
  have hC1 : Chat_complex eta sigma (kfam n) = ((rho : ℝ) : ℂ)⁻¹ :=
    eq_inv_of_mul_eq_one_right
      (rho_mul_Chat_complex_eq_one_of_G_zero hsigma heta1 heta_def hk hzk)
  have hC2 : Chat_complex eta sigma (-(starRingEnd ℂ) (kfam n)) = ((rho : ℝ) : ℂ)⁻¹ :=
    eq_inv_of_mul_eq_one_right
      (rho_mul_Chat_complex_eq_one_of_G_zero hsigma heta1 heta_def hkm hzkm)
  rw [hC1, hC2]
  unfold h_explicit_term
  have hrho' : ((rho : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hrho.ne'
  have hpi : ((Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp

/-- **The `t`-integral ↔ pole-sum interchange** (series dominated convergence): the outer
`t`-integral of the full `Hterm`-difference series is the sum of the per-pole `t`-integrals —
powered by the `y ≥ σ`-uniform summable bound (`OZFIX.4`), valid on all of `[0,σ]` since
`r ± t ≥ σ` for `2σ ≤ r` (including the closed endpoints). -/
theorem hasSum_integral_Chat_poly_Hterm {eta sigma rho : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (hrho : 0 < rho)
    {kfam : ℕ → ℂ} {c d : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hkfam_zero : ∀ n, G_baxter eta sigma rho (kfam n) = 0)
    (hkfam_im : ∀ n, 0 ≤ (kfam n).im)
    (hkfam_re : ∀ n : ℕ, c * (n : ℝ) + d ≤ ‖kfam n‖)
    {r : ℝ} (hr : 2 * sigma ≤ r) :
    HasSum
      (fun n => ∫ t in (0:ℝ)..sigma, (Chat_poly eta sigma t : ℂ) *
        (Hterm eta sigma rho kfam n (r + t) - Hterm eta sigma rho kfam n (r - t)))
      (∫ t in (0:ℝ)..sigma, (Chat_poly eta sigma t : ℂ) *
        ((∑' n, Hterm eta sigma rho kfam n (r + t)) -
          (∑' n, Hterm eta sigma rho kfam n (r - t)))) := by
  obtain ⟨u, hu, hub⟩ := Hterm_uniform_summable_bound_of_pole_family heta0 heta1 hsigma hrho hc hd
    hkfam_zero hkfam_im hkfam_re
  obtain ⟨P, hP0, hP⟩ := Chat_poly_abs_bound eta sigma hsigma
  have hcont_res : ∀ kk : ℂ, Continuous (fun s : ℝ => residue_term eta sigma rho s kk) := by
    intro kk
    unfold residue_term
    fun_prop
  have hcont_term : ∀ n : ℕ, Continuous (fun s : ℝ => Hterm eta sigma rho kfam n s) := by
    intro n
    unfold Hterm
    exact ((hcont_res (kfam n)).div_const _).add
      ((hcont_res (-(starRingEnd ℂ) (kfam n))).div_const _)
  have hFcont : ∀ n : ℕ, Continuous (fun t : ℝ => (Chat_poly eta sigma t : ℂ) *
      (Hterm eta sigma rho kfam n (r + t) - Hterm eta sigma rho kfam n (r - t))) := by
    intro n
    exact (Complex.continuous_ofReal.comp (Chat_poly_continuous eta sigma)).mul
      (((hcont_term n).comp (continuous_const.add continuous_id)).sub
        ((hcont_term n).comp (continuous_const.sub continuous_id)))
  have hsummableP : ∀ {y : ℝ}, sigma ≤ y → Summable (fun n => Hterm eta sigma rho kfam n y) :=
    fun {y} hy => Summable.of_norm_bounded hu (fun n => hub n hy)
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (bound := fun n _ => P * (2 * u n)) (fun n => (hFcont n).aestronglyMeasurable) ?_ ?_ ?_ ?_
  · -- h_bound
    intro n
    refine Filter.Eventually.of_forall fun t ht => ?_
    rw [Set.uIoc_of_le hsigma.le] at ht
    have hyp : sigma ≤ r + t := by linarith [ht.1]
    have hym : sigma ≤ r - t := by linarith [ht.2]
    calc ‖(Chat_poly eta sigma t : ℂ) *
        (Hterm eta sigma rho kfam n (r + t) - Hterm eta sigma rho kfam n (r - t))‖
        = |Chat_poly eta sigma t| *
          ‖Hterm eta sigma rho kfam n (r + t) - Hterm eta sigma rho kfam n (r - t)‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ P * (u n + u n) :=
          mul_le_mul (hP t ⟨ht.1.le, ht.2⟩)
            ((norm_sub_le _ _).trans (add_le_add (hub n hyp) (hub n hym)))
            (norm_nonneg _) hP0
      _ = P * (2 * u n) := by ring
  · -- bound_summable
    exact Filter.Eventually.of_forall fun t _ => (hu.mul_left 2).mul_left P
  · -- bound_integrable
    exact intervalIntegral.intervalIntegrable_const
  · -- h_lim
    refine Filter.Eventually.of_forall fun t ht => ?_
    rw [Set.uIoc_of_le hsigma.le] at ht
    have hyp : sigma ≤ r + t := by linarith [ht.1]
    have hym : sigma ≤ r - t := by linarith [ht.2]
    exact ((hsummableP hyp).hasSum.sub (hsummableP hym).hasSum).mul_left _

/-- **`OZFIX.11` main theorem: the algebraic collapse for `2σ ≤ r`** — the tractable half of
`OZFIX.8`'s `hcollapse` hypothesis, unconditional (no `hint`-family hypothesis, no new axiom).
The conclusion is literally `hcollapse`'s body at this `r`, so the eventual full discharge
composes this with the `σ ≤ r < 2σ` result (`OZFIX.12`/`OZFIX.13`) via `le_or_lt`. -/
theorem oz_collapse_of_two_sigma_le {eta sigma rho : ℝ} (hsigma : 0 < sigma)
    (heta0 : 0 < eta) (heta1 : eta < 1) (hrho : 0 < rho)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6)
    {kfam : ℕ → ℂ} {c d : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hkfam_zero : ∀ n, G_baxter eta sigma rho (kfam n) = 0)
    (hkfam_im : ∀ n, 0 ≤ (kfam n).im)
    (hkfam_re : ∀ n : ℕ, c * (n : ℝ) + d ≤ ‖kfam n‖)
    (hkfam_ne : ∀ n, kfam n ≠ 0)
    {r : ℝ} (hr : 2 * sigma ≤ r) :
    oz_forcing eta sigma rho r +
        oz_linear_op eta sigma rho (fun s => h_explicit eta sigma rho s kfam) r =
      h_explicit eta sigma rho r kfam := by
  have hr' : sigma ≤ r := by linarith
  have hrpos : 0 < r := by linarith
  -- shared summability/continuity infrastructure
  obtain ⟨u, hu, hub⟩ := Hterm_uniform_summable_bound_of_pole_family heta0 heta1 hsigma hrho hc hd
    hkfam_zero hkfam_im hkfam_re
  have hcont_res : ∀ kk : ℂ, Continuous (fun s : ℝ => residue_term eta sigma rho s kk) := by
    intro kk
    unfold residue_term
    fun_prop
  have hcont_term : ∀ n : ℕ, Continuous (fun s : ℝ => Hterm eta sigma rho kfam n s) := by
    intro n
    unfold Hterm
    exact ((hcont_res (kfam n)).div_const _).add
      ((hcont_res (-(starRingEnd ℂ) (kfam n))).div_const _)
  have hcontS : ContinuousOn (fun y => ∑' n, Hterm eta sigma rho kfam n y) (Set.Ici sigma) :=
    continuousOn_tsum (fun n => (hcont_term n).continuousOn) hu (fun n y hy => hub n hy)
  have hmapsP : Set.MapsTo (fun t : ℝ => r + t) (Set.uIcc 0 sigma) (Set.Ici sigma) := by
    intro t ht
    rw [Set.uIcc_of_le hsigma.le] at ht
    exact Set.mem_Ici.mpr (by linarith [ht.1])
  have hmapsM : Set.MapsTo (fun t : ℝ => r - t) (Set.uIcc 0 sigma) (Set.Ici sigma) := by
    intro t ht
    rw [Set.uIcc_of_le hsigma.le] at ht
    exact Set.mem_Ici.mpr (by linarith [ht.2])
  have hΦcont : ContinuousOn (fun t : ℝ => (Chat_poly eta sigma t : ℂ) *
      ((∑' n, Hterm eta sigma rho kfam n (r + t)) -
        (∑' n, Hterm eta sigma rho kfam n (r - t)))) (Set.uIcc 0 sigma) := by
    apply ContinuousOn.mul
    · exact (Complex.continuous_ofReal.comp (Chat_poly_continuous eta sigma)).continuousOn
    · apply ContinuousOn.sub
      · have := hcontS.comp (((by fun_prop : Continuous fun t : ℝ => r + t)).continuousOn
          (s := Set.uIcc (0:ℝ) sigma)) hmapsP
        simpa [Function.comp_def] using this
      · have := hcontS.comp (((by fun_prop : Continuous fun t : ℝ => r - t)).continuousOn
          (s := Set.uIcc (0:ℝ) sigma)) hmapsM
        simpa [Function.comp_def] using this
  have hΦint : IntervalIntegrable (fun t : ℝ => (Chat_poly eta sigma t : ℂ) *
      ((∑' n, Hterm eta sigma rho kfam n (r + t)) -
        (∑' n, Hterm eta sigma rho kfam n (r - t)))) MeasureTheory.volume 0 sigma :=
    hΦcont.intervalIntegrable
  -- the three side conditions of the `OZFIX.5` assembly theorem
  have hint : ∀ t ∈ Set.Ioo (0:ℝ) sigma, r ≤ sigma + t → IntervalIntegrable
      (fun s => ∑' n, h_explicit_term eta sigma rho s kfam n)
      MeasureTheory.volume sigma (r + t) := by
    intro t ht hle
    exact absurd hle (not_le.mpr (by linarith [ht.2]))
  have hint1 : IntervalIntegrable
      (fun t => t * c_HS eta sigma t * (sigma ^ 2 - (r - t) ^ 2) *
        if r < sigma + t then (1 : ℝ) else 0) MeasureTheory.volume 0 sigma := by
    have hEq : Set.EqOn
        (fun t => t * c_HS eta sigma t * (sigma ^ 2 - (r - t) ^ 2) *
          if r < sigma + t then (1 : ℝ) else 0)
        (fun _ => (0 : ℝ)) (Set.uIoo 0 sigma) := by
      intro t ht
      rw [Set.uIoo_of_le hsigma.le] at ht
      have hind : ¬ (r < sigma + t) := not_lt.mpr (by linarith [ht.2])
      simp [hind]
    exact (intervalIntegrable_congr_uIoo hEq).mpr intervalIntegral.intervalIntegrable_const
  have hbridge : Set.EqOn
      (fun t => t * c_HS eta sigma t *
        ∫ s in (max (r - t) sigma)..(r + t), s * h_explicit eta sigma rho s kfam)
      (fun t => (1 / (2 * Real.pi)) * ((Chat_poly eta sigma t : ℂ) *
        ((∑' n, Hterm eta sigma rho kfam n (r + t)) -
          (∑' n, Hterm eta sigma rho kfam n (r - t)))).re)
      (Set.uIoo 0 sigma) := by
    intro t ht
    rw [Set.uIoo_of_le hsigma.le] at ht
    have hmax : max (r - t) sigma = r - t := max_eq_left (by linarith [ht.2])
    have hin := inner_h_explicit_integral_bridge heta0 heta1 hsigma hrho hc hd hkfam_zero
      hkfam_im hkfam_re hkfam_ne (Set.mem_Ioo.mpr ht) hr'
      (fun hle => absurd hle (not_le.mpr (by linarith [ht.2])))
    dsimp only
    rw [hin, hmax, ← Chat_poly_eq_mul_c_HS ht.2, Complex.re_ofReal_mul]
    ring
  have hint2 : IntervalIntegrable
      (fun t => t * c_HS eta sigma t *
        ∫ s in (max (r - t) sigma)..(r + t), s * h_explicit eta sigma rho s kfam)
      MeasureTheory.volume 0 sigma := by
    refine (intervalIntegrable_congr_uIoo hbridge).mpr ?_
    apply ContinuousOn.intervalIntegrable
    exact continuousOn_const.mul (Complex.continuous_re.comp_continuousOn hΦcont)
  -- step 1: the `OZFIX.5` assembly form
  rw [oz_forcing_add_linear_op_h_explicit_eq_outer_integral hsigma heta0 heta1 hrho hc hd
    hkfam_zero hkfam_im hkfam_re hkfam_ne hr' hint1 hint2 hint]
  -- step 2: collapse the assembly integrand to the ℂ-closed form on `(0,σ)`
  have h1 : ∫ t in (0:ℝ)..sigma,
      (t * c_HS eta sigma t *
          (-(1 / 2) * (sigma ^ 2 - (r - t) ^ 2) * (if r < sigma + t then (1 : ℝ) else 0)) +
        t * c_HS eta sigma t *
          ((1 / (2 * Real.pi)) *
            ((∑' n, Hterm eta sigma rho kfam n (r + t)) -
              (∑' n, Hterm eta sigma rho kfam n (max (r - t) sigma))).re)) =
      (1 / (2 * Real.pi)) * ∫ t in (0:ℝ)..sigma, ((Chat_poly eta sigma t : ℂ) *
        ((∑' n, Hterm eta sigma rho kfam n (r + t)) -
          (∑' n, Hterm eta sigma rho kfam n (r - t)))).re := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_uIoo
    intro t ht
    rw [Set.uIoo_of_le hsigma.le] at ht
    have hif : (if r < sigma + t then (1:ℝ) else 0) = 0 :=
      if_neg (not_lt.mpr (by linarith [ht.2]))
    have hmax : max (r - t) sigma = r - t := max_eq_left (by linarith [ht.2])
    dsimp only
    rw [hif, hmax, ← Chat_poly_eq_mul_c_HS ht.2, Complex.re_ofReal_mul]
    ring
  -- step 3: commute `Re` past the interval integral
  have h2 : (∫ t in (0:ℝ)..sigma, ((Chat_poly eta sigma t : ℂ) *
      ((∑' n, Hterm eta sigma rho kfam n (r + t)) -
        (∑' n, Hterm eta sigma rho kfam n (r - t)))).re) =
      (∫ t in (0:ℝ)..sigma, (Chat_poly eta sigma t : ℂ) *
        ((∑' n, Hterm eta sigma rho kfam n (r + t)) -
          (∑' n, Hterm eta sigma rho kfam n (r - t)))).re := by
    change (∫ t in (0:ℝ)..sigma, RCLike.re ((Chat_poly eta sigma t : ℂ) *
      ((∑' n, Hterm eta sigma rho kfam n (r + t)) -
        (∑' n, Hterm eta sigma rho kfam n (r - t))))) = _
    rw [intervalIntegral_re hΦint]
    rfl
  -- step 4: interchange, per-pole collapse, and resummation
  have h3 : (∫ t in (0:ℝ)..sigma, (Chat_poly eta sigma t : ℂ) *
      ((∑' n, Hterm eta sigma rho kfam n (r + t)) -
        (∑' n, Hterm eta sigma rho kfam n (r - t)))) =
      (∑' n, h_explicit_term eta sigma rho r kfam n) / ((2 * Real.pi * rho : ℝ) : ℂ) := by
    rw [← (hasSum_integral_Chat_poly_Hterm heta0 heta1 hsigma hrho hc hd hkfam_zero hkfam_im
      hkfam_re hr).tsum_eq]
    rw [tsum_congr (fun n => integral_Chat_poly_mul_Hterm_pair hsigma heta1 hrho heta_def
      hkfam_zero hkfam_ne n r)]
    exact tsum_div_const
  rw [h1, h2, h3, Complex.div_ofReal_re]
  -- step 5: final scalar normalization `(2πρ/r)·(1/2π)·(X/(2πρ)) = (1/(2πr))·X`
  unfold h_explicit
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-- **`OZFIX.8` with a strictly weaker collapse hypothesis** (the direct downstream unlock of
`OZFIX.11`): `oz_h` equals the spliced `h_explicit`/`(-1)` function conditional only on the
collapse identity **on `σ ≤ r < 2σ`** (`hcollapse_inner`, the still-open `OZFIX.12` region where
`oz_forcing ≠ 0`) plus `hcont_sigma` — the `r ≥ 2σ` half of the original `hcollapse` is now
supplied by `oz_collapse_of_two_sigma_le`. Adds `heta_def` and `hkfam_ne` to
`oz_h_eq_spliced_h_explicit`'s hypothesis pack (both consumed by the `r ≥ 2σ` proof). -/
theorem oz_h_eq_spliced_h_explicit_of_inner_collapse {eta sigma rho : ℝ} (hsigma : 0 < sigma)
    (heta0 : 0 < eta) (heta1 : eta < 1) (hrho : 0 < rho)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6)
    {kfam : ℕ → ℂ} {c d : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hkfam_zero : ∀ n, G_baxter eta sigma rho (kfam n) = 0)
    (hkfam_im : ∀ n, 0 ≤ (kfam n).im)
    (hkfam_re : ∀ n : ℕ, c * (n : ℝ) + d ≤ ‖kfam n‖)
    (hkfam_ne : ∀ n, kfam n ≠ 0)
    (hcollapse_inner : ∀ r, sigma ≤ r → r < 2 * sigma →
      oz_forcing eta sigma rho r +
        oz_linear_op eta sigma rho (fun s => h_explicit eta sigma rho s kfam) r =
      h_explicit eta sigma rho r kfam)
    (hcont_sigma : ContinuousWithinAt (fun r => h_explicit eta sigma rho r kfam)
      (Set.Ici sigma) sigma) :
    oz_h eta sigma rho =
      (fun r => if r < sigma then (-1 : ℝ) else h_explicit eta sigma rho r kfam) := by
  refine oz_h_eq_spliced_h_explicit hsigma heta0 heta1 hrho heta_def hc hd hkfam_zero hkfam_im
    hkfam_re ?_ hcont_sigma
  intro r hr
  rcases lt_or_ge r (2 * sigma) with h2 | h2
  · exact hcollapse_inner r hr h2
  · exact oz_collapse_of_two_sigma_le hsigma heta0 heta1 hrho heta_def hc hd hkfam_zero
      hkfam_im hkfam_re hkfam_ne h2

end

end FMSA.HardSphere
