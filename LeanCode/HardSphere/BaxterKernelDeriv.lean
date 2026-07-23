/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HardSphere.BaxterRealSpace

/-!
# Derivative of the Baxter renewal kernel `q0_poly`

Foundational bricks for **(★DIFF)**, the differentiated renewal equation
`ψ'(r) = baxterForcing'(r) + q0(0)·ψ(r) + ∫_σ^r q0'(r−t)·ψ(t)dt`, whose proof retires BOTH halves of
the split axiom `ozExterior_smooth_repr` / `ozExterior_deriv_integrable` (`OzExteriorSmooth.lean`).

## The two pieces, and why they differ at `σ`

`q0_poly = ρ·q'_py·phi1_real + ρ·q''_py·phi2_real` with
`phi1_real σ r = if r ≤ σ then r − σ else 0`, `phi2_real σ r = if r ≤ σ then (r−σ)²/2 else 0`.

* **`phi2_real` is differentiable EVERYWHERE, and its derivative is exactly `phi1_real`** — including
  at the contact point `r = σ`, where both one-sided derivatives vanish (`(r−σ) → 0` from the left,
  `0` from the right).  So `phi2_real` is `C¹` (though not `C²`).
* **`phi1_real` has a genuine kink at `σ`** (left slope `1`, right slope `0`), so it is differentiable
  only for `r ≠ σ`.

Hence `q0_poly` is differentiable exactly off `σ` — a single point, which is `volume`-null, so the
`∫_σ^r q0'(r−t)ψ(t)dt` term of (★DIFF) is unaffected, but the Leibniz step must use a
Lipschitz/dominated form rather than a naive "differentiate under the integral".
-/

open Set

namespace FMSA.HardSphere

noncomputable section

variable {sigma r : ℝ}

/-- **`phi2_real` is differentiable everywhere with derivative `phi1_real`.**  The interesting point
is `r = σ`: the left branch `(r−σ)²/2` has slope `r−σ → 0` and the right branch `0` has slope `0`, so
the two agree and `phi2_real` is differentiable there (unlike `phi1_real`). -/
theorem hasDerivAt_phi2_real (sigma r : ℝ) :
    HasDerivAt (phi2_real sigma) (phi1_real sigma r) r := by
  rcases lt_trichotomy r sigma with hr | hr | hr
  · -- `r < σ`: locally the quadratic branch
    have hbase : HasDerivAt (fun x : ℝ => (x - sigma) ^ 2 / 2) (r - sigma) r := by
      have h := ((hasDerivAt_id r).sub_const sigma).pow 2
      simpa using (h.div_const 2)
    refine hbase.congr_of_eventuallyEq ?_ |>.congr_deriv ?_
    · filter_upwards [Iio_mem_nhds hr] with x hx
      simp only [phi2_real, if_pos (le_of_lt (mem_Iio.mp hx))]
    · simp only [phi1_real, if_pos (le_of_lt hr)]
  · -- `r = σ`: glue the two one-sided derivatives, both `0`
    subst hr
    have hval : phi1_real r r = 0 := by simp [phi1_real]
    rw [hval]
    have hleft : HasDerivWithinAt (phi2_real r) 0 (Iic r) r := by
      have hbase : HasDerivAt (fun x : ℝ => (x - r) ^ 2 / 2) (0 : ℝ) r := by
        have h := ((hasDerivAt_id r).sub_const r).pow 2
        simpa using (h.div_const 2)
      refine (hbase.hasDerivWithinAt (s := Iic r)).congr (fun x hx => ?_) ?_
      · simp only [phi2_real, if_pos (mem_Iic.mp hx)]
      · simp only [phi2_real, if_pos (le_refl r)]
    have hright : HasDerivWithinAt (phi2_real r) 0 (Ici r) r := by
      refine (hasDerivWithinAt_const r (Ici r) (0 : ℝ)).congr (fun x hx => ?_) ?_
      · rcases eq_or_lt_of_le (mem_Ici.mp hx) with h | h
        · simp only [phi2_real, ← h, if_pos (le_refl r)]; ring
        · simp only [phi2_real, if_neg (not_le.mpr h)]
      · simp only [phi2_real, if_pos (le_refl r)]; ring
    have := hleft.union hright
    rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
  · -- `r > σ`: locally zero
    refine (hasDerivAt_const r (0 : ℝ)).congr_of_eventuallyEq ?_ |>.congr_deriv ?_
    · filter_upwards [Ioi_mem_nhds hr] with x hx
      simp only [phi2_real, if_neg (not_le.mpr (mem_Ioi.mp hx))]
    · simp only [phi1_real, if_neg (not_le.mpr hr)]

/-- **`phi1_real` is differentiable off the contact point**, with slope `1` inside and `0` outside.
At `r = σ` it genuinely fails (left slope `1`, right slope `0`). -/
theorem hasDerivAt_phi1_real_of_ne (sigma : ℝ) {r : ℝ} (hr : r ≠ sigma) :
    HasDerivAt (phi1_real sigma) (if r < sigma then (1 : ℝ) else 0) r := by
  rcases lt_or_gt_of_ne hr with hlt | hgt
  · refine ((hasDerivAt_id r).sub_const sigma).congr_of_eventuallyEq ?_ |>.congr_deriv ?_
    · filter_upwards [Iio_mem_nhds hlt] with x hx
      simp only [phi1_real, if_pos (le_of_lt (mem_Iio.mp hx)), id_eq]
    · simp only [if_pos hlt]
  · refine (hasDerivAt_const r (0 : ℝ)).congr_of_eventuallyEq ?_ |>.congr_deriv ?_
    · filter_upwards [Ioi_mem_nhds hgt] with x hx
      simp only [phi1_real, if_neg (not_le.mpr (mem_Ioi.mp hx))]
    · simp only [if_neg (not_lt.mpr (le_of_lt hgt))]

/-- The pointwise derivative of the Baxter renewal kernel `q0_poly` (valid off `r = σ`).
`= ρ·q'_py·1_{r<σ} + ρ·q''_py·phi1_real σ r`. -/
def q0PolyDeriv (eta sigma rho : ℝ) (r : ℝ) : ℝ :=
  rho * q_prime_py eta sigma * (if r < sigma then (1 : ℝ) else 0)
    + rho * q_doubleprime_py eta * phi1_real sigma r

/-- **Derivative of the renewal kernel, off the contact point.**  `q0_poly` is differentiable at
every `r ≠ σ` (the single exceptional point is `volume`-null, harmless inside (★DIFF)'s integral). -/
theorem hasDerivAt_q0_poly_of_ne {eta rho : ℝ} (sigma : ℝ) {r : ℝ} (hr : r ≠ sigma) :
    HasDerivAt (q0_poly eta sigma rho) (q0PolyDeriv eta sigma rho r) r := by
  have h1 : HasDerivAt (fun y : ℝ => rho * q_prime_py eta sigma * phi1_real sigma y)
      (rho * q_prime_py eta sigma * (if r < sigma then (1 : ℝ) else 0)) r :=
    (hasDerivAt_phi1_real_of_ne sigma hr).const_mul _
  have h2 : HasDerivAt (fun y : ℝ => rho * q_doubleprime_py eta * phi2_real sigma y)
      (rho * q_doubleprime_py eta * phi1_real sigma r) r :=
    (hasDerivAt_phi2_real sigma r).const_mul _
  exact h1.add h2

/-- `q0_poly` vanishes past the core, so its derivative does too (off `σ`). -/
theorem q0PolyDeriv_eq_zero_of_gt {eta rho : ℝ} (sigma : ℝ) {r : ℝ} (hr : sigma < r) :
    q0PolyDeriv eta sigma rho r = 0 := by
  simp only [q0PolyDeriv, if_neg (not_lt.mpr (le_of_lt hr)), phi1_real,
    if_neg (not_le.mpr hr), mul_zero, add_zero]

/-! ### Kernel properties feeding `MA.16`'s hypotheses (`Analysis/ConvolutionLeibniz.lean`)

`hasDerivAt_intervalIntegral_param` / `..._convolution` need: `K` continuous, `K` **a.e.**
differentiable with measurable derivative, and `K` Lipschitz on a compact.  The two closed forms
below make all of that routine. -/

/-- `phi1_real` in closed form: `min r σ − σ`.  (Both branches: `r ≤ σ ↦ r − σ`, `r > σ ↦ 0`.) -/
theorem phi1_real_eq_min_sub (sigma r : ℝ) : phi1_real sigma r = min r sigma - sigma := by
  rcases le_total r sigma with h | h
  · simp only [phi1_real, if_pos h, min_eq_left h]
  · rcases eq_or_lt_of_le h with heq | hlt
    · subst heq; simp only [phi1_real, if_pos (le_refl sigma), min_self]
    · simp only [phi1_real, if_neg (not_le.mpr hlt), min_eq_right (le_of_lt hlt), sub_self]

/-- `phi2_real` is exactly `phi1_real² / 2` — which is why it is `C¹` while `phi1_real` is not. -/
theorem phi2_real_eq_half_sq (sigma r : ℝ) :
    phi2_real sigma r = (phi1_real sigma r) ^ 2 / 2 := by
  rcases le_or_gt r sigma with h | h
  · simp only [phi2_real, phi1_real, if_pos h]
  · simp only [phi2_real, phi1_real, if_neg (not_le.mpr h)]; norm_num

/-- `phi1_real` is `1`-Lipschitz (it is `min · σ` shifted). -/
theorem lipschitzWith_phi1_real (sigma : ℝ) : LipschitzWith 1 (phi1_real sigma) := by
  have h : phi1_real sigma = (fun t : ℝ => t - sigma) ∘ (fun r : ℝ => min r sigma) := by
    funext r; simp [phi1_real_eq_min_sub, Function.comp]
  rw [h]
  have hsub : LipschitzWith 1 (fun t : ℝ => t - sigma) :=
    LipschitzWith.of_dist_le_mul (fun x y => by simp [Real.dist_eq])
  have hmin : LipschitzWith 1 (fun r : ℝ => min r sigma) := by
    simpa using LipschitzWith.id.min (LipschitzWith.const sigma)
  simpa using hsub.comp hmin

/-- The pointwise derivative of `q0_poly` is measurable (an `Iio`-indicator plus a continuous term). -/
theorem q0PolyDeriv_measurable (eta sigma rho : ℝ) :
    Measurable (q0PolyDeriv eta sigma rho) := by
  refine (measurable_const.mul ?_).add (measurable_const.mul ?_)
  · exact Measurable.ite measurableSet_Iio measurable_const measurable_const
  · exact (phi1_real_continuous sigma).measurable

/-- **`q0_poly` is a.e. differentiable** with derivative `q0PolyDeriv` — the exceptional set is the
single point `σ`, which is `volume`-null.  This is the exact shape `MA.16` asks for. -/
theorem hasDerivAt_q0_poly_ae (eta sigma rho : ℝ) :
    ∀ᵐ u, HasDerivAt (q0_poly eta sigma rho) (q0PolyDeriv eta sigma rho u) u := by
  have hne : ∀ᵐ (u : ℝ), u ≠ sigma := by
    rw [MeasureTheory.ae_iff]; simpa using MeasureTheory.measure_singleton sigma
  filter_upwards [hne] with u hu
  exact hasDerivAt_q0_poly_of_ne sigma hu

/-- `|phi1_real σ x| ≤ |x − σ|` (it is either `x − σ` or `0`). -/
theorem abs_phi1_real_le (sigma x : ℝ) : |phi1_real sigma x| ≤ |x - sigma| := by
  rcases le_or_gt x sigma with h | h
  · simp only [phi1_real, if_pos h, le_refl]
  · simp only [phi1_real, if_neg (not_le.mpr h), abs_zero]
    exact abs_nonneg _

/-- **`q0_poly` is Lipschitz on any set where `|x − σ|` is bounded** (in particular on any compact),
with the explicit constant `|ρq'| + |ρq''|·B`.  This is `MA.16`'s `hKlip` hypothesis.

Both summands are handled by the closed forms above: `phi1_real` is `1`-Lipschitz, and
`phi2_real = phi1_real²/2` gives `|phi2(x) − phi2(y)| ≤ B·|x − y|` via
`a² − b² = (a+b)(a−b)`. -/
theorem q0_poly_lipschitzOnWith {eta sigma rho : ℝ} {s : Set ℝ} {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x ∈ s, |x - sigma| ≤ B) :
    LipschitzOnWith
      (Real.nnabs (|rho * q_prime_py eta sigma| + |rho * q_doubleprime_py eta| * B))
      (q0_poly eta sigma rho) s := by
  have hCnn : (0:ℝ) ≤ |rho * q_prime_py eta sigma| + |rho * q_doubleprime_py eta| * B := by
    have := mul_nonneg (abs_nonneg (rho * q_doubleprime_py eta)) hB0
    linarith [abs_nonneg (rho * q_prime_py eta sigma)]
  refine LipschitzOnWith.of_dist_le_mul (fun x hx y hy => ?_)
  have hbx : |phi1_real sigma x| ≤ B := le_trans (abs_phi1_real_le sigma x) (hB x hx)
  have hby : |phi1_real sigma y| ≤ B := le_trans (abs_phi1_real_le sigma y) (hB y hy)
  -- `phi1` is 1-Lipschitz
  have h1 : |phi1_real sigma x - phi1_real sigma y| ≤ |x - y| := by
    have := (lipschitzWith_phi1_real sigma).dist_le_mul x y
    simpa [Real.dist_eq] using this
  -- `phi2 = phi1²/2` ⇒ Lipschitz with constant `B` on `s`
  have h2 : |phi2_real sigma x - phi2_real sigma y| ≤ B * |x - y| := by
    have hfac : phi2_real sigma x - phi2_real sigma y
        = (phi1_real sigma x + phi1_real sigma y) * (phi1_real sigma x - phi1_real sigma y) / 2 := by
      simp only [phi2_real_eq_half_sq]; ring
    rw [hfac, abs_div, abs_mul, abs_two]
    have hsum : |phi1_real sigma x + phi1_real sigma y| ≤ 2 * B := by
      calc |phi1_real sigma x + phi1_real sigma y|
          ≤ |phi1_real sigma x| + |phi1_real sigma y| := abs_add_le _ _
        _ ≤ B + B := add_le_add hbx hby
        _ = 2 * B := by ring
    have hprod : |phi1_real sigma x + phi1_real sigma y| * |phi1_real sigma x - phi1_real sigma y|
        ≤ (2 * B) * |x - y| :=
      mul_le_mul hsum h1 (abs_nonneg _) (by linarith)
    linarith
  -- assemble
  simp only [Real.dist_eq, q0_poly, Real.coe_nnabs, abs_of_nonneg hCnn]
  have hsplit : rho * q_prime_py eta sigma * phi1_real sigma x
        + rho * q_doubleprime_py eta * phi2_real sigma x
      - (rho * q_prime_py eta sigma * phi1_real sigma y
        + rho * q_doubleprime_py eta * phi2_real sigma y)
      = rho * q_prime_py eta sigma * (phi1_real sigma x - phi1_real sigma y)
        + rho * q_doubleprime_py eta * (phi2_real sigma x - phi2_real sigma y) := by ring
  rw [hsplit]
  calc |rho * q_prime_py eta sigma * (phi1_real sigma x - phi1_real sigma y)
        + rho * q_doubleprime_py eta * (phi2_real sigma x - phi2_real sigma y)|
      ≤ |rho * q_prime_py eta sigma * (phi1_real sigma x - phi1_real sigma y)|
        + |rho * q_doubleprime_py eta * (phi2_real sigma x - phi2_real sigma y)| := abs_add_le _ _
    _ = |rho * q_prime_py eta sigma| * |phi1_real sigma x - phi1_real sigma y|
        + |rho * q_doubleprime_py eta| * |phi2_real sigma x - phi2_real sigma y| := by
          simp only [abs_mul]
    _ ≤ |rho * q_prime_py eta sigma| * |x - y|
        + |rho * q_doubleprime_py eta| * (B * |x - y|) :=
          add_le_add (mul_le_mul_of_nonneg_left h1 (abs_nonneg _))
            (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))
    _ = (|rho * q_prime_py eta sigma| + |rho * q_doubleprime_py eta| * B) * |x - y| := by ring

end

end FMSA.HardSphere
