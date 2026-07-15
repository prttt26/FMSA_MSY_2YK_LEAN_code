/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib

/-!
# Task Y1.2 — outer MSA Yukawa DCF Laplace transform ([LN] Eq. 34/46)

Under the MSA closure the outside-core first-order DCF is the bare Yukawa tail
`c^{(1)}_{ij}(r) = βR_{ij}ε_{ij} e^{−z_{ij}(r−R_{ij})}/r` (`r > R_{ij}`, [LN] Eq. 34). Its half-line
Fourier/Laplace transform is ([LN] Eq. 46)
```
{U₁(k)}_{ij} = 2π√(ρ_iρ_j) ∫_{R}^∞ r·c^{(1)}_{ij}(r) e^{−ikr} dr
            = K_{ij} e^{−ikR_{ij}} / (ik + z_{ij}),
```
with the Yukawa coupling `K_{ij} = 2π√(ρ_iρ_j) R_{ij} β ε_{ij}` (Eq. 36). The factor `r` cancels
the `1/r` of the tail, leaving `βR_{ij}ε_{ij} e^{−z(r−R)}`, so the whole content is one improper
complex-exponential integral. `U₁` has a **simple pole at `ik = −z`** (i.e. Laplace `s = z`), the
Yukawa inverse-range — the pole the residue derivation (Y1.4) closes the contour on.

## Results

* `integral_Ioi_cexp` — `∫_{Ioi R} e^{c·r} dr = −e^{c·R}/c` for `Re c < 0` (FTC on `Ioi` via
  `integral_Ioi_of_hasDerivAt_of_tendsto`). Reusable.
* `outerDCF_transform` — [LN] Eq. 46: `∫_{Ioi R} A e^{−z(r−R)} e^{−ikr} dr = A e^{−ikR}/(ik+z)` for
  `z > 0`. With `A = βRε` (and the `2π√(ρρ)` prefactor absorbed into `K`) this is `U₁`.

Status: ✓ DONE (2026-07-15), axiom-clean.
-/

set_option linter.style.longLine false
set_option linter.style.whitespace false

open MeasureTheory Complex Filter Topology

namespace FMSA.OuterDCF

/-- `∫_{Ioi R} e^{c·r} dr = −e^{c·R}/c` for `Re c < 0` (improper integral of a decaying complex
exponential; FTC via `integral_Ioi_of_hasDerivAt_of_tendsto`, antiderivative `e^{c·r}/c`). -/
theorem integral_Ioi_cexp {c : ℂ} (hc : c.re < 0) (R : ℝ) :
    ∫ r in Set.Ioi R, Complex.exp (c * r) = -Complex.exp (c * R) / c := by
  have hc0 : c ≠ 0 := fun h => by simp [h] at hc
  have hlin : ∀ r : ℝ, HasDerivAt (fun x : ℝ => c * (x : ℂ)) c r := fun r => by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := r)).const_mul c)
  have hderiv : ∀ r ∈ Set.Ioi R, HasDerivAt (fun x : ℝ => Complex.exp (c * x) / c)
      (Complex.exp (c * r)) r := by
    intro r _
    simpa [mul_div_assoc, div_self hc0] using ((hlin r).cexp).div_const c
  have hcont : ContinuousWithinAt (fun x : ℝ => Complex.exp (c * x) / c) (Set.Ici R) R :=
    (by fun_prop : Continuous fun x : ℝ => Complex.exp (c * x) / c).continuousWithinAt
  have hatBot : Tendsto (fun x : ℝ => c.re * x) atTop atBot := by
    have h1 : Tendsto (fun x : ℝ => -c.re * x) atTop atTop :=
      Filter.Tendsto.const_mul_atTop (by linarith) tendsto_id
    have h2 := tendsto_neg_atTop_atBot.comp h1
    simp only [Function.comp_def, neg_mul, neg_neg] at h2
    exact h2
  have hint : IntegrableOn (fun r : ℝ => Complex.exp (c * r)) (Set.Ioi R) := by
    apply Integrable.mono' (integrableOn_exp_mul_Ioi hc R)
      ((by fun_prop : Continuous fun r : ℝ => Complex.exp (c * ↑r)).aestronglyMeasurable.restrict)
    filter_upwards with r
    rw [Complex.norm_exp]; simp [Complex.mul_re]
  have htendsto : Tendsto (fun x : ℝ => Complex.exp (c * x) / c) atTop (𝓝 0) := by
    have hnorm0 : Tendsto (fun x : ℝ => Complex.exp (c * x)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have he : (fun x : ℝ => ‖Complex.exp (c * ↑x)‖) = fun x => Real.exp (c.re * x) := by
        ext x; rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re]
      rw [he]; exact Real.tendsto_exp_atBot.comp hatBot
    simpa using hnorm0.div_const c
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint htendsto]; ring

/-- **Y1.2 — outer MSA Yukawa DCF Laplace transform** ([LN] Eq. 46).  For `z > 0`,
`∫_{Ioi R} A e^{−z(r−R)} e^{−ikr} dr = A e^{−ikR}/(ik+z)` — a simple pole at `ik = −z`.  With
`A = βR_{ij}ε_{ij}` (and the `2π√(ρ_iρ_j)` prefactor giving `K_{ij}`) this is `{U₁(k)}_{ij}`. -/
theorem outerDCF_transform {z : ℝ} (hz : 0 < z) (k R : ℝ) (A : ℂ) :
    ∫ r in Set.Ioi R, A * Complex.exp (-(z:ℂ) * ((r:ℂ) - R)) * Complex.exp (-Complex.I * k * r)
      = A * Complex.exp (-Complex.I * k * R) / (Complex.I * k + z) := by
  have hcre : (-(↑z + Complex.I * ↑k) : ℂ).re < 0 := by
    simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im]; ring_nf; linarith
  have hcongr : ∀ r : ℝ,
      A * Complex.exp (-(z:ℂ) * ((r:ℂ) - R)) * Complex.exp (-Complex.I * k * r)
        = (A * Complex.exp ((z:ℂ) * R)) * Complex.exp (-(↑z + Complex.I * ↑k) * r) := by
    intro r
    have hexp : Complex.exp (-(z:ℂ) * ((r:ℂ) - R)) * Complex.exp (-Complex.I * ↑k * ↑r)
        = Complex.exp ((z:ℂ) * ↑R) * Complex.exp (-(↑z + Complex.I * ↑k) * ↑r) := by
      rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
    calc A * Complex.exp (-(z:ℂ) * ((r:ℂ) - R)) * Complex.exp (-Complex.I * ↑k * ↑r)
        = A * (Complex.exp (-(z:ℂ) * ((r:ℂ) - R)) * Complex.exp (-Complex.I * ↑k * ↑r)) := by ring
      _ = A * (Complex.exp ((z:ℂ) * ↑R) * Complex.exp (-(↑z + Complex.I * ↑k) * ↑r)) := by rw [hexp]
      _ = (A * Complex.exp ((z:ℂ) * R)) * Complex.exp (-(↑z + Complex.I * ↑k) * ↑r) := by ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun r _ => hcongr r), integral_const_mul,
      integral_Ioi_cexp hcre]
  have key : Complex.exp ((z:ℂ) * ↑R) * Complex.exp (-(↑z + Complex.I * ↑k) * ↑R)
      = Complex.exp (-Complex.I * ↑k * ↑R) := by rw [← Complex.exp_add]; congr 1; ring
  rw [neg_div_neg_eq, ← mul_div_assoc, mul_assoc A, key, add_comm (↑z : ℂ) (Complex.I * ↑k)]

end FMSA.OuterDCF
