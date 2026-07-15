/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HardSphere.BaxterRealSpace
import LeanCode.HardSphere.RadialFourierCHS

/-!
# Task BAXTER.3 — Baxter's Wiener–Hopf factorization *(formerly Task OZ.12)*

`(1 - ρ·Q̂(k))·(1 - ρ·Q̂(-k)) = 1 - ρ·Ĉ_sine(k)`, where `Q̂` is the Fourier transform (at real `k`)
of `Q_old = q0_poly/ρ` — the *same* function `baxter_factorization_inner` (`BaxterRealSpace.lean`,
Task `BAXTER.1`) already uses — and `Ĉ_sine(k) = radial_fourier (c_HS eta sigma) k` is OZ.8's
closed-form sine-transform.

Equivalently, writing `q0_poly`'s own transform directly (absorbing the `ρ`, since
`q0_poly = ρ·Q_old`) as `q̂0(k) = Re + i·Im`:

    `(1 - Re[q̂0(k)])² + (Im[q̂0(k)])² = 1 - ρ·Ĉ_sine(k)`

**History (`proof_notes_baxter.md` Task `BAXTER.3`):** the first attempt guessed
`Q̂ = 1 + q0_poly_laplace(s)` on the general real/complex Laplace axis — wrong sign, wrong axis,
found broken both numerically and via an `s→∞` asymptotic argument. Re-solving from scratch on the
correct axis (`s=ik`, against `Ĉ_sine`, not `C_HS_laplace`) first found what looked like a
*different* `Q` (a red herring — Wiener–Hopf factorizations of a given real quantity aren't unique
without a normalization condition); the actual resolution was a **sign** correction
(`1 - q0_poly_laplace` on the imaginary axis, not `1 +`), reusing `q0_poly` unchanged. Confirmed
symbolically via `sympy` before this file was written (not just numerically).

## Proof strategy

`Re[q̂0(k)]` and `Im[q̂0(k)]` are `∫₀^σ q0_poly(r)·cos(kr) dr` and `-∫₀^σ q0_poly(r)·sin(kr) dr`.
`q0_poly` is quadratic in `r` on `[0,σ]` (`q0_poly_inner`), so both integrals reduce to the
`{1, r, r²} × {sin(kr), cos(kr)}` moment integrals via a generic quadratic-moment helper:
`ψ1`/`ψ2` (sine, degree 1/2) already exist in `RadialFourierCHS.lean`; this file supplies the
missing degree-0 sine moment (`psi0`) and the degree-0/1/2 cosine moments
(`chi0`/`chi1`/`chi2`), via the same `HasDerivAt`+FTC technique. The main theorem assembles these
against `radial_fourier_c_HS_formula` (OZ.8) and closes by `field_simp` + `ring` after
substituting `eta = π·ρ·σ³/6`, matching `baxter_factorization_inner`'s own closing technique.
-/

open MeasureTheory intervalIntegral Real Set

namespace FMSA.HardSphere

/-! ### Local sin/cos derivative helpers (mirrors `RadialFourierCHS.lean`'s private helpers) -/

private lemma hasDerivAt_sin_mul_wh {k r : ℝ} :
    HasDerivAt (fun x => Real.sin (k * x)) (Real.cos (k * r) * k) r := by
  have h : HasDerivAt (fun x => k * x) k r := by simpa using (hasDerivAt_id r).const_mul k
  exact h.sin

private lemma hasDerivAt_cos_mul_wh {k r : ℝ} :
    HasDerivAt (fun x => Real.cos (k * x)) (-Real.sin (k * r) * k) r := by
  have h : HasDerivAt (fun x => k * x) k r := by simpa using (hasDerivAt_id r).const_mul k
  exact h.cos

/-! ### χ0, ψ0 — degree-0 cosine/sine moments -/

private lemma chi0_hasDerivAt {k : ℝ} (hk : k ≠ 0) (r : ℝ) :
    HasDerivAt (fun r => Real.sin (k * r) / k) (Real.cos (k * r)) r := by
  have h := (hasDerivAt_sin_mul_wh (k := k) (r := r)).div_const k
  exact h.congr_deriv (by field_simp)

/-- `∫0^sigma cos(k·r) dr = sin(k·sigma)/k`. -/
theorem chi0_formula {k : ℝ} (hk : k ≠ 0) (sigma : ℝ) :
    ∫ r in (0 : ℝ)..sigma, Real.cos (k * r) = Real.sin (k * sigma) / k := by
  have hint : IntervalIntegrable (fun r => Real.cos (k * r)) volume 0 sigma :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable 0 sigma
  rw [integral_eq_sub_of_hasDerivAt (fun r _ => chi0_hasDerivAt hk r) hint]
  simp

private lemma psi0_hasDerivAt {k : ℝ} (hk : k ≠ 0) (r : ℝ) :
    HasDerivAt (fun r => -Real.cos (k * r) / k) (Real.sin (k * r)) r := by
  have h := (hasDerivAt_cos_mul_wh (k := k) (r := r)).neg.div_const k
  exact h.congr_deriv (by field_simp)

/-- `∫0^sigma sin(k·r) dr = (1 - cos(k·sigma))/k`. -/
theorem psi0_formula {k : ℝ} (hk : k ≠ 0) (sigma : ℝ) :
    ∫ r in (0 : ℝ)..sigma, Real.sin (k * r) = (1 - Real.cos (k * sigma)) / k := by
  have hint : IntervalIntegrable (fun r => Real.sin (k * r)) volume 0 sigma :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).intervalIntegrable 0 sigma
  rw [integral_eq_sub_of_hasDerivAt (fun r _ => psi0_hasDerivAt hk r) hint]
  simp; ring

/-! ### χ1 — degree-1 cosine moment -/

/-- Antiderivative of `r·cos(k·r)` is `cos(k·r)/k² + r·sin(k·r)/k`. -/
private lemma chi1_hasDerivAt {k : ℝ} (hk : k ≠ 0) (r : ℝ) :
    HasDerivAt (fun r => Real.cos (k * r) / k ^ 2 + r * Real.sin (k * r) / k)
               (r * Real.cos (k * r)) r := by
  have hT1 : HasDerivAt (fun x => Real.cos (k * x) / k ^ 2) (-Real.sin (k * r) * k / k ^ 2) r :=
    hasDerivAt_cos_mul_wh.div_const (k ^ 2)
  have hT2 : HasDerivAt (fun x => x * Real.sin (k * x) / k)
      ((1 * Real.sin (k * r) + r * (Real.cos (k * r) * k)) / k) r :=
    ((hasDerivAt_id r).mul hasDerivAt_sin_mul_wh).div_const k
  exact (hT1.add hT2).congr_deriv (by field_simp; ring)

/-- **χ1 formula:** `∫0^sigma r·cos(k·r) dr = cos(k·sigma)/k² + sigma·sin(k·sigma)/k - 1/k²`. -/
theorem chi1_formula {k : ℝ} (hk : k ≠ 0) (sigma : ℝ) :
    ∫ r in (0 : ℝ)..sigma, r * Real.cos (k * r) =
    Real.cos (k * sigma) / k ^ 2 + sigma * Real.sin (k * sigma) / k - 1 / k ^ 2 := by
  have hint : IntervalIntegrable (fun r => r * Real.cos (k * r)) volume 0 sigma :=
    (continuous_id.mul (Real.continuous_cos.comp
      (continuous_const.mul continuous_id))).intervalIntegrable 0 sigma
  rw [integral_eq_sub_of_hasDerivAt (fun r _ => chi1_hasDerivAt hk r) hint]
  simp only [mul_zero, Real.cos_zero, Real.sin_zero, zero_div]
  field_simp [hk]; ring

/-! ### χ2 — degree-2 cosine moment -/

/-- Antiderivative of `r²·cos(k·r)` is `(2r/k²)·cos(k·r) + (r²/k - 2/k³)·sin(k·r)`. -/
private lemma chi2_hasDerivAt {k : ℝ} (hk : k ≠ 0) (r : ℝ) :
    HasDerivAt (fun r => (2 * r / k ^ 2) * Real.cos (k * r) +
      (r ^ 2 / k - 2 / k ^ 3) * Real.sin (k * r))
      (r ^ 2 * Real.cos (k * r)) r := by
  have hx2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * r) r := by
    have h := hasDerivAt_pow (𝕜 := ℝ) 2 r; simpa [Nat.cast_ofNat, pow_one] using h
  have hA : HasDerivAt (fun x => 2 * x / k ^ 2) (2 / k ^ 2) r := by
    have h := ((hasDerivAt_id r).const_mul 2).div_const (k ^ 2)
    exact h.congr_deriv (by ring)
  have hB : HasDerivAt (fun x => x ^ 2 / k - 2 / k ^ 3) (2 * r / k) r := by
    have h := (hx2.div_const k).sub (hasDerivAt_const r (2 / k ^ 3))
    exact h.congr_deriv (by ring)
  have hT1 : HasDerivAt (fun x => (2 * x / k ^ 2) * Real.cos (k * x))
      ((2 / k ^ 2) * Real.cos (k * r) + (2 * r / k ^ 2) * (-Real.sin (k * r) * k)) r :=
    hA.mul hasDerivAt_cos_mul_wh
  have hT2 : HasDerivAt (fun x => (x ^ 2 / k - 2 / k ^ 3) * Real.sin (k * x))
      ((2 * r / k) * Real.sin (k * r) + (r ^ 2 / k - 2 / k ^ 3) * (Real.cos (k * r) * k)) r :=
    hB.mul hasDerivAt_sin_mul_wh
  exact (hT1.add hT2).congr_deriv (by field_simp [hk]; ring)

/-- **χ2 formula:**
`∫0^sigma r²·cos(k·r) dr = (2·sigma/k²)·cos(k·sigma) + (sigma²/k - 2/k³)·sin(k·sigma)`. -/
theorem chi2_formula {k : ℝ} (hk : k ≠ 0) (sigma : ℝ) :
    ∫ r in (0 : ℝ)..sigma, r ^ 2 * Real.cos (k * r) =
    (2 * sigma / k ^ 2) * Real.cos (k * sigma) +
      (sigma ^ 2 / k - 2 / k ^ 3) * Real.sin (k * sigma) := by
  have hint : IntervalIntegrable (fun r => r ^ 2 * Real.cos (k * r)) volume 0 sigma :=
    ((continuous_id.pow 2).mul (Real.continuous_cos.comp
      (continuous_const.mul continuous_id))).intervalIntegrable 0 sigma
  rw [integral_eq_sub_of_hasDerivAt (fun r _ => chi2_hasDerivAt hk r) hint]
  simp only [mul_zero, Real.cos_zero, Real.sin_zero, zero_div, mul_one, zero_pow,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
  ring

/-! ### Generic quadratic-moment assembly -/

private lemma integral_quadratic_cos (A B C k sigma : ℝ) (hk : k ≠ 0) :
    ∫ r in (0 : ℝ)..sigma, (A + B * r + C * r ^ 2) * Real.cos (k * r) =
    A * (Real.sin (k * sigma) / k) +
      B * (Real.cos (k * sigma) / k ^ 2 + sigma * Real.sin (k * sigma) / k - 1 / k ^ 2) +
      C * ((2 * sigma / k ^ 2) * Real.cos (k * sigma) +
        (sigma ^ 2 / k - 2 / k ^ 3) * Real.sin (k * sigma)) := by
  have hcongr : ∫ r in (0 : ℝ)..sigma, (A + B * r + C * r ^ 2) * Real.cos (k * r) =
      ∫ r in (0 : ℝ)..sigma,
        (A * Real.cos (k * r) + B * (r * Real.cos (k * r)) + C * (r ^ 2 * Real.cos (k * r))) :=
    intervalIntegral.integral_congr (fun r _ => by ring)
  rw [hcongr]
  have hiA : IntervalIntegrable (fun r => A * Real.cos (k * r)) volume 0 sigma :=
    (continuous_const.mul (Real.continuous_cos.comp
      (continuous_const.mul continuous_id))).intervalIntegrable 0 sigma
  have hiB : IntervalIntegrable (fun r => B * (r * Real.cos (k * r))) volume 0 sigma :=
    (continuous_const.mul (continuous_id.mul (Real.continuous_cos.comp
      (continuous_const.mul continuous_id)))).intervalIntegrable 0 sigma
  have hiC : IntervalIntegrable (fun r => C * (r ^ 2 * Real.cos (k * r))) volume 0 sigma :=
    (continuous_const.mul ((continuous_id.pow 2).mul (Real.continuous_cos.comp
      (continuous_const.mul continuous_id)))).intervalIntegrable 0 sigma
  rw [intervalIntegral.integral_add (hiA.add hiB) hiC,
      intervalIntegral.integral_add hiA hiB,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      chi0_formula hk sigma, chi1_formula hk sigma, chi2_formula hk sigma]

private lemma integral_quadratic_sin (A B C k sigma : ℝ) (hk : k ≠ 0) :
    ∫ r in (0 : ℝ)..sigma, (A + B * r + C * r ^ 2) * Real.sin (k * r) =
    A * ((1 - Real.cos (k * sigma)) / k) +
      B * ((Real.sin (k * sigma) - k * sigma * Real.cos (k * sigma)) / k ^ 2) +
      C * ((2 / k ^ 3 - sigma ^ 2 / k) * Real.cos (k * sigma) +
        (2 * sigma / k ^ 2) * Real.sin (k * sigma) - 2 / k ^ 3) := by
  have hcongr : ∫ r in (0 : ℝ)..sigma, (A + B * r + C * r ^ 2) * Real.sin (k * r) =
      ∫ r in (0 : ℝ)..sigma,
        (A * Real.sin (k * r) + B * (r * Real.sin (k * r)) + C * (r ^ 2 * Real.sin (k * r))) :=
    intervalIntegral.integral_congr (fun r _ => by ring)
  rw [hcongr]
  have hiA : IntervalIntegrable (fun r => A * Real.sin (k * r)) volume 0 sigma :=
    (continuous_const.mul (Real.continuous_sin.comp
      (continuous_const.mul continuous_id))).intervalIntegrable 0 sigma
  have hiB : IntervalIntegrable (fun r => B * (r * Real.sin (k * r))) volume 0 sigma :=
    (continuous_const.mul (continuous_id.mul (Real.continuous_sin.comp
      (continuous_const.mul continuous_id)))).intervalIntegrable 0 sigma
  have hiC : IntervalIntegrable (fun r => C * (r ^ 2 * Real.sin (k * r))) volume 0 sigma :=
    (continuous_const.mul ((continuous_id.pow 2).mul (Real.continuous_sin.comp
      (continuous_const.mul continuous_id)))).intervalIntegrable 0 sigma
  rw [intervalIntegral.integral_add (hiA.add hiB) hiC,
      intervalIntegral.integral_add hiA hiB,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      psi0_formula hk sigma, psi1_formula hk sigma, psi2_formula hk sigma]

/-! ### `q0_poly`'s real/imaginary Fourier moments -/

/-- `Re[q̂0(k)] = ∫0^sigma q0_poly(r)·cos(k·r) dr`, closed form. `q0_poly` expands to
`A + B·r + C·r²` on `[0,sigma]` via `q0_poly_inner`, then `integral_quadratic_cos`. -/
theorem q0poly_cos_integral_formula (eta sigma rho k : ℝ) (hsigma : 0 < sigma) (hk : k ≠ 0) :
    ∫ r in (0 : ℝ)..sigma, q0_poly eta sigma rho r * Real.cos (k * r) =
    (rho * q_doubleprime_py eta * sigma ^ 2 / 2 - rho * q_prime_py eta sigma * sigma) *
        (Real.sin (k * sigma) / k) +
      (rho * q_prime_py eta sigma - rho * q_doubleprime_py eta * sigma) *
        (Real.cos (k * sigma) / k ^ 2 + sigma * Real.sin (k * sigma) / k - 1 / k ^ 2) +
      (rho * q_doubleprime_py eta / 2) *
        ((2 * sigma / k ^ 2) * Real.cos (k * sigma) +
          (sigma ^ 2 / k - 2 / k ^ 3) * Real.sin (k * sigma)) := by
  have hcongr : ∫ r in (0 : ℝ)..sigma, q0_poly eta sigma rho r * Real.cos (k * r) =
      ∫ r in (0 : ℝ)..sigma,
        ((rho * q_doubleprime_py eta * sigma ^ 2 / 2 - rho * q_prime_py eta sigma * sigma) +
          (rho * q_prime_py eta sigma - rho * q_doubleprime_py eta * sigma) * r +
          (rho * q_doubleprime_py eta / 2) * r ^ 2) * Real.cos (k * r) := by
    apply intervalIntegral.integral_congr
    intro r hr
    simp only [Set.uIcc_of_le hsigma.le, Set.mem_Icc] at hr
    simp only [q0_poly_inner hr.2]; ring
  rw [hcongr, integral_quadratic_cos _ _ _ k sigma hk]

/-- `-Im[q̂0(k)] = ∫0^sigma q0_poly(r)·sin(k·r) dr`, closed form. -/
theorem q0poly_sin_integral_formula (eta sigma rho k : ℝ) (hsigma : 0 < sigma) (hk : k ≠ 0) :
    ∫ r in (0 : ℝ)..sigma, q0_poly eta sigma rho r * Real.sin (k * r) =
    (rho * q_doubleprime_py eta * sigma ^ 2 / 2 - rho * q_prime_py eta sigma * sigma) *
        ((1 - Real.cos (k * sigma)) / k) +
      (rho * q_prime_py eta sigma - rho * q_doubleprime_py eta * sigma) *
        ((Real.sin (k * sigma) - k * sigma * Real.cos (k * sigma)) / k ^ 2) +
      (rho * q_doubleprime_py eta / 2) *
        ((2 / k ^ 3 - sigma ^ 2 / k) * Real.cos (k * sigma) +
          (2 * sigma / k ^ 2) * Real.sin (k * sigma) - 2 / k ^ 3) := by
  have hcongr : ∫ r in (0 : ℝ)..sigma, q0_poly eta sigma rho r * Real.sin (k * r) =
      ∫ r in (0 : ℝ)..sigma,
        ((rho * q_doubleprime_py eta * sigma ^ 2 / 2 - rho * q_prime_py eta sigma * sigma) +
          (rho * q_prime_py eta sigma - rho * q_doubleprime_py eta * sigma) * r +
          (rho * q_doubleprime_py eta / 2) * r ^ 2) * Real.sin (k * r) := by
    apply intervalIntegral.integral_congr
    intro r hr
    simp only [Set.uIcc_of_le hsigma.le, Set.mem_Icc] at hr
    simp only [q0_poly_inner hr.2]; ring
  rw [hcongr, integral_quadratic_sin _ _ _ k sigma hk]

/-! ### Main theorem: the Wiener–Hopf factorization -/

/-- **Task BAXTER.3 — Baxter's Wiener–Hopf factorization**, symbolically confirmed (`sympy`) before
this proof was written. Using `q0_poly`'s own Fourier transform (`q̂0(k) = Re - i·Im`, `Re`/`Im`
given by `q0poly_cos_integral_formula`/`q0poly_sin_integral_formula`, no factor of `ρ` needed
separately since `q0_poly = ρ·Q_old` already includes it):

    `(1 - Re[q̂0(k)])² + (Im[q̂0(k)])² = 1 - ρ·Ĉ_sine(k)`

closes by `field_simp` + `ring` after substituting `eta = π·ρ·σ³/6`, unfolding `q_prime_py`,
`q_doubleprime_py`, `py_a0`, `py_a1`, `py_a3` — same technique as `baxter_factorization_inner`. -/
theorem baxter_wiener_hopf_factorization (eta sigma rho k : ℝ) (hsigma : 0 < sigma) (hk : k ≠ 0)
    (heta : eta < 1) (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) :
    (1 - ∫ r in (0 : ℝ)..sigma, q0_poly eta sigma rho r * Real.cos (k * r)) ^ 2 +
      (∫ r in (0 : ℝ)..sigma, q0_poly eta sigma rho r * Real.sin (k * r)) ^ 2 =
    1 - rho * radial_fourier (c_HS eta sigma) k := by
  rw [q0poly_cos_integral_formula eta sigma rho k hsigma hk,
      q0poly_sin_integral_formula eta sigma rho k hsigma hk,
      radial_fourier_c_HS_formula eta sigma k hsigma hk]
  unfold q_prime_py q_doubleprime_py py_a0 py_a1 py_a3
  have h1e : (1 : ℝ) - eta ≠ 0 := by linarith
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  -- Eliminate `rho` (not `eta`) so the `(1-eta)` denominators already in play stay simple.
  have hrho_def : rho = 6 * eta / (Real.pi * sigma ^ 3) := by
    rw [heta_def]; field_simp
  subst hrho_def
  have hpyth : ∀ x : ℝ, Real.sin x ^ 2 = 1 - Real.cos x ^ 2 := fun x => by
    have h := Real.sin_sq_add_cos_sq x
    linarith
  field_simp [h1e, hk, hsigma.ne', hpi]
  ring_nf
  simp only [hpyth]
  ring

end HardSphere

end FMSA
