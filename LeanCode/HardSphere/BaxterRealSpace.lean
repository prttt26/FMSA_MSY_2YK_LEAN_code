/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HardSphere.BaxterFactor
import LeanCode.HardSphere.PYDCF

/-!
# Real-space Baxter Q0 Factor and Convolution Identity

**Sources:** [chsY] Eq. 31–33; [LN] Eq. 10–11; Baxter (1970); Wertheim (1963)

For the monodisperse single-component hard-sphere system with packing fraction eta and
sphere diameter sigma:

## Real-space auxiliary functions φ1, φ2  ([chsY] Eq. 32)

    φ1(r; sigma) = (r - sigma)·θ(sigma - r)    (= r - sigma for r ≤ sigma,  0 for r > sigma)
    φ2(r; sigma) = 1/2(r - sigma)^2·θ(sigma - r)  (= 1/2(r-sigma)^2 for r ≤ sigma,  0 for r > sigma)

These are the inverse Laplace transforms of
    φ1(sigma; s) = (1 - ssigma - e^{-ssigma})/s^2
    φ2(sigma; s) = (1 - ssigma + (ssigma)^2/2 - e^{-ssigma})/s^3
proved by FTC with polynomial antiderivatives (no sorry).

## Polynomial Baxter Q-factor  ([chsY] Eq. 33 / [LN] Eq. 10–11)

    q̃0(r) = rhoQ'φ1(r;sigma) + rhoQ''φ2(r;sigma)   for r ∈ [0, sigma],  0 for r > sigma

with PY Baxter coefficients (monodisperse, from [LN] Eq. 11):
    Q' = πsigma(2+eta)/(1-eta)^2
    Q'' = 2π(1+2eta)/(1-eta)^2

The full distributional Baxter factor is `Q0(r) = delta(r) + q̃0(r)`.

## Baxter factorization  (real-space convolution identity)

For r ∈ (0, sigma):
    rho·c_HS(r) = q̃0(r) - ∫_r^sigma q̃0(r')·q̃0(r'-r) dr'

This is the real-space form of the Wiener-Hopf factorization
    1 - rhoĈ_HS(s) = Q̂0(s)·Q̂0(-s)
(Baxter 1970, Wertheim 1963).  The convolution reduces to a degree-4 polynomial integral
identity that holds with the specific PY values Q', Q''.  Stated as `axiom`.

## Sorries / Axioms

- `baxter_factorization_inner`: the polynomial integral identity is exact but the
  formal Lean proof of the degree-4 ring computation is deferred.
-/

set_option linter.unusedSimpArgs false

open MeasureTheory intervalIntegral Real Set

namespace FMSA.HardSphere

/-! ### Private helper -/

private lemma hasDerivAt_exp_neg_mul_rs {s r : ℝ} :
    HasDerivAt (fun x => Real.exp (-s * x)) (Real.exp (-s * r) * -s) r := by
  have h : HasDerivAt (fun x => -s * x) (-s) r := by
    simpa using (hasDerivAt_id r).const_mul (-s)
  exact h.exp

/-! ### Real-space auxiliary functions φ1, φ2 -/

/-- **[chsY] Eq. 32 (φ1_real):** Inverse Laplace transform of `φ1(sigma; s) = (1-ssigma-e^{-ssigma})/s^2`.
    `φ1(r; sigma) = r - sigma` for `r ≤ sigma`,  `0` for `r > sigma`. -/
noncomputable def phi1_real (sigma r : ℝ) : ℝ := if r <= sigma then r - sigma else 0

/-- **[chsY] Eq. 32 (φ2_real):** Inverse Laplace transform of
`φ2(sigma; s) = (1-ssigma+(ssigma)^2/2-e^{-ssigma})/s^3`.
    `φ2(r; sigma) = 1/2(r-sigma)^2` for `r ≤ sigma`,  `0` for `r > sigma`. -/
noncomputable def phi2_real (sigma r : ℝ) : ℝ := if r <= sigma then (r - sigma) ^ 2 / 2 else 0

/-! ### Antiderivative HasDerivAt lemmas for FTC -/

private lemma phi1_real_antideriv_hasDerivAt {s : ℝ} (hs : s ≠ 0) (sigma r : ℝ) :
    HasDerivAt (fun r => -((r - sigma) / s + 1 / s ^ 2) * Real.exp (-s * r))
               ((r - sigma) * Real.exp (-s * r)) r := by
  -- derivative of inner function x - sigma at r
  have hg : HasDerivAt (fun x : ℝ => x - sigma) 1 r := by
    have h := (hasDerivAt_id r).sub (hasDerivAt_const r sigma)
    simp only [id_eq, sub_zero] at h; exact h
  -- antiderivative coefficient A(r) = -((r-sigma)/s + 1/s^2), A'(r) = -1/s
  have hA : HasDerivAt (fun x => -((x - sigma) / s + 1 / s ^ 2)) (-(1 / s)) r := by
    have h := ((hg.div_const s).add (hasDerivAt_const r (1 / s ^ 2))).neg
    exact h.congr_deriv (by ring)
  exact (hA.mul hasDerivAt_exp_neg_mul_rs).congr_deriv (by field_simp [hs]; ring)

private lemma phi2_real_antideriv_hasDerivAt {s : ℝ} (hs : s ≠ 0) (sigma r : ℝ) :
    HasDerivAt (fun r => -((r - sigma) ^ 2 / (2 * s) + (r - sigma) / s ^ 2 + 1 / s ^ 3) *
                         Real.exp (-s * r))
               ((r - sigma) ^ 2 / 2 * Real.exp (-s * r)) r := by
  -- derivative of x - sigma at r
  have hg : HasDerivAt (fun x : ℝ => x - sigma) 1 r := by
    have h := (hasDerivAt_id r).sub (hasDerivAt_const r sigma)
    simp only [id_eq, sub_zero] at h; exact h
  -- derivative of (x-sigma)^2 at r is 2(r-sigma), proved via product rule on (x-sigma)*(x-sigma)
  have hx2 : HasDerivAt (fun x : ℝ => (x - sigma) ^ 2) (2 * (r - sigma)) r := by
    have hmul := hg.mul hg
    -- hmul has Pi-multiplication function form: (fun x => x-sigma) * (fun x => x-sigma)
    have heq : ((fun x : ℝ => x - sigma) * fun x => x - sigma) = fun x => (x - sigma) ^ 2 :=
      funext fun x => by simp [sq, Pi.mul_apply]
    rw [heq] at hmul
    exact hmul.congr_deriv (by ring)
  -- derivative of (x-sigma)^2/(2s) is (r-sigma)/s
  have h1 : HasDerivAt (fun x => (x - sigma) ^ 2 / (2 * s)) ((r - sigma) / s) r :=
    (hx2.div_const _).congr_deriv (by field_simp [hs])
  -- derivative of (x-sigma)/s^2 is 1/s^2
  have h2 : HasDerivAt (fun x => (x - sigma) / s ^ 2) (1 / s ^ 2) r := hg.div_const _
  -- derivative of 1/s^3 is 0
  have h3 : HasDerivAt (fun _ : ℝ => (1 : ℝ) / s ^ 3) 0 r := hasDerivAt_const _ _
  -- antiderivative coefficient A(r) = -((r-sigma)^2/(2s)+(r-sigma)/s^2+1/s^3), A'(r) = -((r-sigma)/s+1/s^2)
  have hA : HasDerivAt (fun x => -((x - sigma) ^ 2 / (2 * s) + (x - sigma) / s ^ 2 + 1 / s ^ 3))
      (-((r - sigma) / s + 1 / s ^ 2)) r := by
    have h := ((h1.add h2).add h3).neg
    exact h.congr_deriv (by ring)
  exact (hA.mul hasDerivAt_exp_neg_mul_rs).congr_deriv (by field_simp [hs]; ring)

/-! ### Forward Laplace transform theorems (no sorry) -/

/-- **[chsY] Eq. 31 — Forward Laplace transform of φ1_real:**
`∫0^sigma (r-sigma)·exp(-sr) dr = (1 - ssigma - e^{-ssigma})/s^2`  for `s ≠ 0`, `sigma ≥ 0`.

This verifies that `phi1_real` is the real-space form of the chsY Eq. 31 function. -/
theorem phi1_real_laplace {s : ℝ} (hs : s ≠ 0) {sigma : ℝ} (hsigma : 0 <= sigma) :
    ∫ r in (0 : ℝ)..sigma, phi1_real sigma r * Real.exp (-s * r) =
    (1 - s * sigma - Real.exp (-s * sigma)) / s ^ 2 := by
  have hint : IntervalIntegrable (fun r => (r - sigma) * Real.exp (-s * r)) volume 0 sigma :=
    (continuous_id.sub continuous_const).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)) |>.intervalIntegrable 0 sigma
  have hcongr : ∫ r in (0 : ℝ)..sigma, phi1_real sigma r * Real.exp (-s * r) =
      ∫ r in (0 : ℝ)..sigma, (r - sigma) * Real.exp (-s * r) := by
    apply intervalIntegral.integral_congr
    intro r hr
    simp only [Set.uIcc_of_le hsigma, Set.mem_Icc] at hr
    simp [phi1_real, hr.2]
  rw [hcongr,
      integral_eq_sub_of_hasDerivAt (fun r _ => phi1_real_antideriv_hasDerivAt hs sigma r) hint]
  simp only [sub_self, zero_div, zero_add, mul_zero, Real.exp_zero, mul_one]
  field_simp [hs]; ring

/-- **[chsY] Eq. 31 — Forward Laplace transform of φ2_real:**
`∫0^sigma 1/2(r-sigma)^2·exp(-sr) dr = (1 - ssigma + (ssigma)^2/2 - e^{-ssigma})/s^3`  for `s ≠ 0`, `sigma ≥ 0`.

This verifies that `phi2_real` is the real-space form of the chsY Eq. 31 function. -/
theorem phi2_real_laplace {s : ℝ} (hs : s ≠ 0) {sigma : ℝ} (hsigma : 0 <= sigma) :
    ∫ r in (0 : ℝ)..sigma, phi2_real sigma r * Real.exp (-s * r) =
    (1 - s * sigma + (s * sigma) ^ 2 / 2 - Real.exp (-s * sigma)) / s ^ 3 := by
  have hint : IntervalIntegrable (fun r => (r - sigma) ^ 2 / 2 * Real.exp (-s * r)) volume 0 sigma :=
    ((continuous_id.sub continuous_const).pow 2 |>.div_const 2).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)) |>.intervalIntegrable 0 sigma
  have hcongr : ∫ r in (0 : ℝ)..sigma, phi2_real sigma r * Real.exp (-s * r) =
      ∫ r in (0 : ℝ)..sigma, (r - sigma) ^ 2 / 2 * Real.exp (-s * r) := by
    apply intervalIntegral.integral_congr
    intro r hr
    simp only [Set.uIcc_of_le hsigma, Set.mem_Icc] at hr
    simp [phi2_real, hr.2]
  rw [hcongr,
      integral_eq_sub_of_hasDerivAt (fun r _ => phi2_real_antideriv_hasDerivAt hs sigma r) hint]
  simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
             zero_add, mul_zero, Real.exp_zero, mul_one]
  field_simp [hs]; ring

/-! ### Single-component PY Baxter Q-factor coefficients -/

/-- **[LN] Eq. 11 — Q' coefficient:**
`Q'(eta, sigma) = πsigma(2+eta)/(1-eta)^2`.

From the multicomponent formula `Q'_{ij} = (2π/Δ)(R_{ij} + πR_iR_jξ2/(4Δ))` with
`i = j`, `R_{ij} = sigma`, `ξ2 = rhosigma^2`, `Δ = 1-eta`, using `πrhosigma^3 = 6eta`. -/
noncomputable def q_prime_py (eta sigma : ℝ) : ℝ := Real.pi * sigma * (2 + eta) / (1 - eta) ^ 2

/-- **[LN] Eq. 11 — Q'' coefficient:**
`Q''(eta) = 2π(1+2eta)/(1-eta)^2`.

From the multicomponent formula `Q''_j = (2π/Δ)(1 + πR_jξ2/(2Δ))` with
`R_j = sigma`, `ξ2 = rhosigma^2`, `Δ = 1-eta`, using `πrhosigma^3 = 6eta`. -/
noncomputable def q_doubleprime_py (eta : ℝ) : ℝ := 2 * Real.pi * (1 + 2 * eta) / (1 - eta) ^ 2

/-! ### Polynomial Baxter Q0 factor in real space -/

/-- **[chsY] Eq. 33 — Polynomial piece of the real-space Baxter Q-factor:**

For r ∈ [0, sigma]: `q̃0(r) = rhoQ'(r-sigma) + (rhoQ''/2)(r-sigma)^2`.  Zero for r > sigma.

The full distributional Baxter factor is `Q0(r) = delta(r) + q̃0(r)`. -/
noncomputable def q0_poly (eta sigma rho : ℝ) (r : ℝ) : ℝ :=
  rho * q_prime_py eta sigma * phi1_real sigma r + rho * q_doubleprime_py eta * phi2_real sigma r

/-- Expand `q0_poly` to its quadratic polynomial form for `r ≤ sigma`. -/
theorem q0_poly_inner {eta sigma rho r : ℝ} (hr : r <= sigma) :
    q0_poly eta sigma rho r =
    rho * q_prime_py eta sigma * (r - sigma) + rho * q_doubleprime_py eta * (r - sigma) ^ 2 / 2 := by
  simp [q0_poly, phi1_real, phi2_real, hr]
  ring

/-- `q0_poly` vanishes outside the core: `q0_poly eta sigma rho r = 0` for `r > sigma`. -/
theorem q0_poly_outer {eta sigma rho r : ℝ} (hr : sigma < r) : q0_poly eta sigma rho r = 0 := by
  have hle : ¬r <= sigma := not_le.mpr hr
  simp [q0_poly, phi1_real, phi2_real, hle]

/-! ### Baxter factorization (real-space convolution identity) -/

/-- **Baxter factorization in real space  (Baxter 1970, Wertheim 1963):**

For `r ∈ (0, sigma)`, the PY hard-sphere DCF satisfies the convolution identity:

    rho·c_HS(eta, sigma, r) = q̃0(r) - ∫_r^sigma q̃0(r')·q̃0(r'-r) dr'

where `q̃0 = q0_poly eta sigma rho`.

**Origin:** The distributional convolution of the full Baxter factor `Q0 = delta + q̃0` with
its reflection `Q0† = delta + q̃0†` (where `q̃0†(r) := q̃0(-r)`, supported on `[-sigma, 0]`)
gives `Q0 ⊛ Q0† = delta + q̃0 + q̃0† + q̃0 ⊛ q̃0†`.  For `r ∈ (0, sigma)`:
`delta(r) = 0`,  `q̃0†(r) = q̃0(-r) = 0`  (support `[-sigma,0]` misses `r > 0`),  and
`(q̃0 ⊛ q̃0†)(r) = ∫_r^sigma q̃0(r')·q̃0(r'-r) dr'`  (support overlap on `[r, sigma]`).
This equals `-rho·c_HS(r)` by the Baxter–Wertheim factorization.

**Polynomial nature:** Substituting the PY values `Q' = πsigma(2+eta)/(1-eta)^2` and
`Q'' = 2π(1+2eta)/(1-eta)^2` gives a degree-4 polynomial convolution integral in `(r, eta, sigma, rho)`
that equals `rho·c_HS_inner(eta, sigma, r)` (a cubic polynomial), with the degree-4 and -5
cancellations being the content of the Baxter–Wertheim PY solution.

Proved via FTC on the degree-5 antiderivative of the convolution integrand,
followed by algebraic verification (`field_simp` + `ring`) using `heta_def`. -/
theorem baxter_factorization_inner {eta sigma rho : ℝ} (hsigma : 0 < sigma) (heta0 : 0 <= eta) (heta : eta < 1)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) :
    ∀ r ∈ Set.Ioo 0 sigma,
    rho * c_HS eta sigma r =
    q0_poly eta sigma rho r -
      ∫ r' in r..sigma, q0_poly eta sigma rho r' * q0_poly eta sigma rho (r' - r) := by
  intro r hr
  obtain ⟨hr0, hr_lt⟩ := hr
  have hr_le : r ≤ sigma := hr_lt.le
  -- Unfold c_HS (inner) and q0_poly (inner polynomial form)
  rw [c_HS_inner hr_lt, q0_poly_inner hr_le]
  -- Abbreviate PY Baxter Q-factor coefficients
  set α := rho * q_prime_py eta sigma with hα_def
  set β := rho * q_doubleprime_py eta with hβ_def
  -- Rewrite integral: replace piecewise q0_poly by its inner polynomial on [r, sigma]
  have hI : ∫ r' in r..sigma, q0_poly eta sigma rho r' * q0_poly eta sigma rho (r' - r) =
      ∫ r' in r..sigma,
        (α * (r' - sigma) + β * (r' - sigma) ^ 2 / 2) *
        (α * (r' - r - sigma) + β * (r' - r - sigma) ^ 2 / 2) := by
    apply intervalIntegral.integral_congr
    intro r' hr'
    rw [Set.uIcc_of_le hr_le] at hr'
    obtain ⟨hr'1, hr'2⟩ := Set.mem_Icc.mp hr'
    dsimp only []
    rw [q0_poly_inner hr'2, q0_poly_inner (by linarith : r' - r ≤ sigma), ← hα_def, ← hβ_def]
  rw [hI]
  -- Polynomial integrand is continuous, hence integrable
  have hint : IntervalIntegrable (fun r' =>
      (α * (r' - sigma) + β * (r' - sigma) ^ 2 / 2) *
      (α * (r' - r - sigma) + β * (r' - r - sigma) ^ 2 / 2)) volume r sigma := by
    apply Continuous.intervalIntegrable
    fun_prop
  -- Degree-5 antiderivative of the convolution integrand
  -- (derivation: expand product in u = r' - sigma, integrate term by term)
  have hderiv : ∀ r' ∈ Set.uIcc r sigma,
      HasDerivAt (fun x =>
          α ^ 2 / 3 * (x - sigma) ^ 3 - α ^ 2 * r / 2 * (x - sigma) ^ 2 +
          α * β / 4 * (x - sigma) ^ 4 - α * β * r / 2 * (x - sigma) ^ 3 +
          α * β * r ^ 2 / 4 * (x - sigma) ^ 2 + β ^ 2 / 20 * (x - sigma) ^ 5 -
          β ^ 2 * r / 8 * (x - sigma) ^ 4 + β ^ 2 * r ^ 2 / 12 * (x - sigma) ^ 3)
        ((α * (r' - sigma) + β * (r' - sigma) ^ 2 / 2) *
         (α * (r' - r - sigma) + β * (r' - r - sigma) ^ 2 / 2))
        r' := by
    intro r' _
    -- Derivatives of (x - sigma)^n via chain rule (inner derivative = 1)
    have hin : HasDerivAt (fun x => x - sigma) 1 r' := by
      have h := (hasDerivAt_id r').sub (hasDerivAt_const r' sigma)
      simp only [id_eq, sub_zero] at h; exact h
    have h2 : HasDerivAt (fun x => (x - sigma) ^ 2) (2 * (r' - sigma)) r' :=
      (hin.pow 2).congr_deriv (by push_cast; ring)
    have h3 : HasDerivAt (fun x => (x - sigma) ^ 3) (3 * (r' - sigma) ^ 2) r' :=
      (hin.pow 3).congr_deriv (by push_cast; ring)
    have h4 : HasDerivAt (fun x => (x - sigma) ^ 4) (4 * (r' - sigma) ^ 3) r' :=
      (hin.pow 4).congr_deriv (by push_cast; ring)
    have h5 : HasDerivAt (fun x => (x - sigma) ^ 5) (5 * (r' - sigma) ^ 4) r' :=
      (hin.pow 5).congr_deriv (by push_cast; ring)
    -- HasDerivAt for each term of the antiderivative (explicit function types)
    have hA1 : HasDerivAt (fun x => α ^ 2 / 3 * (x - sigma) ^ 3)
        (α ^ 2 / 3 * (3 * (r' - sigma) ^ 2)) r' := h3.const_mul _
    have hA2 : HasDerivAt (fun x => α ^ 2 * r / 2 * (x - sigma) ^ 2)
        (α ^ 2 * r / 2 * (2 * (r' - sigma))) r' := h2.const_mul _
    have hA3 : HasDerivAt (fun x => α * β / 4 * (x - sigma) ^ 4)
        (α * β / 4 * (4 * (r' - sigma) ^ 3)) r' := h4.const_mul _
    have hA4 : HasDerivAt (fun x => α * β * r / 2 * (x - sigma) ^ 3)
        (α * β * r / 2 * (3 * (r' - sigma) ^ 2)) r' := h3.const_mul _
    have hA5 : HasDerivAt (fun x => α * β * r ^ 2 / 4 * (x - sigma) ^ 2)
        (α * β * r ^ 2 / 4 * (2 * (r' - sigma))) r' := h2.const_mul _
    have hA6 : HasDerivAt (fun x => β ^ 2 / 20 * (x - sigma) ^ 5)
        (β ^ 2 / 20 * (5 * (r' - sigma) ^ 4)) r' := h5.const_mul _
    have hA7 : HasDerivAt (fun x => β ^ 2 * r / 8 * (x - sigma) ^ 4)
        (β ^ 2 * r / 8 * (4 * (r' - sigma) ^ 3)) r' := h4.const_mul _
    have hA8 : HasDerivAt (fun x => β ^ 2 * r ^ 2 / 12 * (x - sigma) ^ 3)
        (β ^ 2 * r ^ 2 / 12 * (3 * (r' - sigma) ^ 2)) r' := h3.const_mul _
    -- Chain: .sub/.add produces Pi arithmetic form; convert to explicit lambda via
    -- congr_of_eventuallyEq + Pi.add_apply/Pi.sub_apply, then check derivative by ring
    have hchain := ((((((hA1.sub hA2).add hA3).sub hA4).add hA5).add hA6).sub hA7).add hA8
    exact (hchain.congr_of_eventuallyEq
        (Filter.eventually_of_forall fun x => by simp [Pi.add_apply, Pi.sub_apply])
        (by simp [Pi.add_apply, Pi.sub_apply])).congr_deriv (by ring)
  -- Apply FTC: integral = F(sigma) - F(r), with F(sigma) = 0 (all (sigma-sigma)^n = 0)
  rw [integral_eq_sub_of_hasDerivAt hderiv hint]
  -- Unfold all definitions and verify polynomial identity via field_simp + ring
  simp only [hα_def, hβ_def, py_a0, py_a1, py_a3, q_prime_py, q_doubleprime_py]
  have h1e : (1 : ℝ) - eta ≠ 0 := by linarith
  field_simp [hsigma.ne', h1e]
  rw [heta_def]
  ring

end FMSA.HardSphere
