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
# Task BAXTER.1 — Real-space Baxter Q0 Factor and Convolution Identity *(formerly Task OZ.5)*

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
set_option linter.unusedVariables false

open MeasureTheory intervalIntegral Real Set

namespace FMSA.HardSphere

/-! ### Private helper -/

private lemma hasDerivAt_exp_neg_mul_rs {s r : ℝ} :
    HasDerivAt (fun x => Real.exp (-s * x)) (Real.exp (-s * r) * -s) r := by
  have h : HasDerivAt (fun x => -s * x) (-s) r := by
    simpa using (hasDerivAt_id r).const_mul (-s)
  exact h.exp

/-! ### Real-space auxiliary functions φ1, φ2 -/

/-- **[chsY] Eq. 32 (φ1_real):** Inverse Laplace transform of
`φ1(sigma; s) = (1-ssigma-e^{-ssigma})/s^2`.
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
  -- antiderivative A(r) = -((r-sigma)^2/(2s)+(r-sigma)/s^2+1/s^3),
  -- A'(r) = -((r-sigma)/s+1/s^2)
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
`∫0^sigma 1/2(r-sigma)^2·exp(-sr) dr = (1 - ssigma + (ssigma)^2/2 - e^{-ssigma})/s^3`
for `s ≠ 0`, `sigma ≥ 0`.

This verifies that `phi2_real` is the real-space form of the chsY Eq. 31 function. -/
theorem phi2_real_laplace {s : ℝ} (hs : s ≠ 0) {sigma : ℝ} (hsigma : 0 <= sigma) :
    ∫ r in (0 : ℝ)..sigma, phi2_real sigma r * Real.exp (-s * r) =
    (1 - s * sigma + (s * sigma) ^ 2 / 2 - Real.exp (-s * sigma)) / s ^ 3 := by
  have hint : IntervalIntegrable
      (fun r => (r - sigma) ^ 2 / 2 * Real.exp (-s * r)) volume 0 sigma :=
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
    rho * q_prime_py eta sigma * (r - sigma) +
    rho * q_doubleprime_py eta * (r - sigma) ^ 2 / 2 := by
  simp [q0_poly, phi1_real, phi2_real, hr]
  ring

/-- `q0_poly` vanishes outside the core: `q0_poly eta sigma rho r = 0` for `r > sigma`. -/
theorem q0_poly_outer {eta sigma rho r : ℝ} (hr : sigma < r) : q0_poly eta sigma rho r = 0 := by
  have hle : ¬r <= sigma := not_le.mpr hr
  simp [q0_poly, phi1_real, phi2_real, hle]

/-! ### Baxter factorization (real-space convolution identity) -/

/-- **Baxter--Wertheim real-space factorization identity (Baxter 1970, Wertheim 1963):**

For `r ∈ (0, sigma)`, the PY hard-sphere DCF satisfies:

    2*pi*rho*r*c_HS(eta, sigma, r) =
      (integral_r^sigma q0_poly(r'-r)*q0_poly'(r') dr') - q0_poly'(r)

where `q0_poly'(r) = rho*Q' + rho*Q''*(r-sigma)` is the derivative of `q0_poly` w.r.t. `r`.

**Physical origin (Wertheim 1963):** The Laplace-space factorization
`1 - rho*C_HS(s) = Q0_hat(s)*Q0_hat(-s)` gives the real-space identity
`-r*c(r) = Q'(r) - 2*pi*rho * integral_0^{sigma-r} Q(t)*Q'(t+r) dt`
(where `Q = q0_poly/(2*pi*rho)`, `Q' = q0_poly'/(2*pi*rho)`).
Multiplying by `-2*pi*rho` and substituting `t = r'-r` yields the Lean form.

**Numerically verified** at eta=0.4, sigma=1, r=0.5, rho=2.4/pi:
  LHS = 2*pi*(2.4/pi)*0.5*(-295/24) = -29.5;
  RHS = integral(-25.5) - q0_poly'(4) = -29.5 (exact).

**Polynomial proof:** The integrand `q0_poly(r'-r)*q0_poly'(r')` is degree 3 in `r'`
(quadratic x linear), so the antiderivative `F` is degree 4 (7 terms). After FTC,
the identity is a polynomial in `{r, rho, sigma, pi}` closed by `field_simp + ring`
after substituting `eta = pi*rho*sigma^3/6`. -/
theorem baxter_factorization_inner {eta sigma rho : ℝ}
    (hsigma : 0 < sigma) (_heta0 : 0 <= eta) (heta : eta < 1)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) :
    ∀ r ∈ Set.Ioo 0 sigma,
    2 * Real.pi * rho * r * c_HS eta sigma r =
    (∫ r' in r..sigma, q0_poly eta sigma rho (r' - r) *
      (rho * q_prime_py eta sigma + rho * q_doubleprime_py eta * (r' - sigma))) -
    (rho * q_prime_py eta sigma + rho * q_doubleprime_py eta * (r - sigma)) := by
  intro r hr
  obtain ⟨hr0, hr_lt⟩ := hr
  have hr_le : r ≤ sigma := hr_lt.le
  rw [c_HS_inner hr_lt]
  set α := rho * q_prime_py eta sigma with hα_def
  set β := rho * q_doubleprime_py eta with hβ_def
  -- Rewrite integral: expand q0_poly(r'-r) to polynomial form on [r, sigma]
  have hI : ∫ r' in r..sigma, q0_poly eta sigma rho (r' - r) *
      (rho * q_prime_py eta sigma + rho * q_doubleprime_py eta * (r' - sigma)) =
      ∫ r' in r..sigma,
        (α * (r' - r - sigma) + β * (r' - r - sigma) ^ 2 / 2) *
        (α + β * (r' - sigma)) := by
    apply intervalIntegral.integral_congr
    intro r' hr'
    rw [Set.uIcc_of_le hr_le] at hr'
    obtain ⟨hr'1, hr'2⟩ := Set.mem_Icc.mp hr'
    dsimp only []
    rw [q0_poly_inner (by linarith [hr0.le, hr'2] : r' - r ≤ sigma), ← hα_def, ← hβ_def]
  rw [hI]
  -- Degree-3 integrand is continuous, hence integrable
  have hint : IntervalIntegrable (fun r' =>
      (α * (r' - r - sigma) + β * (r' - r - sigma) ^ 2 / 2) *
      (α + β * (r' - sigma))) volume r sigma := by
    apply Continuous.intervalIntegrable; fun_prop
  -- Degree-4 antiderivative F of q0_poly(r'-r)*q0_poly'(r'):
  --   F(x) = α²/2*(x-r-σ)² + αβ/3*(x-σ)³ - αβr/2*(x-σ)² + αβ/6*(x-r-σ)³
  --        + β²/8*(x-σ)⁴ - β²r/3*(x-σ)³ + β²r²/4*(x-σ)²
  -- At x=sigma: F(sigma) = α²r²/2 - αβr³/6  (all (sigma-sigma) terms vanish)
  -- Verified: dF/dx = (α(x-r-σ)+β(x-r-σ)²/2)*(α+β(x-σ)) by algebraic expansion.
  have hderiv : ∀ r' ∈ Set.uIcc r sigma,
      HasDerivAt (fun x =>
          α ^ 2 / 2 * (x - r - sigma) ^ 2 + α * β / 3 * (x - sigma) ^ 3 -
          α * β * r / 2 * (x - sigma) ^ 2 + α * β / 6 * (x - r - sigma) ^ 3 +
          β ^ 2 / 8 * (x - sigma) ^ 4 - β ^ 2 * r / 3 * (x - sigma) ^ 3 +
          β ^ 2 * r ^ 2 / 4 * (x - sigma) ^ 2)
        ((α * (r' - r - sigma) + β * (r' - r - sigma) ^ 2 / 2) *
         (α + β * (r' - sigma)))
        r' := by
    intro r' _
    have hin_B : HasDerivAt (fun x => x - sigma) 1 r' := by
      have h := (hasDerivAt_id r').sub (hasDerivAt_const r' sigma)
      simp only [id_eq, sub_zero] at h; exact h
    have hin_A : HasDerivAt (fun x => x - r - sigma) 1 r' := by
      have h := ((hasDerivAt_id r').sub (hasDerivAt_const r' r)).sub (hasDerivAt_const r' sigma)
      simp only [id_eq, sub_zero] at h
      exact h.congr_deriv (by ring)
    have h2_A : HasDerivAt (fun x => (x - r - sigma) ^ 2) (2 * (r' - r - sigma)) r' :=
      (hin_A.pow 2).congr_deriv (by push_cast; ring)
    have h3_B : HasDerivAt (fun x => (x - sigma) ^ 3) (3 * (r' - sigma) ^ 2) r' :=
      (hin_B.pow 3).congr_deriv (by push_cast; ring)
    have h2_B : HasDerivAt (fun x => (x - sigma) ^ 2) (2 * (r' - sigma)) r' :=
      (hin_B.pow 2).congr_deriv (by push_cast; ring)
    have h3_A : HasDerivAt (fun x => (x - r - sigma) ^ 3) (3 * (r' - r - sigma) ^ 2) r' :=
      (hin_A.pow 3).congr_deriv (by push_cast; ring)
    have h4_B : HasDerivAt (fun x => (x - sigma) ^ 4) (4 * (r' - sigma) ^ 3) r' :=
      (hin_B.pow 4).congr_deriv (by push_cast; ring)
    have hA1 : HasDerivAt (fun x => α ^ 2 / 2 * (x - r - sigma) ^ 2)
        (α ^ 2 / 2 * (2 * (r' - r - sigma))) r' := h2_A.const_mul _
    have hA2 : HasDerivAt (fun x => α * β / 3 * (x - sigma) ^ 3)
        (α * β / 3 * (3 * (r' - sigma) ^ 2)) r' := h3_B.const_mul _
    have hA3 : HasDerivAt (fun x => α * β * r / 2 * (x - sigma) ^ 2)
        (α * β * r / 2 * (2 * (r' - sigma))) r' := h2_B.const_mul _
    have hA4 : HasDerivAt (fun x => α * β / 6 * (x - r - sigma) ^ 3)
        (α * β / 6 * (3 * (r' - r - sigma) ^ 2)) r' := h3_A.const_mul _
    have hA5 : HasDerivAt (fun x => β ^ 2 / 8 * (x - sigma) ^ 4)
        (β ^ 2 / 8 * (4 * (r' - sigma) ^ 3)) r' := h4_B.const_mul _
    have hA6 : HasDerivAt (fun x => β ^ 2 * r / 3 * (x - sigma) ^ 3)
        (β ^ 2 * r / 3 * (3 * (r' - sigma) ^ 2)) r' := h3_B.const_mul _
    have hA7 : HasDerivAt (fun x => β ^ 2 * r ^ 2 / 4 * (x - sigma) ^ 2)
        (β ^ 2 * r ^ 2 / 4 * (2 * (r' - sigma))) r' := h2_B.const_mul _
    have hchain := ((((((hA1.add hA2).sub hA3).add hA4).add hA5).sub hA6).add hA7)
    refine (hchain.congr_of_eventuallyEq ?_).congr_deriv ?_
    · exact Filter.Eventually.of_forall fun x => by simp [Pi.add_apply, Pi.sub_apply]
    · ring
  -- Apply FTC: integral = F(sigma) - F(r)
  rw [integral_eq_sub_of_hasDerivAt hderiv hint]
  -- Substitute all definitions and eta = pi*rho*sigma^3/6, then clear denominators
  simp only [hα_def, hβ_def, py_a0, py_a1, py_a3, q_prime_py, q_doubleprime_py, heta_def]
  have h1e : (1 : ℝ) - Real.pi * rho * sigma ^ 3 / 6 ≠ 0 := by
    have hlt := heta; rw [heta_def] at hlt; linarith
  field_simp [hsigma.ne', h1e]
  ring

/-! ### Contact-value algebraic corollary -/

/-- **Algebraic match: the PY contact-value target formula equals `Q'/(2πσ)`.**

`[LN]`'s hard-sphere contact-value formula (Eq. `g0_contact`),
`g0(R) = (1/(RΔ))·(R + πR²ξ2/(4Δ))`, specializes for a single component (`R_i=R_j=σ`,
`ξ2=ρσ²`, `Δ=1-η`) to exactly `Q'/(2πσ)` where `Q' = q_prime_py`. This lemma is the
mechanical half of `g0_HS_contact_value`'s target formula: it confirms the algebra, but does
**not** establish that `g0_HS(σ)` (the actual value of the abstractly-defined `oz_h` at
contact) equals this — that bridge needs Baxter's second relation (`h`-via-`Q`), not yet
formalized (see `todo_lean.md` Task OZ.9 / this file's module docstring). -/
theorem g0_contact_formula_eq_q_prime (eta sigma : ℝ) (hsigma : 0 < sigma) (heta : eta < 1) :
    q_prime_py eta sigma / (2 * Real.pi * sigma) = (1 + eta / 2) / (1 - eta) ^ 2 := by
  unfold q_prime_py
  have h1e : (1 : ℝ) - eta ≠ 0 := by linarith
  field_simp

end FMSA.HardSphere
