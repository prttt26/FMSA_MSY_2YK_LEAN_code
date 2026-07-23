/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HSMixture.MixtureNoSpinodal
import LeanCode.HardSphere.BaxterNoSpinodalEquiv
import LeanCode.HardSphere.BaxterZeros

/-!
# The `n = 1` bridge — the mixture no-spinodal axiom is a THEOREM at one component

`pyhs_mixture_no_spinodal` (`MixtureNoSpinodal.lean`) is the project's only physics axiom, and it is
**pre-placed with no consumer**.  That is a specific hazard: a consumer-less axiom has no downstream
use that could ever expose a mis-statement, and this project has had **four** axioms that were false
*as stated* — each caught only by a proof attempt, never by `#print axioms`, the build, or review.

This file supplies the one mechanically checkable soundness test available: the `n = 1` slice, where
the mixture claim must reduce to the *proven* scalar `pyhs_no_spinodal`.  It does, exactly:

`pyhs_mixture_no_spinodal_n1` has the **same statement as the axiom specialised to `Fin 1`** and is
proved *without* the axiom.  So on that slice the axiom is not merely consistent with an established
fact — it is redundant.

The chain, in four steps:

1. **Moments** (`xi2_n1`, `etaMix_n1`): `ξ₂ = ρ₀σ₀²` and `η = πρ₀σ₀³/6` — the latter is literally
   the scalar `heta_def` that `pyhs_no_spinodal` requires.
2. **Coefficients** (`Q0phys_n1`, `Qppphys_n1`, `rhoGeoPhys_n1`): the Lebowitz/Baxter *mixture*
   coefficients at `n = 1` are the scalar PY ones, `q_prime_py`/`q_doubleprime_py`.  This direction
   closes a loop — `q_doubleprime_py`'s own docstring derives it *from* the multicomponent formula,
   so the two are now provably the same object rather than two transcriptions of one paper.
3. **Kernels** (`qhat_complex_eq_mixture_kernel`): the mixture Laplace kernels are the scalar
   transform.  With `s = ik`, `(1−sσ−e^{−sσ})/s² = −∫₀^σ(σ−r)e^{−sr}dr` and
   `(1−sσ+(sσ)²/2−e^{−sσ})/s³ = ∫₀^σ(σ−r)²/2·e^{−sr}dr`, which is exactly how `q0_poly` is built.
4. **Determinant** (`Q0_mat_c_phys_n1_det`): a `Fin 1` determinant is its single entry, whose
   off-diagonal shift `λ₀₀ = (σ₀−σ₀)/2` vanishes and whose `δ₀₀ = 1`.

Assembling: `det Q̂₀(ik) = 1 − Q̂(k)`, and `Q̂(k) ≠ 1` is the scalar theorem.
-/

namespace FMSA.MixtureNoSpinodalN1

open FMSA.HardSphere FMSA.MatrixQ0 FMSA.MixtureNoSpinodal FMSA.Q0Complex

noncomputable section

/-! ### Step 1 — the mixture moments at `n = 1` -/

/-- `ξ₂ = Σᵢ ρᵢσᵢ²` collapses to the single term. -/
theorem xi2_n1 (rho sigma : Fin 1 → ℝ) : xi2 rho sigma = rho 0 * sigma 0 ^ 2 := by
  simp [xi2]

/-- `η = (π/6)Σᵢ ρᵢσᵢ³` collapses to **exactly the scalar coupling** `η = πρσ³/6` — the `heta_def`
hypothesis of `pyhs_no_spinodal`. -/
theorem etaMix_n1 (rho sigma : Fin 1 → ℝ) :
    etaMix rho sigma = Real.pi * rho 0 * sigma 0 ^ 3 / 6 := by
  simp [etaMix]
  ring

/-- The geometric-mean density `√(ρ₀ρ₀)` is `ρ₀`. -/
theorem rhoGeoPhys_n1 {rho : Fin 1 → ℝ} (hrho : 0 ≤ rho 0) : rhoGeoPhys rho 0 0 = rho 0 :=
  Real.sqrt_mul_self hrho

/-! ### Step 2 — the physical Baxter coefficients at `n = 1` are the scalar PY ones -/

/-- **`Q'ᵢⱼ` at `n = 1` is the scalar `q_prime_py`.**  `(2π/Δ)(R + πR²ξ₂/(4Δ))` with `R = σ₀`,
`ξ₂ = ρ₀σ₀²` and `πρ₀σ₀³ = 6η` collapses to `πσ(2+η)/(1−η)²`. -/
theorem Q0phys_n1 {rho sigma : Fin 1 → ℝ} (hsigma : 0 < sigma 0) (heta : etaMix rho sigma ≠ 1) :
    Q0phys rho sigma 0 0 = q_prime_py (etaMix rho sigma) (sigma 0) := by
  have hvac : 1 - etaMix rho sigma ≠ 0 := sub_ne_zero.mpr (Ne.symm heta)
  have hrho_eq : rho 0 = 6 * etaMix rho sigma / (Real.pi * sigma 0 ^ 3) := by
    rw [etaMix_n1]
    field_simp [Real.pi_ne_zero, pow_ne_zero 3 hsigma.ne']
  unfold Q0phys vacMix q_prime_py
  rw [xi2_n1, hrho_eq]
  field_simp [Real.pi_ne_zero, pow_ne_zero 3 hsigma.ne']
  ring

/-- **`Q''ⱼ` at `n = 1` is the scalar `q_doubleprime_py`.**  `(2π/Δ)(1 + πRξ₂/(2Δ))` collapses to
`2π(1+2η)/(1−η)²`.  Note `q_doubleprime_py`'s docstring *derives* it from this very formula — this
lemma turns that prose derivation into a machine-checked identity. -/
theorem Qppphys_n1 {rho sigma : Fin 1 → ℝ} (hsigma : 0 < sigma 0) (heta : etaMix rho sigma ≠ 1) :
    Qppphys rho sigma 0 0 = q_doubleprime_py (etaMix rho sigma) := by
  have hvac : 1 - etaMix rho sigma ≠ 0 := sub_ne_zero.mpr (Ne.symm heta)
  have hrho_eq : rho 0 = 6 * etaMix rho sigma / (Real.pi * sigma 0 ^ 3) := by
    rw [etaMix_n1]
    field_simp [Real.pi_ne_zero, pow_ne_zero 3 hsigma.ne']
  unfold Qppphys vacMix q_doubleprime_py
  rw [xi2_n1, hrho_eq]
  field_simp [Real.pi_ne_zero, pow_ne_zero 3 hsigma.ne']
  ring

/-! ### Step 3 — the mixture Laplace kernels reassemble the scalar transform -/

/-- **The scalar `Q̂(k)` written in the mixture's two Laplace kernels.**  With `s = ik`, the kernels
`(1−sσ−e^{−sσ})/s²` and `(1−sσ+(sσ)²/2−e^{−sσ})/s³` are `−∫₀^σ(σ−r)e^{−sr}dr` and
`∫₀^σ(σ−r)²/2·e^{−sr}dr`; since `q0_poly r = ρ(Q'(r−σ) + Q''(r−σ)²/2)`, their `Q'`/`Q''` combination
is exactly `Q̂ = ∫₀^σ q0_poly(r)e^{−ikr}dr`.  Both sides are rational in `s` and `e^{−sσ}`, so this
is `Qhat_complex_formula` plus field algebra — `Complex.I` never needs `I² = −1`. -/
theorem qhat_complex_eq_mixture_kernel (eta sigma rho : ℝ) (hsigma : 0 < sigma) {k : ℂ}
    (hk : k ≠ 0) :
    Qhat_complex eta sigma rho k
      = (rho : ℂ) *
        ((q_prime_py eta sigma : ℂ) *
            ((1 - Complex.I * k * sigma - Complex.exp (-(Complex.I * k * sigma)))
              / (Complex.I * k) ^ 2) +
          (q_doubleprime_py eta : ℂ) *
            ((1 - Complex.I * k * sigma + (Complex.I * k * sigma) ^ 2 / 2
                - Complex.exp (-(Complex.I * k * sigma))) / (Complex.I * k) ^ 3)) := by
  have hIk : Complex.I * k ≠ 0 := mul_ne_zero Complex.I_ne_zero hk
  have hexp : (-Complex.I * k * sigma) = -(Complex.I * k * sigma) := by ring
  rw [Qhat_complex_formula eta sigma rho hsigma hk, hexp]
  push_cast
  field_simp
  ring

/-! ### Step 4 — the `n = 1` determinant is the single entry -/

/-- A `Fin 1` determinant is its single entry; the off-diagonal shift `λ₀₀ = (σ₀−σ₀)/2` vanishes and
`δ₀₀ = 1`. -/
theorem Q0_mat_c_phys_n1_det {sigma rho : Fin 1 → ℝ} (s : ℂ) :
    (Q0_mat_c_phys s sigma rho).det
      = 1 - (rhoGeoPhys rho 0 0 : ℂ) *
          ((Q0phys rho sigma 0 0 : ℂ) *
              ((1 - s * sigma 0 - Complex.exp (-(s * sigma 0))) / s ^ 2) +
            (Qppphys rho sigma 0 0 : ℂ) *
              ((1 - s * sigma 0 + (s * sigma 0) ^ 2 / 2
                - Complex.exp (-(s * sigma 0))) / s ^ 3)) := by
  rw [Matrix.det_fin_one]
  unfold Q0_mat_c_phys Q0_mat_c q0_entry_c
  simp

/-! ### Assembly -/

/-- **The `n = 1` bridge: `pyhs_mixture_no_spinodal` specialised to one component is a THEOREM.**

Same statement as the axiom at `n = 1`, proved from the *scalar* `pyhs_no_spinodal` via
`qhat_complex_ne_one_of_real` — the axiom itself is **not** used.  `det Q̂₀(ik) = 1 − Q̂(k)`, and
the scalar theorem says `Q̂(k) ≠ 1`.

This is the soundness test the axiom otherwise lacks: it pins the quantifiers, the `k ≠ 0`
exclusion, the `etaMix` coupling and the physical-coefficient choice against a fact that is already
proved. -/
theorem pyhs_mixture_no_spinodal_n1 {sigma rho : Fin 1 → ℝ}
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 < rho i)
    (heta : etaMix rho sigma < 1) {k : ℝ} (hk : k ≠ 0) :
    (Q0_mat_c_phys (Complex.I * (k : ℂ)) sigma rho).det ≠ 0 := by
  have hs0 : 0 < sigma 0 := hsigma 0
  have hr0 : 0 < rho 0 := hrho 0
  have heta_def : etaMix rho sigma = Real.pi * rho 0 * sigma 0 ^ 3 / 6 := etaMix_n1 rho sigma
  have heta0 : 0 < etaMix rho sigma := by rw [heta_def]; positivity
  have hIk : Complex.I * (k : ℂ) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hk)
  -- the determinant is `1 − Q̂(k)`
  have hdet : (Q0_mat_c_phys (Complex.I * (k : ℂ)) sigma rho).det
      = 1 - Qhat_complex (etaMix rho sigma) (sigma 0) (rho 0) (k : ℂ) := by
    rw [Q0_mat_c_phys_n1_det, qhat_complex_eq_mixture_kernel _ _ _ hs0
      (Complex.ofReal_ne_zero.mpr hk), rhoGeoPhys_n1 hr0.le, Q0phys_n1 hs0 heta.ne,
      Qppphys_n1 hs0 heta.ne]
  rw [hdet, sub_ne_zero]
  exact fun h => qhat_complex_ne_one_of_real heta0 heta hs0 hr0 heta_def hk h.symm

end

end FMSA.MixtureNoSpinodalN1
