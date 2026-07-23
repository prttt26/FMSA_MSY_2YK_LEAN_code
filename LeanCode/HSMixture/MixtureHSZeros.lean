/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HSMixture.Q0Complex
import LeanCode.Analysis.BanachPoleFamily

/-!
# Task MZERO.1 (foundation) — `det(Q̂₀)` is not identically zero

Foundation for the N=2 HS-pole family: `det(Q0_mat_c s)` is a non-constant entire-type function, so its
zeros (the HS poles) cannot fill the plane.  The essential first ingredient is the **asymptotic**
`det(Q0_mat_c s) → 1` as real `s → +∞`: the diagonal Baxter entries → 1 and the off-diagonal *product*
→ 0 (its two exponential shifts `λ_{01}, λ_{10}` are opposite and cancel, `λ_{01}+λ_{10}=0`, leaving
`O(1/s²)`).  Hence `det` is eventually nonzero along the reals — not identically zero.

The **full** MZERO.1 (`det` has *infinitely many* complex zeros) is a POLE.3-scale Banach-contraction
effort (see `HardSphere/BaxterPoles.lean`); its **Route A (chord-Newton, MZERO.3–MZERO.7)** scaffold now
lives at the bottom of this file, culminating in `Q0_det_c_zeros_infinite` (`Set.Infinite`,
**conditional** on the MZERO.5 quantitative `|det′|`/`|det″|` bounds — supplied as explicit
numerically-validated hypotheses, exactly as `BaxterPoles` isolates its `hDball`/`hstep`).

## Results

* `Q0_mat_c_at_zero` — `Q0_mat_c 0 … = 1` (the Lean `s=0` value is the identity matrix, since the
  `φ`-terms are `0/0 = 0`); an immediate `det ≠ 0` witness.
* `q0_diag_c_tendsto_one` / `q0_offdiag_prod_tendsto_zero` — the diagonal → 1 and off-diagonal-product
  → 0 limits (`λ`-cancellation).
* `Q0_det_c_tendsto_one` — `det(Q0_mat_c (t:ℂ) …) → 1` as `t → +∞` (via `Q0_det_fin_two`).
* `Q0_det_c_not_identically_zero` — `∃ s, det(Q0_mat_c s …) ≠ 0`.

Status: ◑ foundation DONE (MZERO.1) axiom-clean; **Route-A Banach chain MZERO.3–MZERO.7 DONE (2026-07-15),
`sorry`-free**, conditional on the MZERO.5 magnitude bounds (hypotheses). Route B (MZERO.9–MZERO.11) staged.
-/

set_option linter.style.longLine false

open Filter Topology
open scoped Matrix
open FMSA.BanachPoleFamily

namespace FMSA.MixtureHSPoles

/-! ### `s = 0` value: `Q̂₀(0) = I` (Lean convention) ⇒ non-vanishing -/

/-- At the Lean value `s = 0`, `Q0_mat_c` is the identity matrix: the `φ₁,φ₂` terms are `0/0 = 0`, so
every entry collapses to `δ_{ij}`.  (This is the Lean division-convention value, not the analytic
`s→0` limit; it suffices to witness that `det∘Q0_mat_c` is not the zero function.) -/
theorem Q0_mat_c_at_zero {N : ℕ} (sigma : Fin N → ℂ) (rho_geo Qp Qpp : Fin N → Fin N → ℂ) :
    FMSA.Q0Complex.Q0_mat_c 0 sigma rho_geo Qp Qpp = 1 := by
  funext i j
  simp [FMSA.Q0Complex.Q0_mat_c, FMSA.Q0Complex.q0_entry_c, Matrix.one_apply]

/-- **MZERO.1 foundation — `det(Q̂₀)` is not identically zero.**  Witnessed at `s = 0`, where
`Q0_mat_c 0 = I` so `det = 1 ≠ 0`. -/
theorem Q0_det_c_not_identically_zero {N : ℕ} (sigma : Fin N → ℂ) (rho_geo Qp Qpp : Fin N → Fin N → ℂ) :
    ∃ s : ℂ, (FMSA.Q0Complex.Q0_mat_c s sigma rho_geo Qp Qpp).det ≠ 0 := by
  refine ⟨0, ?_⟩
  rw [Q0_mat_c_at_zero, Matrix.det_one]
  exact one_ne_zero

/-! ### Complex-limit helpers along the real axis -/

private lemma cofReal_inv_tendsto_zero : Tendsto (fun t : ℝ => ((t : ℂ))⁻¹) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h : (fun t : ℝ => ‖((t : ℂ))⁻¹‖) =ᶠ[atTop] fun t => t⁻¹ := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    simp [abs_of_pos ht]
  rw [tendsto_congr' h]
  exact tendsto_inv_atTop_zero

private lemma cexp_neg_mul_tendsto_zero {sig : ℝ} (hsig : 0 < sig) :
    Tendsto (fun t : ℝ => Complex.exp (-((t : ℂ) * (sig : ℂ)))) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hnorm : (fun t : ℝ => ‖Complex.exp (-((t : ℂ) * (sig : ℂ)))‖)
      = fun t => Real.exp (-(t * sig)) := by
    funext t
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re]
  rw [hnorm]
  have hb : Tendsto (fun t : ℝ => -(t * sig)) atTop atBot := by
    have : Tendsto (fun t : ℝ => t * sig) atTop atTop := Tendsto.atTop_mul_const hsig tendsto_id
    exact tendsto_neg_atTop_atBot.comp this
  exact Real.tendsto_exp_atBot.comp hb

/-- `φ₁ = (1 − sσ − e^{−sσ})/s² → 0` as real `s → +∞` (for `σ > 0`). -/
private lemma phi1c_tendsto {sig : ℝ} (hsig : 0 < sig) :
    Tendsto (fun t : ℝ =>
        (1 - (t : ℂ) * (sig : ℂ) - Complex.exp (-((t : ℂ) * (sig : ℂ)))) / (t : ℂ) ^ 2)
      atTop (𝓝 0) := by
  have hinv := cofReal_inv_tendsto_zero
  have h1 : Tendsto (fun t : ℝ => ((t : ℂ))⁻¹ ^ 2) atTop (𝓝 0) := by simpa using hinv.pow 2
  have h2 : Tendsto (fun t : ℝ => (sig : ℂ) * ((t : ℂ))⁻¹) atTop (𝓝 0) := by
    simpa using hinv.const_mul (sig : ℂ)
  have h3 : Tendsto (fun t : ℝ => Complex.exp (-((t : ℂ) * (sig : ℂ))) * ((t : ℂ))⁻¹ ^ 2)
      atTop (𝓝 0) := by simpa using (cexp_neg_mul_tendsto_zero hsig).mul h1
  have hsplit : (fun t : ℝ =>
        (1 - (t : ℂ) * (sig : ℂ) - Complex.exp (-((t : ℂ) * (sig : ℂ)))) / (t : ℂ) ^ 2)
      =ᶠ[atTop] fun t => ((t : ℂ))⁻¹ ^ 2 - (sig : ℂ) * ((t : ℂ))⁻¹
                          - Complex.exp (-((t : ℂ) * (sig : ℂ))) * ((t : ℂ))⁻¹ ^ 2 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    field_simp
  rw [tendsto_congr' hsplit]
  simpa using (h1.sub h2).sub h3

/-- `φ₂ = (1 − sσ + (sσ)²/2 − e^{−sσ})/s³ → 0` as real `s → +∞` (for `σ > 0`). -/
private lemma phi2c_tendsto {sig : ℝ} (hsig : 0 < sig) :
    Tendsto (fun t : ℝ =>
        (1 - (t : ℂ) * (sig : ℂ) + ((t : ℂ) * (sig : ℂ)) ^ 2 / 2
          - Complex.exp (-((t : ℂ) * (sig : ℂ)))) / (t : ℂ) ^ 3)
      atTop (𝓝 0) := by
  have hinv := cofReal_inv_tendsto_zero
  have h1 : Tendsto (fun t : ℝ => ((t : ℂ))⁻¹ ^ 3) atTop (𝓝 0) := by simpa using hinv.pow 3
  have h2 : Tendsto (fun t : ℝ => (sig : ℂ) * ((t : ℂ))⁻¹ ^ 2) atTop (𝓝 0) := by
    simpa using (by simpa using hinv.pow 2 : Tendsto (fun t : ℝ => ((t : ℂ))⁻¹ ^ 2) atTop (𝓝 0)).const_mul (sig : ℂ)
  have h3 : Tendsto (fun t : ℝ => (sig : ℂ) ^ 2 / 2 * ((t : ℂ))⁻¹) atTop (𝓝 0) := by
    simpa using hinv.const_mul ((sig : ℂ) ^ 2 / 2)
  have h4 : Tendsto (fun t : ℝ => Complex.exp (-((t : ℂ) * (sig : ℂ))) * ((t : ℂ))⁻¹ ^ 3)
      atTop (𝓝 0) := by simpa using (cexp_neg_mul_tendsto_zero hsig).mul h1
  have hsplit : (fun t : ℝ =>
        (1 - (t : ℂ) * (sig : ℂ) + ((t : ℂ) * (sig : ℂ)) ^ 2 / 2
          - Complex.exp (-((t : ℂ) * (sig : ℂ)))) / (t : ℂ) ^ 3)
      =ᶠ[atTop] fun t => ((t : ℂ))⁻¹ ^ 3 - (sig : ℂ) * ((t : ℂ))⁻¹ ^ 2
                          + (sig : ℂ) ^ 2 / 2 * ((t : ℂ))⁻¹
                          - Complex.exp (-((t : ℂ) * (sig : ℂ))) * ((t : ℂ))⁻¹ ^ 3 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    field_simp
  rw [tendsto_congr' hsplit]
  simpa using ((h1.sub h2).add h3).sub h4

/-- The Baxter bracket `Qp·φ₁ + Qpp·φ₂ → 0`. -/
private lemma bracket_tendsto_zero {sig : ℝ} (hsig : 0 < sig) (Qp Qpp : ℂ) :
    Tendsto (fun t : ℝ =>
        Qp * ((1 - (t : ℂ) * (sig : ℂ) - Complex.exp (-((t : ℂ) * (sig : ℂ)))) / (t : ℂ) ^ 2)
        + Qpp * ((1 - (t : ℂ) * (sig : ℂ) + ((t : ℂ) * (sig : ℂ)) ^ 2 / 2
            - Complex.exp (-((t : ℂ) * (sig : ℂ)))) / (t : ℂ) ^ 3))
      atTop (𝓝 0) := by
  simpa using ((phi1c_tendsto hsig).const_mul Qp).add ((phi2c_tendsto hsig).const_mul Qpp)

/-! ### Diagonal → 1 and off-diagonal product → 0 -/

/-- A diagonal Baxter entry (`λ = 0`, `δ = 1`) tends to `1` as real `s → +∞`. -/
theorem q0_diag_c_tendsto_one {sig : ℝ} (hsig : 0 < sig) (Qp Qpp rho : ℂ) :
    Tendsto (fun t : ℝ => FMSA.Q0Complex.q0_entry_c (t : ℂ) (sig : ℂ) 0 Qp Qpp rho 1) atTop (𝓝 1) := by
  have hb := bracket_tendsto_zero hsig Qp Qpp
  have key : Tendsto (fun t : ℝ => (1 : ℂ) - rho *
        (Qp * ((1 - (t : ℂ) * (sig : ℂ) - Complex.exp (-((t : ℂ) * (sig : ℂ)))) / (t : ℂ) ^ 2)
         + Qpp * ((1 - (t : ℂ) * (sig : ℂ) + ((t : ℂ) * (sig : ℂ)) ^ 2 / 2
             - Complex.exp (-((t : ℂ) * (sig : ℂ)))) / (t : ℂ) ^ 3)))
      atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (hb.const_mul rho)
  refine key.congr (fun t => ?_)
  simp only [FMSA.Q0Complex.q0_entry_c, zero_mul, neg_zero, Complex.exp_zero, mul_one]

/-- Algebraic core of the off-diagonal cancellation: `(0−a·eL·b)(0−c·eR·d) = a·c·b·d` when the two
exponential shifts cancel (`eL·eR = 1`). -/
private lemma offdiag_prod_eq (a b c d eL eR : ℂ) (he : eL * eR = 1) :
    (0 - a * eL * b) * (0 - c * eR * d) = a * c * b * d := by
  linear_combination (a * c * b * d) * he

/-- The off-diagonal Baxter *product* `q₀₁·q₁₀ → 0` as real `s → +∞`.  The two exponential shifts are
opposite (`λ_{01}+λ_{10}=0`) so they cancel, and each surviving Baxter bracket → 0. -/
theorem q0_offdiag_prod_tendsto_zero {sig0 sig1 : ℝ} (hs0 : 0 < sig0) (hs1 : 0 < sig1)
    (Qp01 Qpp01 rho01 Qp10 Qpp10 rho10 : ℂ) :
    Tendsto (fun t : ℝ =>
        FMSA.Q0Complex.q0_entry_c (t : ℂ) (sig0 : ℂ) (((sig1 : ℂ) - (sig0 : ℂ)) / 2) Qp01 Qpp01 rho01 0
      * FMSA.Q0Complex.q0_entry_c (t : ℂ) (sig1 : ℂ) (((sig0 : ℂ) - (sig1 : ℂ)) / 2) Qp10 Qpp10 rho10 0)
      atTop (𝓝 0) := by
  have hbr0 := bracket_tendsto_zero hs0 Qp01 Qpp01
  have hbr1 := bracket_tendsto_zero hs1 Qp10 Qpp10
  have key : Tendsto (fun t : ℝ => rho01 * rho10 *
        (Qp01 * ((1 - (t : ℂ) * (sig0 : ℂ) - Complex.exp (-((t : ℂ) * (sig0 : ℂ)))) / (t : ℂ) ^ 2)
         + Qpp01 * ((1 - (t : ℂ) * (sig0 : ℂ) + ((t : ℂ) * (sig0 : ℂ)) ^ 2 / 2
             - Complex.exp (-((t : ℂ) * (sig0 : ℂ)))) / (t : ℂ) ^ 3))
        * (Qp10 * ((1 - (t : ℂ) * (sig1 : ℂ) - Complex.exp (-((t : ℂ) * (sig1 : ℂ)))) / (t : ℂ) ^ 2)
         + Qpp10 * ((1 - (t : ℂ) * (sig1 : ℂ) + ((t : ℂ) * (sig1 : ℂ)) ^ 2 / 2
             - Complex.exp (-((t : ℂ) * (sig1 : ℂ)))) / (t : ℂ) ^ 3)))
      atTop (𝓝 0) := by
    simpa [mul_assoc] using (hbr0.mul hbr1).const_mul (rho01 * rho10)
  refine key.congr (fun t => ?_)
  have hexp : Complex.exp (-(((sig1 : ℂ) - (sig0 : ℂ)) / 2 * (t : ℂ)))
      * Complex.exp (-(((sig0 : ℂ) - (sig1 : ℂ)) / 2 * (t : ℂ))) = 1 := by
    rw [← Complex.exp_add,
        show -(((sig1 : ℂ) - (sig0 : ℂ)) / 2 * (t : ℂ)) + -(((sig0 : ℂ) - (sig1 : ℂ)) / 2 * (t : ℂ)) = 0
          by ring, Complex.exp_zero]
  simp only [FMSA.Q0Complex.q0_entry_c]
  rw [offdiag_prod_eq _ _ _ _ _ _ hexp]

/-! ### `det(Q̂₀) → 1` and non-vanishing -/

/-- **MZERO.1 foundation — `det(Q̂₀) → 1` as real `s → +∞`.**  The diagonal Baxter entries → 1 and the
off-diagonal product → 0 (opposite `λ`-shifts cancel), so `det = q₀₀q₁₁ − q₀₁q₁₀ → 1·1 − 0 = 1`.
Hence `det(Q̂₀)` is a non-constant function of `s` — the non-constancy foundation for the HS-pole
family.  (`σ` real & positive; `Q0_det_fin_two` = Mathlib `Matrix.det_fin_two`.) -/
theorem Q0_det_c_tendsto_one {sig : Fin 2 → ℝ} (hsig : ∀ i, 0 < sig i)
    (rho_geo Qp Qpp : Fin 2 → Fin 2 → ℂ) :
    Tendsto (fun t : ℝ =>
        (FMSA.Q0Complex.Q0_mat_c (t : ℂ) (fun i => (sig i : ℂ)) rho_geo Qp Qpp).det) atTop (𝓝 1) := by
  have hM : (fun t : ℝ =>
        (FMSA.Q0Complex.Q0_mat_c (t : ℂ) (fun i => (sig i : ℂ)) rho_geo Qp Qpp).det)
      = fun t : ℝ =>
        FMSA.Q0Complex.q0_entry_c (t : ℂ) (sig 0 : ℂ) 0 (Qp 0 0) (Qpp 0 0) (rho_geo 0 0) 1
          * FMSA.Q0Complex.q0_entry_c (t : ℂ) (sig 1 : ℂ) 0 (Qp 1 1) (Qpp 1 1) (rho_geo 1 1) 1
        - FMSA.Q0Complex.q0_entry_c (t : ℂ) (sig 0 : ℂ) (((sig 1 : ℂ) - (sig 0 : ℂ)) / 2)
              (Qp 0 1) (Qpp 0 1) (rho_geo 0 1) 0
          * FMSA.Q0Complex.q0_entry_c (t : ℂ) (sig 1 : ℂ) (((sig 0 : ℂ) - (sig 1 : ℂ)) / 2)
              (Qp 1 0) (Qpp 1 0) (rho_geo 1 0) 0 := by
    funext t
    simp [Matrix.det_fin_two, FMSA.Q0Complex.Q0_mat_c]
  rw [hM]
  have hd0 := q0_diag_c_tendsto_one (hsig 0) (Qp 0 0) (Qpp 0 0) (rho_geo 0 0)
  have hd1 := q0_diag_c_tendsto_one (hsig 1) (Qp 1 1) (Qpp 1 1) (rho_geo 1 1)
  have hoff := q0_offdiag_prod_tendsto_zero (hsig 0) (hsig 1)
    (Qp 0 1) (Qpp 0 1) (rho_geo 0 1) (Qp 1 0) (Qpp 1 0) (rho_geo 1 0)
  simpa using (hd0.mul hd1).sub hoff

/-! ### Holomorphy of `det(Q̂₀)` away from `s = 0` (for the eventual zero-counting) -/

/-- A Baxter entry `s ↦ q̂₀(s)` is complex-differentiable at every `s₀ ≠ 0` (the only singularities of
`q0_entry_c` are the removable `s=0` pole of the `φ₁,φ₂` factors). -/
theorem q0_entry_c_differentiableAt (sig lam Qp Qpp rho delta : ℂ) {s₀ : ℂ} (hs₀ : s₀ ≠ 0) :
    DifferentiableAt ℂ (fun s => FMSA.Q0Complex.q0_entry_c s sig lam Qp Qpp rho delta) s₀ := by
  have h2 : s₀ ^ 2 ≠ 0 := pow_ne_zero 2 hs₀
  have h3 : s₀ ^ 3 ≠ 0 := pow_ne_zero 3 hs₀
  unfold FMSA.Q0Complex.q0_entry_c
  fun_prop (disch := assumption)

/-- **MZERO.1 foundation — `det(Q̂₀)` is holomorphic away from `s = 0`.**  For `N = 2`, `s ↦ det(Q̂₀(s))`
is complex-differentiable at every `s₀ ≠ 0` (`Matrix.det_fin_two` of differentiable Baxter entries).
Together with `Q0_det_c_tendsto_one` (non-constancy) this is the holomorphic-and-non-constant setup a
zero-counting (Rouché / argument-principle / Banach-contraction) argument for the HS-pole family
starts from. -/
theorem Q0_det_c_differentiableAt (sigma : Fin 2 → ℂ) (rho_geo Qp Qpp : Fin 2 → Fin 2 → ℂ)
    {s₀ : ℂ} (hs₀ : s₀ ≠ 0) :
    DifferentiableAt ℂ (fun s => (FMSA.Q0Complex.Q0_mat_c s sigma rho_geo Qp Qpp).det) s₀ := by
  have hentry : ∀ i j : Fin 2,
      DifferentiableAt ℂ (fun s => FMSA.Q0Complex.Q0_mat_c s sigma rho_geo Qp Qpp i j) s₀ := by
    intro i j
    simp only [FMSA.Q0Complex.Q0_mat_c]
    exact q0_entry_c_differentiableAt _ _ _ _ _ _ hs₀
  have hdet : (fun s => (FMSA.Q0Complex.Q0_mat_c s sigma rho_geo Qp Qpp).det)
      = fun s => FMSA.Q0Complex.Q0_mat_c s sigma rho_geo Qp Qpp 0 0
            * FMSA.Q0Complex.Q0_mat_c s sigma rho_geo Qp Qpp 1 1
          - FMSA.Q0Complex.Q0_mat_c s sigma rho_geo Qp Qpp 0 1
            * FMSA.Q0Complex.Q0_mat_c s sigma rho_geo Qp Qpp 1 0 := by
    funext s; rw [Matrix.det_fin_two]
  rw [hdet]
  exact ((hentry 0 0).mul (hentry 1 1)).sub ((hentry 0 1).mul (hentry 1 0))

/-! ### MZERO.8 (Rouché route) — `det(Q̂₀)` is meromorphic (for the Jensen zero-counting) -/

/-- **MZERO.8 — `det(Q̂₀)` is meromorphic at every point.**  No analytic continuation is needed: each
`φ₁,φ₂ = (entire)/s^{2,3}` is `MeromorphicAt` everywhere as a *ratio of entire functions*, and
meromorphic functions are closed under `+,−,×,÷`; so the `det_fin_two` combination of Baxter entries
is `MeromorphicAt`.  (The Lean `0/0` value at `s=0` is irrelevant — `MeromorphicAt` only concerns a
punctured neighbourhood.)  This is the input the Rouché/Jensen zero-counting (MZERO.9–MZERO.11) needs. -/
theorem det_meromorphicAt (sigma : Fin 2 → ℂ) (rho_geo Qp Qpp : Fin 2 → Fin 2 → ℂ) (x : ℂ) :
    MeromorphicAt (fun s => (FMSA.Q0Complex.Q0_mat_c s sigma rho_geo Qp Qpp).det) x := by
  have hrw : (fun s => (FMSA.Q0Complex.Q0_mat_c s sigma rho_geo Qp Qpp).det)
      = fun s => FMSA.Q0Complex.Q0_mat_c s sigma rho_geo Qp Qpp 0 0
            * FMSA.Q0Complex.Q0_mat_c s sigma rho_geo Qp Qpp 1 1
          - FMSA.Q0Complex.Q0_mat_c s sigma rho_geo Qp Qpp 0 1
            * FMSA.Q0Complex.Q0_mat_c s sigma rho_geo Qp Qpp 1 0 := by
    funext s; rw [Matrix.det_fin_two]
  rw [hrw]
  simp only [FMSA.Q0Complex.Q0_mat_c, FMSA.Q0Complex.q0_entry_c]
  fun_prop

/-- **MZERO.8 — `det(Q̂₀)` is `MeromorphicOn` any set** (in particular every `Metric.closedBall 0 R`,
the domain Jensen's formula `MeromorphicOn.circleAverage_log_norm` is applied on in MZERO.11). -/
theorem det_meromorphicOn (sigma : Fin 2 → ℂ) (rho_geo Qp Qpp : Fin 2 → Fin 2 → ℂ) (U : Set ℂ) :
    MeromorphicOn (fun s => (FMSA.Q0Complex.Q0_mat_c s sigma rho_geo Qp Qpp).det) U :=
  fun x _ => det_meromorphicAt sigma rho_geo Qp Qpp x

/-! ## MZERO.1 Route A — Banach (chord-Newton) route to infinitely many zeros (MZERO.3–MZERO.7)

The generic chord-Newton engine (MZERO.3/MZERO.4/MZERO.6) and the **shared** `ChordPoleFamily` predicate +
`zeros_infinite_of_chordPoleFamily` (MZERO.7's infinitude) now live in
`LeanCode/Analysis/BanachPoleFamily.lean` (`open`ed above), so that **`det(Q̂₀_c)` (MZERO.5) and
`G_baxter` (POLE.3) instantiate the same predicate** and their remaining gaps close together (see
`todo_lean.md` Conditional-hypotheses table). This section only instantiates `F = detC`. The
quantitative MZERO.5 bounds (`‖1 − det′/Fp1‖ ≤ K`, `hstep`) enter as explicit hypotheses. -/

/-! ### MZERO.7 — `det` instantiation + infinitude via the shared predicate -/

/-- The complex determinant `det(Q̂₀(s))` for `N = 2` with real diameters cast to `ℂ`. -/
noncomputable def detC (sigma : Fin 2 → ℝ) (rho_geo Qp Qpp : Fin 2 → Fin 2 → ℂ) (s : ℂ) : ℂ :=
  (FMSA.Q0Complex.Q0_mat_c s (fun i => (sigma i : ℂ)) rho_geo Qp Qpp).det

/-- **MZERO.7, single disk.** Given a disk `(s1, r)` avoiding `s = 0`, a frozen nonzero derivative
`Fp1`, the chord Lipschitz bound (MZERO.5) and the good-guess self-map bound `hstep`, `detC` has a zero
in the disk. Chains `chordPhi_lipschitzOnWith` → `mapsTo…` → `chord_zero_exists_of_bounds`; the
differentiability of `detC` on the ball is discharged from `Q0_det_c_differentiableAt` (needs `0∉ball`). -/
theorem det_zero_exists_for_n (sigma : Fin 2 → ℝ) (rho_geo Qp Qpp : Fin 2 → Fin 2 → ℂ)
    (s1 : ℂ) (r : ℝ) (hr : 0 < r) (h0 : (0 : ℂ) ∉ Metric.closedBall s1 r)
    (Fp1 : ℂ) (hFp1 : Fp1 ≠ 0) (K : NNReal) (hK1 : K < 1)
    (hbound : ∀ s ∈ Metric.closedBall s1 r,
        ‖1 - deriv (detC sigma rho_geo Qp Qpp) s / Fp1‖ ≤ K)
    (hstep : ‖detC sigma rho_geo Qp Qpp s1 / Fp1‖ ≤ r * (1 - K)) :
    ∃ s ∈ Metric.closedBall s1 r, detC sigma rho_geo Qp Qpp s = 0 := by
  have hderiv : ∀ s ∈ Metric.closedBall s1 r,
      HasDerivAt (detC sigma rho_geo Qp Qpp) (deriv (detC sigma rho_geo Qp Qpp) s) s := by
    intro s hs
    have hsne : s ≠ 0 := by rintro rfl; exact h0 hs
    exact (Q0_det_c_differentiableAt (fun i => (sigma i : ℂ)) rho_geo Qp Qpp hsne).hasDerivAt
  have hLip := chordPhi_lipschitzOnWith (F := detC sigma rho_geo Qp Qpp)
    (F' := deriv (detC sigma rho_geo Qp Qpp)) (Fp1 := Fp1) (s1 := s1) (r := r) K hderiv hbound
  have hstep' : dist s1 (chordPhi (detC sigma rho_geo Qp Qpp) Fp1 s1) ≤ r * (1 - K) := by
    simp only [chordPhi, dist_eq_norm, sub_sub_cancel]
    exact hstep
  have hMapsTo := mapsTo_closedBall_of_lipschitzOnWith_of_dist_le
    (chordPhi (detC sigma rho_geo Qp Qpp) Fp1) s1 r hr.le K hLip hstep'
  exact chord_zero_exists_of_bounds (detC sigma rho_geo Qp Qpp) Fp1 s1 r hr hFp1 K hK1 hMapsTo hLip

/-- **MZERO.7 — `det(Q̂₀)` has infinitely many complex zeros (N=2), conditional on the MZERO.5 bounds.**
A thin instantiation of the **shared** `zeros_infinite_of_chordPoleFamily`: package the explicit
det-family data (`det` differentiability off `s=0` from `Q0_det_c_differentiableAt`; the Im-spacing
`(s1 n).im = π·n` with `r < π/2` ⇒ pairwise `>2r` separation) into a `ChordPoleFamily detC`. The
quantitative hyps `hbound` (`‖1 − det′/Fp1‖ ≤ K`) + `hstep` (self-map good-guess) are numerically
validated by MZERO.2 (`K ≈ 0.30`); this is the **same obligation `G_baxter` (POLE.3) carries** — one
`ChordPoleFamily`-construction technique closes both. -/
theorem Q0_det_c_zeros_infinite (sigma : Fin 2 → ℝ) (rho_geo Qp Qpp : Fin 2 → Fin 2 → ℂ)
    {r : ℝ} (hr : 0 < r) (hrspace : r < Real.pi / 2) (N : ℕ) (s1 : ℕ → ℂ) (Fp1 : ℕ → ℂ)
    (hk1im : ∀ n, N ≤ n → (s1 n).im = Real.pi * n)
    (h0 : ∀ n, N ≤ n → (0 : ℂ) ∉ Metric.closedBall (s1 n) r)
    (hFp1 : ∀ n, N ≤ n → Fp1 n ≠ 0) (K : NNReal) (hK1 : K < 1)
    (hbound : ∀ n, N ≤ n → ∀ s ∈ Metric.closedBall (s1 n) r,
        ‖1 - deriv (detC sigma rho_geo Qp Qpp) s / Fp1 n‖ ≤ K)
    (hstep : ∀ n, N ≤ n → ‖detC sigma rho_geo Qp Qpp (s1 n) / Fp1 n‖ ≤ r * (1 - K)) :
    {s : ℂ | detC sigma rho_geo Qp Qpp s = 0}.Infinite := by
  apply zeros_infinite_of_chordPoleFamily
  exact
    { N := N
      s1 := s1
      Fp1 := Fp1
      F' := deriv (detC sigma rho_geo Qp Qpp)
      r := r
      K := K
      hr := hr
      hK1 := hK1
      hFp1 := hFp1
      hderiv := fun n hn s hs => by
        have hsne : s ≠ 0 := by rintro rfl; exact h0 n hn hs
        exact (Q0_det_c_differentiableAt (fun i => (sigma i : ℂ)) rho_geo Qp Qpp hsne).hasDerivAt
      hbound := hbound
      hstep := hstep
      hsep := fun m n hm hn hmn => by
        have him : (s1 m).im - (s1 n).im = Real.pi * ((m : ℝ) - (n : ℝ)) := by
          rw [hk1im m hm, hk1im n hn]; ring
        have hnat : (1 : ℝ) ≤ |((m : ℝ) - (n : ℝ))| := by
          have hmm : (m : ℤ) - (n : ℤ) ≠ 0 := sub_ne_zero.mpr (fun h => hmn (by exact_mod_cast h))
          have h1 : (1 : ℤ) ≤ |(m : ℤ) - (n : ℤ)| := Int.one_le_abs hmm
          have h2 : ((|(m : ℤ) - (n : ℤ)| : ℤ) : ℝ) = |((m : ℝ) - (n : ℝ))| := by push_cast; ring
          rw [← h2]; exact_mod_cast h1
        have himge : Real.pi ≤ |((s1 m).im - (s1 n).im)| := by
          rw [him, abs_mul, abs_of_pos Real.pi_pos]
          calc Real.pi = Real.pi * 1 := (mul_one _).symm
            _ ≤ Real.pi * |((m : ℝ) - (n : ℝ))| := mul_le_mul_of_nonneg_left hnat Real.pi_pos.le
        have hdistim : |((s1 m - s1 n).im)| ≤ ‖s1 m - s1 n‖ := Complex.abs_im_le_norm _
        rw [Complex.sub_im] at hdistim
        rw [dist_eq_norm]
        have h2r : 2 * r < Real.pi := by linarith [hrspace]
        linarith [himge, hdistim, h2r] }

/-- **MML.5-concrete growth witness (mixture pole family).** The same `ChordPoleFamily detC` as
`Q0_det_c_zeros_infinite`, but exposing an injective zero family `g` with a **positive linear growth**
`π·n + (π·N − r) ≤ ‖g n‖` (via `exists_zero_family_growth_of_chordPoleFamily`): the centres satisfy
`‖s1 n‖ ≥ |Im(s1 n)| = π·n` (`Complex.abs_im_le_norm` + `hk1im`), and each zero is within `r` of its
centre. With `N ≥ 1` and `r < π/2` the offset `π·N − r > π/2 > 0`. This is exactly the linear-growth
hypothesis `mixHS_summable_of_growth` (MML.5) consumes; conditional on the MZERO.5 bounds, like
`Q0_det_c_zeros_infinite`. -/
theorem Q0_det_c_pole_family_growth (sigma : Fin 2 → ℝ) (rho_geo Qp Qpp : Fin 2 → Fin 2 → ℂ)
    {r : ℝ} (hr : 0 < r) (hrspace : r < Real.pi / 2) (N : ℕ) (hN : 1 ≤ N) (s1 : ℕ → ℂ) (Fp1 : ℕ → ℂ)
    (hk1im : ∀ n, N ≤ n → (s1 n).im = Real.pi * n)
    (h0 : ∀ n, N ≤ n → (0 : ℂ) ∉ Metric.closedBall (s1 n) r)
    (hFp1 : ∀ n, N ≤ n → Fp1 n ≠ 0) (K : NNReal) (hK1 : K < 1)
    (hbound : ∀ n, N ≤ n → ∀ s ∈ Metric.closedBall (s1 n) r,
        ‖1 - deriv (detC sigma rho_geo Qp Qpp) s / Fp1 n‖ ≤ K)
    (hstep : ∀ n, N ≤ n → ‖detC sigma rho_geo Qp Qpp (s1 n) / Fp1 n‖ ≤ r * (1 - K)) :
    ∃ g : ℕ → ℂ, Function.Injective g ∧ (∀ n, detC sigma rho_geo Qp Qpp (g n) = 0) ∧
      ∃ cc dd : ℝ, 0 < cc ∧ 0 < dd ∧ ∀ n : ℕ, cc * (n : ℝ) + dd ≤ ‖g n‖ := by
  have hcentre : ∀ n, N ≤ n → Real.pi * (n : ℝ) + 0 ≤ ‖s1 n‖ := by
    intro n hn
    have himle : |(s1 n).im| ≤ ‖s1 n‖ := Complex.abs_im_le_norm (s1 n)
    rw [hk1im n hn, abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.pi * (n : ℝ))] at himle
    linarith [himle]
  obtain ⟨g, hinj, hzero, hg⟩ :=
    exists_zero_family_growth_of_chordPoleFamily
      (F := detC sigma rho_geo Qp Qpp)
      { N := N
        s1 := s1
        Fp1 := Fp1
        F' := deriv (detC sigma rho_geo Qp Qpp)
        r := r
        K := K
        hr := hr
        hK1 := hK1
        hFp1 := hFp1
        hderiv := fun n hn s hs => by
          have hsne : s ≠ 0 := by rintro rfl; exact h0 n hn hs
          exact (Q0_det_c_differentiableAt (fun i => (sigma i : ℂ)) rho_geo Qp Qpp hsne).hasDerivAt
        hbound := hbound
        hstep := hstep
        hsep := fun m n hm hn hmn => by
          have him : (s1 m).im - (s1 n).im = Real.pi * ((m : ℝ) - (n : ℝ)) := by
            rw [hk1im m hm, hk1im n hn]; ring
          have hnat : (1 : ℝ) ≤ |((m : ℝ) - (n : ℝ))| := by
            have hmm : (m : ℤ) - (n : ℤ) ≠ 0 := sub_ne_zero.mpr (fun h => hmn (by exact_mod_cast h))
            have h1 : (1 : ℤ) ≤ |(m : ℤ) - (n : ℤ)| := Int.one_le_abs hmm
            have h2 : ((|(m : ℤ) - (n : ℤ)| : ℤ) : ℝ) = |((m : ℝ) - (n : ℝ))| := by push_cast; ring
            rw [← h2]; exact_mod_cast h1
          have himge : Real.pi ≤ |((s1 m).im - (s1 n).im)| := by
            rw [him, abs_mul, abs_of_pos Real.pi_pos]
            calc Real.pi = Real.pi * 1 := (mul_one _).symm
              _ ≤ Real.pi * |((m : ℝ) - (n : ℝ))| := mul_le_mul_of_nonneg_left hnat Real.pi_pos.le
          have hdistim : |((s1 m - s1 n).im)| ≤ ‖s1 m - s1 n‖ := Complex.abs_im_le_norm _
          rw [Complex.sub_im] at hdistim
          rw [dist_eq_norm]
          have h2r : 2 * r < Real.pi := by linarith [hrspace]
          linarith [himge, hdistim, h2r] }
      (c := Real.pi) (d := 0) Real.pi_pos hcentre
  refine ⟨g, hinj, hzero, Real.pi, Real.pi * (N : ℝ) - r, Real.pi_pos, ?_, fun n => ?_⟩
  · have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hpiN : Real.pi ≤ Real.pi * (N : ℝ) := by
      have := mul_le_mul_of_nonneg_left hN1 Real.pi_pos.le
      simpa using this
    linarith [Real.pi_pos, hrspace, hpiN]
  · calc Real.pi * (n : ℝ) + (Real.pi * (N : ℝ) - r)
        = Real.pi * (n : ℝ) + (Real.pi * (N : ℝ) + 0 - r) := by ring
      _ ≤ ‖g n‖ := hg n

/-! ### MZERO.5a — the structural bridge: `det_c` is an `e^{±λs}`-free 2-frequency exp-polynomial -/

/-- **MZERO.5a bridge.** `det(Q̂₀_c)` has **no `e^{±λs}` blow-up**: the off-diagonal exponential shifts
cancel (`λ_{01}+λ_{10}=0`), leaving `det_c` as `(diag₀)(diag₁) − ρ₀₁ρ₁₀·(bracket₀)(bracket₁)` — a
combination of the Baxter brackets `Q'·φ₁(σⱼ,s)+Q''·φ₂(σⱼ,s)` (each only in `e^{−sσⱼ}`, `1/sᵏ`). So
`det_c` lies in the **same exponential-polynomial class as `G_baxter`** (built from the same
`mAux/nAux(sσⱼ)` Baxter auxiliaries), which is why they instantiate the *same* `ChordPoleFamily`
obligation (`Q0_det_c_zeros_infinite` ↔ POLE.3): one asymptotic-family technique closes both. -/
theorem detC_lam_free (sigma : Fin 2 → ℝ) (rho_geo Qp Qpp : Fin 2 → Fin 2 → ℂ) (s : ℂ) :
    detC sigma rho_geo Qp Qpp s =
      (1 - rho_geo 0 0 *
        (Qp 0 0 * ((1 - s * (sigma 0 : ℂ) - Complex.exp (-(s * (sigma 0 : ℂ)))) / s ^ 2) +
         Qpp 0 0 * ((1 - s * (sigma 0 : ℂ) + (s * (sigma 0 : ℂ)) ^ 2 / 2
            - Complex.exp (-(s * (sigma 0 : ℂ)))) / s ^ 3)))
    * (1 - rho_geo 1 1 *
        (Qp 1 1 * ((1 - s * (sigma 1 : ℂ) - Complex.exp (-(s * (sigma 1 : ℂ)))) / s ^ 2) +
         Qpp 1 1 * ((1 - s * (sigma 1 : ℂ) + (s * (sigma 1 : ℂ)) ^ 2 / 2
            - Complex.exp (-(s * (sigma 1 : ℂ)))) / s ^ 3)))
    - rho_geo 0 1 * rho_geo 1 0 *
        (Qp 0 1 * ((1 - s * (sigma 0 : ℂ) - Complex.exp (-(s * (sigma 0 : ℂ)))) / s ^ 2) +
         Qpp 0 1 * ((1 - s * (sigma 0 : ℂ) + (s * (sigma 0 : ℂ)) ^ 2 / 2
            - Complex.exp (-(s * (sigma 0 : ℂ)))) / s ^ 3))
      * (Qp 1 0 * ((1 - s * (sigma 1 : ℂ) - Complex.exp (-(s * (sigma 1 : ℂ)))) / s ^ 2) +
         Qpp 1 0 * ((1 - s * (sigma 1 : ℂ) + (s * (sigma 1 : ℂ)) ^ 2 / 2
            - Complex.exp (-(s * (sigma 1 : ℂ)))) / s ^ 3)) := by
  unfold detC FMSA.Q0Complex.Q0_mat_c
  rw [Matrix.det_fin_two]
  simp only [FMSA.Q0Complex.q0_entry_c, Fin.isValue, Fin.reduceEq, ↓reduceIte]
  have hd0 : ((sigma 0 : ℂ) - (sigma 0 : ℂ)) / 2 = 0 := by ring
  have hd1 : ((sigma 1 : ℂ) - (sigma 1 : ℂ)) / 2 = 0 := by ring
  have hexp : Complex.exp (-(((sigma 1 : ℂ) - (sigma 0 : ℂ)) / 2 * s))
            * Complex.exp (-(((sigma 0 : ℂ) - (sigma 1 : ℂ)) / 2 * s)) = 1 := by
    rw [← Complex.exp_add,
        show -(((sigma 1 : ℂ) - (sigma 0 : ℂ)) / 2 * s) + -(((sigma 0 : ℂ) - (sigma 1 : ℂ)) / 2 * s)
          = 0 by ring, Complex.exp_zero]
  rw [hd0, hd1]
  simp only [zero_mul, neg_zero, Complex.exp_zero]
  linear_combination (-(rho_geo 0 1 * rho_geo 1 0 *
    (Qp 0 1 * ((1 - s * (sigma 0 : ℂ) - Complex.exp (-(s * (sigma 0 : ℂ)))) / s ^ 2) +
     Qpp 0 1 * ((1 - s * (sigma 0 : ℂ) + (s * (sigma 0 : ℂ)) ^ 2 / 2
        - Complex.exp (-(s * (sigma 0 : ℂ)))) / s ^ 3)) *
    (Qp 1 0 * ((1 - s * (sigma 1 : ℂ) - Complex.exp (-(s * (sigma 1 : ℂ)))) / s ^ 2) +
     Qpp 1 0 * ((1 - s * (sigma 1 : ℂ) + (s * (sigma 1 : ℂ)) ^ 2 / 2
        - Complex.exp (-(s * (sigma 1 : ℂ)))) / s ^ 3)))) * hexp

end FMSA.MixtureHSPoles
