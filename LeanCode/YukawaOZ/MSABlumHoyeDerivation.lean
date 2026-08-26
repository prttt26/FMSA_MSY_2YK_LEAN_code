/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.YukawaOZ.MSADCFTransform
import LeanCode.YukawaOZ.MSABaxterTransform
import LeanCode.YukawaOZ.MSABlumHoyeSystem

/-!
# Deriving the Blum–Høye MSA equations (29)/(33) — leg 3 (`N = 1`)

**Goal (transcription → derivation).**  Turn the scalar Blum–Høye equations, currently POSITED as
hypotheses `h29 : Dt·bhF(z) = 2πK/z` and `h33 : 2π·G·bhF(z) = bhP` (`MSAFullFactorization.lean`),
into THEOREMS derived from the Ornstein–Zernike + MSA-closure + Baxter-factorization physics.  This
shrinks the trusted transcription surface (currently the whole `(Dt,G)` 2×2 system) down to the
recognised OZ/Baxter objects.

**The derivation (waisman_msa_closed_form.md §6, §7d).**  (29) is the *exterior-closure
coefficient-matching / residue* condition.  The MSA closure sets the exterior direct correlation
function `c(r > σ) = K·e^{−z(r−σ)}/r` (contact-normalised Yukawa).  Baxter's real-space relation
(Eq. 8) is `2πr·c(r) = −q′(r) + ρ∫q′(t)q(r+t)dt` with the **non-compact** Baxter function
`q(r) = q0_poly(r) + Dt·e^{−zr}` (`msaBaxterFn`).  At `r > σ`:

* LHS `= 2πK·e^{zσ}·e^{−zr}` (the pure Yukawa tail);
* RHS `= e^{−zr}·[Σ_l Dt_il(δ_lj − ρ_l Q̂_jl(z))]` (the Baxter-tail response).

Matching the coefficient of `e^{−zr}` gives **(29)**; the Laplace moment `ĝ(z)` of the same relation
gives **(33)** (whose `K = 0` base is already the proved `bh_base_eq`).  Equivalently
`Dt = (2π/z)·K/bhF(z)` — the amplitude is the coupling divided by the full Baxter factor at the
Yukawa rate (§6, the "exact-MSA self-consistency").

**Roadmap / milestones.**
1. ✅ **the exterior-closure LHS, in real space and Laplace** (this file): `cMSAtail_exterior_lhs`
   and `cMSAtail_lhs_laplace` — `2πr·c(r>1)` is the pure Yukawa `2πK·e^{−z(r−1)}`, whose Laplace
   `∫_{r>1}(…)e^{−sr} = 2πK·e^{−s}/(s+z)` carries the `1/(s+z)` pole with residue ∝ K.  This is the
   **K-side** of the coefficient match.
2. ◑ the **exterior non-compact-`q` Baxter relation** (the RHS of Eq. 8 at `r > 1` for
   `q = q0_poly + Dt·e^{−zr}`) — STARTED: `tail_tail_conv` computes the tail–tail self-overlap
   `∫_{t>0} e^{−zt}·e^{−z(r+t)} = e^{−zr}/(2z)`, the source of the `Dt²` (doubly-propagated) term.
   plus `exp_shift_factor` reduces the poly–tail cross overlap to a core Laplace moment.  These two
   overlap integrals are the *convention-independent* components.  ✅ the `Q̂` integral↔closed-form
   **faithfulness bridge is now a theorem** (milestone 2b below): `qhat0_eq_laplace_q0poly` proves
   `ρ·Q̂₀ = ∫₀¹ q0_poly·e^{−zr}` — the closed-form `Q̂₀ = φ₁q′+φ₂A` (`MSABlumHoyeSystem`) IS the
   real-space Baxter transform, not just numerically so.  The convention is also pinned: Blum & Høye
   Eq. (10) has `Q(r) = Q⁰(r) + Σ D e^{−zr}` with `Q⁰` compact and the exp tail over the full
   half-line (it is what generates the `s=−z` pole).  What remains is the **assembly** of the two
   overlaps into the exterior Eq. (8) — the substantive step.
3. ☐ **match the `e^{−zr}` coefficient** ⟹ `h29 : Dt·bhF(z) = 2πK/z` as a theorem.
4. ☐ the **Laplace moment `ĝ(z)`** ⟹ `h33`, carrying the `Dt`/`γ` terms onto the proved base
   `bh_base_eq`.
5. ☐ wire the derived `h29`/`h33` back into `MSAFullFactorization.exactMSA_factorization`, retiring
   the hypotheses.

Each `(29)/(33)` is only degree-2 in `(Dt,G)` — so unlike the `hcore` closure-recovery ring
(measured `ring`-infeasible, degree ≈ 22), this derivation is `ring`-tractable.
-/

open MeasureTheory Set Real

namespace FMSA.ExactMSA

/-! ### Milestone 1 — the exterior-closure (`K`-side) of Baxter's Eq. (8) -/

/-- **(29) LHS, real space.**  On the exterior `r > 1`, the MSA closure's `2πr·c(r)` is the pure
contact-normalised Yukawa `2πK·e^{−z(r−1)}` (`σ = 1`) — the left side of Baxter's Eq. (8) at
`r > σ`, where the radial factor `r` cancels the closure's `1/r`. -/
theorem cMSAtail_exterior_lhs (K z : ℝ) {r : ℝ} (hr : 1 < r) :
    2 * Real.pi * r * cMSAtail K z 1 r = 2 * Real.pi * K * Real.exp (-z * (r - 1)) := by
  unfold cMSAtail
  rw [if_pos hr]
  field_simp

/-- **(29) LHS, Laplace domain.**  The one-sided Laplace transform of the exterior `2πr·c(r)` is
`2πK·e^{−s}/(s+z)` — the elementary Yukawa transform carrying the simple pole at `s = −z` whose
residue is proportional to the coupling `K`.  This is the `K`-side that the exterior Baxter relation
(milestone 2) must reproduce from the tail amplitude `Dt`. -/
theorem cMSAtail_lhs_laplace (K : ℝ) {s z : ℝ} (hsz : 0 < s + z) :
    ∫ r in Ioi (1 : ℝ), (2 * Real.pi * r * cMSAtail K z 1 r) * Real.exp (-s * r)
      = 2 * Real.pi * K * (Real.exp (-s) / (s + z)) := by
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    (fun r hr => by rw [cMSAtail_exterior_lhs K z (mem_Ioi.mp hr)])]
  have hcm : ∀ r : ℝ, 2 * Real.pi * K * Real.exp (-z * (r - 1)) * Real.exp (-s * r)
      = (2 * Real.pi * K) * (Real.exp (-z * (r - 1)) * Real.exp (-s * r)) := fun r => by ring
  simp only [hcm]
  rw [MeasureTheory.integral_const_mul, yukawa_tail_laplace hsz]

/-! ### Milestone 2 (in progress) — the exterior non-compact-`q` Baxter convolution -/

/-- **Milestone 2 building block — the tail–tail self-overlap.**  In Baxter's exterior relation the
convolution `∫ q′(t) q(r+t) dt` for the non-compact `q = q0_poly + Dt·e^{−zr}` picks up, at `r > σ`,
the tail-against-tail overlap `∫_{t>0} e^{−zt}·e^{−z(r+t)} dt = e^{−zr}/(2z)`.  Times the tail's
`−z Dt` derivative and the `Dt` shift, this is the `−Dt²/2·e^{−zr}` **doubly-propagated** `Dt²` term
of the exterior relation — the structure that makes `(29)` degree-2. -/
theorem tail_tail_conv {z : ℝ} (hz : 0 < z) (r : ℝ) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-z * t) * Real.exp (-z * (r + t))
      = Real.exp (-z * r) / (2 * z) := by
  have hcomb : (fun t => Real.exp (-z * t) * Real.exp (-z * (r + t)))
      = fun t => Real.exp (-z * r) * Real.exp (-(2 * z) * t) := by
    funext t; rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  rw [hcomb, MeasureTheory.integral_const_mul,
    integral_exp_mul_Ioi (by linarith : -(2 * z) < 0) 0]
  rw [mul_zero, Real.exp_zero, neg_div_neg_eq]
  ring

/-- **Milestone 2 building block — the exterior shift factors out.**  The other convolution overlap
in Baxter's exterior relation is the core polynomial against the tail: `∫ g(t)·e^{−z(r+t)} dt`.  The
exterior point's `e^{−zr}` pulls straight out of any such integrand, `= e^{−zr}·∫ g(t)·e^{−zt} dt`
— reducing the poly–tail cross term to the core Laplace moment `∫ g(t)e^{−zt} dt`.  Convention-
independent (pure shift algebra), so it holds for any `g` and interval. -/
theorem exp_shift_factor (g : ℝ → ℝ) (z r a b : ℝ) :
    ∫ t in a..b, g t * Real.exp (-z * (r + t))
      = Real.exp (-z * r) * ∫ t in a..b, g t * Real.exp (-z * t) := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  have hsplit : Real.exp (-z * (r + t)) = Real.exp (-z * r) * Real.exp (-z * t) := by
    rw [← Real.exp_add]; congr 1; ring
  simp only [hsplit]; ring

/-! ### Milestone 2b — the `Q̂` integral ↔ closed-form faithfulness bridge

The scalar exact-MSA transcription carries `Q̂₀(z) = φ₁(z) q⁰′ + φ₂(z) A⁰`
(`MSABlumHoyeSystem.Qhat0`) as a *closed form*.  For the leg-3 derivation to touch Baxter's
real-space Eq. (8) it must be the Laplace transform of the real-space Baxter polynomial `q0_poly`.
That was previously only a
numerical check; the two moment corollaries and `qhat0_eq_laplace_q0poly` make it a theorem, reusing
the already-proved `phi1_real_laplace`/`phi2_real_laplace`. -/

/-- **φ₁ as a core Laplace moment.**  Corollary of `phi1_real_laplace` at `σ = 1`: the closed-form
Baxter coefficient factor `φ₁(z)` is the one-sided transform of the linear basis element `(r−1)`. -/
theorem phi1_laplace_moment {z : ℝ} (hz : z ≠ 0) :
    ∫ r in (0:ℝ)..1, (r - 1) * Real.exp (-z * r) = phi1 z := by
  rw [show phi1 z = (1 - z * 1 - Real.exp (-z * 1)) / z ^ 2 from by simp only [phi1, mul_one],
      ← FMSA.HardSphere.phi1_real_laplace hz (by norm_num : (0:ℝ) ≤ 1)]
  apply intervalIntegral.integral_congr
  intro r hr
  simp only [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1), Set.mem_Icc] at hr
  simp [FMSA.HardSphere.phi1_real, hr.2]

/-- **φ₂ as a core Laplace moment.**  Corollary of `phi2_real_laplace` at `σ = 1`: `φ₂(z)` is the
one-sided transform of the quadratic basis element `½(r−1)²`. -/
theorem phi2_laplace_moment {z : ℝ} (hz : z ≠ 0) :
    ∫ r in (0:ℝ)..1, ((r - 1) ^ 2 / 2) * Real.exp (-z * r) = phi2 z := by
  rw [show phi2 z = (1 - z * 1 + (z * 1) ^ 2 / 2 - Real.exp (-z * 1)) / z ^ 3 from by
        simp only [phi2, mul_one],
      ← FMSA.HardSphere.phi2_real_laplace hz (by norm_num : (0:ℝ) ≤ 1)]
  apply intervalIntegral.integral_congr
  intro r hr
  simp only [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1), Set.mem_Icc] at hr
  simp [FMSA.HardSphere.phi2_real, hr.2]

/-- **Faithfulness bridge (integral ↔ closed form).**  The closed-form PY Baxter transform
`ρ·Q̂₀(z) = ρ(φ₁ q⁰′ + φ₂ A⁰)` is *literally* the one-sided Laplace transform of the real-space
Baxter polynomial `q0_poly` over the core `[0,1]`.  This discharges — as a theorem, no longer a
numerical check — the "the closed form is the integral" gap in the exact-MSA transcription.  It uses
the already-proved `phi1_real_laplace`/`phi2_real_laplace` and the coefficient identities
`qp0 = q_prime_py σ=1`, `bA0 = q_doubleprime_py` (both discharged inside by `ring`). -/
theorem qhat0_eq_laplace_q0poly (xi z : ℝ) (hz : z ≠ 0) :
    ∫ r in (0:ℝ)..1, FMSA.HardSphere.q0_poly xi 1 (rhoOf xi) r * Real.exp (-z * r)
      = rhoOf xi * Qhat0 xi z := by
  have hcongr :
      (∫ r in (0:ℝ)..1, FMSA.HardSphere.q0_poly xi 1 (rhoOf xi) r * Real.exp (-z * r))
      = ∫ r in (0:ℝ)..1,
          ((rhoOf xi * FMSA.HardSphere.q_prime_py xi 1) * ((r - 1) * Real.exp (-z * r))
         + (rhoOf xi * FMSA.HardSphere.q_doubleprime_py xi)
             * ((r - 1) ^ 2 / 2 * Real.exp (-z * r))) := by
    apply intervalIntegral.integral_congr
    intro r hr
    simp only [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1), Set.mem_Icc] at hr
    show FMSA.HardSphere.q0_poly xi 1 (rhoOf xi) r * Real.exp (-z * r) = _
    rw [FMSA.HardSphere.q0_poly_inner (show r ≤ (1:ℝ) from hr.2)]
    ring
  rw [hcongr, intervalIntegral.integral_add
        (by apply Continuous.intervalIntegrable; fun_prop)
        (by apply Continuous.intervalIntegrable; fun_prop),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      phi1_laplace_moment hz, phi2_laplace_moment hz]
  simp only [Qhat0, qp0, bA0, FMSA.HardSphere.q_prime_py, FMSA.HardSphere.q_doubleprime_py]
  ring

end FMSA.ExactMSA
