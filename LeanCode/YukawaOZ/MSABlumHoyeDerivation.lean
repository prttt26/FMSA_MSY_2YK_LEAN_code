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
import LeanCode.HardSphere.BaxterDiluteDecay
import LeanCode.YukawaOZ.MSABaxterKSpace

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
3. ◑ **the exterior convolution, general moment form** (milestone 3 below).  For ANY Baxter
   function `P = p + Dt·e^{−z·}` (`p` supported on `[0,1]`), `baxter_exterior_moment_form` proves
   the exterior right side `−P'(r) + ∫ P·P'(·+r) = z Dt e^{−zr}·(1 − M_full)`, with
   `M_full = ∫₀¹ p e^{−zt} + Dt/(2z)` the full Laplace moment.  Matching the MSA closure gives
   `z Dt (1 − M_full) = 2πρ K e^{z}` — i.e. **(29) reduces to the definitional `bhF = 1 − M_full`**.
   The FMSA instance `msaBaxter_exterior_rhs` (`p = q0_poly`) gives first-order `1 − M_full =
   F₀ − Dt/(2z)`.  ⚠ The *exact* `bhF` is NOT this instance: `tailtil` (the exact tail moment) is
   `G`-entangled (measured: varies with `G`, `≠ 1/(2z)`), so the exact Baxter tail couples to the
   RDF moment `G` via continuity — reconstructing it is the full Blum–Høye reduction, not a
   mechanical dressing of `q0_poly`.
4. ◑ **the exact `bhF` faithfulness bridge** (milestone 4 below).  `bhF_eq_one_sub_dressed_moment`:
   `bhF = 1 − (∫₀¹ q₀ᵈʳᵉˢˢᵉᵈ e^{−zt} + Dt·ρ·tailtil)`, the exact Baxter factor as `1` minus the full
   Laplace moment of the DRESSED Baxter function (coefficients `msaQp`/`msaA`, Eqs. 23/24).
   The polynomial half is a genuine integral theorem; the `Dt·ρ·tailtil` closed form is the residual
   (`G`-entangled) tail transcription.  This discharges the poly half of exact `h29`; the exterior
   match to the closure and the tail's `Dt`-vs-amplitude relation remain (the deep BH continuity
   content, see ⚠ above).
5. ☐ the **Laplace moment `ĝ(z)`** ⟹ `h33`, carrying the `Dt`/`γ` terms onto the proved base
   `bh_base_eq`.
6. ☐ wire the derived `h29`/`h33` back into `MSAFullFactorization.exactMSA_factorization`, retiring
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

/-! ### Milestone 3 — the exterior Baxter convolution, in general moment form

Baxter's real-space relation (`HardSphere.baxter_factorization_inner`) is
`2πρ r c(r) = −P'(r) + ∫ P(t)·P'(t+r) dt`.  On the exterior `r > σ = 1` the polynomial part of a
Baxter function `P = p + Dt·e^{−z·}` (`p` compactly supported on `[0,1]`) vanishes, so
`P'(t+r) = −z Dt e^{−z(t+r)}` and the convolution collapses onto the poly–tail overlap
(`gen_poly_tail_conv`) and tail–tail overlap (`tail_tail_conv`).  The result is the exterior right
side `z Dt e^{−zr}·(1 − M_full)`, carrying the *full* Laplace moment `M_full = ∫₀¹ p e^{−zt} +
Dt/(2z)` — so matching the MSA closure reduces (29) to the definitional `bhF = 1 − M_full`.  The
concrete FMSA case (`p = q0_poly`) is `msaBaxter_exterior_rhs`; it recovers the first-order/DP cut.
The *exact* `bhF` is a different `p` whose tail moment is `G`-entangled (roadmap ⚠). -/

/-- **General poly–tail overlap on the improper `(0,∞)`.**  For any `p` supported on `[0,1]` and
continuous, the half-line integral reduces to the core one (compact support) and factors out the
exterior shift (`exp_shift_factor`): `∫₀^∞ p(t) e^{−z(r+t)} dt = e^{−zr} · ∫₀¹ p(t) e^{−zt} dt`. -/
theorem gen_poly_tail_conv (z : ℝ) (p : ℝ → ℝ) (hp0 : ∀ t, 1 < t → p t = 0)
    (hpc : Continuous p) (r : ℝ) :
    ∫ t in Set.Ioi (0:ℝ), p t * Real.exp (-z * (r + t))
      = Real.exp (-z * r) * ∫ t in (0:ℝ)..1, p t * Real.exp (-z * t) := by
  have hZero : ∀ t ∈ Set.Ioi (1:ℝ), p t * Real.exp (-z * (r + t)) = 0 := by
    intro t ht; rw [hp0 t (Set.mem_Ioi.mp ht), zero_mul]
  have hIoc : MeasureTheory.IntegrableOn
      (fun t => p t * Real.exp (-z * (r + t))) (Set.Ioc (0:ℝ) 1) := by
    apply Continuous.integrableOn_Ioc; exact hpc.mul (by fun_prop)
  have hIoi1 : MeasureTheory.IntegrableOn
      (fun t => p t * Real.exp (-z * (r + t))) (Set.Ioi (1:ℝ)) := by
    rw [MeasureTheory.integrableOn_congr_fun hZero measurableSet_Ioi]
    exact MeasureTheory.integrableOn_zero
  rw [← Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (0:ℝ) ≤ 1),
      MeasureTheory.setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hIoc hIoi1,
      MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero hZero, add_zero,
      ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1), exp_shift_factor _ z r 0 1]

/-- **General exterior convolution.**  For `P = p + Dt·e^{−z·}` (`p` supported on `[0,1]`) the
exterior convolution collapses to the poly moment `∫₀¹ p e^{−zt}` plus the tail `Dt²/2`. -/
theorem gen_exterior_conv (z Dt : ℝ) (hz : 0 < z) (p : ℝ → ℝ) (hp0 : ∀ t, 1 < t → p t = 0)
    (hpc : Continuous p) (r : ℝ) :
    ∫ t in Set.Ioi (0:ℝ),
        (p t + Dt * Real.exp (-z * t)) * (-z * Dt * Real.exp (-z * (r + t)))
      = -z * Dt * Real.exp (-z * r) * (∫ t in (0:ℝ)..1, p t * Real.exp (-z * t))
        - Dt ^ 2 * Real.exp (-z * r) / 2 := by
  have hZero : ∀ t ∈ Set.Ioi (1:ℝ), p t * Real.exp (-z * (r + t)) = 0 := by
    intro t ht; rw [hp0 t (Set.mem_Ioi.mp ht), zero_mul]
  have hI1 : MeasureTheory.IntegrableOn
      (fun t => p t * Real.exp (-z * (r + t))) (Set.Ioi (0:ℝ)) := by
    have hIoc : MeasureTheory.IntegrableOn
        (fun t => p t * Real.exp (-z * (r + t))) (Set.Ioc (0:ℝ) 1) := by
      apply Continuous.integrableOn_Ioc; exact hpc.mul (by fun_prop)
    have hIoi1 : MeasureTheory.IntegrableOn
        (fun t => p t * Real.exp (-z * (r + t))) (Set.Ioi (1:ℝ)) := by
      rw [MeasureTheory.integrableOn_congr_fun hZero measurableSet_Ioi]
      exact MeasureTheory.integrableOn_zero
    rw [← Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (0:ℝ) ≤ 1)]
    exact hIoc.union hIoi1
  have hI2 : MeasureTheory.IntegrableOn
      (fun t => Real.exp (-z * t) * Real.exp (-z * (r + t))) (Set.Ioi (0:ℝ)) := by
    have h2 : (fun t => Real.exp (-z * t) * Real.exp (-z * (r + t)))
        = (fun t => Real.exp (-z * r) * Real.exp (-(2 * z) * t)) := by
      funext t; rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    rw [h2]; exact (exp_neg_integrableOn_Ioi 0 (by linarith : (0:ℝ) < 2 * z)).const_mul _
  have hcongr : (∫ t in Set.Ioi (0:ℝ),
        (p t + Dt * Real.exp (-z * t)) * (-z * Dt * Real.exp (-z * (r + t))))
      = ∫ t in Set.Ioi (0:ℝ),
          ((-z * Dt) * (p t * Real.exp (-z * (r + t)))
         + (-z * Dt ^ 2) * (Real.exp (-z * t) * Real.exp (-z * (r + t)))) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t _; ring
  rw [hcongr, MeasureTheory.integral_add (hI1.const_mul _) (hI2.const_mul _),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      gen_poly_tail_conv z p hp0 hpc r, tail_tail_conv hz r]
  field_simp; ring

/-- **General exterior derivative.**  Past `σ`, `p` is locally `0`, so `P'(r) = −z Dt e^{−zr}`. -/
theorem gen_exterior_deriv (z Dt : ℝ) (p : ℝ → ℝ) (hp0 : ∀ t, 1 < t → p t = 0) {r : ℝ}
    (hr : 1 < r) :
    HasDerivAt (fun s => p s + Dt * Real.exp (-z * s)) (-z * Dt * Real.exp (-z * r)) r := by
  have hpder : HasDerivAt p 0 r := by
    apply (hasDerivAt_const r (0:ℝ)).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hr] with s hs
    exact hp0 s (Set.mem_Ioi.mp hs)
  have hexp : HasDerivAt (fun s => Dt * Real.exp (-z * s)) (-z * Dt * Real.exp (-z * r)) r := by
    have hg : HasDerivAt (fun s => Real.exp (-z * s)) (Real.exp (-z * r) * -z) r := by
      have h : HasDerivAt (fun s => -z * s) (-z) r := by
        simpa using (hasDerivAt_id r).const_mul (-z)
      exact h.exp
    exact (hg.const_mul Dt).congr_deriv (by ring)
  have hadd := hpder.add hexp
  rw [zero_add] at hadd
  exact hadd

/-- **Milestone 3 — the exterior Baxter RHS, general moment form.**  For ANY Baxter function
`P = p + Dt·e^{−z·}` with `p` supported on `[0,1]`, the exterior right side `−P'(r) + ∫ P·P'(·+r)`
equals `z Dt e^{−zr}·(1 − M_full)`, `M_full = ∫₀¹ p e^{−zt} + Dt/(2z)` the full one-sided Laplace
moment of `P`.  Matching the MSA closure `2πρ r c = 2πρ K e^{z} e^{−zr}` then gives
`z Dt (1 − M_full) = 2πρ K e^{z}`, i.e. `Dt·bhF ∝ K` **with `bhF := 1 − M_full`** — reducing (29) to
the definitional identity "`bhF` is `1` minus the Baxter Laplace moment". -/
theorem baxter_exterior_moment_form (z Dt : ℝ) (hz : 0 < z) (p : ℝ → ℝ)
    (hp0 : ∀ t, 1 < t → p t = 0) (hpc : Continuous p) {r : ℝ} (hr : 1 < r) :
    -deriv (fun s => p s + Dt * Real.exp (-z * s)) r
      + ∫ t in Set.Ioi (0:ℝ),
          (p t + Dt * Real.exp (-z * t)) * (-z * Dt * Real.exp (-z * (r + t)))
      = z * Dt * Real.exp (-z * r)
          * (1 - ((∫ t in (0:ℝ)..1, p t * Real.exp (-z * t)) + Dt / (2 * z))) := by
  have hz' : z ≠ 0 := hz.ne'
  rw [(gen_exterior_deriv z Dt p hp0 hr).deriv, gen_exterior_conv z Dt hz p hp0 hpc r]
  field_simp; ring

/-- **M3 (FMSA instance) — the exterior Baxter RHS in `F₀` form.**  The `p = q0_poly` case of
`baxter_exterior_moment_form`, poly moment resolved to `ρ Q̂₀` by `qhat0_eq_laplace_q0poly`,
so `1 − M_full = F₀ − Dt/(2z)`, `F₀ = 1 − ρ Q̂₀`.  Matching the MSA closure gives first-order
Blum–Høye (29) `z Dt F₀ − Dt²/2 = 2πρ K e^{z}`. -/
theorem msaBaxter_exterior_rhs (xi z Dt : ℝ) (hz : 0 < z) {r : ℝ} (hr : 1 < r) :
    -deriv (fun s => msaBaxterFn xi 1 (rhoOf xi) z Dt s) r
      + ∫ t in Set.Ioi (0:ℝ),
          msaBaxterFn xi 1 (rhoOf xi) z Dt t * (-z * Dt * Real.exp (-z * (r + t)))
      = z * Dt * Real.exp (-z * r) * F0 xi z - Dt ^ 2 * Real.exp (-z * r) / 2 := by
  simp only [msaBaxterFn]
  rw [baxter_exterior_moment_form z Dt hz (FMSA.HardSphere.q0_poly xi 1 (rhoOf xi))
        (fun t ht => FMSA.HardSphere.q0_poly_eq_zero_of_ge (le_of_lt ht))
        (FMSA.HardSphere.q0_poly_continuous xi 1 (rhoOf xi)) hr,
      qhat0_eq_laplace_q0poly xi z hz.ne', F0]
  field_simp
  ring

/-! ### Milestone 4 — the exact `bhF` faithfulness bridge (dressed Baxter function)

M2b's bridge (`qhat0_eq_laplace_q0poly`) proved `ρ Q̂₀ = ∫₀¹ q0_poly e^{−zt}` for the HARD-SPHERE
Baxter polynomial.  The exact Blum–Høye Baxter factor `bhF = 1 − ρ Q̂` dresses that polynomial: its
coefficients become `msaQp = q⁰′(1+M) + A⁰N` and `msaA = A⁰(1+M) − 4B⁰N` (`MSABaxterKSpace`, Eqs.
23/24), with `M = Dt·Mtil`, `N = Dt·Ntil`.  `bhF_eq_one_sub_dressed_moment` proves the exact bridge
`bhF = 1 − (∫₀¹ q₀ᵈʳᵉˢˢᵉᵈ e^{−zt} + Dt·ρ·tailtil)`: the exact factor is `1` minus the full Laplace
moment of the DRESSED Baxter function.  The polynomial half is a genuine integral (via the M2b
moment lemmas); `Dt·ρ·tailtil` is the `G`-entangled tail closed form (numerically confirmed
`tailtil ≠ 1/(2z)`), the residual transcription the exterior route cannot supply. -/

/-- **General two-coefficient Baxter poly moment.**  `∫₀¹ (c₁(t−1) + c₂(t−1)²/2) e^{−zt} =
c₁ φ₁ + c₂ φ₂` — the linear + quadratic core basis against the exterior weight, via the M2b moment
lemmas.  With `c₁ = ρ·msaQp`, `c₂ = ρ·msaA` this is the dressed polynomial's Laplace moment. -/
theorem baxter_poly_moment (c1 c2 z : ℝ) (hz : z ≠ 0) :
    ∫ t in (0:ℝ)..1, (c1 * (t - 1) + c2 * ((t - 1) ^ 2 / 2)) * Real.exp (-z * t)
      = c1 * phi1 z + c2 * phi2 z := by
  have hcongr : (∫ t in (0:ℝ)..1, (c1 * (t - 1) + c2 * ((t - 1) ^ 2 / 2)) * Real.exp (-z * t))
      = ∫ t in (0:ℝ)..1,
          (c1 * ((t - 1) * Real.exp (-z * t)) + c2 * (((t - 1) ^ 2 / 2) * Real.exp (-z * t))) := by
    apply intervalIntegral.integral_congr; intro t _; ring
  rw [hcongr, intervalIntegral.integral_add
        (by apply Continuous.intervalIntegrable; fun_prop)
        (by apply Continuous.intervalIntegrable; fun_prop),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      phi1_laplace_moment hz, phi2_laplace_moment hz]

/-- **Exact `bhF` faithfulness bridge.**  The exact Blum–Høye Baxter factor is `1` minus the full
Laplace moment of the DRESSED Baxter function: `bhF = 1 − (∫₀¹ q₀ᵈʳᵉˢˢᵉᵈ e^{−zt} + Dt·ρ·tailtil)`,
with dressed polynomial `ρ(msaQp·(t−1) + msaA·(t−1)²/2)` (coupling-dressed coefficients, Eqs. 23/24)
and `tailtil` the `G`-entangled tail moment.  The integral (polynomial half) is discharged as a
theorem via the M2b moment lemmas; the closed-form `Dt·ρ·tailtil` is the residual tail term.
Extends `qhat0_eq_laplace_q0poly` from the hard-sphere `q0_poly` to the full dressed Baxter function
— the exact analog of the M2b bridge for the interacting factor. -/
theorem bhF_eq_one_sub_dressed_moment (xi z Dt G : ℝ) (hz : z ≠ 0) (hxi : (1 - xi) ≠ 0) :
    bhF xi z (Dt, G)
      = 1 - ((∫ t in (0:ℝ)..1,
                (rhoOf xi * msaQp xi z Dt G * (t - 1)
                 + rhoOf xi * msaA xi z Dt G * ((t - 1) ^ 2 / 2)) * Real.exp (-z * t))
             + Dt * rhoOf xi * tailtil xi z G) := by
  rw [baxter_poly_moment (rhoOf xi * msaQp xi z Dt G) (rhoOf xi * msaA xi z Dt G) z hz]
  simp only [bhF, F0, bhFRest, msaQp, msaA, Mtil, Ntil, tailtil, gam, Qhat0, phi1, phi2,
    rhoOf, qp0, bA0, bB0]
  field_simp
  ring

/-! ### Phase 2 — the σ-continuity linear system (Blum–Høye Eqs. 17/18)

Phase 0 (`proof_notes_leg3_bh_phase0.md`) pinned the exact Baxter function and identified the two
core-matching equations Blum–Høye (17)/(18) — the constant- and `r`-coefficient match of the OZ
equation (9) at `r < σ`, whose 2×2 solution is the dressed `(A, q') = (msaA, msaQp)` (Eqs. 23/24).
These two lemmas discharge the **linear-algebra half** of Phase 2: the dressed coefficients
*satisfy* that continuity system (`B = q' − A` from Eq. 14, `M = Dt·Mtil`, `N = Dt·Ntil`, `σ = 1`).
They reduce to `field_simp; ring`; the base (`M=N=0`) case is the PY identity `(1−4ξ)A⁰−6ξB⁰ = 2π`,
`2π(1−ξ)²/(1−ξ)²`.  (The remaining half — *deriving* (17)/(18) from the OZ equation (9) itself —
needs the real-space OZ integral equation, tracked separately.) -/

/-- **Blum–Høye continuity system, Eq. (17)** (σ = 1, `B = q' − A` via Eq. 14).  The dressed Baxter
coefficients satisfy the first core-matching equation: `(1−4ξ)A − 6ξB = 2π(1+M)`, `M = Dt·Mtil`. -/
theorem msaCoeff_continuity_17 (xi z Dt G : ℝ) (hz : z ≠ 0) (hxi : (1 - xi) ≠ 0) :
    (1 - 4 * xi) * msaA xi z Dt G - 6 * xi * (msaQp xi z Dt G - msaA xi z Dt G)
      = 2 * π * (1 + Dt * Mtil xi z G) := by
  simp only [msaA, msaQp, Mtil, Ntil, gam, qp0, bA0, bB0, rhoOf]
  field_simp
  ring

/-- **Blum–Høye continuity system, Eq. (18)** (σ = 1).  The second core-matching equation:
`(3/2)ξA + (1+2ξ)B = 2πN`, `N = Dt·Ntil`. -/
theorem msaCoeff_continuity_18 (xi z Dt G : ℝ) (hz : z ≠ 0) (hxi : (1 - xi) ≠ 0) :
    (3 / 2) * xi * msaA xi z Dt G + (1 + 2 * xi) * (msaQp xi z Dt G - msaA xi z Dt G)
      = 2 * π * (Dt * Ntil xi z G) := by
  simp only [msaA, msaQp, Mtil, Ntil, gam, qp0, bA0, bB0, rhoOf]
  field_simp
  ring

/-! ### Phase 3 — `tailtil` from the C-exp basis moment (normalization pinned)

Phase 0 pinned the exact Baxter function's continuity-enforcing exponential piece
`C·(e^{−zr} − e^{−zσ})` (Blum–Høye Eq. 11), whose Laplace moment is the physical origin of the
`G`-entangled `tailtil`.  The `C ↔ (Dt, G)` normalization is now RESOLVED: the repo's `gam` is the
Blum–Høye **Eq. (27) bracket** `1 − 2πρĝ/z` (not the Eq. 35 `γ`), so `ĝ(z) = G e^{−z}` (matching the
`G₀ = ĝ_PY e^z` convention), `C = −gam·D`, and the exterior tail amplitude is `D = Dt·e^{z}` (the
`e^{zσ}` contact factor — verified numerically `D/Dt = e^z` to `1e-6`).  With this, `tailtil` is
exactly the C-exp basis moment combination (`tailtil_cexp_form`), and — via
`cexp_basis_laplace_moment` — the actual Laplace integral of the continuity piece
(`tailtil_eq_cexp_integral`).  This discharges the physical origin of the `G`-entangled tail. -/

/-- **The C-exp basis Laplace moment.**  `∫₀¹ (e^{−zt} − e^{−z})·e^{−zt} dt = (1−e^{−z})²/(2z)`.
The one-sided moment of the exact Baxter continuity term `(e^{−zr} − e^{−zσ})`, `σ=1`. -/
theorem cexp_basis_laplace_moment {z : ℝ} (hz : z ≠ 0) :
    ∫ t in (0:ℝ)..1, (Real.exp (-z * t) - Real.exp (-z)) * Real.exp (-z * t)
      = (1 - Real.exp (-z)) ^ 2 / (2 * z) := by
  have key : ∀ t : ℝ, HasDerivAt
      (fun t => -(Real.exp (-z * t) ^ 2 / (2 * z)) + Real.exp (-z) / z * Real.exp (-z * t))
      ((Real.exp (-z * t) - Real.exp (-z)) * Real.exp (-z * t)) t := by
    intro t
    have hg : HasDerivAt (fun t => Real.exp (-z * t)) (Real.exp (-z * t) * -z) t := by
      have h : HasDerivAt (fun t => -z * t) (-z) t := by
        simpa using (hasDerivAt_id t).const_mul (-z)
      exact h.exp
    have hF := (((hg.pow 2).div_const (2 * z)).neg).add (hg.const_mul (Real.exp (-z) / z))
    refine hF.congr_deriv ?_
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => key t)
        (by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [mul_one, mul_zero, Real.exp_zero, one_pow]
  field_simp
  ring

/-- **`tailtil` is the C-exp moment combination.**  `e^{−z}·tailtil = 1/(2z) − γ·(1−e^{−z})²/(2z)`,
with `(1−e^{−z})²/(2z)` the C-exp basis moment and `γ = gam` the Blum–Høye Eq. (27) bracket
`1 − 2πρĝ/z` (`ĝ = G e^{−z}`).  Ring identity (reduces to `e^z(1−γ) = 2πρG/z`). -/
theorem tailtil_cexp_form (xi z G : ℝ) (hz : z ≠ 0) :
    tailtil xi z G * Real.exp (-z)
      = 1 / (2 * z) - gam xi z G * ((1 - Real.exp (-z)) ^ 2 / (2 * z)) := by
  simp only [tailtil, gam, rhoOf]
  field_simp
  ring

/-- **Phase 3 capstone — `tailtil` via the C-exp Laplace integral.**  The `G`-entangled tail closed
form `tailtil` is, up to the contact factor `e^{−z}` and the Eq. (27) bracket `γ = gam`, exactly the
one-sided Laplace transform of the exact Baxter function's continuity piece `(e^{−zr} − e^{−zσ})`.
Combines `tailtil_cexp_form` with `cexp_basis_laplace_moment`. -/
theorem tailtil_eq_cexp_integral (xi z G : ℝ) (hz : z ≠ 0) :
    tailtil xi z G * Real.exp (-z)
      = 1 / (2 * z) - gam xi z G
          * (∫ t in (0:ℝ)..1, (Real.exp (-z * t) - Real.exp (-z)) * Real.exp (-z * t)) := by
  rw [cexp_basis_laplace_moment hz, tailtil_cexp_form xi z G hz]

/-- **`tailtil` in integral form.**  `tailtil = e^z·(1/(2z) − γ·∫₀¹ (e^{−zt}−e^{−z}) e^{−zt})` — the
`e^z`-lifted form of `tailtil_eq_cexp_integral`, ready to substitute into the `bhF` bridge. -/
theorem tailtil_eq_integral_form (xi z G : ℝ) (hz : z ≠ 0) :
    tailtil xi z G
      = Real.exp z * (1 / (2 * z) - gam xi z G
          * (∫ t in (0:ℝ)..1, (Real.exp (-z * t) - Real.exp (-z)) * Real.exp (-z * t))) := by
  have he : Real.exp z * Real.exp (-z) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [← tailtil_eq_cexp_integral xi z G hz,
      show Real.exp z * (tailtil xi z G * Real.exp (-z))
        = tailtil xi z G * (Real.exp z * Real.exp (-z)) from by ring, he, mul_one]

/-- **Full `bhF` faithfulness bridge (integral form).**  `bhF = 1 − (dressed-poly moment + tail
moment)` with BOTH halves as genuine Laplace integrals of the exact Baxter function's pieces: the
dressed polynomial and (via `e^z`/`γ`) the continuity term `(e^{−zr}−e^{−zσ})`.  Upgrades
`bhF_eq_one_sub_dressed_moment` (M4) with the Phase-3 `tailtil_eq_integral_form`. -/
theorem bhF_eq_one_sub_full_integral (xi z Dt G : ℝ) (hz : z ≠ 0) (hxi : (1 - xi) ≠ 0) :
    bhF xi z (Dt, G)
      = 1 - ((∫ t in (0:ℝ)..1,
                (rhoOf xi * msaQp xi z Dt G * (t - 1)
                 + rhoOf xi * msaA xi z Dt G * ((t - 1) ^ 2 / 2)) * Real.exp (-z * t))
             + Dt * rhoOf xi * (Real.exp z * (1 / (2 * z) - gam xi z G *
                 (∫ t in (0:ℝ)..1,
                   (Real.exp (-z * t) - Real.exp (-z)) * Real.exp (-z * t))))) := by
  rw [bhF_eq_one_sub_dressed_moment xi z Dt G hz hxi, tailtil_eq_integral_form xi z G hz]

end FMSA.ExactMSA
