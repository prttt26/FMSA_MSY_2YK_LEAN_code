/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.YukawaOZ.MSADCFTransform
import LeanCode.YukawaOZ.MSABaxterTransform

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
2. ☐ the **exterior non-compact-`q` Baxter relation** (the RHS of Eq. 8 at `r > 1` for
   `q = q0_poly + Dt·e^{−zr}`) — the `baxter_factorization_inner` (`BaxterRealSpace.lean`) technique
   (explicit antiderivative + FTC + `ring`) extended with the Yukawa tail's exponential
   antiderivatives (`yukawa_laplace_unit`, `yukawa_tail_laplace`).  This is the substantive step.
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

end FMSA.ExactMSA
