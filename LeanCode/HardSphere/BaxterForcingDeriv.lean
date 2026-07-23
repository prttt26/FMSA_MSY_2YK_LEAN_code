/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HardSphere.BaxterKernelDeriv
import LeanCode.HardSphere.BaxterRenewal
import LeanCode.Analysis.ConvolutionLeibniz

/-!
# Derivative of the renewal forcing `baxterForcing` — step 2 of (★DIFF)

`baxterForcing r = ∫ s in 0..σ, q0_poly(r − s) · (−s)` has **fixed** limits, so its derivative is the
pure parameter-differentiation case of `MA.16`
(`FMSA.Analysis.hasDerivAt_intervalIntegral_param`, `Analysis/ConvolutionLeibniz.lean`):

  `baxterForcing'(r) = ∫ s in 0..σ, q0PolyDeriv(r − s) · (−s)`.

All four of `MA.16`'s hypotheses on the kernel are supplied by `BaxterKernelDeriv.lean`:
`q0_poly_continuous`, `hasDerivAt_q0_poly_ae` (a.e. — `q0_poly` has a kink at `σ`),
`q0PolyDeriv_measurable`, and `q0_poly_lipschitzOnWith`.
-/

open MeasureTheory Set Filter Topology

namespace FMSA.HardSphere

noncomputable section

/-- `q0_poly` is Lipschitz on any closed interval, with an explicit constant. -/
theorem q0_poly_lipschitzOnWith_Icc (eta sigma rho lo hi : ℝ) (hlohi : lo ≤ hi) :
    LipschitzOnWith
      (Real.nnabs (|rho * q_prime_py eta sigma|
        + |rho * q_doubleprime_py eta| * ((hi - lo) + |lo - sigma|)))
      (q0_poly eta sigma rho) (Icc lo hi) := by
  refine q0_poly_lipschitzOnWith ?_ (fun x hx => ?_)
  · have : (0:ℝ) ≤ hi - lo := by linarith
    have := abs_nonneg (lo - sigma)
    linarith
  · have h1 : x - sigma = (x - lo) + (lo - sigma) := by ring
    rw [h1]
    refine le_trans (abs_add_le _ _) ?_
    have h2 : |x - lo| ≤ hi - lo := by
      rw [abs_of_nonneg (by linarith [(mem_Icc.mp hx).1] : (0:ℝ) ≤ x - lo)]
      linarith [(mem_Icc.mp hx).2]
    linarith

/-- **Step 2 of (★DIFF): the forcing is differentiable**, with
`baxterForcing'(r) = ∫ s in 0..σ, q0PolyDeriv(r − s)·(−s)`.  Fixed limits, so this is `MA.16`'s
parameter case; the kernel hypotheses come from `BaxterKernelDeriv.lean`. -/
theorem hasDerivAt_baxterForcing (eta sigma rho : ℝ) (hsigma : 0 ≤ sigma) (r : ℝ) :
    HasDerivAt (baxterForcing eta sigma rho)
      (∫ s in (0:ℝ)..sigma, q0PolyDeriv eta sigma rho (r - s) * (-s)) r := by
  have hlip := q0_poly_lipschitzOnWith_Icc eta sigma rho (r - 1 - sigma) (r + 1 - 0)
    (by linarith)
  exact FMSA.Analysis.hasDerivAt_intervalIntegral_param (K := q0_poly eta sigma rho)
    (K' := q0PolyDeriv eta sigma rho) (φ := fun s => -s)
    (by norm_num) hsigma
    (q0_poly_continuous eta sigma rho) (continuous_neg)
    (hasDerivAt_q0_poly_ae eta sigma rho) (q0PolyDeriv_measurable eta sigma rho)
    hlip

end

end FMSA.HardSphere
