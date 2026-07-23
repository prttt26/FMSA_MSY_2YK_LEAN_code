/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HardSphere.OZExteriorBridge
import LeanCode.HardSphere.RadialFourier
import LeanCode.HardSphere.OzCoreClosure

/-!
# Task OZ.7 — Fourier-domain exterior OZ equation for `oz_h`

## Summary

`oz_laplace_oz_eq_of_core_closure` (`OZExteriorBridge.lean`) assembles Gap A (the `r ≥ σ`
half, unconditionally proved) with Gap B (the PY core closure, `hcore`) to reach the
Laplace-domain OZ equation — but it does so via `radial_laplace_conv`, now known
**mathematically false** (`RadialLaplace.lean`).

This file reruns the *exact same* Gap A ∪ Gap B assembly, substituting the correct
`radial_fourier`/`radial_fourier_conv` (`RadialFourier.lean`) for the false
`radial_laplace`/`radial_laplace_conv`. The pointwise real-space content (`hpointwise`,
reusing `oz_h_satisfies_conv_ext` and `hcore` verbatim) is transform-independent and carries
over unchanged; only the "apply the transform" step differs.

**Task OZ.8 (done, `HardSphere/RadialFourierCHS.lean`):** the conclusion below is stated
directly in terms of `radial_fourier (c_HS eta sigma) k`, not a named closed form — that file
supplies the closed form (`radial_fourier_c_HS_formula`) and the `s ↔ -ik` correspondence to
`C_HS_laplace_formula`/`S0` (`radial_fourier_c_HS_eq_C_HS_laplace_expr`), via direct algebraic
computation on the two closed forms rather than analytic-continuation machinery. Deriving
`g0_HS_contact_value` from this is separate, much larger future work (needs Fourier inversion
of the closed-form-in-`k` OZ solution) — not attempted.
-/

open MeasureTheory Set Real

namespace FMSA.HardSphere

/-- **Task OZ.7 (conditional on Gap B only): the Fourier-domain hard-sphere OZ equation,
proved (not axiomatized) given the PY core closure `hcore` for `r < σ` (Gap B — the one
genuinely hard, unscaffolded physics input) plus the routine integrability side-conditions
for Gap A and for `radial_fourier_conv`.** This is the mathematically correct counterpart of
`oz_laplace_oz_eq_of_core_closure`, replacing the false `radial_laplace_conv` step with the
proved `radial_fourier_conv`. -/
theorem oz_fourier_oz_eq_of_core_closure {eta sigma rho k : ℝ}
    (hsigma : 0 < sigma)
    (hex : ∃ f : ℝ → ℝ, OzFixedPt eta sigma rho f ∧ ContinuousOn f (Set.Ici sigma)
        ∧ ∃ C, ∀ r, |f r| ≤ C)
    (hk : 0 < k)
    (hcore : ∀ r ∈ Set.Ioo (0 : ℝ) sigma,
      oz_h eta sigma rho r =
        c_HS eta sigma r + rho * radial3d_conv (c_HS eta sigma) (oz_h eta sigma rho) r)
    (hintA1 : ∀ r, sigma ≤ r → IntervalIntegrable
      (fun t => t * c_HS eta sigma t * (sigma ^ 2 - (r - t) ^ 2) *
        if r < sigma + t then (1 : ℝ) else 0) MeasureTheory.volume 0 sigma)
    (hintA2 : ∀ r, sigma ≤ r → IntervalIntegrable
      (fun t => t * c_HS eta sigma t *
        ∫ s' in (max (r - t) sigma)..(r + t), s' * oz_h eta sigma rho s')
      MeasureTheory.volume 0 sigma)
    (htsIntC : ∀ r ∈ Set.Ioi (0 : ℝ), Integrable
      (fun p : ℝ × ℝ =>
        p.1 * c_HS eta sigma p.1 *
          (Set.Icc |r - p.1| (r + p.1)).indicator (fun s => s * oz_h eta sigma rho s) p.2)
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))))
    (hjointC : Integrable
      (fun p : ℝ × ℝ × ℝ =>
        (p.2.1 * c_HS eta sigma p.2.1) *
          (Set.Icc |p.1 - p.2.1| (p.1 + p.2.1)).indicator
            (fun s => s * oz_h eta sigma rho s) p.2.2 *
          Real.sin (k * p.1))
      ((volume.restrict (Set.Ioi 0)).prod
        ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0)))))
    (hintB1 : Integrable (fun r => r * c_HS eta sigma r * Real.sin (k * r))
      (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hintConv : Integrable
      (fun r => r * radial3d_conv (c_HS eta sigma) (oz_h eta sigma rho) r * Real.sin (k * r))
      (MeasureTheory.volume.restrict (Set.Ioi 0))) :
    (radial_fourier (oz_h eta sigma rho) k) *
      (1 - rho * radial_fourier (c_HS eta sigma) k) = radial_fourier (c_HS eta sigma) k := by
  -- Step 1: the pointwise 3D-OZ equation, for every `r > 0` (Gap A ∪ Gap B) — identical to
  -- `oz_laplace_oz_eq_of_core_closure`'s Step 1, transform-independent.
  have hpointwise : ∀ r ∈ Set.Ioi (0 : ℝ), oz_h eta sigma rho r =
      c_HS eta sigma r + rho * radial3d_conv (c_HS eta sigma) (oz_h eta sigma rho) r := by
    intro r hrpos
    by_cases hr : r < sigma
    · exact hcore r ⟨hrpos, hr⟩
    · exact oz_h_satisfies_conv_ext hsigma hex (not_lt.mp hr) (hintA1 r (not_lt.mp hr))
        (hintA2 r (not_lt.mp hr))
  -- Step 2: apply `radial_fourier` to both sides.
  have hsum : (∫ r in Set.Ioi (0 : ℝ), r * c_HS eta sigma r * Real.sin (k * r)) +
      rho * (∫ r in Set.Ioi (0 : ℝ),
        r * radial3d_conv (c_HS eta sigma) (oz_h eta sigma rho) r * Real.sin (k * r)) =
      ∫ r in Set.Ioi (0 : ℝ), r * oz_h eta sigma rho r * Real.sin (k * r) := by
    rw [← MeasureTheory.integral_const_mul,
        ← MeasureTheory.integral_add hintB1 (hintConv.const_mul rho)]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    change r * c_HS eta sigma r * Real.sin (k * r) +
        rho * (r * radial3d_conv (c_HS eta sigma) (oz_h eta sigma rho) r * Real.sin (k * r)) =
      r * oz_h eta sigma rho r * Real.sin (k * r)
    rw [hpointwise r hr]
    ring
  have hfourier : radial_fourier (oz_h eta sigma rho) k =
      radial_fourier (c_HS eta sigma) k +
        rho * radial_fourier (radial3d_conv (c_HS eta sigma) (oz_h eta sigma rho)) k := by
    unfold radial_fourier
    rw [← hsum]
    ring
  -- Step 3: `radial_fourier_conv` factors the convolution transform (correct, unlike the
  -- disproven `radial_laplace_conv`).
  rw [radial_fourier_conv hk htsIntC hjointC] at hfourier
  -- Step 4: rearrange to the `H·(1-ρC) = C` form.
  linear_combination hfourier

/-- **Task OZ.9b: the Fourier-domain hard-sphere OZ equation, conditional only on the
routine integrability side-conditions — Gap B is now supplied by `oz_core_closure`
(Task OZ.9a), not an externally-threaded hypothesis.** Direct specialization of
`oz_fourier_oz_eq_of_core_closure`; the only change from that theorem is replacing `hcore`
with `oz_core_closure hsigma heta_def heta_lt`. This is the most complete, trustworthy result
in the whole `radial_laplace_conv`/`oz_laplace_oz_eq` lineage: Gap A (proved,
`OZExteriorBridge.lean`), the convolution theorem (proved, `radial_fourier_conv`, no
`radial_laplace_conv`-style false claim), and Gap B (`oz_core_closure`, numerically verified)
are all now accounted for by name, with only the routine integrability hypotheses remaining
open. -/
theorem oz_fourier_oz_eq_of_PY_core {eta sigma rho k : ℝ}
    (hsigma : 0 < sigma) (hrho : 0 < rho) (hk : 0 < k)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) (heta_lt : eta < 1)
    (huniq : ∃! h : ℝ → ℝ, OzFixedPt eta sigma rho h ∧ ContinuousOn h (Set.Ici sigma)
        ∧ ∃ C, ∀ r, |h r| ≤ C)
    (hintA1 : ∀ r, sigma ≤ r → IntervalIntegrable
      (fun t => t * c_HS eta sigma t * (sigma ^ 2 - (r - t) ^ 2) *
        if r < sigma + t then (1 : ℝ) else 0) MeasureTheory.volume 0 sigma)
    (hintA2 : ∀ r, sigma ≤ r → IntervalIntegrable
      (fun t => t * c_HS eta sigma t *
        ∫ s' in (max (r - t) sigma)..(r + t), s' * oz_h eta sigma rho s')
      MeasureTheory.volume 0 sigma)
    (htsIntC : ∀ r ∈ Set.Ioi (0 : ℝ), Integrable
      (fun p : ℝ × ℝ =>
        p.1 * c_HS eta sigma p.1 *
          (Set.Icc |r - p.1| (r + p.1)).indicator (fun s => s * oz_h eta sigma rho s) p.2)
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))))
    (hjointC : Integrable
      (fun p : ℝ × ℝ × ℝ =>
        (p.2.1 * c_HS eta sigma p.2.1) *
          (Set.Icc |p.1 - p.2.1| (p.1 + p.2.1)).indicator
            (fun s => s * oz_h eta sigma rho s) p.2.2 *
          Real.sin (k * p.1))
      ((volume.restrict (Set.Ioi 0)).prod
        ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0)))))
    (hintB1 : Integrable (fun r => r * c_HS eta sigma r * Real.sin (k * r))
      (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hintConv : Integrable
      (fun r => r * radial3d_conv (c_HS eta sigma) (oz_h eta sigma rho) r * Real.sin (k * r))
      (MeasureTheory.volume.restrict (Set.Ioi 0))) :
    (radial_fourier (oz_h eta sigma rho) k) *
      (1 - rho * radial_fourier (c_HS eta sigma) k) = radial_fourier (c_HS eta sigma) k :=
  oz_fourier_oz_eq_of_core_closure hsigma huniq.exists hk
    (oz_core_closure hsigma hrho heta_def heta_lt huniq)
    hintA1 hintA2 htsIntC hjointC hintB1 hintConv

end FMSA.HardSphere
