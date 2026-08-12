/-
Copyright (c) 2026 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import LeanCode.HSMixture.MatrixBaxterFourierWH

/-!
# The matrix Wiener–Khinchin identity `hWK` — general `N`

`MatBaxterFourierWH` was reduced (`MatrixBaxterFourierWH`) to the matrix **Wiener–Khinchin
identity** `hWK`: `∑ₗ q̃ᵢₗ·conj(q̃ⱼₗ) = (∫mSCᵢⱼcos + ∫mSCⱼᵢcos) + i(∫mSCᵢⱼsin − ∫mSCⱼᵢsin)`.  This
file proves it, reducing to the scalar correlation-theorem facts and — at bottom — a Fubini swap.

* `triangle_swap` — **the analytic crux**: the triangular Fubini swap
  `∫ x in 0..σ ∫ y in x..σ Φ = ∫ y in 0..σ ∫ x in 0..y Φ` (indicator + `integral_integral_swap`; the
  off-diagonal null set is handled by `setIntegral_congr_ae` + `Real.volume_singleton`).
* `corrCos_eq_lower` / `corrSin_eq_lower` — the correlation transform to the lower-triangle iterated
  integral `∫ t in 0..σ, f t · ∫ s in 0..t, g s · trig(k(t−s))` (via `triangle_swap` + a shift CoV
  `integral_comp_sub_left`).
* `upper_eq_corrCos` / `upper_eq_negCorrSin` — the upper triangle equals `corrCos g f` (cos even)
  resp. `−corrSin g f` (sin odd), via `triangle_swap` + `cos_neg`/`sin_neg`.
* `corrCos_add` / `corrSin_sub` — the **scalar Wiener–Khinchin identities**
  `Cf·Cg + Sf·Sg = corrCos f g + corrCos g f` and `Sf·Cg − Cf·Sg = corrSin f g − corrSin g f`
  (product → square via `cos_sub`/`sin_sub`, split via `integral_add_adjacent_intervals`, then the
  two triangle lemmas).
* `mscCos_eq_sum` / `mscSin_eq_sum` — `mSCᵢⱼ`'s transform is `∑ₗ` of the correlation transforms.
* `hWK_matrix` — the matrix `hWK`, assembled from the scalar identities (`qtil_mul_conj_qtil`)
  summed over the intermediate species.

Integrability side-conditions are carried as explicit hypotheses (the `radial_fourier_conv`
precedent).  So `hWK_matrix`, fed the proved `corrCos_add`/`corrSin_sub` per species pair,
discharges the `hWK` input of `matBaxterFourierWH_of_wk_sym` — modulo those integrability facts.
-/

open MeasureTheory
namespace FMSA.MixtureOzStar
open FMSA.HardSphere
variable {N : ℕ}

/-! ### The triangular Fubini swap (the analytic crux) -/

/-- **Triangular Fubini swap.**  `∫ x in 0..σ, ∫ y in x..σ, Φ x y = ∫ y in 0..σ, ∫ x in 0..y, Φ x y`
— the lower-triangular region `{0 ≤ x ≤ y ≤ σ}` integrated in either order.  Via the indicator form
over `Ioc 0 σ` and `integral_integral_swap`; the diagonal `x = y` (a null set) is bridged by
`setIntegral_congr_ae`. -/
theorem triangle_swap (Phi : ℝ → ℝ → ℝ) {sigma : ℝ} (hsigma : 0 ≤ sigma)
    (hint : Integrable (Function.uncurry (fun x y => (Set.Ioc x sigma).indicator (Phi x) y))
      ((volume.restrict (Set.Ioc (0:ℝ) sigma)).prod (volume.restrict (Set.Ioc (0:ℝ) sigma)))) :
    ∫ x in (0:ℝ)..sigma, ∫ y in x..sigma, Phi x y
      = ∫ y in (0:ℝ)..sigma, ∫ x in (0:ℝ)..y, Phi x y := by
  have hL : ∀ x ∈ Set.Ioc (0:ℝ) sigma, (∫ y in x..sigma, Phi x y)
      = ∫ y in Set.Ioc (0:ℝ) sigma, (Set.Ioc x sigma).indicator (Phi x) y := by
    intro x hx
    rw [intervalIntegral.integral_of_le hx.2, ← MeasureTheory.integral_indicator measurableSet_Ioc,
        MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro z hz
    exact Set.indicator_of_notMem (fun hc => hz (Set.Ioc_subset_Ioc_left hx.1.le hc)) _
  rw [intervalIntegral.integral_of_le hsigma,
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioc hL,
      MeasureTheory.integral_integral_swap hint, intervalIntegral.integral_of_le hsigma]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
  intro y hy
  dsimp only
  rw [intervalIntegral.integral_of_le hy.1.le,
      show (∫ x in Set.Ioc (0:ℝ) y, Phi x y)
        = ∫ x in Set.Ioc (0:ℝ) sigma, (Set.Ioc (0:ℝ) y).indicator (fun x' => Phi x' y) x from ?_]
  · apply MeasureTheory.setIntegral_congr_ae measurableSet_Ioc
    have hne : ∀ᵐ x' ∂(volume : Measure ℝ), x' ≠ y := by
      rw [ae_iff]; have : {a : ℝ | ¬ a ≠ y} = {y} := by ext a; simp
      rw [this]; exact Real.volume_singleton
    filter_upwards [hne] with x' hx' hmem
    simp only [Set.indicator_apply, Set.mem_Ioc]
    by_cases hlt : x' < y
    · rw [if_pos ⟨hlt, hy.2⟩, if_pos ⟨hmem.1, hlt.le⟩]
    · rw [if_neg (fun h => hlt h.1), if_neg (fun h => hlt (lt_of_le_of_ne h.2 hx'))]
  · rw [← MeasureTheory.integral_indicator measurableSet_Ioc,
        MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro z hz
    exact Set.indicator_of_notMem (fun hc => hz (Set.Ioc_subset_Ioc_right hy.2 hc)) _

/-! ### Correlation transforms -/

/-- The one-sided correlation `Corr(f,g)(v) = ∫_v^σ f(t)·g(t−v) dt`. -/
noncomputable def corr (f g : ℝ → ℝ) (sigma v : ℝ) : ℝ := ∫ t in v..sigma, f t * g (t - v)
/-- Cosine transform of the correlation. -/
noncomputable def corrCos (f g : ℝ → ℝ) (sigma k : ℝ) : ℝ :=
  ∫ v in (0:ℝ)..sigma, corr f g sigma v * Real.cos (k * v)
/-- Sine transform of the correlation. -/
noncomputable def corrSin (f g : ℝ → ℝ) (sigma k : ℝ) : ℝ :=
  ∫ v in (0:ℝ)..sigma, corr f g sigma v * Real.sin (k * v)

/-- **`corrCos` as a lower-triangle iterated integral.**  `corrCos f g = ∫ t, f t · ∫ s in 0..t,
g s · cos(k(t−s))`, via `triangle_swap` + the shift CoV `s = t − v`. -/
theorem corrCos_eq_lower (f g : ℝ → ℝ) (sigma k : ℝ) (hsigma : 0 ≤ sigma)
    (hint : Integrable (Function.uncurry
      (fun v t => (Set.Ioc v sigma).indicator (fun t' => f t' * g (t' - v) * Real.cos (k * v)) t))
      ((volume.restrict (Set.Ioc (0:ℝ) sigma)).prod (volume.restrict (Set.Ioc (0:ℝ) sigma)))) :
    corrCos f g sigma k
      = ∫ t in (0:ℝ)..sigma, f t * ∫ s in (0:ℝ)..t, g s * Real.cos (k * (t - s)) := by
  unfold corrCos corr
  have h1 : ∀ v, (∫ t in v..sigma, f t * g (t - v)) * Real.cos (k * v)
      = ∫ t in v..sigma, f t * g (t - v) * Real.cos (k * v) := by
    intro v; rw [intervalIntegral.integral_mul_const]
  simp_rw [h1]
  rw [triangle_swap (fun v t => f t * g (t - v) * Real.cos (k * v)) hsigma hint]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [show (fun v => f t * g (t - v) * Real.cos (k * v))
        = (fun v => f t * (g (t - v) * Real.cos (k * v))) from by funext v; ring,
      intervalIntegral.integral_const_mul]
  congr 1
  have hcong : (∫ v in (0:ℝ)..t, g (t - v) * Real.cos (k * v))
             = ∫ v in (0:ℝ)..t, (fun s => g s * Real.cos (k * (t - s))) (t - v) := by
    apply intervalIntegral.integral_congr; intro v _; dsimp only
    rw [show t - (t - v) = v from by ring]
  rw [hcong, intervalIntegral.integral_comp_sub_left (fun s => g s * Real.cos (k * (t - s))) t]
  simp only [sub_self, sub_zero]

/-- **`corrSin` as a lower-triangle iterated integral** (sin analog of `corrCos_eq_lower`). -/
theorem corrSin_eq_lower (f g : ℝ → ℝ) (sigma k : ℝ) (hsigma : 0 ≤ sigma)
    (hint : Integrable (Function.uncurry
      (fun v t => (Set.Ioc v sigma).indicator (fun t' => f t' * g (t' - v) * Real.sin (k * v)) t))
      ((volume.restrict (Set.Ioc (0:ℝ) sigma)).prod (volume.restrict (Set.Ioc (0:ℝ) sigma)))) :
    corrSin f g sigma k
      = ∫ t in (0:ℝ)..sigma, f t * ∫ s in (0:ℝ)..t, g s * Real.sin (k * (t - s)) := by
  unfold corrSin corr
  have h1 : ∀ v, (∫ t in v..sigma, f t * g (t - v)) * Real.sin (k * v)
      = ∫ t in v..sigma, f t * g (t - v) * Real.sin (k * v) := by
    intro v; rw [intervalIntegral.integral_mul_const]
  simp_rw [h1]
  rw [triangle_swap (fun v t => f t * g (t - v) * Real.sin (k * v)) hsigma hint]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [show (fun v => f t * g (t - v) * Real.sin (k * v))
        = (fun v => f t * (g (t - v) * Real.sin (k * v))) from by funext v; ring,
      intervalIntegral.integral_const_mul]
  congr 1
  have hcong : (∫ v in (0:ℝ)..t, g (t - v) * Real.sin (k * v))
             = ∫ v in (0:ℝ)..t, (fun s => g s * Real.sin (k * (t - s))) (t - v) := by
    apply intervalIntegral.integral_congr; intro v _; dsimp only
    rw [show t - (t - v) = v from by ring]
  rw [hcong, intervalIntegral.integral_comp_sub_left (fun s => g s * Real.sin (k * (t - s))) t]
  simp only [sub_self, sub_zero]

/-- **Upper triangle = `corrCos g f`** (cos is even), via `triangle_swap` + `cos_neg`. -/
theorem upper_eq_corrCos (f g : ℝ → ℝ) (sigma k : ℝ) (hsigma : 0 ≤ sigma)
    (hsw : Integrable (Function.uncurry (fun t s => (Set.Ioc t sigma).indicator
        (fun s' => f t * g s' * Real.cos (k * (t - s'))) s))
      ((volume.restrict (Set.Ioc (0:ℝ) sigma)).prod (volume.restrict (Set.Ioc (0:ℝ) sigma))))
    (hlg : corrCos g f sigma k
        = ∫ t in (0:ℝ)..sigma, g t * ∫ s in (0:ℝ)..t, f s * Real.cos (k * (t - s))) :
    (∫ t in (0:ℝ)..sigma, ∫ s in t..sigma, f t * g s * Real.cos (k * (t - s)))
      = corrCos g f sigma k := by
  rw [triangle_swap (fun t s => f t * g s * Real.cos (k * (t - s))) hsigma hsw, hlg]
  apply intervalIntegral.integral_congr; intro s _; dsimp only
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr; intro t _; dsimp only
  rw [show k * (t - s) = -(k * (s - t)) from by ring, Real.cos_neg]; ring

/-- **Upper triangle = `−corrSin g f`** (sin is odd), via `triangle_swap` + `sin_neg`. -/
theorem upper_eq_negCorrSin (f g : ℝ → ℝ) (sigma k : ℝ) (hsigma : 0 ≤ sigma)
    (hsw : Integrable (Function.uncurry (fun t s => (Set.Ioc t sigma).indicator
        (fun s' => f t * g s' * Real.sin (k * (t - s'))) s))
      ((volume.restrict (Set.Ioc (0:ℝ) sigma)).prod (volume.restrict (Set.Ioc (0:ℝ) sigma))))
    (hlg : corrSin g f sigma k
        = ∫ t in (0:ℝ)..sigma, g t * ∫ s in (0:ℝ)..t, f s * Real.sin (k * (t - s))) :
    (∫ t in (0:ℝ)..sigma, ∫ s in t..sigma, f t * g s * Real.sin (k * (t - s)))
      = - corrSin g f sigma k := by
  rw [triangle_swap (fun t s => f t * g s * Real.sin (k * (t - s))) hsigma hsw, hlg,
      ← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr; intro s _; dsimp only
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr; intro t _; dsimp only
  rw [show k * (t - s) = -(k * (s - t)) from by ring, Real.sin_neg]; ring

/-! ### The scalar Wiener–Khinchin identities -/

/-- **Scalar Wiener–Khinchin (cosine).**  `Cf·Cg + Sf·Sg = corrCos f g + corrCos g f`, where
`Cf = ∫₀^σ f·cos`, `Sf = ∫₀^σ f·sin`.  Product → square (`cos_sub`), split
(`integral_add_adjacent_intervals`), then `corrCos_eq_lower` + `upper_eq_corrCos`. -/
theorem corrCos_add (f g : ℝ → ℝ) (sigma k : ℝ)
    (hInnerC : ∀ t, IntervalIntegrable
      (fun s => f t * Real.cos (k*t) * (g s * Real.cos (k*s))) volume 0 sigma)
    (hInnerS : ∀ t, IntervalIntegrable
      (fun s => f t * Real.sin (k*t) * (g s * Real.sin (k*s))) volume 0 sigma)
    (hOuterC : IntervalIntegrable
      (fun t => ∫ s in (0:ℝ)..sigma, f t * Real.cos (k*t) * (g s * Real.cos (k*s))) volume 0 sigma)
    (hOuterS : IntervalIntegrable
      (fun t => ∫ s in (0:ℝ)..sigma, f t * Real.sin (k*t) * (g s * Real.sin (k*s))) volume 0 sigma)
    (hInAdj0 : ∀ t, IntervalIntegrable
      (fun s => f t * g s * Real.cos (k*(t-s))) volume 0 t)
    (hInAdjT : ∀ t, IntervalIntegrable
      (fun s => f t * g s * Real.cos (k*(t-s))) volume t sigma)
    (hLow : IntervalIntegrable
      (fun t => ∫ s in (0:ℝ)..t, f t * g s * Real.cos (k*(t-s))) volume 0 sigma)
    (hUp : IntervalIntegrable
      (fun t => ∫ s in t..sigma, f t * g s * Real.cos (k*(t-s))) volume 0 sigma)
    (hlow_fg : corrCos f g sigma k
      = ∫ t in (0:ℝ)..sigma, f t * ∫ s in (0:ℝ)..t, g s * Real.cos (k * (t - s)))
    (hupper : (∫ t in (0:ℝ)..sigma, ∫ s in t..sigma, f t * g s * Real.cos (k * (t - s)))
      = corrCos g f sigma k) :
    (∫ t in (0:ℝ)..sigma, f t * Real.cos (k * t)) * (∫ t in (0:ℝ)..sigma, g t * Real.cos (k * t))
      + (∫ t in (0:ℝ)..sigma, f t * Real.sin (k * t))
        * (∫ t in (0:ℝ)..sigma, g t * Real.sin (k * t))
      = corrCos f g sigma k + corrCos g f sigma k := by
  have hP : (∫ t in (0:ℝ)..sigma, f t * Real.cos (k*t))
        * (∫ t in (0:ℝ)..sigma, g t * Real.cos (k*t))
      + (∫ t in (0:ℝ)..sigma, f t * Real.sin (k*t)) * (∫ t in (0:ℝ)..sigma, g t * Real.sin (k*t))
      = ∫ t in (0:ℝ)..sigma, ∫ s in (0:ℝ)..sigma, f t * g s * Real.cos (k*(t-s)) := by
    rw [← intervalIntegral.integral_mul_const, ← intervalIntegral.integral_mul_const]
    simp_rw [← intervalIntegral.integral_const_mul]
    rw [← intervalIntegral.integral_add hOuterC hOuterS]
    apply intervalIntegral.integral_congr; intro t _; dsimp only
    rw [← intervalIntegral.integral_add (hInnerC t) (hInnerS t)]
    apply intervalIntegral.integral_congr; intro s _; dsimp only
    rw [show k*(t-s) = k*t - k*s from by ring, Real.cos_sub]; ring
  rw [hP]
  have hS : (∫ t in (0:ℝ)..sigma, ∫ s in (0:ℝ)..sigma, f t * g s * Real.cos (k*(t-s)))
      = (∫ t in (0:ℝ)..sigma, ∫ s in (0:ℝ)..t, f t * g s * Real.cos (k*(t-s)))
        + (∫ t in (0:ℝ)..sigma, ∫ s in t..sigma, f t * g s * Real.cos (k*(t-s))) := by
    rw [← intervalIntegral.integral_add hLow hUp]
    apply intervalIntegral.integral_congr; intro t _; dsimp only
    rw [intervalIntegral.integral_add_adjacent_intervals (hInAdj0 t) (hInAdjT t)]
  rw [hS, hlow_fg, hupper]
  congr 1
  apply intervalIntegral.integral_congr; intro t _; dsimp only
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr; intro s _; ring

/-- **Scalar Wiener–Khinchin (sine).**  `Sf·Cg − Cf·Sg = corrSin f g − corrSin g f` (`sin_sub`; the
upper triangle contributes `−corrSin g f` since `sin` is odd, so the split gives the difference). -/
theorem corrSin_sub (f g : ℝ → ℝ) (sigma k : ℝ)
    (hInnerC : ∀ t, IntervalIntegrable
      (fun s => f t * Real.sin (k*t) * (g s * Real.cos (k*s))) volume 0 sigma)
    (hInnerS : ∀ t, IntervalIntegrable
      (fun s => f t * Real.cos (k*t) * (g s * Real.sin (k*s))) volume 0 sigma)
    (hOuterC : IntervalIntegrable
      (fun t => ∫ s in (0:ℝ)..sigma, f t * Real.sin (k*t) * (g s * Real.cos (k*s))) volume 0 sigma)
    (hOuterS : IntervalIntegrable
      (fun t => ∫ s in (0:ℝ)..sigma, f t * Real.cos (k*t) * (g s * Real.sin (k*s))) volume 0 sigma)
    (hInAdj0 : ∀ t, IntervalIntegrable
      (fun s => f t * g s * Real.sin (k*(t-s))) volume 0 t)
    (hInAdjT : ∀ t, IntervalIntegrable
      (fun s => f t * g s * Real.sin (k*(t-s))) volume t sigma)
    (hLow : IntervalIntegrable
      (fun t => ∫ s in (0:ℝ)..t, f t * g s * Real.sin (k*(t-s))) volume 0 sigma)
    (hUp : IntervalIntegrable
      (fun t => ∫ s in t..sigma, f t * g s * Real.sin (k*(t-s))) volume 0 sigma)
    (hlow_fg : corrSin f g sigma k
      = ∫ t in (0:ℝ)..sigma, f t * ∫ s in (0:ℝ)..t, g s * Real.sin (k * (t - s)))
    (hupper : (∫ t in (0:ℝ)..sigma, ∫ s in t..sigma, f t * g s * Real.sin (k * (t - s)))
      = - corrSin g f sigma k) :
    (∫ t in (0:ℝ)..sigma, f t * Real.sin (k * t)) * (∫ t in (0:ℝ)..sigma, g t * Real.cos (k * t))
      - (∫ t in (0:ℝ)..sigma, f t * Real.cos (k * t))
        * (∫ t in (0:ℝ)..sigma, g t * Real.sin (k * t))
      = corrSin f g sigma k - corrSin g f sigma k := by
  have hP : (∫ t in (0:ℝ)..sigma, f t * Real.sin (k*t))
        * (∫ t in (0:ℝ)..sigma, g t * Real.cos (k*t))
      - (∫ t in (0:ℝ)..sigma, f t * Real.cos (k*t)) * (∫ t in (0:ℝ)..sigma, g t * Real.sin (k*t))
      = ∫ t in (0:ℝ)..sigma, ∫ s in (0:ℝ)..sigma, f t * g s * Real.sin (k*(t-s)) := by
    rw [← intervalIntegral.integral_mul_const, ← intervalIntegral.integral_mul_const]
    simp_rw [← intervalIntegral.integral_const_mul]
    rw [← intervalIntegral.integral_sub hOuterC hOuterS]
    apply intervalIntegral.integral_congr; intro t _; dsimp only
    rw [← intervalIntegral.integral_sub (hInnerC t) (hInnerS t)]
    apply intervalIntegral.integral_congr; intro s _; dsimp only
    rw [show k*(t-s) = k*t - k*s from by ring, Real.sin_sub]; ring
  rw [hP]
  have hS : (∫ t in (0:ℝ)..sigma, ∫ s in (0:ℝ)..sigma, f t * g s * Real.sin (k*(t-s)))
      = (∫ t in (0:ℝ)..sigma, ∫ s in (0:ℝ)..t, f t * g s * Real.sin (k*(t-s)))
        + (∫ t in (0:ℝ)..sigma, ∫ s in t..sigma, f t * g s * Real.sin (k*(t-s))) := by
    rw [← intervalIntegral.integral_add hLow hUp]
    apply intervalIntegral.integral_congr; intro t _; dsimp only
    rw [intervalIntegral.integral_add_adjacent_intervals (hInAdj0 t) (hInAdjT t)]
  rw [hS, hlow_fg, hupper]
  rw [show (∫ t in (0:ℝ)..sigma, f t * ∫ s in (0:ℝ)..t, g s * Real.sin (k * (t - s)))
        = ∫ t in (0:ℝ)..sigma, ∫ s in (0:ℝ)..t, f t * g s * Real.sin (k * (t - s)) from ?_]
  · ring
  · apply intervalIntegral.integral_congr; intro t _; dsimp only
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr; intro s _; ring

/-! ### The matrix `hWK`, assembled from the scalar identities -/

/-- The self-convolution's cosine transform splits over the intermediate species: `∫mSCᵢⱼcos =
∑ₗ corrCos(qᵢₗ, qⱼₗ)`. -/
theorem mscCos_eq_sum (q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma k : ℝ) (i j : Fin N)
    (hint : ∀ l, IntervalIntegrable
      (fun v => corr (q i l) (q j l) sigma v * Real.cos (k * v)) volume 0 sigma) :
    mscCos q sigma k i j = ∑ l, corrCos (q i l) (q j l) sigma k := by
  unfold mscCos corrCos
  rw [← intervalIntegral.integral_finsetSum (fun l _ => hint l)]
  apply intervalIntegral.integral_congr
  intro v _
  dsimp only
  rw [matSelfConv_apply, Finset.sum_mul]
  rfl

/-- The self-convolution's sine transform splits over the intermediate species. -/
theorem mscSin_eq_sum (q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma k : ℝ) (i j : Fin N)
    (hint : ∀ l, IntervalIntegrable
      (fun v => corr (q i l) (q j l) sigma v * Real.sin (k * v)) volume 0 sigma) :
    mscSin q sigma k i j = ∑ l, corrSin (q i l) (q j l) sigma k := by
  unfold mscSin corrSin
  rw [← intervalIntegral.integral_finsetSum (fun l _ => hint l)]
  apply intervalIntegral.integral_congr
  intro v _
  dsimp only
  rw [matSelfConv_apply, Finset.sum_mul]
  rfl

/-- The per-species-pair complex Wiener–Khinchin term, from the scalar identities. -/
theorem qtil_mul_conj_qtil (q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma k : ℝ) (i j l : Fin N)
    (hC : (qCos q sigma k i l) * (qCos q sigma k j l) + (qSin q sigma k i l) * (qSin q sigma k j l)
      = corrCos (q i l) (q j l) sigma k + corrCos (q j l) (q i l) sigma k)
    (hS : (qSin q sigma k i l) * (qCos q sigma k j l) - (qCos q sigma k i l) * (qSin q sigma k j l)
      = corrSin (q i l) (q j l) sigma k - corrSin (q j l) (q i l) sigma k) :
    qtil q sigma k i l * (starRingEnd ℂ) (qtil q sigma k j l)
      = ((corrCos (q i l) (q j l) sigma k + corrCos (q j l) (q i l) sigma k : ℝ) : ℂ)
        + ((corrSin (q i l) (q j l) sigma k - corrSin (q j l) (q i l) sigma k : ℝ) : ℂ)
          * Complex.I := by
  simp only [qtil, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, Complex.mul_im, Complex.add_im]
    ring_nf; ring_nf at hC; linarith [hC]
  · simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.add_re]
    ring_nf; ring_nf at hS; linarith [hS]

/-- **The matrix Wiener–Khinchin identity `hWK`** (general `N`), assembled from the scalar
identities `hC`/`hS` per species pair (`corrCos_add`/`corrSin_sub`) + the split integrability. -/
theorem hWK_matrix (q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma k : ℝ)
    (hintC : ∀ i j l, IntervalIntegrable
      (fun v => corr (q i l) (q j l) sigma v * Real.cos (k * v)) volume 0 sigma)
    (hintS : ∀ i j l, IntervalIntegrable
      (fun v => corr (q i l) (q j l) sigma v * Real.sin (k * v)) volume 0 sigma)
    (hC : ∀ i j l, (qCos q sigma k i l) * (qCos q sigma k j l)
        + (qSin q sigma k i l) * (qSin q sigma k j l)
      = corrCos (q i l) (q j l) sigma k + corrCos (q j l) (q i l) sigma k)
    (hS : ∀ i j l, (qSin q sigma k i l) * (qCos q sigma k j l)
        - (qCos q sigma k i l) * (qSin q sigma k j l)
      = corrSin (q i l) (q j l) sigma k - corrSin (q j l) (q i l) sigma k)
    (i j : Fin N) :
    ∑ l, qtil q sigma k i l * (starRingEnd ℂ) (qtil q sigma k j l)
      = ((mscCos q sigma k i j + mscCos q sigma k j i : ℝ) : ℂ)
        + ((mscSin q sigma k i j - mscSin q sigma k j i : ℝ) : ℂ) * Complex.I := by
  simp_rw [fun l => qtil_mul_conj_qtil q sigma k i j l (hC i j l) (hS i j l)]
  rw [mscCos_eq_sum q sigma k i j (hintC i j), mscCos_eq_sum q sigma k j i (hintC j i),
      mscSin_eq_sum q sigma k i j (hintS i j), mscSin_eq_sum q sigma k j i (hintS j i)]
  push_cast
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]

end FMSA.MixtureOzStar
