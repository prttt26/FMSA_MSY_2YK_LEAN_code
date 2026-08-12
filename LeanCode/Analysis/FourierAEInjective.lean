/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib.Analysis.Fourier.Inversion

/-!
# L¹ Fourier transform is a.e.-injective (from Mathlib's inversion formula)

The MML.15 mixture-DCF symmetry transfer needs: an integrable function whose Fourier transform
vanishes is zero a.e. (equivalently, `𝓕 f = 𝓕 g` a.e.-determines `f`).  Earlier notes flagged this
"Fourier a.e.-injectivity" as **absent in Mathlib** and treated it as a research-scale obstacle.

That is now **stale**: `Mathlib/Analysis/Fourier/Inversion.lean`
(`MeasureTheory.Integrable.fourierInv_fourier_eq`) gives `𝓕⁻(𝓕 f) v = f v` at every continuity
point of `f`, provided `f` and `𝓕 f` are integrable.  The general inversion needs `𝓕 f` integrable —
which the mixture DCF's transform fails — but for the **symmetry difference** the transform is
identically `0`, and `𝓕 f = 0` is trivially integrable.  So the inversion applies with
`integrable_zero`, and since `𝓕⁻ 0 = 0` it yields `f = 0` at every continuity point, hence a.e. when
`f` is continuous a.e. (the mixture DCF jumps only on the measure-zero set `{v = λᵢⱼ}`).

* **`ae_eq_zero_of_fourier_eq_zero`** — `Integrable f`, `𝓕 f = 0`, `f` cont. a.e. ⟹ `f = 0` a.e.
* **`ae_eq_of_fourier_eq`** — the difference form consumed by the DCF symmetry transfer:
  `𝓕 f = 𝓕 g`, both continuous a.e. ⟹ `f = g` a.e.

All axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

/-- **L¹ Fourier a.e.-injectivity, vanishing-transform form.**  An integrable `f` on a
finite-dimensional real inner product space with `𝓕 f = 0` that is continuous almost everywhere is
`0` a.e.  Uses Mathlib's inversion at continuity points; the required `Integrable (𝓕 f)` is trivial
here (`𝓕 f = 0`), and `𝓕⁻ 0 = 0`, so the inversion `𝓕⁻(𝓕 f) v = f v` reads `0 = f v`. -/
theorem ae_eq_zero_of_fourier_eq_zero {V E : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {f : V → E} (hf : Integrable f) (hFf : 𝓕 f = 0)
    (hcont : ∀ᵐ v, ContinuousAt f v) :
    f =ᵐ[MeasureTheory.volume] 0 := by
  have h'f : Integrable (𝓕 f) := by rw [hFf]; exact integrable_zero _ _ _
  filter_upwards [hcont] with v hv
  have hinv := hf.fourierInv_fourier_eq h'f hv
  rw [hFf] at hinv
  have hz : (𝓕⁻ (0 : V → E)) v = 0 := by simp [Real.fourierInv_eq]
  rw [hz] at hinv
  exact hinv.symm

/-- **L¹ Fourier a.e.-injectivity, difference form.**  Two integrable functions with equal Fourier
transforms, both continuous almost everywhere, agree a.e.  This is the shape the MML.15
mixture-DCF symmetry consumes: `𝓕(matDCF i k) = 𝓕(matDCF k i)` (the momentum symmetry `Cmix0` is
symmetric) ⟹ `matDCF i k = matDCF k i` a.e. -/
theorem ae_eq_of_fourier_eq {V E : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {f g : V → E} (hf : Integrable f) (hg : Integrable g) (hFeq : 𝓕 f = 𝓕 g)
    (hcontf : ∀ᵐ v, ContinuousAt f v) (hcontg : ∀ᵐ v, ContinuousAt g v) :
    f =ᵐ[MeasureTheory.volume] g := by
  have hsub : 𝓕 (f - g) = 0 := by
    funext w
    have hIf := (Real.fourierIntegral_convergent_iff (V := V) (E := E) w).2 hf
    have hIg := (Real.fourierIntegral_convergent_iff (V := V) (E := E) w).2 hg
    rw [Real.fourier_eq]
    have hpt : ∀ v, 𝐞 (-⟪v, w⟫) • (f - g) v
        = 𝐞 (-⟪v, w⟫) • f v - 𝐞 (-⟪v, w⟫) • g v := fun v => by
      rw [Pi.sub_apply, smul_sub]
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_sub hIf hIg,
      ← Real.fourier_eq, ← Real.fourier_eq, congrFun hFeq w, sub_self, Pi.zero_apply]
  have hcontd : ∀ᵐ v, ContinuousAt (f - g) v := by
    filter_upwards [hcontf, hcontg] with v h1 h2 using h1.sub h2
  have hd := ae_eq_zero_of_fourier_eq_zero (hf.sub hg) hsub hcontd
  filter_upwards [hd] with v hv
  have hv0 : (f - g) v = (0 : V → E) v := hv
  rw [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at hv0
  exact hv0
