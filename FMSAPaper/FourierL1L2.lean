import Mathlib.Analysis.Fourier.LpSpace

/-! The actual integral and L2 Fourier transforms coincide on L1 intersect L2.
This is proved via Schwartz tests and the fundamental lemma, without an
integrability assumption on the Fourier transform and without a new axiom. -/
noncomputable section
open MeasureTheory Filter Topology FourierTransform SchwartzMap
open scoped BigOperators ContDiff

namespace FMSA.Paper.FourierL1L2
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem integral_fourier_test (f : V → ℂ) (hf : Integrable f) (g : 𝓢(V, ℂ)) :
    (∫ x, (𝓕 g : 𝓢(V, ℂ)) x * f x) = ∫ x, g x * (𝓕 f) x := by
  simpa using! VectorFourier.integral_bilin_fourierIntegral_eq_flip
    (ContinuousLinearMap.mul ℂ ℂ) (L := innerₗ V)
    Real.continuous_fourierChar continuous_inner g.integrable hf

/-- Equality against every Schwartz test identifies the L2 transform with the
classical integral transform, before a.e. uniqueness is invoked. -/
theorem L2_fourier_test (f : V → ℂ) (hf : Integrable f) (h2 : MemLp f 2 volume)
    (g : 𝓢(V, ℂ)) :
    (∫ x, g x * ((𝓕 (h2.toLp f) : Lp ℂ 2 (volume : Measure V)) : V → ℂ) x) =
      ∫ x, g x * (𝓕 f) x := by
  have he := congrArg (fun A : 𝓢'(V, ℂ) => A g)
    (Lp.fourier_toTemperedDistribution_eq (h2.toLp f))
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply, smul_eq_mul] at he
  calc
    _ = ∫ x, (𝓕 g : 𝓢(V, ℂ)) x * (h2.toLp f : V → ℂ) x := he.symm
    _ = ∫ x, (𝓕 g : 𝓢(V, ℂ)) x * f x := by
      apply integral_congr_ae
      filter_upwards [h2.coeFn_toLp] with x hx
      rw [hx]
    _ = _ := integral_fourier_test f hf g

/-- The abstract L2 Fourier transform is the actual integral Fourier transform
almost everywhere, with no premise about Fourier integrability. -/
theorem L2_fourier_ae_integral (f : V → ℂ) (hf : Integrable f) (h2 : MemLp f 2 volume) :
    (((𝓕 (h2.toLp f) : Lp ℂ 2 (volume : Measure V)) : V → ℂ)) =ᵐ[volume] 𝓕 f := by
  apply ae_eq_of_integral_contDiff_smul_eq
  · exact (Lp.memLp (𝓕 (h2.toLp f) : Lp ℂ 2 (volume : Measure V))).locallyIntegrable (by norm_num)
  · exact (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hf).locallyIntegrable
  · intro g hg hc
    let test : 𝓢(V, ℂ) := (hc.comp_left (show Complex.ofReal (0 : ℝ) = 0 by simp)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hg)
    have he := L2_fourier_test f hf h2 test
    simpa [test, Complex.real_smul] using he

end FMSA.Paper.FourierL1L2

/-- info: 'FMSA.Paper.FourierL1L2.integral_fourier_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.FourierL1L2.integral_fourier_test

/-- info: 'FMSA.Paper.FourierL1L2.L2_fourier_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.FourierL1L2.L2_fourier_test

/-- info: 'FMSA.Paper.FourierL1L2.L2_fourier_ae_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.FourierL1L2.L2_fourier_ae_integral
