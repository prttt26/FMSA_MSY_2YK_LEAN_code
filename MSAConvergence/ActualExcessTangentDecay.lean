import MSAConvergence.ActualExcessSourceTangent

/-! Decay and genuine boundary integrability of the actual amplitude
excess tangent, using the cancelled actual linearized renewal. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open scoped BigOperators

namespace FMSA.Convergence.ActualExcessTangentDecay
open FMSA.Paper FMSA.ExactMSA.MultiTailMixture MSAMixture FMSA.MatrixQ0
open FMSA.Convergence.ActualRDFTangent FMSA.Convergence.RDFExponentialOrder
open FMSA.Convergence.CanonicalResolventAnalysis
open FMSA.Convergence.ActualLaplaceJets FMSA.Convergence.CanonicalFourierLaplace
open FMSA.Convergence.CanonicalVolterraResolvent FMSA.Convergence.CanonicalRenewalFormula
open FMSA.Convergence.ActualExcessDecay FMSA.Convergence.ActualExcessSourceTangent

variable {N : ℕ} {T : Type*} [Fintype T]

/-- A genuine continuous right renewal with a proved exponential growth
bound equals the concrete source response. All Laplace integrability and
the sufficiently strong common damping are proved internally. -/
theorem right_renewal_eq_source_response
    (q f y : ℝ → Matrix (Fin N) (Fin N) ℝ) (hq : Continuous q) (hf : Continuous f) (hy : Continuous y)
    (M B gamma C : ℝ) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hk : ∀ t, 0 ≤ t → FMSA.matrixAbsSum (q t) ≤ M)
    (hb : ∀ t, 0 ≤ t → FMSA.matrixAbsSum (f t) ≤ B*(1+t))
    (hY : ∀ i j t, 0 ≤ t → exp (-gamma*t)*|y t i j| ≤ C)
    (heq : ∀ i j t, 0 ≤ t → y t i j = f t i j+
      ∑ m, causalIntervalConv (fun u => q u m j) (fun u => y u i m) t) :
    ∀ t, 0 ≤ t → y t = sourceResolventResponse f (kernelResolvent q hq) t := by
  let c := max (M+1) gamma+2
  have hcM : M+1 < c := by dsimp [c]; linarith [le_max_left (M+1) gamma]
  have hcg : gamma < c := by dsimp [c]; linarith [le_max_right (M+1) gamma]
  have hyi (s : ℂ) (hs : gamma < s.re) (i j : Fin N) :
      IntegrableOn (fun t : ℝ => exp (-s.re*t)*y t i j) (Ioi 0) :=
    exp_order_real_integrable _ (hy.matrix_elem i j).aestronglyMeasurable gamma C s.re
      (fun t ht => hY i j t ht.le) hs
  have hyl (s : ℂ) (hsM : M+1 < s.re) (hsg : gamma < s.re) :
      rdfMatrixLaplace y s = rdfMatrixLaplace (rightVolterra q f hq hf) s := by
    have hq0 : ∀ t, 0 ≤ t → exp (-(0 : ℝ)*t)*FMSA.matrixAbsSum (q t) ≤ M := by
      simpa only [neg_zero, zero_mul, exp_zero, one_mul] using hk
    have hqi := matrix_exp_order_damped_integrable q hq 0 M hq0 s.re (by linarith)
    have hfi := affine_matrix_damped_integrable f hf B hB hb s.re (by linarith)
    have he := complexMatrixLaplace_right_renewal q f y hq hf hy s hqi hfi (hyi s hsg) heq
    have hu := bounded_matrix_laplace_isUnit q hq M hk s (by linarith) (by linarith)
    have hd := (Matrix.isUnit_iff_isUnit_det _).mp hu
    have hx := Matrix.mul_nonsing_inv_cancel_right (1-rdfMatrixLaplace q s) (rdfMatrixLaplace y s) hd
    rw [he] at hx
    exact hx.symm.trans (right_volterra_laplace_eq q f hq hf M B hM hB hk hb s hsM).symm
  have hentry (i j : Fin N) : EqOn (fun t : ℝ => (y t i j : ℂ))
      (fun t : ℝ => (rightVolterra q f hq hf t i j : ℂ)) (Ici (0 : ℝ)) := by
    apply causal_laplace_injective _ _ c
      (Complex.continuous_ofReal.comp (hy.matrix_elem i j)).continuousOn
      (Complex.continuous_ofReal.comp ((right_volterra_continuous q f hq hf).matrix_elem i j)).continuousOn
      (ofReal_damped_integrable _ c (hyi (c : ℂ) (by simpa using hcg) i j))
      (ofReal_damped_integrable _ c (right_volterra_damped_integrable q f hq hf M B hM hB hk hb c hcM i j))
    intro xi
    let s := verticalPoint c (2*π*xi)
    change rdfMatrixLaplace y s i j = rdfMatrixLaplace (rightVolterra q f hq hf) s i j
    exact congrFun (congrFun (hyl s (by simpa [s, verticalPoint] using hcM)
      (by simpa [s, verticalPoint] using hcg)) i) j
  intro t ht
  have he : y t = rightVolterra q f hq hf t := by
    ext i j
    exact Complex.ofReal_injective (hentry i j (show t ∈ Ici (0 : ℝ) from ht))
  exact he.trans (right_volterra_variation_of_constants q f hq hf M B hM hB hk hb t ht)

/-- Weakening a proved exponential envelope retains the same constant. -/
theorem weaken_decay_rate (a b t D v : ℝ) (hab : a ≤ b) (ht : 0 ≤ t) (hD : 0 ≤ D)
    (h : |v| ≤ D*exp (-b*t)) : |v| ≤ D*exp (-a*t) :=
  h.trans (mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by nlinarith)) hD)

/-- A matrix exponential envelope gives an internally computed affine
absolute-sum bound suitable for genuine far-right Laplace uniqueness. -/
theorem matrix_decay_affine_bound (f : ℝ → Matrix (Fin N) (Fin N) ℝ) (a D : ℝ)
    (ha : 0 ≤ a) (hD : 0 ≤ D) (h : ∀ t, 0 ≤ t → ∀ i j, |f t i j| ≤ D*exp (-a*t)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t, 0 ≤ t → FMSA.matrixAbsSum (f t) ≤ B*(1+t) := by
  obtain ⟨B, hB, hb⟩ := matrix_weighted_bound_of_entries f 0 (fun i j => by
    refine ⟨D, hD, ?_⟩
    intro t ht
    simpa only [neg_zero, zero_mul, exp_zero, one_mul, mul_one] using
      weaken_decay_rate 0 a t D (f t i j) ha ht hD (h t ht i j))
  refine ⟨B, hB, ?_⟩
  intro t ht
  have he : FMSA.matrixAbsSum (f t) ≤ B := by
    simpa only [zero_mul, exp_zero, one_mul] using hb t ht
  exact he.trans (by nlinarith)

/-- Genuine source for the actual linearized excess renewal. -/
def excessTangentForcing (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (t : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of (fun i j => excessSourceVariation z rho sigma p v i j t+
    ∑ m, causalIntervalConv (kernelVariation z rho sigma p v m j)
      (fun u => nonlinearRDFExcess z rho sigma p.1 p.2 u i m) t)

/-- The actual linearized forcing is continuous at every real time. -/
theorem excess_tangent_forcing_continuous (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) : Continuous (excessTangentForcing z rho sigma p v) := by
  apply continuous_matrix
  intro i j
  exact (excess_source_variation_continuous z rho sigma p v i j).add
    (continuous_finsetSum _ (fun m _ => causal_convolution_continuous _ _
      (kernel_variation_continuous z rho sigma p v m j)
      ((nonlinearRDFExcess_continuous z rho sigma p.1 p.2).matrix_elem i m)))

/-- The actual excess Frechet derivative has the existing global continuity. -/
theorem excess_variation_continuous (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) :
    Continuous (fun t : ℝ => Matrix.of (fun i j => excessVariation z rho sigma p v i j t)) := by
  apply continuous_matrix
  intro i j
  change Continuous (excessVariation z rho sigma p v i j)
  have he : excessVariation z rho sigma p v i j = causalVariation z rho sigma p v i j :=
    funext (excessVariation_eq_causalVariation z rho sigma p v i j)
  rw [he]
  exact causalVariation_continuous z rho sigma p v i j

/-- Decay of a source plus a correctly ordered convolution, where the
point source and the convolution input may be different actual fields. -/
theorem source_convolution_decay
    (s f r : ℝ → Matrix (Fin N) (Fin N) ℝ) (Cs Cf Cr a : ℝ)
    (hCs : 0 ≤ Cs) (hCf : 0 ≤ Cf) (hCr : 0 ≤ Cr) (ha : 0 < a)
    (hs : ∀ t, 0 ≤ t → ∀ i j, |s t i j| ≤ Cs*exp (-a*t))
    (hf : ∀ t, 0 ≤ t → ∀ i j, |f t i j| ≤ Cf*exp (-a*t))
    (hr : ∀ t, 0 ≤ t → ∀ i j, |r t i j| ≤ Cr*exp (-a*t)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t, 0 ≤ t → ∀ i j,
      |s t i j+∑ m, causalIntervalConv (fun u => r u m j) (fun u => f u i m) t| ≤ D*exp (-(a/2)*t) := by
  obtain ⟨Dz, hDz, hz⟩ := source_resolvent_response_decay f r Cf Cr a hCf hCr ha hf hr
  refine ⟨Cs+Dz+Cf, by positivity, ?_⟩
  intro t ht i j
  have hs' := weaken_decay_rate (a/2) a t Cs (s t i j) (by linarith) ht hCs (hs t ht i j)
  have hf' := weaken_decay_rate (a/2) a t Cf (f t i j) (by linarith) ht hCf (hf t ht i j)
  have he : s t i j+∑ m, causalIntervalConv (fun u => r u m j) (fun u => f u i m) t =
      s t i j+sourceResolventResponse f r t i j-f t i j := by
    simp only [sourceResolventResponse, Matrix.of_apply]
    ring
  rw [he]
  calc
    _ ≤ |s t i j+sourceResolventResponse f r t i j|+|f t i j| := abs_sub _ _
    _ ≤ (|s t i j|+|sourceResolventResponse f r t i j|)+|f t i j| :=
      add_le_add (abs_add_le _ _) le_rfl
    _ ≤ (Cs*exp (-(a/2)*t)+Dz*exp (-(a/2)*t))+Cf*exp (-(a/2)*t) :=
      add_le_add (add_le_add hs' (hz t ht i j)) hf'
    _ = _ := by ring

/-- The actual linearized forcing decays, using the genuine cancelled
source derivative and kernel derivative, not assumed tangent tail data. -/
theorem actual_excess_tangent_forcing_decay
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 ≤ sigma i) (hv : vacMix rho sigma ≠ 0)
    (p v : TailMatrix T N × TailMatrix T N)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)) :
    ∃ a D : ℝ, 0 < a ∧ 0 ≤ D ∧ ∀ t, 0 ≤ t → ∀ i j,
      |excessTangentForcing z rho sigma p v t i j| ≤ D*exp (-a*t) := by
  obtain ⟨ex, Dx, hex, hDx, hx⟩ := actual_excess_canonical_decay z hz rho sigma hsigma hv p hcanon
  obtain ⟨delta, _b, _Br, hd, hdz, _hb, _hBr, _hr⟩ :=
    actual_kernel_resolvent_canonical z hz rho sigma hsigma p hcanon
  let a := min ex (delta/2)
  have ha : 0 < a := lt_min hex (by linarith)
  have haz (u : T) : a ≤ z u := (min_le_right ex (delta/2)).trans (by linarith [hdz u])
  obtain ⟨Cs, hCs, hs⟩ := excess_source_variation_weighted_bounded z hz rho sigma hsigma hv p v a haz
  obtain ⟨Cq, hCq, hq⟩ := kernel_variation_weighted_bounded z rho sigma p v a haz
  have hentry (g : ℝ → Matrix (Fin N) (Fin N) ℝ) (C : ℝ)
      (h : ∀ t, 0 ≤ t → exp (a*t)*FMSA.matrixAbsSum (g t) ≤ C) (t : ℝ) (ht : 0 ≤ t) (i j : Fin N) :
      |g t i j| ≤ C*exp (-a*t) := by
    apply weighted_bound_to_decay
    exact (mul_le_mul_of_nonneg_left (FMSA.matrixAbsSum_entry_le (g t) i j) (exp_pos _).le).trans (h t ht)
  obtain ⟨D, hD, hdec⟩ := source_convolution_decay
    (fun t => Matrix.of (fun i j => excessSourceVariation z rho sigma p v i j t))
    (nonlinearRDFExcess z rho sigma p.1 p.2)
    (fun t => Matrix.of (fun i j => kernelVariation z rho sigma p v i j t)) Cs Dx Cq a hCs hDx hCq ha
    (hentry _ Cs hs)
    (fun t ht i j => weaken_decay_rate a ex t Dx _ (min_le_left _ _) ht hDx (hx t ht i j))
    (hentry _ Cq hq)
  exact ⟨a/2, D, by linarith, hD, hdec⟩

/-- The actual Frechet tangent is the canonical real source response of
its genuine linearized forcing. Only canonicity at the fixed base point
is required, not a nearby canonical family or a curve of BH roots. -/
theorem actual_excess_tangent_resolvent_formula
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 ≤ sigma i) (hv : vacMix rho sigma ≠ 0)
    (p v : TailMatrix T N × TailMatrix T N)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)) :
    ∀ t, 0 ≤ t → Matrix.of (fun i j => excessVariation z rho sigma p v i j t) =
      sourceResolventResponse (excessTangentForcing z rho sigma p v) (actualKernelResolvent z rho sigma p) t := by
  obtain ⟨a, D, ha, hD, hforcing⟩ := actual_excess_tangent_forcing_decay z hz rho sigma hsigma hv p v hcanon
  obtain ⟨B, hB, hb⟩ := matrix_decay_affine_bound _ a D ha.le hD hforcing
  obtain ⟨M, _C, hM, _hC, hlocal⟩ := actual_kernel_source_local_bounds z hz rho sigma hsigma p
  obtain ⟨gamma, C, _hg, _hC', hY⟩ := actual_causal_entries_exponential_order z hz rho sigma hsigma p v
  apply right_renewal_eq_source_response _ _ _
    (nonlinearCausalKernel_continuous z rho sigma p.1 p.2)
    (excess_tangent_forcing_continuous z rho sigma p v)
    (excess_variation_continuous z rho sigma p v) M B gamma C hM hB
    (fun t ht => (hlocal.self_of_nhds t ht).1) hb
  · intro i j t ht
    simpa only [Matrix.of_apply, excessVariation_eq_causalVariation] using (hY i j t ht).2
  · intro i j t ht
    have he := actual_excess_tangent_renewal z rho sigma p v i j t ht
    change excessVariation z rho sigma p v i j t =
      (excessSourceVariation z rho sigma p v i j t+
        ∑ m, causalIntervalConv (kernelVariation z rho sigma p v m j)
          (fun u => nonlinearRDFExcess z rho sigma p.1 p.2 u i m) t)+
      ∑ m, causalIntervalConv (fun u => nonlinearCausalKernel z rho sigma p.1 p.2 u m j)
        (excessVariation z rho sigma p v i m) t
    exact he.trans (by abel)

/-- Genuine exponential decay of the existing amplitude Frechet tangent
of the actual RDF excess under full base-point canonicity. -/
theorem actual_excess_tangent_canonical_decay
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 ≤ sigma i) (hv : vacMix rho sigma ≠ 0)
    (p v : TailMatrix T N × TailMatrix T N)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)) :
    ∃ epsilon D : ℝ, 0 < epsilon ∧ 0 ≤ D ∧ ∀ t, 0 ≤ t → ∀ i j,
      |excessVariation z rho sigma p v i j t| ≤ D*exp (-epsilon*t) := by
  obtain ⟨af, Cf, haf, hCf, hf⟩ := actual_excess_tangent_forcing_decay z hz rho sigma hsigma hv p v hcanon
  obtain ⟨delta, _b, Cr, hd, _hdz, _hb, hCr, hres⟩ :=
    actual_kernel_resolvent_canonical z hz rho sigma hsigma p hcanon
  let a := min af (delta/2)
  have ha : 0 < a := lt_min haf (by linarith)
  have hr (t : ℝ) (ht : 0 ≤ t) (i j : Fin N) :
      |actualKernelResolvent z rho sigma p t i j| ≤ Cr*exp (-a*t) := by
    apply weaken_decay_rate a (delta/2) t Cr _ (min_le_right _ _) ht hCr
    simpa only [neg_div] using (hres i j).2.1 t ht
  obtain ⟨D, hD, hdec⟩ := source_resolvent_response_decay _ _ Cf Cr a hCf hCr ha
    (fun t ht i j => weaken_decay_rate a af t Cf _ (min_le_left _ _) ht hCf (hf t ht i j)) hr
  refine ⟨a/2, D, by linarith, hD, ?_⟩
  intro t ht i j
  have he := congrFun (congrFun (actual_excess_tangent_resolvent_formula z hz rho sigma hsigma hv p v hcanon t ht) i) j
  rw [show excessVariation z rho sigma p v i j t =
    sourceResolventResponse (excessTangentForcing z rho sigma p v) (actualKernelResolvent z rho sigma p) t i j from he]
  exact hdec t ht i j

/-- Actual amplitude-tangent positive-axis L1 and real weighted L1, with
honest complex Laplace integrability beyond an obtained negative cutoff.
This includes every Fourier frequency and zero. -/
theorem actual_excess_tangent_canonical_integrable
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 ≤ sigma i) (hv : vacMix rho sigma ≠ 0)
    (p v : TailMatrix T N × TailMatrix T N)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)) :
    ∃ epsilon D : ℝ, 0 < epsilon ∧ 0 ≤ D ∧ ∀ i j,
      (∀ t, 0 ≤ t → |excessVariation z rho sigma p v i j t| ≤ D*exp (-epsilon*t)) ∧
      IntegrableOn (excessVariation z rho sigma p v i j) (Ioi 0) ∧
      (∀ c : ℝ, -epsilon < c → IntegrableOn
        (fun t : ℝ => exp (-c*t)*excessVariation z rho sigma p v i j t) (Ioi 0)) ∧
      ∀ s : ℂ, -epsilon < s.re → IntegrableOn
        (fun t : ℝ => (excessVariation z rho sigma p v i j t : ℂ)*Complex.exp (-s*(t : ℂ))) (Ioi 0) := by
  obtain ⟨epsilon, D, he, hD, hdec⟩ := actual_excess_tangent_canonical_decay z hz rho sigma hsigma hv p v hcanon
  have hc := excess_variation_continuous z rho sigma p v
  have hcij (i j : Fin N) : Continuous (excessVariation z rho sigma p v i j) := hc.matrix_elem i j
  have hi (i j : Fin N) (c : ℝ) (h : -epsilon < c) : IntegrableOn
      (fun t : ℝ => exp (-c*t)*excessVariation z rho sigma p v i j t) (Ioi 0) :=
    entry_decay_weighted_integrable _ (hcij i j) epsilon D (fun t ht => hdec t ht i j) c h
  refine ⟨epsilon, D, he, hD, ?_⟩
  intro i j
  refine ⟨(fun t ht => hdec t ht i j), ?_, hi i j, ?_⟩
  · simpa only [neg_zero, zero_mul, exp_zero, one_mul] using hi i j 0 (by linarith)
  · intro s hs
    exact FMSA.complex_laplace_integrable _ (hcij i j).continuousOn s (hi i j s.re hs)

/-- Honest Fourier-boundary Laplace formula for the actual Frechet excess
tangent. The cancelled forcing is integrable even at zero frequency; no
Laplace integral of the uncancelled affine background is introduced. -/
theorem actual_excess_tangent_boundary_laplace
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 ≤ sigma i) (hv : vacMix rho sigma ≠ 0)
    (p v : TailMatrix T N × TailMatrix T N)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s))
    (s : ℂ) (hs : 0 ≤ s.re) :
    (∀ i j, IntegrableOn (fun t : ℝ =>
      (excessVariation z rho sigma p v i j t : ℂ)*Complex.exp (-s*(t : ℂ))) (Ioi 0)) ∧
    rdfMatrixLaplace (fun t : ℝ => Matrix.of (fun i j => excessVariation z rho sigma p v i j t)) s =
      rdfMatrixLaplace (excessTangentForcing z rho sigma p v) s*
        (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)⁻¹ := by
  obtain ⟨epsilon, _D, he, _hD, hY⟩ := actual_excess_tangent_canonical_integrable z hz rho sigma hsigma hv p v hcanon
  obtain ⟨af, Cf, haf, _hCf, hf⟩ := actual_excess_tangent_forcing_decay z hz rho sigma hsigma hv p v hcanon
  have hq := nonlinearCausalKernel_continuous z rho sigma p.1 p.2
  have hqi (i j : Fin N) : IntegrableOn
      (fun t : ℝ => exp (-s.re*t)*nonlinearCausalKernel z rho sigma p.1 p.2 t i j) (Ioi 0) := by
    have hi := nonlinearCausalKernel_weighted_entry_integrable z rho sigma p.1 p.2 hsigma (-s.re)
      (fun u => by linarith [hz u]) i j
    apply hi.mono' ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (hq.matrix_elem i j)).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _ht
    change ‖exp (-s.re*t)*nonlinearCausalKernel z rho sigma p.1 p.2 t i j‖ ≤
      exp (-s.re*t)*|nonlinearCausalKernel z rho sigma p.1 p.2 t i j|
    simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _)]
    exact le_rfl
  have hfi (i j : Fin N) := entry_decay_weighted_integrable _
    ((excess_tangent_forcing_continuous z rho sigma p v).matrix_elem i j) af Cf
    (fun t ht => hf t ht i j) s.re (by linarith)
  have hyi (i j : Fin N) := (hY i j).2.2.1 s.re (by linarith)
  have hrenew := complexMatrixLaplace_right_renewal _ _ _ hq
    (excess_tangent_forcing_continuous z rho sigma p v)
    (excess_variation_continuous z rho sigma p v) s hqi hfi hyi (by
      intro i j t ht
      have htangent := actual_excess_tangent_renewal z rho sigma p v i j t ht
      change excessVariation z rho sigma p v i j t =
        (excessSourceVariation z rho sigma p v i j t+
          ∑ m, causalIntervalConv (kernelVariation z rho sigma p v m j)
            (fun u => nonlinearRDFExcess z rho sigma p.1 p.2 u i m) t)+
        ∑ m, causalIntervalConv (fun u => nonlinearCausalKernel z rho sigma p.1 p.2 u m j)
          (excessVariation z rho sigma p v i m) t
      exact htangent.trans (by abel))
  refine ⟨(fun i j => (hY i j).2.2.2 s (by linarith)), ?_⟩
  have hu := (Matrix.isUnit_iff_isUnit_det _).mp (hcanon s hs)
  have hi := Matrix.mul_nonsing_inv_cancel_right (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)
    (rdfMatrixLaplace (fun t : ℝ => Matrix.of (fun i j => excessVariation z rho sigma p v i j t)) s) hu
  rw [hrenew] at hi
  exact hi.symm

end FMSA.Convergence.ActualExcessTangentDecay

/-- info: 'FMSA.Convergence.ActualExcessTangentDecay.right_renewal_eq_source_response' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualExcessTangentDecay.right_renewal_eq_source_response

/-- info: 'FMSA.Convergence.ActualExcessTangentDecay.weaken_decay_rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualExcessTangentDecay.weaken_decay_rate

/-- info: 'FMSA.Convergence.ActualExcessTangentDecay.matrix_decay_affine_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualExcessTangentDecay.matrix_decay_affine_bound

/-- info: 'FMSA.Convergence.ActualExcessTangentDecay.excess_tangent_forcing_continuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualExcessTangentDecay.excess_tangent_forcing_continuous

/-- info: 'FMSA.Convergence.ActualExcessTangentDecay.excess_variation_continuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualExcessTangentDecay.excess_variation_continuous

/-- info: 'FMSA.Convergence.ActualExcessTangentDecay.source_convolution_decay' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualExcessTangentDecay.source_convolution_decay

/-- info: 'FMSA.Convergence.ActualExcessTangentDecay.actual_excess_tangent_forcing_decay' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualExcessTangentDecay.actual_excess_tangent_forcing_decay

/-- info: 'FMSA.Convergence.ActualExcessTangentDecay.actual_excess_tangent_resolvent_formula' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualExcessTangentDecay.actual_excess_tangent_resolvent_formula

/-- info: 'FMSA.Convergence.ActualExcessTangentDecay.actual_excess_tangent_canonical_decay' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualExcessTangentDecay.actual_excess_tangent_canonical_decay

/-- info: 'FMSA.Convergence.ActualExcessTangentDecay.actual_excess_tangent_canonical_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualExcessTangentDecay.actual_excess_tangent_canonical_integrable

/-- info: 'FMSA.Convergence.ActualExcessTangentDecay.actual_excess_tangent_boundary_laplace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualExcessTangentDecay.actual_excess_tangent_boundary_laplace
