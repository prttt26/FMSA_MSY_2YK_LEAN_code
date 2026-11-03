import MSAConvergence.CausalLaplaceL2
import MSAConvergence.CanonicalInverseCovariance

/-! A genuine causal L1/L2 time field for s/(s+1)^2 times the actual
canonical inverse. No unknown L2 field or Hardy assumption is supplied. -/
noncomputable section
open MeasureTheory Set Real Filter Topology FourierTransform
open scoped BigOperators
namespace FMSA.Convergence.RegularizedInverseField
open FMSA.Paper FMSA.Paper.ActualRDFParameters FMSA.ExactMSA.MultiTailMixture
open FMSA.Convergence.CanonicalVolterraResolvent FMSA.Convergence.CanonicalRenewalFormula
open FMSA.Convergence.CanonicalFourierLaplace FMSA.Convergence.CanonicalResolventAnalysis
open FMSA.Convergence.ActualExcessDecay FMSA.Convergence.ActualHRadialL2
open FMSA.Convergence.CanonicalInverseCovariance
variable {N : ℕ}

def filterScalar (t : ℝ) : ℝ := (1-t)*exp (-t)
def filterMatrix (t : ℝ) : Matrix (Fin N) (Fin N) ℝ := filterScalar t • 1

private theorem filterMatrix_continuous : Continuous (filterMatrix (N := N)) := by
  unfold filterMatrix filterScalar
  fun_prop

/-- The fixed rational regularizer has an explicit exponential time envelope. -/
theorem filter_scalar_bound (t : ℝ) (ht : 0 ≤ t) : |filterScalar t| ≤ 3*exp (-(1/2 : ℝ)*t) := by
  have hb : |1-t| ≤ 1+t := by
    have h := abs_add_le (1 : ℝ) (-t)
    simpa only [sub_eq_add_neg,abs_neg,abs_one,abs_of_nonneg ht] using h
  have h := linear_exponential_absorption 1 t zero_lt_one ht
  norm_num at h
  calc
    |filterScalar t| = |1-t| *exp (-t) := by rw [filterScalar,abs_mul,abs_of_pos (exp_pos _)]
    _ ≤ (1+t)*exp (-t) := mul_le_mul_of_nonneg_right hb (exp_pos _).le
    _ ≤ _ := by simpa only [neg_mul,one_mul,div_eq_mul_inv,mul_assoc] using h

private theorem filter_matrix_bound (t : ℝ) (ht : 0 ≤ t) (i j : Fin N) :
    |filterMatrix t i j| ≤ 3*exp (-(1/2 : ℝ)*t) := by
  by_cases h : i=j
  · simpa only [filterMatrix,Matrix.smul_apply,Matrix.one_apply,if_pos h,smul_eq_mul,mul_one] using filter_scalar_bound t ht
  · simp only [filterMatrix,Matrix.smul_apply,Matrix.one_apply,if_neg h,smul_eq_mul,mul_zero,abs_zero]
    positivity

/-- The honest regularizer Laplace integral on the entire closed right
half-plane, including zero, has its exact rational value. -/
theorem filter_matrix_laplace (s : ℂ) (hs : 0 ≤ s.re) :
    rdfMatrixLaplace (filterMatrix (N := N)) s = (s/(s+1)^2) • (1 : Matrix (Fin N) (Fin N) ℂ) := by
  have hs1 : 0 < (s+1).re := by simp only [Complex.add_re,Complex.one_re]; linarith
  have hs10 : s+1 ≠ 0 := by intro h; rw [h] at hs1; simp at hs1
  have hneg : (-(s+1)).re < 0 := by simp only [Complex.neg_re]; linarith
  have hi0 := integrableOn_exp_mul_complex_Ioi (a := -(s+1)) hneg 0
  have hi1 := FMSA.complex_first_integrable hs1
  have he (t : ℝ) : (filterScalar t : ℂ)*Complex.exp (-s*t) =
      Complex.exp (-(s+1)*t)-(t : ℂ)*Complex.exp (-(s+1)*t) := by
    simp only [filterScalar,Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_exp,Complex.ofReal_neg]
    have hx : Complex.exp (-(t : ℂ))*Complex.exp (-s*t) = Complex.exp (-(s+1)*t) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    rw [mul_assoc,hx]
    ring
  have hscalar : FMSA.causalComplexLaplace filterScalar s = s/(s+1)^2 := by
    unfold FMSA.causalComplexLaplace
    simp_rw [he]
    rw [integral_sub hi0 hi1,integral_exp_mul_complex_Ioi (a := -(s+1)) hneg 0,
      FMSA.complex_first_Ioi hs1]
    simp only [Complex.ofReal_zero,mul_zero,Complex.exp_zero,neg_div]
    field_simp [hs10]
    ring
  ext i j
  by_cases h : i=j
  · simpa only [rdfMatrixLaplace,FMSA.causalComplexLaplace,Matrix.of_apply,filterMatrix,Matrix.smul_apply,Matrix.one_apply,
      if_pos h,smul_eq_mul,mul_one] using hscalar
  · simp only [rdfMatrixLaplace,FMSA.causalComplexLaplace,Matrix.of_apply,filterMatrix,Matrix.smul_apply,Matrix.one_apply,
      if_neg h,smul_eq_mul,mul_zero,Complex.ofReal_zero,zero_mul,integral_zero]

variable {T : Type*} [Fintype T]

def response (z : T → ℝ) (ρ σ : Fin N → ℝ) (D G : TailMatrix T N) :
    ℝ → Matrix (Fin N) (Fin N) ℝ :=
  sourceResolventResponse filterMatrix (actualKernelResolvent z ρ σ (D,G))

def field (z : T → ℝ) (ρ σ : Fin N → ℝ) (D G : TailMatrix T N) (i j : Fin N) (t : ℝ) : ℂ :=
  (causalFull (fun u => response z ρ σ D G u i j) t : ℂ)

private theorem resolvent_continuous (z : T → ℝ) (ρ σ : Fin N → ℝ) (D G : TailMatrix T N) :
    Continuous (actualKernelResolvent z ρ σ (D,G)) :=
  kernel_resolvent_continuous _ _

private theorem response_continuous (z : T → ℝ) (ρ σ : Fin N → ℝ) (D G : TailMatrix T N) :
    Continuous (response z ρ σ D G) :=
  source_resolvent_response_continuous _ _ filterMatrix_continuous (resolvent_continuous z ρ σ D G)

/-- The constructed actual regularized inverse time field decays exponentially.
This is per-root existence; no bound on amplitudes is a premise. -/
theorem actual_response_decay (z : T → ℝ) (hz : ∀ u, 0 < z u) (ρ σ : Fin N → ℝ)
    (hσ : ∀ i, 0 ≤ σ i) (D G : TailMatrix T N)
    (hc : ∀ s : ℂ, 0 ≤ s.re → IsUnit (causalFactor z ρ σ D G s)) :
    ∃ epsilon B : ℝ, 0 < epsilon ∧ 0 ≤ B ∧ ∀ t : ℝ, 0 ≤ t → ∀ i j,
      |response z ρ σ D G t i j| ≤ B*exp (-epsilon*t) := by
  obtain ⟨delta,b,Br,hd,hdz,hdb,hBr,hres⟩ := actual_kernel_resolvent_canonical z hz ρ σ hσ (D,G) hc
  let a := min (1/2 : ℝ) (delta/2)
  have ha : 0 < a := lt_min (by norm_num) (by linarith)
  have hf (t : ℝ) (ht : 0 ≤ t) (i j : Fin N) : |filterMatrix t i j| ≤ 3*exp (-a*t) := by
    apply (filter_matrix_bound t ht i j).trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 3)
    apply exp_le_exp.mpr
    have h := min_le_left (1/2 : ℝ) (delta/2)
    dsimp only [a]
    nlinarith
  have hr (t : ℝ) (ht : 0 ≤ t) (i j : Fin N) :
      |actualKernelResolvent z ρ σ (D,G) t i j| ≤ Br*exp (-a*t) := by
    apply ((hres i j).2.1 t ht).trans
    apply mul_le_mul_of_nonneg_left _ hBr
    apply exp_le_exp.mpr
    have h := min_le_right (1/2 : ℝ) (delta/2)
    dsimp only [a]
    nlinarith
  obtain ⟨B,hB,h⟩ := source_resolvent_response_decay filterMatrix (actualKernelResolvent z ρ σ (D,G))
    3 Br a (by norm_num) hBr ha hf hr
  exact ⟨a/2,B,by linarith,hB,h⟩

/-- The actual constructed causal inverse field supplies BOTH global L1
and global L2; neither membership is passed in as an assumption. -/
theorem actual_field_L1_L2 (z : T → ℝ) (hz : ∀ u, 0 < z u) (ρ σ : Fin N → ℝ)
    (hσ : ∀ i, 0 ≤ σ i) (D G : TailMatrix T N)
    (hc : ∀ s : ℂ, 0 ≤ s.re → IsUnit (causalFactor z ρ σ D G s)) (i j : Fin N) :
    Integrable (field z ρ σ D G i j) ∧ MemLp (field z ρ σ D G i j) 2 volume := by
  obtain ⟨epsilon,B,he,hB,hdec⟩ := actual_response_decay z hz ρ σ hσ D G hc
  have hp : IntegrableOn (fun t : ℝ => response z ρ σ D G t i j) (Ioi 0) := by
    have h := entry_decay_weighted_integrable _ ((response_continuous z ρ σ D G).matrix_elem i j)
      epsilon B (fun t ht => hdec t ht i j) 0 (by linarith)
    simpa only [neg_zero,zero_mul,exp_zero,one_mul] using h
  have hi : Integrable (field z ρ σ D G i j) := (causalFull_integrable _ hp).ofReal
  refine ⟨hi,integrable_bounded_memLp_two _ hi B ?_⟩
  apply ae_of_all
  intro t
  by_cases ht : t ∈ Ici (0 : ℝ)
  · simp only [field,causalFull,indicator_of_mem ht,Complex.norm_real,Real.norm_eq_abs]
    have h := hdec t ht i j
    have he1 : exp (-epsilon*t) ≤ 1 := exp_le_one_iff.mpr (by change 0 ≤ t at ht; nlinarith)
    nlinarith
  · simp only [field,causalFull,indicator_of_notMem ht,Complex.ofReal_zero,norm_zero]
    exact hB

/-- The genuine closed-right-half-plane response transform is the rational
regularizer times the TRUE causal inverse, with the full matrix order. -/
theorem actual_response_laplace (z : T → ℝ) (hz : ∀ u, 0 < z u) (ρ σ : Fin N → ℝ)
    (hσ : ∀ i, 0 ≤ σ i) (D G : TailMatrix T N)
    (hc : ∀ s : ℂ, 0 ≤ s.re → IsUnit (causalFactor z ρ σ D G s)) (s : ℂ) (hs : 0 ≤ s.re) :
    rdfMatrixLaplace (response z ρ σ D G) s = (s/(s+1)^2) • (causalFactor z ρ σ D G s)⁻¹ := by
  obtain ⟨delta,b,Br,hd,hdz,hdb,hBr,hres⟩ := actual_kernel_resolvent_canonical z hz ρ σ hσ (D,G) hc
  have hf (i j : Fin N) : IntegrableOn (fun t : ℝ => exp (-s.re*t)*filterMatrix t i j) (Ioi 0) :=
    entry_decay_weighted_integrable _ (filterMatrix_continuous.matrix_elem i j) (1/2) 3
      (fun t ht => filter_matrix_bound t ht i j) s.re (by linarith)
  have hr (i j : Fin N) : IntegrableOn
      (fun t : ℝ => exp (-s.re*t)*actualKernelResolvent z ρ σ (D,G) t i j) (Ioi 0) :=
    (hres i j).2.2.2.1 s.re (by linarith)
  have hrl : rdfMatrixLaplace (actualKernelResolvent z ρ σ (D,G)) s =
      (causalFactor z ρ σ D G s)⁻¹-1 := by
    ext i j
    exact ((hres i j).2.2.2.2 s (by linarith)).2
  rw [response,(source_resolvent_response_laplace _ _ filterMatrix_continuous
    (resolvent_continuous z ρ σ D G) s hf hr).2,filter_matrix_laplace s hs,hrl]
  simp only [Matrix.smul_mul,Matrix.one_mul,Matrix.mul_sub,Matrix.mul_one]
  module

/-- The honest integral Fourier transform of the actual L1/L2 causal field
is the regularized actual inverse on the Fourier axis. -/
theorem actual_field_fourier (z : T → ℝ) (hz : ∀ u, 0 < z u) (ρ σ : Fin N → ℝ)
    (hσ : ∀ i, 0 ≤ σ i) (D G : TailMatrix T N)
    (hc : ∀ s : ℂ, 0 ≤ s.re → IsUnit (causalFactor z ρ σ D G s)) (i j : Fin N) (w : ℝ) :
    𝓕 (field z ρ σ D G i j) w =
      ((Complex.I*((2*Real.pi*w : ℝ) : ℂ))/(Complex.I*((2*Real.pi*w : ℝ) : ℂ)+1)^2)*
        (causalFactor z ρ σ D G (Complex.I*((2*Real.pi*w : ℝ) : ℂ)))⁻¹ i j := by
  have he : field z ρ σ D G i j = causalDamping (fun t : ℝ => (response z ρ σ D G t i j : ℂ)) 0 := by
    funext t
    by_cases ht : t ∈ Ici (0 : ℝ)
    · simp [field,causalFull,causalDamping,dampedField,ht]
    · simp [field,causalFull,causalDamping,ht]
  rw [he,causal_damping_fourier]
  have h := congrFun (congrFun (actual_response_laplace z hz ρ σ hσ D G hc
    (Complex.I*((2*Real.pi*w : ℝ) : ℂ)) (by simp)) i) j
  simpa only [rdfMatrixLaplace,FMSA.causalComplexLaplace,Matrix.of_apply,Matrix.smul_apply,smul_eq_mul,
    verticalPoint,Complex.ofReal_zero,zero_add,mul_comm] using h

/-- The actual positive-real Laplace integral of the SAME causal field. -/
theorem actual_field_positive_laplace (z : T → ℝ) (hz : ∀ u, 0 < z u) (ρ σ : Fin N → ℝ)
    (hσ : ∀ i, 0 ≤ σ i) (D G : TailMatrix T N)
    (hc : ∀ s : ℂ, 0 ≤ s.re → IsUnit (causalFactor z ρ σ D G s)) (i j : Fin N)
    (s : ℝ) (hs : 0 < s) :
    (∫ t in Ioi (0 : ℝ), field z ρ σ D G i j t*Complex.exp (-(s : ℂ)*t)) =
      (((s/(s+1)^2 : ℝ) : ℂ))*(causalFactor z ρ σ D G (s : ℂ))⁻¹ i j := by
  have h := congrFun (congrFun (actual_response_laplace z hz ρ σ hσ D G hc (s : ℂ)
    (by simpa using hs.le)) i) j
  change (∫ t in Ioi (0 : ℝ), (response z ρ σ D G t i j : ℂ)*Complex.exp (-(s : ℂ)*t)) = _ at h
  calc
    _ = ∫ t in Ioi (0 : ℝ), (response z ρ σ D G t i j : ℂ)*Complex.exp (-(s : ℂ)*t) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      simp only [field,causalFull,indicator_of_mem (show t ∈ Ici (0 : ℝ) from (show 0 < t from ht).le)]
    _ = _ := by simpa only [Matrix.smul_apply,smul_eq_mul,Complex.ofReal_div,Complex.ofReal_pow,
      Complex.ofReal_add,Complex.ofReal_one] using h

end FMSA.Convergence.RegularizedInverseField
/-- info: 'FMSA.Convergence.RegularizedInverseField.filter_scalar_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.RegularizedInverseField.filter_scalar_bound
/-- info: 'FMSA.Convergence.RegularizedInverseField.filter_matrix_laplace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.RegularizedInverseField.filter_matrix_laplace
/-- info: 'FMSA.Convergence.RegularizedInverseField.actual_response_decay' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.RegularizedInverseField.actual_response_decay
/-- info: 'FMSA.Convergence.RegularizedInverseField.actual_field_L1_L2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.RegularizedInverseField.actual_field_L1_L2
/-- info: 'FMSA.Convergence.RegularizedInverseField.actual_response_laplace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.RegularizedInverseField.actual_response_laplace
/-- info: 'FMSA.Convergence.RegularizedInverseField.actual_field_fourier' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.RegularizedInverseField.actual_field_fourier
/-- info: 'FMSA.Convergence.RegularizedInverseField.actual_field_positive_laplace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.RegularizedInverseField.actual_field_positive_laplace
