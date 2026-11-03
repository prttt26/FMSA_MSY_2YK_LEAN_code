import MSAConvergence.CanonicalRenewalFormula

/-! Exponential decay for the actual background-cancelled RDF excess under
full closed-right-half-plane canonicity. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open scoped BigOperators

namespace FMSA.Convergence.ActualExcessDecay
open FMSA.Paper FMSA.ExactMSA.MultiTailMixture MSAMixture FMSA.MatrixQ0
open FMSA.Convergence.RDFExponentialOrder FMSA.Convergence.CanonicalVolterraResolvent
open FMSA.Convergence.CanonicalRenewalFormula

variable {N : ℕ}

/-- Undoing a genuine positive exponential weight. -/
theorem weighted_bound_to_decay (a t v C : ℝ) (h : exp (a*t)*|v| ≤ C) :
    |v| ≤ C*exp (-a*t) := by
  have he : exp (-a*t)*exp (a*t) = 1 := by
    rw [← exp_add, show -a*t+a*t = 0 by ring, exp_zero]
  calc
    |v| = exp (-a*t)*(exp (a*t)*|v|) := by rw [← mul_assoc, he, one_mul]
    _ ≤ exp (-a*t)*C := mul_le_mul_of_nonneg_left h (exp_pos _).le
    _ = _ := mul_comm _ _

/-- Convolving two exponential envelopes gives the actual interval-length
factor. The input functions are the entries of the genuine source/resolvent. -/
theorem scalar_causal_convolution_decay
    (f g : ℝ → ℝ) (Cf Cg a : ℝ) (_hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg)
    (hf : ∀ t, 0 ≤ t → |f t| ≤ Cf*exp (-a*t))
    (hg : ∀ t, 0 ≤ t → |g t| ≤ Cg*exp (-a*t)) (t : ℝ) (ht : 0 ≤ t) :
    |causalIntervalConv g f t| ≤ Cf*Cg*t*exp (-a*t) := by
  have hb : ∀ u ∈ Set.uIoc (0 : ℝ) t, ‖g (t-u)*f u‖ ≤ Cf*Cg*exp (-a*t) := by
    intro u hu
    rw [Set.uIoc_of_le ht] at hu
    have hu0 : 0 ≤ u := hu.1.le
    have htu : 0 ≤ t-u := sub_nonneg.mpr hu.2
    calc
      ‖g (t-u)*f u‖ = |g (t-u)| * |f u| := by rw [Real.norm_eq_abs, abs_mul]
      _ ≤ (Cg*exp (-a*(t-u)))*(Cf*exp (-a*u)) :=
        mul_le_mul (hg _ htu) (hf _ hu0) (abs_nonneg _) (mul_nonneg hCg (exp_pos _).le)
      _ = Cf*Cg*(exp (-a*(t-u))*exp (-a*u)) := by ring
      _ = _ := by rw [← exp_add, show -a*(t-u)+ -a*u = -a*t by ring]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hb
  simpa only [causalIntervalConv, Real.norm_eq_abs, sub_zero, abs_of_nonneg ht,
    mul_assoc, mul_left_comm, mul_comm] using h

/-- A linear prefactor can be absorbed by halving a positive decay rate. -/
theorem linear_exponential_absorption (a t : ℝ) (ha : 0 < a) (ht : 0 ≤ t) :
    (1+t)*exp (-a*t) ≤ (1+(a/2)⁻¹)*exp (-(a/2)*t) := by
  have hb : 0 < a/2 := by linarith
  have he1 : 1 ≤ exp ((a/2)*t) := one_le_exp (mul_nonneg hb.le ht)
  have he2 : t ≤ (a/2)⁻¹*exp ((a/2)*t) := by
    have h : (a/2)*t ≤ exp ((a/2)*t) := (le_add_of_nonneg_right zero_le_one).trans (add_one_le_exp _)
    calc
      t = (a/2)⁻¹*((a/2)*t) := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hb), one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hb.le)
  calc
    (1+t)*exp (-a*t) ≤ (exp ((a/2)*t)+(a/2)⁻¹*exp ((a/2)*t))*exp (-a*t) :=
      mul_le_mul_of_nonneg_right (add_le_add he1 he2) (exp_pos _).le
    _ = (1+(a/2)⁻¹)*(exp ((a/2)*t)*exp (-a*t)) := by ring
    _ = _ := by rw [← exp_add, show (a/2)*t+ -a*t = -(a/2)*t by ring]

/-- Genuine matrix source response decay, retaining all intermediate
species and the F*r order. -/
theorem source_resolvent_response_decay
    (f r : ℝ → Matrix (Fin N) (Fin N) ℝ) (Cf Cr a : ℝ)
    (hCf : 0 ≤ Cf) (hCr : 0 ≤ Cr) (ha : 0 < a)
    (hf : ∀ t, 0 ≤ t → ∀ i j, |f t i j| ≤ Cf*exp (-a*t))
    (hr : ∀ t, 0 ≤ t → ∀ i j, |r t i j| ≤ Cr*exp (-a*t)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t, 0 ≤ t → ∀ i j,
      |sourceResolventResponse f r t i j| ≤ D*exp (-(a/2)*t) := by
  let K : ℝ := N*Cf*Cr
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨(Cf+K)*(1+(a/2)⁻¹), by positivity, ?_⟩
  intro t ht i j
  have hconv (m : Fin N) := scalar_causal_convolution_decay (fun u => f u i m)
    (fun u => r u m j) Cf Cr a hCf hCr (fun u hu => hf u hu i m) (fun u hu => hr u hu m j) t ht
  have hsum : |∑ m, causalIntervalConv (fun u => r u m j) (fun u => f u i m) t| ≤ K*t*exp (-a*t) := by
    calc
      _ ≤ ∑ m : Fin N, |causalIntervalConv (fun u => r u m j) (fun u => f u i m) t| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _m : Fin N, Cf*Cr*t*exp (-a*t) := Finset.sum_le_sum (fun m _ => hconv m)
      _ = _ := by simp [K]; ring
  calc
    _ ≤ |f t i j|+|∑ m, causalIntervalConv (fun u => r u m j) (fun u => f u i m) t| := abs_add_le _ _
    _ ≤ Cf*exp (-a*t)+K*t*exp (-a*t) := add_le_add (hf t ht i j) hsum
    _ = (Cf+K*t)*exp (-a*t) := by ring
    _ ≤ ((Cf+K)*(1+t))*exp (-a*t) := mul_le_mul_of_nonneg_right (by nlinarith) (exp_pos _).le
    _ = (Cf+K)*((1+t)*exp (-a*t)) := by ring
    _ ≤ (Cf+K)*((1+(a/2)⁻¹)*exp (-(a/2)*t)) :=
      mul_le_mul_of_nonneg_left (linear_exponential_absorption a t ha ht) (add_nonneg hCf hK)
    _ = _ := by ring

/-- Full canonicity gives genuine exponential decay of the existing real
RDF excess, using its actual cancelled source. The conclusion concerns the
closed causal half-line, not the max-extended negative-time representative. -/
theorem actual_excess_canonical_decay {T : Type*} [Fintype T]
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 ≤ sigma i) (hv : vacMix rho sigma ≠ 0)
    (p : TailMatrix T N × TailMatrix T N)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)) :
    ∃ epsilon D : ℝ, 0 < epsilon ∧ 0 ≤ D ∧ ∀ t, 0 ≤ t → ∀ i j,
      |nonlinearRDFExcess z rho sigma p.1 p.2 t i j| ≤ D*exp (-epsilon*t) := by
  obtain ⟨delta, _b, Br, hd, hdz, _hb, hBr, hres⟩ :=
    actual_kernel_resolvent_canonical z hz rho sigma hsigma p hcanon
  have ha : 0 < delta/2 := by linarith
  obtain ⟨Cf, hCf, hsource⟩ := nonlinearExcessSource_weighted_bounded z rho sigma p.1 p.2
    hz hsigma hv (delta/2) (fun u => by linarith [hdz u])
  have hf (t : ℝ) (ht : 0 ≤ t) (i j : Fin N) :
      |nonlinearExcessSource z rho sigma p.1 p.2 t i j| ≤ Cf*exp (-(delta/2)*t) := by
    apply weighted_bound_to_decay
    exact (mul_le_mul_of_nonneg_left
      (FMSA.matrixAbsSum_entry_le (nonlinearExcessSource z rho sigma p.1 p.2 t) i j)
      (exp_pos _).le).trans (hsource t ht)
  have hr (t : ℝ) (ht : 0 ≤ t) (i j : Fin N) :
      |actualKernelResolvent z rho sigma p t i j| ≤ Br*exp (-(delta/2)*t) := by
    simpa only [neg_div] using (hres i j).2.1 t ht
  obtain ⟨D, hD, hdec⟩ := source_resolvent_response_decay _ _ Cf Br (delta/2) hCf hBr ha hf hr
  refine ⟨(delta/2)/2, D, by linarith, hD, ?_⟩
  intro t ht i j
  rw [actual_excess_resolvent_formula z hz rho sigma hsigma hv p t ht]
  exact hdec t ht i j

/-- A true entrywise exponential envelope supplies weighted real L1 at
all weaker decay weights, rather than assuming the target integrability. -/
theorem entry_decay_weighted_integrable
    (f : ℝ → ℝ) (hf : Continuous f) (epsilon D : ℝ)
    (hdec : ∀ t, 0 ≤ t → |f t| ≤ D*exp (-epsilon*t))
    (c : ℝ) (hc : -epsilon < c) :
    IntegrableOn (fun t : ℝ => exp (-c*t)*f t) (Ioi 0) := by
  apply exp_order_real_integrable f hf.aestronglyMeasurable (-epsilon) D c _ hc
  intro t ht
  have he : exp (-(-epsilon)*t)*exp (-epsilon*t) = 1 := by
    rw [← exp_add, show -(-epsilon)*t+ -epsilon*t = 0 by ring, exp_zero]
  calc
    _ ≤ exp (-(-epsilon)*t)*(D*exp (-epsilon*t)) :=
      mul_le_mul_of_nonneg_left (hdec t ht.le) (exp_pos _).le
    _ = D*(exp (-(-epsilon)*t)*exp (-epsilon*t)) := by ring
    _ = _ := by rw [he, mul_one]

/-- Actual excess positive-axis L1, real exponentially weighted L1 and
honest complex Laplace integrability on a half-plane containing its entire
Fourier boundary, including frequency zero. -/
theorem actual_excess_canonical_integrable {T : Type*} [Fintype T]
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 ≤ sigma i) (hv : vacMix rho sigma ≠ 0)
    (p : TailMatrix T N × TailMatrix T N)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)) :
    ∃ epsilon D : ℝ, 0 < epsilon ∧ 0 ≤ D ∧ ∀ i j,
      (∀ t, 0 ≤ t → |nonlinearRDFExcess z rho sigma p.1 p.2 t i j| ≤ D*exp (-epsilon*t)) ∧
      IntegrableOn (fun t : ℝ => nonlinearRDFExcess z rho sigma p.1 p.2 t i j) (Ioi 0) ∧
      (∀ c : ℝ, -epsilon < c → IntegrableOn
        (fun t : ℝ => exp (-c*t)*nonlinearRDFExcess z rho sigma p.1 p.2 t i j) (Ioi 0)) ∧
      ∀ s : ℂ, -epsilon < s.re → IntegrableOn
        (fun t : ℝ => (nonlinearRDFExcess z rho sigma p.1 p.2 t i j : ℂ)*Complex.exp (-s*(t : ℂ))) (Ioi 0) := by
  obtain ⟨epsilon, D, he, hD, hdec⟩ := actual_excess_canonical_decay z hz rho sigma hsigma hv p hcanon
  have hc := nonlinearRDFExcess_continuous z rho sigma p.1 p.2
  have hi (i j : Fin N) (c : ℝ) (h : -epsilon < c) :=
    entry_decay_weighted_integrable _ (hc.matrix_elem i j) epsilon D (fun t ht => hdec t ht i j) c h
  refine ⟨epsilon, D, he, hD, ?_⟩
  intro i j
  refine ⟨(fun t ht => hdec t ht i j), ?_, hi i j, ?_⟩
  · simpa only [neg_zero, zero_mul, exp_zero, one_mul] using hi i j 0 (by linarith)
  · intro s hs
    exact FMSA.complex_laplace_integrable _ (hc.matrix_elem i j).continuousOn s (hi i j s.re hs)

/-- The actual excess has the genuine finite-matrix Laplace formula on
an internally obtained negative half-plane, including the Fourier axis
and zero frequency. Both sides use actual integral transforms. -/
theorem actual_excess_canonical_laplace {T : Type*} [Fintype T]
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 ≤ sigma i) (hv : vacMix rho sigma ≠ 0)
    (p : TailMatrix T N × TailMatrix T N)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ s : ℂ, -epsilon < s.re →
      (∀ i j, IntegrableOn (fun t : ℝ =>
        (nonlinearRDFExcess z rho sigma p.1 p.2 t i j : ℂ)*Complex.exp (-s*(t : ℂ))) (Ioi 0)) ∧
      rdfMatrixLaplace (nonlinearRDFExcess z rho sigma p.1 p.2) s =
        rdfMatrixLaplace (nonlinearExcessSource z rho sigma p.1 p.2) s*
          (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)⁻¹ := by
  obtain ⟨delta, _b, Br, hd, hdz, _hb, _hBr, hres⟩ :=
    actual_kernel_resolvent_canonical z hz rho sigma hsigma p hcanon
  obtain ⟨Cf, _hCf, hsource⟩ := nonlinearExcessSource_weighted_bounded z rho sigma p.1 p.2
    hz hsigma hv (delta/2) (fun u => by linarith [hdz u])
  let f := nonlinearExcessSource z rho sigma p.1 p.2
  let r := actualKernelResolvent z rho sigma p
  let x := nonlinearRDFExcess z rho sigma p.1 p.2
  let v := sourceResolventResponse f r
  have hf : Continuous f := nonlinearExcessSource_continuous z rho sigma p.1 p.2
  have hr : Continuous r := kernel_resolvent_continuous _ _
  have hdec (t : ℝ) (ht : 0 ≤ t) (i j : Fin N) : |f t i j| ≤ Cf*exp (-(delta/2)*t) := by
    apply weighted_bound_to_decay
    exact (mul_le_mul_of_nonneg_left (FMSA.matrixAbsSum_entry_le (f t) i j) (exp_pos _).le).trans (hsource t ht)
  have he (t : ℝ) (ht : 0 ≤ t) : x t = v t :=
    actual_excess_resolvent_formula z hz rho sigma hsigma hv p t ht
  refine ⟨delta/2, by linarith, ?_⟩
  intro s hs
  have hfi (i j : Fin N) := entry_decay_weighted_integrable _ (hf.matrix_elem i j)
    (delta/2) Cf (fun t ht => hdec t ht i j) s.re hs
  have hri (i j : Fin N) := (hres i j).2.2.2.1 s.re (by simpa only [neg_div] using hs)
  obtain ⟨hvi, hvl⟩ := source_resolvent_response_laplace f r hf hr s hfi hri
  have heq (i j : Fin N) : EqOn
      (fun t : ℝ => (x t i j : ℂ)*Complex.exp (-s*(t : ℂ)))
      (fun t : ℝ => (v t i j : ℂ)*Complex.exp (-s*(t : ℂ))) (Ioi (0 : ℝ)) := by
    intro t ht
    change (x t i j : ℂ)*Complex.exp (-s*(t : ℂ)) = (v t i j : ℂ)*Complex.exp (-s*(t : ℂ))
    rw [he t ht.le]
  constructor
  · intro i j
    exact (integrableOn_congr_fun (heq i j) measurableSet_Ioi).mpr (hvi i j)
  · have hxl : rdfMatrixLaplace x s = rdfMatrixLaplace v s := by
      ext i j
      exact setIntegral_congr_fun measurableSet_Ioi (heq i j)
    have hrl : rdfMatrixLaplace r s =
        (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)⁻¹-1 := by
      ext i j
      exact ((hres i j).2.2.2.2 s (by simpa only [neg_div] using hs)).2
    rw [hxl, hvl, hrl, Matrix.mul_sub, Matrix.mul_one]
    abel

end FMSA.Convergence.ActualExcessDecay

/-- info: 'FMSA.Convergence.ActualExcessDecay.weighted_bound_to_decay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualExcessDecay.weighted_bound_to_decay

/-- info: 'FMSA.Convergence.ActualExcessDecay.scalar_causal_convolution_decay' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualExcessDecay.scalar_causal_convolution_decay

/-- info: 'FMSA.Convergence.ActualExcessDecay.linear_exponential_absorption' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualExcessDecay.linear_exponential_absorption

/-- info: 'FMSA.Convergence.ActualExcessDecay.source_resolvent_response_decay' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualExcessDecay.source_resolvent_response_decay

/-- info: 'FMSA.Convergence.ActualExcessDecay.actual_excess_canonical_decay' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualExcessDecay.actual_excess_canonical_decay

/-- info: 'FMSA.Convergence.ActualExcessDecay.entry_decay_weighted_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualExcessDecay.entry_decay_weighted_integrable

/-- info: 'FMSA.Convergence.ActualExcessDecay.actual_excess_canonical_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualExcessDecay.actual_excess_canonical_integrable

/-- info: 'FMSA.Convergence.ActualExcessDecay.actual_excess_canonical_laplace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualExcessDecay.actual_excess_canonical_laplace
