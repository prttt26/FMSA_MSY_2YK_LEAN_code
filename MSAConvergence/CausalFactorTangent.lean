import MSAConvergence.CanonicalVolterraResolvent
import MSAConvergence.SymplecticTangent

/-! Causal support and finite logarithmic response identities for canonical
factor tangents. The contact point carries no L1 point mass. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open scoped BigOperators FourierTransform RealInnerProductSpace
namespace FMSA.Convergence.CausalFactorTangent
open FMSA.ExactMSA.MultiTailMixture FMSA.ExactMSA.Breakpoint FMSA.MatrixQ0 MSAMixture

/-- Real-line Fourier reflection, with the frequency sign reversed. -/
theorem fourier_reflection (f : ℝ → ℂ) (w : ℝ) :
    𝓕 (fun t => f (-t)) w = 𝓕 f (-w) := by
  simpa only [LinearIsometryEquiv.coe_neg, Function.comp_def] using
    Real.fourier_comp_linearIsometry (LinearIsometryEquiv.neg ℝ) f w

/-- Actual L1 Fourier addition, retaining genuine integrability. -/
theorem fourier_add_L1 (f g : ℝ → ℂ) (hf : Integrable f) (hg : Integrable g) (w : ℝ) :
    𝓕 (fun t => f t+g t) w = 𝓕 f w+𝓕 g w := by
  have hif := (Real.fourierIntegral_convergent_iff (V := ℝ) (E := ℂ) w).2 hf
  have hig := (Real.fourierIntegral_convergent_iff (V := ℝ) (E := ℂ) w).2 hg
  rw [Real.fourier_eq, Real.fourier_eq, Real.fourier_eq]
  simp only [smul_add]
  exact integral_add hif hig

/-- A Fourier transform zero a.e. suffices for zero at every actual
continuity point; the transform is then genuinely L1 for inversion. -/
theorem zero_at_of_fourier_ae_zero (f : ℝ → ℂ) (hf : Integrable f)
    (hF : 𝓕 f =ᵐ[volume] 0) (t : ℝ) (hc : ContinuousAt f t) : f t = 0 := by
  have hFi : Integrable (𝓕 f) := (integrable_congr hF).mpr (integrable_zero _ _ _)
  have hinv := hf.fourierInv_fourier_eq hFi hc
  have hz : (𝓕⁻ (𝓕 f)) t = 0 := by
    rw [Real.fourierInv_eq]
    calc
      _ = ∫ w : ℝ, (0 : ℂ) := by
        apply integral_congr_ae
        filter_upwards [hF] with w hw
        simp only [hw, Pi.zero_apply, smul_zero]
      _ = 0 := by simp
  exact hinv.symm.trans hz

/-- The full causal-shift Fourier formula uses exactly physical k=2*pi*w. -/
theorem causal_shift_fourier (f : ℝ → ℝ) (a w : ℝ) :
    𝓕 (fun t => (causalShift f a t : ℂ)) w =
      Complex.exp (-(Complex.I*(2*π*w))*(a : ℂ))*
        FMSA.causalComplexLaplace f (Complex.I*(2*π*w)) := by
  rw [FMSA.MixtureBaxter.fourier_eq_zOfW]
  have hs : FMSA.MixtureBaxter.zOfW w = Complex.I*(2*π*w) := by
    unfold FMSA.MixtureBaxter.zOfW
    push_cast
    ring
  rw [hs]
  simpa only [neg_mul] using causalShift_complex_laplace f a (Complex.I*(2*π*w))

/-- Opposite causal support thresholds touch in exactly one point.
Fourier antisymmetry forces the first actual continuous half-line field
to vanish; closure then supplies zero at the causal origin as well. -/
theorem touching_causal_pair_zero (f g : ℝ → ℝ) (a : ℝ)
    (hf : Continuous f) (hif : IntegrableOn f (Ioi 0)) (hig : IntegrableOn g (Ioi 0))
    (hanti : ∀ w : ℝ, w ≠ 0 →
      𝓕 (fun t => (causalShift f a t : ℂ)) w+
        𝓕 (fun t => (causalShift g (-a) t : ℂ)) (-w) = 0) :
    EqOn f (fun _ => 0) (Ici (0 : ℝ)) := by
  let U := fun t : ℝ => (causalShift f a t : ℂ)
  let V := fun t : ℝ => (causalShift g (-a) t : ℂ)
  let H := fun t : ℝ => U t+V (-t)
  have hU : Integrable U := (causalShift_integrable f hif a).ofReal
  have hV : Integrable V := (causalShift_integrable g hig (-a)).ofReal
  have hH : Integrable H := hU.add hV.comp_neg
  have hFFT : 𝓕 H =ᵐ[volume] 0 := by
    filter_upwards [volume.ae_ne (0 : ℝ)] with w hw
    rw [show H = fun t => U t+V (-t) from rfl, fourier_add_L1 U (fun t => V (-t)) hU hV.comp_neg w,
      fourier_reflection]
    exact hanti w hw
  have hpos : EqOn f (fun _ => 0) (Ioi (0 : ℝ)) := by
    intro r hr
    change 0 < r at hr
    let t := r+a
    have ht : a < t := by dsimp only [t]; linarith
    have hlocal : H =ᶠ[𝓝 t] fun x : ℝ => (f (x-a) : ℂ) := by
      filter_upwards [isOpen_Ioi.mem_nhds ht] with x hx
      have hxlt : a < x := hx
      have hneg : -x < -a := by linarith
      have hx0 : 0 ≤ x-a := by linarith
      simp only [H, U, V, causalShift_eq_zero_below g (-a) (-x) hneg, Complex.ofReal_zero, add_zero]
      simp only [causalShift, causalFull, indicator_of_mem (show x-a ∈ Ici (0 : ℝ) from hx0)]
    have hc : ContinuousAt H t :=
      ((Complex.continuous_ofReal.comp (hf.comp (continuous_id.sub continuous_const))).continuousAt).congr_of_eventuallyEq hlocal
    have hzero := zero_at_of_fourier_ae_zero H hH hFFT t hc
    have he := hlocal.self_of_nhds
    rw [he] at hzero
    have htR : t-a = r := by dsimp only [t]; ring
    change (f (t-a) : ℂ) = 0 at hzero
    rw [htR] at hzero
    exact Complex.ofReal_eq_zero.mp hzero
  have hcl := hpos.closure hf continuous_const
  rw [closure_Ioi] at hcl
  exact hcl

/-- Source edgeLo reverses sign on the reversed species pair. -/
theorem edgeLo_reverse {N : ℕ} (sigma : Fin N → ℝ) (i j : Fin N) :
    edgeLo sigma j i = -edgeLo sigma i j := by unfold edgeLo; ring

/-- An unequal-diameter check fixes both pair orders and both reflected
support thresholds. They meet at -1/4 for 01 and +1/4 for 10. -/
theorem unequal_pair_touching_supports (f g : ℝ → ℝ) :
    let sigma : Fin 2 → ℝ := ![1, 1/2]
    edgeLo sigma 0 1 = -(1/4 : ℝ) ∧ edgeLo sigma 1 0 = (1/4 : ℝ) ∧
    (∀ r : ℝ, r < -(1/4 : ℝ) → causalShift f (edgeLo sigma 0 1) r = 0) ∧
    (∀ r : ℝ, -(1/4 : ℝ) < r → causalShift g (edgeLo sigma 1 0) (-r) = 0) ∧
    (∀ r : ℝ, r < (1/4 : ℝ) → causalShift g (edgeLo sigma 1 0) r = 0) ∧
    (∀ r : ℝ, (1/4 : ℝ) < r → causalShift f (edgeLo sigma 0 1) (-r) = 0) := by
  dsimp only
  have h01 : edgeLo (![1, 1/2] : Fin 2 → ℝ) 0 1 = -(1/4 : ℝ) := by norm_num [edgeLo]
  have h10 : edgeLo (![1, 1/2] : Fin 2 → ℝ) 1 0 = (1/4 : ℝ) := by norm_num [edgeLo]
  refine ⟨h01, h10, ?_, ?_, ?_, ?_⟩
  · intro r hr; exact causalShift_eq_zero_below _ _ _ (by rw [h01]; exact hr)
  · intro r hr; exact causalShift_eq_zero_below _ _ _ (by rw [h10]; linarith)
  · intro r hr; exact causalShift_eq_zero_below _ _ _ (by rw [h10]; exact hr)
  · intro r hr; exact causalShift_eq_zero_below _ _ _ (by rw [h01]; linarith)

/-- Zero product variation gives the actual anti-transpose logarithmic
response at opposite frequencies, in the correct matrix order. -/
theorem logarithmic_response_anti {N : ℕ}
    (F G dF dG : Matrix (Fin N) (Fin N) ℂ) (hF : IsUnit F) (hG : IsUnit G)
    (hd : dF*G.transpose+F*dG.transpose = 0) :
    F⁻¹*dF+(G⁻¹*dG).transpose = 0 := by
  have hFd := (Matrix.isUnit_iff_isUnit_det _).mp hF
  have hGtd : IsUnit G.transpose.det := by
    simpa only [Matrix.det_transpose] using (Matrix.isUnit_iff_isUnit_det _).mp hG
  have he := congrArg (fun Z => F⁻¹*Z*G.transpose⁻¹) hd
  rw [Matrix.mul_add, Matrix.add_mul] at he
  simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hFd, Matrix.mul_nonsing_inv _ hGtd,
    Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, Matrix.mul_one] at he
  rw [← Matrix.mul_assoc F⁻¹ F (dG.transpose*G.transpose⁻¹), Matrix.nonsing_inv_mul _ hFd, Matrix.one_mul] at he
  rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv]
  exact he

/-- Symmetric density/phase congruences transport logarithmic tangents
without inverting densities, even when the density matrix is singular. -/
theorem logarithmic_response_transport {N : ℕ}
    (F A dF dA S P R : Matrix (Fin N) (Fin N) ℂ)
    (hF : IsUnit F) (hA : IsUnit A) (hP : IsUnit P)
    (hST : S.transpose = S) (hPT : P.transpose = P) (hR : S*S = R)
    (hphase : F.transpose*S*P = S*P*A.transpose)
    (hdphase : dF.transpose*S*P = S*P*dA.transpose) :
    S*(F⁻¹*dF)*S = P⁻¹*(A⁻¹*dA)*P*R := by
  have hFT : IsUnit F.transpose.det := by
    simpa only [Matrix.det_transpose] using (Matrix.isUnit_iff_isUnit_det _).mp hF
  have hAT : IsUnit A.transpose.det := by
    simpa only [Matrix.det_transpose] using (Matrix.isUnit_iff_isUnit_det _).mp hA
  have hPD := (Matrix.isUnit_iff_isUnit_det _).mp hP
  have hinv : F.transpose⁻¹*S*P = S*P*A.transpose⁻¹ := by
    have he := congrArg (fun Z => F.transpose⁻¹*Z*A.transpose⁻¹) hphase
    have hl : F.transpose⁻¹*(F.transpose*S*P)*A.transpose⁻¹ = S*P*A.transpose⁻¹ := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hFT, Matrix.one_mul]
    have hr : F.transpose⁻¹*(S*P*A.transpose)*A.transpose⁻¹ = F.transpose⁻¹*S*P := by
      simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hAT, Matrix.mul_one]
    rw [hl, hr] at he
    exact he.symm
  have hb : (F⁻¹*dF).transpose*S*P = S*P*(A⁻¹*dA).transpose := by
    rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv, Matrix.transpose_mul, Matrix.transpose_nonsing_inv]
    calc
      _ = dF.transpose*(F.transpose⁻¹*S*P) := by noncomm_ring
      _ = dF.transpose*(S*P*A.transpose⁻¹) := by rw [hinv]
      _ = (dF.transpose*S*P)*A.transpose⁻¹ := by noncomm_ring
      _ = (S*P*dA.transpose)*A.transpose⁻¹ := by rw [hdphase]
      _ = _ := by noncomm_ring
  have hbt := congrArg Matrix.transpose hb
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hST, hPT] at hbt
  calc
    _ = (P⁻¹*P)*(S*(F⁻¹*dF))*S := by rw [Matrix.nonsing_inv_mul _ hPD, Matrix.one_mul]
    _ = P⁻¹*(P*(S*(F⁻¹*dF)))*S := by noncomm_ring
    _ = P⁻¹*((A⁻¹*dA)*(P*S))*S := by rw [hbt]
    _ = P⁻¹*(A⁻¹*dA)*P*(S*S) := by noncomm_ring
    _ = _ := by rw [hR]

end FMSA.Convergence.CausalFactorTangent

/-- info: 'FMSA.Convergence.CausalFactorTangent.fourier_reflection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CausalFactorTangent.fourier_reflection

/-- info: 'FMSA.Convergence.CausalFactorTangent.fourier_add_L1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CausalFactorTangent.fourier_add_L1

/-- info: 'FMSA.Convergence.CausalFactorTangent.zero_at_of_fourier_ae_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CausalFactorTangent.zero_at_of_fourier_ae_zero

/-- info: 'FMSA.Convergence.CausalFactorTangent.causal_shift_fourier' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CausalFactorTangent.causal_shift_fourier

/-- info: 'FMSA.Convergence.CausalFactorTangent.touching_causal_pair_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CausalFactorTangent.touching_causal_pair_zero

/-- info: 'FMSA.Convergence.CausalFactorTangent.edgeLo_reverse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CausalFactorTangent.edgeLo_reverse

/-- info: 'FMSA.Convergence.CausalFactorTangent.unequal_pair_touching_supports' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CausalFactorTangent.unequal_pair_touching_supports

/-- info: 'FMSA.Convergence.CausalFactorTangent.logarithmic_response_anti' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CausalFactorTangent.logarithmic_response_anti

/-- info: 'FMSA.Convergence.CausalFactorTangent.logarithmic_response_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CausalFactorTangent.logarithmic_response_transport
