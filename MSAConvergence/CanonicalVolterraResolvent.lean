import MSAConvergence.CanonicalFourierLaplace

/-! Complex common-damping uniqueness and identification of the existing
concrete Volterra resolvent with the canonical inverse field. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open scoped BigOperators FourierTransform RealInnerProductSpace

namespace FMSA.Convergence.CanonicalVolterraResolvent
open FMSA.Paper FMSA.ExactMSA.MultiTailMixture MSAMixture
open FMSA.Convergence.RDFExponentialOrder FMSA.Convergence.ActualLaplaceJets
open FMSA.Convergence.CanonicalResolventAnalysis FMSA.Convergence.CanonicalFourierLaplace

/-- Causal zero extension of the actual complex damped half-line field. -/
def causalDamping (f : ℝ → ℂ) (gamma : ℝ) : ℝ → ℂ :=
  (Ici (0 : ℝ)).indicator (dampedField f gamma)

/-- Genuine half-line L1 extends causally; a single endpoint has zero measure. -/
theorem causal_damping_integrable (f : ℝ → ℂ) (gamma : ℝ)
    (hi : IntegrableOn (dampedField f gamma) (Ioi (0 : ℝ))) :
    Integrable (causalDamping f gamma) := by
  have hc : IntegrableOn (dampedField f gamma) (Ici (0 : ℝ)) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr hi
  exact hc.integrable_indicator measurableSet_Ici

/-- Exact Fourier/Laplace identity for the causal complex field at arbitrary
common damping. Its convergence is separately supplied by half-line L1. -/
theorem causal_damping_fourier (f : ℝ → ℂ) (gamma xi : ℝ) :
    𝓕 (causalDamping f gamma) xi =
      ∫ t in Ioi (0 : ℝ), f t*Complex.exp (-verticalPoint gamma (2*π*xi)*(t : ℂ)) := by
  have he : causalDamping f gamma = dampedField ((Ici (0 : ℝ)).indicator f) gamma := by
    funext t
    by_cases ht : t ∈ Ici (0 : ℝ)
    · simp only [causalDamping, dampedField, indicator_of_mem ht]
    · simp only [causalDamping, dampedField, indicator_of_notMem ht, mul_zero]
  rw [he, fourier_damped_eq_laplace]
  have hh : (fun t : ℝ => (Ici (0 : ℝ)).indicator f t*
      Complex.exp (-verticalPoint gamma (2*π*xi)*(t : ℂ))) =
      (Ici (0 : ℝ)).indicator (fun t : ℝ => f t*Complex.exp (-verticalPoint gamma (2*π*xi)*(t : ℂ))) := by
    funext t
    by_cases ht : t ∈ Ici (0 : ℝ)
    · simp only [indicator_of_mem ht]
    · simp only [indicator_of_notMem ht, zero_mul]
  rw [hh, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]

/-- Complex-valued causal Laplace uniqueness at arbitrary common real damping.
Only actual damped L1 and continuity on the closed causal half-line are
needed; no real/imaginary split of a complex-line hypothesis is used. -/
theorem causal_laplace_injective (f g : ℝ → ℂ) (gamma : ℝ)
    (hf : ContinuousOn f (Ici (0 : ℝ))) (hg : ContinuousOn g (Ici (0 : ℝ)))
    (hif : IntegrableOn (dampedField f gamma) (Ioi (0 : ℝ)))
    (hig : IntegrableOn (dampedField g gamma) (Ioi (0 : ℝ)))
    (hLap : ∀ k : ℝ,
      (∫ t in Ioi (0 : ℝ), f t*Complex.exp (-verticalPoint gamma (2*π*k)*(t : ℂ))) =
      (∫ t in Ioi (0 : ℝ), g t*Complex.exp (-verticalPoint gamma (2*π*k)*(t : ℂ)))) :
    EqOn f g (Ici (0 : ℝ)) := by
  let U := causalDamping f gamma
  let V := causalDamping g gamma
  have hU : Integrable U := causal_damping_integrable f gamma hif
  have hV : Integrable V := causal_damping_integrable g gamma hig
  have hFFT : 𝓕 (U-V) = 0 := by
    funext k
    have hIU := (Real.fourierIntegral_convergent_iff (V := ℝ) (E := ℂ) k).2 hU
    have hIV := (Real.fourierIntegral_convergent_iff (V := ℝ) (E := ℂ) k).2 hV
    rw [Real.fourier_eq]
    have he : (fun t : ℝ => 𝐞 (-⟪t,k⟫) • (U-V) t) =
        fun t : ℝ => 𝐞 (-⟪t,k⟫) • U t-𝐞 (-⟪t,k⟫) • V t := by
      funext t
      change 𝐞 (-⟪t,k⟫) • (U t-V t) = 𝐞 (-⟪t,k⟫) • U t-𝐞 (-⟪t,k⟫) • V t
      rw [smul_sub]
    rw [he, integral_sub hIU hIV, ← Real.fourier_eq, ← Real.fourier_eq]
    change 𝓕 (causalDamping f gamma) k-𝓕 (causalDamping g gamma) k = 0
    rw [causal_damping_fourier, causal_damping_fourier, hLap, sub_self]
  let fe := fun t : ℝ => f (max 0 t)
  let ge := fun t : ℝ => g (max 0 t)
  have hfe : Continuous fe := hf.comp_continuous (continuous_const.max continuous_id) (by
    intro t
    change (0 : ℝ) ≤ max 0 t
    exact le_max_left _ _)
  have hge : Continuous ge := hg.comp_continuous (continuous_const.max continuous_id) (by
    intro t
    change (0 : ℝ) ≤ max 0 t
    exact le_max_left _ _)
  have hpos : EqOn fe ge (Ioi (0 : ℝ)) := by
    intro t ht
    have hlocal : U-V =ᶠ[𝓝 t] fun x : ℝ => Complex.exp (-(gamma : ℂ)*(x : ℂ))*(fe x-ge x) := by
      filter_upwards [isOpen_Ioi.mem_nhds ht] with x hx
      have hx0 : (0 : ℝ) ≤ x := (show (0 : ℝ) < x from hx).le
      change causalDamping f gamma x-causalDamping g gamma x =
        Complex.exp (-(gamma : ℂ)*(x : ℂ))*(fe x-ge x)
      simp only [causalDamping, dampedField,
        indicator_of_mem (show x ∈ Ici (0 : ℝ) from hx0), fe, ge, max_eq_right hx0, mul_sub]
    have hc : ContinuousAt (U-V) t :=
      ((by fun_prop : Continuous (fun x : ℝ => Complex.exp (-(gamma : ℂ)*(x : ℂ)))).mul
        (hfe.sub hge)).continuousAt.congr_of_eventuallyEq hlocal
    have hFI : Integrable (𝓕 (U-V)) := by rw [hFFT]; exact integrable_zero _ _ _
    have hinv := (hU.sub hV).fourierInv_fourier_eq hFI hc
    rw [hFFT] at hinv
    have hz : (𝓕⁻ (0 : ℝ → ℂ)) t = 0 := by simp [Real.fourierInv_eq]
    have hzero : (U-V) t = 0 := hinv.symm.trans hz
    have hv : Complex.exp (-(gamma : ℂ)*(t : ℂ))*(fe t-ge t) = 0 :=
      hlocal.self_of_nhds.symm.trans hzero
    exact sub_eq_zero.mp ((mul_eq_zero.mp hv).resolve_left (Complex.exp_ne_zero _))
  have hall := hpos.closure hfe hge
  rw [closure_Ioi] at hall
  intro t ht
  have ht0 : (0 : ℝ) ≤ t := ht
  simpa only [fe, ge, max_eq_right ht0] using hall ht

/-- The existing concrete real matrix Volterra constructor, transposed
once to solve the right-oriented actual Baxter renewal. -/
def rightVolterra {N : ℕ} (q f : ℝ → Matrix (Fin N) (Fin N) ℝ)
    (hq : Continuous q) (hf : Continuous f) (r : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  (FMSA.MixtureOzStar.matBaxterPsiOuterFun 0 (fun t => (q t).transpose) (fun t => (f t).transpose)
    (continuous_matrix (fun i j => hq.matrix_elem j i))
    (continuous_matrix (fun i j => hf.matrix_elem j i)) r).transpose

/-- The concrete constructor has its established max-extended continuity. -/
theorem right_volterra_continuous {N : ℕ} (q f : ℝ → Matrix (Fin N) (Fin N) ℝ)
    (hq : Continuous q) (hf : Continuous f) : Continuous (rightVolterra q f hq hf) :=
  continuous_matrix fun i j =>
    (FMSA.MixtureOzStar.matBaxterPsiOuterFun_continuous 0 _ _ _ _).matrix_elem j i

/-- Actual right-oriented renewal of the concrete constructor, with species
order and row-density placement retained. -/
theorem right_volterra_renewal {N : ℕ} (q f : ℝ → Matrix (Fin N) (Fin N) ℝ)
    (hq : Continuous q) (hf : Continuous f) (i j : Fin N) (r : ℝ) (hr : 0 ≤ r) :
    rightVolterra q f hq hf r i j = f r i j+
      ∑ m, ∫ t in (0 : ℝ)..r, rightVolterra q f hq hf t i m*q (r-t) m j := by
  have h := FMSA.MixtureOzStar.matBaxterPsiOuter_matRenewalEq 0
    (fun t => (q t).transpose) (fun t => (f t).transpose)
    (continuous_matrix (fun i j => hq.matrix_elem j i))
    (continuous_matrix (fun i j => hf.matrix_elem j i)) j i r hr
  simpa only [rightVolterra, Matrix.transpose_apply, mul_comm] using h

/-- The actual concrete Volterra initial value is the source at zero. -/
theorem right_volterra_at_zero {N : ℕ} (q f : ℝ → Matrix (Fin N) (Fin N) ℝ)
    (hq : Continuous q) (hf : Continuous f) : rightVolterra q f hq hf 0 = f 0 := by
  ext i j
  simpa only [intervalIntegral.integral_same, Finset.sum_const_zero, add_zero] using
    right_volterra_renewal q f hq hf i j 0 le_rfl

/-- The classical actual kernel resolvent is the existing Volterra constructor
with kernel and source both equal to q, in the actual right orientation. -/
def kernelResolvent {N : ℕ} (q : ℝ → Matrix (Fin N) (Fin N) ℝ) (hq : Continuous q) :
    ℝ → Matrix (Fin N) (Fin N) ℝ := rightVolterra q q hq hq

/-- Its continuity is inherited from the concrete constructor. -/
theorem kernel_resolvent_continuous {N : ℕ} (q : ℝ → Matrix (Fin N) (Fin N) ℝ) (hq : Continuous q) :
    Continuous (kernelResolvent q hq) := right_volterra_continuous q q hq hq

/-- Actual real right resolvent renewal, without a spectral identity premise. -/
theorem kernel_resolvent_renewal {N : ℕ} (q : ℝ → Matrix (Fin N) (Fin N) ℝ) (hq : Continuous q)
    (i j : Fin N) (r : ℝ) (hr : 0 ≤ r) :
    kernelResolvent q hq r i j = q r i j+
      ∑ m, ∫ t in (0 : ℝ)..r, kernelResolvent q hq t i m*q (r-t) m j :=
  right_volterra_renewal q q hq hq i j r hr

/-- Internally computed exponential order of the actual constructed real
resolvent; this preliminary bound permits growth and is not a small budget. -/
theorem kernel_resolvent_exponential_order {N : ℕ}
    (q : ℝ → Matrix (Fin N) (Fin N) ℝ) (hq : Continuous q)
    (M : ℝ) (hM : 0 ≤ M) (hk : ∀ r, 0 ≤ r → FMSA.matrixAbsSum (q r) ≤ M) :
    ∀ r, 0 ≤ r → exp (-(M+1)*r)*FMSA.matrixAbsSum (kernelResolvent q hq r) ≤ M*(M+1) := by
  have hqt : Continuous (fun r => (q r).transpose) := continuous_matrix fun i j => hq.matrix_elem j i
  have hyt : Continuous (fun r => (kernelResolvent q hq r).transpose) :=
    continuous_matrix fun i j => (kernel_resolvent_continuous q hq).matrix_elem j i
  have h := matrix_renewal_exponential_order (fun r => (q r).transpose) (fun r => (q r).transpose)
    (fun r => (kernelResolvent q hq r).transpose) hqt hyt M M hM hM
    (fun r hr => by simpa only [FMSA.matrixAbsSum_transpose] using hk r hr)
    (fun r hr => by
      rw [FMSA.matrixAbsSum_transpose]
      exact (hk r hr).trans (by nlinarith))
    (fun i j r hr => by simpa only [Matrix.transpose_apply, mul_comm] using kernel_resolvent_renewal q hq j i r hr)
  simpa only [FMSA.matrixAbsSum_transpose] using h

/-- A genuine matrix exponential-order bound supplies each actual damped
real entry's L1, at every stronger damping. -/
theorem matrix_exp_order_damped_integrable {N : ℕ}
    (y : ℝ → Matrix (Fin N) (Fin N) ℝ) (hy : Continuous y) (gamma B : ℝ)
    (hY : ∀ r, 0 ≤ r → exp (-gamma*r)*FMSA.matrixAbsSum (y r) ≤ B)
    (c : ℝ) (hc : gamma < c) (i j : Fin N) :
    IntegrableOn (fun r : ℝ => exp (-c*r)*y r i j) (Ioi 0) := by
  apply exp_order_real_integrable _ (hy.matrix_elem i j).aestronglyMeasurable gamma B c _ hc
  intro r hr
  exact (mul_le_mul_of_nonneg_left (FMSA.matrixAbsSum_entry_le (y r) i j) (exp_pos _).le).trans (hY r hr.le)

/-- Actual real damping integrability of the concrete resolvent, not an
assumption about an unknown Volterra solution. -/
theorem kernel_resolvent_damped_integrable {N : ℕ}
    (q : ℝ → Matrix (Fin N) (Fin N) ℝ) (hq : Continuous q)
    (M : ℝ) (hM : 0 ≤ M) (hk : ∀ r, 0 ≤ r → FMSA.matrixAbsSum (q r) ≤ M)
    (c : ℝ) (hc : M+1 < c) (i j : Fin N) :
    IntegrableOn (fun r : ℝ => exp (-c*r)*kernelResolvent q hq r i j) (Ioi 0) :=
  matrix_exp_order_damped_integrable _ (kernel_resolvent_continuous q hq) (M+1) (M*(M+1))
    (kernel_resolvent_exponential_order q hq M hM hk) c hc i j

/-- The actual real Volterra resolvent satisfies the integrated matrix
renewal on an internally controlled far-right half-plane. -/
theorem kernel_resolvent_laplace_renewal {N : ℕ}
    (q : ℝ → Matrix (Fin N) (Fin N) ℝ) (hq : Continuous q)
    (M : ℝ) (hM : 0 ≤ M) (hk : ∀ r, 0 ≤ r → FMSA.matrixAbsSum (q r) ≤ M)
    (s : ℂ) (hs : M+1 < s.re) :
    rdfMatrixLaplace (kernelResolvent q hq) s*(1-rdfMatrixLaplace q s) = rdfMatrixLaplace q s := by
  have hq0 : ∀ r, 0 ≤ r → exp (-(0 : ℝ)*r)*FMSA.matrixAbsSum (q r) ≤ M := by
    simpa only [neg_zero, zero_mul, exp_zero, one_mul] using hk
  have hqi (i j : Fin N) : IntegrableOn (fun r : ℝ => exp (-s.re*r)*q r i j) (Ioi 0) :=
    matrix_exp_order_damped_integrable q hq 0 M hq0 s.re (by linarith) i j
  apply complexMatrixLaplace_right_renewal q q (kernelResolvent q hq) hq hq (kernel_resolvent_continuous q hq) s
    hqi hqi (kernel_resolvent_damped_integrable q hq M hM hk s.re hs)
  intro i j r hr
  simpa only [causalIntervalConv, mul_comm] using kernel_resolvent_renewal q hq i j r hr

/-- The actual constructed resolvent's far-right Laplace transform equals
the true finite inverse minus I. Strong damping computes unit control here;
no canonical or physical small-kernel-budget premise is added. -/
theorem kernel_resolvent_laplace_eq {N : ℕ}
    (q : ℝ → Matrix (Fin N) (Fin N) ℝ) (hq : Continuous q)
    (M : ℝ) (hM : 0 ≤ M) (hk : ∀ r, 0 ≤ r → FMSA.matrixAbsSum (q r) ≤ M)
    (s : ℂ) (hs : M+1 < s.re) :
    rdfMatrixLaplace (kernelResolvent q hq) s = (1-rdfMatrixLaplace q s)⁻¹-1 := by
  let Q := rdfMatrixLaplace q s
  have hu : IsUnit (1-Q) := bounded_matrix_laplace_isUnit q hq M hk s (by linarith) (by linarith)
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp hu
  have hr := kernel_resolvent_laplace_renewal q hq M hM hk s hs
  change rdfMatrixLaplace (kernelResolvent q hq) s*(1-Q) = Q at hr
  have hc := Matrix.mul_nonsing_inv_cancel_right (1-Q) (rdfMatrixLaplace (kernelResolvent q hq) s) hd
  rw [hr] at hc
  have hh : (1-Q)⁻¹ = 1+Q*(1-Q)⁻¹ := by
    have ht := Matrix.mul_nonsing_inv (1-Q) hd
    rw [sub_mul, one_mul] at ht
    exact sub_eq_iff_eq_add.mp ht
  calc
    _ = Q*(1-Q)⁻¹ := hc.symm
    _ = (1+Q*(1-Q)⁻¹)-1 := by abel
    _ = _ := by rw [← hh]

/-- Real damped entry integrability gives the actual complex damped field
integrability by the genuine complex embedding, at the same damping. -/
theorem ofReal_damped_integrable (f : ℝ → ℝ) (gamma : ℝ)
    (hi : IntegrableOn (fun t : ℝ => exp (-gamma*t)*f t) (Ioi 0)) :
    IntegrableOn (dampedField (fun t : ℝ => (f t : ℂ)) gamma) (Ioi 0) := by
  have hreal : Integrable (fun t : ℝ => exp (-gamma*t)*f t) (volume.restrict (Ioi 0)) := hi
  change Integrable (fun t : ℝ => Complex.exp (-(gamma : ℂ)*(t : ℂ))*(f t : ℂ)) (volume.restrict (Ioi 0))
  have hc : Integrable (fun t : ℝ => ((exp (-gamma*t)*f t : ℝ) : ℂ)) (volume.restrict (Ioi 0)) := hreal.ofReal
  simpa only [Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_neg] using hc

/-- The actual MSA kernel inserted into the pre-existing concrete real
Volterra constructor, with source equal to that same actual kernel. -/
def actualKernelResolvent {N : ℕ} {T : Type*} [Fintype T]
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (p : TailMatrix T N × TailMatrix T N) :
    ℝ → Matrix (Fin N) (Fin N) ℝ :=
  kernelResolvent (nonlinearCausalKernel z rho sigma p.1 p.2)
    (nonlinearCausalKernel_continuous z rho sigma p.1 p.2)

/-- The actual concrete Volterra resolvent equals the canonical inverse field
on the closed causal half-line. This transfers real decay, actual positive-axis
L1 and the true Fourier-boundary Laplace identity to the existing constructor,
without a small physical kernel budget or a damping-below-one premise. -/
theorem actual_kernel_resolvent_canonical
    {N : ℕ} {T : Type*} [Fintype T]
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 ≤ sigma i) (p : TailMatrix T N × TailMatrix T N)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)) :
    ∃ delta b B : ℝ, 0 < delta ∧ (∀ u, delta < z u) ∧ delta < b ∧ 0 ≤ B ∧
      ∀ i j : Fin N,
        let F := fun s : ℂ => regularizedResolvent (nonlinearCausalKernel z rho sigma p.1 p.2) b s i j
        let r := restoredInverse F (nonlinearCausalKernel z rho sigma p.1 p.2 0 i j : ℂ) b (-delta/2)
        EqOn (fun t : ℝ => (actualKernelResolvent z rho sigma p t i j : ℂ)) r (Ici (0 : ℝ)) ∧
        (∀ t : ℝ, 0 ≤ t → |actualKernelResolvent z rho sigma p t i j| ≤ B*exp ((-delta/2)*t)) ∧
        IntegrableOn (fun t : ℝ => actualKernelResolvent z rho sigma p t i j) (Ioi 0) ∧
        (∀ c : ℝ, -delta/2 < c → IntegrableOn
          (fun t : ℝ => exp (-c*t)*actualKernelResolvent z rho sigma p t i j) (Ioi 0)) ∧
        ∀ s : ℂ, -delta/2 < s.re →
          IntegrableOn (fun t : ℝ => (actualKernelResolvent z rho sigma p t i j : ℂ)*Complex.exp (-s*(t : ℂ))) (Ioi 0) ∧
          rdfMatrixLaplace (actualKernelResolvent z rho sigma p) s i j =
            ((1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)⁻¹-1) i j := by
  obtain ⟨M, _C, hM, _hC, hlocal⟩ := actual_kernel_source_local_bounds z hz rho sigma hsigma p
  let q := nonlinearCausalKernel z rho sigma p.1 p.2
  have hq : Continuous q := nonlinearCausalKernel_continuous z rho sigma p.1 p.2
  have hk (t : ℝ) (ht : 0 ≤ t) : FMSA.matrixAbsSum (q t) ≤ M := (hlocal.self_of_nhds t ht).1
  let y := kernelResolvent q hq
  have hy : Continuous y := kernel_resolvent_continuous q hq
  let gamma := M+2
  have hgM : M+1 < gamma := by dsimp [gamma]; linarith
  obtain ⟨delta, b, B, hd, hdr, hb, hB, hfields⟩ := actual_canonical_resolvent_field z hz rho sigma hsigma p hcanon
  have hgA : -delta/2 < gamma := by dsimp [gamma]; linarith
  refine ⟨delta, b, B, hd, hdr, hb, hB, ?_⟩
  intro i j
  let F := fun s : ℂ => regularizedResolvent q b s i j
  let r := restoredInverse F (q 0 i j : ℂ) b (-delta/2)
  rcases hfields i j with ⟨hrc, _hr0, _hrn, _hri, hdec, hLap⟩
  let f := fun t : ℝ => (y t i j : ℂ)
  have hfc : ContinuousOn f (Ici (0 : ℝ)) :=
    (Complex.continuous_ofReal.comp (hy.matrix_elem i j)).continuousOn
  have hif : IntegrableOn (dampedField f gamma) (Ioi 0) :=
    ofReal_damped_integrable (fun t => y t i j) gamma
      (kernel_resolvent_damped_integrable q hq M hM hk gamma hgM i j)
  have hig : IntegrableOn (dampedField r gamma) (Ioi 0) := by
    have hc := (hLap (gamma : ℂ) (by simpa only [Complex.ofReal_re] using hgA)).1
    have hi : IntegrableOn (fun t : ℝ => r t*Complex.exp (-(gamma : ℂ)*(t : ℂ))) (Ioi 0) := hc.integrableOn
    change Integrable (fun t : ℝ => r t*Complex.exp (-(gamma : ℂ)*(t : ℂ))) (volume.restrict (Ioi 0)) at hi
    change Integrable (fun t : ℝ => Complex.exp (-(gamma : ℂ)*(t : ℂ))*r t) (volume.restrict (Ioi 0))
    simpa only [mul_comm] using hi
  have hEq : EqOn f r (Ici (0 : ℝ)) := by
    apply causal_laplace_injective f r gamma hfc hrc hif hig
    intro xi
    let s := verticalPoint gamma (2*π*xi)
    have hsM : M+1 < s.re := by simpa [s, verticalPoint] using hgM
    have hsA : -delta/2 < s.re := by simpa [s, verticalPoint] using hgA
    have he : (∫ t in Ioi (0 : ℝ), f t*Complex.exp (-s*(t : ℂ))) =
        ((1-rdfMatrixLaplace q s)⁻¹-1) i j := by
      change rdfMatrixLaplace (kernelResolvent q hq) s i j = _
      exact congrFun (congrFun (kernel_resolvent_laplace_eq q hq M hM hk s hsM) i) j
    exact he.trans (hLap s hsA).2.symm
  have hreal (t : ℝ) (ht : 0 ≤ t) : |y t i j| ≤ B*exp ((-delta/2)*t) := by
    have hh : ‖r t‖ ≤ B*exp ((-delta/2)*t) := hdec t ht
    rw [← hEq (show t ∈ Ici (0 : ℝ) from ht)] at hh
    simpa only [f, Complex.norm_real, Real.norm_eq_abs] using hh
  refine ⟨hEq, hreal, ?_, ?_, ?_⟩
  · have hi : IntegrableOn (fun t : ℝ => B*exp ((-delta/2)*t)) (Ioi 0) :=
      (integrableOn_exp_mul_Ioi (by linarith : -delta/2 < 0) 0).const_mul B
    apply hi.mono' (hy.matrix_elem i j).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simpa only [Real.norm_eq_abs] using hreal t ht.le
  · intro c hc
    apply exp_order_real_integrable (fun t => y t i j) (hy.matrix_elem i j).aestronglyMeasurable (-delta/2) B c _ hc
    intro t ht
    have hex : exp (-(-delta/2)*t)*exp ((-delta/2)*t) = 1 := by
      rw [← exp_add, show -(-delta/2)*t+(-delta/2)*t = 0 by ring, exp_zero]
    calc
      _ ≤ exp (-(-delta/2)*t)*(B*exp ((-delta/2)*t)) :=
        mul_le_mul_of_nonneg_left (hreal t ht.le) (exp_pos _).le
      _ = B*(exp (-(-delta/2)*t)*exp ((-delta/2)*t)) := by ring
      _ = _ := by rw [hex, mul_one]
  · intro s hs
    obtain ⟨hic, htc⟩ := hLap s hs
    have he : EqOn (fun t : ℝ => (y t i j : ℂ)*Complex.exp (-s*(t : ℂ)))
        (fun t : ℝ => r t*Complex.exp (-s*(t : ℂ))) (Ioi (0 : ℝ)) := by
      intro t ht
      exact congrArg (fun w : ℂ => w*Complex.exp (-s*(t : ℂ)))
        (hEq (show t ∈ Ici (0 : ℝ) from (show (0 : ℝ) < t from ht).le))
    refine ⟨(integrableOn_congr_fun he measurableSet_Ioi).mpr hic.integrableOn, ?_⟩
    change (∫ t in Ioi (0 : ℝ), (y t i j : ℂ)*Complex.exp (-s*(t : ℂ))) = _
    exact (setIntegral_congr_fun measurableSet_Ioi he).trans htc

end FMSA.Convergence.CanonicalVolterraResolvent

/-- info: 'FMSA.Convergence.CanonicalVolterraResolvent.causal_damping_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalVolterraResolvent.causal_damping_integrable

/-- info: 'FMSA.Convergence.CanonicalVolterraResolvent.causal_damping_fourier' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalVolterraResolvent.causal_damping_fourier

/-- info: 'FMSA.Convergence.CanonicalVolterraResolvent.causal_laplace_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalVolterraResolvent.causal_laplace_injective

/-- info: 'FMSA.Convergence.CanonicalVolterraResolvent.right_volterra_continuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalVolterraResolvent.right_volterra_continuous

/-- info: 'FMSA.Convergence.CanonicalVolterraResolvent.right_volterra_renewal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalVolterraResolvent.right_volterra_renewal

/-- info: 'FMSA.Convergence.CanonicalVolterraResolvent.right_volterra_at_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalVolterraResolvent.right_volterra_at_zero

/-- info: 'FMSA.Convergence.CanonicalVolterraResolvent.kernel_resolvent_continuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalVolterraResolvent.kernel_resolvent_continuous

/-- info: 'FMSA.Convergence.CanonicalVolterraResolvent.kernel_resolvent_renewal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalVolterraResolvent.kernel_resolvent_renewal

/-- info: 'FMSA.Convergence.CanonicalVolterraResolvent.kernel_resolvent_exponential_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalVolterraResolvent.kernel_resolvent_exponential_order

/-- info: 'FMSA.Convergence.CanonicalVolterraResolvent.matrix_exp_order_damped_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalVolterraResolvent.matrix_exp_order_damped_integrable

/-- info: 'FMSA.Convergence.CanonicalVolterraResolvent.kernel_resolvent_damped_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalVolterraResolvent.kernel_resolvent_damped_integrable

/-- info: 'FMSA.Convergence.CanonicalVolterraResolvent.kernel_resolvent_laplace_renewal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalVolterraResolvent.kernel_resolvent_laplace_renewal

/-- info: 'FMSA.Convergence.CanonicalVolterraResolvent.kernel_resolvent_laplace_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalVolterraResolvent.kernel_resolvent_laplace_eq

/-- info: 'FMSA.Convergence.CanonicalVolterraResolvent.ofReal_damped_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalVolterraResolvent.ofReal_damped_integrable

/-- info: 'FMSA.Convergence.CanonicalVolterraResolvent.actual_kernel_resolvent_canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalVolterraResolvent.actual_kernel_resolvent_canonical
