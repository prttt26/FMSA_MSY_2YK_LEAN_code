import MSAConvergence.M2TangencyCenter
import MSAConvergence.M2TangencyDefect

/-! CONSTRUCTED actual M2 stationary zero-mode contact in an explicit
positive-density ten-dimensional box. No numerical root witness, inverse,
analytic enclosure or PASS flag is assumed. PY matching, firstness and
nondegenerate-minimum geometry remain separate questions. -/
noncomputable section
open Set Real Filter Topology
namespace FMSA.Convergence.M2TangencyExistence
open FMSA.ExactMSA.MultiTailMixture
open FMSA.Convergence.BHResidualPolynomials FMSA.Convergence.M2JacobianFormula
open FMSA.Convergence.M2TangencySystem FMSA.Convergence.M2TangencyData
open FMSA.Convergence.M2TangencyJacobian FMSA.Convergence.M2TangencyDefect
open FMSA.Convergence.M2TangencyCenter FMSA.Convergence.NewtonBoxExistence
open FMSA.Convergence.M2ZeroMode FMSA.Convergence.RegularEndpointContinuation
open FMSA.Convergence.CanonicalFirstLoss FMSA.Convergence.CanonicalNeighborhood

/-- A root of ALL TEN actual contact equations is constructed, uniquely
inside this precise ten-dimensional box. No root is supplied as a premise. -/
theorem exists_unique_system_zero :
    ∃! y : Fin 10 → ℝ, y ∈ Icc M2TangencyData.lower M2TangencyData.upper ∧ system y = 0 := by
  refine exists_unique_root_in_box M2TangencyData.lower M2TangencyData.upper M2TangencyData.center M2TangencyData.preconditioner system M2TangencyJacobian.formula
    (⟨1/1000000,by norm_num⟩ : NNReal)
    (1/500000000) (1/10000000000) (1/200000000000)
    (by change (1 : ℝ)/1000000 < 1; norm_num) (by norm_num) (by norm_num)
    M2TangencyData.center_margin M2TangencyData.center_radius ?_ ?_ M2TangencyCenter.center_residual_bound
    (by change (1 : ℝ)/1000000*(1/500000000)+1/200000000000 ≤ 1/10000000000; norm_num)
  · intro x _hx
    exact M2TangencyJacobian.system_hasFDerivAt x
  · intro x hx i
    exact (M2TangencyDefect.row_defect_bound x (fun j => ⟨hx.1 j,hx.2 j⟩) i).le

/-- A genuine positive-coupling original BH root is actually regular but
NONCANONICAL, with a true physical Fourier zero. Thus regularity does not
imply full canonicity even at an actual positive-density BH root. This
asserts nothing about the germ at zero coupling or its Taylor radius. -/
theorem exists_actual_regular_noncanonical_root :
    ∃ (b w : ℝ) (a : TailMatrix (Fin 2) 1 × TailMatrix (Fin 2) 1),
      b ∈ Icc (M2TangencyData.lower 4) (M2TangencyData.upper 4) ∧ w ∈ Icc (M2TangencyData.lower 5) (M2TangencyData.upper 5) ∧
      0 < b ∧ w < 0 ∧ IsRoot z rho sigma (b • strength w) a.1 a.2 ∧
      EndpointRegular z rho sigma (strength w) b a ∧
      a ∉ canonicalAmplitudes z rho sigma ∧ renewalDet z rho sigma a 0 = 0 ∧
      fourierFactor z rho sigma (amplitudeA z rho sigma a.1 a.2)
        (amplitudeQp z rho sigma a.1 a.2) (W z rho a.1 a.2) (C z rho sigma a.1 a.2) 0 0 0 = 0 := by
  obtain ⟨y,hy,_⟩ := exists_unique_system_zero
  obtain ⟨hb,hw⟩ := parameter_signs y hy.1
  obtain ⟨hr,hd,hc⟩ := zero_gives_actual_root_and_noncanonical y hy.2
  have hbox := amplitude_box y hy.1
  refine ⟨y 4,y 5,point (amplitudes y),⟨hy.1.1 4,hy.1.2 4⟩,⟨hy.1.1 5,hy.1.2 5⟩,
    hb,hw,hr,?_,hc,hd,?_⟩
  · exact M2KernelCertificate.actual_regular_on_box _ _ _ (by
      simpa only [point_coordinates] using hbox)
  · rw [actual_fourier_at_zero,((system_zero_iff y).mp hy.2).2.2.1,Complex.ofReal_zero]

/-- The contact comes with a CONSTRUCTED true two-sided analytic root
curve. Its certified velocities are the true coupling derivatives, and
the honest zero-frequency factor has value and derivative zero. This is
stationarity; minimum curvature, first loss and PY matching are not claimed. -/
theorem exists_actual_stationary_branch :
    ∃ (y : Fin 10 → ℝ) (p : ℝ → Fin 4 → ℝ),
      y ∈ Icc M2TangencyData.lower M2TangencyData.upper ∧ system y = 0 ∧
      p (y 4) = amplitudes y ∧ AnalyticAt ℝ p (y 4) ∧
      (∀ᶠ t in 𝓝 (y 4), IsRoot z rho sigma (t • strength (y 5)) (point (p t)).1 (point (p t)).2) ∧
      HasDerivAt p (velocity y) (y 4) ∧ zeroMode (p (y 4)) = 0 ∧
      HasDerivAt (fun t => 1-rdfMatrixLaplace
        (nonlinearCausalKernel z rho sigma (point (p t)).1 (point (p t)).2) 0 0 0) 0 (y 4) := by
  obtain ⟨y,hy,_⟩ := exists_unique_system_zero
  obtain ⟨p,hp⟩ := zero_in_box_constructs_stationary_branch y hy.2 (amplitude_box y hy.1)
  exact ⟨y,p,hy.1,hy.2,hp⟩

end FMSA.Convergence.M2TangencyExistence

/-- info: 'FMSA.Convergence.M2TangencyExistence.exists_unique_system_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2TangencyExistence.exists_unique_system_zero

/-- info: 'FMSA.Convergence.M2TangencyExistence.exists_actual_regular_noncanonical_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2TangencyExistence.exists_actual_regular_noncanonical_root

/-- info: 'FMSA.Convergence.M2TangencyExistence.exists_actual_stationary_branch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2TangencyExistence.exists_actual_stationary_branch

