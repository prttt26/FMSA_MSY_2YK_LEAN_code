import MSAConvergence.MixtureHSCanonicity

/-! A theorem with the exact legacy physical-mixture no-spinodal statement.
The legacy declaration stays frozen; it is not used in this proof. -/
noncomputable section
open Set Real
open scoped BigOperators
namespace FMSA.Convergence.MixtureHSNoSpinodal
open FMSA.MatrixQ0 FMSA.Convergence.MixtureHSAxis
open FMSA.Convergence.MixtureHSKernel FMSA.Convergence.MixtureHSCanonicity
variable {N : ℕ}

/-- Finite determinant swap removes square-root density weights without
inverting any density, so tracer faces are included. -/
theorem sqrt_core_factor_isUnit (rho sigma : Fin N → ℝ) (hrho : ∀ i, 0 ≤ rho i)
    (c k : ℝ) (hk : k ≠ 0) :
    IsUnit (1-Matrix.diagonal (fun i => (sqrt (rho i) : ℂ))*bareHS rho sigma c (Complex.I*(k : ℂ))*
      Matrix.diagonal (fun i => (sqrt (rho i) : ℂ))) := by
  let S := Matrix.diagonal (fun i => (sqrt (rho i) : ℂ))
  have hS : S*S = Matrix.diagonal (fun i => (rho i : ℂ)) := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact_mod_cast mul_self_sqrt (hrho i)
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [Matrix.det_one_sub_mul_comm,← Matrix.mul_assoc,hS]
  exact (Matrix.isUnit_iff_isUnit_det _).mp (row_factor_axis_isUnit rho sigma hrho c k hk)

/-- The literal frozen physical Q0 matrix is phase-conjugate to the proved
square-root-density core factor. No Fourier convention is silently changed. -/
theorem legacy_factor_phase (rho sigma : Fin N → ℝ) (hrho : ∀ i, 0 ≤ rho i) (hv : vacMix rho sigma ≠ 0) (s : ℂ) :
    FMSA.MixtureNoSpinodal.Q0_mat_c_phys s sigma rho *
      Matrix.diagonal (fun j => Complex.exp (s*(sigma j : ℂ)/2)) =
    Matrix.diagonal (fun i => Complex.exp (s*(sigma i : ℂ)/2))*
      (1-Matrix.diagonal (fun i => (sqrt (rho i) : ℂ))*bareHS rho sigma (Real.pi/vacMix rho sigma) s*
        Matrix.diagonal (fun i => (sqrt (rho i) : ℂ))) := by
  ext i j
  have he : Complex.exp (-(((sigma j : ℂ)-(sigma i : ℂ))/2*s))*Complex.exp (s*(sigma j : ℂ)/2) =
      Complex.exp (s*(sigma i : ℂ)/2) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  simp only [Matrix.mul_diagonal,Matrix.diagonal_mul,Matrix.sub_apply,Matrix.one_apply,
    FMSA.MixtureNoSpinodal.Q0_mat_c_phys,FMSA.Q0Complex.Q0_mat_c,FMSA.Q0Complex.q0_entry_c,
    bareHS,phi1,phi2,hs_A_physical rho sigma hv,hs_qp_physical rho sigma hv,rhoGeoPhys,
    Real.sqrt_mul (hrho i),Complex.ofReal_mul,show Qppphys rho sigma i j = Qppphys rho sigma j j from rfl]
  by_cases hij : i = j
  · subst j
    simp only [ite_true,sub_self,zero_div,zero_mul,neg_zero,Complex.exp_zero,mul_one]
    ring
  · simp only [hij,ite_false,zero_sub]
    calc
      _ = -((sqrt (rho i) : ℂ)*(sqrt (rho j) : ℂ))*
          (Complex.exp (-(((sigma j : ℂ)-(sigma i : ℂ))/2*s))*Complex.exp (s*(sigma j : ℂ)/2))*
          ((Q0phys rho sigma i j : ℂ)*phi1 s (sigma i)+(Qppphys rho sigma j j : ℂ)*phi2 s (sigma i)) := by
            unfold phi1 phi2
            ring
      _ = _ := by rw [he]; unfold phi1 phi2; ring

/-- General finite-mixture PY-HS no-spinodal theorem, INCLUDING tracers.
This is the legacy physics axiom's conclusion proved independently, with
nonnegative densities and positive vacancy (no diameter-sign premise). -/
theorem pyhs_mixture_no_spinodal_nonnegative (rho sigma : Fin N → ℝ)
    (hrho : ∀ i, 0 ≤ rho i) (hv : 0 < vacMix rho sigma) (k : ℝ) (hk : k ≠ 0) :
    (FMSA.MixtureNoSpinodal.Q0_mat_c_phys (Complex.I*(k : ℂ)) sigma rho).det ≠ 0 := by
  let s : ℂ := Complex.I*(k : ℂ)
  let P := Matrix.diagonal (fun i => Complex.exp (s*(sigma i : ℂ)/2))
  have hP : IsUnit P := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    rw [Matrix.det_diagonal]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr (fun _ _ => Complex.exp_ne_zero _))
  have hF := sqrt_core_factor_isUnit rho sigma hrho (Real.pi/vacMix rho sigma) k hk
  have hprod := hP.mul hF
  rw [← legacy_factor_phase rho sigma hrho hv.ne' s] at hprod
  have hdet : IsUnit ((FMSA.MixtureNoSpinodal.Q0_mat_c_phys s sigma rho).det*P.det) := by
    simpa only [Matrix.det_mul] using (Matrix.isUnit_iff_isUnit_det _).mp hprod
  exact isUnit_iff_ne_zero.mp (isUnit_of_mul_isUnit_left hdet)

/-- EXACT statement of frozen pyhs_mixture_no_spinodal, now a theorem for
arbitrary finite N. The original physics axiom is not consumed. -/
theorem pyhs_mixture_no_spinodal {sigma rho : Fin N → ℝ}
    (_hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 < rho i)
    (heta : etaMix rho sigma < 1) {k : ℝ} (hk : k ≠ 0) :
    (FMSA.MixtureNoSpinodal.Q0_mat_c_phys (Complex.I*(k : ℂ)) sigma rho).det ≠ 0 := by
  have hv : 0 < vacMix rho sigma := by unfold vacMix; linarith
  exact pyhs_mixture_no_spinodal_nonnegative rho sigma (fun i => (hrho i).le) hv k hk

end FMSA.Convergence.MixtureHSNoSpinodal

/-- info: 'FMSA.Convergence.MixtureHSNoSpinodal.sqrt_core_factor_isUnit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureHSNoSpinodal.sqrt_core_factor_isUnit

/-- info: 'FMSA.Convergence.MixtureHSNoSpinodal.legacy_factor_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureHSNoSpinodal.legacy_factor_phase

/-- info: 'FMSA.Convergence.MixtureHSNoSpinodal.pyhs_mixture_no_spinodal_nonnegative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureHSNoSpinodal.pyhs_mixture_no_spinodal_nonnegative

/-- info: 'FMSA.Convergence.MixtureHSNoSpinodal.pyhs_mixture_no_spinodal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureHSNoSpinodal.pyhs_mixture_no_spinodal

