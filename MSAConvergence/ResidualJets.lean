import MSAConvergence.PoleResidual

/-! Differentiate a residual factorization without assuming a root curve. -/
noncomputable section
open Real
open scoped BigOperators ContDiff Matrix.Norms.Elementwise

namespace FMSA.Convergence.ResidualJets
open FMSA.Paper FMSA.Paper.JacobianExterior
open FMSA.ExactMSA.MultiTailMixture
open FMSA.Convergence.PoleResidual MSAMixture

/-- A differentiable lift vanishing on the zero-error slice annihilates every
kernel vector of the residual derivative at a root. No root curve is needed. -/
theorem residual_lift_kernel_fderiv {P Q : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    (r : P → Q) (L : P →L[ℝ] Q) (F : P × Q → ℝ) (p v : P)
    (hr : HasFDerivAt r L p) (hr0 : r p = 0) (hv : L v = 0)
    (hF : DifferentiableAt ℝ F (p, 0)) (hzero : ∀ a, F (a, 0) = 0) :
    fderiv ℝ (fun a => F (a, r a)) p v = 0 := by
  have hF' : HasFDerivAt F (fderiv ℝ F (p, 0)) (p, r p) := by
    simpa only [hr0] using hF.hasFDerivAt
  have hc := hF'.comp p ((hasFDerivAt_id p).prodMk hr)
  have hg : HasFDerivAt (fun a : P => (a, (0 : Q)))
      ((ContinuousLinearMap.id ℝ P).prod (0 : P →L[ℝ] Q)) p :=
    (hasFDerivAt_id p).prodMk (hasFDerivAt_const (0 : Q) p)
  have hz := HasFDerivAt.comp (𝕜 := ℝ) (E := P) (F := P × Q) (G := ℝ)
    (f := fun a : P => (a, (0 : Q))) (g := F) p hF.hasFDerivAt hg
  have he : (fun a => F (a, (0 : Q))) = fun _ : P => (0 : ℝ) := funext hzero
  simp only [Function.comp_def] at hz
  rw [he] at hz
  have hc' := congrArg (fun A : P →L[ℝ] ℝ => A v) hc.fderiv
  have hz' := congrArg (fun A : P →L[ℝ] ℝ => A v) hz.fderiv
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, zero_apply, hv] at hc' hz'
  simpa only [Function.comp_def, id_eq, fderiv_const_apply, zero_apply] using hc'.trans hz'.symm

variable {N : ℕ} {T : Type*} [Fintype T]

/-- Smooth matrix multiplication for finite real matrix families, using the
entry norm rather than introducing an operator-norm alias on the amplitudes. -/
@[fun_prop]
theorem matrix_family_mul_contDiff {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (A B : P → Matrix (Fin N) (Fin N) ℝ) (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) :
    ContDiff ℝ ∞ (fun a => A a * B a) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  simp only [Matrix.mul_apply]
  apply ContDiff.sum
  intro m _
  exact ((contDiff_pi.mp (contDiff_pi.mp hA i)) m).mul
    ((contDiff_pi.mp (contDiff_pi.mp hB m)) j)

/-- Transposition preserves smooth finite matrix families in the entry norm. -/
@[fun_prop]
theorem matrix_family_transpose_contDiff {P : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (A : P → Matrix (Fin N) (Fin N) ℝ) (hA : ContDiff ℝ ∞ A) :
    ContDiff ℝ ∞ (fun a => (A a).transpose) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  exact (contDiff_pi.mp (contDiff_pi.mp hA j)) i

/-- Every scalar entry of the error lift is smooth jointly in amplitudes and
independent error data; no differentiability of a root selection is assumed. -/
theorem poleErrorLift_entry_contDiff (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (u : T) (k : Fin 4) (i j : Fin N) :
    ContDiff ℝ ∞ (fun b : (TailMatrix T N × TailMatrix T N) ×
        (TailMatrix T N × TailMatrix T N) => poleErrorLift z rho sigma b.1 b.2 u k i j) := by
  let B := (TailMatrix T N × TailMatrix T N) × (TailMatrix T N × TailMatrix T N)
  let P := Matrix.diagonal rho
  let E := Matrix.diagonal (fun a => exp (-z u * sigma a))
  let H := fun b : B => (2 * π / z u) • Matrix.of (b.1.2 u)
  let WW := fun b : B => Matrix.of (W z rho b.1.1 b.1.2 u)
  let CC := fun b : B => Matrix.of (C z rho sigma b.1.1 b.1.2 u)
  let D := fun b : B => Matrix.of (b.2.1 u)
  let A := fun b : B => (D b).transpose - D b
  let S := fun b : B => (-(z u)⁻¹) • Matrix.of (b.2.2 u)
  let M := fun b : B => 1 - E * H b * P
  have mmul {A B : B → Matrix (Fin N) (Fin N) ℝ}
      (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) := matrix_family_mul_contDiff A B hA hB
  have mtrans {A : B → Matrix (Fin N) (Fin N) ℝ}
      (hA : ContDiff ℝ ∞ A) := matrix_family_transpose_contDiff A hA
  have hP : ContDiff ℝ ∞ (fun _ : B => P) := contDiff_const
  have hE : ContDiff ℝ ∞ (fun _ : B => E) := contDiff_const
  have hH : ContDiff ℝ ∞ H := by
    apply contDiff_pi.mpr
    intro a
    apply contDiff_pi.mpr
    intro c
    change ContDiff ℝ ∞ (fun b : (TailMatrix T N × TailMatrix T N) ×
      (TailMatrix T N × TailMatrix T N) => (2 * π / z u) * b.1.2 u a c)
    fun_prop
  have hD : ContDiff ℝ ∞ D := by
    apply contDiff_pi.mpr
    intro a
    apply contDiff_pi.mpr
    intro c
    change ContDiff ℝ ∞ (fun b : (TailMatrix T N × TailMatrix T N) ×
      (TailMatrix T N × TailMatrix T N) => b.2.1 u a c)
    fun_prop
  have hS : ContDiff ℝ ∞ S := by
    apply contDiff_pi.mpr
    intro a
    apply contDiff_pi.mpr
    intro c
    change ContDiff ℝ ∞ (fun b : (TailMatrix T N × TailMatrix T N) ×
      (TailMatrix T N × TailMatrix T N) => (-(z u)⁻¹) * b.2.2 u a c)
    fun_prop
  have hW : ContDiff ℝ ∞ WW := by
    apply contDiff_pi.mpr
    intro a
    apply contDiff_pi.mpr
    intro c
    exact (W_contDiff z rho u a c).comp contDiff_fst
  have hC : ContDiff ℝ ∞ CC := by
    apply contDiff_pi.mpr
    intro a
    apply contDiff_pi.mpr
    intro c
    exact (C_contDiff z rho sigma u a c).comp contDiff_fst
  have hA : ContDiff ℝ ∞ A := (mtrans hD).sub hD
  have hM : ContDiff ℝ ∞ M := contDiff_const.sub (mmul (mmul hE hH) hP)
  have hu := ((mmul (mmul (mmul hM hA) hP) (mtrans hH)).sub
    (mmul (mmul hC hP) (mtrans hS))).sub (mmul (mmul (mmul hE hS) hP) (mtrans hW))
  have hum := ((mmul (mmul (mmul hH hP) (mtrans hA)) (mtrans hM)).sub
    (mmul (mmul hS hP) (mtrans hC))).sub (mmul (mmul (mmul hW hP) (mtrans hS)) (mtrans hE))
  have hv := ((mmul (mmul (mmul hH hP) hA) (mmul hP (mtrans hH))).add
    (mmul (mmul hS hP) (mtrans hW))).sub (mmul (mmul hW hP) (mtrans hS))
  have hvm := ((mmul (mmul hM hA) (mtrans hM)).neg.add
    (mmul (mmul (mmul hE hS) hP) (mtrans hC))).sub
      (mmul (mmul (mmul hC hP) (mtrans hS)) (mtrans hE))
  fin_cases k
  · exact (contDiff_pi.mp (contDiff_pi.mp hu i)) j
  · exact (contDiff_pi.mp (contDiff_pi.mp hum i)) j
  · change ContDiff ℝ ∞ (fun b : B =>
      (H b * P * A b * P * (H b).transpose + S b * P * (WW b).transpose -
        WW b * P * (S b).transpose) i j)
    simpa only [Matrix.mul_assoc] using (contDiff_pi.mp (contDiff_pi.mp hv i)) j
  · exact (contDiff_pi.mp (contDiff_pi.mp hvm i)) j

/-- All four actual normalized finite-pole defects have zero genuine amplitude
variation along every actual BH Jacobian kernel vector at a symmetric root. -/
theorem actual_kernel_poleDefects_fderiv_zero (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (hz : ∀ u, 0 < z u) (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hv : amplitudeJacobian z rho sigma K t p v = 0)
    (u : T) (k : Fin 4) (i j : Fin N) :
    fderiv ℝ (fun a => poleDefects z rho sigma a u k i j) p v = 0 := by
  have he : (fun a => poleDefects z rho sigma a u k i j) =
      fun a => poleErrorLift z rho sigma a (residual z rho sigma K (t, a)) u k i j := by
    funext a
    rw [actual_pole_residual_factorization z rho sigma K hK t a hz u]
  rw [he]
  apply residual_lift_kernel_fderiv
    (fun a => residual z rho sigma K (t, a)) (amplitudeJacobian z rho sigma K t p)
    (fun b => poleErrorLift z rho sigma b.1 b.2 u k i j) p v
    (residual_amplitudes_hasFDerivAt z rho sigma K t p)
    ((residual_eq_zero_iff z rho sigma K p.1 p.2 t).mpr hroot) hv
  · exact (poleErrorLift_entry_contDiff z rho sigma u k i j).differentiable (by simp) _
  · intro a
    rw [poleErrorLift_zero]
    rfl

/-- The actual defects themselves are smooth at arbitrary amplitudes, by the
zero-strength off-root residual factorization. -/
theorem actual_poleDefects_entry_contDiff (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (hz : ∀ u, 0 < z u) (u : T) (k : Fin 4) (i j : Fin N) :
    ContDiff ℝ ∞ (fun a : TailMatrix T N × TailMatrix T N => poleDefects z rho sigma a u k i j) := by
  have he : (fun a => poleDefects z rho sigma a u k i j) =
      fun a => poleErrorLift z rho sigma a (residual z rho sigma 0 (0, a)) u k i j := by
    funext a
    rw [actual_pole_residual_factorization z rho sigma 0 (by intros; rfl) 0 a hz u]
  rw [he]
  have hi : ContDiff ℝ ∞ (fun a : TailMatrix T N × TailMatrix T N => ((0 : ℝ), a)) :=
    contDiff_const.prodMk contDiff_id
  have hR : ContDiff ℝ ∞ (fun a : TailMatrix T N × TailMatrix T N =>
      residual z rho sigma 0 (0, a)) := (residual_contDiff z rho sigma 0).comp hi
  have hg : ContDiff ℝ ∞ (fun a : TailMatrix T N × TailMatrix T N =>
      (a, residual z rho sigma 0 (0, a))) := contDiff_id.prodMk hR
  exact ContDiff.comp (g := fun b : (TailMatrix T N × TailMatrix T N) ×
      (TailMatrix T N × TailMatrix T N) => poleErrorLift z rho sigma b.1 b.2 u k i j)
    (f := fun a : TailMatrix T N × TailMatrix T N => (a, residual z rho sigma 0 (0, a)))
    (poleErrorLift_entry_contDiff z rho sigma u k i j) hg

/-- Genuine unnormalized residue variations vanish in every actual BH kernel
direction, matching the finite Wronskian polynomial interface. -/
theorem actual_kernel_yukawaResidues_fderiv_zero (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (hz : ∀ u, 0 < z u) (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hv : amplitudeJacobian z rho sigma K t p v = 0)
    (u : T) (k : Fin 4) (i j : Fin N) :
    fderiv ℝ (fun a => yukawaResidues z rho sigma a u k i j) p v = 0 := by
  have he : (fun a => yukawaResidues z rho sigma a u k i j) =
      fun a => z u * poleDefects z rho sigma a u k i j := by
    funext a
    rw [yukawaResidues_eq_rate_smul z rho sigma a u (hz u).ne']
    rfl
  rw [he]
  have hd := ((actual_poleDefects_entry_contDiff z rho sigma hz u k i j).differentiable
    (by simp) p).hasFDerivAt.const_mul (z u)
  rw [hd.fderiv]
  simp only [smul_apply, smul_eq_mul,
    actual_kernel_poleDefects_fderiv_zero z rho sigma K hK hz t p v hroot hv, mul_zero]

end FMSA.Convergence.ResidualJets

/-- info: 'FMSA.Convergence.ResidualJets.residual_lift_kernel_fderiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ResidualJets.residual_lift_kernel_fderiv

/-- info: 'FMSA.Convergence.ResidualJets.matrix_family_mul_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ResidualJets.matrix_family_mul_contDiff

/-- info: 'FMSA.Convergence.ResidualJets.matrix_family_transpose_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ResidualJets.matrix_family_transpose_contDiff

/-- info: 'FMSA.Convergence.ResidualJets.poleErrorLift_entry_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ResidualJets.poleErrorLift_entry_contDiff

/-- info: 'FMSA.Convergence.ResidualJets.actual_kernel_poleDefects_fderiv_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ResidualJets.actual_kernel_poleDefects_fderiv_zero

/-- info: 'FMSA.Convergence.ResidualJets.actual_poleDefects_entry_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ResidualJets.actual_poleDefects_entry_contDiff

/-- info: 'FMSA.Convergence.ResidualJets.actual_kernel_yukawaResidues_fderiv_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ResidualJets.actual_kernel_yukawaResidues_fderiv_zero
