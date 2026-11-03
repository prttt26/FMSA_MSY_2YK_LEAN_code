import MSAConvergence.TracerTailField
import MSAConvergence.ActualStructureCovariance

/-! Genuine base-c odd L1/L2 and unweighted value OZ for the actual MSA
mixture root. All species rows, including zero-density tracers, are retained. -/
noncomputable section
open MeasureTheory Set Real FMSA.ExactMSA.MultiTailMixture FMSA.HardSphere
open FMSA.Paper.PhysicalExteriorJets FMSA.Paper.JacobianL2 FMSA.Paper
open FMSA.Convergence.ActualStructureCovariance FMSA.Convergence.ActualRadialTangentOZ
open scoped BigOperators
namespace FMSA.Convergence.TracerBaseCField
variable {N : ℕ} {T : Type*} [Fintype T]

/-- The actual finite Baxter basis bounds the weighted root DCF numerator. -/
theorem root_c_weighted_bounded (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hs : ∀ i, 0 ≤ sigma i)
    (p : TailMatrix T N × TailMatrix T N) (i j : Fin N) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r : ℝ, |r*rootCorrelation z rho sigma p i j r| ≤ B := by
  choose M hM using numeratorKernel_bounded z hz sigma hs i j
  let d := numeratorCoefficient z rho sigma p i j
  let A := ∑ b : NumeratorIndex T N, |d b| *M b
  have hM0 (b : NumeratorIndex T N) : 0 ≤ M b := (abs_nonneg _).trans (hM b 0)
  have hA : 0 ≤ A := Finset.sum_nonneg (fun b _ => mul_nonneg (abs_nonneg _) (hM0 b))
  have hnum (r : ℝ) :
      |∑ b : NumeratorIndex T N, d b*numeratorKernel z sigma i j b r| ≤ A := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro b _
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hM b r) (abs_nonneg _)
  refine ⟨A/(2*Real.pi),by positivity,?_⟩
  intro r
  by_cases hr : r = 0
  · simp only [hr,zero_mul,abs_zero]
    positivity
  · have he : r*rootCorrelation z rho sigma p i j r =
        (∑ b : NumeratorIndex T N, d b*numeratorKernel z sigma i j b r)/(2*Real.pi) := by
      rw [correlation_eq_numerator z hz rho sigma hs p i j r]
      dsimp only [d]
      field_simp [hr]
    rw [he,abs_div,abs_of_pos (by positivity : 0 < 2*Real.pi)]
    exact div_le_div_of_nonneg_right (hnum r) (by positivity)

/-- The ordered DCF choice retains the same weighted pointwise bound. -/
theorem ordered_c_weighted_bounded (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hs : ∀ i, 0 ≤ sigma i)
    (K D G : TailMatrix T N) (i j : Fin N) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r : ℝ,
      |r*orderedRadialCorrelation z rho sigma K D G i j r| ≤ B := by
  obtain ⟨B1,hB1,h1⟩ := root_c_weighted_bounded z hz rho sigma hs (D,G) i j
  obtain ⟨B2,hB2,h2⟩ := root_c_weighted_bounded z hz rho sigma hs (D,G) j i
  refine ⟨max B1 B2,hB1.trans (le_max_left _ _),?_⟩
  intro r
  unfold orderedRadialCorrelation
  split_ifs with ho
  · exact (h1 r).trans (le_max_left _ _)
  · exact (h2 r).trans (le_max_right _ _)

/-- At an actual root the ordered DCF odd radial field belongs to L1 and L2. -/
theorem actual_odd_c_L1_L2 (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hs : ∀ i, 0 < sigma i)
    (K D G : TailMatrix T N) (hroot : IsRoot z rho sigma K D G)
    (i j : Fin N) :
    Integrable (oddRadialMoment (orderedRadialCorrelation z rho sigma K D G i j)) ∧
      MemLp (oddRadialMoment (orderedRadialCorrelation z rho sigma K D G i j)) 2 volume := by
  have hσ : ∀ i, 0 ≤ sigma i := fun i => (hs i).le
  have hi := oddRadialMoment_integrable
    (nonlinear_orderedCorrelation_radius_integrable z hz rho sigma K D G hσ hroot i j)
  obtain ⟨B,hB,hbound⟩ := ordered_c_weighted_bounded z hz rho sigma hσ K D G i j
  refine ⟨hi,?_⟩
  apply FMSA.Convergence.ActualHRadialL2.integrable_bounded_memLp_two _ hi B
  apply ae_of_all
  intro r
  have h := hbound |r|
  simpa only [oddRadialMoment,Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_abs] using h

/-- The genuine DCF Fourier value equals the finite spectral C at a root. -/
theorem actual_c_radial_eq_spectral (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hs : ∀ i, 0 < sigma i)
    (hv : FMSA.MatrixQ0.vacMix rho sigma ≠ 0)
    (K D G : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (hroot : IsRoot z rho sigma K D G) (k : ℝ) (hk : k ≠ 0)
    (i j : Fin N) :
    (radial_fourier (orderedRadialCorrelation z rho sigma K D G i j) k : ℂ) =
      nonlinearActualFourierC z rho sigma D G k i j := by
  classical
  have hσ : ∀ i, 0 ≤ sigma i := fun i => (hs i).le
  have hw := nonlinearRoot_automatic_finite_wronskian z rho sigma K D G hz hv hroot hK
  have hc := nonlinear_finite_wronskian_actual_core_reciprocity z rho sigma D G hz hσ hw
  have he := spectralBaxterC_eq_ordered_radial_of_ae_core_reciprocity z hz rho sigma K D G hs hroot hK hc k hk i j
  simpa only [nonlinearActualFourierC,Matrix.of_apply] using he.symm

/-- The actual c and h Fourier value matrices satisfy unweighted OZ. -/
theorem actual_unweighted_radial_OZ (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hs : ∀ i, 0 < sigma i)
    (hv : FMSA.MatrixQ0.vacMix rho sigma ≠ 0)
    (K D G : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (hroot : IsRoot z rho sigma K D G)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma D G) s))
    (k : ℝ) (hk : k ≠ 0) :
    let C : Matrix (Fin N) (Fin N) ℂ := Matrix.of (fun i j =>
      (radial_fourier (orderedRadialCorrelation z rho sigma K D G i j) k : ℂ))
    let H : Matrix (Fin N) (Fin N) ℂ := Matrix.of (fun i j =>
      (radial_fourier (nonlinearH z rho sigma D G i j) k : ℂ))
    let R : Matrix (Fin N) (Fin N) ℂ := Matrix.diagonal (fun i => (rho i : ℂ))
    H = C*(1+R*H) := by
  classical
  dsimp only
  let C : Matrix (Fin N) (Fin N) ℂ := Matrix.of (fun i j =>
    (radial_fourier (orderedRadialCorrelation z rho sigma K D G i j) k : ℂ))
  let H : Matrix (Fin N) (Fin N) ℂ := Matrix.of (fun i j =>
    (radial_fourier (nonlinearH z rho sigma D G i j) k : ℂ))
  let R : Matrix (Fin N) (Fin N) ℂ := Matrix.diagonal (fun i => (rho i : ℂ))
  have hC : C = nonlinearActualFourierC z rho sigma D G k := by
    ext i j
    exact actual_c_radial_eq_spectral z hz rho sigma hs hv K D G hK hroot k hk i j
  have hH : H = completedRadial z rho sigma (D,G) k :=
    actual_h_radial_eq_completed z hz rho sigma hs hv D G hcanon k hk
  have hoz : (1-C*R)*H=C := by
    rw [hC,hH]
    exact (actual_kernel_completed_OZ z hz rho sigma (fun i => (hs i).le)
      K hK hv 1 (D,G) 0 (by simpa only [one_smul] using hroot)
      (by exact map_zero _) hcanon k hk).1
  dsimp only [C,H,R] at hoz ⊢
  linear_combination (norm := noncomm_ring) hoz

/-- OZ survives zero-density rows without dividing by any density. -/
theorem actual_sqrt_density_row_OZ (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ i, 0 ≤ rho i)
    (hs : ∀ i, 0 < sigma i) (hv : FMSA.MatrixQ0.vacMix rho sigma ≠ 0)
    (K D G : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (hroot : IsRoot z rho sigma K D G)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma D G) s))
    (k : ℝ) (hk : k ≠ 0) :
    let C : Matrix (Fin N) (Fin N) ℂ := Matrix.of (fun i j =>
      (radial_fourier (orderedRadialCorrelation z rho sigma K D G i j) k : ℂ))
    let H : Matrix (Fin N) (Fin N) ℂ := Matrix.of (fun i j =>
      (radial_fourier (nonlinearH z rho sigma D G i j) k : ℂ))
    let S : Matrix (Fin N) (Fin N) ℂ := Matrix.diagonal (fun i => (sqrt (rho i) : ℂ))
    H*S = (C*S)*(1+S*H*S) := by
  dsimp only
  let C : Matrix (Fin N) (Fin N) ℂ := Matrix.of (fun i j =>
    (radial_fourier (orderedRadialCorrelation z rho sigma K D G i j) k : ℂ))
  let H : Matrix (Fin N) (Fin N) ℂ := Matrix.of (fun i j =>
    (radial_fourier (nonlinearH z rho sigma D G i j) k : ℂ))
  let S : Matrix (Fin N) (Fin N) ℂ := Matrix.diagonal (fun i => (sqrt (rho i) : ℂ))
  let R : Matrix (Fin N) (Fin N) ℂ := Matrix.diagonal (fun i => (rho i : ℂ))
  have hsquare : S*S=R := by
    rw [show S=Matrix.diagonal (fun i => (sqrt (rho i) : ℂ)) from rfl,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact_mod_cast Real.mul_self_sqrt (hρ i)
  have hoz : H=C*(1+R*H) :=
    actual_unweighted_radial_OZ z hz rho sigma hs hv K D G hK hroot hcanon k hk
  rw [← hsquare] at hoz
  change H*S=(C*S)*(1+S*H*S)
  calc
    H*S = (C*(1+S*S*H))*S := congrArg (fun X : Matrix (Fin N) (Fin N) ℂ => X*S) hoz
    _ = (C*S)*(1+S*H*S) := by noncomm_ring

/-- The genuine h/c row transfer uses the positive physical structure matrix. -/
theorem actual_row_OZ_structure (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ i, 0 ≤ rho i)
    (hs : ∀ i, 0 < sigma i) (hv : FMSA.MatrixQ0.vacMix rho sigma ≠ 0)
    (K D G : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (hroot : IsRoot z rho sigma K D G)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma D G) s))
    (k : ℝ) (hk : k ≠ 0) :
    let C : Matrix (Fin N) (Fin N) ℂ := Matrix.of (fun i j =>
      (radial_fourier (orderedRadialCorrelation z rho sigma K D G i j) k : ℂ))
    let H : Matrix (Fin N) (Fin N) ℂ := Matrix.of (fun i j =>
      (radial_fourier (nonlinearH z rho sigma D G i j) k : ℂ))
    let S : Matrix (Fin N) (Fin N) ℂ := Matrix.diagonal (fun i => (sqrt (rho i) : ℂ))
    H*S = (C*S)*MatrixOZPairing.structureMatrix z rho sigma K D G k := by
  let C : Matrix (Fin N) (Fin N) ℂ := Matrix.of (fun i j =>
    (radial_fourier (orderedRadialCorrelation z rho sigma K D G i j) k : ℂ))
  let H : Matrix (Fin N) (Fin N) ℂ := Matrix.of (fun i j =>
    (radial_fourier (nonlinearH z rho sigma D G i j) k : ℂ))
  let S : Matrix (Fin N) (Fin N) ℂ := Matrix.diagonal (fun i => (sqrt (rho i) : ℂ))
  have hrow : H*S=(C*S)*(1+S*H*S) :=
    actual_sqrt_density_row_OZ z hz rho sigma hρ hs hv K D G hK hroot hcanon k hk
  have hstructure : 1+S*H*S=MatrixOZPairing.structureMatrix z rho sigma K D G k := by
    simpa only [S,H] using actual_structure_eq_covariance z hz rho sigma hρ hs hv K D G hK hroot hcanon k hk
  change H*S=(C*S)*MatrixOZPairing.structureMatrix z rho sigma K D G k
  rw [← hstructure]
  exact hrow

end FMSA.Convergence.TracerBaseCField
/-- info: 'FMSA.Convergence.TracerBaseCField.root_c_weighted_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerBaseCField.root_c_weighted_bounded
/-- info: 'FMSA.Convergence.TracerBaseCField.ordered_c_weighted_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerBaseCField.ordered_c_weighted_bounded
/-- info: 'FMSA.Convergence.TracerBaseCField.actual_odd_c_L1_L2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerBaseCField.actual_odd_c_L1_L2
/-- info: 'FMSA.Convergence.TracerBaseCField.actual_c_radial_eq_spectral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerBaseCField.actual_c_radial_eq_spectral
/-- info: 'FMSA.Convergence.TracerBaseCField.actual_unweighted_radial_OZ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerBaseCField.actual_unweighted_radial_OZ
/-- info: 'FMSA.Convergence.TracerBaseCField.actual_sqrt_density_row_OZ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerBaseCField.actual_sqrt_density_row_OZ
/-- info: 'FMSA.Convergence.TracerBaseCField.actual_row_OZ_structure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerBaseCField.actual_row_OZ_structure
