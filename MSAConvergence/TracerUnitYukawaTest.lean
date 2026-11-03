import MSAConvergence.TracerUniformRowEnergy

/-! A fixed unit-strength exterior Yukawa test localized to one active
column. Its covariance budget is independent of physical BH amplitudes. -/
noncomputable section
open Matrix MeasureTheory Real Set FMSA.HardSphere FMSA.ExactMSA FMSA.ExactMSA.MultiTailMixture MSAMixture
open FMSA.Convergence.TracerTailSpectralBound FMSA.Convergence.TracerSpectralL2
open FMSA.Convergence.TracerCovarianceQuadraticTrace FMSA.Convergence.RadialCovarianceBounds
open FMSA.Convergence.TracerStructureContinuity FMSA.Convergence.CanonicalInverseCovariance
open FMSA.Paper FMSA.Paper.ActualRDFParameters
open scoped BigOperators ComplexOrder
namespace FMSA.Convergence.TracerUnitYukawaTest
variable {N : ℕ} {T : Type*} [Fintype T]

def unitYukawaVector (s : ℝ) (rho sigma : Fin N → ℝ)
    (i j a : Fin N) (w : ℝ) : ℂ :=
  if a = j then (Real.sqrt (rho j) : ℂ) *
    ((w*radial_fourier (cMSAtail 1 s (edgeHi sigma i j)) (2*Real.pi*w) : ℝ) : ℂ)
  else 0

/-- A unit Yukawa test localized in column j has a fixed compact-spectrum
square majorant, valid at zero frequency as well. -/
theorem unit_yukawa_vector_square_dominated (s : ℝ) (hs : 0 < s)
    (rho sigma : Fin N → ℝ) (hρ : ∀ a, 0 ≤ rho a)
    (hσ : ∀ a, 0 < sigma a) (R : ℝ) (hR : 0 < R)
    (i j : Fin N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℝ,
      (∑ a : Fin N, ‖unitYukawaVector s rho sigma i j a w‖^2) ≤
        C*testWeight R w := by
  have hedge : 0 < edgeHi sigma i j := by dsimp [edgeHi]; linarith [hσ i,hσ j]
  obtain ⟨C,hC,hbound⟩ := tail_fourier_square_dominated s
    (edgeHi sigma i j) R hs hedge hR 1
  let M := rho j*C
  have hM : 0 ≤ M := mul_nonneg (hρ j) hC
  refine ⟨M,hM,?_⟩
  intro w
  have hsum : (∑ a : Fin N, ‖unitYukawaVector s rho sigma i j a w‖^2) =
      ‖unitYukawaVector s rho sigma i j j w‖^2 := by
    calc
      _ = ∑ a : Fin N, if a = j then
          ‖unitYukawaVector s rho sigma i j j w‖^2 else 0 := by
        apply Finset.sum_congr rfl
        intro a _
        by_cases ha : a = j
        · subst a; simp
        · simp [unitYukawaVector,ha]
      _ = _ := by simp
  rw [hsum]
  by_cases hw : w = 0
  · subst w
    simp [unitYukawaVector,testWeight]
  have hk : 2*Real.pi*w ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hw
  have htail := hbound (2*Real.pi*w) hk
  have hnorm : ‖unitYukawaVector s rho sigma i j j w‖^2 =
      rho j*w^2*|radial_fourier (cMSAtail 1 s (edgeHi sigma i j)) (2*Real.pi*w)|^2 := by
    have hval : unitYukawaVector s rho sigma i j j w =
        (Real.sqrt (rho j) : ℂ) *
          ((w*radial_fourier (cMSAtail 1 s (edgeHi sigma i j)) (2*Real.pi*w) : ℝ) : ℂ) := by
      simp [unitYukawaVector]
    rw [hval]
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,sq_abs,Real.sq_sqrt (hρ j)]
    ring
  calc
    _ = rho j*w^2*|radial_fourier (cMSAtail 1 s (edgeHi sigma i j)) (2*Real.pi*w)|^2 := hnorm
    _ ≤ (rho j*w^2)*(C*radial_fourier
        (fun r => CompactSpectralTest.profile (r/R)) (2*Real.pi*w)) :=
      mul_le_mul_of_nonneg_left htail (mul_nonneg (hρ j) (sq_nonneg w))
    _ = M*testWeight R w := by dsimp [M,testWeight]; ring


/-- The fixed unit-strength Yukawa test vector is continuous in frequency. -/
theorem unit_yukawa_vector_continuous (s : ℝ) (hs : 0 < s)
    (rho sigma : Fin N → ℝ) (hσ : ∀ a, 0 < sigma a)
    (i j a : Fin N) :
    Continuous (fun w : ℝ => unitYukawaVector s rho sigma i j a w) := by
  by_cases ha : a = j
  · subst a
    have hedge : 0 < edgeHi sigma i j := by dsimp [edgeHi]; linarith [hσ i,hσ j]
    have h := continuous_weighted_radial_fourier
      (cMSAtail 1 s (edgeHi sigma i j))
      (tail_odd_integrable s (edgeHi sigma i j) 1 hs hedge)
    have hc : Continuous (fun w : ℝ => (Real.sqrt (rho j) : ℂ) *
        ((w*radial_fourier (cMSAtail 1 s (edgeHi sigma i j)) (2*Real.pi*w) : ℝ) : ℂ)) :=
      (continuous_const : Continuous (fun _ : ℝ => (Real.sqrt (rho j) : ℂ))).mul
        (Complex.continuous_ofReal.comp h)
    simpa [unitYukawaVector,Complex.ofReal_mul] using hc
  · simpa [unitYukawaVector,ha] using (continuous_const : Continuous (fun _ : ℝ => (0 : ℂ)))

def unitYukawaQuadratic (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (K D G : TailMatrix T N) (s : ℝ) (i j : Fin N) (w : ℝ) : ℂ :=
  ∑ a : Fin N, ∑ b : Fin N,
    star (unitYukawaVector s rho sigma i j a w) *
      (MatrixOZPairing.structureMatrix z rho sigma K D G (2*Real.pi*w)) a b *
        unitYukawaVector s rho sigma i j b w

/-- The actual covariance integral of the fixed localized unit Yukawa test
has a uniform bound over bounded K and canonical roots; L1 is included. -/
theorem actual_unit_yukawa_covariance_integral_uniform
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hρ : ∀ a, 0 ≤ rho a) (hσ : ∀ a, 0 < sigma a)
    (hv : FMSA.MatrixQ0.vacMix rho sigma ≠ 0)
    (R : ℝ) (hR : 0 < R) (hRσ : ∀ a, R < sigma a)
    (B s : ℝ) (hs : 0 < s) (i j : Fin N) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ K D G : TailMatrix T N,
      ‖K‖ ≤ B → (∀ u a b, K u a b = K u b a) →
      IsRoot z rho sigma K D G →
      (∀ v : ℂ, 0 ≤ v.re → IsUnit (causalFactor z rho sigma D G v)) →
      Integrable (unitYukawaQuadratic z rho sigma K D G s i j) ∧
      ‖∫ w : ℝ, unitYukawaQuadratic z rho sigma K D G s i j w‖ ≤ M := by
  obtain ⟨C,hC,hvec⟩ := unit_yukawa_vector_square_dominated
    s hs rho sigma hρ hσ R hR i j
  let A : ℝ := (N:ℝ)*C
  let M : ℝ := max 0 (A*((N:ℝ)*(∫ w : ℝ, testWeight R w)))
  have hA : 0 ≤ A := mul_nonneg (Nat.cast_nonneg _) hC
  have hM : 0 ≤ M := le_max_left _ _
  refine ⟨M,hM,?_⟩
  intro K D G hB hK hroot hcanon
  let S : ℝ → Matrix (Fin N) (Fin N) ℂ := fun w =>
    MatrixOZPairing.structureMatrix z rho sigma K D G (2*Real.pi*w)
  let t : Fin N → ℝ → ℂ := fun a w => unitYukawaVector s rho sigma i j a w
  have hSc : Continuous S :=
    (actual_structure_matrix_continuous z hz rho sigma hρ hσ hv K D G hroot hK hcanon).comp
      (show Continuous (fun w : ℝ => 2*Real.pi*w) by fun_prop)
  have htc (a : Fin N) : Continuous (t a) :=
    unit_yukawa_vector_continuous s hs rho sigma hσ i j a
  have hqc : Continuous (unitYukawaQuadratic z rho sigma K D G s i j) := by
    change Continuous (fun w : ℝ => ∑ a : Fin N, ∑ b : Fin N,
      star (t a w)*S w a b*t b w)
    apply continuous_finsetSum
    intro a _
    apply continuous_finsetSum
    intro b _
    have he : Continuous (fun w : ℝ => S w a b) :=
      (continuous_apply b).comp ((continuous_apply a).comp hSc)
    exact ((htc a).star.mul he).mul (htc b)
  have htrace := actual_structure_weighted_trace_bound z hz rho sigma hρ hσ hv
    R hR hRσ K D G hK hroot hcanon
  have hpoint (w : ℝ) : ‖unitYukawaQuadratic z rho sigma K D G s i j w‖ ≤
      A*(testWeight R w*(S w).trace.re) := by
    have hF : IsUnit (physicalFactor z rho sigma D G (2*Real.pi*w)) :=
      FMSA.Convergence.ActualRadialTangentOZ.physical_fourier_factor_unit_of_kernel_unit
        z rho sigma hρ (D,G) (2*Real.pi*w) (hcanon _ (by simp))
    have hpos : (S w).PosDef :=
      MatrixOZPairing.actual_structure_matrix_posDef z hz rho sigma K D G
        hρ hσ hv hroot hK (2*Real.pi*w) hF
    exact posdef_quadratic_norm_le_weighted_trace (S w) hpos
      (fun a => t a w) C (testWeight R w) (hvec w)
  have hqi : Integrable (unitYukawaQuadratic z rho sigma K D G s i j) := by
    apply (htrace.1.const_mul A).mono' hqc.aestronglyMeasurable
    exact ae_of_all _ hpoint
  refine ⟨hqi,?_⟩
  calc
    ‖∫ w : ℝ, unitYukawaQuadratic z rho sigma K D G s i j w‖ ≤
      ∫ w : ℝ, ‖unitYukawaQuadratic z rho sigma K D G s i j w‖ :=
      norm_integral_le_integral_norm _
    _ ≤ A*(∫ w : ℝ, testWeight R w*(S w).trace.re) := by
      rw [← integral_const_mul]
      exact integral_mono hqi.norm (htrace.1.const_mul A) hpoint
    _ ≤ A*((N:ℝ)*(∫ w : ℝ, testWeight R w)) :=
      mul_le_mul_of_nonneg_left htrace.2 hA
    _ ≤ M := le_max_right _ _

end FMSA.Convergence.TracerUnitYukawaTest
/-- info: 'FMSA.Convergence.TracerUnitYukawaTest.unit_yukawa_vector_square_dominated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerUnitYukawaTest.unit_yukawa_vector_square_dominated
/-- info: 'FMSA.Convergence.TracerUnitYukawaTest.unit_yukawa_vector_continuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerUnitYukawaTest.unit_yukawa_vector_continuous
/-- info: 'FMSA.Convergence.TracerUnitYukawaTest.actual_unit_yukawa_covariance_integral_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerUnitYukawaTest.actual_unit_yukawa_covariance_integral_uniform
