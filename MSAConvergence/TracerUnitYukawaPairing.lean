import MSAConvergence.TracerUnitYukawaTest

/-! Exact localized unit-Yukawa spectral pairing with an original MSA
tracer row, and its covariance-metric pointwise energy bound. -/
noncomputable section
open Matrix MeasureTheory Real FMSA.HardSphere FMSA.ExactMSA FMSA.ExactMSA.MultiTailMixture MSAMixture
open FMSA.Convergence.TracerUnitYukawaTest FMSA.Convergence.TracerWeightedRowAlgebra
open FMSA.Convergence.TracerActualPointwiseForcing FMSA.Convergence.TracerEnergyCauchy
open FMSA.Convergence.TracerEnergyYoung FMSA.Convergence.TracerIntegratedEnergyIdentity
open FMSA.Convergence.TracerSpectralL2 FMSA.Convergence.TracerTailSpectralBound
open FMSA.Convergence.TracerUniformRowEnergy
open FMSA.Convergence.CanonicalInverseCovariance
open FMSA.Paper FMSA.Paper.ActualRDFParameters
open scoped BigOperators ComplexOrder
namespace FMSA.Convergence.TracerUnitYukawaPairing
variable {N : ℕ} {T : Type*} [Fintype T]

def unitYukawaRealRow (s : ℝ) (sigma : Fin N → ℝ)
    (i j a : Fin N) (w : ℝ) : ℝ :=
  if a = j then w*radial_fourier (cMSAtail 1 s (edgeHi sigma i j)) (2*Real.pi*w)
  else 0

/-- The localized test is a real density-weighted spectral row. -/
theorem unit_yukawa_vector_eq_weighted_real_row (s : ℝ)
    (rho sigma : Fin N → ℝ) (i j : Fin N) (w : ℝ) :
    (fun a => unitYukawaVector s rho sigma i j a w) =
      weightedRealRow rho (fun a => unitYukawaRealRow s sigma i j a w) := by
  funext a
  by_cases ha : a = j
  · subst a
    simp [unitYukawaVector,unitYukawaRealRow,weightedRealRow]
  · simp [unitYukawaVector,unitYukawaRealRow,weightedRealRow,ha]

/-- Real localized test removes the covariance transpose exactly. -/
theorem unit_yukawa_quadratic_transpose (A : Matrix (Fin N) (Fin N) ℂ)
    (s : ℝ) (rho sigma : Fin N → ℝ) (i j : Fin N) (w : ℝ) :
    let t : Fin N → ℂ := fun a => unitYukawaVector s rho sigma i j a w
    star t ⬝ᵥ (A.transpose *ᵥ t) = star t ⬝ᵥ (A *ᵥ t) := by
  rw [unit_yukawa_vector_eq_weighted_real_row]
  exact weighted_real_row_quadratic_transpose A rho
    (fun a => unitYukawaRealRow s sigma i j a w)

/-- The physical covariance trial uses exactly the finite double sum
controlled by the compact-spectrum trace estimate. -/
theorem unit_yukawa_quadratic_dotProduct (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (K D G : TailMatrix T N) (s : ℝ) (i j : Fin N) (w : ℝ) :
    let t : Fin N → ℂ := fun a => unitYukawaVector s rho sigma i j a w
    star t ⬝ᵥ
      (MatrixOZPairing.structureMatrix z rho sigma K D G (2*Real.pi*w) *ᵥ t) =
      unitYukawaQuadratic z rho sigma K D G s i j w := by
  change (∑ a : Fin N, star (unitYukawaVector s rho sigma i j a w) *
    (∑ b : Fin N,
      (MatrixOZPairing.structureMatrix z rho sigma K D G (2*Real.pi*w)) a b *
        unitYukawaVector s rho sigma i j b w)) = _
  simp only [unitYukawaQuadratic,Finset.mul_sum,mul_assoc]

/-- The localized test/actual-h row dot product is exactly rho_j times
the radial Fourier product, with its true w-squared normalization. -/
theorem unit_yukawa_h_pair (s : ℝ) (rho sigma : Fin N → ℝ)
    (hρ : ∀ a, 0 ≤ rho a) (i j : Fin N) (w : ℝ) (h : Fin N → ℝ) :
    (star (fun a => unitYukawaVector s rho sigma i j a w) ⬝ᵥ
      weightedRealRow rho h).re =
      rho j*(w*radial_fourier (cMSAtail 1 s (edgeHi sigma i j)) (2*Real.pi*w))*h j := by
  rw [unit_yukawa_vector_eq_weighted_real_row]
  rw [weighted_real_row_pair rho hρ
    (fun a => unitYukawaRealRow s sigma i j a w) h]
  simp [unitYukawaRealRow]


/-- The actual localized Yukawa h spectral pairing is pointwise controlled
by one quarter of the genuine tracer-row energy plus the fixed test's
physical covariance quadratic. -/
theorem actual_unit_yukawa_pair_pointwise_energy_bound
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ a, 0 ≤ rho a)
    (hσ : ∀ a, 0 < sigma a) (hv : FMSA.MatrixQ0.vacMix rho sigma ≠ 0)
    (K D G : TailMatrix T N) (hK : ∀ u a b, K u a b = K u b a)
    (hroot : IsRoot z rho sigma K D G)
    (hcanon : ∀ v : ℂ, 0 ≤ v.re → IsUnit (causalFactor z rho sigma D G v))
    (s : ℝ) (i j : Fin N) (w : ℝ) (hw : w ≠ 0) :
    rho j * |w^2*radial_fourier (nonlinearH z rho sigma D G i j) (2*Real.pi*w)*
      radial_fourier (cMSAtail 1 s (edgeHi sigma i j)) (2*Real.pi*w)| ≤
      rowEnergy z rho sigma K D G i w/4 +
        (unitYukawaQuadratic z rho sigma K D G s i j w).re := by
  let S := MatrixOZPairing.structureMatrix z rho sigma K D G (2*Real.pi*w)
  let c : Fin N → ℝ := fun a => w*radial_fourier
    (orderedRadialCorrelation z rho sigma K D G i a) (2*Real.pi*w)
  let h : Fin N → ℝ := fun a => w*radial_fourier
    (nonlinearH z rho sigma D G i a) (2*Real.pi*w)
  let x : Fin N → ℂ := weightedRealRow rho c
  let t : Fin N → ℂ := fun a => unitYukawaVector s rho sigma i j a w
  have hF : IsUnit (physicalFactor z rho sigma D G (2*Real.pi*w)) :=
    FMSA.Convergence.ActualRadialTangentOZ.physical_fourier_factor_unit_of_kernel_unit
      z rho sigma hρ (D,G) (2*Real.pi*w) (hcanon _ (by simp))
  have hpos : S.PosDef := MatrixOZPairing.actual_structure_matrix_posDef
    z hz rho sigma K D G hρ hσ hv hroot hK (2*Real.pi*w) hF
  have hrow : weightedRealRow rho h = S.transpose *ᵥ x :=
    actual_weighted_row_OZ z hz rho sigma hρ hσ hv K D G hK hroot hcanon i w hw
  have hpair := unit_yukawa_h_pair s rho sigma hρ i j w h
  have hE : (star x ⬝ᵥ (S.transpose *ᵥ x)).re =
      rowEnergy z rho sigma K D G i w := by
    rw [← hrow]
    rw [weighted_real_row_pair rho hρ c h]
    simp only [rowEnergy,c,h]
    apply Finset.sum_congr rfl
    intro a _
    ring
  have hQ : (star t ⬝ᵥ (S.transpose *ᵥ t)).re =
      (unitYukawaQuadratic z rho sigma K D G s i j w).re := by
    rw [unit_yukawa_quadratic_transpose S s rho sigma i j w]
    exact congrArg Complex.re (unit_yukawa_quadratic_dotProduct z rho sigma K D G s i j w)
  have hEn : 0 ≤ (star x ⬝ᵥ (S.transpose *ᵥ x)).re :=
    hpos.transpose.posSemidef.re_dotProduct_nonneg x
  have hQn : 0 ≤ (star t ⬝ᵥ (S.transpose *ᵥ t)).re :=
    hpos.transpose.posSemidef.re_dotProduct_nonneg t
  have hCS := positive_matrix_cross_norm_le_energy S.transpose hpos.transpose t x
  have hreal : |(star t ⬝ᵥ weightedRealRow rho h).re| ≤
      (star x ⬝ᵥ (S.transpose *ᵥ x)).re/4 +
        (star t ⬝ᵥ (S.transpose *ᵥ t)).re := by
    rw [hrow]
    calc
      _ ≤ ‖star t ⬝ᵥ (S.transpose *ᵥ x)‖ := Complex.abs_re_le_norm _
      _ ≤ Real.sqrt ((star t ⬝ᵥ (S.transpose *ᵥ t)).re) *
        Real.sqrt ((star x ⬝ᵥ (S.transpose *ᵥ x)).re) := hCS
      _ = Real.sqrt ((star x ⬝ᵥ (S.transpose *ᵥ x)).re) *
        Real.sqrt ((star t ⬝ᵥ (S.transpose *ᵥ t)).re) := mul_comm _ _
      _ ≤ _ := sqrt_mul_le_quarter_energy_add _ _ hEn hQn
  rw [hpair,hE,hQ] at hreal
  have he : |rho j * (w*radial_fourier (cMSAtail 1 s (edgeHi sigma i j)) (2*Real.pi*w))*h j| =
      rho j * |w^2*radial_fourier (nonlinearH z rho sigma D G i j) (2*Real.pi*w)*
        radial_fourier (cMSAtail 1 s (edgeHi sigma i j)) (2*Real.pi*w)| := by
    have he0 : rho j * (w*radial_fourier (cMSAtail 1 s (edgeHi sigma i j)) (2*Real.pi*w))*h j =
        rho j * (w^2*radial_fourier (nonlinearH z rho sigma D G i j) (2*Real.pi*w)*
          radial_fourier (cMSAtail 1 s (edgeHi sigma i j)) (2*Real.pi*w)) := by
      dsimp only [h]
      ring
    rw [he0,abs_mul,abs_of_nonneg (hρ j)]
  rw [he] at hreal
  exact hreal


/-- The ACTUAL h/unit-Yukawa spectral pairing is controlled by one quarter
of the integrated tracer-row energy and the norm of the fixed test's
physical covariance integral. -/
theorem actual_unit_yukawa_spectral_pair_integral_le
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ a, 0 ≤ rho a)
    (hσ : ∀ a, 0 < sigma a) (hv : FMSA.MatrixQ0.vacMix rho sigma ≠ 0)
    (R : ℝ) (hR : 0 < R) (hRσ : ∀ a, R < sigma a)
    (B s : ℝ) (hs : 0 < s) (K D G : TailMatrix T N) (hB : ‖K‖ ≤ B)
    (hK : ∀ u a b, K u a b = K u b a)
    (hroot : IsRoot z rho sigma K D G)
    (hcanon : ∀ v : ℂ, 0 ≤ v.re → IsUnit (causalFactor z rho sigma D G v))
    (i j : Fin N) :
    rho j * |∫ w : ℝ, w^2*
      radial_fourier (nonlinearH z rho sigma D G i j) (2*Real.pi*w)*
      radial_fourier (cMSAtail 1 s (edgeHi sigma i j)) (2*Real.pi*w)| ≤
      (∫ w : ℝ, rowEnergy z rho sigma K D G i w)/4 +
      ‖∫ w : ℝ, unitYukawaQuadratic z rho sigma K D G s i j w‖ := by
  let H := nonlinearH z rho sigma D G i j
  let ψ := cMSAtail 1 s (edgeHi sigma i j)
  let F : ℝ → ℝ := fun w => w^2*radial_fourier H (2*Real.pi*w)*
    radial_fourier ψ (2*Real.pi*w)
  have hedge : 0 < edgeHi sigma i j := by dsimp [edgeHi]; linarith [hσ i,hσ j]
  have hHi := actual_h_weighted_spectral_memLp_two z hz rho sigma hσ hv D G hcanon i j
  have hψi := weighted_radial_fourier_memLp_two ψ
    (tail_odd_integrable s (edgeHi sigma i j) 1 hs hedge)
    (tail_odd_memLp_two s (edgeHi sigma i j) 1 hs hedge)
  have hFi : Integrable F := weighted_radial_pair_integrable H ψ hHi hψi
  have hEi := (actual_row_energy_integral_split z hz rho sigma hσ hv K D G
    hK hroot hcanon i).1
  obtain ⟨M,hM,hq⟩ := actual_unit_yukawa_covariance_integral_uniform
    z hz rho sigma hρ hσ hv R hR hRσ B s hs i j
  obtain ⟨hqi,_⟩ := hq K D G hB hK hroot hcanon
  have hqr : Integrable (fun w : ℝ =>
      (unitYukawaQuadratic z rho sigma K D G s i j w).re) := by
    simpa only [RCLike.re_to_complex] using hqi.re
  have hpoint (w : ℝ) : rho j*|F w| ≤
      rowEnergy z rho sigma K D G i w/4 +
        (unitYukawaQuadratic z rho sigma K D G s i j w).re := by
    by_cases hw : w = 0
    · subst w
      simp [F,rowEnergy,unitYukawaQuadratic,unitYukawaVector]
    · exact actual_unit_yukawa_pair_pointwise_energy_bound z hz rho sigma hρ hσ hv
        K D G hK hroot hcanon s i j w hw
  have hRi : Integrable (fun w : ℝ =>
      rowEnergy z rho sigma K D G i w/4 +
        (unitYukawaQuadratic z rho sigma K D G s i j w).re) :=
    (hEi.div_const 4).add hqr
  calc
    rho j*|∫ w : ℝ, F w| ≤ rho j*(∫ w : ℝ, |F w|) :=
      mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm F)) (hρ j)
    _ = ∫ w : ℝ, rho j*|F w| := (integral_const_mul _ _).symm
    _ ≤ ∫ w : ℝ, rowEnergy z rho sigma K D G i w/4 +
        (unitYukawaQuadratic z rho sigma K D G s i j w).re :=
      integral_mono (hFi.norm.const_mul _) hRi hpoint
    _ = (∫ w : ℝ, rowEnergy z rho sigma K D G i w)/4 +
        (∫ w : ℝ, (unitYukawaQuadratic z rho sigma K D G s i j w).re) := by
      rw [integral_add (hEi.div_const 4) hqr,integral_div]
    _ ≤ _ := add_le_add_right
      (FMSA.Convergence.TracerUniformRowEnergy.integral_real_part_le_norm_integral _ hqi) _


/-- For any fixed positive rate and any row/column, the genuine h Fourier
pairing with the unit exterior Yukawa test is uniformly bounded after the
single column-density weight. In particular, active columns can be
unweighted by their fixed positive density. -/
theorem actual_unit_yukawa_spectral_pair_uniform
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hρ : ∀ a, 0 ≤ rho a)
    (hσ : ∀ a, 0 < sigma a) (hv : FMSA.MatrixQ0.vacMix rho sigma ≠ 0)
    (R : ℝ) (hR : 0 < R) (hRσ : ∀ a, R < sigma a)
    (B s : ℝ) (hs : 0 < s) (i j : Fin N) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ K D G : TailMatrix T N,
      ‖K‖ ≤ B → (∀ u a b, K u a b = K u b a) →
      IsRoot z rho sigma K D G →
      (∀ v : ℂ, 0 ≤ v.re → IsUnit (causalFactor z rho sigma D G v)) →
      rho j * |∫ w : ℝ, w^2*
        radial_fourier (nonlinearH z rho sigma D G i j) (2*Real.pi*w)*
        radial_fourier (cMSAtail 1 s (edgeHi sigma i j)) (2*Real.pi*w)| ≤ M := by
  obtain ⟨ME,hME,hE⟩ := actual_tracer_row_energy_integral_uniform
    z hz rho sigma hρ hσ hv R hR hRσ B i
  obtain ⟨MQ,hMQ,hQ⟩ := actual_unit_yukawa_covariance_integral_uniform
    z hz rho sigma hρ hσ hv R hR hRσ B s hs i j
  refine ⟨ME/4+MQ,by positivity,?_⟩
  intro K D G hB hK hroot hcanon
  have hpair := actual_unit_yukawa_spectral_pair_integral_le
    z hz rho sigma hρ hσ hv R hR hRσ B s hs K D G hB hK hroot hcanon i j
  have hEb := hE K D G hB hK hroot hcanon
  have hQb := (hQ K D G hB hK hroot hcanon).2
  linarith

end FMSA.Convergence.TracerUnitYukawaPairing
/-- info: 'FMSA.Convergence.TracerUnitYukawaPairing.unit_yukawa_vector_eq_weighted_real_row' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerUnitYukawaPairing.unit_yukawa_vector_eq_weighted_real_row
/-- info: 'FMSA.Convergence.TracerUnitYukawaPairing.unit_yukawa_quadratic_transpose' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerUnitYukawaPairing.unit_yukawa_quadratic_transpose
/-- info: 'FMSA.Convergence.TracerUnitYukawaPairing.unit_yukawa_quadratic_dotProduct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerUnitYukawaPairing.unit_yukawa_quadratic_dotProduct
/-- info: 'FMSA.Convergence.TracerUnitYukawaPairing.unit_yukawa_h_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerUnitYukawaPairing.unit_yukawa_h_pair
/-- info: 'FMSA.Convergence.TracerUnitYukawaPairing.actual_unit_yukawa_pair_pointwise_energy_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerUnitYukawaPairing.actual_unit_yukawa_pair_pointwise_energy_bound
/-- info: 'FMSA.Convergence.TracerUnitYukawaPairing.actual_unit_yukawa_spectral_pair_integral_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerUnitYukawaPairing.actual_unit_yukawa_spectral_pair_integral_le
/-- info: 'FMSA.Convergence.TracerUnitYukawaPairing.actual_unit_yukawa_spectral_pair_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerUnitYukawaPairing.actual_unit_yukawa_spectral_pair_uniform
