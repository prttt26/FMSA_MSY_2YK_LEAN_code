import MSAConvergence.TracerTailSpectralBound

/-! Genuine L1/L2 memberships and Fourier linearity for the finite exterior
Yukawa tail field, with an exact link to the actual ordered MSA DCF. -/
noncomputable section
open MeasureTheory Set Real FMSA.ExactMSA FMSA.ExactMSA.MultiTailMixture FMSA.HardSphere MSAMixture
namespace FMSA.Convergence.TracerTailSpectralBound

/-- The positive radial moment of one exterior tail is genuinely L1. -/
theorem tail_radius_integrable (z sigma K : ℝ) (hz : 0 < z) (hs : 0 < sigma) :
    IntegrableOn (fun r : ℝ => r*cMSAtail K z sigma r) (Ioi 0) := by
  have hi : IntegrableOn (fun r : ℝ => K*exp (-z*(r-sigma))) (Ioi sigma) :=
    (shiftedRealExp_integrable z sigma sigma hz).const_mul K
  have he : (Ioi (0:ℝ)).indicator (fun r => r*cMSAtail K z sigma r) =
      (Ioi sigma).indicator (fun r => K*exp (-z*(r-sigma))) := by
    funext r
    by_cases houter : sigma < r
    · have h0 : 0 < r := hs.trans houter
      rw [indicator_of_mem (mem_Ioi.mpr h0),indicator_of_mem (mem_Ioi.mpr houter)]
      simp only [cMSAtail,if_pos houter]
      field_simp [h0.ne']
    · rw [indicator_of_notMem (show r ∉ Ioi sigma from houter)]
      by_cases h0 : 0 < r
      · rw [indicator_of_mem (mem_Ioi.mpr h0)]
        simp only [cMSAtail,if_neg houter,mul_zero]
      · rw [indicator_of_notMem (show r ∉ Ioi 0 from h0)]
  apply (integrable_indicator_iff measurableSet_Ioi).mp
  rw [he]
  exact hi.integrable_indicator measurableSet_Ioi

/-- One Yukawa exterior tail has an honest odd radial L1 field. -/
theorem tail_odd_integrable (z sigma K : ℝ) (hz : 0 < z) (hs : 0 < sigma) :
    Integrable (oddRadialMoment (cMSAtail K z sigma)) :=
  oddRadialMoment_integrable (tail_radius_integrable z sigma K hz hs)

/-- The same odd radial exterior field belongs to L2. -/
theorem tail_odd_memLp_two (z sigma K : ℝ) (hz : 0 < z) (hs : 0 < sigma) :
    MemLp (oddRadialMoment (cMSAtail K z sigma)) 2 volume := by
  apply FMSA.Convergence.ActualHRadialL2.integrable_bounded_memLp_two _
    (tail_odd_integrable z sigma K hz hs) |K|
  apply ae_of_all
  intro r
  by_cases houter : sigma < |r|
  · have hr : 0 < |r| := hs.trans houter
    have he : exp (-z*(|r|-sigma)) ≤ 1 := exp_le_one_iff.mpr (by nlinarith)
    simp only [oddRadialMoment,cMSAtail,if_pos houter,Complex.norm_real,Real.norm_eq_abs]
    rw [abs_mul,abs_div,abs_mul,abs_of_pos (exp_pos _),abs_abs]
    have hx : |r| *(|K| *exp (-z*(|r|-sigma))/|r|)=|K| *exp (-z*(|r|-sigma)) := by
      field_simp [hr.ne']
    rw [hx]
    exact mul_le_of_le_one_right (abs_nonneg K) he
  · simp only [oddRadialMoment,cMSAtail,if_neg houter,mul_zero,Complex.ofReal_zero,norm_zero]
    exact abs_nonneg K

/-- The physical finite exterior Yukawa tail as a function of radius. -/
def tailField {T : Type*} [Fintype T] (z : T → ℝ)
    (sigma : ℝ) (K : T → ℝ) (r : ℝ) : ℝ :=
  ∑ u, cMSAtail (K u) (z u) sigma r

/-- The finite signed tail field has its own odd radial L1 and L2 proofs. -/
theorem tail_field_odd_L1_L2 {T : Type*} [Fintype T] (z : T → ℝ)
    (hz : ∀ u, 0 < z u) (sigma : ℝ) (hs : 0 < sigma) (K : T → ℝ) :
    Integrable (oddRadialMoment (tailField z sigma K)) ∧
      MemLp (oddRadialMoment (tailField z sigma K)) 2 volume := by
  have he (r : ℝ) : oddRadialMoment (tailField z sigma K) r =
      ∑ u, oddRadialMoment (cMSAtail (K u) (z u) sigma) r := by
    simp only [oddRadialMoment,tailField,Finset.mul_sum,Complex.ofReal_sum]
  constructor
  · rw [show oddRadialMoment (tailField z sigma K) =
        (fun r => ∑ u, oddRadialMoment (cMSAtail (K u) (z u) sigma) r) from funext he]
    exact integrable_finsetSum Finset.univ
      (fun u _ => tail_odd_integrable (z u) sigma (K u) (hz u) hs)
  · rw [show oddRadialMoment (tailField z sigma K) =
        (fun r => ∑ u, oddRadialMoment (cMSAtail (K u) (z u) sigma) r) from funext he]
    exact memLp_finsetSum Finset.univ
      (fun u _ => tail_odd_memLp_two (z u) sigma (K u) (hz u) hs)

/-- Its actual radial Fourier transform equals the finite symbol. -/
theorem tail_field_radial_fourier_eq_symbol {T : Type*} [Fintype T]
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (sigma : ℝ) (hs : 0 < sigma)
    (K : T → ℝ) (k : ℝ) :
    radial_fourier (tailField z sigma K) k = tailSymbol z sigma K k := by
  have hi (u : T) : IntegrableOn
      (fun r : ℝ => r*cMSAtail (K u) (z u) sigma r*Real.sin (k*r)) (Ioi 0) := by
    exact (tail_radius_integrable (z u) sigma (K u) (hz u) hs).mul_bdd
      ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).aestronglyMeasurable)
      (ae_of_all _ (fun r => by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one (k*r)))
  have he : (∫ r in Ioi (0:ℝ), r*tailField z sigma K r*Real.sin (k*r)) =
      ∑ u, ∫ r in Ioi (0:ℝ), r*cMSAtail (K u) (z u) sigma r*Real.sin (k*r) := by
    have hpoint : ∀ r : ℝ, r*tailField z sigma K r*Real.sin (k*r) =
        ∑ u, r*cMSAtail (K u) (z u) sigma r*Real.sin (k*r) := by
      intro r
      simp only [tailField,Finset.mul_sum,Finset.sum_mul]
    simp_rw [hpoint]
    exact integral_finsetSum Finset.univ (fun u _ => hi u)
  unfold radial_fourier tailSymbol
  rw [he,Finset.mul_sum]
  rfl

/-- Uniform compact-profile square domination for the genuine tail field. -/
theorem tail_field_square_dominated {T : Type*} [Fintype T]
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (sigma R : ℝ)
    (hs : 0 < sigma) (hR : 0 < R) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K : T → ℝ, (∀ u, |K u| ≤ B) →
      ∀ k : ℝ, k ≠ 0 →
        |radial_fourier (tailField z sigma K) k|^2 ≤
          C*radial_fourier (fun r => CompactSpectralTest.profile (r/R)) k := by
  obtain ⟨C,hC,hbound⟩ := tail_symbol_square_dominated z hz sigma R hs hR B
  refine ⟨C,hC,?_⟩
  intro K hK k hk
  rw [tail_field_radial_fourier_eq_symbol z hz sigma hs K k]
  exact hbound K hK k hk

variable {N : ℕ} {T : Type*} [Fintype T]
/-- Actual ordered MSA DCF equals the finite tail field outside contact. -/
theorem actual_c_exterior_eq_tail_field (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hs : ∀ i, 0 < sigma i)
    (K D G : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (hr : IsRoot z rho sigma K D G) (i j : Fin N) (r : ℝ)
    (houter : edgeHi sigma i j < r) :
    orderedRadialCorrelation z rho sigma K D G i j r =
      tailField z (edgeHi sigma i j) (fun u => K u i j) r := by
  simpa only [tailField] using actual_c_exterior_eq_tail_sum z hz rho sigma hs K D G hK hr i j r houter

/-- The actual c h spatial split written using the genuine tail field. -/
theorem actual_pair_product_split_field (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hs : ∀ i, 0 < sigma i)
    (K D G : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (hr : IsRoot z rho sigma K D G) (i j : Fin N) (r : ℝ)
    (hr0 : 0 < r) (hcontact : r ≠ edgeHi sigma i j) :
    orderedRadialCorrelation z rho sigma K D G i j r * nonlinearH z rho sigma D G i j r =
      orderedRadialCorrelation z rho sigma K D G i j r * coreValue (edgeHi sigma i j) r +
        tailField z (edgeHi sigma i j) (fun u => K u i j) r * nonlinearH z rho sigma D G i j r := by
  simpa only [tailField] using actual_pair_product_split z hz rho sigma hs K D G hK hr i j r hr0 hcontact

end FMSA.Convergence.TracerTailSpectralBound
/-- info: 'FMSA.Convergence.TracerTailSpectralBound.tail_radius_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerTailSpectralBound.tail_radius_integrable
/-- info: 'FMSA.Convergence.TracerTailSpectralBound.tail_odd_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerTailSpectralBound.tail_odd_integrable
/-- info: 'FMSA.Convergence.TracerTailSpectralBound.tail_odd_memLp_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerTailSpectralBound.tail_odd_memLp_two
/-- info: 'FMSA.Convergence.TracerTailSpectralBound.tail_field_odd_L1_L2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerTailSpectralBound.tail_field_odd_L1_L2
/-- info: 'FMSA.Convergence.TracerTailSpectralBound.tail_field_radial_fourier_eq_symbol' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerTailSpectralBound.tail_field_radial_fourier_eq_symbol
/-- info: 'FMSA.Convergence.TracerTailSpectralBound.tail_field_square_dominated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerTailSpectralBound.tail_field_square_dominated
/-- info: 'FMSA.Convergence.TracerTailSpectralBound.actual_c_exterior_eq_tail_field' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerTailSpectralBound.actual_c_exterior_eq_tail_field
/-- info: 'FMSA.Convergence.TracerTailSpectralBound.actual_pair_product_split_field' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerTailSpectralBound.actual_pair_product_split_field
