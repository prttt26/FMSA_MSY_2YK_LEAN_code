import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearKernel
import LeanCode.YukawaOZMix.MSAMultiTailMixtureHSPairReference

/-! The actual nonlinear mixture excess source: its nondecaying background
is canceled by proved integral moments, rather than assumed at a BH root. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

def nonlinearTailAmplitude (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (u : ι) (i j : Fin N) : ℝ :=
  W z ρ Dt G u i j+C z ρ σ Dt G u i j*exp (z u*σ i)

theorem nonlinearRecenteredQ_tail (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (i j : Fin N) (t : ℝ) (ht : σ i ≤ t) :
    nonlinearRecenteredQ z ρ σ Dt G i j t =
      ∑ u, nonlinearTailAmplitude z ρ σ Dt G u i j*exp (-z u*t) := by
  simp only [nonlinearRecenteredQ, min_eq_right ht, max_eq_left ht, sub_self,
    mul_zero, zero_pow (by norm_num : 2 ≠ 0), add_zero, zero_add]
  apply Finset.sum_congr rfl
  intro u _
  have he : exp (-z u*(t-σ i))=exp (z u*σ i)*exp (-z u*t) := by
    rw [← exp_add]; congr 1; ring
  rw [he]
  unfold nonlinearTailAmplitude
  ring

theorem nonlinearTailAmplitude_eq_Dt (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (u : ι) (i j : Fin N) :
    nonlinearTailAmplitude z ρ σ Dt G u i j=Dt u i j*exp (z u*σ i) := by
  have hc := cancellation_star (z u) ρ σ (G u) (Dt u) i j
  have he : exp (-z u*σ i)*exp (z u*σ i)=1 := by rw [← exp_add]; simp
  change Dt u i j-C z ρ σ Dt G u i j=exp (-z u*σ i)*W z ρ Dt G u i j at hc
  unfold nonlinearTailAmplitude
  linear_combination -(exp (z u*σ i))*hc-W z ρ Dt G u i j*he

theorem nonlinear_exp_affine_integrable (z r R : ℝ) (hz : 0 < z) (hr : 0 ≤ r) :
    IntegrableOn (fun t => exp (-z*t)*(r-t+R)) (Ioi r) := by
  have he : (fun t => exp (-z*t)*(r-t+R)) =
      fun t => (r+R)*exp (-z*t)-t*exp (-z*t) := by funext t; ring
  rw [he]
  exact ((integrableOn_exp_mul_Ioi (by linarith : -z < 0) r).const_mul _).sub
    ((FMSA.ExactMSA.integrableOn_Ioi_id_mul_exp_neg hz).mono_set (Ioi_subset_Ioi hr))

theorem nonlinear_exp_affine_integral (z r R : ℝ) (hz : 0 < z) (hr : 0 ≤ r) :
    (∫ t in Ioi r, exp (-z*t)*(r-t+R))=exp (-z*r)*(R/z-1/z^2) := by
  have he : (fun t => exp (-z*t)*(r-t+R)) =
      fun t => (r+R)*exp (-z*t)-t*exp (-z*t) := by funext t; ring
  rw [he, integral_sub ((integrableOn_exp_mul_Ioi (by linarith : -z < 0) r).const_mul _)
    ((FMSA.ExactMSA.integrableOn_Ioi_id_mul_exp_neg hz).mono_set (Ioi_subset_Ioi hr)),
    integral_const_mul, integral_exp_mul_Ioi (by linarith : -z < 0),
    FMSA.ExactMSA.MultiTail.exp_first_Ioi z r hz]
  ring

theorem nonlinearQ_background_convolution (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i)
    (i j : Fin N) (r R : ℝ) (hr : 0 ≤ r) (hri : σ i ≤ r) :
    (∫ t in (0 : ℝ)..r, nonlinearRecenteredQ z ρ σ Dt G i j t*(r-t+R)) =
      (r+R)*nonlinearQMoment0 z ρ σ Dt G i j-nonlinearQMoment1 z ρ σ Dt G i j-
        ∑ u, nonlinearTailAmplitude z ρ σ Dt G u i j*exp (-z u*r)*(R/z u-1/(z u)^2) := by
  have hi0 := nonlinearRecenteredQ_integrable z ρ σ Dt G hz hσ i j
  have hi1 := nonlinearRecenteredQ_first_integrable z ρ σ Dt G hz hσ i j
  have hf : (fun t => nonlinearRecenteredQ z ρ σ Dt G i j t*(r-t+R)) =
      fun t => (r+R)*nonlinearRecenteredQ z ρ σ Dt G i j t-
        t*nonlinearRecenteredQ z ρ σ Dt G i j t := by funext t; ring
  have hwhole : IntegrableOn (fun t => nonlinearRecenteredQ z ρ σ Dt G i j t*(r-t+R)) (Ioi 0) := by
    rw [hf]; exact (hi0.const_mul _).sub hi1
  have hfull : (∫ t in Ioi (0 : ℝ), nonlinearRecenteredQ z ρ σ Dt G i j t*(r-t+R)) =
      (r+R)*nonlinearQMoment0 z ρ σ Dt G i j-nonlinearQMoment1 z ρ σ Dt G i j := by
    rw [hf, integral_sub (hi0.const_mul _) hi1, integral_const_mul,
      ← nonlinearQMoment0_eq_integral z ρ σ Dt G hz hσ,
      ← nonlinearQMoment1_eq_integral z ρ σ Dt G hz hσ]
  have htail : (∫ t in Ioi r, nonlinearRecenteredQ z ρ σ Dt G i j t*(r-t+R)) =
      ∑ u, nonlinearTailAmplitude z ρ σ Dt G u i j*exp (-z u*r)*(R/z u-1/(z u)^2) := by
    have he : (∫ t in Ioi r, nonlinearRecenteredQ z ρ σ Dt G i j t*(r-t+R)) =
        ∫ t in Ioi r, ∑ u, nonlinearTailAmplitude z ρ σ Dt G u i j*(exp (-z u*t)*(r-t+R)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [nonlinearRecenteredQ_tail z ρ σ Dt G i j t (hri.trans ht.le), Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro u _
      ring
    rw [he, integral_finsetSum _ (fun u _ => (nonlinear_exp_affine_integrable (z u) r R (hz u) hr).const_mul _)]
    apply Finset.sum_congr rfl
    intro u _
    rw [integral_const_mul, nonlinear_exp_affine_integral (z u) r R (hz u) hr]
    ring
  have hb : IntervalIntegrable (fun t => nonlinearRecenteredQ z ρ σ Dt G i j t*(r-t+R)) volume 0 r :=
    ((nonlinearRecenteredQ_continuous z ρ σ Dt G i j).mul (by fun_prop)).intervalIntegrable 0 r
  have he := intervalIntegral.integral_interval_add_Ioi' hb (hwhole.mono_set (Ioi_subset_Ioi hr))
  rw [hfull, htail] at he
  linear_combination he

def nonlinearGSource (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (r : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of (fun i j => (amplitudeA z ρ σ Dt G j*r+amplitudeQp z ρ σ Dt G i j+
    ∑ u, z u*C z ρ σ Dt G u i j*exp (-z u*r))/(2*π))

theorem nonlinearGSource_continuous (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N) :
    Continuous (nonlinearGSource z ρ σ Dt G) := by unfold nonlinearGSource; fun_prop

def nonlinearExcessSource (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (r : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of (fun i j => nonlinearGSource z ρ σ Dt G r i j-(r+edgeHi σ i j)+
    ∑ m, ρ m*∫ t in (0 : ℝ)..r, nonlinearRecenteredQ z ρ σ Dt G m j (r-t)*(t+edgeHi σ i m))

theorem nonlinearExcessSource_continuous (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N) :
    Continuous (nonlinearExcessSource z ρ σ Dt G) := by
  apply continuous_matrix
  intro i j
  simp only [nonlinearExcessSource, Matrix.of_apply]
  apply Continuous.add
  · exact ((nonlinearGSource_continuous z ρ σ Dt G).matrix_elem i j).sub (by fun_prop)
  · apply continuous_finsetSum
    intro m _
    apply Continuous.const_mul
    have hc : Continuous (Function.uncurry (fun r t : ℝ =>
      nonlinearRecenteredQ z ρ σ Dt G m j (r-t)*(t+edgeHi σ i m))) := by
      exact ((nonlinearRecenteredQ_continuous z ρ σ Dt G m j).comp
        (continuous_fst.sub continuous_snd)).mul (continuous_snd.add_const _)
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hc continuous_id

def nonlinearExcessTail (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (u : ι) (i j : Fin N) : ℝ :=
  z u*C z ρ σ Dt G u i j/(2*π)-
    ∑ m, ρ m*nonlinearTailAmplitude z ρ σ Dt G u m j*(edgeHi σ i m/z u-1/(z u)^2)

theorem nonlinearExcessSource_tail (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i)
    (hv : vacMix ρ σ ≠ 0) (r : ℝ) (hr : rdfHSSupportCeiling σ ≤ r) (i j : Fin N) :
    nonlinearExcessSource z ρ σ Dt G r i j =
      ∑ u, nonlinearExcessTail z ρ σ Dt G u i j*exp (-z u*r) := by
  have hr0 := (rdfHSSupportCeiling_nonneg σ).trans hr
  have hri (m : Fin N) : σ m ≤ r := (le_abs_self _).trans
    ((Finset.single_le_sum (f := fun m : Fin N => |σ m|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ m)).trans hr)
  have hconv (m : Fin N) : (∫ t in (0 : ℝ)..r,
      nonlinearRecenteredQ z ρ σ Dt G m j (r-t)*(t+edgeHi σ i m)) =
      (r+edgeHi σ i m)*nonlinearQMoment0 z ρ σ Dt G m j-nonlinearQMoment1 z ρ σ Dt G m j-
        ∑ u, nonlinearTailAmplitude z ρ σ Dt G u m j*exp (-z u*r)*(edgeHi σ i m/z u-1/(z u)^2) := by
    have he : (∫ t in (0 : ℝ)..r, nonlinearRecenteredQ z ρ σ Dt G m j (r-t)*(t+edgeHi σ i m)) =
        ∫ t in (0 : ℝ)..r, nonlinearRecenteredQ z ρ σ Dt G m j t*(r-t+edgeHi σ i m) := by
      calc
        _ = ∫ t in (0 : ℝ)..r, (fun v => nonlinearRecenteredQ z ρ σ Dt G m j v*(r-v+edgeHi σ i m)) (r-t) := by
          apply intervalIntegral.integral_congr
          intro t _
          dsimp only
          congr 1
          ring
        _ = _ := by
          simpa using intervalIntegral.integral_comp_sub_left
            (f := fun v => nonlinearRecenteredQ z ρ σ Dt G m j v*(r-v+edgeHi σ i m))
            (a := (0 : ℝ)) (b := r) r
    rw [he]
    exact nonlinearQ_background_convolution z ρ σ Dt G hz hσ m j r _ hr0 (hri m)
  have hmass := nonlinear_background_mass_normalization z ρ σ Dt G (fun u => (hz u).ne') hv j
  have hcontact := nonlinear_background_contact_normalization z ρ σ Dt G (fun u => (hz u).ne') hv i j
  have hpoly : nonlinearGSource z ρ σ Dt G r i j-(r+edgeHi σ i j)+
      (∑ m, ρ m*((r+edgeHi σ i m)*nonlinearQMoment0 z ρ σ Dt G m j-
        nonlinearQMoment1 z ρ σ Dt G m j)) =
        ∑ u, z u*C z ρ σ Dt G u i j*exp (-z u*r)/(2*π) := by
    have he : (∑ m, ρ m*((r+edgeHi σ i m)*nonlinearQMoment0 z ρ σ Dt G m j-
        nonlinearQMoment1 z ρ σ Dt G m j)) =
        r*(∑ m, ρ m*nonlinearQMoment0 z ρ σ Dt G m j)-
          (∑ m, ρ m*(nonlinearQMoment1 z ρ σ Dt G m j-
            edgeHi σ i m*nonlinearQMoment0 z ρ σ Dt G m j)) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro m _
      ring
    rw [he]
    simp only [nonlinearGSource, Matrix.of_apply]
    rw [show (∑ m, ρ m*nonlinearQMoment0 z ρ σ Dt G m j) =
      1-amplitudeA z ρ σ Dt G j/(2*π) from by linarith [hmass],
      show (∑ m, ρ m*(nonlinearQMoment1 z ρ σ Dt G m j-
        edgeHi σ i m*nonlinearQMoment0 z ρ σ Dt G m j)) =
        amplitudeQp z ρ σ Dt G i j/(2*π)-edgeHi σ i j from by linarith [hcontact]]
    rw [← Finset.sum_div]
    ring
  simp only [nonlinearExcessSource, Matrix.of_apply, hconv]
  have he : (∑ m, ρ m*((r+edgeHi σ i m)*nonlinearQMoment0 z ρ σ Dt G m j-
      nonlinearQMoment1 z ρ σ Dt G m j-
      ∑ u, nonlinearTailAmplitude z ρ σ Dt G u m j*exp (-z u*r)*(edgeHi σ i m/z u-1/(z u)^2))) =
      (∑ m, ρ m*((r+edgeHi σ i m)*nonlinearQMoment0 z ρ σ Dt G m j-
        nonlinearQMoment1 z ρ σ Dt G m j))-
        (∑ m, ∑ u, ρ m*(nonlinearTailAmplitude z ρ σ Dt G u m j*exp (-z u*r)*
          (edgeHi σ i m/z u-1/(z u)^2))) := by
    simp only [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
  rw [he, ← add_sub_assoc, hpoly, Finset.sum_comm, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro u _
  unfold nonlinearExcessTail
  rw [sub_mul, Finset.sum_mul]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro m _
    ring

theorem nonlinearExcessSource_weighted_bounded (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i)
    (hv : vacMix ρ σ ≠ 0) (δ : ℝ) (hδz : ∀ u, δ ≤ z u) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r, 0 ≤ r →
      exp (δ*r)*FMSA.matrixAbsSum (nonlinearExcessSource z ρ σ Dt G r) ≤ B := by
  let f := fun r => exp (δ*r)*FMSA.matrixAbsSum (nonlinearExcessSource z ρ σ Dt G r)
  have hc : Continuous f := (by fun_prop : Continuous (fun r : ℝ => exp (δ*r))).mul
    (FMSA.matrixAbsSum_continuous _ (nonlinearExcessSource_continuous z ρ σ Dt G))
  obtain ⟨x, _, hm⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0 : ℝ) (rdfHSSupportCeiling σ)).Nonempty from
      ⟨0, ⟨le_rfl, rdfHSSupportCeiling_nonneg σ⟩⟩) hc.continuousOn
  let b := ∑ i, ∑ j, ∑ u, |nonlinearExcessTail z ρ σ Dt G u i j|
  refine ⟨f x+b, add_nonneg (mul_nonneg (exp_pos _).le (FMSA.matrixAbsSum_nonneg _))
    (by dsimp [b]; positivity), ?_⟩
  intro r hr
  by_cases h : r ≤ rdfHSSupportCeiling σ
  · exact (hm ⟨hr, h⟩).trans (le_add_of_nonneg_right (by dsimp [b]; positivity))
  · have hb (i j : Fin N) : exp (δ*r)*|nonlinearExcessSource z ρ σ Dt G r i j| ≤
        ∑ u, |nonlinearExcessTail z ρ σ Dt G u i j| := by
      rw [nonlinearExcessSource_tail z ρ σ Dt G hz hσ hv r (not_le.mp h).le i j]
      calc
        _ ≤ exp (δ*r)*∑ u, |nonlinearExcessTail z ρ σ Dt G u i j*exp (-z u*r)| :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (exp_pos _).le
        _ = ∑ u, |nonlinearExcessTail z ρ σ Dt G u i j| * exp ((δ-z u)*r) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro u _
          rw [abs_mul, abs_of_pos (exp_pos _)]
          have he : exp (δ*r)*exp (-z u*r)=exp ((δ-z u)*r) := by
            rw [← exp_add]; congr 1; ring
          linear_combination |nonlinearExcessTail z ρ σ Dt G u i j| * he
        _ ≤ _ := Finset.sum_le_sum (fun u _ => mul_le_of_le_one_right (abs_nonneg _)
          (exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hδz u)) hr)))
    have hh : f r ≤ b := by
      dsimp [f, b]
      simp only [FMSA.matrixAbsSum, Finset.mul_sum]
      exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hb i j))
    exact hh.trans (le_add_of_nonneg_left (mul_nonneg (exp_pos _).le (FMSA.matrixAbsSum_nonneg _)))

end FMSA.ExactMSA.MultiTailMixture
