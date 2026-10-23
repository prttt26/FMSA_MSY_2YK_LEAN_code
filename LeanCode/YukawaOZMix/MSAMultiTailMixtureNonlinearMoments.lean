import LeanCode.YukawaOZMix.MSAMultiTailMixtureHSPairMoments
import LeanCode.YukawaOZMix.MSAMultiTailMixtureSystem

/-! Nonlinear finite-tail mixture normalization. These identities use the
actual BH amplitude dictionary, with no root or reciprocity hypothesis. -/
noncomputable section
open MeasureTheory Set Real
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

def nonlinearM (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N) (j : Fin N) : ℝ :=
  ∑ u, mixM (z u) ρ σ (G u) (Dt u) j

def nonlinearN (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N) (j : Fin N) : ℝ :=
  ∑ u, mixN (z u) ρ σ (G u) (Dt u) j

def nonlinearB (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N) (j : Fin N) : ℝ :=
  2*π/vacMix ρ σ*(σ j/2*(1+nonlinearM z ρ σ Dt G j)+nonlinearN z ρ σ Dt G j)

theorem amplitudeA_moment_dictionary (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (j : Fin N) :
    amplitudeA z ρ σ Dt G j = Qppphys ρ σ j j*(1+nonlinearM z ρ σ Dt G j)+
      (2*π^2*xi2 ρ σ/vacMix ρ σ^2)*nonlinearN z ρ σ Dt G j := by
  simp only [amplitudeA, mixDA, nonlinearM, nonlinearN, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  ring

theorem amplitudeQp_moment_dictionary (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (i j : Fin N) :
    amplitudeQp z ρ σ Dt G i j = Q0phys ρ σ i j*(1+nonlinearM z ρ σ Dt G j)+
      Qppphys ρ σ i i*nonlinearN z ρ σ Dt G j := by
  simp only [amplitudeQp, mixDqp, nonlinearM, nonlinearN, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  ring

/-- The dressed polynomial remains rank two, even off root. -/
theorem amplitudeQp_nonlinear_rank_two (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (i j : Fin N) :
    amplitudeQp z ρ σ Dt G i j = amplitudeA z ρ σ Dt G j*σ i/2+
      nonlinearB z ρ σ Dt G j := by
  rw [amplitudeQp_moment_dictionary, amplitudeA_moment_dictionary]
  unfold nonlinearB Q0phys Qppphys
  ring

def nonlinearRecenteredQ (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (i j : Fin N) (t : ℝ) : ℝ :=
  amplitudeQp z ρ σ Dt G i j*(min t (σ i)-σ i)+
    amplitudeA z ρ σ Dt G j/2*(min t (σ i)-σ i)^2+
    ∑ u, (W z ρ Dt G u i j*exp (-z u*t)+
      C z ρ σ Dt G u i j*exp (-z u*(max t (σ i)-σ i)))

theorem nonlinearRecenteredQ_continuous (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (i j : Fin N) :
    Continuous (nonlinearRecenteredQ z ρ σ Dt G i j) := by
  unfold nonlinearRecenteredQ
  fun_prop

theorem nonlinearRecenteredQ_eq_actual (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (i j : Fin N) (t : ℝ) (ht : 0 ≤ t) :
    nonlinearRecenteredQ z ρ σ Dt G i j t =
      q z σ (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G)
        (W z ρ Dt G) (C z ρ σ Dt G) i j (t+edgeLo σ i j) := by
  have hl : ¬t+edgeLo σ i j < edgeLo σ i j := by linarith
  have he : t+edgeLo σ i j-edgeHi σ i j=t-σ i := by unfold edgeLo edgeHi; ring
  by_cases hh : t ≤ σ i
  · have hr : t+edgeLo σ i j ≤ edgeHi σ i j := by unfold edgeLo edgeHi; linarith
    simp [nonlinearRecenteredQ, q, hl, hr, he, min_eq_left hh, max_eq_right hh]
  · have hr : ¬t+edgeLo σ i j ≤ edgeHi σ i j := by unfold edgeLo edgeHi; linarith
    simp [nonlinearRecenteredQ, q, hl, hr, he, min_eq_right (not_le.mp hh).le,
      max_eq_left (not_le.mp hh).le]

def nonlinearQMoment0 (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (i j : Fin N) : ℝ :=
  -amplitudeQp z ρ σ Dt G i j*σ i^2/2+amplitudeA z ρ σ Dt G j*σ i^3/6+
    ∑ u, (W z ρ Dt G u i j/z u+C z ρ σ Dt G u i j*(σ i+1/z u))

def nonlinearQMoment1 (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (i j : Fin N) : ℝ :=
  -amplitudeQp z ρ σ Dt G i j*σ i^3/6+amplitudeA z ρ σ Dt G j*σ i^4/24+
    ∑ u, (W z ρ Dt G u i j/(z u)^2+
      C z ρ σ Dt G u i j*(σ i^2/2+σ i/z u+1/(z u)^2))

theorem nonlinearM_tail_mass (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, z u ≠ 0) (j : Fin N) :
    (∑ m, ρ m*∑ u, (W z ρ Dt G u m j/z u+
      C z ρ σ Dt G u m j*(σ m+1/z u))) = -nonlinearM z ρ σ Dt G j := by
  simp only [nonlinearM, mixM, ← Finset.sum_neg_distrib, neg_mul, neg_neg, W, C,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro m _
  field_simp [hz u]
  ring

theorem nonlinearN_tail_centered_moment (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, z u ≠ 0) (j : Fin N) :
    (∑ m, ρ m*∑ u, (W z ρ Dt G u m j/(z u)^2+
      C z ρ σ Dt G u m j*(σ m^2/2+σ m/z u+1/(z u)^2)-
      σ m/2*(W z ρ Dt G u m j/z u+C z ρ σ Dt G u m j*(σ m+1/z u)))) =
        nonlinearN z ρ σ Dt G j+σ j/2*nonlinearM z ρ σ Dt G j := by
  simp only [nonlinearN, nonlinearM, mixN, mixM, W, C, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro m _
  field_simp [hz u]
  ring

theorem nonlinearQMoment0_column (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, z u ≠ 0) (j : Fin N) :
    (∑ m, ρ m*nonlinearQMoment0 z ρ σ Dt G m j) =
      -amplitudeA z ρ σ Dt G j*(∑ m, ρ m*σ m^3)/12-
        nonlinearB z ρ σ Dt G j*xi2 ρ σ/2-nonlinearM z ρ σ Dt G j := by
  have hp : (∑ m, ρ m*(-amplitudeQp z ρ σ Dt G m j*σ m^2/2+
      amplitudeA z ρ σ Dt G j*σ m^3/6)) =
      -amplitudeA z ρ σ Dt G j*(∑ m, ρ m*σ m^3)/12-
        nonlinearB z ρ σ Dt G j*xi2 ρ σ/2 := by
    simp_rw [amplitudeQp_nonlinear_rank_two]
    unfold xi2
    rw [Finset.mul_sum, Finset.sum_div, Finset.mul_sum, Finset.sum_div,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m _
    ring
  calc
    _ = (∑ m, ρ m*(-amplitudeQp z ρ σ Dt G m j*σ m^2/2+
        amplitudeA z ρ σ Dt G j*σ m^3/6))+
        ∑ m, ρ m*∑ u, (W z ρ Dt G u m j/z u+
          C z ρ σ Dt G u m j*(σ m+1/z u)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro m _
      unfold nonlinearQMoment0
      ring
    _ = _ := by rw [hp, nonlinearM_tail_mass z ρ σ Dt G hz]; ring

theorem nonlinearQMoment_column_centered (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, z u ≠ 0) (j : Fin N) :
    (∑ m, ρ m*(nonlinearQMoment1 z ρ σ Dt G m j-
      σ m/2*nonlinearQMoment0 z ρ σ Dt G m j)) =
        nonlinearB z ρ σ Dt G j*(∑ m, ρ m*σ m^3)/12+
          nonlinearN z ρ σ Dt G j+σ j/2*nonlinearM z ρ σ Dt G j := by
  have he (m : Fin N) : nonlinearQMoment1 z ρ σ Dt G m j-
      σ m/2*nonlinearQMoment0 z ρ σ Dt G m j =
      nonlinearB z ρ σ Dt G j*σ m^3/12+
        ∑ u, (W z ρ Dt G u m j/(z u)^2+
          C z ρ σ Dt G u m j*(σ m^2/2+σ m/z u+1/(z u)^2)-
          σ m/2*(W z ρ Dt G u m j/z u+C z ρ σ Dt G u m j*(σ m+1/z u))) := by
    unfold nonlinearQMoment0 nonlinearQMoment1
    rw [amplitudeQp_nonlinear_rank_two]
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  simp only [he]
  have hsplit : (∑ m, ρ m*(nonlinearB z ρ σ Dt G j*σ m^3/12+
      ∑ u, (W z ρ Dt G u m j/(z u)^2+
        C z ρ σ Dt G u m j*(σ m^2/2+σ m/z u+1/(z u)^2)-
        σ m/2*(W z ρ Dt G u m j/z u+C z ρ σ Dt G u m j*(σ m+1/z u))))) =
      (∑ m, ρ m*(nonlinearB z ρ σ Dt G j*σ m^3/12))+
        ∑ m, ρ m*∑ u, (W z ρ Dt G u m j/(z u)^2+
          C z ρ σ Dt G u m j*(σ m^2/2+σ m/z u+1/(z u)^2)-
          σ m/2*(W z ρ Dt G u m j/z u+C z ρ σ Dt G u m j*(σ m+1/z u))) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m _
    ring
  rw [hsplit, nonlinearN_tail_centered_moment z ρ σ Dt G hz]
  have hp : (∑ m, ρ m*(nonlinearB z ρ σ Dt G j*σ m^3/12)) =
      nonlinearB z ρ σ Dt G j*(∑ m, ρ m*σ m^3)/12 := by
    rw [Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro m _
    ring
  rw [hp]
  ring

/-- Both far-field polynomial coefficients cancel for every dressed amplitude
pair. Neither a root nor a supplied asymptotic-normalization equation is used. -/
theorem nonlinear_background_mass_normalization (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, z u ≠ 0) (hv : vacMix ρ σ ≠ 0)
    (j : Fin N) :
    1-(∑ m, ρ m*nonlinearQMoment0 z ρ σ Dt G m j) =
      amplitudeA z ρ σ Dt G j/(2*π) := by
  rw [nonlinearQMoment0_column z ρ σ Dt G hz]
  have hm : (∑ m, ρ m*σ m^3)=6*(1-vacMix ρ σ)/π := by
    unfold vacMix etaMix
    field_simp [pi_ne_zero]
    ring
  rw [hm, amplitudeA_moment_dictionary]
  unfold nonlinearB Qppphys
  field_simp [hv, pi_ne_zero]
  ring

theorem nonlinear_background_contact_normalization (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, z u ≠ 0) (hv : vacMix ρ σ ≠ 0)
    (i j : Fin N) :
    edgeHi σ i j+(∑ m, ρ m*(nonlinearQMoment1 z ρ σ Dt G m j-
      edgeHi σ i m*nonlinearQMoment0 z ρ σ Dt G m j)) =
        amplitudeQp z ρ σ Dt G i j/(2*π) := by
  have he : (∑ m, ρ m*(nonlinearQMoment1 z ρ σ Dt G m j-
      edgeHi σ i m*nonlinearQMoment0 z ρ σ Dt G m j)) =
      (∑ m, ρ m*(nonlinearQMoment1 z ρ σ Dt G m j-
        σ m/2*nonlinearQMoment0 z ρ σ Dt G m j))-
      σ i/2*(∑ m, ρ m*nonlinearQMoment0 z ρ σ Dt G m j) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m _
    unfold edgeHi
    ring
  rw [he, nonlinearQMoment_column_centered z ρ σ Dt G hz]
  have hmass := nonlinear_background_mass_normalization z ρ σ Dt G hz hv j
  rw [show (∑ m, ρ m*nonlinearQMoment0 z ρ σ Dt G m j) =
    1-amplitudeA z ρ σ Dt G j/(2*π) from by linarith [hmass]]
  have hm : (∑ m, ρ m*σ m^3)=6*(1-vacMix ρ σ)/π := by
    unfold vacMix etaMix
    field_simp [pi_ne_zero]
    ring
  rw [hm, amplitudeQp_nonlinear_rank_two]
  unfold nonlinearB edgeHi
  field_simp [hv, pi_ne_zero]
  ring

end FMSA.ExactMSA.MultiTailMixture
