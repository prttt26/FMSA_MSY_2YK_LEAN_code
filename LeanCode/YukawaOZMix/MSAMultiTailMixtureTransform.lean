import LeanCode.YukawaOZMix.MSAMultiTailMixtureSystem
import LeanCode.YukawaOZMix.MSAMixtureBaxterLaplace

/-!
# Actual Laplace transform of the finite-tail mixture Baxter function

The transform is an integral of the independently defined real-space function.
No Fourier-factorization or matrix-closure hypothesis is used.
-/

noncomputable section
open MeasureTheory Set Real
open FMSA.ExactMSA.Breakpoint FMSA.ExactMSA.MixLeg3 MSAMixture
open scoped BigOperators

namespace FMSA.ExactMSA.MultiTailMixture

variable {N : ℕ} {ι : Type*} [Fintype ι]

private theorem weighted_integrable (f : ℝ → ℝ) (hf : Integrable f)
    (edge s : ℝ) (hs : 0 ≤ s) (hsupp : ∀ r, r < edge → f r = 0) :
    Integrable (fun r => f r * exp (-s * r)) := by
  let weight : ℝ → ℝ := fun r => if r < edge then 0 else exp (-s * r)
  have hm : AEStronglyMeasurable weight := by
    apply Measurable.aestronglyMeasurable
    exact Measurable.ite measurableSet_Iio measurable_const (by fun_prop)
  have hb : ∀ r, ‖weight r‖ ≤ exp (-s * edge) := by
    intro r
    dsimp [weight]
    split_ifs with h
    · simpa using (exp_pos (-s * edge)).le
    · rw [abs_of_pos (exp_pos _)]
      apply exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_left (le_of_not_gt h) (neg_nonpos.mpr hs)
  have hprod := hf.mul_bdd hm (Filter.Eventually.of_forall hb)
  exact hprod.congr (Filter.Eventually.of_forall (fun r => by
    dsimp [weight]
    by_cases h : r < edge
    · simp [h, hsupp r h]
    · simp [h]))

theorem q_weighted_integrable (z : ι → ℝ) (hz : ∀ t, 0 < z t)
    (σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N)
    (hσ : ∀ i, 0 ≤ σ i) (i j : Fin N) (s : ℝ) (hs : 0 ≤ s) :
    Integrable (fun r => q z σ A qp W C i j r * exp (-s * r)) := by
  exact weighted_integrable _ (q_integrable z hz σ A qp W C hσ i j)
    (edgeLo σ i j) s hs (fun r hr => by simp [q, hr])

private theorem baxterQ_weighted_integrable (z : ℝ) (hz : 0 < z)
    (σ A : Fin N → ℝ) (qp W C : Fin N → Fin N → ℝ)
    (hσ : ∀ i, 0 ≤ σ i) (i j : Fin N) (s : ℝ) (hs : 0 ≤ s) :
    Integrable (fun r => baxterQ z σ A qp W C i j r * exp (-s * r)) := by
  exact weighted_integrable _ (baxterQ_integrable z hz σ A qp W C i j hσ)
    (edgeLo σ i j) s hs (fun r hr => by simp [baxterQ, hr])

/-- Polynomial part plus all tail transforms, with the actual support geometry. -/
theorem Qhat_decomposition (z : ι → ℝ) (σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ)
    (W C : TailMatrix ι N) (s : ℝ) (i j : Fin N) :
    Qhat z σ A qp W C s i j =
      qhatMixRuneq 1 σ qp 0 0 A s i j +
        ∑ t, qhatMixRuneq (z t) σ 0 (W t) (C t) 0 s i j := by
  simp only [Qhat, qhatMixRuneq, Matrix.zero_apply, Pi.zero_apply, mul_zero, zero_div,
    add_zero, zero_add, edgeLo, edgeHi, neg_mul, Finset.mul_sum, Finset.sum_add_distrib,
    mul_add, mul_div_assoc]
  ring

/-- Positive-s transform, including the negative support edge of unequal diameters. -/
theorem laplaceQ_eq_Qhat (z : ι → ℝ) (hz : ∀ t, 0 < z t)
    (σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N)
    (hσ : ∀ i, 0 ≤ σ i) (i j : Fin N) (s : ℝ) (hs : 0 < s) :
    (∫ r : ℝ, q z σ A qp W C i j r * exp (-s * r)) = Qhat z σ A qp W C s i j := by
  simp_rw [q_decomposition, add_mul, Finset.sum_mul]
  rw [integral_add (baxterQ_weighted_integrable 1 one_pos σ A qp _ _ hσ i j s hs.le)
    (integrable_finsetSum _ (fun t _ =>
      baxterQ_weighted_integrable (z t) (hz t) σ _ _ (W t) (C t) hσ i j s hs.le)),
    integral_finsetSum _ (fun t _ =>
      baxterQ_weighted_integrable (z t) (hz t) σ _ _ (W t) (C t) hσ i j s hs.le),
    baxterQ_transform_eq_qhatMixRuneq 1 σ A qp _ _ i j s hs.ne' (by linarith) (hσ i)]
  simp_rw [baxterQ_transform_eq_qhatMixRuneq _ σ _ _ _ _ i j s hs.ne'
    (add_pos hs (hz _)) (hσ i)]
  exact (Qhat_decomposition z σ A qp W C s i j).symm

/-- The exterior coefficient, before inserting BH amplitudes. -/
def exteriorAmplitude (z : ι → ℝ) (σ : Fin N → ℝ) (W C : TailMatrix ι N)
    (u : ι) (i j : Fin N) : ℝ :=
  W u i j * exp (z u * edgeLo σ i j) + C u i j * exp (z u * edgeHi σ i j)

/-- Exterior convolution with all mixed-rate contributions retained. -/
theorem convolution_exterior (z : ι → ℝ) (hz : ∀ t, 0 < z t)
    (σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N)
    (hσ : ∀ i, 0 ≤ σ i) (i j l : Fin N) (r : ℝ) (hr : edgeHi σ i j < r) :
    (∫ t : ℝ, qPrime z σ A qp W C i l (t + r) * q z σ A qp W C j l t) =
      ∑ u, (-z u * exp (-z u * r) * exteriorAmplitude z σ W C u i l) *
        Qhat z σ A qp W C (z u) j l := by
  have hedge : edgeLo σ j l + edgeHi σ i j = edgeHi σ i l := by
    unfold edgeLo edgeHi
    ring
  have hi : edgeLo σ i l ≤ edgeHi σ i l := by
    unfold edgeLo edgeHi
    linarith [hσ i]
  have he (u : ι) (b t : ℝ) :
      exp (-z u * (t + r - b)) = exp (-z u * r) * exp (z u * b) * exp (-z u * t) := by
    rw [← exp_add, ← exp_add]
    congr 1
    ring
  have hstep : (fun t => qPrime z σ A qp W C i l (t + r) * q z σ A qp W C j l t) =
      fun t => ∑ u, (-z u * exp (-z u * r) * exteriorAmplitude z σ W C u i l) *
        (q z σ A qp W C j l t * exp (-z u * t)) := by
    funext t
    by_cases ht : t < edgeLo σ j l
    · simp [q, ht]
    · have htj := le_of_not_gt ht
      have h1 : ¬ (t + r < edgeLo σ i l) := by linarith
      have h2 : ¬ (t + r ≤ edgeHi σ i l) := by linarith
      simp only [qPrime, if_neg h1, if_neg h2, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro u _
      rw [he u (edgeLo σ i l) t, he u (edgeHi σ i l) t]
      unfold exteriorAmplitude
      ring
  rw [hstep, integral_finsetSum _ (fun u _ =>
    (q_weighted_integrable z hz σ A qp W C hσ j l (z u) (hz u).le).const_mul _)]
  apply Finset.sum_congr rfl
  intro u _
  rw [integral_const_mul, laplaceQ_eq_Qhat z hz σ A qp W C hσ j l (z u) (hz u)]

/-- Exterior numerator of the independently defined real-space correlation. -/
theorem correlation_numerator_exterior (z : ι → ℝ) (hz : ∀ t, 0 < z t)
    (ρ σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N)
    (hσ : ∀ i, 0 ≤ σ i) (i j : Fin N) (r : ℝ) (hr : edgeHi σ i j < r) :
    -qPrime z σ A qp W C i j r +
      ∑ l, ρ l * ∫ t : ℝ, qPrime z σ A qp W C i l (t + r) * q z σ A qp W C j l t =
    ∑ u, z u * exp (-z u * r) *
      (exteriorAmplitude z σ W C u i j -
        ∑ l, ρ l * exteriorAmplitude z σ W C u i l * Qhat z σ A qp W C (z u) j l) := by
  have hij : edgeLo σ i j ≤ edgeHi σ i j := by
    unfold edgeLo edgeHi
    linarith [hσ i]
  have h1 : ¬ (r < edgeLo σ i j) := by linarith
  have h2 : ¬ (r ≤ edgeHi σ i j) := by linarith
  have he (u : ι) (b : ℝ) : exp (-z u * (r - b)) = exp (-z u * r) * exp (z u * b) := by
    rw [← exp_add]
    congr 1
    ring
  have hq : -qPrime z σ A qp W C i j r =
      ∑ u, z u * exp (-z u * r) * exteriorAmplitude z σ W C u i j := by
    simp only [qPrime, if_neg h1, if_neg h2, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro u _
    rw [he u (edgeLo σ i j), he u (edgeHi σ i j)]
    unfold exteriorAmplitude
    ring
  rw [hq]
  simp_rw [convolution_exterior z hz σ A qp W C hσ i j _ r hr, Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  rw [mul_sub, Finset.mul_sum]
  have hp : (∑ l, ρ l * ((-z u * exp (-z u * r) * exteriorAmplitude z σ W C u i l) *
      Qhat z σ A qp W C (z u) j l)) =
      -(∑ l, z u * exp (-z u * r) *
        (ρ l * exteriorAmplitude z σ W C u i l * Qhat z σ A qp W C (z u) j l)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [hp]
  ring

theorem firstLHS_eq (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (u : ι) (i j : Fin N) :
    firstLHS z ρ σ Dt G u i j = Dt u i j -
      ∑ l, ρ l * exp (z u * edgeLo σ j l) * Dt u i l * dressedQhat z ρ σ Dt G (z u) j l := by
  simp only [firstLHS, mul_sub, Finset.sum_sub_distrib]
  congr 1
  · simp
  · apply Finset.sum_congr rfl
    intro l _
    ring

/-- The first BH equations recover the prescribed sum of exterior Yukawa tails,
for arbitrary finite species/tail counts and unequal nonnegative diameters. -/
theorem correlation_exterior_of_root (z : ι → ℝ) (hz : ∀ t, 0 < z t)
    (ρ σ : Fin N → ℝ) (K Dt G : TailMatrix ι N) (hσ : ∀ i, 0 ≤ σ i)
    (hroot : IsRoot z ρ σ K Dt G) (i j : Fin N) (r : ℝ) (hr : edgeHi σ i j < r) :
    correlation z ρ σ (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G)
      (W z ρ Dt G) (C z ρ σ Dt G) i j r =
        ∑ u, K u i j * exp (-z u * (r - edgeHi σ i j)) / r := by
  have hr0 : r ≠ 0 := by
    have hR : 0 ≤ edgeHi σ i j := by unfold edgeHi; linarith [hσ i, hσ j]
    exact (lt_of_le_of_lt hR hr).ne'
  have hS (u : ι) (a b : Fin N) :
      exteriorAmplitude z σ (W z ρ Dt G) (C z ρ σ Dt G) u a b =
        Dt u a b * exp (z u * edgeHi σ a b) :=
    W_add_C_exp z ρ σ Dt G u a b
  have hedge (u : ι) (l : Fin N) : exp (z u * edgeHi σ i l) =
      exp (z u * edgeHi σ i j) * exp (z u * edgeLo σ j l) := by
    rw [← exp_add]
    congr 1
    unfold edgeHi edgeLo
    ring
  have hb (u : ι) :
      exteriorAmplitude z σ (W z ρ Dt G) (C z ρ σ Dt G) u i j -
        ∑ l, ρ l * exteriorAmplitude z σ (W z ρ Dt G) (C z ρ σ Dt G) u i l *
          dressedQhat z ρ σ Dt G (z u) j l =
      exp (z u * edgeHi σ i j) * firstLHS z ρ σ Dt G u i j := by
    simp_rw [hS]
    rw [firstLHS_eq, mul_sub, Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro l _
      rw [hedge u l]
      ring
  unfold correlation
  rw [correlation_numerator_exterior z hz ρ σ _ _ _ _ hσ i j r hr]
  change (∑ u, z u * exp (-z u * r) *
    (exteriorAmplitude z σ (W z ρ Dt G) (C z ρ σ Dt G) u i j -
      ∑ l, ρ l * exteriorAmplitude z σ (W z ρ Dt G) (C z ρ σ Dt G) u i l *
        dressedQhat z ρ σ Dt G (z u) j l)) / (2 * π * r) = _
  simp_rw [hb, hroot.1]
  have hn : (∑ u, z u * exp (-z u * r) *
      (exp (z u * edgeHi σ i j) * (2 * π * K u i j / z u))) =
      2 * π * ∑ u, K u i j * exp (-z u * (r - edgeHi σ i j)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    have he : exp (-z u * (r - edgeHi σ i j)) = exp (-z u * r) * exp (z u * edgeHi σ i j) := by
      rw [← exp_add]
      congr 1
      ring
    rw [he]
    field_simp [(hz u).ne']
  rw [hn, ← Finset.sum_div]
  field_simp [Real.pi_ne_zero, hr0]
  apply Finset.sum_congr rfl
  intro u _
  congr 2
  ring

end FMSA.ExactMSA.MultiTailMixture
