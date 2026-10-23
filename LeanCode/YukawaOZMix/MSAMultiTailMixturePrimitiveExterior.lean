import LeanCode.YukawaOZMix.MSAMultiTailMixturePrimitive

/-! Actual exterior Baxter primitive. Symmetric physical pair strengths give
its exterior reciprocity/evenness; the inner-core reciprocity is not assumed. -/
noncomputable section
open MeasureTheory Set Real
open FMSA.ExactMSA.Breakpoint MSAMixture
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

theorem q_convolution_exterior (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N)
    (hσ : ∀ i, 0 ≤ σ i) (i j l : Fin N) (r : ℝ) (hr : edgeHi σ i j < r) :
    (∫ t : ℝ, q z σ A qp W C i l (t + r) * q z σ A qp W C j l t) =
      ∑ u, (exp (-z u * r) * exteriorAmplitude z σ W C u i l) *
        Qhat z σ A qp W C (z u) j l := by
  have hedge : edgeLo σ j l + edgeHi σ i j = edgeHi σ i l := by
    unfold edgeLo edgeHi
    ring
  have hi : edgeLo σ i l ≤ edgeHi σ i l := by unfold edgeLo edgeHi; linarith [hσ i]
  have he (u : ι) (b t : ℝ) :
      exp (-z u * (t + r - b)) = exp (-z u * r) * exp (z u * b) * exp (-z u * t) := by
    rw [← exp_add, ← exp_add]
    congr 1
    ring
  have hstep : (fun t => q z σ A qp W C i l (t + r) * q z σ A qp W C j l t) =
      fun t => ∑ u, (exp (-z u * r) * exteriorAmplitude z σ W C u i l) *
        (q z σ A qp W C j l t * exp (-z u * t)) := by
    funext t
    by_cases ht : t < edgeLo σ j l
    · simp [q, ht]
    · have htj := le_of_not_gt ht
      have h1 : ¬ (t + r < edgeLo σ i l) := by linarith
      have h2 : ¬ (t + r ≤ edgeHi σ i l) := by linarith
      rw [show q z σ A qp W C i l (t+r) =
        ∑ u, (W u i l * exp (-z u * (t+r-edgeLo σ i l)) +
          C u i l * exp (-z u * (t+r-edgeHi σ i l))) by simp only [q, if_neg h1, if_neg h2],
        Finset.sum_mul]
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

theorem baxterPrimitive_exterior_of_root (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (K Dt G : TailMatrix ι N) (hσ : ∀ i, 0 ≤ σ i)
    (hroot : IsRoot z ρ σ K Dt G) (i j : Fin N) (r : ℝ) (hr : edgeHi σ i j < r) :
    baxterPrimitive z ρ σ (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G)
      (W z ρ Dt G) (C z ρ σ Dt G) i j r =
      ((∑ u, 2 * π * K u i j / z u * exp (-z u * (r - edgeHi σ i j)) : ℝ) : ℂ) := by
  let A := amplitudeA z ρ σ Dt G
  let qp := amplitudeQp z ρ σ Dt G
  let V := W z ρ Dt G
  let T := C z ρ σ Dt G
  have hl : ¬ (r < edgeLo σ i j) := by unfold edgeLo edgeHi at *; linarith [hσ i]
  have hh : ¬ (r ≤ edgeHi σ i j) := not_le_of_gt hr
  have href : q z σ A qp V T j i (-r) = 0 := by
    have he : -r < edgeLo σ j i := by unfold edgeLo edgeHi at *; linarith [hσ i]
    simp only [q, if_pos he]
  have hp : baxterPrimitive z ρ σ A qp V T i j r =
      ((q z σ A qp V T i j r - ∑ l, ρ l *
        ∫ t : ℝ, q z σ A qp V T i l (t+r) * q z σ A qp V T j l t : ℝ) : ℂ) := by
    unfold baxterPrimitive
    rw [href]
    simp only [Complex.ofReal_zero, add_zero]
    simp_rw [qCrossCorr_eq_ordered, ← Complex.ofReal_mul, integral_complex_ofReal]
    push_cast
    rfl
  rw [hp]
  congr 1
  have hs (u : ι) (a b : Fin N) : exteriorAmplitude z σ V T u a b =
      Dt u a b * exp (z u * edgeHi σ a b) := W_add_C_exp z ρ σ Dt G u a b
  have he (u : ι) (l : Fin N) : exp (z u * edgeHi σ i l) =
      exp (z u * edgeHi σ i j) * exp (z u * edgeLo σ j l) := by
    rw [← exp_add]
    congr 1
    unfold edgeHi edgeLo
    ring
  have hq : q z σ A qp V T i j r =
      ∑ u, exp (-z u * r) * exteriorAmplitude z σ V T u i j := by
    simp only [q, if_neg hl, if_neg hh]
    apply Finset.sum_congr rfl
    intro u _
    have hx (b : ℝ) : exp (-z u * (r-b)) = exp (-z u*r) * exp (z u*b) := by
      rw [← exp_add]
      congr 1
      ring
    rw [hx, hx]
    unfold exteriorAmplitude
    ring
  rw [hq]
  simp_rw [q_convolution_exterior z hz σ A qp V T hσ i j _ r hr, Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro u _
  have hb : exteriorAmplitude z σ V T u i j -
      ∑ l, ρ l * exteriorAmplitude z σ V T u i l * dressedQhat z ρ σ Dt G (z u) j l =
      exp (z u * edgeHi σ i j) * firstLHS z ρ σ Dt G u i j := by
    simp_rw [hs]
    rw [firstLHS_eq, mul_sub, Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro l _
      rw [he u l]
      ring
  have hx : exp (-z u * (r-edgeHi σ i j)) =
      exp (-z u*r) * exp (z u*edgeHi σ i j) := by
    rw [← exp_add]
    congr 1
    ring
  rw [hx]
  have hc : (∑ l, ρ l * ((exp (-z u * r) * exteriorAmplitude z σ V T u i l) *
      Qhat z σ A qp V T (z u) j l)) =
      exp (-z u*r) * ∑ l, ρ l * exteriorAmplitude z σ V T u i l *
        dressedQhat z ρ σ Dt G (z u) j l := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    change ρ l * (exp (-z u*r) * exteriorAmplitude z σ V T u i l *
      dressedQhat z ρ σ Dt G (z u) j l) = _
    ring
  rw [hc, ← mul_sub, hb, hroot.1]
  ring

/-- Physical symmetric pair strengths give actual exterior reciprocity.
No ordering of the two diameters is required outside contact. -/
theorem baxterPrimitive_exterior_reciprocity (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (K Dt G : TailMatrix ι N) (hσ : ∀ i, 0 ≤ σ i)
    (hroot : IsRoot z ρ σ K Dt G) (hK : ∀ u i j, K u i j = K u j i)
    (i j : Fin N) (r : ℝ) (hr : edgeHi σ i j < r) :
    baxterPrimitive z ρ σ (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G)
      (W z ρ Dt G) (C z ρ σ Dt G) i j r =
    baxterPrimitive z ρ σ (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G)
      (W z ρ Dt G) (C z ρ σ Dt G) j i r := by
  have he : edgeHi σ j i = edgeHi σ i j := by unfold edgeHi; ring
  rw [baxterPrimitive_exterior_of_root z hz ρ σ K Dt G hσ hroot i j r hr,
    baxterPrimitive_exterior_of_root z hz ρ σ K Dt G hσ hroot j i r (by rwa [he])]
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  rw [hK u i j, he]

/-- With symmetric physical strengths, the actual primitive is even outside
contact on both sides of the real line. -/
theorem baxterPrimitive_even_exterior (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (K Dt G : TailMatrix ι N) (hσ : ∀ i, 0 ≤ σ i)
    (hroot : IsRoot z ρ σ K Dt G) (hK : ∀ u i j, K u i j = K u j i)
    (i j : Fin N) (r : ℝ) (hr : edgeHi σ i j < |r|) :
    baxterPrimitive z ρ σ (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G)
      (W z ρ Dt G) (C z ρ σ Dt G) i j (-r) =
    baxterPrimitive z ρ σ (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G)
      (W z ρ Dt G) (C z ρ σ Dt G) i j r := by
  by_cases h : 0 ≤ r
  · rw [abs_of_nonneg h] at hr
    rw [baxterPrimitive_reflection]
    exact (baxterPrimitive_exterior_reciprocity z hz ρ σ K Dt G hσ hroot hK i j r hr).symm
  · have hn : r < 0 := lt_of_not_ge h
    rw [abs_of_neg hn] at hr
    rw [baxterPrimitive_exterior_reciprocity z hz ρ σ K Dt G hσ hroot hK i j (-r) hr,
      baxterPrimitive_reflection]

/-- The remaining species-antisymmetric part is confined to the finite core.
Thus exterior reciprocity has been discharged, not assumed globally. -/
theorem baxterPrimitive_asym_support_core (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (K Dt G : TailMatrix ι N) (hσ : ∀ i, 0 ≤ σ i)
    (hroot : IsRoot z ρ σ K Dt G) (hK : ∀ u i j, K u i j = K u j i) (i j : Fin N) :
    Function.support (fun r : ℝ =>
      baxterPrimitive z ρ σ (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G)
        (W z ρ Dt G) (C z ρ σ Dt G) i j r -
      baxterPrimitive z ρ σ (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G)
        (W z ρ Dt G) (C z ρ σ Dt G) j i r) ⊆ Icc (-edgeHi σ i j) (edgeHi σ i j) := by
  intro r hr
  by_contra hmem
  have ha : edgeHi σ i j < |r| := by
    by_cases h : 0 ≤ r
    · rw [abs_of_nonneg h]
      have hR : 0 ≤ edgeHi σ i j := by unfold edgeHi; linarith [hσ i, hσ j]
      have hl : -edgeHi σ i j ≤ r := by linarith
      exact lt_of_not_ge (fun hh => hmem ⟨hl, hh⟩)
    · rw [abs_of_neg (lt_of_not_ge h)]
      have hR : 0 ≤ edgeHi σ i j := by unfold edgeHi; linarith [hσ i, hσ j]
      have hu : r ≤ edgeHi σ i j := by linarith
      have hl : r < -edgeHi σ i j := lt_of_not_ge (fun hh => hmem ⟨hh, hu⟩)
      linarith
  have he := baxterPrimitive_even_exterior z hz ρ σ K Dt G hσ hroot hK i j r ha
  rw [baxterPrimitive_reflection] at he
  rw [Function.mem_support] at hr
  exact hr (sub_eq_zero.mpr he.symm)

/-- Actual spectral reciprocity reduces to an integral over the finite core.
The exterior contribution is discharged from the actual BH closure. -/
theorem spectralBaxterC_asym_eq_core_integral (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (K Dt G : TailMatrix ι N) (hσ : ∀ i, 0 ≤ σ i)
    (hroot : IsRoot z ρ σ K Dt G) (hK : ∀ u i j, K u i j = K u j i)
    (k : ℝ) (i j : Fin N) :
    spectralBaxterC z ρ σ (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G)
      (W z ρ Dt G) (C z ρ σ Dt G) k i j -
    spectralBaxterC z ρ σ (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G)
      (W z ρ Dt G) (C z ρ σ Dt G) k j i =
    ∫ r in Icc (-edgeHi σ i j) (edgeHi σ i j),
      (baxterPrimitive z ρ σ (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G)
        (W z ρ Dt G) (C z ρ σ Dt G) i j r -
      baxterPrimitive z ρ σ (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G)
        (W z ρ Dt G) (C z ρ σ Dt G) j i r) * Complex.exp (-(Complex.I * k) * r) := by
  let A := amplitudeA z ρ σ Dt G
  let qp := amplitudeQp z ρ σ Dt G
  let V := W z ρ Dt G
  let T := C z ρ σ Dt G
  have hf := baxterPrimitive_axis_weighted_integrable z hz ρ σ A qp V T hσ k i j
  have hg := baxterPrimitive_axis_weighted_integrable z hz ρ σ A qp V T hσ k j i
  have hs := baxterPrimitive_asym_support_core z hz ρ σ K Dt G hσ hroot hK i j
  have hzero : ∀ r, r ∉ Icc (-edgeHi σ i j) (edgeHi σ i j) →
      (baxterPrimitive z ρ σ A qp V T i j r - baxterPrimitive z ρ σ A qp V T j i r) *
        Complex.exp (-(Complex.I * k) * r) = 0 := by
    intro r hr
    have he : baxterPrimitive z ρ σ A qp V T i j r - baxterPrimitive z ρ σ A qp V T j i r = 0 := by
      by_contra h
      exact hr (hs (Function.mem_support.mpr h))
    rw [he, zero_mul]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  simp_rw [sub_mul]
  rw [integral_sub hf hg, baxterPrimitive_fourier z hz ρ σ A qp V T hσ k i j,
    baxterPrimitive_fourier z hz ρ σ A qp V T hσ k j i]

end FMSA.ExactMSA.MultiTailMixture
