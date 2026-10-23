import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearGIdentification
import LeanCode.Analysis.RadialMixtureFirstOrder
import LeanCode.YukawaOZMix.MSAMultiTailMixtureRadial

/-! Actual contact test and the full nonlinear zero-density boundary.
The signed-tail MSA closure does not imply nonnegative g, even at zero density.
No conclusion here about a positive-density nonlinear OZ certificate is assumed. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0 FMSA.HardSphere
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

theorem nonlinearCausalG_at_zero (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (i j : Fin N) :
    nonlinearCausalG z ρ σ Dt G 0 i j=nonlinearGSource z ρ σ Dt G 0 i j := by
  simpa using nonlinearCausalG_renewal z ρ σ Dt G i j 0 le_rfl

theorem nonlinearG_at_contact (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (i j : Fin N) :
    nonlinearG z ρ σ Dt G i j (edgeHi σ i j)=
      (amplitudeQp z ρ σ Dt G i j+∑ u, z u*C z ρ σ Dt G u i j)/(2*π*edgeHi σ i j) := by
  simp only [nonlinearG, lt_self_iff_false, if_false, sub_self, nonlinearCausalG_at_zero,
    nonlinearGSource, Matrix.of_apply, mul_zero, exp_zero, mul_one, zero_add]
  ring

/-- A finite, directly computable necessary condition for physical RDF positivity. -/
theorem nonlinearG_negative_contact_iff (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (i j : Fin N) (hR : 0 < edgeHi σ i j) :
    nonlinearG z ρ σ Dt G i j (edgeHi σ i j)<0 ↔
      amplitudeQp z ρ σ Dt G i j+∑ u, z u*C z ρ σ Dt G u i j<0 := by
  rw [nonlinearG_at_contact]
  rw [div_lt_iff₀ (by positivity : 0 < 2*π*edgeHi σ i j)]
  simp

theorem nonlinearG_negative_contact_has_outer_interval (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (i j : Fin N) (hR : 0 < edgeHi σ i j)
    (hc : nonlinearG z ρ σ Dt G i j (edgeHi σ i j)<0) :
    ∃ ε > 0, ∀ r ∈ Ico (edgeHi σ i j) (edgeHi σ i j+ε),
      nonlinearG z ρ σ Dt G i j r<0 := by
  have hy : nonlinearCausalG z ρ σ Dt G 0 i j<0 := by
    simpa only [nonlinearG, lt_self_iff_false, if_false, sub_self,
      div_lt_iff₀ hR, zero_mul] using hc
  have ht : ∀ᶠ t in 𝓝 (0 : ℝ), nonlinearCausalG z ρ σ Dt G t i j<0 :=
    (((nonlinearCausalG_continuous z ρ σ Dt G).matrix_elem i j).continuousAt).eventually_lt
      continuousAt_const hy
  obtain ⟨ε, he, hball⟩ := Metric.mem_nhds_iff.mp ht
  refine ⟨ε, he, ?_⟩
  intro r hr
  have hr0 : 0 < r := hR.trans_le hr.1
  have hneg : nonlinearCausalG z ρ σ Dt G (r-edgeHi σ i j) i j<0 :=
    hball (by simpa [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hr.1)]
      using (show r-edgeHi σ i j<ε from by linarith [hr.2]))
  rw [nonlinearG, if_neg (not_lt.mpr hr.1), div_lt_iff₀ hr0, zero_mul]
  exact hneg

@[simp] theorem nonlinearW_zero_density (z : ι → ℝ) (Dt G : TailMatrix ι N)
    (u : ι) (i j : Fin N) : W z 0 Dt G u i j=0 := by
  simp [W, Wt]

@[simp] theorem nonlinearC_zero_density (z : ι → ℝ) (σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (u : ι) (i j : Fin N) : C z 0 σ Dt G u i j=Dt u i j := by
  simp [C, Ct, MSAMixture.gam, ite_mul]

@[simp] theorem nonlinearA_zero_density (z : ι → ℝ) (σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (j : Fin N) : amplitudeA z 0 σ Dt G j=2*π := by
  simp [amplitudeA, mixDA, mixM, mixN, Qppphys, xi2, vacMix, etaMix]

@[simp] theorem nonlinearQp_zero_density (z : ι → ℝ) (σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (i j : Fin N) : amplitudeQp z 0 σ Dt G i j=2*π*edgeHi σ i j := by
  simp [amplitudeQp, mixDqp, mixM, mixN, Q0phys, xi2, vacMix, etaMix, edgeHi]

@[simp] theorem nonlinearKernel_zero_density (z : ι → ℝ) (σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (r : ℝ) : nonlinearCausalKernel z 0 σ Dt G r=0 := by
  ext i j
  simp [nonlinearCausalKernel]

@[simp] theorem nonlinearBudget_zero_density (z : ι → ℝ) (σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (δ : ℝ) : nonlinearWeightedKernelBudget z 0 σ Dt G δ=0 := by
  simp [nonlinearWeightedKernelBudget, FMSA.matrixAbsSum]

theorem nonlinearDt_zero_density_of_root (z : ι → ℝ) (σ : Fin N → ℝ)
    (K Dt G : TailMatrix ι N) (hroot : IsRoot z 0 σ K Dt G) (u : ι) (i j : Fin N) :
    Dt u i j=2*π*K u i j/z u := by
  simpa [firstLHS] using hroot.1 u i j

theorem nonlinearCausalG_zero_density (z : ι → ℝ) (σ : Fin N → ℝ)
    (K Dt G : TailMatrix ι N) (hz : ∀ u, z u ≠ 0) (hroot : IsRoot z 0 σ K Dt G)
    (i j : Fin N) (r : ℝ) (hr : 0 ≤ r) :
    nonlinearCausalG z 0 σ Dt G r i j=r+edgeHi σ i j+
      ∑ u, K u i j*exp (-z u*r) := by
  rw [nonlinearCausalG_renewal z 0 σ Dt G i j r hr]
  simp only [nonlinearKernel_zero_density, Matrix.zero_apply, mul_zero,
    intervalIntegral.integral_zero, Finset.sum_const_zero, add_zero,
    nonlinearGSource, Matrix.of_apply, nonlinearA_zero_density,
    nonlinearQp_zero_density, nonlinearC_zero_density]
  simp_rw [nonlinearDt_zero_density_of_root z σ K Dt G hroot]
  have he : (∑ u, z u*(2*π*K u i j/z u)*exp (-z u*r))=
      2*π*∑ u, K u i j*exp (-z u*r) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    field_simp [hz u]
  rw [he]
  field_simp [pi_ne_zero]

theorem nonlinearG_zero_density_outer (z : ι → ℝ) (σ : Fin N → ℝ)
    (K Dt G : TailMatrix ι N) (hz : ∀ u, z u ≠ 0) (hroot : IsRoot z 0 σ K Dt G)
    (i j : Fin N) (r : ℝ) (hr : 0 < r) (hR : edgeHi σ i j ≤ r) :
    nonlinearG z 0 σ Dt G i j r=1+(∑ u, K u i j*exp (-z u*(r-edgeHi σ i j)))/r := by
  rw [nonlinearG, if_neg (not_lt.mpr hR),
    nonlinearCausalG_zero_density z σ K Dt G hz hroot i j _ (sub_nonneg.mpr hR)]
  field_simp [hr.ne']
  ring

theorem nonlinearH_zero_density_outer (z : ι → ℝ) (σ : Fin N → ℝ)
    (K Dt G : TailMatrix ι N) (hz : ∀ u, z u ≠ 0) (hroot : IsRoot z 0 σ K Dt G)
    (i j : Fin N) (hR : 0 < edgeHi σ i j) (r : ℝ) (hr : edgeHi σ i j ≤ r) :
    nonlinearH z 0 σ Dt G i j r=(∑ u, K u i j*exp (-z u*(r-edgeHi σ i j)))/r := by
  have he := nonlinearG_eq_one_add_h z 0 σ Dt G i j hR r (hR.trans_le hr)
  rw [nonlinearG_zero_density_outer z σ K Dt G hz hroot i j r (hR.trans_le hr) hr] at he
  linarith

/-- The actual BH root has a unique dilute amplitude solution. -/
theorem nonlinearRoot_zero_density_iff (z : ι → ℝ) (σ : Fin N → ℝ)
    (K Dt G : TailMatrix ι N) (hz : ∀ u, z u ≠ 0) :
    IsRoot z 0 σ K Dt G ↔
      (∀ u i j, Dt u i j=2*π*K u i j/z u) ∧
      (∀ u i j, G u i j=(1+z u*edgeHi σ i j)/(z u)^2+
        ∑ t, K t i j/(z u+z t)) := by
  have hs (u : ι) (i j : Fin N) (hD : ∀ t, Dt t i j=2*π*K t i j/z t) :
      secondRHS z 0 σ Dt G u i j=2*π*((1+z u*edgeHi σ i j)/(z u)^2+
        ∑ t, K t i j/(z u+z t)) := by
    simp only [secondRHS, nonlinearA_zero_density, nonlinearQp_zero_density,
      nonlinearC_zero_density, hD]
    have he : (∑ t, (z u)^2*z t/(z u+z t)*(2*π*K t i j/z t))=
        2*π*(z u)^2*∑ t, K t i j/(z u+z t) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      field_simp [hz t]
    rw [he]
    field_simp [hz u]
  constructor
  · intro h
    refine ⟨fun u i j => nonlinearDt_zero_density_of_root z σ K Dt G h u i j, ?_⟩
    intro u i j
    have he := h.2 u i j
    simp only [secondLHS, Pi.zero_apply, zero_mul, sub_zero, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at he
    rw [hs u i j (fun t => nonlinearDt_zero_density_of_root z σ K Dt G h t i j)] at he
    exact mul_left_cancel₀ (mul_ne_zero two_ne_zero pi_ne_zero) he
  · rintro ⟨hD, hG⟩
    constructor
    · intro u i j
      simpa [firstLHS] using hD u i j
    · intro u i j
      simp only [secondLHS, Pi.zero_apply, zero_mul, sub_zero, mul_ite, mul_one,
        mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [hs u i j (fun t => hD t i j), hG]

def nonlinearZeroDensityDt (z : ι → ℝ) (K : TailMatrix ι N) : TailMatrix ι N :=
  fun u i j => 2*π*K u i j/z u

def nonlinearZeroDensityG (z : ι → ℝ) (σ : Fin N → ℝ) (K : TailMatrix ι N) : TailMatrix ι N :=
  fun u i j => (1+z u*edgeHi σ i j)/(z u)^2+∑ t, K t i j/(z u+z t)

theorem nonlinearRoot_zero_density_exists (z : ι → ℝ) (σ : Fin N → ℝ)
    (K : TailMatrix ι N) (hz : ∀ u, z u ≠ 0) :
    IsRoot z 0 σ K (nonlinearZeroDensityDt z K) (nonlinearZeroDensityG z σ K) :=
  (nonlinearRoot_zero_density_iff z σ K _ _ hz).mpr ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩

/-- At zero density the exact constructed RDF is affine in coupling on the
whole real coupling axis, so adding higher Taylor orders cannot cure a negative
RDF there. This says nothing about finite-density thermodynamic thresholds. -/
theorem nonlinearG_zero_density_coupling_affine (z : ι → ℝ) (σ : Fin N → ℝ)
    (K : TailMatrix ι N) (hz : ∀ u, z u ≠ 0) (τ : ℝ) (i j : Fin N) (r : ℝ) (hr : 0 < r) :
    nonlinearG z 0 σ (nonlinearZeroDensityDt z (τ • K)) (nonlinearZeroDensityG z σ (τ • K)) i j r=
      nonlinearG z 0 σ (nonlinearZeroDensityDt z 0) (nonlinearZeroDensityG z σ 0) i j r+
      τ*(nonlinearG z 0 σ (nonlinearZeroDensityDt z K) (nonlinearZeroDensityG z σ K) i j r-
        nonlinearG z 0 σ (nonlinearZeroDensityDt z 0) (nonlinearZeroDensityG z σ 0) i j r) := by
  by_cases hc : r < edgeHi σ i j
  · simp only [nonlinearG_hardcore z 0 σ _ _ i j r hc]
    ring
  · have hR : edgeHi σ i j ≤ r := not_lt.mp hc
    rw [nonlinearG_zero_density_outer z σ (τ • K) _ _ hz
      (nonlinearRoot_zero_density_exists z σ (τ • K) hz) i j r hr hR,
      nonlinearG_zero_density_outer z σ K _ _ hz
      (nonlinearRoot_zero_density_exists z σ K hz) i j r hr hR,
      nonlinearG_zero_density_outer z σ 0 _ _ hz
      (nonlinearRoot_zero_density_exists z σ 0 hz) i j r hr hR]
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, zero_mul,
      Finset.sum_const_zero, zero_div, add_zero, mul_assoc, ← Finset.mul_sum]
    ring

theorem nonlinearG_zero_density_negative_contact_iff (z : ι → ℝ) (σ : Fin N → ℝ)
    (K Dt G : TailMatrix ι N) (hz : ∀ u, z u ≠ 0) (hroot : IsRoot z 0 σ K Dt G)
    (i j : Fin N) (hR : 0 < edgeHi σ i j) :
    nonlinearG z 0 σ Dt G i j (edgeHi σ i j)<0 ↔
      (∑ u, K u i j)< -edgeHi σ i j := by
  rw [nonlinearG_zero_density_outer z σ K Dt G hz hroot i j _ hR le_rfl]
  simp only [sub_self, mul_zero, exp_zero, mul_one]
  have he : 1+(∑ u, K u i j)/edgeHi σ i j=
      (edgeHi σ i j+∑ u, K u i j)/edgeHi σ i j := by field_simp
  rw [he, div_lt_iff₀ hR]
  simp only [zero_mul]
  constructor <;> intro h <;> linarith

theorem nonlinearCorrelation_zero_density_core (z : ι → ℝ) (σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (i j : Fin N) (horder : σ j ≤ σ i)
    (r : ℝ) (hr : 0 < r) (hR : r ≤ edgeHi σ i j) :
    correlation z 0 σ (amplitudeA z 0 σ Dt G) (amplitudeQp z 0 σ Dt G)
      (W z 0 Dt G) (C z 0 σ Dt G) i j r= -1 := by
  have hlo : ¬r < edgeLo σ i j := by unfold edgeLo; linarith
  simp only [correlation, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero,
    qPrime, if_neg hlo, if_pos hR, nonlinearA_zero_density, nonlinearQp_zero_density,
    nonlinearW_zero_density, mul_zero, zero_sub, zero_mul, sub_zero]
  field_simp [hr.ne', pi_ne_zero]
  ring

/-- At the actual dilute BH root, the same constructed h satisfies actual radial
OZ with the canonical ordered Baxter DCF, without any reciprocity/OZ premise. -/
theorem nonlinearH_zero_density_actual_radial_OZ (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (σ : Fin N → ℝ) (hσ : ∀ i, 0 < σ i) (K Dt G : TailMatrix ι N)
    (hroot : IsRoot z 0 σ K Dt G) (hK : ∀ u i j, K u i j=K u j i) (i j : Fin N) :
    nonlinearH z 0 σ Dt G i j =ᵐ[volume.restrict (Ioi 0)] fun r =>
      orderedRadialCorrelation z 0 σ K Dt G i j r+
        radialMixtureConv (orderedRadialCorrelation z 0 σ K Dt G) (nonlinearH z 0 σ Dt G) 0 i j r := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi,
    ae_restrict_of_ae (volume.ae_ne (edgeHi σ i j))] with r hr hne
  change 0 < r at hr
  simp only [radialMixtureConv, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
  have hRs : edgeHi σ j i=edgeHi σ i j := by unfold edgeHi; ring
  have hpos : 0 < edgeHi σ i j := by unfold edgeHi; linarith [hσ i, hσ j]
  by_cases hc : r < edgeHi σ i j
  · rw [nonlinearH_hardcore z 0 σ Dt G i j r hr hc]
    unfold orderedRadialCorrelation
    split_ifs with ho
    · exact (nonlinearCorrelation_zero_density_core z σ Dt G i j ho r hr hc.le).symm
    · exact (nonlinearCorrelation_zero_density_core z σ Dt G j i (le_of_not_ge ho) r hr
        (by rw [hRs]; exact hc.le)).symm
  · have he : edgeHi σ i j < r := lt_of_le_of_ne (not_lt.mp hc) hne.symm
    rw [nonlinearH_zero_density_outer z σ K Dt G (fun u => (hz u).ne') hroot i j hpos r he.le]
    unfold orderedRadialCorrelation
    split_ifs
    · rw [correlation_exterior_of_root z hz 0 σ K Dt G (fun i => (hσ i).le) hroot i j r he,
        Finset.sum_div]
    · rw [correlation_exterior_of_root z hz 0 σ K Dt G (fun i => (hσ i).le) hroot j i r
        (by rw [hRs]; exact he), hRs, Finset.sum_div]
      simp_rw [← hK]

theorem nonlinearG_zero_density_nonnegative_of_attraction (z : ι → ℝ) (σ : Fin N → ℝ)
    (K Dt G : TailMatrix ι N) (hz : ∀ u, z u ≠ 0) (hroot : IsRoot z 0 σ K Dt G)
    (hK : ∀ u i j, 0 ≤ K u i j) (i j : Fin N) (r : ℝ) (hr : 0 < r) :
    0 ≤ nonlinearG z 0 σ Dt G i j r := by
  by_cases hc : r < edgeHi σ i j
  · rw [nonlinearG_hardcore z 0 σ Dt G i j r hc]
  · rw [nonlinearG_zero_density_outer z σ K Dt G hz hroot i j r hr (not_lt.mp hc)]
    exact add_nonneg zero_le_one (div_nonneg (Finset.sum_nonneg
      (fun u _ => mul_nonneg (hK u i j) (exp_pos _).le)) hr.le)

theorem nonlinear_exists_decay_rate (z : ι → ℝ) (hz : ∀ u, 0 < z u) :
    ∃ δ > 0, ∀ u, δ < z u := by
  have hsum : 0 ≤ ∑ u, (1/z u) := Finset.sum_nonneg (fun u _ => (one_div_pos.mpr (hz u)).le)
  have hd : 0 < 2+∑ u, (1/z u) := by positivity
  refine ⟨1/(2+∑ u, (1/z u)), by positivity, ?_⟩
  intro u
  have hi : 1/z u ≤ ∑ t, (1/z t) := Finset.single_le_sum (f := fun t => (1/z t))
    (fun t _ => (one_div_pos.mpr (hz t)).le) (Finset.mem_univ u)
  have hm := (div_le_iff₀ (hz u)).mp hi
  rw [div_lt_iff₀ hd]
  nlinarith [hz u]

/-- Complete dilute-boundary certificate for the actual constructed nonlinear
mixture RDF: root, core, actual G moments, actual radial OZ, and global radius L1.
No density division or reciprocal-root premise is needed. -/
theorem nonlinear_zero_density_certificate (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (σ : Fin N → ℝ) (hσ : ∀ i, 0 < σ i) (K : TailMatrix ι N)
    (hK : ∀ u i j, K u i j=K u j i) :
    let Dt := nonlinearZeroDensityDt z K
    let G := nonlinearZeroDensityG z σ K
    IsRoot z 0 σ K Dt G ∧
      (∀ i j r, 0 < r → r < edgeHi σ i j → nonlinearH z 0 σ Dt G i j r= -1) ∧
      (∀ u i j, (∫ r in Ioi (0 : ℝ), exp (-z u*r)*(r*nonlinearG z 0 σ Dt G i j r))=
        exp (-z u*edgeHi σ i j)*G u i j) ∧
      (∀ i j, nonlinearH z 0 σ Dt G i j =ᵐ[volume.restrict (Ioi 0)] fun r =>
        orderedRadialCorrelation z 0 σ K Dt G i j r+
          radialMixtureConv (orderedRadialCorrelation z 0 σ K Dt G) (nonlinearH z 0 σ Dt G) 0 i j r) ∧
      (∀ i j, Integrable (fun r => r*nonlinearH z 0 σ Dt G i j r)) := by
  dsimp only
  have hroot := nonlinearRoot_zero_density_exists z σ K (fun u => (hz u).ne')
  obtain ⟨δ, hδ, hδz⟩ := nonlinear_exists_decay_rate z hz
  have hv : vacMix (0 : Fin N → ℝ) σ ≠ 0 := by simp [vacMix, etaMix]
  have hb : nonlinearWeightedKernelBudget z 0 σ (nonlinearZeroDensityDt z K)
      (nonlinearZeroDensityG z σ K) δ<1 := by rw [nonlinearBudget_zero_density]; norm_num
  refine ⟨hroot, nonlinearH_hardcore z 0 σ _ _, ?_,
    nonlinearH_zero_density_actual_radial_OZ z hz σ hσ K _ _ hroot hK, ?_⟩
  · exact nonlinearG_amplitude_eq_actual_radial_laplace z 0 σ K _ _ hz hσ hv hroot δ hδ hδz hb
  · exact nonlinearH_radius_integrable_of_weighted_budget z 0 σ _ _ hz (fun i => (hσ i).le)
      hv δ hδ hδz hb

/-- Two positive rates, a long attractive tail and a short repulsive tail, a
symmetric strength matrix, an actual unique dilute BH root and budget zero.
The actual g is negative on an interval outside every positive pair contact. -/
theorem nonlinear_long_attraction_short_repulsion_negative_RDF (σ : Fin N → ℝ)
    (i j : Fin N) (hR : 0 < edgeHi σ i j) :
    let z : Fin 2 → ℝ := fun u => if u=0 then 1 else 20
    let K : TailMatrix (Fin 2) N := fun u a b => if u=0 then edgeHi σ a b else -3*edgeHi σ a b
    let Dt := nonlinearZeroDensityDt z K
    let G := nonlinearZeroDensityG z σ K
    IsRoot z 0 σ K Dt G ∧ nonlinearWeightedKernelBudget z 0 σ Dt G 0.5=0 ∧
      (∃ ε > 0, ∀ r ∈ Ico (edgeHi σ i j) (edgeHi σ i j+ε), nonlinearG z 0 σ Dt G i j r<0) := by
  dsimp only
  let z : Fin 2 → ℝ := fun u => if u=0 then 1 else 20
  let K : TailMatrix (Fin 2) N := fun u a b => if u=0 then edgeHi σ a b else -3*edgeHi σ a b
  have hz : ∀ u, z u ≠ 0 := by intro u; simp only [z]; split_ifs <;> norm_num
  have hroot := nonlinearRoot_zero_density_exists z σ K hz
  refine ⟨hroot, nonlinearBudget_zero_density _ _ _ _ _, ?_⟩
  apply nonlinearG_negative_contact_has_outer_interval z 0 σ _ _ i j hR
  apply (nonlinearG_zero_density_negative_contact_iff z σ K _ _ hz hroot i j hR).mpr
  simp only [Fin.sum_univ_two, K]
  norm_num
  linarith

/-- The negative-RDF example also satisfies the actual radial OZ closure,
for the same root and the same constructed h, at every physical pair. -/
theorem nonlinear_long_attraction_short_repulsion_OZ_counterexample (σ : Fin N → ℝ)
    (hσ : ∀ i, 0 < σ i) :
    let z : Fin 2 → ℝ := fun u => if u=0 then 1 else 20
    let K : TailMatrix (Fin 2) N := fun u a b => if u=0 then edgeHi σ a b else -3*edgeHi σ a b
    let Dt := nonlinearZeroDensityDt z K
    let G := nonlinearZeroDensityG z σ K
    IsRoot z 0 σ K Dt G ∧
      (∀ a b, nonlinearH z 0 σ Dt G a b =ᵐ[volume.restrict (Ioi 0)] fun r =>
        orderedRadialCorrelation z 0 σ K Dt G a b r+
          radialMixtureConv (orderedRadialCorrelation z 0 σ K Dt G) (nonlinearH z 0 σ Dt G) 0 a b r) ∧
      (∀ a b, ∃ ε > 0, ∀ r ∈ Ico (edgeHi σ a b) (edgeHi σ a b+ε), nonlinearG z 0 σ Dt G a b r<0) := by
  dsimp only
  let z : Fin 2 → ℝ := fun u => if u=0 then 1 else 20
  let K : TailMatrix (Fin 2) N := fun u a b => if u=0 then edgeHi σ a b else -3*edgeHi σ a b
  have hz : ∀ u, 0 < z u := by intro u; simp only [z]; split_ifs <;> norm_num
  have hK : ∀ u a b, K u a b=K u b a := by
    intro u a b
    simp only [K]
    split_ifs <;> unfold edgeHi <;> ring
  have hroot := nonlinearRoot_zero_density_exists z σ K (fun u => (hz u).ne')
  refine ⟨hroot, nonlinearH_zero_density_actual_radial_OZ z hz σ hσ K _ _ hroot hK, ?_⟩
  intro a b
  exact (nonlinear_long_attraction_short_repulsion_negative_RDF σ a b
    (by unfold edgeHi; linarith [hσ a, hσ b])).2.2

end FMSA.ExactMSA.MultiTailMixture
