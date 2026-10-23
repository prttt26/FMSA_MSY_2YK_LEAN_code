import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearCoreCertificate

/-! Actual nonlinear DCF continuity and second moments for radial OZ transfer. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0 FMSA.HardSphere
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

theorem qPrime_bounded (z : ι → ℝ) (hz : ∀ u, 0 < z u) (σ A : Fin N → ℝ)
    (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N) (hσ : ∀ i, 0 ≤ σ i) (i j : Fin N) :
    ∃ M, ∀ r, |qPrime z σ A qp W C i j r| ≤ M := by
  classical
  obtain ⟨M0, h0⟩ := baxterQ'_bounded 1 one_pos σ A qp (fun _ _ => 0) (fun _ _ => 0) i j hσ
  choose M hM using fun u => baxterQ'_bounded (z u) (hz u) σ (fun _ => 0)
    (fun _ _ => 0) (W u) (C u) i j hσ
  refine ⟨M0+∑ u, M u, fun r => ?_⟩
  rw [qPrime_decomposition]
  exact (abs_add_le _ _).trans (add_le_add (h0 r)
    ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun u _ => hM u r))))

theorem qPrime_continuousAt_off_edges (z : ι → ℝ) (σ A : Fin N → ℝ)
    (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N) (i j : Fin N) (r : ℝ)
    (hrL : r ≠ edgeLo σ i j) (hrR : r ≠ edgeHi σ i j) :
    ContinuousAt (qPrime z σ A qp W C i j) r := by
  rcases lt_or_gt_of_ne hrL with hl | hl
  · apply (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) r).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hl] with x hx
    simp only [qPrime, if_pos hx]
  · rcases lt_or_gt_of_ne hrR with hh | hh
    · have he : qPrime z σ A qp W C i j =ᶠ[𝓝 r] fun x =>
          qp i j+A j*(x-edgeHi σ i j)-∑ u, z u*W u i j*exp (-z u*(x-edgeLo σ i j)) := by
        filter_upwards [eventually_gt_nhds hl, eventually_lt_nhds hh] with x hxl hxh
        simp only [qPrime, if_neg (not_lt.mpr hxl.le), if_pos hxh.le]
      exact (by fun_prop : ContinuousAt (fun x =>
        qp i j+A j*(x-edgeHi σ i j)-∑ u, z u*W u i j*exp (-z u*(x-edgeLo σ i j))) r).congr_of_eventuallyEq he
    · have he : qPrime z σ A qp W C i j =ᶠ[𝓝 r] fun x =>
          ∑ u, (-z u*W u i j*exp (-z u*(x-edgeLo σ i j))-
            z u*C u i j*exp (-z u*(x-edgeHi σ i j))) := by
        filter_upwards [eventually_gt_nhds hl, eventually_gt_nhds hh] with x hxl hxh
        simp only [qPrime, if_neg (not_lt.mpr hxl.le), if_neg (not_le.mpr hxh)]
      exact (by fun_prop : ContinuousAt (fun x =>
        ∑ u, (-z u*W u i j*exp (-z u*(x-edgeLo σ i j))-
          z u*C u i j*exp (-z u*(x-edgeHi σ i j)))) r).congr_of_eventuallyEq he

theorem qPrime_convolution_continuous (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N)
    (hσ : ∀ i, 0 ≤ σ i) (i j l : Fin N) :
    Continuous (fun r => ∫ t : ℝ, qPrime z σ A qp W C i l (t+r)*q z σ A qp W C j l t) := by
  obtain ⟨M, hM⟩ := qPrime_bounded z hz σ A qp W C hσ i l
  apply continuous_iff_continuousAt.mpr
  intro r
  apply continuousAt_of_dominated (bound := fun t => M*|q z σ A qp W C j l t|)
  · exact Eventually.of_forall (fun x => (convolution_integrable z hz σ A qp W C hσ i j l x).aestronglyMeasurable)
  · exact Eventually.of_forall (fun x => Eventually.of_forall (fun t => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hM (t+x)) (abs_nonneg _)))
  · exact (q_integrable z hz σ A qp W C hσ j l).abs.const_mul _
  · filter_upwards [volume.ae_ne (edgeLo σ i l-r), volume.ae_ne (edgeHi σ i l-r)] with t htL htR
    have hl : t+r ≠ edgeLo σ i l := by intro h; apply htL; linarith
    have hh : t+r ≠ edgeHi σ i l := by intro h; apply htR; linarith
    exact ((qPrime_continuousAt_off_edges z σ A qp W C i l (t+r) hl hh).comp
      (continuous_const.add continuous_id).continuousAt).mul continuousAt_const

theorem correlation_continuousAt_ordered (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N)
    (hσ : ∀ i, 0 ≤ σ i) (i j : Fin N) (horder : σ j ≤ σ i)
    (r : ℝ) (hr : 0 < r) (hrR : r ≠ edgeHi σ i j) :
    ContinuousAt (correlation z ρ σ A qp W C i j) r := by
  have hrL : r ≠ edgeLo σ i j := by unfold edgeLo; linarith
  have hp := (qPrime_continuousAt_off_edges z σ A qp W C i j r hrL hrR).neg
  have hc := (continuous_finsetSum Finset.univ (fun l _ =>
    (qPrime_convolution_continuous z hz σ A qp W C hσ i j l).const_mul (ρ l))).continuousAt (x := r)
  exact (hp.add hc).div (continuousAt_const.mul continuousAt_id) (by positivity)

theorem nonlinear_orderedCorrelation_odd_ae_continuous (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (K Dt G : TailMatrix ι N) (hσ : ∀ i, 0 ≤ σ i) (i j : Fin N) :
    ∀ᵐ v, ContinuousAt (oddRadialMoment (orderedRadialCorrelation z ρ σ K Dt G i j)) v := by
  apply oddRadialMoment_ae_continuous_off_contact _ (edgeHi σ i j)
  intro r hr hrR
  unfold orderedRadialCorrelation
  split_ifs with ho
  · exact correlation_continuousAt_ordered z hz ρ σ _ _ _ _ hσ i j ho r hr hrR
  · apply correlation_continuousAt_ordered z hz ρ σ _ _ _ _ hσ j i (not_le.mp ho).le r hr
    simpa only [edgeHi, add_comm] using hrR

theorem nonlinearH_odd_ae_continuous (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (i j : Fin N) (hR : 0 < edgeHi σ i j) :
    ∀ᵐ v, ContinuousAt (oddRadialMoment (nonlinearH z ρ σ Dt G i j)) v := by
  apply oddRadialMoment_ae_continuous_off_contact _ (edgeHi σ i j)
  intro r hr hrR
  rcases lt_or_gt_of_ne hrR with hl | hh
  · have he : nonlinearH z ρ σ Dt G i j =ᶠ[𝓝 r] fun _ => -1 := by
      filter_upwards [isOpen_Ioi.mem_nhds hr, isOpen_Iio.mem_nhds hl] with x hx hxR
      exact nonlinearH_hardcore z ρ σ Dt G i j x hx hxR
    exact continuousAt_const.congr_of_eventuallyEq he
  · have he : nonlinearH z ρ σ Dt G i j =ᶠ[𝓝 r]
        fun x => nonlinearRDFExcess z ρ σ Dt G (x-edgeHi σ i j) i j/x := by
      filter_upwards [isOpen_Ioi.mem_nhds hh] with x hx
      unfold nonlinearH
      rw [nonlinearRDFMoment_outer z ρ σ Dt G i j hR x hx.le]
    exact (((((nonlinearRDFExcess_continuous z ρ σ Dt G).matrix_elem i j).comp
      (continuous_id.sub continuous_const)).continuousAt).div continuousAt_id hr.ne').congr_of_eventuallyEq he

theorem nonlinear_orderedCorrelation_radius_integrable (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (K Dt G : TailMatrix ι N) (hσ : ∀ i, 0 ≤ σ i)
    (hroot : IsRoot z ρ σ K Dt G) (i j : Fin N) :
    IntegrableOn (fun r => r*orderedRadialCorrelation z ρ σ K Dt G i j r) (Ioi 0) := by
  unfold orderedRadialCorrelation
  split_ifs with ho
  · exact correlation_radius_integrable_of_root z hz ρ σ K Dt G hσ hroot i j ho
  · exact correlation_radius_integrable_of_root z hz ρ σ K Dt G hσ hroot j i (not_le.mp ho).le

theorem correlation_second_moment_integrable_of_root (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (K Dt G : TailMatrix ι N) (hσ : ∀ i, 0 ≤ σ i)
    (hroot : IsRoot z ρ σ K Dt G) (i j : Fin N) (horder : σ j ≤ σ i) :
    IntegrableOn (fun r => r*(r*correlation z ρ σ (amplitudeA z ρ σ Dt G)
      (amplitudeQp z ρ σ Dt G) (W z ρ Dt G) (C z ρ σ Dt G) i j r)) (Ioi 0) := by
  let R := edgeHi σ i j
  let c := correlation z ρ σ (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G)
    (W z ρ Dt G) (C z ρ σ Dt G) i j
  have hR : 0 ≤ R := by unfold R edgeHi; linarith [hσ i, hσ j]
  have hi := correlation_radius_integrable_of_root z hz ρ σ K Dt G hσ hroot i j horder
  have hic : IntegrableOn (fun r => r*(r*c r)) (Ioc 0 R) := by
    have hi' : IntegrableOn (fun r => (r*c r)*min r R) (Ioi 0) :=
      hi.mul_bdd (by fun_prop) (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min hr.le hR)]
        exact min_le_right _ _)
    apply (hi'.mono_set Ioc_subset_Ioi_self).congr_fun _ measurableSet_Ioc
    intro r hr; dsimp only; rw [min_eq_left hr.2]; ring
  have hit : IntegrableOn (fun r => r*(r*c r)) (Ioi R) := by
    have hie : IntegrableOn (fun r => ∑ u, K u i j*exp (z u*R)*(r*exp (-z u*r))) (Ioi R) :=
      integrable_finsetSum _ (fun u _ =>
        ((FMSA.ExactMSA.integrableOn_Ioi_id_mul_exp_neg (hz u)).mono_set
          (fun r hr => hR.trans_lt hr)).const_mul _)
    apply hie.congr_fun _ measurableSet_Ioi
    intro r hr
    dsimp only [c]
    rw [correlation_exterior_of_root z hz ρ σ K Dt G hσ hroot i j r hr, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    have he : exp (-z u*(r-R))=exp (z u*R)*exp (-z u*r) := by
      rw [← exp_add]; congr 1; ring
    rw [he]
    field_simp [(hR.trans_lt hr).ne']
    <;> ring
  have hset : Ioi (0 : ℝ)=Ioc 0 R ∪ Ioi R := by
    ext r; simp only [mem_Ioi, mem_Ioc, mem_union]
    constructor
    · intro hr; by_cases h : r ≤ R
      · exact Or.inl ⟨hr,h⟩
      · exact Or.inr (not_le.mp h)
    · rintro (⟨hr,_⟩ | hr)
      · exact hr
      · exact hR.trans_lt hr
  rw [hset, integrableOn_union]
  exact ⟨hic,hit⟩

theorem nonlinear_orderedCorrelation_second_moment_integrable (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (K Dt G : TailMatrix ι N) (hσ : ∀ i, 0 ≤ σ i)
    (hroot : IsRoot z ρ σ K Dt G) (i j : Fin N) :
    IntegrableOn (fun r => r*(r*orderedRadialCorrelation z ρ σ K Dt G i j r)) (Ioi 0) := by
  unfold orderedRadialCorrelation
  split_ifs with ho
  · exact correlation_second_moment_integrable_of_root z hz ρ σ K Dt G hσ hroot i j ho
  · exact correlation_second_moment_integrable_of_root z hz ρ σ K Dt G hσ hroot j i (not_le.mp ho).le

end FMSA.ExactMSA.MultiTailMixture
