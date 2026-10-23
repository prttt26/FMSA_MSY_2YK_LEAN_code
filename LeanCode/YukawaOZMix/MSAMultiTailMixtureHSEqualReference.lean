import LeanCode.YukawaOZMix.MSAMultiTailMixtureHSEqualDCF
import LeanCode.YukawaOZMix.MSAMultiTailMixtureRDFBudget
import LeanCode.HardSphere.BaxterWeightedDecay

/-! An independently constructed equal-diameter HS reference for the actual
canonical mixture c0. The explicit matrix budget also supplies the scalar
HS decay budget, so the capstone takes neither h0 nor its moments as premises. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0 FMSA.HardSphere
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

def rdfEqualHSReference (ρ σ : Fin N → ℝ) (s : ℝ) (_i _j : Fin N) (r : ℝ) : ℝ :=
  baxterPsi (etaMix ρ σ) s (∑ i, ρ i) r/r

theorem equalDiam_scalar_kernel_eq_columnSum (ρ σ : Fin N → ℝ) (s : ℝ)
    (hs : ∀ i, σ i=s) (hs0 : 0 < s) (hv : vacMix ρ σ ≠ 0) (j : Fin N)
    (t : ℝ) :
    q0_poly (etaMix ρ σ) s (∑ i, ρ i) t=∑ i, rdfCausalKernel ρ σ t i j := by
  simp only [rdfCausalKernel, Matrix.of_apply, rdfRecenteredHSQ, hs,
    FMSA.HSMix.Q0phys_equalDiam hs hs0 hv, FMSA.HSMix.Qppphys_equalDiam hs hs0 hv,
    ← Finset.sum_mul]
  by_cases ht : t ≤ s
  · rw [min_eq_left ht, q0_poly_inner ht]; ring
  · rw [min_eq_right (not_le.mp ht).le, q0_poly_outer (not_le.mp ht)]
    ring

theorem equalDiam_scalar_weightedMass_le_matrixBudget (ρ σ : Fin N → ℝ) (s δ : ℝ)
    (hs : ∀ i, σ i=s) (hs0 : 0 < s) (hv : vacMix ρ σ ≠ 0) (j : Fin N) :
    baxterWeightedMass (etaMix ρ σ) s (∑ i, ρ i) δ ≤ rdfWeightedKernelBudget ρ σ δ := by
  unfold baxterWeightedMass rdfWeightedKernelBudget
  apply integral_mono_ae (q0_poly_weighted_integrable hs0)
    (rdfCausalKernel_weighted_absSum_integrable ρ σ δ)
  filter_upwards [] with t
  apply mul_le_mul_of_nonneg_left _ (exp_pos _).le
  rw [equalDiam_scalar_kernel_eq_columnSum ρ σ s hs hs0 hv j t]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  unfold FMSA.matrixAbsSum
  apply Finset.sum_le_sum
  intro i _
  exact Finset.single_le_sum (f := fun k : Fin N => |rdfCausalKernel ρ σ t i k|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ j)

theorem radial3d_conv_congr_first_ae_positive (f f' g : ℝ → ℝ)
    (h : f =ᵐ[volume.restrict (Ioi 0)] f') (r : ℝ) :
    radial3d_conv f g r=radial3d_conv f' g r := by
  unfold radial3d_conv
  split_ifs
  · rfl
  · congr 1
    apply integral_congr_ae
    filter_upwards [h] with t ht
    rw [ht]

theorem rdfEqualHSReference_actual_radial_OZ (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (s : ℝ) (hs : ∀ i, σ i=s) (hs0 : 0 < s)
    (hv : 0 < vacMix ρ σ) (hρ : ∀ i, 0 ≤ ρ i) (hρtot : (∑ i, ρ i) ≠ 0)
    (i j : Fin N) :
    rdfEqualHSReference ρ σ s i j =ᵐ[volume.restrict (Ioi 0)]
      fun r => rdfActualHS z ρ σ i j r+
        radialMixtureConv (rdfActualHS z ρ σ) (rdfEqualHSReference ρ σ s) ρ i j r := by
  let η := etaMix ρ σ
  let d := ∑ i, ρ i
  have hη : η < 1 := by change 0 < 1-η at hv; linarith
  have hηdef : η=π*d*s^3/6 := by
    dsimp [η, d, etaMix]
    simp only [hs, ← Finset.sum_mul]; ring
  have hc (a b : Fin N) := rdfActualHS_equalDiam_ae z hz ρ σ s hs hs0 hv hρ hρtot a b
  have he (r : ℝ) : radialMixtureConv (rdfActualHS z ρ σ) (rdfEqualHSReference ρ σ s) ρ i j r=
      d*radial3d_conv (c_HS η s) (fun x => baxterPsi η s d x/x) r := by
    unfold radialMixtureConv
    simp_rw [radial3d_conv_congr_first_ae_positive _ _ _ (hc i _) r]
    change (∑ x, ρ x*radial3d_conv (c_HS η s) (fun t => baxterPsi η s d t/t) r)=
      (∑ x, ρ x)*radial3d_conv (c_HS η s) (fun t => baxterPsi η s d t/t) r
    exact (Finset.sum_mul _ _ _).symm
  filter_upwards [ae_restrict_mem measurableSet_Ioi, hc i j] with r hr hcr
  rw [hcr, he r]
  have ho := baxterPsi_ozstar hs0 hη hηdef r hr
  dsimp only [rdfEqualHSReference]
  apply (div_eq_iff hr.ne').mpr
  linear_combination ho

theorem rdfEqualHSReference_valid_of_weighted_budget [NeZero N]
    (z : ι → ℝ) (hz : ∀ u, 0 < z u) (ρ σ : Fin N → ℝ) (s : ℝ)
    (hs : ∀ i, σ i=s) (hs0 : 0 < s) (hv : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 < ρ i) (δ : ℝ) (hδ : 0 < δ)
    (hb : rdfWeightedKernelBudget ρ σ δ < 1) :
    ValidRadialHSReference z ρ σ (rdfEqualHSReference ρ σ s) := by
  have hd : 0 < ∑ i, ρ i := Finset.sum_pos (fun i _ => hρ i) Finset.univ_nonempty
  have hm : baxterWeightedMass (etaMix ρ σ) s (∑ i, ρ i) δ < 1 :=
    (equalDiam_scalar_weightedMass_le_matrixBudget ρ σ s δ hs hs0 hv.ne' (0 : Fin N)).trans_lt hb
  refine ⟨fun _ _ => baxterPsi_div_radius_measurable _ _ _,
    fun _ _ => baxterPsi_div_radius_integrable_of_weighted_budget hs0 hδ hm,
    ?_, rdfEqualHSReference_actual_radial_OZ z hz ρ σ s hs hs0 hv (fun i => (hρ i).le) hd.ne'⟩
  intro i j r hr hR
  have hrs : r < s := by simpa [edgeHi, hs] using hR
  dsimp only [rdfEqualHSReference]
  rw [baxterPsi_core (show r ∈ Ioo (-s) s from ⟨by linarith, hrs⟩)]
  field_simp

theorem firstOrderMixtureRDF_equalDiam_certificate_of_weighted_budget [NeZero N]
    (z : ι → ℝ) (hz : ∀ u, 0 < z u) (ρ σ : Fin N → ℝ) (s : ℝ)
    (hs : ∀ i, σ i=s) (hs0 : 0 < s) (hv : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 < ρ i) (K : TailMatrix ι N) (hK : ∀ u i j, K u i j=K u j i)
    (δ : ℝ) (hδ : 0 < δ) (hzδ : ∀ u, δ ≤ z u)
    (hb : rdfWeightedKernelBudget ρ σ δ < 1) :
    (∀ i j r, r < edgeHi σ i j → rdfFirstOrderCausal z ρ σ K i j r=0) ∧
    (∀ τ i j r, 0 < r → r < edgeHi σ i j →
      rdfEqualHSReference ρ σ s i j r+τ*rdfFirstOrderCausal z ρ σ K i j r = -1) ∧
    (∀ i j, rdfFirstOrderCausal z ρ σ K i j =ᵐ[volume.restrict (Ioi 0)]
      fun r => rdfActualC1 z ρ σ K i j r+
        radialMixtureConv (rdfActualHS z ρ σ) (rdfFirstOrderCausal z ρ σ K) ρ i j r+
          radialMixtureConv (rdfActualC1 z ρ σ K) (rdfEqualHSReference ρ σ s) ρ i j r) :=
  firstOrderMixtureRDF_certificate_of_weighted_budget z hz ρ σ hv hρ
    (fun i => by rw [hs i]; exact hs0) K hK δ hδ hzδ hb (rdfEqualHSReference ρ σ s)
    (rdfEqualHSReference_valid_of_weighted_budget z hz ρ σ s hs hs0 hv hρ δ hδ hb)

end FMSA.ExactMSA.MultiTailMixture
