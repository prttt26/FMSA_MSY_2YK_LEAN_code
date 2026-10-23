import LeanCode.YukawaOZMix.MSAMultiTailMixtureRDFCertificate
import LeanCode.HSMixture.PhysHSMixRhoWeight

/-! Equal-diameter dictionary between the actual canonical HS DCF and PY.
This is a direct polynomial/convolution identity, independent of RDF uniqueness. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0 FMSA.HardSphere
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

def hsEqualQ (η s t : ℝ) : ℝ :=
  q_prime_py η s*(t-s)+q_doubleprime_py η/2*(t-s)^2
def hsEqualPrime (η s t : ℝ) : ℝ := q_prime_py η s+q_doubleprime_py η*(t-s)

theorem q_zero_equalDiam (z : ι → ℝ) (ρ σ : Fin N → ℝ) (s : ℝ)
    (hs : ∀ i, σ i=s) (hs0 : 0 < s) (hv : vacMix ρ σ ≠ 0) (i j : Fin N) (t : ℝ) :
    q z σ (amplitudeA z ρ σ 0 (baseSeed z ρ σ))
      (amplitudeQp z ρ σ 0 (baseSeed z ρ σ)) (W z ρ 0 (baseSeed z ρ σ))
      (C z ρ σ 0 (baseSeed z ρ σ)) i j t =
        (Icc (0 : ℝ) s).indicator (hsEqualQ (etaMix ρ σ) s) t := by
  have hlo : edgeLo σ i j=0 := by simp [edgeLo, hs]
  have hhi : edgeHi σ i j=s := by simp [edgeHi, hs]
  simp only [q, amplitudeA_zero, amplitudeQp_zero, W, C, Wt, Ct, Pi.zero_apply,
    mul_zero, zero_mul, Finset.sum_const_zero, add_zero,
    FMSA.HSMix.Q0phys_equalDiam hs hs0 hv, FMSA.HSMix.Qppphys_equalDiam hs hs0 hv, hlo, hhi]
  split_ifs with hl hh
  · exact (indicator_of_notMem (show t ∉ Icc (0 : ℝ) s from fun h => not_le_of_gt hl h.1) _).symm
  · rw [indicator_of_mem (show t ∈ Icc (0 : ℝ) s from ⟨le_of_not_gt hl, hh⟩)]
    rfl
  · exact (indicator_of_notMem (show t ∉ Icc (0 : ℝ) s from fun h => hh h.2) _).symm

theorem qPrime_zero_equalDiam (z : ι → ℝ) (ρ σ : Fin N → ℝ) (s : ℝ)
    (hs : ∀ i, σ i=s) (hs0 : 0 < s) (hv : vacMix ρ σ ≠ 0) (i j : Fin N) (t : ℝ) :
    qPrime z σ (amplitudeA z ρ σ 0 (baseSeed z ρ σ))
      (amplitudeQp z ρ σ 0 (baseSeed z ρ σ)) (W z ρ 0 (baseSeed z ρ σ))
      (C z ρ σ 0 (baseSeed z ρ σ)) i j t =
        (Icc (0 : ℝ) s).indicator (hsEqualPrime (etaMix ρ σ) s) t := by
  have hlo : edgeLo σ i j=0 := by simp [edgeLo, hs]
  have hhi : edgeHi σ i j=s := by simp [edgeHi, hs]
  simp only [qPrime, amplitudeA_zero, amplitudeQp_zero, W, C, Wt, Ct, Pi.zero_apply,
    mul_zero, zero_mul, Finset.sum_const_zero, sub_zero,
    FMSA.HSMix.Q0phys_equalDiam hs hs0 hv, FMSA.HSMix.Qppphys_equalDiam hs hs0 hv, hlo, hhi]
  split_ifs with hl hh
  · exact (indicator_of_notMem (show t ∉ Icc (0 : ℝ) s from fun h => not_le_of_gt hl h.1) _).symm
  · rw [indicator_of_mem (show t ∈ Icc (0 : ℝ) s from ⟨le_of_not_gt hl, hh⟩)]
    rfl
  · exact (indicator_of_notMem (show t ∉ Icc (0 : ℝ) s from fun h => hh h.2) _).symm

theorem hsEqual_convolution_window {η s r : ℝ} (hr : 0 < r) (hrs : r < s) :
    (∫ t : ℝ, (Icc (0 : ℝ) s).indicator (hsEqualPrime η s) (t+r)*
        (Icc (0 : ℝ) s).indicator (hsEqualQ η s) t) =
      ∫ t in r..s, hsEqualQ η s (t-r)*hsEqualPrime η s t := by
  have he : (fun t : ℝ => (Icc (0 : ℝ) s).indicator (hsEqualPrime η s) (t+r)*
      (Icc (0 : ℝ) s).indicator (hsEqualQ η s) t) =
      (Icc (0 : ℝ) (s-r)).indicator (fun t => hsEqualQ η s t*hsEqualPrime η s (t+r)) := by
    funext t
    by_cases ht : t ∈ Icc (0 : ℝ) (s-r)
    · rw [indicator_of_mem ht,
        indicator_of_mem (show t+r ∈ Icc (0 : ℝ) s from ⟨by linarith [ht.1], by linarith [ht.2]⟩),
        indicator_of_mem (show t ∈ Icc (0 : ℝ) s from ⟨ht.1, by linarith [ht.2]⟩)]
      ring
    · rw [indicator_of_notMem ht]
      by_cases hl : t < 0
      · rw [indicator_of_notMem (show t ∉ Icc (0 : ℝ) s from fun h => not_le_of_gt hl h.1), mul_zero]
      · have hh : s < t+r := by
          have ht0 : 0 ≤ t := le_of_not_gt hl
          have hh : ¬t ≤ s-r := fun h => ht ⟨ht0, h⟩
          linarith
        rw [indicator_of_notMem (show t+r ∉ Icc (0 : ℝ) s from fun h => not_le_of_gt hh h.2), zero_mul]
  rw [he, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ s-r from by linarith)]
  have hc := intervalIntegral.integral_comp_add_right
    (fun t => hsEqualQ η s (t-r)*hsEqualPrime η s t) (a := (0 : ℝ)) (b := s-r) r
  simpa only [zero_add, sub_add_cancel, add_sub_cancel_right] using hc

theorem rdfActualHS_equalDiam_inner (z : ι → ℝ) (ρ σ : Fin N → ℝ) (s : ℝ)
    (hs : ∀ i, σ i=s) (hs0 : 0 < s) (hv : 0 < vacMix ρ σ)
    (hη0 : 0 ≤ etaMix ρ σ) (hρtot : (∑ i, ρ i) ≠ 0)
    (i j : Fin N) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) s) :
    rdfActualHS z ρ σ i j r=c_HS (etaMix ρ σ) s r := by
  let η := etaMix ρ σ
  let d := ∑ i, ρ i
  have hη : η < 1 := by change 0 < 1-η at hv; linarith
  have hηdef : η=π*d*s^3/6 := by
    dsimp [η, d, etaMix]
    simp only [hs, ← Finset.sum_mul]
    ring
  have hp := baxter_factorization_inner hs0 hη0 hη hηdef r hr
  have hi : (∫ t in r..s, q0_poly η s d (t-r)*
      (d*q_prime_py η s+d*q_doubleprime_py η*(t-s))) =
      d^2*(∫ t in r..s, hsEqualQ η s (t-r)*hsEqualPrime η s t) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hr.2.le]
    intro t ht
    dsimp only
    rw [q0_poly_inner (show t-r ≤ s from by linarith [ht.2, hr.1])]
    unfold hsEqualQ hsEqualPrime
    ring
  rw [hi] at hp
  have he : rdfActualHS z ρ σ i j r=
      (-hsEqualPrime η s r+d*(∫ t in r..s, hsEqualQ η s (t-r)*hsEqualPrime η s t))/(2*π*r) := by
    unfold rdfActualHS orderedRadialCorrelation
    rw [if_pos (by rw [hs j, hs i])]
    unfold correlation
    simp only [q_zero_equalDiam z ρ σ s hs hs0 hv.ne', qPrime_zero_equalDiam z ρ σ s hs hs0 hv.ne']
    rw [indicator_of_mem (show r ∈ Icc (0 : ℝ) s from ⟨hr.1.le, hr.2.le⟩)]
    simp only [hsEqual_convolution_window hr.1 hr.2, ← Finset.sum_mul]
    rfl
  rw [he]
  apply (div_eq_iff (mul_ne_zero (by positivity : 2*π ≠ 0) hr.1.ne')).mpr
  have hd : d ≠ 0 := hρtot
  simp only [hsEqualPrime] at hp ⊢
  apply mul_left_cancel₀ hd
  linear_combination -hp

theorem rdfActualHS_equalDiam_ae (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (s : ℝ) (hs : ∀ i, σ i=s) (hs0 : 0 < s)
    (hv : 0 < vacMix ρ σ) (hρ : ∀ i, 0 ≤ ρ i) (hρtot : (∑ i, ρ i) ≠ 0)
    (i j : Fin N) :
    rdfActualHS z ρ σ i j =ᵐ[volume.restrict (Ioi 0)] c_HS (etaMix ρ σ) s := by
  have hη0 : 0 ≤ etaMix ρ σ := by
    unfold etaMix
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (hρ i) (by rw [hs i]; positivity))
  filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_restrict_of_ae (volume.ae_ne s)] with r hr hR
  by_cases hh : r < s
  · exact rdfActualHS_equalDiam_inner z ρ σ s hs hs0 hv hη0 hρtot i j ⟨hr, hh⟩
  · have hsr : s < r := lt_of_le_of_ne (le_of_not_gt hh) (Ne.symm hR)
    have hσ : ∀ i, 0 < σ i := fun i => by rw [hs i]; exact hs0
    rw [c_HS_outer hsr.le]
    exact orderedRadialCorrelation_zero_exterior z hz ρ σ hv hρ hσ i j r
      (by simpa [edgeHi, hs] using hsr)

end FMSA.ExactMSA.MultiTailMixture
