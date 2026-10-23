import LeanCode.YukawaOZMix.MSAMultiTailMixtureDPKernelFourier
import LeanCode.YukawaOZMix.MSAMultiTailMixtureRadial
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.OpenPos

/-! Recover the independent DP primitive from the actual first-order
Fourier integral. Finite increments avoid an additional first-moment premise. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

theorem real_axis_weighted_integrable (f : ℝ → ℝ) (hf : Integrable f) (k : ℝ) :
    Integrable (fun r => (f r : ℂ)*Complex.exp (-(Complex.I*k)*r)) := by
  apply (hf.ofReal (𝕜 := ℂ)).mul_bdd (μ := volume) (c := 1)
    (show AEStronglyMeasurable (fun r : ℝ => Complex.exp (-(Complex.I*k)*r)) volume by fun_prop)
  filter_upwards with r
  simp [Complex.norm_exp]

def intervalBox (h : ℝ) : ℝ → ℝ := (Icc 0 h).indicator (fun _ => 1)

theorem intervalBox_integrable (h : ℝ) : Integrable (intervalBox h) :=
  (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc

theorem intervalBox_positive_fourier (h : ℝ) (hh : 0 ≤ h) (k : ℝ) (hk : k ≠ 0) :
    (∫ r : ℝ, (intervalBox h r : ℂ)*Complex.exp ((Complex.I*k)*r)) =
      (Complex.exp ((Complex.I*k)*h)-1)/(Complex.I*k) := by
  have hs : Complex.I*(k : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hk)
  have he : (fun r : ℝ => (intervalBox h r : ℂ)*Complex.exp ((Complex.I*k)*r)) =
      (Icc 0 h).indicator (fun r => Complex.exp ((Complex.I*k)*r)) := by
    funext r
    by_cases hr : r ∈ Icc 0 h <;> simp [intervalBox, hr]
  rw [he, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hh]
  have hi := expComplex_interval (-(Complex.I*k)) 0 h (neg_ne_zero.mpr hs)
  simp only [neg_neg, Complex.ofReal_zero, mul_zero, Complex.exp_zero, div_neg] at hi
  rw [hi]
  ring

theorem realPlusConv_intervalBox (V : ℝ → ℝ) (h : ℝ) (hh : 0 ≤ h) (r : ℝ) :
    realPlusConv (intervalBox h) V r = ∫ t in r..r+h, V t := by
  unfold realPlusConv intervalBox
  have he : (fun u => (Icc 0 h).indicator (fun _ => (1 : ℝ)) u*V (r+u)) =
      (Icc 0 h).indicator (fun u => V (u+r)) := by
    funext u
    by_cases hu : u ∈ Icc 0 h <;> simp [hu, add_comm]
  rw [he, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hh, intervalIntegral.integral_comp_add_right]
  simp [add_comm]

theorem realPlusConv_intervalBox_continuous (V : ℝ → ℝ) (hV : Integrable V)
    (h : ℝ) (hh : 0 ≤ h) : Continuous (realPlusConv (intervalBox h) V) := by
  have he : realPlusConv (intervalBox h) V =
      fun r => (∫ t in (0 : ℝ)..r+h, V t)-(∫ t in (0 : ℝ)..r, V t) := by
    funext r
    rw [realPlusConv_intervalBox V h hh r]
    have hi := intervalIntegral.integral_add_adjacent_intervals
      (a := 0) (b := r) (c := r+h) hV.intervalIntegrable hV.intervalIntegrable
    linarith
  rw [he]
  exact ((hV.continuous_primitive 0).comp (continuous_id.add continuous_const)).sub
    (hV.continuous_primitive 0)

/-- An L1 Fourier antiderivative has the correct finite increments. -/
theorem ae_increment_of_fourier_antiderivative (P V : ℝ → ℝ)
    (hP : Integrable P) (hV : Integrable V) (a : ℝ)
    (hcP : ∀ r, r ≠ a → ContinuousAt P r)
    (hFT : ∀ k : ℝ, k ≠ 0 →
      (∫ r : ℝ, (P r : ℂ)*Complex.exp (-(Complex.I*k)*r)) =
        -(∫ r : ℝ, (V r : ℂ)*Complex.exp (-(Complex.I*k)*r))/(Complex.I*k))
    (h : ℝ) (hh : 0 ≤ h) :
    ∀ᵐ r, P (r+h)-P r = -(∫ t in r..r+h, V t) := by
  have hshift : Integrable (fun r => P (r+h)) :=
    ((measurePreserving_add_right volume h).integrable_comp hP.aestronglyMeasurable).mpr hP
  have hG : Integrable (realPlusConv (intervalBox h) V) := by
    have hi := realPlusConv_axis_weighted_integrable (intervalBox h) V 0
      (by simpa using ((intervalBox_integrable h).ofReal : Integrable (fun r => (intervalBox h r : ℂ))))
      (by simpa using (hV.ofReal : Integrable (fun r => (V r : ℂ))))
    simpa using hi.re
  have hcf : ∀ᵐ r, ContinuousAt (fun r => ((P (r+h)-P r : ℝ) : ℂ)) r := by
    filter_upwards [volume.ae_ne a, volume.ae_ne (a-h)] with r hr hs
    have hrh : r+h ≠ a := by intro he; apply hs; linarith
    exact Complex.continuous_ofReal.continuousAt.comp
      (((hcP (r+h) hrh).comp (f := fun x : ℝ => x+h)
        (show ContinuousAt (fun x : ℝ => x+h) r by fun_prop)).sub (hcP r hr))
  have hcg : ∀ᵐ r, ContinuousAt (fun r => (-(realPlusConv (intervalBox h) V r) : ℂ)) r :=
    Eventually.of_forall (fun r =>
      (Complex.continuous_ofReal.continuousAt.comp
        (realPlusConv_intervalBox_continuous V hV h hh).continuousAt).neg)
  have hae := FMSA.MixtureBaxter.ae_eq_of_zOfW_transform_offdiag
    ((hshift.sub hP).ofReal : Integrable (fun r => ((P (r+h)-P r : ℝ) : ℂ)))
    (hG.ofReal.neg : Integrable (fun r => (-(realPlusConv (intervalBox h) V r) : ℂ)))
    hcf hcg (fun w hw => ?_)
  · filter_upwards [hae] with r hr
    rw [← Complex.ofReal_neg] at hr
    exact (Complex.ofReal_injective hr).trans (by rw [realPlusConv_intervalBox V h hh r])
  · let k : ℝ := 2*π*w
    have hk : k ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero pi_ne_zero) hw
    have he : FMSA.MixtureBaxter.zOfW w = Complex.I*k := by
      unfold FMSA.MixtureBaxter.zOfW k
      push_cast
      ring
    simp only [he, neg_mul, Complex.ofReal_sub, sub_mul]
    have hs := real_axis_weighted_integrable _ hshift k
    have hp := real_axis_weighted_integrable P hP k
    simp only [neg_mul] at hs hp
    rw [integral_sub hs hp, integral_neg]
    have ht := FMSA.MixtureBaxter.laplace_shift (fun r => (P r : ℂ)) h (Complex.I*k)
    have hc := realPlusConv_fourier (intervalBox h) V k
      (by simpa only [Complex.ofReal_neg, mul_neg, neg_neg] using
        real_axis_weighted_integrable (intervalBox h) (intervalBox_integrable h) (-k))
      (real_axis_weighted_integrable V hV k)
    have hpFT := hFT k hk
    simp only [neg_mul] at ht hc hpFT
    rw [ht, hc, intervalBox_positive_fourier h hh k hk, hpFT]
    ring

/-- The vanishing boundary at infinity fixes the integration constant. -/
theorem ae_tail_primitive_of_fourier_antiderivative (P V : ℝ → ℝ)
    (hP : Integrable P) (hV : Integrable V) (a : ℝ)
    (hcP : ∀ r, r ≠ a → ContinuousAt P r)
    (hFT : ∀ k : ℝ, k ≠ 0 →
      (∫ r : ℝ, (P r : ℂ)*Complex.exp (-(Complex.I*k)*r)) =
        -(∫ r : ℝ, (V r : ℂ)*Complex.exp (-(Complex.I*k)*r))/(Complex.I*k))
    (hlim : Tendsto P atTop (𝓝 0)) :
    P =ᵐ[volume] fun r => ∫ t in Ioi r, V t := by
  have hall : ∀ᵐ r, ∀ n : ℕ, P (r+n)-P r = -(∫ t in r..r+n, V t) :=
    ae_all_iff.mpr (fun n => ae_increment_of_fourier_antiderivative P V hP hV a hcP hFT
      n (Nat.cast_nonneg n))
  filter_upwards [hall] with r hr
  have hn : Tendsto (fun n : ℕ => r+(n : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left _ r tendsto_natCast_atTop_atTop
  have hp := (hlim.comp hn).sub_const (P r)
  have hv := (intervalIntegral_tendsto_integral_Ioi r hV.integrableOn hn).neg
  have he := tendsto_nhds_unique hp (hv.congr (fun n => (hr n).symm))
  simpa using he

def dpOddW (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K : TailMatrix ι N)
    (i j : Fin N) (r : ℝ) : ℝ := dpW z ρ σ K i j r-dpW z ρ σ K i j (-r)

def dpPrimitive (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K : TailMatrix ι N)
    (i j : Fin N) (r : ℝ) : ℝ := ∫ t in Ioi r, dpOddW z ρ σ K i j t

theorem dpW_integrable (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (K : TailMatrix ι N) (i j : Fin N) :
    Integrable (dpW z ρ σ K i j) := by
  have hi := dpW_axis_weighted_integrable z hz ρ σ hσ K 0 i j
  simpa using hi.re

theorem dpOddW_integrable (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (K : TailMatrix ι N) (i j : Fin N) :
    Integrable (dpOddW z ρ σ K i j) :=
  (dpW_integrable z hz ρ σ hσ K i j).sub (dpW_integrable z hz ρ σ hσ K i j).comp_neg

theorem dpOddW_fourier (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (K : TailMatrix ι N) (k : ℝ) (i j : Fin N) :
    (∫ r : ℝ, (dpOddW z ρ σ K i j r : ℂ)*Complex.exp (-(Complex.I*k)*r)) =
      dpWFourier z ρ σ K k i j-dpWFourier z ρ σ K (-k) i j := by
  have hw := dpW_integrable z hz ρ σ hσ K i j
  simp only [dpOddW, Complex.ofReal_sub, sub_mul]
  rw [integral_sub (real_axis_weighted_integrable _ hw k)
    (real_axis_weighted_integrable _ hw.comp_neg k)]
  unfold dpWFourier
  congr 1
  have he := integral_neg_eq_self (fun r : ℝ =>
    (dpW z ρ σ K i j r : ℂ)*Complex.exp (-(Complex.I*(-k : ℝ))*r)) volume
  simpa only [Complex.ofReal_neg, mul_neg, neg_neg, neg_mul] using he

theorem dpPrimitive_continuous (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (K : TailMatrix ι N) (i j : Fin N) :
    Continuous (dpPrimitive z ρ σ K i j) := by
  have hi := dpOddW_integrable z hz ρ σ hσ K i j
  have he : dpPrimitive z ρ σ K i j = fun r =>
      (∫ t in Ioi (0 : ℝ), dpOddW z ρ σ K i j t)-
        (∫ t in (0 : ℝ)..r, dpOddW z ρ σ K i j t) := by
    funext r
    unfold dpPrimitive
    have he := intervalIntegral.integral_Ioi_sub_Ioi' (a := 0) (b := r)
      hi.integrableOn hi.integrableOn
    linarith
  rw [he]
  exact continuous_const.sub (hi.continuous_primitive 0)

theorem linearizedPrimitiveReal_tendsto_zero (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hv : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i) (i j : Fin N) :
    Tendsto (linearizedPrimitiveReal z ρ σ (firstOrderDt z ρ σ K)
      (baseSeed z ρ σ) i j) atTop (𝓝 0) := by
  have he : linearizedPrimitiveReal z ρ σ (firstOrderDt z ρ σ K) (baseSeed z ρ σ) i j =ᶠ[atTop]
      fun r => ∑ u, 2*π*K u i j/z u*exp (-z u*(r-edgeHi σ i j)) := by
    filter_upwards [eventually_gt_atTop (edgeHi σ i j)] with r hr
    exact linearizedPrimitiveReal_exterior z ρ σ K hz hv hρ hσ i j r hr
  apply Tendsto.congr' he.symm
  have ht := tendsto_finsetSum Finset.univ (fun u _ =>
    (shiftedRealExp_tendsto (z u) (edgeHi σ i j) (hz u)).const_mul (2*π*K u i j/z u))
  simpa using ht

/-- Joint actual P1 / independently constructed DP primitive identification,
throughout the full real axis up to closed-support endpoint representatives. -/
theorem linearizedPrimitiveReal_ae_eq_dpPrimitive (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hv : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i)
    (hK : ∀ u i j, K u i j=K u j i) (i j : Fin N) :
    linearizedPrimitiveReal z ρ σ (firstOrderDt z ρ σ K) (baseSeed z ρ σ) i j =ᵐ[volume]
      dpPrimitive z ρ σ K i j := by
  have hp := linearizedPrimitiveReal_complex_integrable z hz ρ σ (fun i => (hσ i).le)
    (firstOrderDt z ρ σ K) (baseSeed z ρ σ) i j
  apply ae_tail_primitive_of_fourier_antiderivative _ _ (by simpa using hp.re)
    (dpOddW_integrable z hz ρ σ (fun i => (hσ i).le) K i j) (edgeLo σ i j)
    (linearizedPrimitiveReal_continuousAt_off_edges z hz ρ σ (fun i => (hσ i).le) _ _ i j)
    (fun k hk => ?_) (linearizedPrimitiveReal_tendsto_zero z ρ σ K hz hv hρ hσ i j)
  rw [linearizedPrimitiveReal_fourier_eq_DP_W_difference z ρ σ K hz hv hρ hσ hK k hk,
    dpOddW_fourier z hz ρ σ (fun i => (hσ i).le) K]
  ring

theorem dpPrimitive_integrable (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hv : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i)
    (hK : ∀ u i j, K u i j=K u j i) (i j : Fin N) :
    Integrable (dpPrimitive z ρ σ K i j) := by
  have hi := linearizedPrimitiveReal_complex_integrable z hz ρ σ (fun i => (hσ i).le)
    (firstOrderDt z ρ σ K) (baseSeed z ρ σ) i j
  have hp : Integrable (linearizedPrimitiveReal z ρ σ (firstOrderDt z ρ σ K) (baseSeed z ρ σ) i j) :=
    by simpa using hi.re
  exact hp.congr (linearizedPrimitiveReal_ae_eq_dpPrimitive z ρ σ K hz hv hρ hσ hK i j)

theorem linearizedPrimitiveReal_eq_dpPrimitive_off_edge (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hv : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i)
    (hK : ∀ u i j, K u i j=K u j i) (i j : Fin N) (r : ℝ)
    (hr : r ≠ edgeLo σ i j) :
    linearizedPrimitiveReal z ρ σ (firstOrderDt z ρ σ K) (baseSeed z ρ σ) i j r =
      dpPrimitive z ρ σ K i j r := by
  have he := volume.eqOn_open_of_ae_eq
    (ae_restrict_of_ae (linearizedPrimitiveReal_ae_eq_dpPrimitive z ρ σ K hz hv hρ hσ hK i j)
      : _ =ᵐ[volume.restrict ({edgeLo σ i j}ᶜ)] _)
    isClosed_singleton.isOpen_compl
    (fun t ht => (linearizedPrimitiveReal_continuousAt_off_edges z hz ρ σ (fun i => (hσ i).le)
      _ _ i j t (by simpa using ht)).continuousWithinAt)
    (dpPrimitive_continuous z hz ρ σ (fun i => (hσ i).le) K i j).continuousOn
  exact he (by simpa using hr)

end FMSA.ExactMSA.MultiTailMixture
