import FMSAPaper.ActualRadialIdentification
import FMSAPaper.BaxterZeroMode
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-! A continuous radial Fourier symbol, including the actual zero mode. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open scoped BigOperators

namespace FMSA.Paper.RadialZeroMode
open ExactMSA.MultiTailMixture MSAMixture FMSA.ExactMSA.Breakpoint MatrixQ0

def radialSymbol (c : ℝ → ℝ) (k : ℝ) : ℝ :=
  4 * π * ∫ r in Ioi (0 : ℝ), r ^ 2 * c r * sinc (k * r)

theorem radialSymbol_zero (c : ℝ → ℝ) :
    radialSymbol c 0 = 4 * π * ∫ r in Ioi (0 : ℝ), r ^ 2 * c r := by
  simp [radialSymbol]

theorem radialSymbol_eq_radial_fourier (c : ℝ → ℝ) (k : ℝ) (hk : k ≠ 0) :
    radialSymbol c k = HardSphere.radial_fourier c k := by
  have he : (fun r => r ^ 2 * c r * sinc (k * r)) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun r => (1 / k) * (r * c r * sin (k * r)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : r ≠ 0 := ne_of_gt hr
    rw [sinc_of_ne_zero (mul_ne_zero hk hr0)]
    field_simp
  unfold radialSymbol HardSphere.radial_fourier
  rw [integral_congr_ae he, integral_const_mul]
  ring

theorem weighted_sinc_integrable (c : ℝ → ℝ)
    (hc : IntegrableOn (fun r => r ^ 2 * c r) (Ioi (0 : ℝ))) (k : ℝ) :
    IntegrableOn (fun r => r ^ 2 * c r * sinc (k * r)) (Ioi (0 : ℝ)) := by
  exact hc.mul_bdd (by fun_prop : AEStronglyMeasurable (fun r : ℝ => sinc (k * r))
    (volume.restrict (Ioi (0 : ℝ)))) (ae_of_all _ fun r => by
      simpa only [Real.norm_eq_abs] using abs_sinc_le_one (k * r))

theorem radialSymbol_continuous (c : ℝ → ℝ)
    (hc : IntegrableOn (fun r => r ^ 2 * c r) (Ioi (0 : ℝ))) :
    Continuous (radialSymbol c) := by
  unfold radialSymbol
  apply continuous_const.mul
  apply continuous_of_dominated
    (bound := fun r => ‖r ^ 2 * c r‖)
  · intro k
    exact (weighted_sinc_integrable c hc k).aestronglyMeasurable
  · intro k
    exact ae_of_all _ fun r => by
      rw [norm_mul]
      calc
        _ ≤ ‖r ^ 2 * c r‖ * 1 := mul_le_mul_of_nonneg_left
          (by simpa only [Real.norm_eq_abs] using abs_sinc_le_one (k * r)) (norm_nonneg _)
        _ = _ := mul_one _
  · exact hc.norm
  · exact ae_of_all _ fun r => by fun_prop

variable {N : ℕ} {T : Type*} [Fintype T]

theorem fourierQ_continuous (z : T → ℝ) (hz : ∀ t, 0 < z t)
    (sigma A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ) (W C : TailMatrix T N)
    (hs : ∀ i, 0 ≤ sigma i) (i j : Fin N) :
    Continuous (fun k => fourierQ z sigma A qp W C k i j) := by
  unfold fourierQ
  apply continuous_of_dominated (bound := fun r => ‖q z sigma A qp W C i j r‖)
  · intro k
    exact (q_complex_weighted_integrable z hz sigma A qp W C hs (Complex.I * k)
      (by simp) i j).aestronglyMeasurable
  · intro k
    exact ae_of_all _ fun r => by simp [Complex.norm_exp]
  · exact (q_integrable z hz sigma A qp W C hs i j).norm
  · exact ae_of_all _ fun r => by fun_prop

theorem spectralBaxterC_continuous (z : T → ℝ) (hz : ∀ t, 0 < z t)
    (rho sigma A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ) (W C : TailMatrix T N)
    (hs : ∀ i, 0 ≤ sigma i) (i j : Fin N) :
    Continuous (fun k => spectralBaxterC z rho sigma A qp W C k i j) := by
  have hf := fourierQ_continuous z hz sigma A qp W C hs
  unfold spectralBaxterC
  apply ((hf i j).add (hf j i).star).sub
  exact continuous_finsetSum _ fun l _ =>
    (continuous_const.mul (hf i l)).mul (hf j l).star

theorem shifted_radius_exp_integrable (z R : ℝ) (hz : 0 < z) (hR : 0 ≤ R) :
    IntegrableOn (fun r => r * exp (-z * (r - R))) (Ioi R) := by
  have hi := (FMSA.ExactMSA.integrableOn_Ioi_id_mul_exp_neg hz).mono_set (Ioi_subset_Ioi hR)
  have hi2 : IntegrableOn (fun r => exp (z * R) * (r * exp (-z * r))) (Ioi R) :=
    hi.const_mul _
  apply hi2.congr_fun _ measurableSet_Ioi
  intro r _
  dsimp only
  rw [show -z * (r - R) = z * R + (-z * r) by ring, exp_add]
  ring

theorem correlation_radius_sq_integrable_of_root (z : T → ℝ) (hz : ∀ t, 0 < z t)
    (rho sigma : Fin N → ℝ) (K Dt G : TailMatrix T N) (hs : ∀ i, 0 ≤ sigma i)
    (hroot : IsRoot z rho sigma K Dt G) (i j : Fin N) (horder : sigma j ≤ sigma i) :
    IntegrableOn (fun r => r ^ 2 * correlation z rho sigma (amplitudeA z rho sigma Dt G)
      (amplitudeQp z rho sigma Dt G) (W z rho Dt G) (C z rho sigma Dt G) i j r) (Ioi 0) := by
  let R := edgeHi sigma i j
  let c := correlation z rho sigma (amplitudeA z rho sigma Dt G)
    (amplitudeQp z rho sigma Dt G) (W z rho Dt G) (C z rho sigma Dt G) i j
  have hR : 0 ≤ R := by unfold R edgeHi; linarith [hs i, hs j]
  have hrc : IntegrableOn (fun r => r * c r) (Ioi 0) :=
    correlation_radius_integrable_of_root z hz rho sigma K Dt G hs hroot i j horder
  have hc := hrc.mono_set (show Ioc 0 R ⊆ Ioi (0 : ℝ) from fun r hr => hr.1)
  have hcore0 : IntegrableOn (fun r => r * (r * c r)) (Ioc 0 R) := by
    apply hc.bdd_mul (c := R) (by fun_prop : AEStronglyMeasurable (fun r : ℝ => r)
      (volume.restrict (Ioc 0 R)))
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    simpa only [Real.norm_eq_abs, abs_of_pos hr.1] using hr.2
  have hcore : IntegrableOn (fun r => r ^ 2 * c r) (Ioc 0 R) := by
    apply hcore0.congr_fun _ measurableSet_Ioc
    intro r _
    ring
  have htail : IntegrableOn (fun r => r ^ 2 * c r) (Ioi R) := by
    have hi : IntegrableOn (fun r => ∑ t, K t i j * (r * exp (-z t * (r - R)))) (Ioi R) :=
      integrable_finsetSum _ (fun t _ => (shifted_radius_exp_integrable (z t) R (hz t) hR).const_mul _)
    apply hi.congr_fun _ measurableSet_Ioi
    intro r hr
    dsimp only [c]
    rw [correlation_exterior_of_root z hz rho sigma K Dt G hs hroot i j r hr, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    field_simp [(hR.trans_lt hr).ne']
    ring
  have he : Ioi (0 : ℝ) = Ioc 0 R ∪ Ioi R := by
    ext r
    simp only [mem_Ioi, mem_Ioc, mem_union]
    constructor
    · intro hr
      by_cases h : r ≤ R
      · exact Or.inl ⟨hr, h⟩
      · exact Or.inr (not_le.mp h)
    · rintro (⟨hr, _⟩ | hr)
      · exact hr
      · exact hR.trans_lt hr
  change IntegrableOn (fun r => r ^ 2 * c r) (Ioi 0)
  rw [he, integrableOn_union]
  exact ⟨hcore, htail⟩

theorem ordered_radius_sq_integrable_of_root (z : T → ℝ) (hz : ∀ t, 0 < z t)
    (rho sigma : Fin N → ℝ) (K Dt G : TailMatrix T N) (hs : ∀ i, 0 ≤ sigma i)
    (hroot : IsRoot z rho sigma K Dt G) (i j : Fin N) :
    IntegrableOn (fun r => r ^ 2 * orderedRadialCorrelation z rho sigma K Dt G i j r) (Ioi 0) := by
  unfold orderedRadialCorrelation
  split_ifs with horder
  · exact correlation_radius_sq_integrable_of_root z hz rho sigma K Dt G hs hroot i j horder
  · exact correlation_radius_sq_integrable_of_root z hz rho sigma K Dt G hs hroot j i
      (lt_of_not_ge horder).le

theorem actual_radialSymbol_continuous (z : T → ℝ) (hz : ∀ t, 0 < z t)
    (rho sigma : Fin N → ℝ) (K Dt G : TailMatrix T N) (hs : ∀ i, 0 ≤ sigma i)
    (hroot : IsRoot z rho sigma K Dt G) (i j : Fin N) :
    Continuous (radialSymbol (orderedRadialCorrelation z rho sigma K Dt G i j)) :=
  radialSymbol_continuous _ (ordered_radius_sq_integrable_of_root z hz rho sigma K Dt G hs hroot i j)

/-- Equality at every real wave number, using the continuous sinc symbol at zero. -/
theorem root_radial_symbol (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (K Dt G : TailMatrix T N) (hz : ∀ u, 0 < z u)
    (hs : ∀ i, 0 < sigma i) (hv : vacMix rho sigma ≠ 0)
    (hroot : IsRoot z rho sigma K Dt G) (hK : ∀ u i j, K u i j = K u j i)
    (k : ℝ) (i j : Fin N) :
    spectralBaxterC z rho sigma (amplitudeA z rho sigma Dt G)
      (amplitudeQp z rho sigma Dt G) (W z rho Dt G) (C z rho sigma Dt G) k i j =
      (radialSymbol (orderedRadialCorrelation z rho sigma K Dt G i j) k : ℂ) := by
  have he : ∀ x : ℝ, x ≠ 0 →
      spectralBaxterC z rho sigma (amplitudeA z rho sigma Dt G)
        (amplitudeQp z rho sigma Dt G) (W z rho Dt G) (C z rho sigma Dt G) x i j =
        (radialSymbol (orderedRadialCorrelation z rho sigma K Dt G i j) x : ℂ) := by
    intro x hx
    rw [radialSymbol_eq_radial_fourier _ x hx]
    exact ActualRadialIdentification.root_radial_fourier z rho sigma K Dt G hz hs hv hroot hK x hx i j
  by_cases hk : k = 0
  · subst k
    have hleft := (spectralBaxterC_continuous z hz rho sigma
      (amplitudeA z rho sigma Dt G) (amplitudeQp z rho sigma Dt G)
      (W z rho Dt G) (C z rho sigma Dt G) (fun i => (hs i).le) i j).continuousAt (x := (0 : ℝ)) |>.tendsto
    have hright := (Complex.continuous_ofReal.comp
      (actual_radialSymbol_continuous z hz rho sigma K Dt G (fun i => (hs i).le) hroot i j)).continuousAt (x := (0 : ℝ)) |>.tendsto
    have hevent : (fun x => spectralBaxterC z rho sigma (amplitudeA z rho sigma Dt G)
        (amplitudeQp z rho sigma Dt G) (W z rho Dt G) (C z rho sigma Dt G) x i j) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun x => (radialSymbol (orderedRadialCorrelation z rho sigma K Dt G i j) x : ℂ)) := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact he x (ne_of_gt hx)
    exact tendsto_nhds_unique (hleft.mono_left nhdsWithin_le_nhds)
      ((hright.mono_left nhdsWithin_le_nhds).congr' hevent.symm)
  · exact he k hk

/-- The zero mode is the actual absolutely integrable second radial moment. -/
theorem root_zero_moment (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (K Dt G : TailMatrix T N) (hz : ∀ u, 0 < z u)
    (hs : ∀ i, 0 < sigma i) (hv : vacMix rho sigma ≠ 0)
    (hroot : IsRoot z rho sigma K Dt G) (hK : ∀ u i j, K u i j = K u j i)
    (i j : Fin N) :
    spectralBaxterC z rho sigma (amplitudeA z rho sigma Dt G)
      (amplitudeQp z rho sigma Dt G) (W z rho Dt G) (C z rho sigma Dt G) 0 i j =
      ((4 * π * ∫ r in Ioi (0 : ℝ),
        r ^ 2 * orderedRadialCorrelation z rho sigma K Dt G i j r : ℝ) : ℂ) := by
  rw [root_radial_symbol z rho sigma K Dt G hz hs hv hroot hK 0 i j, radialSymbol_zero]

/-- The actual radial symbol supplies the physical density-weighted Gram identity,
including k=0. No inverse structure factor is postulated. -/
theorem root_factor_gram_radial (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (K Dt G : TailMatrix T N) (hz : ∀ u, 0 < z u)
    (hr : ∀ i, 0 ≤ rho i) (hs : ∀ i, 0 < sigma i) (hv : vacMix rho sigma ≠ 0)
    (hroot : IsRoot z rho sigma K Dt G) (hK : ∀ u i j, K u i j = K u j i) (k : ℝ) :
    let F := fourierFactor z rho sigma (amplitudeA z rho sigma Dt G)
      (amplitudeQp z rho sigma Dt G) (W z rho Dt G) (C z rho sigma Dt G) k
    F * F.conjTranspose = 1 - Matrix.of (fun i j =>
      (sqrt (rho i) : ℂ) * (sqrt (rho j) : ℂ) *
        (radialSymbol (orderedRadialCorrelation z rho sigma K Dt G i j) k : ℂ)) := by
  dsimp only
  rw [fourierFactor_gram_eq z rho sigma _ _ _ _ k hr]
  congr 1
  ext i j
  rw [Matrix.of_apply, Matrix.of_apply, root_radial_symbol z rho sigma K Dt G hz hs hv hroot hK k i j]

/-- Actual one-species compressibility denominator, with arbitrary finite tails. -/
theorem scalar_radial_den_zero (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin 1 → ℝ) (K Dt G : T → Matrix (Fin 1) (Fin 1) ℝ)
    (hs : 0 < sigma 0) (hv : vacMix rho sigma ≠ 0)
    (hroot : IsRoot z rho sigma K Dt G) :
    1 - rho 0 * radialSymbol (orderedRadialCorrelation z rho sigma K Dt G 0 0) 0 =
      (amplitudeA z rho sigma Dt G 0 / (2 * π)) ^ 2 := by
  have hsall : ∀ i : Fin 1, 0 < sigma i := fun i => by fin_cases i; exact hs
  have hK : ∀ u (i j : Fin 1), K u i j = K u j i := by
    intro u i j; fin_cases i; fin_cases j; rfl
  have he := BaxterZeroMode.scalar_spectral_den_zero z hz rho sigma Dt G hs.le hv
  rw [root_radial_symbol z rho sigma K Dt G hz hsall hv hroot hK 0 0 0] at he
  exact_mod_cast he

theorem scalar_radial_den_zero_iff (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin 1 → ℝ) (K Dt G : T → Matrix (Fin 1) (Fin 1) ℝ)
    (hs : 0 < sigma 0) (hv : vacMix rho sigma ≠ 0)
    (hroot : IsRoot z rho sigma K Dt G) :
    1 - rho 0 * radialSymbol (orderedRadialCorrelation z rho sigma K Dt G 0 0) 0 = 0 ↔
      amplitudeA z rho sigma Dt G 0 = 0 := by
  rw [scalar_radial_den_zero z hz rho sigma K Dt G hs hv hroot, sq_eq_zero_iff]
  simp only [div_eq_zero_iff, mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) pi_ne_zero, or_false]

/-- Every physical positive one-tail state has an actual zero-frequency DCF
moment witness strictly inside the common Taylor disk of the PY germ. -/
theorem actual_single_tail_zero_moment_before_radius [Unique T]
    (z : T → ℝ) (rho sigma : Fin 1 → ℝ) (K : TailMatrix T 1)
    (hz : 0 < z default) (hr : 0 < rho 0) (hs : 0 < sigma 0)
    (hv : 0 < vacMix rho sigma) (hk : 0 < K default 0 0)
    (p : ℝ → TailMatrix T 1 × TailMatrix T 1)
    (hp : ContinuousAt p 0) (hp0 : p 0 = (0, baseSeed z rho sigma))
    (hroot : ∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K) (p t).1 (p t).2) :
    ∃ t : ℝ, 0 < t ∧ ENNReal.ofReal t < FoldRadius.amplitudeRadius (TaylorRoot.branchCoefficients p) ∧
      IsRoot z rho sigma (t • K) (SingleTailRadius.physBranch z rho sigma K t).1
        (SingleTailRadius.physBranch z rho sigma K t).2 ∧
      4 * π * rho 0 * ∫ r in Ioi (0 : ℝ), r ^ 2 * orderedRadialCorrelation z rho sigma
        (t • K) (SingleTailRadius.physBranch z rho sigma K t).1
          (SingleTailRadius.physBranch z rho sigma K t).2 0 0 r = 1 := by
  obtain ⟨t, ht, hR, hrt, hA⟩ := SingleTailSpinodal.actual_single_tail_zero_lt_radius
    z rho sigma K hz hr hs hv hk p hp hp0 hroot
  have hzall : ∀ u, 0 < z u := fun u => by simpa only [Subsingleton.elim u default] using hz
  have hactualA : amplitudeA z rho sigma (SingleTailRadius.physBranch z rho sigma K t).1
      (SingleTailRadius.physBranch z rho sigma K t).2 0 = 0 := by
    unfold SingleTailRadius.physBranch
    rw [BaxterZeroMode.single_tail_amplitudeA_eq]
    exact hA
  have hden := (scalar_radial_den_zero_iff z hzall rho sigma (t • K)
    (SingleTailRadius.physBranch z rho sigma K t).1
    (SingleTailRadius.physBranch z rho sigma K t).2 hs hv.ne' hrt).mpr hactualA
  rw [radialSymbol_zero] at hden
  refine ⟨t, ht, hR, hrt, ?_⟩
  nlinarith only [hden]

end FMSA.Paper.RadialZeroMode

/-- info: 'FMSA.Paper.RadialZeroMode.radialSymbol_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.RadialZeroMode.radialSymbol_zero

/-- info: 'FMSA.Paper.RadialZeroMode.radialSymbol_eq_radial_fourier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.RadialZeroMode.radialSymbol_eq_radial_fourier

/-- info: 'FMSA.Paper.RadialZeroMode.weighted_sinc_integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.RadialZeroMode.weighted_sinc_integrable

/-- info: 'FMSA.Paper.RadialZeroMode.radialSymbol_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.RadialZeroMode.radialSymbol_continuous

/-- info: 'FMSA.Paper.RadialZeroMode.fourierQ_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.RadialZeroMode.fourierQ_continuous

/-- info: 'FMSA.Paper.RadialZeroMode.spectralBaxterC_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.RadialZeroMode.spectralBaxterC_continuous

/-- info: 'FMSA.Paper.RadialZeroMode.shifted_radius_exp_integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.RadialZeroMode.shifted_radius_exp_integrable

/-- info: 'FMSA.Paper.RadialZeroMode.correlation_radius_sq_integrable_of_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.RadialZeroMode.correlation_radius_sq_integrable_of_root

/-- info: 'FMSA.Paper.RadialZeroMode.ordered_radius_sq_integrable_of_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.RadialZeroMode.ordered_radius_sq_integrable_of_root

/-- info: 'FMSA.Paper.RadialZeroMode.actual_radialSymbol_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.RadialZeroMode.actual_radialSymbol_continuous

/-- info: 'FMSA.Paper.RadialZeroMode.root_radial_symbol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.RadialZeroMode.root_radial_symbol

/-- info: 'FMSA.Paper.RadialZeroMode.root_zero_moment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.RadialZeroMode.root_zero_moment

/-- info: 'FMSA.Paper.RadialZeroMode.root_factor_gram_radial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.RadialZeroMode.root_factor_gram_radial

/-- info: 'FMSA.Paper.RadialZeroMode.scalar_radial_den_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.RadialZeroMode.scalar_radial_den_zero

/-- info: 'FMSA.Paper.RadialZeroMode.scalar_radial_den_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.RadialZeroMode.scalar_radial_den_zero_iff

/-- info: 'FMSA.Paper.RadialZeroMode.actual_single_tail_zero_moment_before_radius' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.RadialZeroMode.actual_single_tail_zero_moment_before_radius
