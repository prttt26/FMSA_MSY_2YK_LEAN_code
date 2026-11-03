import MSAConvergence.PureFluidSingleTailLossCounterexample
import MSAConvergence.ComplexPolynomialSystem

set_option linter.style.header false

/-! A negative real coupling gives a genuine one-tail BH root beyond the
Taylor radius of the positive-tail HS seed germ. This refutes the unrestricted
real-coupling root/convergence equivalence, without asserting a counterexample
on the physical positive-coupling attractive path. -/
noncomputable section
namespace FMSA.Convergence.SingleTailNegativeCouplingCounterexample

open Real
open FMSA.Paper.QuarticBranch
open FMSA.Paper.FoldRadius
open FMSA.Paper.SingleTailRadius
open FMSA.Paper.SingleTail
open FMSA.Paper.TaylorRoot
open FMSA.ExactMSA.MultiTailMixture
open FMSA.Convergence.ComplexPolynomialSystem
open FMSA.Convergence.PureFluidScalarMixtureBridge
open scoped ENNReal
open scoped Topology

/-- The one-tail quartic takes arbitrarily negative values to the left of
its HS seed parameter. The explicit witness avoids an asymptotic axiom. -/
theorem quartic_negative_unbounded (a b L f : ℝ)
    (hab : a < b) (hb : b < 0) (hL : 0 < L) (hf : 0 < f) :
    ∃ u : ℝ, u < a ∧ FMSA.Paper.QuarticBranch.q a b L u < -f := by
  let n : ℝ := f / L + 2
  let u : ℝ := a - n
  have hn : 2 < n := by
    have hdiv : 0 < f / L := div_pos hf hL
    dsimp [n]
    linarith
  have ha : a < 0 := hab.trans hb
  have hu : u < a := by dsimp [u]; linarith
  have hu0 : u < -2 := by dsimp [u]; linarith
  have hbu : b - u > 2 := by dsimp [u, n]; linarith
  have hau : a - u > 2 := by dsimp [u]; linarith
  have hsq : 1 < u ^ 2 := by nlinarith
  have hprod : 1 < (u - a) * (u - b) := by nlinarith
  have hbig : f < L * n := by
    dsimp [n]
    field_simp
    nlinarith
  refine ⟨u, hu, ?_⟩
  unfold FMSA.Paper.QuarticBranch.q
  have htotal : n < u ^ 2 * ((u - a) * (u - b)) := by
    nlinarith [mul_pos (show 0 < u ^ 2 - 1 by linarith) (show 0 < (u-a)*(u-b)-n by nlinarith)]
  nlinarith [mul_lt_mul_of_pos_left htotal hL]

/-- If the finite BH amplitude vector series is summable at a real
coupling, that coupling lies within its common component Taylor radius. -/
theorem radius_ge_of_vector_summable {T : Type*} [Fintype T] {N : ℕ}
    (a : ℕ → TailMatrix T N × TailMatrix T N) (tau : ℝ)
    (hs : Summable (fun n => tau ^ n • a n)) :
    ENNReal.ofReal |tau| ≤ amplitudeRadius a := by
  have hnorm : (‖tau‖₊ : ENNReal) = ENNReal.ofReal |tau| := by
    have hreal : ‖tau‖₊ = (⟨|tau|, abs_nonneg tau⟩ : NNReal) := by
      ext
      exact Real.norm_eq_abs tau
    rw [hreal]
    exact (ENNReal.ofReal_eq_coe_nnreal (abs_nonneg tau)).symm
  unfold amplitudeRadius
  apply le_iInf
  intro u
  apply le_iInf
  intro i
  apply le_iInf
  intro j
  apply le_min
  · let l : (TailMatrix T N × TailMatrix T N) →L[ℝ] ℝ :=
      (entry u i j).comp (ContinuousLinearMap.fst ℝ _ _)
    have hcomp : Summable (fun n => (a n).1 u i j * tau ^ n) := by
      convert l.summable hs using 1
      ext n
      simp [l, entry, smul_eq_mul, mul_comm]
    by_contra hnot
    have hlt : (FormalMultilinearSeries.ofScalars ℝ
        (fun n => (a n).1 u i j)).radius < (‖tau‖₊ : ENNReal) := by
      rw [hnorm]
      exact lt_of_not_ge hnot
    exact (real_not_summable_of_radius_lt_norm _ tau hlt)
      (by simpa [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, mul_comm] using hcomp)

  · let l : (TailMatrix T N × TailMatrix T N) →L[ℝ] ℝ :=
      (entry u i j).comp (ContinuousLinearMap.snd ℝ _ _)
    have hcomp : Summable (fun n => (a n).2 u i j * tau ^ n) := by
      convert l.summable hs using 1
      ext n
      simp [l, entry, smul_eq_mul, mul_comm]
    by_contra hnot
    have hlt : (FormalMultilinearSeries.ofScalars ℝ
        (fun n => (a n).2 u i j)).radius < (‖tau‖₊ : ENNReal) := by
      rw [hnorm]
      exact lt_of_not_ge hnot
    exact (real_not_summable_of_radius_lt_norm _ tau hlt)
      (by simpa [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, mul_comm] using hcomp)

/-- The original one-tail BH equations have a real root at every negative
coupling of a positive tail. This is a quartic intermediate-value fact,
independent of Taylor convergence. -/
theorem negative_exact_root_at_every_coupling
    (z : Fin 1 → ℝ) (rho sigma : Fin 1 → ℝ)
    (K : TailMatrix (Fin 1) 1)
    (hz : 0 < z 0) (hr : 0 < rho 0) (hs : 0 < sigma 0)
    (hv : 0 < FMSA.MatrixQ0.vacMix rho sigma)
    (hk : 0 < K 0 0 0)
    (tau : ℝ) (htau : tau < 0) :
    ∃ D G : TailMatrix (Fin 1) 1,
      IsRoot z rho sigma (tau • K) D G := by
  have hab : aR z rho sigma < bR z rho sigma :=
    FMSA.Paper.SingleTailRadius.hab z rho sigma hz hr hs hv
  have hb : bR z rho sigma < 0 :=
    FMSA.Paper.SingleTailRadius.hb z rho sigma hz hr hs hv
  have hL : 0 < LR z rho sigma K :=
    FMSA.Paper.SingleTailRadius.hL z rho sigma K hz hr hs hv hk
  obtain ⟨u0, hu0, hq0⟩ := quartic_negative_unbounded
    (aR z rho sigma) (bR z rho sigma) (LR z rho sigma K)
    (-tau) hab hb hL (by linarith)
  have hcont : ContinuousOn
      (FMSA.Paper.QuarticBranch.q (aR z rho sigma) (bR z rho sigma)
        (LR z rho sigma K)) (Set.Icc u0 (aR z rho sigma)) := by
    intro u _
    exact (FMSA.Paper.QuarticBranch.hasDerivAt_q hab hb u).continuousAt.continuousWithinAt
  have htarget : tau ∈ Set.Icc
      (FMSA.Paper.QuarticBranch.q (aR z rho sigma) (bR z rho sigma)
        (LR z rho sigma K) u0)
      (FMSA.Paper.QuarticBranch.q (aR z rho sigma) (bR z rho sigma)
        (LR z rho sigma K) (aR z rho sigma)) := by
    rw [FMSA.Paper.QuarticBranch.q_a]
    constructor <;> linarith
  obtain ⟨u, hu, hqu⟩ := intermediate_value_Icc hu0.le hcont htarget
  have hu_ne : u ≠ 0 := by
    have ha : aR z rho sigma < 0 := hab.trans hb
    linarith [hu.2]
  have hK : ∀ v i j, K v i j = K 0 0 0 := by
    intro v i j
    simp only [Subsingleton.elim v 0,
      Subsingleton.elim i 0, Subsingleton.elim j 0]
  have hroot : IsRoot z rho sigma
      ((FMSA.Paper.SingleTail.tauS (z 0) (rho 0) (sigma 0) (K 0 0 0) u) • K)
      (sc (DtS (z 0) (rho 0) (sigma 0) u))
      (sc (GS (z 0) (rho 0) (sigma 0) u)) :=
    isRoot_param z rho sigma K (K 0 0 0) hK hz.ne' hs.ne' hr.ne'
      (FMSA.Paper.SingleTailRadius.hw z rho sigma hz hr hs hv).ne'
      hk.ne' (FMSA.Paper.SingleTailRadius.hDd z rho sigma hz hr hs hv).ne' u hu_ne
  have heq : FMSA.Paper.SingleTail.tauS
      (z 0) (rho 0) (sigma 0) (K 0 0 0) u = tau := by
    change FMSA.Paper.QuarticBranch.q
      (aR z rho sigma) (bR z rho sigma) (LR z rho sigma K) u = tau
    exact hqu
  rw [heq] at hroot
  exact ⟨_, _, hroot⟩

/-- A repulsive one-tail mixture has a real Exact MSA root for every
positive coupling, even though its HS Taylor series has finite radius. -/
theorem repulsive_exact_root_at_every_positive_coupling
    (z : Fin 1 → ℝ) (rho sigma : Fin 1 → ℝ)
    (K : TailMatrix (Fin 1) 1)
    (hz : 0 < z 0) (hr : 0 < rho 0) (hs : 0 < sigma 0)
    (hv : 0 < FMSA.MatrixQ0.vacMix rho sigma)
    (hk : 0 < K 0 0 0)
    (tau : ℝ) (htau : 0 < tau) :
    ∃ D G : TailMatrix (Fin 1) 1,
      IsRoot z rho sigma (tau • (-K)) D G := by
  obtain ⟨D, G, hroot⟩ := negative_exact_root_at_every_coupling
    z rho sigma K hz hr hs hv hk (-tau) (by linarith)
  refine ⟨D, G, ?_⟩
  convert hroot using 1
  funext t i j
  simp [Pi.smul_apply, Pi.neg_apply, smul_eq_mul]

/-- Reflection of the real coupling axis multiplies each original BH
Taylor coefficient by the expected parity sign. -/
theorem branchCoefficients_reflected {T : Type*} [Fintype T] {N : ℕ}
    (p : ℝ → TailMatrix T N × TailMatrix T N) (n : ℕ) :
    branchCoefficients (fun t => p (-t)) n =
      (-1 : ℝ) ^ n • branchCoefficients p n := by
  apply Prod.ext <;> funext u i j
  · simp only [branchCoefficients, FMSA.ExactMSA.BSource.jet,
      Pi.smul_apply, Prod.smul_fst, smul_eq_mul]
    have hd := iteratedDeriv_comp_neg n (fun t => (p t).1 u i j) 0
    simpa only [neg_zero, smul_eq_mul, mul_div_assoc] using
      congrArg (fun x : ℝ => x / ↑n.factorial) hd
  · simp only [branchCoefficients, FMSA.ExactMSA.BSource.jet,
      Pi.smul_apply, Prod.smul_snd, smul_eq_mul]
    have hd := iteratedDeriv_comp_neg n (fun t => (p t).2 u i j) 0
    simpa only [neg_zero, smul_eq_mul, mul_div_assoc] using
      congrArg (fun x : ℝ => x / ↑n.factorial) hd

/-- Alternating coefficient signs do not change the scalar power-series
radius, because every coefficient norm is unchanged. -/
theorem scalar_radius_reflected (a : ℕ → ℝ) :
    (FormalMultilinearSeries.ofScalars ℝ
      (fun n => (-1 : ℝ) ^ n * a n)).radius =
    (FormalMultilinearSeries.ofScalars ℝ a).radius := by
  apply le_antisymm
  · apply FormalMultilinearSeries.radius_le_of_le
    intro n
    simp [norm_mul]
  · apply FormalMultilinearSeries.radius_le_of_le
    intro n
    simp [norm_mul]

/-- Reflection of the real coupling axis preserves the common radius of
all original finite BH amplitude coefficients. -/
theorem amplitudeRadius_reflected {T : Type*} [Fintype T] {N : ℕ}
    (p : ℝ → TailMatrix T N × TailMatrix T N) :
    amplitudeRadius (branchCoefficients (fun t => p (-t))) =
      amplitudeRadius (branchCoefficients p) := by
  unfold amplitudeRadius
  apply iInf_congr
  intro u
  apply iInf_congr
  intro i
  apply iInf_congr
  intro j
  simp only [branchCoefficients_reflected, Prod.smul_fst, Prod.smul_snd,
    Pi.smul_apply, smul_eq_mul]
  rw [scalar_radius_reflected, scalar_radius_reflected]

/-- The repulsive one-tail HS germ has the same exact original-amplitude
Taylor radius as the attractive germ: the explicit positive fold scale. -/
theorem repulsive_hs_radius_eq_fold
    (z : Fin 1 → ℝ) (rho sigma : Fin 1 → ℝ)
    (K : TailMatrix (Fin 1) 1)
    (hz : 0 < z 0) (hr : 0 < rho 0) (hs : 0 < sigma 0)
    (hv : 0 < FMSA.MatrixQ0.vacMix rho sigma)
    (hk : 0 < K 0 0 0) :
    amplitudeRadius
      (branchCoefficients (fun t => physBranch z rho sigma K (-t))) =
      ENNReal.ofReal (foldCoupling z rho sigma K) := by
  rw [amplitudeRadius_reflected]
  exact single_tail_radius_eq_fold z rho sigma K hz hr hs hv hk
    (physBranch z rho sigma K)
    (physBranch_continuousAt z rho sigma K hz hr hs hv hk)
    (physBranch_zero z rho sigma K hz hr hs hv hk)
    (physBranch_local_root z rho sigma K hz hr hs hv hk)

/-- The reflected path is analytic at the HS seed and solves the MSA
equations locally for the repulsive tail `-K`. -/
theorem reflected_physBranch_hs_germ
    (z : Fin 1 → ℝ) (rho sigma : Fin 1 → ℝ)
    (K : TailMatrix (Fin 1) 1)
    (hz : 0 < z 0) (hr : 0 < rho 0) (hs : 0 < sigma 0)
    (hv : 0 < FMSA.MatrixQ0.vacMix rho sigma)
    (hk : 0 < K 0 0 0) :
    (fun t => physBranch z rho sigma K (-t)) 0 = (0, baseSeed z rho sigma) ∧
    AnalyticAt ℝ (fun t => physBranch z rho sigma K (-t)) 0 ∧
    ∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • (-K))
      (physBranch z rho sigma K (-t)).1
      (physBranch z rho sigma K (-t)).2 := by
  refine ⟨by simpa using physBranch_zero z rho sigma K hz hr hs hv hk, ?_, ?_⟩
  · have hneg : AnalyticAt ℝ (fun t : ℝ => -t) 0 := by
      have heq : (-(id : ℝ → ℝ)) = (fun t : ℝ => -t) := by
        funext t
        simp [id]
      rw [← heq]
      exact (analyticAt_neg (f := (id : ℝ → ℝ)) (x := (0 : ℝ))).mpr
        (analyticAt_id (𝕜 := ℝ) (z := (0 : ℝ)))
    have hphy : AnalyticAt ℝ (physBranch z rho sigma K) (-(0 : ℝ)) := by
      simpa only [neg_zero] using
        (physBranch_analyticAt z rho sigma K hz hr hs hv hk
          (zero_mem_Ioo z rho sigma K hz hr hs hv hk))
    simpa only [Function.comp_def, Pi.neg_apply, id_eq] using hphy.comp hneg
  · have hmap : Filter.Tendsto (fun t : ℝ => -t) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
      simpa using (continuous_neg.tendsto (0 : ℝ))
    filter_upwards [hmap.eventually
      (physBranch_local_root z rho sigma K hz hr hs hv hk)] with t ht
    convert ht using 1
    funext u i j
    simp [Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
/-- Data-constructed exact MSA counterexample on the negative real
coupling axis: the original BH equations have a real solution, while the
HS-seeded amplitude Taylor vector series is not summable there. -/
theorem exists_negative_exact_root_with_divergent_seed_series
    (z : Fin 1 → ℝ) (rho sigma : Fin 1 → ℝ)
    (K : TailMatrix (Fin 1) 1)
    (hz : 0 < z 0) (hr : 0 < rho 0) (hs : 0 < sigma 0)
    (hv : 0 < FMSA.MatrixQ0.vacMix rho sigma)
    (hk : 0 < K 0 0 0) :
    ∃ tau : ℝ, tau < 0 ∧
      (∃ D G : TailMatrix (Fin 1) 1,
        IsRoot z rho sigma (tau • K) D G) ∧
      ¬Summable (fun n => tau ^ n •
        branchCoefficients (physBranch z rho sigma K) n) := by
  have hab : aR z rho sigma < bR z rho sigma :=
    FMSA.Paper.SingleTailRadius.hab z rho sigma hz hr hs hv
  have hb : bR z rho sigma < 0 :=
    FMSA.Paper.SingleTailRadius.hb z rho sigma hz hr hs hv
  have hL : 0 < LR z rho sigma K :=
    FMSA.Paper.SingleTailRadius.hL z rho sigma K hz hr hs hv hk
  have hf : 0 < foldCoupling z rho sigma K :=
    foldCoupling_pos z rho sigma K hz hr hs hv hk
  obtain ⟨u, hu, hq⟩ := quartic_negative_unbounded
    (aR z rho sigma) (bR z rho sigma)
    (LR z rho sigma K) (foldCoupling z rho sigma K)
    hab hb hL hf
  let tau := FMSA.Paper.SingleTail.tauS (z 0) (rho 0) (sigma 0) (K 0 0 0) u
  have htau : tau = FMSA.Paper.QuarticBranch.q
      (aR z rho sigma) (bR z rho sigma) (LR z rho sigma K) u := rfl
  have htneg : tau < -foldCoupling z rho sigma K := by
    rw [htau]
    exact hq
  have hu0 : u ≠ 0 := by
    have ha : aR z rho sigma < 0 := hab.trans hb
    linarith
  have hK : ∀ v i j, K v i j = K 0 0 0 := by
    intro v i j
    simp only [Subsingleton.elim v 0,
      Subsingleton.elim i 0, Subsingleton.elim j 0]
  have hroot : IsRoot z rho sigma (tau • K)
      (sc (DtS (z 0) (rho 0) (sigma 0) u))
      (sc (GS (z 0) (rho 0) (sigma 0) u)) := by
    exact isRoot_param z rho sigma K (K 0 0 0) hK hz.ne' hs.ne' hr.ne'
      (FMSA.Paper.SingleTailRadius.hw z rho sigma hz hr hs hv).ne'
      hk.ne' (FMSA.Paper.SingleTailRadius.hDd z rho sigma hz hr hs hv).ne' u hu0
  have hradius : amplitudeRadius
      (branchCoefficients (physBranch z rho sigma K)) =
      ENNReal.ofReal (foldCoupling z rho sigma K) :=
    single_tail_radius_eq_fold z rho sigma K hz hr hs hv hk
      (physBranch z rho sigma K)
      (physBranch_continuousAt z rho sigma K hz hr hs hv hk)
      (physBranch_zero z rho sigma K hz hr hs hv hk)
      (physBranch_local_root z rho sigma K hz hr hs hv hk)
  have hfoldAbs : foldCoupling z rho sigma K < |tau| := by
    have htneg0 : tau < 0 := by linarith
    rw [abs_of_neg htneg0]
    linarith
  have hradlt : amplitudeRadius
      (branchCoefficients (physBranch z rho sigma K)) <
      ENNReal.ofReal |tau| := by
    rw [hradius]
    exact (ENNReal.ofReal_lt_ofReal_iff (hf.trans hfoldAbs)).mpr hfoldAbs
  refine ⟨tau, by linarith, ⟨_, _, hroot⟩, ?_⟩
  intro hsum
  exact (not_le_of_gt hradlt)
    (radius_ge_of_vector_summable
      (branchCoefficients (physBranch z rho sigma K)) tau hsum)

/-- The real root persists at every negative coupling, while the
HS-seeded vector series diverges at every point strictly outside its
exact one-tail Taylor radius. -/
theorem negative_root_and_divergence_beyond_fold
    (z : Fin 1 → ℝ) (rho sigma : Fin 1 → ℝ)
    (K : TailMatrix (Fin 1) 1)
    (hz : 0 < z 0) (hr : 0 < rho 0) (hs : 0 < sigma 0)
    (hv : 0 < FMSA.MatrixQ0.vacMix rho sigma)
    (hk : 0 < K 0 0 0)
    (tau : ℝ) (htau : tau < -foldCoupling z rho sigma K) :
    (∃ D G : TailMatrix (Fin 1) 1,
      IsRoot z rho sigma (tau • K) D G) ∧
    ¬Summable (fun n => tau ^ n •
      branchCoefficients (physBranch z rho sigma K) n) := by
  have hf : 0 < foldCoupling z rho sigma K :=
    foldCoupling_pos z rho sigma K hz hr hs hv hk
  have hroot := negative_exact_root_at_every_coupling
    z rho sigma K hz hr hs hv hk tau (by linarith)
  have hradius : amplitudeRadius
      (branchCoefficients (physBranch z rho sigma K)) =
      ENNReal.ofReal (foldCoupling z rho sigma K) :=
    single_tail_radius_eq_fold z rho sigma K hz hr hs hv hk
      (physBranch z rho sigma K)
      (physBranch_continuousAt z rho sigma K hz hr hs hv hk)
      (physBranch_zero z rho sigma K hz hr hs hv hk)
      (physBranch_local_root z rho sigma K hz hr hs hv hk)
  have hfoldAbs : foldCoupling z rho sigma K < |tau| := by
    rw [abs_of_neg (by linarith : tau < 0)]
    linarith
  have hradlt : amplitudeRadius
      (branchCoefficients (physBranch z rho sigma K)) <
      ENNReal.ofReal |tau| := by
    rw [hradius]
    exact (ENNReal.ofReal_lt_ofReal_iff (hf.trans hfoldAbs)).mpr hfoldAbs
  refine ⟨hroot, ?_⟩
  intro hsum
  exact (not_le_of_gt hradlt)
    (radius_ge_of_vector_summable
      (branchCoefficients (physBranch z rho sigma K)) tau hsum)

/-- For every positive coupling beyond the one-tail radius, a repulsive
tail has an exact MSA root although its HS-seeded Taylor vector diverges. -/
theorem repulsive_root_and_divergence_beyond_radius
    (z : Fin 1 → ℝ) (rho sigma : Fin 1 → ℝ)
    (K : TailMatrix (Fin 1) 1)
    (hz : 0 < z 0) (hr : 0 < rho 0) (hs : 0 < sigma 0)
    (hv : 0 < FMSA.MatrixQ0.vacMix rho sigma)
    (hk : 0 < K 0 0 0)
    (tau : ℝ) (htau : foldCoupling z rho sigma K < tau) :
    (∃ D G : TailMatrix (Fin 1) 1,
      IsRoot z rho sigma (tau • (-K)) D G) ∧
    ¬Summable (fun n => tau ^ n •
      branchCoefficients (fun t => physBranch z rho sigma K (-t)) n) := by
  obtain ⟨⟨D, G, hroot⟩, hdiv⟩ :=
    negative_root_and_divergence_beyond_fold
      z rho sigma K hz hr hs hv hk (-tau) (by linarith)
  refine ⟨⟨D, G, ?_⟩, ?_⟩
  · convert hroot using 1
    funext t i j
    simp [Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  · have hseries : (fun n => tau ^ n •
        branchCoefficients (fun t => physBranch z rho sigma K (-t)) n) =
        (fun n => (-tau) ^ n • branchCoefficients (physBranch z rho sigma K) n) := by
      funext n
      rw [branchCoefficients_reflected]
      simp [smul_smul, ← mul_pow]
    simpa only [hseries] using hdiv

/-- For the repulsive tail `-K`, a positive coupling admits a genuine
exact MSA root beyond the Taylor radius of the reflected HS seed branch. -/
theorem exists_positive_repulsive_exact_root_with_divergent_seed_series
    (z : Fin 1 → ℝ) (rho sigma : Fin 1 → ℝ)
    (K : TailMatrix (Fin 1) 1)
    (hz : 0 < z 0) (hr : 0 < rho 0) (hs : 0 < sigma 0)
    (hv : 0 < FMSA.MatrixQ0.vacMix rho sigma)
    (hk : 0 < K 0 0 0) :
    ∃ tau : ℝ, 0 < tau ∧
      (∃ D G : TailMatrix (Fin 1) 1,
        IsRoot z rho sigma (tau • (-K)) D G) ∧
      ¬Summable (fun n => tau ^ n •
        branchCoefficients (fun t => physBranch z rho sigma K (-t)) n) := by
  obtain ⟨tau, htneg, ⟨D, G, hroot⟩, hdiv⟩ :=
    exists_negative_exact_root_with_divergent_seed_series
      z rho sigma K hz hr hs hv hk
  refine ⟨-tau, by linarith, ⟨D, G, ?_⟩, ?_⟩
  · convert hroot using 1
    funext t i j
    simp [Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  · have hseries : (fun n => (-tau) ^ n •
        branchCoefficients (fun t => physBranch z rho sigma K (-t)) n) =
        (fun n => tau ^ n • branchCoefficients (physBranch z rho sigma K) n) := by
      funext n
      rw [branchCoefficients_reflected]
      simp [smul_smul, ← mul_pow]
    simpa only [hseries] using hdiv

/-- The same negative-coupling counterexample is a genuine pure-fluid
`MultiTail.IsRoot` after the proven one-species matrix dictionary. The
non-summable coefficients are the original one-species matrix BH amplitudes. -/
theorem exists_negative_pure_fluid_root_with_divergent_seed_series
    (xi : ℝ) (hxi0 : 0 < xi) (hxi1 : xi < 1)
    (z K : Fin 1 → ℝ) (hz : 0 < z 0) (hK : 0 < K 0) :
    ∃ tau : ℝ, tau < 0 ∧
      ∃ D G : Fin 1 → ℝ,
        FMSA.ExactMSA.MultiTail.IsRoot xi z
          (fun t => tau * K t) D G ∧
        ¬Summable (fun n => tau ^ n •
          branchCoefficients
            (physBranch z (rho1 xi) sigma1 (liftTail K)) n) := by
  have hr : 0 < rho1 xi 0 := by
    simp only [rho1, FMSA.ExactMSA.rhoOf]
    positivity
  have hs : 0 < sigma1 0 := by simp [sigma1]
  have hv : 0 < FMSA.MatrixQ0.vacMix (rho1 xi) sigma1 := by
    rw [vacMix_rho1_sigma1]
    linarith
  have hk : 0 < liftTail K 0 0 0 := by
    simpa only [liftTail] using hK
  obtain ⟨tau, htneg, ⟨D, G, hroot⟩, hdiv⟩ :=
    exists_negative_exact_root_with_divergent_seed_series
      z (rho1 xi) sigma1 (liftTail K) hz hr hs hv hk
  have hstrength : tau • liftTail K =
      liftTail (fun t => tau * K t) := by
    funext t i j
    simp [liftTail, Pi.smul_apply, smul_eq_mul]
  rw [hstrength, ← lift_lowerTail D, ← lift_lowerTail G] at hroot
  have hpure : FMSA.ExactMSA.MultiTail.IsRoot xi z
      (fun t => tau * K t) (lowerTail D) (lowerTail G) :=
    (isRoot_iff xi hxi1.ne z (fun t => tau * K t)
      (lowerTail D) (lowerTail G)).mp hroot
  exact ⟨tau, htneg, lowerTail D, lowerTail G, hpure, hdiv⟩

end FMSA.Convergence.SingleTailNegativeCouplingCounterexample

/-- info: 'FMSA.Convergence.SingleTailNegativeCouplingCounterexample.quartic_negative_unbounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.SingleTailNegativeCouplingCounterexample.quartic_negative_unbounded
/-- info: 'FMSA.Convergence.SingleTailNegativeCouplingCounterexample.radius_ge_of_vector_summable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.SingleTailNegativeCouplingCounterexample.radius_ge_of_vector_summable
/-- info: 'FMSA.Convergence.SingleTailNegativeCouplingCounterexample.negative_exact_root_at_every_coupling' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.SingleTailNegativeCouplingCounterexample.negative_exact_root_at_every_coupling
/-- info: 'FMSA.Convergence.SingleTailNegativeCouplingCounterexample.repulsive_exact_root_at_every_positive_coupling' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.SingleTailNegativeCouplingCounterexample.repulsive_exact_root_at_every_positive_coupling
/-- info: 'FMSA.Convergence.SingleTailNegativeCouplingCounterexample.branchCoefficients_reflected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.SingleTailNegativeCouplingCounterexample.branchCoefficients_reflected
/-- info: 'FMSA.Convergence.SingleTailNegativeCouplingCounterexample.scalar_radius_reflected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.SingleTailNegativeCouplingCounterexample.scalar_radius_reflected
/-- info: 'FMSA.Convergence.SingleTailNegativeCouplingCounterexample.amplitudeRadius_reflected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.SingleTailNegativeCouplingCounterexample.amplitudeRadius_reflected
/-- info: 'FMSA.Convergence.SingleTailNegativeCouplingCounterexample.repulsive_hs_radius_eq_fold' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.SingleTailNegativeCouplingCounterexample.repulsive_hs_radius_eq_fold
/-- info: 'FMSA.Convergence.SingleTailNegativeCouplingCounterexample.reflected_physBranch_hs_germ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.SingleTailNegativeCouplingCounterexample.reflected_physBranch_hs_germ
/-- info: 'FMSA.Convergence.SingleTailNegativeCouplingCounterexample.exists_negative_exact_root_with_divergent_seed_series' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.SingleTailNegativeCouplingCounterexample.exists_negative_exact_root_with_divergent_seed_series
/-- info: 'FMSA.Convergence.SingleTailNegativeCouplingCounterexample.negative_root_and_divergence_beyond_fold' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.SingleTailNegativeCouplingCounterexample.negative_root_and_divergence_beyond_fold
/-- info: 'FMSA.Convergence.SingleTailNegativeCouplingCounterexample.repulsive_root_and_divergence_beyond_radius' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.SingleTailNegativeCouplingCounterexample.repulsive_root_and_divergence_beyond_radius
/-- info: 'FMSA.Convergence.SingleTailNegativeCouplingCounterexample.exists_positive_repulsive_exact_root_with_divergent_seed_series' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.SingleTailNegativeCouplingCounterexample.exists_positive_repulsive_exact_root_with_divergent_seed_series
/-- info: 'FMSA.Convergence.SingleTailNegativeCouplingCounterexample.exists_negative_pure_fluid_root_with_divergent_seed_series' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.SingleTailNegativeCouplingCounterexample.exists_negative_pure_fluid_root_with_divergent_seed_series
