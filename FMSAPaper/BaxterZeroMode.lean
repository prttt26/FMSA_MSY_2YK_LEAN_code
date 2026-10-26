import LeanCode.YukawaOZMix.MSAMultiTailMixtureSpectral
import FMSAPaper.SingleTailSpinodal

/-! Actual zero-frequency Baxter integrals. The quotient closed form is
used only away from zero; these formulas evaluate the integral itself. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open scoped BigOperators

namespace FMSA.Paper.BaxterZeroMode
open ExactMSA.MultiTailMixture MSAMixture FMSA.ExactMSA.Breakpoint MatrixQ0

variable {N : ℕ} {T : Type*} [Fintype T]

def zeroMoment (z : T → ℝ) (sigma A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ)
    (W C : TailMatrix T N) (i j : Fin N) : ℝ :=
  -qp i j * sigma i ^ 2 / 2 + A j * sigma i ^ 3 / 6 +
    ∑ t, (W t i j / z t + C t i j * (sigma i + 1 / z t))

theorem core_zero_integral (sigma A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ)
    (i j : Fin N) (hs : 0 ≤ sigma i) :
    (∫ r, (Icc (edgeLo sigma i j) (edgeHi sigma i j)).indicator
      (qComplexPoly sigma A qp 0 i j) r) =
      ((-qp i j * sigma i ^ 2 / 2 + A j * sigma i ^ 3 / 6 : ℝ) : ℂ) := by
  have hle : edgeLo sigma i j ≤ edgeHi sigma i j := by unfold edgeLo edgeHi; linarith
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hle]
  simp only [qComplexPoly, zero_mul, neg_zero, Complex.exp_zero, mul_one]
  rw [intervalIntegral.integral_ofReal]
  congr 1
  have hp : (fun r : ℝ => qp i j * (r - edgeHi sigma i j) +
      A j / 2 * (r - edgeHi sigma i j) ^ 2) =
      fun r => (-qp i j * edgeHi sigma i j + A j * edgeHi sigma i j ^ 2 / 2) +
        (qp i j - A j * edgeHi sigma i j) * r + (A j / 2) * r ^ 2 + 0 * r ^ 3 := by
    funext r
    ring
  rw [hp, FMSA.FiniteYukawa.integral_cubic]
  unfold FMSA.FiniteYukawa.polyPrimitive edgeLo edgeHi
  ring

omit [Fintype T] in
theorem row_zero_integral (z : T → ℝ) (sigma : Fin N → ℝ) (W C : TailMatrix T N)
    (i j : Fin N) (t : T) (hz : 0 < z t) (hs : 0 ≤ sigma i) :
    (∫ r, qComplexRow z sigma W C 0 i j t r) =
      ((W t i j / z t + C t i j * (sigma i + 1 / z t) : ℝ) : ℂ) := by
  have hz0 : 0 < (0 : ℂ).re + z t := by simpa
  have hW : Integrable ((Ici (edgeLo sigma i j)).indicator
      (shiftedExpComplex (z t) (edgeLo sigma i j) 0)) :=
    ((integrableOn_Ici_iff_integrableOn_Ioi).mpr
      (shiftedExpComplex_integrable (z t) (edgeLo sigma i j) 0 hz0)).integrable_indicator
        measurableSet_Ici
  have hC : Integrable ((Icc (edgeLo sigma i j) (edgeHi sigma i j)).indicator
      (fun r : ℝ => Complex.exp (-(0 : ℂ) * r))) :=
    (by fun_prop : Continuous (fun r : ℝ => Complex.exp (-(0 : ℂ) * r))).integrableOn_Icc.integrable_indicator
      measurableSet_Icc
  have hT : Integrable ((Ioi (edgeHi sigma i j)).indicator
      (shiftedExpComplex (z t) (edgeHi sigma i j) 0)) :=
    (shiftedExpComplex_integrable (z t) (edgeHi sigma i j) 0 hz0).integrable_indicator measurableSet_Ioi
  have ha := hW.const_mul (W t i j : ℂ)
  have hb := hC.const_mul (C t i j : ℂ)
  have hc := hT.const_mul (C t i j : ℂ)
  have hab : Integrable (fun r => (W t i j : ℂ) * (Ici (edgeLo sigma i j)).indicator
      (shiftedExpComplex (z t) (edgeLo sigma i j) 0) r +
      (C t i j : ℂ) * (Icc (edgeLo sigma i j) (edgeHi sigma i j)).indicator
      (fun r => Complex.exp (-(0 : ℂ) * r)) r) := ha.add hb
  have hle : edgeLo sigma i j ≤ edgeHi sigma i j := by unfold edgeLo edgeHi; linarith
  unfold qComplexRow
  rw [integral_add hab hc, integral_add ha hb,
    integral_const_mul, integral_const_mul, integral_const_mul,
    integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
    shiftedExpComplex_integral _ _ _ hz0,
    integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hle,
    integral_indicator measurableSet_Ioi, shiftedExpComplex_integral _ _ _ hz0]
  simp only [zero_mul, neg_zero, Complex.exp_zero, zero_add,
    intervalIntegral.integral_const, Complex.real_smul, mul_one]
  push_cast
  unfold edgeLo edgeHi
  push_cast
  ring

theorem fourierQ_zero (z : T → ℝ) (hz : ∀ t, 0 < z t)
    (sigma A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ) (W C : TailMatrix T N)
    (hs : ∀ i, 0 ≤ sigma i) (i j : Fin N) :
    fourierQ z sigma A qp W C 0 i j = (zeroMoment z sigma A qp W C i j : ℂ) := by
  have ht : ∀ t, 0 < (0 : ℂ).re + z t := fun t => by simpa using hz t
  unfold fourierQ
  simp only [Complex.ofReal_zero, mul_zero]
  rw [q_complex_decomposition z sigma A qp W C hs 0 i j,
    integral_add (qComplexPoly_integrable sigma A qp 0 i j)
      (integrable_finsetSum _ (fun t _ => qComplexRow_integrable z sigma W C 0 i j t (ht t))),
    integral_finsetSum _ (fun t _ => qComplexRow_integrable z sigma W C 0 i j t (ht t)),
    core_zero_integral sigma A qp i j (hs i)]
  simp_rw [row_zero_integral z sigma W C i j _ (hz _) (hs i)]
  simp [zeroMoment]

theorem fourierFactor_zero_entry (z : T → ℝ) (hz : ∀ t, 0 < z t)
    (rho sigma A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ) (W C : TailMatrix T N)
    (hs : ∀ i, 0 ≤ sigma i) (i j : Fin N) :
    fourierFactor z rho sigma A qp W C 0 i j =
      (if i = j then 1 else 0) - (sqrt (rho i) : ℂ) * (sqrt (rho j) : ℂ) *
        (zeroMoment z sigma A qp W C i j : ℂ) := by
  simp only [fourierFactor, Matrix.sub_apply, Matrix.one_apply, Matrix.of_apply,
    fourierQ_zero z hz sigma A qp W C hs]

theorem scalar_HS_balance (rho sigma : Fin 1 → ℝ) (hv : vacMix rho sigma ≠ 0) :
    1 - rho 0 * (-Q0phys rho sigma 0 0 * sigma 0 ^ 2 / 2 +
      Qppphys rho sigma 0 0 * sigma 0 ^ 3 / 6) = Qppphys rho sigma 0 0 / (2 * π) := by
  have hpi : π ≠ 0 := pi_ne_zero
  simp only [Q0phys, Qppphys, xi2, Finset.univ_unique, Finset.sum_singleton,
    Fin.default_eq_zero, add_self_div_two]
  field_simp
  simp only [vacMix, etaMix, Finset.univ_unique, Finset.sum_singleton, Fin.default_eq_zero] at *
  ring

theorem scalar_tail_balance (z : ℝ) (hz : z ≠ 0) (rho sigma : Fin 1 → ℝ)
    (G Dt : Matrix (Fin 1) (Fin 1) ℝ) (hv : vacMix rho sigma ≠ 0) :
    -rho 0 * (-mixDqp z rho sigma G Dt 0 0 * sigma 0 ^ 2 / 2 +
      mixDA z rho sigma G Dt 0 * sigma 0 ^ 3 / 6 +
      Wt z rho G Dt 0 0 / z + Ct z rho sigma G Dt 0 0 * (sigma 0 + 1 / z)) =
      mixDA z rho sigma G Dt 0 / (2 * π) := by
  have hpi : π ≠ 0 := pi_ne_zero
  simp only [mixDA, mixDqp, mixM, mixN, Q0phys, Qppphys, xi2,
    Finset.univ_unique, Finset.sum_singleton, Fin.default_eq_zero, sub_self,
    zero_div, mul_zero, zero_mul, add_self_div_two]
  field_simp
  simp only [vacMix, etaMix, Finset.univ_unique, Finset.sum_singleton, Fin.default_eq_zero] at *
  ring

theorem scalar_zeroMoment_balance (z : T → ℝ) (hz : ∀ t, z t ≠ 0)
    (rho sigma : Fin 1 → ℝ) (Dt G : T → Matrix (Fin 1) (Fin 1) ℝ) (hv : vacMix rho sigma ≠ 0) :
    1 - rho 0 * zeroMoment z sigma (amplitudeA z rho sigma Dt G)
      (amplitudeQp z rho sigma Dt G) (W z rho Dt G) (C z rho sigma Dt G) 0 0 =
      amplitudeA z rho sigma Dt G 0 / (2 * π) := by
  have hsplit : zeroMoment z sigma (amplitudeA z rho sigma Dt G)
      (amplitudeQp z rho sigma Dt G) (W z rho Dt G) (C z rho sigma Dt G) 0 0 =
      (-Q0phys rho sigma 0 0 * sigma 0 ^ 2 / 2 + Qppphys rho sigma 0 0 * sigma 0 ^ 3 / 6) +
      ∑ t, (-mixDqp (z t) rho sigma (G t) (Dt t) 0 0 * sigma 0 ^ 2 / 2 +
        mixDA (z t) rho sigma (G t) (Dt t) 0 * sigma 0 ^ 3 / 6 +
        Wt (z t) rho (G t) (Dt t) 0 0 / z t +
        Ct (z t) rho sigma (G t) (Dt t) 0 0 * (sigma 0 + 1 / z t)) := by
    unfold zeroMoment amplitudeA amplitudeQp W C
    simp only [neg_mul, Finset.sum_add_distrib]
    ring_nf
    simp only [← Finset.sum_mul, ← Finset.mul_sum]
    ring
  rw [hsplit]
  calc
    _ = (1 - rho 0 * (-Q0phys rho sigma 0 0 * sigma 0 ^ 2 / 2 +
        Qppphys rho sigma 0 0 * sigma 0 ^ 3 / 6)) +
        ∑ t, -rho 0 * (-mixDqp (z t) rho sigma (G t) (Dt t) 0 0 * sigma 0 ^ 2 / 2 +
          mixDA (z t) rho sigma (G t) (Dt t) 0 * sigma 0 ^ 3 / 6 +
          Wt (z t) rho (G t) (Dt t) 0 0 / z t +
          Ct (z t) rho sigma (G t) (Dt t) 0 0 * (sigma 0 + 1 / z t)) := by
      rw [← Finset.mul_sum]
      ring
    _ = Qppphys rho sigma 0 0 / (2 * π) +
        ∑ t, mixDA (z t) rho sigma (G t) (Dt t) 0 / (2 * π) := by
      rw [scalar_HS_balance rho sigma hv]
      congr 1
      apply Finset.sum_congr rfl
      intro t _
      exact scalar_tail_balance (z t) (hz t) rho sigma (G t) (Dt t) hv
    _ = _ := by simp [amplitudeA, add_div, Finset.sum_div]

theorem scalar_fourierFactor_zero (z : T → ℝ) (hz : ∀ t, 0 < z t)
    (rho sigma : Fin 1 → ℝ) (Dt G : T → Matrix (Fin 1) (Fin 1) ℝ)
    (hr : 0 ≤ rho 0) (hs : 0 ≤ sigma 0) (hv : vacMix rho sigma ≠ 0) :
    fourierFactor z rho sigma (amplitudeA z rho sigma Dt G)
      (amplitudeQp z rho sigma Dt G) (W z rho Dt G) (C z rho sigma Dt G) 0 0 0 =
      ((amplitudeA z rho sigma Dt G 0 / (2 * π) : ℝ) : ℂ) := by
  have hsall : ∀ i : Fin 1, 0 ≤ sigma i := fun i => by fin_cases i; exact hs
  rw [fourierFactor_zero_entry z hz rho sigma _ _ _ _ hsall]
  simp only [ite_true]
  have hrho : (sqrt (rho 0) : ℂ) * (sqrt (rho 0) : ℂ) = (rho 0 : ℂ) := by
    norm_cast
    exact mul_self_sqrt hr
  rw [hrho]
  exact_mod_cast scalar_zeroMoment_balance z (fun t => (hz t).ne') rho sigma Dt G hv

theorem scalar_fourierFactor_zero_iff (z : T → ℝ) (hz : ∀ t, 0 < z t)
    (rho sigma : Fin 1 → ℝ) (Dt G : T → Matrix (Fin 1) (Fin 1) ℝ)
    (hr : 0 ≤ rho 0) (hs : 0 ≤ sigma 0) (hv : vacMix rho sigma ≠ 0) :
    fourierFactor z rho sigma (amplitudeA z rho sigma Dt G)
      (amplitudeQp z rho sigma Dt G) (W z rho Dt G) (C z rho sigma Dt G) 0 = 0 ↔
      amplitudeA z rho sigma Dt G 0 = 0 := by
  constructor
  · intro h
    have he := congrArg (fun M : Matrix (Fin 1) (Fin 1) ℂ => M 0 0) h
    rw [scalar_fourierFactor_zero z hz rho sigma Dt G hr hs hv] at he
    change ((amplitudeA z rho sigma Dt G 0 / (2 * π) : ℝ) : ℂ) = 0 at he
    have hq : amplitudeA z rho sigma Dt G 0 / (2 * π) = 0 := by exact_mod_cast he
    have hpi : π ≠ 0 := pi_ne_zero
    field_simp at hq
    simpa using hq
  · intro hA
    ext i j
    fin_cases i
    fin_cases j
    simp [scalar_fourierFactor_zero z hz rho sigma Dt G hr hs hv, hA]

theorem scalar_spectral_den_zero (z : T → ℝ) (hz : ∀ t, 0 < z t)
    (rho sigma : Fin 1 → ℝ) (Dt G : T → Matrix (Fin 1) (Fin 1) ℝ)
    (hs : 0 ≤ sigma 0) (hv : vacMix rho sigma ≠ 0) :
    1 - (rho 0 : ℂ) * spectralBaxterC z rho sigma (amplitudeA z rho sigma Dt G)
      (amplitudeQp z rho sigma Dt G) (W z rho Dt G) (C z rho sigma Dt G) 0 0 0 =
      (((amplitudeA z rho sigma Dt G 0 / (2 * π)) ^ 2 : ℝ) : ℂ) := by
  have hsall : ∀ i : Fin 1, 0 ≤ sigma i := fun i => by fin_cases i; exact hs
  calc
    _ = (((1 - rho 0 * zeroMoment z sigma (amplitudeA z rho sigma Dt G)
        (amplitudeQp z rho sigma Dt G) (W z rho Dt G) (C z rho sigma Dt G) 0 0) ^ 2 : ℝ) : ℂ) := by
      simp only [spectralBaxterC, fourierQ_zero z hz sigma _ _ _ _ hsall,
        Finset.univ_unique, Finset.sum_singleton, Fin.default_eq_zero,
        Complex.star_def, Complex.conj_ofReal]
      push_cast
      ring
    _ = _ := by rw [scalar_zeroMoment_balance z (fun t => (hz t).ne') rho sigma Dt G hv]

theorem single_tail_amplitudeA_eq [Unique T] (z : T → ℝ) (rho sigma : Fin 1 → ℝ)
    (d g : ℝ) :
    amplitudeA z rho sigma (SingleTail.sc d) (SingleTail.sc g) 0 =
      SingleTail.AS (z default) (rho 0) (sigma 0) d g := by
  simp only [amplitudeA, SingleTail.sc, mixDA, mixM, mixN, Wt, Ct, gam, sigMix,
    Finset.univ_unique, Finset.sum_singleton, Qppphys, xi2, vacMix, etaMix,
    SingleTail.QppS, SingleTail.xi2S, SingleTail.vacS, SingleTail.AS, SingleTail.MS,
    SingleTail.NS, SingleTail.WtS, SingleTail.CtS, SingleTail.gamS, SingleTail.Ez,
    if_true, sub_self, zero_div, mul_zero, Real.exp_zero, mul_one,
    Fin.default_eq_zero, add_self_div_two]
  ring_nf

theorem actual_single_tail_zero_before_radius [Unique T]
    (z : T → ℝ) (rho sigma : Fin 1 → ℝ) (K : TailMatrix T 1)
    (hz : 0 < z default) (hr : 0 < rho 0) (hs : 0 < sigma 0)
    (hv : 0 < vacMix rho sigma) (hk : 0 < K default 0 0)
    (p : ℝ → TailMatrix T 1 × TailMatrix T 1)
    (hp : ContinuousAt p 0) (hp0 : p 0 = (0, baseSeed z rho sigma))
    (hroot : ∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K) (p t).1 (p t).2) :
    ∃ t : ℝ, 0 < t ∧ ENNReal.ofReal t < FoldRadius.amplitudeRadius (TaylorRoot.branchCoefficients p) ∧
      IsRoot z rho sigma (t • K) (SingleTailRadius.physBranch z rho sigma K t).1
        (SingleTailRadius.physBranch z rho sigma K t).2 ∧
      (fourierFactor z rho sigma
        (amplitudeA z rho sigma (SingleTailRadius.physBranch z rho sigma K t).1
          (SingleTailRadius.physBranch z rho sigma K t).2)
        (amplitudeQp z rho sigma (SingleTailRadius.physBranch z rho sigma K t).1
          (SingleTailRadius.physBranch z rho sigma K t).2)
        (W z rho (SingleTailRadius.physBranch z rho sigma K t).1
          (SingleTailRadius.physBranch z rho sigma K t).2)
        (C z rho sigma (SingleTailRadius.physBranch z rho sigma K t).1
          (SingleTailRadius.physBranch z rho sigma K t).2) 0).det = 0 := by
  obtain ⟨t, ht, hR, hrt, hA⟩ := SingleTailSpinodal.actual_single_tail_zero_lt_radius
    z rho sigma K hz hr hs hv hk p hp hp0 hroot
  have hzall : ∀ u, 0 < z u := fun u => by simpa only [Subsingleton.elim u default] using hz
  have hactualA : amplitudeA z rho sigma (SingleTailRadius.physBranch z rho sigma K t).1
      (SingleTailRadius.physBranch z rho sigma K t).2 0 = 0 := by
    unfold SingleTailRadius.physBranch
    rw [single_tail_amplitudeA_eq]
    exact hA
  have hF := (scalar_fourierFactor_zero_iff z hzall rho sigma
    (SingleTailRadius.physBranch z rho sigma K t).1
    (SingleTailRadius.physBranch z rho sigma K t).2 hr.le hs.le hv.ne').mpr hactualA
  refine ⟨t, ht, hR, hrt, ?_⟩
  rw [hF]
  simp

end FMSA.Paper.BaxterZeroMode

/-- info: 'FMSA.Paper.BaxterZeroMode.core_zero_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.BaxterZeroMode.core_zero_integral

/-- info: 'FMSA.Paper.BaxterZeroMode.row_zero_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.BaxterZeroMode.row_zero_integral

/-- info: 'FMSA.Paper.BaxterZeroMode.fourierQ_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.BaxterZeroMode.fourierQ_zero

/-- info: 'FMSA.Paper.BaxterZeroMode.fourierFactor_zero_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.BaxterZeroMode.fourierFactor_zero_entry

/-- info: 'FMSA.Paper.BaxterZeroMode.scalar_HS_balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.BaxterZeroMode.scalar_HS_balance

/-- info: 'FMSA.Paper.BaxterZeroMode.scalar_tail_balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.BaxterZeroMode.scalar_tail_balance

/-- info: 'FMSA.Paper.BaxterZeroMode.scalar_zeroMoment_balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.BaxterZeroMode.scalar_zeroMoment_balance

/-- info: 'FMSA.Paper.BaxterZeroMode.scalar_fourierFactor_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.BaxterZeroMode.scalar_fourierFactor_zero

/-- info: 'FMSA.Paper.BaxterZeroMode.scalar_fourierFactor_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.BaxterZeroMode.scalar_fourierFactor_zero_iff

/-- info: 'FMSA.Paper.BaxterZeroMode.scalar_spectral_den_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.BaxterZeroMode.scalar_spectral_den_zero

/-- info: 'FMSA.Paper.BaxterZeroMode.single_tail_amplitudeA_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.BaxterZeroMode.single_tail_amplitudeA_eq

/-- info: 'FMSA.Paper.BaxterZeroMode.actual_single_tail_zero_before_radius' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.BaxterZeroMode.actual_single_tail_zero_before_radius
