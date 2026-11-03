import MSAConvergence.HolomorphicHomotopy
import MSAConvergence.LowDensityCanonicalSeed
import MSAConvergence.CanonicalFirstLoss
import LeanCode.HardSphere.BaxterLowerHalfPlane
import LeanCode.HSMixture.MixtureNoSpinodalN1

/-! Initial full canonicity for every physical one-species HS state. The
frozen scalar homotopy inputs are reused with a PROVED analysis replacement. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open scoped BigOperators ContDiff
namespace FMSA.Convergence.ScalarCanonicalSeed
open FMSA.HardSphere FMSA.MatrixQ0 FMSA.Paper
open FMSA.ExactMSA.MultiTailMixture FMSA.ExactMSA.Breakpoint MSAMixture
open FMSA.Convergence.CanonicalNeighborhood FMSA.Convergence.CanonicalKernelEstimates
open FMSA.Convergence.LowDensityCanonicalSeed
open FMSA.Paper.ActualAnalyticTaylor FMSA.Paper.FoldRadius FMSA.Paper.TaylorRoot
open FMSA.MixtureNoSpinodalN1

/-- The actual physical density constraint along the frozen scalar homotopy. -/
theorem scalar_physical_density_constraint {sigma t : ℝ} (hsigma : 0 < sigma) :
    t = Real.pi * rhoPhys sigma t * sigma^3/6 := by
  have hpi := Real.pi_ne_zero
  have hs := hsigma.ne'
  unfold rhoPhys
  field_simp

/-- The actual scalar HS homotopy has no open-lower-half-plane zero, using
only proved scalar inputs and the new maximum-modulus homotopy theorem. -/
theorem scalar_baxterH_no_lower_zero {sigma t : ℝ} (hsigma : 0 < sigma) (ht0 : 0 < t) (ht1 : t < 1)
    {k : ℂ} (hk : k.im < 0) : baxterH sigma t k ≠ 0 := by
  have hs7hi : Real.sqrt 7 < 3 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 7 by norm_num), Real.sqrt_nonneg 7]
  have hrhoNonneg : ∀ u : ℝ, 0 ≤ u → 0 ≤ rhoPhys sigma u := fun u hu => by
    unfold rhoPhys; positivity
  rcases le_or_gt t ((3 - Real.sqrt 7) / 4) with hsmall | hbig
  · -- Direct base case: `t` below the dilute wall.
    have hd := Qhat_complex_ne_one_of_im_nonpos_of_dilute ht0 ht1 hsigma
      (hrhoNonneg t ht0.le) (scalar_physical_density_constraint hsigma) (by linarith) hk.le
    exact sub_ne_zero.mpr (Ne.symm hd)
  · -- Homotopy case: `(3−√7)/4 < t`.
    have ha0 : 0 < (3 - Real.sqrt 7) / 4 := by linarith
    have ha1 : (3 - Real.sqrt 7) / 4 < 1 := by linarith [Real.sqrt_nonneg 7]
    obtain ⟨R, hRpos, hRbound⟩ := exists_uniform_escape_radius (a := (3 - Real.sqrt 7) / 4)
      (b := t) (sigma := sigma) ht1 (rhoPhys_continuous sigma).continuousOn
    have hholo : ∀ s ∈ Set.Icc ((3 - Real.sqrt 7) / 4) t, Differentiable ℂ (baxterH sigma s) :=
      fun s _ => (differentiable_const 1).sub (Qhat_complex_entire s sigma (rhoPhys sigma s) hsigma)
    have hbound : ∀ s ∈ Set.Icc ((3 - Real.sqrt 7) / 4) t, ∀ z : ℂ, z.im ≤ 0 →
        baxterH sigma s z = 0 → ‖z‖ < R := by
      intro s hs z hzim hHz
      by_contra hlt
      push Not at hlt
      have hz0 : z ≠ 0 := fun h => by rw [h, norm_zero] at hlt; linarith
      have hG0 : G_baxter s sigma (rhoPhys sigma s) z = 0 :=
        (Qhat_pole_iff_G_baxter_zero s sigma (rhoPhys sigma s) hsigma hz0).mp hHz
      exact G_baxter_ne_zero_of_norm_dominant hsigma hzim (hRbound s hs z hlt) hG0
    have hreal : ∀ s ∈ Set.Icc ((3 - Real.sqrt 7) / 4) t, ∀ z : ℂ, z.im = 0 →
        baxterH sigma s z ≠ 0 := by
      intro s hs z hzim
      have hs0 : 0 < s := lt_of_lt_of_le ha0 hs.1
      have hs1 : s < 1 := lt_of_le_of_lt hs.2 ht1
      have hdef := scalar_physical_density_constraint (sigma := sigma) (t := s) hsigma
      have hz : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [hzim])
      show (1 : ℂ) - Qhat_complex s sigma (rhoPhys sigma s) z ≠ 0
      by_cases hre : z.re = 0
      · have hz0 : z = 0 := by rw [hz, hre]; simp
        rw [hz0]
        exact one_sub_Qhat_complex_zero_ne_zero hs0 hsigma hs1 hdef
      · intro hH
        have hz0 : z ≠ 0 := by rw [hz]; simpa using hre
        have hG : G_baxter s sigma (rhoPhys sigma s) z ≠ 0 := by
          rw [hz]; exact G_baxter_ne_zero_of_real hsigma hs1 hdef hre
        exact hG ((Qhat_pole_iff_G_baxter_zero s sigma (rhoPhys sigma s) hsigma hz0).mp hH)
    have hbase : ∀ z : ℂ, z.im < 0 → baxterH sigma ((3 - Real.sqrt 7) / 4) z ≠ 0 := by
      intro z hzim
      have hd := Qhat_complex_ne_one_of_im_nonpos_of_dilute ha0 ha1 hsigma
        (hrhoNonneg _ ha0.le) (scalar_physical_density_constraint hsigma) (by linarith) hzim.le
      exact sub_ne_zero.mpr (Ne.symm hd)
    exact FMSA.Convergence.HolomorphicHomotopy.zeroFree_lowerHalfPlane_of_homotopy (H := baxterH sigma)
      (a := (3 - Real.sqrt 7) / 4) (b := t) (R := R) hbig.le hRpos (baxterH_continuousOn ht1)
      hholo hbound hreal hbase k hk


/-- The HONEST scalar Baxter integral factor is nonzero on the whole closed
lower half-plane, including frequency zero and vacuum, for every eta<1. -/
theorem scalar_baxter_symbol_nonzero
    (eta sigma rho : ℝ) (hsigma : 0 < sigma) (hrho : 0 ≤ rho) (heta : eta < 1)
    (hdef : eta = Real.pi*rho*sigma^3/6) (k : ℂ) (hk : k.im ≤ 0) :
    1-Qhat_complex eta sigma rho k ≠ 0 := by
  by_cases hzero : rho = 0
  · simp [Qhat_complex,q0_poly,hzero]
  have hrhop : 0 < rho := lt_of_le_of_ne hrho (Ne.symm hzero)
  have hetap : 0 < eta := by rw [hdef]; positivity
  rcases lt_or_eq_of_le hk with hneg | haxis
  · have hphys : rhoPhys sigma eta = rho := by
      unfold rhoPhys
      rw [hdef]
      field_simp [Real.pi_ne_zero,hsigma.ne']
    have h := scalar_baxterH_no_lower_zero hsigma hetap heta hneg
    simpa only [baxterH,hphys] using h
  · have hkreal : k = (k.re : ℂ) := Complex.ext (by simp) (by simp [haxis])
    by_cases hk0 : k = 0
    · rw [hk0]
      exact one_sub_Qhat_complex_zero_ne_zero hetap hsigma heta hdef
    · have hre : k.re ≠ 0 := by intro he; apply hk0; rw [hkreal,he]; simp
      intro he
      have hG : G_baxter eta sigma rho k ≠ 0 := by
        rw [hkreal]
        exact G_baxter_ne_zero_of_real hsigma heta hdef hre
      exact hG ((Qhat_pole_iff_G_baxter_zero eta sigma rho hsigma hk0).mp he)

variable {T : Type*} [Fintype T]

/-- Equality of the actual density-weighted scalar HS kernel and the frozen
physical polynomial; the equality is in real space, before any transform. -/
theorem actual_scalar_hs_kernel_eq_poly
    (z : T → ℝ) (rho sigma : Fin 1 → ℝ) (G : TailMatrix T 1)
    (hsigma : 0 < sigma 0) (heta : etaMix rho sigma < 1) (r : ℝ) :
    nonlinearCausalKernel z rho sigma 0 G r 0 0 =
      q0_poly (etaMix rho sigma) (sigma 0) (rho 0) r := by
  simp only [nonlinearCausalKernel,Matrix.of_apply,nonlinearRecenteredQ,
    amplitudeQp_zero,amplitudeA_zero]
  simp only [W,Wt,C,Ct,Pi.zero_apply,mul_zero,zero_mul,add_zero,Finset.sum_const_zero]
  rw [Q0phys_n1 hsigma heta.ne,Qppphys_n1 hsigma heta.ne]
  by_cases hr : r ≤ sigma 0
  · simp only [min_eq_left hr,q0_poly,phi1_real,phi2_real,if_pos hr]
    ring
  · simp [min_eq_right (le_of_not_ge hr),q0_poly,phi1_real,phi2_real,hr]

/-- The actual causal Laplace symbol equals the honest scalar Baxter
Fourier integral at k=-i*s, including s=0. No rational junk value is used. -/
theorem actual_scalar_hs_laplace_eq
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin 1 → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (heta : etaMix rho sigma < 1)
    (G : TailMatrix T 1) (s : ℂ) (hs : 0 ≤ s.re) :
    rdfMatrixLaplace (nonlinearCausalKernel z rho sigma 0 G) s 0 0 =
      Qhat_complex (etaMix rho sigma) (sigma 0) (rho 0) (-Complex.I*s) := by
  let f : ℝ → ℂ := fun r => (q0_poly (etaMix rho sigma) (sigma 0) (rho 0) r : ℂ)*Complex.exp (-s*r)
  have hi : IntegrableOn f (Ioi 0) := by
    have h := kernel_laplace_integrable_rate_domain z rho sigma (fun i => (hsigma i).le) (0,G) s
      (fun u => by linarith [hz u]) 0 0
    simpa only [f,actual_scalar_hs_kernel_eq_poly z rho sigma G (hsigma 0) heta] using h
  have ht : (∫ r in Ioi (sigma 0), f r) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro r hr
    change sigma 0 < r at hr
    simp only [f,q0_poly_outer hr,Complex.ofReal_zero,zero_mul]
  have he := intervalIntegral.integral_Ioi_sub_Ioi hi (hsigma 0).le
  rw [ht,sub_zero] at he
  change (∫ r in Ioi (0 : ℝ), (nonlinearCausalKernel z rho sigma 0 G r 0 0 : ℂ)*Complex.exp (-s*r)) = _
  simp_rw [actual_scalar_hs_kernel_eq_poly z rho sigma G (hsigma 0) heta]
  rw [he]
  unfold Qhat_complex
  apply intervalIntegral.integral_congr
  intro r _
  change _*Complex.exp (-s*(r : ℂ)) = _*Complex.exp (-Complex.I*(-Complex.I*s)*(r : ℂ))
  congr 2
  rw [show -Complex.I*(-Complex.I*s) = -s by
    calc
      _ = (Complex.I*Complex.I)*s := by ring
      _ = -s := by rw [Complex.I_mul_I]; ring]

/-- For ONE species, every physical initial HS state is fully canonical,
without a dilute-budget restriction, including vacuum and frequency zero. -/
theorem actual_scalar_hs_canonical
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin 1 → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (heta : etaMix rho sigma < 1) (G : TailMatrix T 1) :
    (0,G) ∈ canonicalAmplitudes z rho sigma := by
  intro s hs
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [Matrix.det_fin_one]
  change IsUnit (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma 0 G) s 0 0)
  rw [actual_scalar_hs_laplace_eq z hz rho sigma hsigma heta G s hs]
  apply isUnit_iff_ne_zero.mpr
  apply scalar_baxter_symbol_nonzero _ _ _ (hsigma 0) (hrho 0) heta (etaMix_n1 rho sigma)
  simpa only [Complex.mul_im,Complex.neg_re,Complex.I_re,neg_zero,Complex.neg_im,
    Complex.I_im,zero_mul,neg_mul,one_mul,zero_add] using neg_nonpos.mpr hs

/-- Every physical ONE-species HS seed constructs an actual analytic
canonical MSA root germ with positive Taylor radius, for arbitrary finite K. -/
theorem exists_scalar_analytic_canonical_hs_seed
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin 1 → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (hv : 0 < vacMix rho sigma) (K : TailMatrix T 1) :
    ∃ p : ℝ → TailMatrix T 1 × TailMatrix T 1,
      p 0 = (0,baseSeed z rho sigma) ∧ AnalyticAt ℝ p 0 ∧
      0 < amplitudeRadius (branchCoefficients p) ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K) (p t).1 (p t).2) ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), p t ∈ canonicalAmplitudes z rho sigma) := by
  have heta : etaMix rho sigma < 1 := by unfold vacMix at hv; linarith
  obtain ⟨p,hp0,hr,ha,hR⟩ := exists_analytic_seed_positive_radius z rho sigma K hz hv hrho hsigma
  have hc := actual_scalar_hs_canonical z hz rho sigma hsigma hrho heta (baseSeed z rho sigma)
  have ht : Tendsto p (𝓝 0) (𝓝 (0,baseSeed z rho sigma)) := by rw [← hp0]; exact ha.continuousAt.tendsto
  exact ⟨p,hp0,ha,hR,hr,ht.eventually
    (actual_canonicity_eventually z hz rho sigma (fun i => (hsigma i).le) _ hc)⟩

/-- For every physical ONE-species density eta<1, a common actual local
canonical root interval exists and all amplitude Taylor sums equal its roots. -/
theorem exists_scalar_convergent_canonical_hs_interval
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin 1 → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (hv : 0 < vacMix rho sigma) (K : TailMatrix T 1) :
    ∃ p : ℝ → TailMatrix T 1 × TailMatrix T 1, ∃ b : ℝ,
      0 < b ∧ p 0 = (0,baseSeed z rho sigma) ∧
      0 < amplitudeRadius (branchCoefficients p) ∧ ∀ t : ℝ, |t| < b →
        AnalyticAt ℝ p t ∧ IsRoot z rho sigma (t • K) (p t).1 (p t).2 ∧
        p t ∈ canonicalAmplitudes z rho sigma ∧
        (∀ u i j, HasSum (fun n => (branchCoefficients p n).1 u i j*t^n) ((p t).1 u i j)) ∧
        (∀ u i j, HasSum (fun n => (branchCoefficients p n).2 u i j*t^n) ((p t).2 u i j)) := by
  obtain ⟨p,hp0,ha,hR,hr,hc⟩ := exists_scalar_analytic_canonical_hs_seed z hz rho sigma hsigma hrho hv K
  have hs := analytic_amplitudes_eventually_hasSum p ha
  have he := ha.eventually_analyticAt.and (hr.and (hc.and hs))
  obtain ⟨b,hb,hball⟩ := Metric.eventually_nhds_iff.mp he
  exact ⟨p,b,hb,hp0,hR,fun t ht => hball (by simpa only [Real.dist_eq,sub_zero] using ht)⟩

/-- The correct full-interval Taylor criterion for a physical ONE-species
HS-seeded branch, without a caller-supplied initial canonical seed or Jacobian
inverse. The all-real-frequency path condition and radius bound remain explicit. -/
theorem exists_scalar_series_extension_of_physical_axis_units
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin 1 → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T 1) (hv : 0 < vacMix rho sigma)
    (p : ℝ → TailMatrix T 1 × TailMatrix T 1) (bound : ENNReal) (hbound : 0 < bound)
    (hp : ContinuousOn p (FMSA.Paper.StableIntervalRadius.initialCouplings bound))
    (hp0 : p 0 = (0,baseSeed z rho sigma))
    (hroot : ∀ t ∈ FMSA.Paper.StableIntervalRadius.initialCouplings bound,
      IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hF : ∀ t ∈ FMSA.Paper.StableIntervalRadius.initialCouplings bound, ∀ k : ℝ, IsUnit
      (fourierFactor z rho sigma (amplitudeA z rho sigma (p t).1 (p t).2)
        (amplitudeQp z rho sigma (p t).1 (p t).2) (W z rho (p t).1 (p t).2)
          (C z rho sigma (p t).1 (p t).2) k)) :
    ∃ e : ℝ → TailMatrix T 1 × TailMatrix T 1,
      Set.EqOn e p (FMSA.Paper.StableIntervalRadius.initialCouplings bound) ∧
      AnalyticOnNhd ℝ e (FMSA.Paper.StableIntervalRadius.initialCouplings bound) ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K) (e t).1 (e t).2) ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), e t ∈ canonicalAmplitudes z rho sigma) ∧
      0 < amplitudeRadius (branchCoefficients e) ∧
      (FMSA.Convergence.ActualCanonicalBranch.AmplitudeHasSumTo e p bound ↔
        bound ≤ amplitudeRadius (branchCoefficients e)) := by
  have heta : etaMix rho sigma < 1 := by unfold vacMix at hv; linarith
  have hc : p 0 ∈ canonicalAmplitudes z rho sigma := by
    rw [hp0]
    exact actual_scalar_hs_canonical z hz rho sigma hsigma hrho heta _
  have hK : ∀ u i j, K u i j = K u j i := by intro u i j; fin_cases i; fin_cases j; rfl
  exact FMSA.Convergence.CanonicalFirstLoss.exists_series_extension_of_physical_axis_units
    z hz rho sigma hsigma hrho K hK hv.ne' p bound hbound hp hroot hc hF

end FMSA.Convergence.ScalarCanonicalSeed

/-- info: 'FMSA.Convergence.ScalarCanonicalSeed.scalar_physical_density_constraint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ScalarCanonicalSeed.scalar_physical_density_constraint

/-- info: 'FMSA.Convergence.ScalarCanonicalSeed.scalar_baxterH_no_lower_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ScalarCanonicalSeed.scalar_baxterH_no_lower_zero

/-- info: 'FMSA.Convergence.ScalarCanonicalSeed.scalar_baxter_symbol_nonzero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ScalarCanonicalSeed.scalar_baxter_symbol_nonzero

/-- info: 'FMSA.Convergence.ScalarCanonicalSeed.actual_scalar_hs_kernel_eq_poly' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ScalarCanonicalSeed.actual_scalar_hs_kernel_eq_poly

/-- info: 'FMSA.Convergence.ScalarCanonicalSeed.actual_scalar_hs_laplace_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ScalarCanonicalSeed.actual_scalar_hs_laplace_eq

/-- info: 'FMSA.Convergence.ScalarCanonicalSeed.actual_scalar_hs_canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ScalarCanonicalSeed.actual_scalar_hs_canonical

/-- info: 'FMSA.Convergence.ScalarCanonicalSeed.exists_scalar_analytic_canonical_hs_seed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ScalarCanonicalSeed.exists_scalar_analytic_canonical_hs_seed

/-- info: 'FMSA.Convergence.ScalarCanonicalSeed.exists_scalar_convergent_canonical_hs_interval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ScalarCanonicalSeed.exists_scalar_convergent_canonical_hs_interval

/-- info: 'FMSA.Convergence.ScalarCanonicalSeed.exists_scalar_series_extension_of_physical_axis_units' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ScalarCanonicalSeed.exists_scalar_series_extension_of_physical_axis_units
