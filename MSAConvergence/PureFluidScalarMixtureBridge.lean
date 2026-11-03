import MSAConvergence.PureFluidThetaPringsheimRoute
import MSAConvergence.MaximalMSAConvergence

set_option linter.style.header false

/-! Unit-diameter, one-species bridge between the pure-fluid
multi-tail BH system and the matrix multi-tail mixture system. -/
noncomputable section
open Real FMSA.MatrixQ0 FMSA.HardSphere FMSA.MixtureNoSpinodalN1 MSAMixture
namespace FMSA.Convergence.PureFluidScalarMixtureBridge
open FMSA.ExactMSA
open FMSA.Paper.StableIntervalRadius

variable {T : Type*} [Fintype T]

def rho1 (xi : ℝ) : Fin 1 → ℝ := fun _ => rhoOf xi

def sigma1 : Fin 1 → ℝ := fun _ => 1

def liftTail (a : T → ℝ) : MultiTailMixture.TailMatrix T 1 :=
  fun t _ _ => a t

def lowerTail (a : MultiTailMixture.TailMatrix T 1) : T → ℝ :=
  fun t => a t 0 0

omit [Fintype T] in
theorem lift_lowerTail (a : MultiTailMixture.TailMatrix T 1) :
    liftTail (lowerTail a) = a := by
  funext t i j
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst i
  subst j
  rfl

/-- The one-species unit-diameter mixture packing fraction is xi. -/
theorem etaMix_rho1_sigma1 (xi : ℝ) :
    etaMix (rho1 xi) sigma1 = xi := by
  simp [etaMix, rho1, sigma1, rhoOf]

/-- The two definitions of the hard-sphere vacancy agree. -/
theorem vacMix_rho1_sigma1 (xi : ℝ) :
    vacMix (rho1 xi) sigma1 = 1 - xi := by
  rw [vacMix, etaMix_rho1_sigma1]

/-- The one-species HS Baxter slope agrees with the pure-fluid BH
normalization at unit diameter. -/
theorem Q0phys_eq_qp0 (xi : ℝ) (hxi : xi ≠ 1) :
    Q0phys (rho1 xi) sigma1 0 0 = qp0 xi := by
  have hs : 0 < sigma1 0 := by simp [sigma1]
  have he : etaMix (rho1 xi) sigma1 ≠ 1 := by
    rw [etaMix_rho1_sigma1]
    exact hxi
  rw [Q0phys_n1 hs he, etaMix_rho1_sigma1]
  simp only [sigma1] at *
  unfold q_prime_py qp0
  ring

/-- The one-species HS Baxter curvature agrees with the pure-fluid
BH normalization at unit diameter. -/
theorem Qppphys_eq_bA0 (xi : ℝ) (hxi : xi ≠ 1) :
    Qppphys (rho1 xi) sigma1 0 0 = bA0 xi := by
  have hs : 0 < sigma1 0 := by simp [sigma1]
  have he : etaMix (rho1 xi) sigma1 ≠ 1 := by
    rw [etaMix_rho1_sigma1]
    exact hxi
  rw [Qppphys_n1 hs he, etaMix_rho1_sigma1]
  unfold q_doubleprime_py bA0
  ring

omit [Fintype T] in
/-- The matrix-tail noncompact weight reduces to the exact pure-fluid
weight for a single species at unit diameter. -/
theorem W_eq_pure (xi : ℝ) (z D G : T → ℝ) (t : T) :
    MultiTailMixture.W z (rho1 xi) (liftTail D) (liftTail G) t 0 0 =
      MultiTail.W xi z D G t := by
  simp [MultiTailMixture.W, Wt, MultiTail.W, rho1, liftTail]
  ring

omit [Fintype T] in
theorem gam_eq_pure (xi : ℝ) (z G : T → ℝ) (t : T) :
    MSAMixture.gam (z t) (rho1 xi) sigma1 (liftTail G t) 0 0 =
      ExactMSA.gam xi (z t) (G t) := by
  simp [MSAMixture.gam, MSAMixture.sigMix, ExactMSA.gam,
    rho1, sigma1, liftTail]

omit [Fintype T] in
/-- The matrix-tail exponential weight reduces to the exact
pure-fluid weight at unit diameter. -/
theorem C_eq_pure (xi : ℝ) (z D G : T → ℝ) (t : T) :
    MultiTailMixture.C z (rho1 xi) sigma1
        (liftTail D) (liftTail G) t 0 0 =
      MultiTail.C xi z D G t := by
  simp [MultiTailMixture.C, Ct, MultiTail.C, sigma1, liftTail]
  exact Or.inl (gam_eq_pure xi z G t)

omit [Fintype T] in
theorem Mtil_term_eq (xi : ℝ) (z D G : T → ℝ) (t : T) :
    -(1 / z t) * (rhoOf xi *
      (MultiTail.W xi z D G t +
        (1 + z t) * MultiTail.C xi z D G t)) =
      D t * Mtil xi (z t) (G t) := by
  unfold MultiTail.W MultiTail.C Mtil
  ring

omit [Fintype T] in
theorem Ntil_term_eq (xi : ℝ) (z D G : T → ℝ) (t : T) :
    rhoOf xi *
      ((1 / (z t) ^ 2) * MultiTail.W xi z D G t +
        ((1 + z t + (z t) ^ 2 / 2) / (z t) ^ 2) *
          MultiTail.C xi z D G t) =
      D t * Ntil xi (z t) (G t) := by
  unfold MultiTail.W MultiTail.C Ntil
  ring

omit [Fintype T] in
theorem mixM_eq_pure_term (xi : ℝ) (z D G : T → ℝ) (t : T) :
    mixM (z t) (rho1 xi) sigma1
      (liftTail G t) (liftTail D t) 0 =
      D t * Mtil xi (z t) (G t) := by
  unfold mixM
  simp only [Fin.sum_univ_one, rho1, sigma1]
  simp only [mul_one]
  change -(1 / z t) * (rhoOf xi *
      (MultiTailMixture.W z (rho1 xi) (liftTail D) (liftTail G) t 0 0 +
        (1 + z t) * MultiTailMixture.C z (rho1 xi) sigma1
          (liftTail D) (liftTail G) t 0 0)) =
    D t * Mtil xi (z t) (G t)
  rw [W_eq_pure, C_eq_pure]
  exact Mtil_term_eq xi z D G t

omit [Fintype T] in
theorem mixN_eq_pure_term (xi : ℝ) (z D G : T → ℝ) (t : T) :
    mixN (z t) (rho1 xi) sigma1
      (liftTail G t) (liftTail D t) 0 =
      D t * Ntil xi (z t) (G t) := by
  unfold mixN
  simp only [Fin.sum_univ_one, rho1, sigma1,
    sub_self, zero_div, mul_zero, add_zero, mul_one]
  simp only [zero_mul, zero_div, add_zero]
  change rhoOf xi *
      ((1 / (z t) ^ 2) *
          MultiTailMixture.W z (rho1 xi) (liftTail D) (liftTail G) t 0 0 +
        ((1 + z t + (z t) ^ 2 / 2) / (z t) ^ 2) *
          MultiTailMixture.C z (rho1 xi) sigma1
            (liftTail D) (liftTail G) t 0 0) =
    D t * Ntil xi (z t) (G t)
  rw [W_eq_pure, C_eq_pure]
  exact Ntil_term_eq xi z D G t

theorem mixDA_N_coefficient_eq (xi : ℝ) (hxi : xi ≠ 1) :
    2 * Real.pi ^ 2 * xi2 (rho1 xi) sigma1 /
      vacMix (rho1 xi) sigma1 ^ 2 = -4 * bB0 xi := by
  rw [vacMix_rho1_sigma1]
  simp only [xi2, Fin.sum_univ_one, rho1, sigma1]
  unfold rhoOf bB0
  field_simp [Real.pi_ne_zero, sub_ne_zero.mpr (Ne.symm hxi)]
  ring

omit [Fintype T] in
theorem mixDA_eq_pure_term (xi : ℝ) (hxi : xi ≠ 1)
    (z D G : T → ℝ) (t : T) :
    mixDA (z t) (rho1 xi) sigma1
      (liftTail G t) (liftTail D t) 0 =
      D t * (bA0 xi * Mtil xi (z t) (G t) -
        4 * bB0 xi * Ntil xi (z t) (G t)) := by
  unfold mixDA
  rw [Qppphys_eq_bA0 xi hxi,
    mixM_eq_pure_term, mixN_eq_pure_term,
    mixDA_N_coefficient_eq xi hxi]
  ring

omit [Fintype T] in
theorem mixDqp_eq_pure_term (xi : ℝ) (hxi : xi ≠ 1)
    (z D G : T → ℝ) (t : T) :
    mixDqp (z t) (rho1 xi) sigma1
      (liftTail G t) (liftTail D t) 0 0 =
      D t * (qp0 xi * Mtil xi (z t) (G t) +
        bA0 xi * Ntil xi (z t) (G t)) := by
  unfold mixDqp
  rw [Q0phys_eq_qp0 xi hxi, Qppphys_eq_bA0 xi hxi,
    mixM_eq_pure_term, mixN_eq_pure_term]
  ring

/-- The one-species mixture curvature amplitude is the pure-fluid
multi-tail curvature amplitude. -/
theorem amplitudeA_eq_pure (xi : ℝ) (hxi : xi ≠ 1)
    (z D G : T → ℝ) :
    MultiTailMixture.amplitudeA z (rho1 xi) sigma1
        (liftTail D) (liftTail G) 0 =
      MultiTail.amplitudeA xi z D G := by
  rw [MultiTailMixture.amplitudeA,
    Qppphys_eq_bA0 xi hxi, MultiTail.amplitudeA_affine]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  exact mixDA_eq_pure_term xi hxi z D G t

/-- The one-species mixture slope amplitude is the pure-fluid
multi-tail slope amplitude. -/
theorem amplitudeQp_eq_pure (xi : ℝ) (hxi : xi ≠ 1)
    (z D G : T → ℝ) :
    MultiTailMixture.amplitudeQp z (rho1 xi) sigma1
        (liftTail D) (liftTail G) 0 0 =
      MultiTail.amplitudeQp xi z D G := by
  rw [MultiTailMixture.amplitudeQp,
    Q0phys_eq_qp0 xi hxi, MultiTail.amplitudeQp_affine]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  exact mixDqp_eq_pure_term xi hxi z D G t

/-- The dressed matrix Baxter transform at its sole entry is the
pure-fluid multi-tail transform. -/
theorem dressedQhat_eq_pure (xi : ℝ) (hxi : xi ≠ 1)
    (z D G : T → ℝ) (s : ℝ) :
    MultiTailMixture.dressedQhat z (rho1 xi) sigma1
        (liftTail D) (liftTail G) s 0 0 =
      MultiTail.Qhat xi z D G s := by
  simp only [MultiTailMixture.dressedQhat, MultiTailMixture.Qhat,
    edgeLo, edgeHi, sigma1, sub_self, zero_div, mul_zero,
    exp_zero, one_mul]
  norm_num only
  simp only [mul_one]
  rw [amplitudeA_eq_pure xi hxi, amplitudeQp_eq_pure xi hxi]
  simp only [MultiTail.Qhat, phi1, phi2]
  have hw : ∀ t, MultiTailMixture.W z (rho1 xi)
      (liftTail D) (liftTail G) t 0 0 = MultiTail.W xi z D G t :=
    fun t => W_eq_pure xi z D G t
  have hc : ∀ t, MultiTailMixture.C z (rho1 xi) sigma1
      (liftTail D) (liftTail G) t 0 0 = MultiTail.C xi z D G t :=
    fun t => C_eq_pure xi z D G t
  simp only [hw, hc]
  have hsum :
      (∑ t, (MultiTail.W xi z D G t / (s + z t) +
        MultiTail.C xi z D G t * (1 - exp (-s)) / s)) +
      (∑ t, MultiTail.C xi z D G t * exp (-s) / (s + z t)) =
      ∑ t, ((MultiTail.W xi z D G t +
          MultiTail.C xi z D G t * exp (-s)) / (s + z t) +
        MultiTail.C xi z D G t * (1 - exp (-s)) / s) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _
    ring
  linear_combination hsum

theorem firstLHS_eq_pure (xi : ℝ) (hxi : xi ≠ 1)
    (z D G : T → ℝ) (u : T) :
    MultiTailMixture.firstLHS z (rho1 xi) sigma1
        (liftTail D) (liftTail G) u 0 0 =
      D u * MultiTail.factor xi z D G (z u) := by
  unfold MultiTailMixture.firstLHS MultiTail.factor
  simp only [Fin.sum_univ_one, liftTail, rho1, ite_true,
    edgeLo, sigma1, sub_self, zero_div, mul_zero,
    exp_zero, mul_one]
  rw [dressedQhat_eq_pure xi hxi]

theorem secondLHS_eq_pure (xi : ℝ) (hxi : xi ≠ 1)
    (z D G : T → ℝ) (u : T) :
    MultiTailMixture.secondLHS z (rho1 xi) sigma1
        (liftTail D) (liftTail G) u 0 0 =
      2 * π * G u * MultiTail.factor xi z D G (z u) := by
  unfold MultiTailMixture.secondLHS MultiTail.factor
  simp only [Fin.sum_univ_one, liftTail, rho1, ite_true,
    edgeLo, sigma1, sub_self, zero_div, mul_zero,
    exp_zero, mul_one]
  rw [dressedQhat_eq_pure xi hxi]
  ring

theorem secondRHS_eq_pure (xi : ℝ) (hxi : xi ≠ 1)
    (z D G : T → ℝ) (u : T) :
    MultiTailMixture.secondRHS z (rho1 xi) sigma1
        (liftTail D) (liftTail G) u 0 0 =
      MultiTail.secondRHS xi z D G (z u) := by
  unfold MultiTailMixture.secondRHS MultiTail.secondRHS
  rw [amplitudeA_eq_pure xi hxi, amplitudeQp_eq_pure xi hxi]
  simp only [C_eq_pure]

/-- The scalar and matrix multi-tail equations are exactly the same
equations at one species and unit diameter. -/
theorem isRoot_iff (xi : ℝ) (hxi : xi ≠ 1)
    (z K D G : T → ℝ) :
    MultiTailMixture.IsRoot z (rho1 xi) sigma1
        (liftTail K) (liftTail D) (liftTail G) ↔
      MultiTail.IsRoot xi z K D G := by
  constructor
  · intro h
    constructor
    · intro u
      simpa only [firstLHS_eq_pure xi hxi z D G u, liftTail] using h.1 u 0 0
    · intro u
      simpa only [secondLHS_eq_pure xi hxi z D G u,
        secondRHS_eq_pure xi hxi z D G u] using h.2 u 0 0
  · intro h
    constructor
    · intro u i j
      have hi : i = 0 := Subsingleton.elim _ _
      have hj : j = 0 := Subsingleton.elim _ _
      subst i
      subst j
      simpa only [firstLHS_eq_pure xi hxi z D G u, liftTail] using h.1 u
    · intro u i j
      have hi : i = 0 := Subsingleton.elim _ _
      have hj : j = 0 := Subsingleton.elim _ _
      subst i
      subst j
      simpa only [secondLHS_eq_pure xi hxi z D G u,
        secondRHS_eq_pure xi hxi z D G u] using h.2 u

/-- The constructed one-species matrix PY seed equals the closed-form
pure-fluid PY seed at every tail rate. -/
theorem baseSeed_eq_pure (xi : ℝ) (hxi0 : 0 < xi) (hxi1 : xi < 1)
    (z : T → ℝ) (hz : ∀ t, 0 < z t) :
    lowerTail (MultiTailMixture.baseSeed z (rho1 xi) sigma1) =
      (fun t => G0 xi (z t)) := by
  have hv : 0 < vacMix (rho1 xi) sigma1 := by
    rw [vacMix_rho1_sigma1]
    linarith
  have hrho : ∀ i, 0 ≤ rho1 xi i := by
    intro i
    simp only [rho1, rhoOf]
    positivity
  have hsigma : ∀ i, 0 < sigma1 i := by
    intro i
    simp [sigma1]
  have hm := MultiTailMixture.baseSeed_isRoot z (rho1 xi) sigma1
    hz hv hrho hsigma
  rw [← lift_lowerTail (MultiTailMixture.baseSeed z (rho1 xi) sigma1)] at hm
  have hzlift : liftTail (fun _ : T => 0) =
      (0 : MultiTailMixture.TailMatrix T 1) := by
    funext t i j
    rfl
  have hpure : MultiTail.IsRoot xi z (fun _ => 0) (fun _ => 0)
      (lowerTail (MultiTailMixture.baseSeed z (rho1 xi) sigma1)) := by
    apply (isRoot_iff xi hxi1.ne z (fun _ => 0) (fun _ => 0) _).mp
    simpa only [hzlift] using hm
  funext t
  have h := hpure.2 t
  rw [MultiTail.factor_zero, MultiTail.secondRHS_zero] at h
  have hbase := bh_base_eq (show xi ∈ Set.Ioo (0 : ℝ) 1 from ⟨hxi0, hxi1⟩) (hz t)
  rw [bhF_base, bhP_base] at hbase
  have hbase' : 2 * π * G0 xi (z t) * F0 xi (z t) = bhP0 xi (z t) := by
    simpa only [F0, mul_assoc] using hbase
  have hF : F0 xi (z t) ≠ 0 := by
    have hf := bhF_base_ne_zero
      (show xi ∈ Set.Ioo (0 : ℝ) 1 from ⟨hxi0, hxi1⟩) (hz t)
    simpa [bhF, F0] using hf
  have hprod : 2 * π * F0 xi (z t) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hF
  have hdiff :
      (lowerTail (MultiTailMixture.baseSeed z (rho1 xi) sigma1) t -
        G0 xi (z t)) * (2 * π * F0 xi (z t)) = 0 := by
    linear_combination h - hbase'
  exact sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_right hprod)

def lowerPath (p : ℝ → MultiTailMixture.TailMatrix T 1 ×
    MultiTailMixture.TailMatrix T 1) :
    ℝ → (T → ℝ) × (T → ℝ) :=
  fun tau => (lowerTail (p tau).1, lowerTail (p tau).2)

/-- Coordinate projection sends an analytic matrix-amplitude path to
an analytic pure-fluid amplitude path. -/
theorem lowerPath_analyticOn {S : Set ℝ}
    (p : ℝ → MultiTailMixture.TailMatrix T 1 ×
      MultiTailMixture.TailMatrix T 1)
    (hp : AnalyticOnNhd ℝ p S) :
    AnalyticOnNhd ℝ (lowerPath p) S := by
  intro tau htau
  have ha := hp tau htau
  apply AnalyticAt.prod
  · apply analyticAt_pi_iff.mpr
    intro t
    change AnalyticAt ℝ (fun x => (p x).1 t 0 0) tau
    have hf : AnalyticAt ℝ (fun x => (p x).1) tau :=
      analyticAt_fst.comp ha
    exact analyticAt_pi_iff.mp
      (analyticAt_pi_iff.mp (analyticAt_pi_iff.mp hf t) 0) 0
  · apply analyticAt_pi_iff.mpr
    intro t
    change AnalyticAt ℝ (fun x => (p x).2 t 0 0) tau
    have hs : AnalyticAt ℝ (fun x => (p x).2) tau :=
      analyticAt_snd.comp ha
    exact analyticAt_pi_iff.mp
      (analyticAt_pi_iff.mp (analyticAt_pi_iff.mp hs t) 0) 0

/-- The genuine maximal one-species matrix branch is an analytic
pure-fluid BH root branch with the exact closed-form HS seed. -/
theorem maximalBranch_pure_path
    (xi : ℝ) (hxi0 : 0 < xi) (hxi1 : xi < 1)
    (z K : T → ℝ) (hz : ∀ t, 0 < z t)
    (M : FMSA.Convergence.MaximalCanonicalBranch.MaximalBranch
      z (rho1 xi) sigma1 (liftTail K)
      (0, MultiTailMixture.baseSeed z (rho1 xi) sigma1)) :
    lowerPath M.path 0 = (0, fun t => G0 xi (z t)) ∧
    AnalyticOnNhd ℝ (lowerPath M.path)
      (initialCouplings M.bound) ∧
    (∀ tau ∈ initialCouplings M.bound,
      MultiTail.IsRoot xi z (fun t => tau * K t)
        (lowerPath M.path tau).1 (lowerPath M.path tau).2) := by
  constructor
  · rw [lowerPath, M.at_seed]
    apply Prod.ext
    · funext t
      rfl
    · exact baseSeed_eq_pure xi hxi0 hxi1 z hz
  constructor
  · exact lowerPath_analyticOn M.path M.analytic
  · intro tau htau
    have hm := M.roots tau htau
    have hk : tau • liftTail K = liftTail (fun t => tau * K t) := by
      funext t i j
      simp [liftTail, Pi.smul_apply, smul_eq_mul]
    rw [hk, ← lift_lowerTail (M.path tau).1,
      ← lift_lowerTail (M.path tau).2] at hm
    exact (isRoot_iff xi hxi1.ne z (fun t => tau * K t)
      (lowerTail (M.path tau).1) (lowerTail (M.path tau).2)).mp hm

end FMSA.Convergence.PureFluidScalarMixtureBridge

/-- info: 'FMSA.Convergence.PureFluidScalarMixtureBridge.lift_lowerTail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PureFluidScalarMixtureBridge.lift_lowerTail

/-- info: 'FMSA.Convergence.PureFluidScalarMixtureBridge.etaMix_rho1_sigma1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PureFluidScalarMixtureBridge.etaMix_rho1_sigma1

/-- info: 'FMSA.Convergence.PureFluidScalarMixtureBridge.vacMix_rho1_sigma1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PureFluidScalarMixtureBridge.vacMix_rho1_sigma1

/-- info: 'FMSA.Convergence.PureFluidScalarMixtureBridge.Q0phys_eq_qp0' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PureFluidScalarMixtureBridge.Q0phys_eq_qp0

/-- info: 'FMSA.Convergence.PureFluidScalarMixtureBridge.Qppphys_eq_bA0' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PureFluidScalarMixtureBridge.Qppphys_eq_bA0

/-- info: 'FMSA.Convergence.PureFluidScalarMixtureBridge.W_eq_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PureFluidScalarMixtureBridge.W_eq_pure

/-- info: 'FMSA.Convergence.PureFluidScalarMixtureBridge.gam_eq_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PureFluidScalarMixtureBridge.gam_eq_pure

/-- info: 'FMSA.Convergence.PureFluidScalarMixtureBridge.C_eq_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PureFluidScalarMixtureBridge.C_eq_pure

/-- info: 'FMSA.Convergence.PureFluidScalarMixtureBridge.Mtil_term_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PureFluidScalarMixtureBridge.Mtil_term_eq

/-- info: 'FMSA.Convergence.PureFluidScalarMixtureBridge.Ntil_term_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PureFluidScalarMixtureBridge.Ntil_term_eq

/-- info: 'FMSA.Convergence.PureFluidScalarMixtureBridge.mixM_eq_pure_term' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PureFluidScalarMixtureBridge.mixM_eq_pure_term

/-- info: 'FMSA.Convergence.PureFluidScalarMixtureBridge.mixN_eq_pure_term' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PureFluidScalarMixtureBridge.mixN_eq_pure_term

/-- info: 'FMSA.Convergence.PureFluidScalarMixtureBridge.mixDA_N_coefficient_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PureFluidScalarMixtureBridge.mixDA_N_coefficient_eq

/-- info: 'FMSA.Convergence.PureFluidScalarMixtureBridge.mixDA_eq_pure_term' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PureFluidScalarMixtureBridge.mixDA_eq_pure_term

/-- info: 'FMSA.Convergence.PureFluidScalarMixtureBridge.mixDqp_eq_pure_term' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PureFluidScalarMixtureBridge.mixDqp_eq_pure_term

/-- info: 'FMSA.Convergence.PureFluidScalarMixtureBridge.amplitudeA_eq_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PureFluidScalarMixtureBridge.amplitudeA_eq_pure

/-- info: 'FMSA.Convergence.PureFluidScalarMixtureBridge.amplitudeQp_eq_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PureFluidScalarMixtureBridge.amplitudeQp_eq_pure

/-- info: 'FMSA.Convergence.PureFluidScalarMixtureBridge.dressedQhat_eq_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PureFluidScalarMixtureBridge.dressedQhat_eq_pure

/-- info: 'FMSA.Convergence.PureFluidScalarMixtureBridge.firstLHS_eq_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PureFluidScalarMixtureBridge.firstLHS_eq_pure

/-- info: 'FMSA.Convergence.PureFluidScalarMixtureBridge.secondLHS_eq_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PureFluidScalarMixtureBridge.secondLHS_eq_pure

/-- info: 'FMSA.Convergence.PureFluidScalarMixtureBridge.secondRHS_eq_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PureFluidScalarMixtureBridge.secondRHS_eq_pure

/-- info: 'FMSA.Convergence.PureFluidScalarMixtureBridge.isRoot_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PureFluidScalarMixtureBridge.isRoot_iff

/-- info: 'FMSA.Convergence.PureFluidScalarMixtureBridge.baseSeed_eq_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PureFluidScalarMixtureBridge.baseSeed_eq_pure

/-- info: 'FMSA.Convergence.PureFluidScalarMixtureBridge.lowerPath_analyticOn' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PureFluidScalarMixtureBridge.lowerPath_analyticOn

/-- info: 'FMSA.Convergence.PureFluidScalarMixtureBridge.maximalBranch_pure_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.PureFluidScalarMixtureBridge.maximalBranch_pure_path
