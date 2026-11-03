import MSAConvergence.PureFluidMixedPicard

set_option linter.style.header false

/-! Restricting the multivariate series to a ray `K_t τ` gives the Taylor series of the actual
hard-sphere germ along that ray, with an explicit polynomial in `K` at each order. -/

noncomputable section
open Filter Topology
namespace FMSA.Convergence.PureFluidMixedRay
open FMSA.Convergence.PureFluidMixedPicard
open FMSA.Convergence.PureFluidRFormalSolution
open FMSA.Convergence.PureFluidThetaFixedPointUniqueness
open FMSA.Convergence.PureFluidPositiveSubstitution
open FMSA.Convergence.PureFluidThetaCouplingTaylor
open FMSA.Convergence.PureFluidHardSphereNodePositivity
open FMSA.Convergence.AnalyticScalarTaylorPowerSeries

variable {T : Type*} [Fintype T] [DecidableEq T]

/-- The ray in the tail strengths. -/
def ray (K : T → ℝ) (t : T) : PowerSeries ℝ := PowerSeries.C (K t) * PowerSeries.X

theorem ray_constantCoeff (K : T → ℝ) (t : T) : PowerSeries.constantCoeff (ray K t) = 0 := by
  simp [ray]

theorem ray_hasSubst (K : T → ℝ) : MvPowerSeries.HasSubst (ray K) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (ray_constantCoeff K)

/-- Restriction to the ray. -/
def res (K : T → ℝ) (f : MvPowerSeries T ℝ) : PowerSeries ℝ := MvPowerSeries.subst (ray K) f

theorem res_add (K : T → ℝ) (f g : MvPowerSeries T ℝ) : res K (f + g) = res K f + res K g :=
  MvPowerSeries.subst_add (ray_hasSubst K) f g

theorem res_sub (K : T → ℝ) (f g : MvPowerSeries T ℝ) : res K (f - g) = res K f - res K g :=
  MvPowerSeries.subst_sub (ray_hasSubst K) f g

theorem res_mul (K : T → ℝ) (f g : MvPowerSeries T ℝ) : res K (f * g) = res K f * res K g :=
  MvPowerSeries.subst_mul (ray_hasSubst K) f g

theorem res_pow (K : T → ℝ) (f : MvPowerSeries T ℝ) (n : ℕ) : res K (f ^ n) = res K f ^ n :=
  MvPowerSeries.subst_pow (ray_hasSubst K) f n

theorem res_X (K : T → ℝ) (t : T) : res K (MvPowerSeries.X t) = ray K t :=
  MvPowerSeries.subst_X (ray_hasSubst K) t

theorem res_C (K : T → ℝ) (c : ℝ) : res K (MvPowerSeries.C c) = PowerSeries.C c := by
  have h := MvPowerSeries.subst_monomial (ray_hasSubst K) (0 : T →₀ ℕ) c
  simpa [res, MvPowerSeries.monomial_zero_eq_C_apply, PowerSeries.smul_eq_C_mul] using h

theorem res_one (K : T → ℝ) : res K (1 : MvPowerSeries T ℝ) = 1 := by
  simpa using res_C K 1

/-- Restriction sends the geometric inverse to the geometric inverse. -/
theorem res_inv (K : T → ℝ) {g : MvPowerSeries T ℝ} (h0 : MvPowerSeries.constantCoeff g = 0) :
    res K (1 - g)⁻¹ = (1 - res K g)⁻¹ := by
  have hc : MvPowerSeries.constantCoeff (1 - g) ≠ 0 := by simp [h0]
  have hm := congrArg (res K) (MvPowerSeries.mul_inv_cancel (1 - g) hc)
  rw [res_mul, res_sub, res_one] at hm
  have hg0 : PowerSeries.constantCoeff (res K g) = 0 :=
    MvPowerSeries.constantCoeff_subst_eq_zero (ray_hasSubst K) (ray_constantCoeff K) h0
  have hc' : PowerSeries.constantCoeff (1 - res K g) ≠ 0 := by simp [hg0]
  rw [PowerSeries.eq_inv_iff_mul_eq_one hc']
  rw [mul_comm]; exact hm

/-- Restriction of a substitution. -/
theorem res_subst (K : T → ℝ) {a : T → MvPowerSeries T ℝ}
    (h0 : ∀ t, MvPowerSeries.constantCoeff (a t) = 0) (f : MvPowerSeries T ℝ) :
    res K (MvPowerSeries.subst a f) = MvPowerSeries.subst (fun t => res K (a t)) f :=
  MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero h0)
    (ray_hasSubst K) f

/-- The monomial `K^m τ^|m|`. -/
theorem ray_prod (K : T → ℝ) (m : T →₀ ℕ) :
    (m.prod fun t k => ray K t ^ k) =
      PowerSeries.C (m.prod fun t k => K t ^ k) * PowerSeries.X ^ (∑ t ∈ m.support, m t) := by
  classical
  simp only [Finsupp.prod, ray, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    map_prod, map_pow]

/-- The coefficient of `τ^n` on the ray as a polynomial in `K`. -/
theorem coeff_res (K : T → ℝ) (f : MvPowerSeries T ℝ) (n : ℕ) :
    PowerSeries.coeff n (res K f) =
      ∑ m ∈ Finset.univ.finsuppAntidiag n, MvPowerSeries.coeff m f * m.prod fun t k => K t ^ k := by
  classical
  change MvPowerSeries.coeff (Finsupp.single () n) (MvPowerSeries.subst (ray K) f) = _
  rw [MvPowerSeries.coeff_subst (ray_hasSubst K)]
  have hterm : ∀ m : T →₀ ℕ, MvPowerSeries.coeff m f • MvPowerSeries.coeff (Finsupp.single () n)
      (m.prod fun t k => ray K t ^ k) =
      if m ∈ Finset.univ.finsuppAntidiag n then
        MvPowerSeries.coeff m f * m.prod fun t k => K t ^ k else 0 := by
    intro m
    have hsum : ∑ t ∈ m.support, m t = ∑ t, m t :=
      Finset.sum_subset (Finset.subset_univ _) fun t _ ht => by simpa using ht
    have hc : MvPowerSeries.coeff (Finsupp.single () n) (m.prod fun t k => ray K t ^ k) =
        PowerSeries.coeff n (m.prod fun t k => ray K t ^ k) := rfl
    have hmem : m ∈ Finset.univ.finsuppAntidiag n ↔ ∑ t, m t = n := by
      simp [Finset.mem_finsuppAntidiag]
    rw [hc, ray_prod, PowerSeries.coeff_C_mul_X_pow, hsum, smul_eq_mul]
    by_cases h : ∑ t, m t = n
    · rw [if_pos (hmem.mpr h), if_pos h.symm]
    · rw [if_neg (fun e => h (hmem.mp e)), if_neg (fun e => h e.symm), mul_zero]
  simp only [hterm]
  rw [finsum_eq_sum_of_support_subset (s := Finset.univ.finsuppAntidiag n)]
  · exact Finset.sum_congr rfl fun m hm => if_pos hm
  · intro m hm
    by_contra hn
    exact hm (if_neg hn)

/-- Nonnegative mixed coefficients give nonnegative ray coefficients for nonnegative strengths. -/
theorem res_coeffNonneg {K : T → ℝ} (hK : ∀ t, 0 ≤ K t) {f : MvPowerSeries T ℝ} (hf : NN f) :
    CoeffNonneg (res K f) := fun n => by
  rw [coeff_res]
  refine Finset.sum_nonneg fun m _ => mul_nonneg (hf m) ?_
  exact Finset.prod_nonneg fun t _ => pow_nonneg (hK t) _

/-- The physical strength per unit `K`. -/
def alphaUnit (xi : ℝ) (z : T → ℝ) (t : T) : ℝ := physicalAlpha xi z (fun _ => 1) t

/-- The physical `κ`. -/
def kappaOf (xi : ℝ) (z : T → ℝ) (t : T) : ℝ := hardKappa xi (z t)

/-- `θ` in the tail strengths. -/
def thetaK (xi : ℝ) (z : T → ℝ) : T → MvPowerSeries T ℝ :=
  thetaM z (alphaUnit xi z) (kappaOf xi z)

/-- `r` in the tail strengths. -/
def rK (xi : ℝ) (z : T → ℝ) (t : T) : MvPowerSeries T ℝ :=
  MvPowerSeries.subst (thetaK xi z) (RSeries z t)

/-- `H` in the tail strengths. -/
def hK (xi : ℝ) (z : T → ℝ) (t : T) : MvPowerSeries T ℝ :=
  MvPowerSeries.subst (thetaK xi z) (physicalH z t)

/-- `1/(1 - κ r)` in the tail strengths. -/
def qK (xi : ℝ) (z : T → ℝ) (t : T) : MvPowerSeries T ℝ :=
  (1 - MvPowerSeries.C (kappaOf xi z t) * rK xi z t)⁻¹

theorem thetaK_constantCoeff (xi : ℝ) (z : T → ℝ) (t : T) :
    MvPowerSeries.constantCoeff (thetaK xi z t) = 0 := thetaM_constantCoeff t

theorem rK_constantCoeff (xi : ℝ) (z : T → ℝ) (t : T) :
    MvPowerSeries.constantCoeff (rK xi z t) = 0 :=
  subst_constantCoeff_zero (thetaK_constantCoeff xi z) (RSeries_constantCoeff z t)

theorem res_r (xi : ℝ) (z K : T → ℝ) (t : T) :
    res K (rK xi z t) = MvPowerSeries.subst (fun u => res K (thetaK xi z u)) (RSeries z t) :=
  res_subst K (thetaK_constantCoeff xi z) _

theorem res_H (xi : ℝ) (z K : T → ℝ) (t : T) :
    res K (hK xi z t) = MvPowerSeries.subst (fun u => res K (thetaK xi z u)) (physicalH z t) :=
  res_subst K (thetaK_constantCoeff xi z) _

theorem res_q (xi : ℝ) (z K : T → ℝ) (t : T) :
    res K (qK xi z t) = (1 - PowerSeries.C (kappaOf xi z t) * res K (rK xi z t))⁻¹ := by
  have hg : MvPowerSeries.constantCoeff (MvPowerSeries.C (kappaOf xi z t) * rK xi z t) = 0 := by
    simp [rK_constantCoeff]
  unfold qK
  rw [res_inv K hg, res_mul, res_C]

/-- The restricted `θ` solves the one-variable Picard equation of the ray. -/
theorem res_theta_fixed (xi : ℝ) (z K : T → ℝ) (t : T) :
    res K (thetaK xi z t) =
      PowerSeries.C (physicalAlpha xi z K t) * PowerSeries.X *
        (1 - PowerSeries.C (hardKappa xi (z t)) *
          MvPowerSeries.subst (fun u => res K (thetaK xi z u)) (RSeries z t))⁻¹ ^ 2 := by
  have hfix := thetaM_fixed (z := z) (a := alphaUnit xi z) (κ := kappaOf xi z) t
  have h := congrArg (res K) hfix
  have hq := res_q xi z K t
  rw [res_r xi z K t] at hq
  have hq' : res K ((1 - MvPowerSeries.C (kappaOf xi z t) *
      MvPowerSeries.subst (thetaM z (alphaUnit xi z) (kappaOf xi z)) (RSeries z t))⁻¹) =
      (1 - PowerSeries.C (hardKappa xi (z t)) *
        MvPowerSeries.subst (fun u => res K (thetaK xi z u)) (RSeries z t))⁻¹ := hq
  rw [res_mul, res_C, res_mul, res_X, res_pow, hq'] at h
  have hα : physicalAlpha xi z K t = alphaUnit xi z t * K t := by
    simp only [alphaUnit, physicalAlpha]; ring
  rw [hα, map_mul]
  change res K (thetaM z (alphaUnit xi z) (kappaOf xi z) t) = _
  rw [h, ray]
  ring

/-- Any zero-seeded solution of the one-variable Picard equation is the restriction. -/
theorem res_theta_eq (xi : ℝ) (z K : T → ℝ) {θS : T → PowerSeries ℝ}
    (h0 : ∀ t, PowerSeries.constantCoeff (θS t) = 0)
    (hfix : ∀ t, θS t = PowerSeries.C (physicalAlpha xi z K t) * PowerSeries.X *
      (1 - PowerSeries.C (hardKappa xi (z t)) * MvPowerSeries.subst θS (RSeries z t))⁻¹ ^ 2) :
    (fun t => res K (thetaK xi z t)) = θS := by
  refine theta_fixed_point_unique z (physicalAlpha xi z K) (fun t => hardKappa xi (z t)) _ θS
    (fun t => ?_) h0 (res_theta_fixed xi z K) hfix
  exact MvPowerSeries.constantCoeff_subst_eq_zero (ray_hasSubst K) (ray_constantCoeff K)
    (thetaK_constantCoeff xi z t)


end FMSA.Convergence.PureFluidMixedRay

/-- info: 'FMSA.Convergence.PureFluidMixedRay.ray_constantCoeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedRay.ray_constantCoeff
/-- info: 'FMSA.Convergence.PureFluidMixedRay.ray_hasSubst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedRay.ray_hasSubst
/-- info: 'FMSA.Convergence.PureFluidMixedRay.res_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedRay.res_add
/-- info: 'FMSA.Convergence.PureFluidMixedRay.res_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedRay.res_sub
/-- info: 'FMSA.Convergence.PureFluidMixedRay.res_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedRay.res_mul
/-- info: 'FMSA.Convergence.PureFluidMixedRay.res_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedRay.res_pow
/-- info: 'FMSA.Convergence.PureFluidMixedRay.res_X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedRay.res_X
/-- info: 'FMSA.Convergence.PureFluidMixedRay.res_C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedRay.res_C
/-- info: 'FMSA.Convergence.PureFluidMixedRay.res_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedRay.res_one
/-- info: 'FMSA.Convergence.PureFluidMixedRay.res_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedRay.res_inv
/-- info: 'FMSA.Convergence.PureFluidMixedRay.res_subst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedRay.res_subst
/-- info: 'FMSA.Convergence.PureFluidMixedRay.ray_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedRay.ray_prod
/-- info: 'FMSA.Convergence.PureFluidMixedRay.coeff_res' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedRay.coeff_res
/-- info: 'FMSA.Convergence.PureFluidMixedRay.res_coeffNonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedRay.res_coeffNonneg
/-- info: 'FMSA.Convergence.PureFluidMixedRay.thetaK_constantCoeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedRay.thetaK_constantCoeff
/-- info: 'FMSA.Convergence.PureFluidMixedRay.rK_constantCoeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedRay.rK_constantCoeff
/-- info: 'FMSA.Convergence.PureFluidMixedRay.res_r' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedRay.res_r
/-- info: 'FMSA.Convergence.PureFluidMixedRay.res_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedRay.res_H
/-- info: 'FMSA.Convergence.PureFluidMixedRay.res_q' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedRay.res_q
/-- info: 'FMSA.Convergence.PureFluidMixedRay.res_theta_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedRay.res_theta_fixed
/-- info: 'FMSA.Convergence.PureFluidMixedRay.res_theta_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidMixedRay.res_theta_eq
