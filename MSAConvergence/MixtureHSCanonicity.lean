import MSAConvergence.MixtureHSContinuity

/-! Full HS canonicity for every finite physical mixture. A clopen argument
on the convex density domain uses the proved collective axis identity,
actual inverse perturbation and the proved zero-free closure principle. -/
noncomputable section
open Set Real Filter Topology
open scoped BigOperators ContDiff
namespace FMSA.Convergence.MixtureHSCanonicity
open FMSA.Paper FMSA.MatrixQ0 FMSA.ExactMSA.MultiTailMixture
open FMSA.Convergence.MixtureHSKernel FMSA.Convergence.MixtureHSContinuity
open FMSA.Convergence.CanonicalFirstLoss FMSA.Convergence.HolomorphicZeroPersistence
open FMSA.Convergence.CanonicalNeighborhood FMSA.Convergence.LowDensityCanonicalSeed
open FMSA.Convergence.MaximalCanonicalBranch FMSA.Convergence.MaximalMSAConvergence
variable {N : ℕ}

/-- Packing fraction is linear in the density vector at fixed diameters. -/
def packingLinear (sigma : Fin N → ℝ) : (Fin N → ℝ) →ₗ[ℝ] ℝ where
  toFun rho := etaMix rho sigma
  map_add' x y := by
    unfold etaMix
    simp only [Pi.add_apply,add_mul,Finset.sum_add_distrib,mul_add]
  map_smul' a x := by
    simp only [etaMix,Pi.smul_apply,smul_eq_mul,RingHom.id_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

def physicalDensities (sigma : Fin N → ℝ) : Set (Fin N → ℝ) :=
  {rho | (∀ i, 0 ≤ rho i) ∧ etaMix rho sigma < 1}

/-- Unequal diameters and tracer faces preserve convexity of the full
physical density domain. -/
theorem physical_densities_convex (sigma : Fin N → ℝ) :
    Convex ℝ (physicalDensities sigma) := by
  have hpos : Convex ℝ {rho : Fin N → ℝ | ∀ i, 0 ≤ rho i} := by
    intro x hx y hy a b ha hb _ i
    exact add_nonneg (mul_nonneg ha (hx i)) (mul_nonneg hb (hy i))
  exact hpos.inter ((convex_Iio (1 : ℝ)).linear_preimage (packingLinear sigma))

/-- Vacuum is an actual physical density point at every diameter vector. -/
theorem zero_mem_physical_densities (sigma : Fin N → ℝ) :
    (0 : Fin N → ℝ) ∈ physicalDensities sigma := by simp [physicalDensities,etaMix]

/-- The actual HS symbol vanishes at vacuum, at every frequency. -/
theorem seed_symbol_zero_density (sigma : Fin N → ℝ) (s : ℂ) :
    seedSymbol (0 : Fin N → ℝ) sigma s = 0 := by
  ext i j
  simp [seedSymbol,seedKernel,rdfMatrixLaplace,nonlinearCausalKernel,FMSA.causalComplexLaplace]

/-- FULL actual HS canonicity is relatively open on the physical domain,
proved from the true inverse and coefficient-integral perturbation bound. -/
theorem canonical_densities_isOpen (sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i) :
    IsOpen {rho : physicalDensities sigma | ∀ s : ℂ, 0 ≤ s.re → IsUnit (seedFactor rho.val sigma s)} := by
  apply isOpen_iff_mem_nhds.mpr
  intro rho hrho
  have hv : 0 < vacMix rho.val sigma := by unfold vacMix; linarith [rho.property.2]
  exact (seed_canonicity_eventually rho.val sigma hsigma hv.ne' hrho).filter_mono
    (continuous_subtype_val.tendsto rho)

/-- A limit of canonical physical densities remains canonical. The
strictly-right determinant cannot acquire an interior zero; the axis was
proved independently by the collective identity and true static integrals. -/
theorem canonical_densities_isClosed (sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i) :
    IsClosed {rho : physicalDensities sigma | ∀ s : ℂ, 0 ≤ s.re → IsUnit (seedFactor rho.val sigma s)} := by
  apply isClosed_of_closure_subset
  intro rho hrho
  have hv : 0 < vacMix rho.val sigma := by unfold vacMix; linarith [rho.property.2]
  have ha (r : physicalDensities sigma) :
      AnalyticOnNhd ℂ (seedDet r.val sigma) {s : ℂ | 0 < s.re} :=
    renewal_det_analytic_right emptyRates empty_rates_pos r.val sigma hsigma (0,0)
  have hn : ∃ s : ℂ, 0 < s.re ∧ seedDet rho.val sigma s ≠ 0 :=
    renewal_det_exists_nonzero_right emptyRates empty_rates_pos rho.val sigma hsigma (0,0)
  have hj (s : ℂ) (hs : 0 < s.re) :
      ContinuousAt (fun x : physicalDensities sigma × ℂ => seedDet x.1.val sigma x.2) (rho,s) := by
    have hc : ContinuousAt (fun x : physicalDensities sigma × ℂ => (x.1.val,x.2)) (rho,s) := by fun_prop
    exact ContinuousAt.comp (f := fun x : physicalDensities sigma × ℂ => (x.1.val,x.2)) (x := (rho,s))
      (seed_det_joint_continuousAt rho.val sigma hsigma hv.ne' s hs) hc
  have hz := zero_free_at_closure (fun r : physicalDensities sigma => seedDet r.val sigma)
    {r : physicalDensities sigma | ∀ s : ℂ, 0 ≤ s.re → IsUnit (seedFactor r.val sigma s)} rho
    {s : ℂ | 0 < s.re} (isOpen_lt continuous_const Complex.continuous_re)
    (convex_halfSpace_re_gt (0 : ℝ)).isPreconnected hrho (ha rho) hn hj
    (fun r _ => (ha r).differentiableOn)
    (fun r hr s hs => isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp (hr s hs.le)))
  intro s hs
  by_cases hp : 0 < s.re
  · exact (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (hz s hp))
  · exact seed_factor_imaginary_isUnit rho.val sigma rho.property.1 hsigma hv s (le_antisymm (le_of_not_gt hp) hs)

/-- For EVERY finite physical mixture (unequal diameters, arbitrary tracer
faces, eta<1), the ACTUAL HS factor is a unit on the ENTIRE closed right
half-plane. No no-spinodal, homotopy or new mathematical axiom is used. -/
theorem seed_factor_closed_right_isUnit (rho sigma : Fin N → ℝ)
    (hrho : ∀ i, 0 ≤ rho i) (hsigma : ∀ i, 0 ≤ sigma i) (heta : etaMix rho sigma < 1)
    (s : ℂ) (hs : 0 ≤ s.re) : IsUnit (seedFactor rho sigma s) := by
  letI : PreconnectedSpace (physicalDensities sigma) :=
    Subtype.preconnectedSpace (physical_densities_convex sigma).isPreconnected
  have hc : IsClopen {r : physicalDensities sigma | ∀ s : ℂ, 0 ≤ s.re → IsUnit (seedFactor r.val sigma s)} :=
    ⟨canonical_densities_isClosed sigma hsigma,canonical_densities_isOpen sigma hsigma⟩
  have hn : {r : physicalDensities sigma | ∀ s : ℂ, 0 ≤ s.re → IsUnit (seedFactor r.val sigma s)}.Nonempty := by
    refine ⟨⟨0,zero_mem_physical_densities sigma⟩,?_⟩
    intro w _
    simp only [seedFactor,seed_symbol_zero_density,sub_zero]
    exact isUnit_one
  have he := hc.eq_univ hn
  have hm : (⟨rho,hrho,heta⟩ : physicalDensities sigma) ∈
      {r : physicalDensities sigma | ∀ s : ℂ, 0 ≤ s.re → IsUnit (seedFactor r.val sigma s)} := by rw [he]; trivial
  exact hm s hs

/-- The full-canonicity conclusion is for the ORIGINAL nonlinear MSA kernel
at HS, for ANY finite tail representation and ANY irrelevant HS G value. -/
theorem actual_mixture_hs_canonical {T : Type*} [Fintype T] (z : T → ℝ)
    (rho sigma : Fin N → ℝ) (hrho : ∀ i, 0 ≤ rho i) (hsigma : ∀ i, 0 ≤ sigma i)
    (heta : etaMix rho sigma < 1) (G : TailMatrix T N) :
    (0,G) ∈ canonicalAmplitudes z rho sigma := by
  intro s hs
  have h := seed_factor_closed_right_isUnit rho sigma hrho hsigma heta s hs
  simpa only [seedFactor,seedSymbol,seed_kernel_eq_actual z rho sigma G] using h

/-- The maximal initial analytic canonical MSA branch now exists from
physical DATA ALONE for every finite mixture at eta<1. No supplied initial
canonicity, root curve, inverse or maximality is required. -/
theorem exists_mixture_hs_maximal_branch {T : Type*} [Fintype T]
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (hv : 0 < vacMix rho sigma) :
    ∃ M : MaximalBranch z rho sigma K (0,baseSeed z rho sigma),
      M.bound = maximalBound z rho sigma K (0,baseSeed z rho sigma) := by
  have heta : etaMix rho sigma < 1 := by unfold vacMix at hv; linarith
  exact exists_hs_maximal_branch_of_initial_canonicity z hz rho sigma hsigma hrho K hK hv
    (actual_mixture_hs_canonical z rho sigma hrho (fun i => (hsigma i).le) heta (baseSeed z rho sigma))

end FMSA.Convergence.MixtureHSCanonicity

/-- info: 'FMSA.Convergence.MixtureHSCanonicity.physical_densities_convex' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureHSCanonicity.physical_densities_convex

/-- info: 'FMSA.Convergence.MixtureHSCanonicity.zero_mem_physical_densities' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureHSCanonicity.zero_mem_physical_densities

/-- info: 'FMSA.Convergence.MixtureHSCanonicity.seed_symbol_zero_density' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureHSCanonicity.seed_symbol_zero_density

/-- info: 'FMSA.Convergence.MixtureHSCanonicity.canonical_densities_isOpen' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureHSCanonicity.canonical_densities_isOpen

/-- info: 'FMSA.Convergence.MixtureHSCanonicity.canonical_densities_isClosed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureHSCanonicity.canonical_densities_isClosed

/-- info: 'FMSA.Convergence.MixtureHSCanonicity.seed_factor_closed_right_isUnit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureHSCanonicity.seed_factor_closed_right_isUnit

/-- info: 'FMSA.Convergence.MixtureHSCanonicity.actual_mixture_hs_canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureHSCanonicity.actual_mixture_hs_canonical

/-- info: 'FMSA.Convergence.MixtureHSCanonicity.exists_mixture_hs_maximal_branch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureHSCanonicity.exists_mixture_hs_maximal_branch

