import FMSAPaper.SpatialDictionary

/-! Pointwise differentiation preserves the finite spatial space. No smoothly
chosen coordinates or linearly independent dictionary are assumed. -/
noncomputable section
open Filter Topology Set
open scoped ContDiff

namespace FMSA.Paper.SpatialJets

open SpatialDictionary
variable {T : Type*} [Fintype T]

theorem derivative_hasForm (z : T → ℝ) (s : Set ℝ) (f : ℝ → ℝ → ℝ) (x : ℝ)
    (hmem : ∀ᶠ t in 𝓝 x, HasForm z s (f t))
    (hdiff : ∀ r ∈ s, DifferentiableAt ℝ (fun t => f t r) x) :
    HasForm z s (fun r => deriv (fun t => f t r) x) := by
  letI := space_finiteDimensional z s
  have hx := hmem.self_of_nhds
  have hlim : Tendsto (fun t => fun r : s => (t-x)⁻¹ * (f t r - f x r))
      (𝓝[≠] x) (𝓝 (fun r : s => deriv (fun t => f t r) x)) := by
    apply tendsto_pi_nhds.mpr
    intro r
    exact (hdiff r r.property).hasDerivAt.tendsto_slope
  apply (space z s).closed_of_finiteDimensional.mem_of_tendsto hlim
  filter_upwards [hmem.filter_mono nhdsWithin_le_nhds] with t ht
  exact (space z s).smul_mem ((t-x)⁻¹) ((space z s).sub_mem ht hx)

theorem iteratedDeriv_hasForm_on (z : T → ℝ) (s U : Set ℝ) (hU : IsOpen U)
    (f : ℝ → ℝ → ℝ) (n : ℕ)
    (hmem : ∀ t ∈ U, HasForm z s (f t))
    (hsmooth : ∀ r ∈ s, ContDiffOn ℝ n (fun t => f t r) U) :
    ∀ m, m <= n → ∀ x ∈ U, HasForm z s (fun r => iteratedDeriv m (fun t => f t r) x) := by
  intro m
  induction m with
  | zero =>
    intro _ x hx
    simpa only [iteratedDeriv_zero] using hmem x hx
  | succ m ih =>
    intro hmn x hx
    simp only [iteratedDeriv_succ]
    apply derivative_hasForm
    · filter_upwards [hU.mem_nhds hx] with t ht
      exact ih (by omega) t ht
    · intro r hr
      have hm : (m : ℕ∞ω) < (n : ℕ∞ω) := by exact_mod_cast (show m < n by omega)
      have hd := (hsmooth r hr).differentiableOn_iteratedDerivWithin hm hU.uniqueDiffOn
      have he : iteratedDerivWithin m (fun t => f t r) U =ᶠ[𝓝 x]
          iteratedDeriv m (fun t => f t r) := by
        filter_upwards [hU.mem_nhds hx] with t ht
        exact iteratedDerivWithin_of_isOpen hU ht
      exact (hd.differentiableAt (hU.mem_nhds hx)).congr_of_eventuallyEq he.symm

theorem jet_hasForm_of_smooth_parameters {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (z : T → ℝ) (s : Set ℝ) (F : E → ℝ → ℝ)
    (hmem : ∀ a, HasForm z s (F a))
    (hsmooth : ∀ r ∈ s, ContDiff ℝ ∞ (fun a => F a r))
    (p : ℝ → E) (n : ℕ) (hp : ContDiffAt ℝ n p 0) :
    HasForm z s (fun r => ExactMSA.BSource.jet (fun t => F (p t) r) n) := by
  obtain ⟨U, hU, hpU⟩ := hp.contDiffOn (m := (n : ℕ∞ω)) le_rfl (by simp)
  obtain ⟨V, hVU, hV, h0V⟩ := mem_nhds_iff.mp hU
  have hpV := hpU.mono hVU
  have hs (r : ℝ) (hr : r ∈ s) : ContDiffOn ℝ n (fun t => F (p t) r) V :=
    ((hsmooth r hr).of_le (by exact_mod_cast le_top)).comp_contDiffOn hpV
  have h := iteratedDeriv_hasForm_on z s V hV (fun t => F (p t)) n
    (fun t _ => hmem (p t)) hs n le_rfl 0 h0V
  apply (h.const_mul ((n.factorial : ℝ)⁻¹)).congr
  intro r _
  simp only [ExactMSA.BSource.jet, div_eq_mul_inv, mul_comm]

theorem weighted_truncation_hasForm (z : T → ℝ) (s : Set ℝ) (c : ℕ → ℝ → ℝ)
    (p : ℕ) (tau : ℝ) (hc : ∀ n, n <= p → HasForm z s (fun r => r * c n r)) :
    HasForm z s (fun r => r * ∑ n ∈ Finset.range (p + 1), tau ^ n * c n r) := by
  have h := (space z s).sum_mem (t := Finset.range (p + 1))
    (fun n hn => (space z s).smul_mem (tau ^ n) (hc n (by
      have := Finset.mem_range.mp hn
      omega)))
  have hs : HasForm z s (fun r => ∑ n ∈ Finset.range (p + 1), tau ^ n * (r * c n r)) := by
    change (fun r : s => ∑ n ∈ Finset.range (p + 1), tau ^ n * (r * c n r)) ∈ space z s
    convert h using 1
    ext r
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply hs.congr
  intro r _
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  ring

end FMSA.Paper.SpatialJets

/-- info: 'FMSA.Paper.SpatialJets.derivative_hasForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SpatialJets.derivative_hasForm

/-- info: 'FMSA.Paper.SpatialJets.iteratedDeriv_hasForm_on' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SpatialJets.iteratedDeriv_hasForm_on

/-- info: 'FMSA.Paper.SpatialJets.jet_hasForm_of_smooth_parameters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SpatialJets.jet_hasForm_of_smooth_parameters

/-- info: 'FMSA.Paper.SpatialJets.weighted_truncation_hasForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SpatialJets.weighted_truncation_hasForm
