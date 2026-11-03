import MSAConvergence.M3TaylorRadius
import MSAConvergence.MixedSignRadiusObstruction
import MSAConvergence.ActualCanonicalBranch

/-! Transfer a checked M3 monodromy bound from its locally constructed HS
germ to the coefficients of the actual maximal canonical branch. -/
noncomputable section
namespace FMSA.Convergence.M3CanonicalRadiusTransfer
open Set Filter Topology
open FMSA.Paper FMSA.Paper.TaylorRoot FMSA.Paper.FoldRadius
open FMSA.Paper.StableIntervalRadius
open FMSA.Convergence.M3TaylorRadius FMSA.Convergence.M3ResidualModel
open FMSA.Convergence.M3MonodromyPath FMSA.Convergence.ActualCanonicalBranch
open FMSA.Convergence.MaximalCanonicalBranch
open FMSA.Convergence.MixtureHSCanonicity
open FMSA.Convergence.CanonicalNeighborhood
open FMSA.Convergence.MixedSignRadiusObstruction
open FMSA.ExactMSA.MultiTailMixture FMSA.ExactMSA.BSource FMSA.MatrixQ0
open ComplexTaylorCells ComplexTaylorPaths

variable {N : ℕ} {T : Type*} [Fintype T]

/-- For a vector-valued real analytic germ, each scalar projection of the
formal series coefficient is its ordinary Taylor jet. -/
theorem projected_coeff_eq_jet
    (p : ℝ → TailMatrix T N × TailMatrix T N)
    (a : FormalMultilinearSeries ℝ ℝ (TailMatrix T N × TailMatrix T N))
    (ha : HasFPowerSeriesAt p a 0)
    (l : (TailMatrix T N × TailMatrix T N) →L[ℝ] ℝ) (n : ℕ) :
    l (a.coeff n) = jet (l ∘ p) n := by
  let q := l.compFormalMultilinearSeries a
  have hq : HasFPowerSeriesAt (l ∘ p) q 0 := by
    obtain ⟨r, hr⟩ := ha
    exact ⟨r, l.comp_hasFPowerSeriesOnBall hr⟩
  have heq : q = FormalMultilinearSeries.ofScalars ℝ
      (fun m => iteratedDeriv m (l ∘ p) 0 / m.factorial) :=
    hq.eq_formalMultilinearSeries hq.analyticAt.hasFPowerSeriesAt
  have hc := congrArg (fun s : FormalMultilinearSeries ℝ ℝ ℝ => s.coeff n) heq
  change l (a.coeff n) =
    (FormalMultilinearSeries.ofScalars ℝ
      (fun m => iteratedDeriv m (l ∘ p) 0 / m.factorial)).coeff n at hc
  simpa only [FormalMultilinearSeries.coeff_ofScalars, jet] using hc

/-- The vector power-series coefficients are exactly the original BH
`(D,G)` branch coefficients, component by component. -/
theorem coeff_eq_branchCoefficients
    (p : ℝ → TailMatrix T N × TailMatrix T N)
    (a : FormalMultilinearSeries ℝ ℝ (TailMatrix T N × TailMatrix T N))
    (ha : HasFPowerSeriesAt p a 0) :
    (fun n => a.coeff n) = branchCoefficients p := by
  funext n
  apply Prod.ext <;> funext u i j
  · let l : (TailMatrix T N × TailMatrix T N) →L[ℝ] ℝ :=
      (entry u i j).comp (ContinuousLinearMap.fst ℝ _ _)
    have h := projected_coeff_eq_jet p a ha l n
    have hf : (l ∘ p) = (fun t => (p t).1 u i j) := by
      funext t
      simp [l, entry]
    rw [hf] at h
    simpa [l, entry, branchCoefficients] using h
  · let l : (TailMatrix T N × TailMatrix T N) →L[ℝ] ℝ :=
      (entry u i j).comp (ContinuousLinearMap.snd ℝ _ _)
    have h := projected_coeff_eq_jet p a ha l n
    have hf : (l ∘ p) = (fun t => (p t).2 u i j) := by
      funext t
      simp [l, entry]
    rw [hf] at h
    simpa [l, entry, branchCoefficients] using h

/-- A changed M3 lift controls the coefficients of the actual maximal
HS-seeded canonical branch, regardless of which analytic extension of its
local germ was returned by the monodromy theorem. -/
theorem maximal_branch_nonsummable_of_chainL
    (chain₀ rest : List Slab)
    (h₀ : chainRest chain₀ = true)
    (hrest : chainFrom (lastPosL chain₀) (lastCellL chain₀) rest = true)
    (hpos : headPos chain₀ = (0, 0))
    (hA : lastPosL chain₀ = (0, G))
    (hB : lastPos (lastPosL chain₀) rest = (4, G))
    (hdisj : boxDisjoint 4 (lastCellL chain₀)
      (lastCell (lastCellL chain₀) rest) = true)
    (hseed : seedOK (headCell chain₀) = true)
    (M : MaximalBranch z rho sigma strengths (0, baseSeed z rho sigma)) :
    ∀ tau : ℝ, 84 < |tau| →
      ¬Summable (fun n => tau ^ n • branchCoefficients M.path n) := by
  obtain ⟨p, a, hp0, ha, hroot, _, _, hdiv⟩ :=
    radius_of_chainL chain₀ rest h₀ hrest hpos hA hB hdisj hseed
  obtain ⟨hz, hsigma, hrho, hK⟩ := physical_data
  have hv : vacMix rho sigma ≠ 0 := by rw [vacancy_eq]; norm_num
  have hM0 : (0 : ℝ) ∈ initialCouplings M.bound :=
    ⟨le_rfl, by simpa using M.positive⟩
  have hcoeff : branchCoefficients p = branchCoefficients M.path :=
    actual_canonical_root_coefficients_unique z hz rho sigma hsigma hrho
      strengths hK hv p M.path ha.continuousAt
      (M.analytic 0 hM0).continuousAt (by rw [hp0, M.at_seed])
      hroot M.local_roots (by simpa only [hp0, M.at_seed] using M.canonical 0 hM0)
  have hseries : (fun n => a.coeff n) = branchCoefficients M.path :=
    (coeff_eq_branchCoefficients p a ha).trans hcoeff
  intro tau htau
  simpa only [← hseries] using hdiv tau htau

omit [Fintype T] in
/-- Componentwise summability of the finite original BH amplitudes implies
summability of their product-valued series. -/
theorem summable_vector_of_component_hasSum
    (c : ℕ → TailMatrix T N × TailMatrix T N) (tau : ℝ)
    (b : TailMatrix T N × TailMatrix T N)
    (hD : ∀ u i j, HasSum (fun n => (c n).1 u i j * tau ^ n) (b.1 u i j))
    (hG : ∀ u i j, HasSum (fun n => (c n).2 u i j * tau ^ n) (b.2 u i j)) :
    Summable (fun n => tau ^ n • c n) := by
  have hd : Summable (fun n => (tau ^ n • c n).1) := by
    apply Pi.summable.mpr
    intro u
    apply Pi.summable.mpr
    intro i
    apply Pi.summable.mpr
    intro j
    simpa [smul_eq_mul, mul_comm] using (hD u i j).summable
  have hg : Summable (fun n => (tau ^ n • c n).2) := by
    apply Pi.summable.mpr
    intro u
    apply Pi.summable.mpr
    intro i
    apply Pi.summable.mpr
    intro j
    simpa [smul_eq_mul, mul_comm] using (hG u i j).summable
  exact (hd.hasSum.prodMk hg.hasSum).summable

/-- The checked complex monodromy chain bounds the intrinsic Taylor radius
of the actual M3 maximal canonical branch, rather than only an existential
local analytic representative. -/
theorem maximal_branch_radius_le_of_chainL
    (chain₀ rest : List Slab)
    (h₀ : chainRest chain₀ = true)
    (hrest : chainFrom (lastPosL chain₀) (lastCellL chain₀) rest = true)
    (hpos : headPos chain₀ = (0, 0))
    (hA : lastPosL chain₀ = (0, G))
    (hB : lastPos (lastPosL chain₀) rest = (4, G))
    (hdisj : boxDisjoint 4 (lastCellL chain₀)
      (lastCell (lastCellL chain₀) rest) = true)
    (hseed : seedOK (headCell chain₀) = true)
    (M : MaximalBranch z rho sigma strengths (0, baseSeed z rho sigma)) :
    amplitudeRadius (branchCoefficients M.path) ≤ ENNReal.ofReal 84 := by
  have hdiv := maximal_branch_nonsummable_of_chainL
    chain₀ rest h₀ hrest hpos hA hB hdisj hseed M
  apply amplitudeRadius_le_of_nonconvergence (branchCoefficients M.path) 84 (by norm_num)
  intro r hr hsum
  obtain ⟨b, hD, hG⟩ := hsum
  have hrpos : 0 < r := by linarith
  have hrabs : (84 : ℝ) < |r| := by simpa only [abs_of_pos hrpos] using hr
  exact hdiv r hrabs
    (summable_vector_of_component_hasSum (branchCoefficients M.path) r b hD hG)

/-- A checked M3 monodromy chain together with a certified canonical real
state beyond 84 yields an actual MSA root whose original amplitude Taylor
series is not summable there. One original coefficient has both signs
arbitrarily late. The real-state membership remains a separate certificate. -/
theorem canonical_m3_state_beyond_chain_radius
    (chain₀ rest : List Slab)
    (h₀ : chainRest chain₀ = true)
    (hrest : chainFrom (lastPosL chain₀) (lastCellL chain₀) rest = true)
    (hpos : headPos chain₀ = (0, 0))
    (hA : lastPosL chain₀ = (0, G))
    (hB : lastPos (lastPosL chain₀) rest = (4, G))
    (hdisj : boxDisjoint 4 (lastCellL chain₀)
      (lastCell (lastCellL chain₀) rest) = true)
    (hseed : seedOK (headCell chain₀) = true)
    (M : MaximalBranch z rho sigma strengths (0, baseSeed z rho sigma))
    (b : ℝ) (h84 : 84 < b) (hbM : b ∈ initialCouplings M.bound) :
    IsRoot z rho sigma (b • strengths) (M.path b).1 (M.path b).2 ∧
      M.path b ∈ canonicalAmplitudes z rho sigma ∧
      ¬Summable (fun n => b ^ n • branchCoefficients M.path n) ∧
      ∃ u : Fin 2, ∃ i j : Fin 1,
        Oscillates (fun n => (branchCoefficients M.path n).1 u i j) ∨
        Oscillates (fun n => (branchCoefficients M.path n).2 u i j) := by
  have hradius := maximal_branch_radius_le_of_chainL
    chain₀ rest h₀ hrest hpos hA hB hdisj hseed M
  have hnonsum := maximal_branch_nonsummable_of_chainL
    chain₀ rest h₀ hrest hpos hA hB hdisj hseed M
  have hbpos : 0 < b := by linarith
  have hradlt : amplitudeRadius (branchCoefficients M.path) < ENNReal.ofReal b :=
    hradius.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hbpos).mpr h84)
  refine ⟨M.roots b hbM, M.canonical b hbM, ?_, ?_⟩
  · exact hnonsum b (by simpa only [abs_of_pos hbpos] using h84)
  · exact canonical_state_beyond_radius_has_oscillating_component
      z rho sigma strengths _ M b hbpos hbM hradlt

/-- The physical M3 data construct the HS maximal branch. Once a checked
monodromy chain and real-prefix membership certificate are supplied, this
is a direct actual-root counterexample to the universal root/series claim. -/
theorem exists_canonical_m3_state_with_nonsummable_series
    (chain₀ rest : List Slab)
    (h₀ : chainRest chain₀ = true)
    (hrest : chainFrom (lastPosL chain₀) (lastCellL chain₀) rest = true)
    (hpos : headPos chain₀ = (0, 0))
    (hA : lastPosL chain₀ = (0, G))
    (hB : lastPos (lastPosL chain₀) rest = (4, G))
    (hdisj : boxDisjoint 4 (lastCellL chain₀)
      (lastCell (lastCellL chain₀) rest) = true)
    (hseed : seedOK (headCell chain₀) = true)
    (b : ℝ) (h84 : 84 < b)
    (hb : b ∈ initialCouplings
      (maximalBound z rho sigma strengths (0, baseSeed z rho sigma))) :
    ∃ M : MaximalBranch z rho sigma strengths (0, baseSeed z rho sigma),
      M.bound = maximalBound z rho sigma strengths (0, baseSeed z rho sigma) ∧
      IsRoot z rho sigma (b • strengths) (M.path b).1 (M.path b).2 ∧
      M.path b ∈ canonicalAmplitudes z rho sigma ∧
      ¬Summable (fun n => b ^ n • branchCoefficients M.path n) ∧
      ∃ u : Fin 2, ∃ i j : Fin 1,
        Oscillates (fun n => (branchCoefficients M.path n).1 u i j) ∨
        Oscillates (fun n => (branchCoefficients M.path n).2 u i j) := by
  obtain ⟨hz, hsigma, hrho, hK⟩ := physical_data
  have hv : 0 < vacMix rho sigma := by rw [vacancy_eq]; norm_num
  obtain ⟨M, hM⟩ := exists_mixture_hs_maximal_branch
    z hz rho sigma hsigma hrho strengths hK hv
  refine ⟨M, hM, ?_⟩
  exact canonical_m3_state_beyond_chain_radius
    chain₀ rest h₀ hrest hpos hA hB hdisj hseed M b h84 (hM ▸ hb)

end FMSA.Convergence.M3CanonicalRadiusTransfer

/-- info: 'FMSA.Convergence.M3CanonicalRadiusTransfer.projected_coeff_eq_jet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3CanonicalRadiusTransfer.projected_coeff_eq_jet
/-- info: 'FMSA.Convergence.M3CanonicalRadiusTransfer.coeff_eq_branchCoefficients' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3CanonicalRadiusTransfer.coeff_eq_branchCoefficients
/-- info: 'FMSA.Convergence.M3CanonicalRadiusTransfer.maximal_branch_nonsummable_of_chainL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3CanonicalRadiusTransfer.maximal_branch_nonsummable_of_chainL
/-- info: 'FMSA.Convergence.M3CanonicalRadiusTransfer.summable_vector_of_component_hasSum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3CanonicalRadiusTransfer.summable_vector_of_component_hasSum
/-- info: 'FMSA.Convergence.M3CanonicalRadiusTransfer.maximal_branch_radius_le_of_chainL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3CanonicalRadiusTransfer.maximal_branch_radius_le_of_chainL
/-- info: 'FMSA.Convergence.M3CanonicalRadiusTransfer.canonical_m3_state_beyond_chain_radius' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3CanonicalRadiusTransfer.canonical_m3_state_beyond_chain_radius
/-- info: 'FMSA.Convergence.M3CanonicalRadiusTransfer.exists_canonical_m3_state_with_nonsummable_series' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3CanonicalRadiusTransfer.exists_canonical_m3_state_with_nonsummable_series
