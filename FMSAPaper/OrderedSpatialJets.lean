import FMSAPaper.ActualSpatialJets
import LeanCode.YukawaOZMix.MSAMultiTailMixtureRadial

/-! Spatial jets of the existing ordered radial definition, for every species
pair. This does not discharge the separate Fourier reciprocity premise. -/
noncomputable section
open Filter Topology Set Real
open scoped ContDiff BigOperators

namespace FMSA.Paper.OrderedSpatialJets

open ExactMSA.MultiTailMixture ExactMSA.BSource MSAMixture MSAMixtureCoreUneq
open SpatialDictionary PhysicalExteriorJets ActualSpatialJets
variable {N : ℕ} {T : Type*} [Fintype T]

omit [Fintype T] in
theorem contact_swap (sigma : Fin N → ℝ) (i j : Fin N) :
    edgeHi sigma j i = edgeHi sigma i j := by unfold edgeHi; ring

omit [Fintype T] in
theorem breakpoint_swap (sigma : Fin N → ℝ) (i j : Fin N) :
    lamA sigma j i = lamA sigma i j := by
  have h : edgeLo sigma j i = -edgeLo sigma i j := by unfold edgeLo; ring
  simp only [lamA, h, abs_neg]

theorem ordered_core_jet_hasForm (z : T → ℝ) (hz : ∀ u, 0 < z u) (u0 : T)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 < sigma i) (K : TailMatrix T N)
    (i j : Fin N) (p : ℝ → TailMatrix T N × TailMatrix T N)
    (n : ℕ) (hp : ContDiffAt ℝ n p 0) :
    HasForm z (Ioo (0 : ℝ) (lamA sigma i j))
      (fun r => r * jet (fun t => orderedRadialCorrelation z rho sigma K (p t).1 (p t).2 i j r) n) ∧
    HasForm z (Ioo (lamA sigma i j) (edgeHi sigma i j))
      (fun r => r * jet (fun t => orderedRadialCorrelation z rho sigma K (p t).1 (p t).2 i j r) n) := by
  by_cases h : sigma j <= sigma i
  · simpa only [orderedRadialCorrelation, if_pos h, rootCorrelation] using
      And.intro
        (core_jet_inner_hasForm z hz u0 rho sigma (fun i => (hsigma i).le) i j (hsigma j) h p n hp)
        (core_jet_outer_hasForm z hz u0 rho sigma (fun i => (hsigma i).le) i j (hsigma j) h p n hp)
  · have hji : sigma i <= sigma j := le_of_lt (lt_of_not_ge h)
    simpa only [orderedRadialCorrelation, if_neg h, rootCorrelation,
      breakpoint_swap sigma i j, contact_swap sigma i j] using
      And.intro
        (core_jet_inner_hasForm z hz u0 rho sigma (fun i => (hsigma i).le) j i (hsigma i) hji p n hp)
        (core_jet_outer_hasForm z hz u0 rho sigma (fun i => (hsigma i).le) j i (hsigma i) hji p n hp)

theorem weighted_exterior_jet_hasForm (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 <= sigma i) (K : TailMatrix T N)
    (p : ℝ → TailMatrix T N × TailMatrix T N)
    (hroot : ∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (i j : Fin N) (n : ℕ) :
    HasForm z (Ioi (edgeHi sigma i j))
      (fun r => r * jet (fun t => rootCorrelation z rho sigma (p t) i j r) n) := by
  by_cases hn : n = 1
  · have h := finite_sum_hasForm z (Ioi (edgeHi sigma i j)) _ (fun u =>
      (dictionary_hasForm z _ (.inr (.inl u))).const_mul
        (K u i j * exp (z u * edgeHi sigma i j)))
    apply h.congr
    intro r hr
    dsimp only
    have hr0 : r ≠ 0 := by
      have hR : 0 <= edgeHi sigma i j := by unfold edgeHi; linarith [hsigma i, hsigma j]
      exact (lt_of_le_of_lt hR hr).ne'
    rw [exterior_jet z rho sigma K hz hsigma p hroot i j r hr n, if_pos hn, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    simp only [dictionary]
    rw [mul_div_left_comm, div_self hr0, mul_one]
    rw [mul_assoc, ← exp_add]
    congr 2
    ring
  · apply ((dictionary_hasForm z (Ioi (edgeHi sigma i j)) (.inl 0)).const_mul 0).congr
    intro r hr
    dsimp only
    rw [exterior_jet z rho sigma K hz hsigma p hroot i j r hr n, if_neg hn]
    simp

theorem ordered_exterior_jet_hasForm (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 <= sigma i) (K : TailMatrix T N)
    (p : ℝ → TailMatrix T N × TailMatrix T N)
    (hroot : ∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (i j : Fin N) (n : ℕ) :
    HasForm z (Ioi (edgeHi sigma i j))
      (fun r => r * jet (fun t => orderedRadialCorrelation z rho sigma K (p t).1 (p t).2 i j r) n) := by
  by_cases h : sigma j <= sigma i
  · simpa only [orderedRadialCorrelation, if_pos h, rootCorrelation] using
      weighted_exterior_jet_hasForm z hz rho sigma hsigma K p hroot i j n
  · simpa only [orderedRadialCorrelation, if_neg h, rootCorrelation, contact_swap sigma i j] using
      weighted_exterior_jet_hasForm z hz rho sigma hsigma K p hroot j i n

theorem ordered_jet_contDiffAt_off_knots (z : T → ℝ) (hz : ∀ u, 0 < z u) (u0 : T)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 < sigma i) (K : TailMatrix T N)
    (p : ℝ → TailMatrix T N × TailMatrix T N)
    (hroot : ∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (i j : Fin N) (n : ℕ) (hp : ContDiffAt ℝ n p 0)
    (r : ℝ) (hr : 0 < r) (hlam : r ≠ lamA sigma i j) (hR : r ≠ edgeHi sigma i j) :
    ContDiffAt ℝ ∞
      (fun r => jet (fun t => orderedRadialCorrelation z rho sigma K (p t).1 (p t).2 i j r) n) r := by
  obtain ⟨hi, ho⟩ := ordered_core_jet_hasForm z hz u0 rho sigma hsigma K i j p n hp
  by_cases hiR : r < lamA sigma i j
  · exact (coefficient_contDiffOn_of_weighted z _ _ (fun x hx => hx.1.ne') hi).contDiffAt
      (isOpen_Ioo.mem_nhds ⟨hr, hiR⟩)
  · have hli : lamA sigma i j < r := lt_of_le_of_ne (le_of_not_gt hiR) hlam.symm
    by_cases hoR : r < edgeHi sigma i j
    · exact (coefficient_contDiffOn_of_weighted z _ _
        (fun x hx => (lt_of_le_of_lt (abs_nonneg _) hx.1).ne') ho).contDiffAt
        (isOpen_Ioo.mem_nhds ⟨hli, hoR⟩)
    · have hri : edgeHi sigma i j < r := lt_of_le_of_ne (le_of_not_gt hoR) hR.symm
      have he := ordered_exterior_jet_hasForm z hz rho sigma (fun i => (hsigma i).le) K p hroot i j n
      have hpos : 0 < edgeHi sigma i j := by unfold edgeHi; linarith [hsigma i, hsigma j]
      exact (coefficient_contDiffOn_of_weighted z _ _
        (fun x hx => (lt_trans hpos hx).ne') he).contDiffAt (isOpen_Ioi.mem_nhds hri)

end FMSA.Paper.OrderedSpatialJets

/-- info: 'FMSA.Paper.OrderedSpatialJets.contact_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.OrderedSpatialJets.contact_swap

/-- info: 'FMSA.Paper.OrderedSpatialJets.breakpoint_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.OrderedSpatialJets.breakpoint_swap

/-- info: 'FMSA.Paper.OrderedSpatialJets.ordered_core_jet_hasForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.OrderedSpatialJets.ordered_core_jet_hasForm

/-- info: 'FMSA.Paper.OrderedSpatialJets.weighted_exterior_jet_hasForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.OrderedSpatialJets.weighted_exterior_jet_hasForm

/-- info: 'FMSA.Paper.OrderedSpatialJets.ordered_exterior_jet_hasForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.OrderedSpatialJets.ordered_exterior_jet_hasForm

/-- info: 'FMSA.Paper.OrderedSpatialJets.ordered_jet_contDiffAt_off_knots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.OrderedSpatialJets.ordered_jet_contDiffAt_off_knots
