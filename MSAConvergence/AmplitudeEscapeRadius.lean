import MSAConvergence.CanonicalEndpointContinuation

/-! A genuine amplitude escape bounds the actual Taylor radius. This is an
UPPER bound and makes no all-stable-interval convergence assertion. -/
noncomputable section
open Filter Topology Set
open scoped BigOperators ContDiff
namespace FMSA.Convergence.AmplitudeEscapeRadius
open FMSA.Paper FMSA.MatrixQ0 FMSA.ExactMSA.MultiTailMixture
open FMSA.Paper.FoldRadius FMSA.Paper.TaylorRoot FMSA.Paper.StableIntervalRadius
open FMSA.Convergence.CanonicalNeighborhood FMSA.Convergence.ActualCanonicalBranch
variable {N : ℕ} {T : Type*} [Fintype T]

/-- Taylor sums of a genuine root germ through the same seed cannot exist
beyond a finite endpoint where the actual canonical branch is unbounded.
No finite continuous endpoint, fold or supplied Jacobian inverse is assumed. -/
theorem nonconvergence_beyond_amplitude_escape
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (hv : vacMix rho sigma ≠ 0)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ) (hb : 0 < b)
    (hp : ContinuousOn p (Ico 0 b))
    (hroot : ∀ t ∈ Ico 0 b, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hcanon : ∀ t ∈ Ico 0 b, p t ∈ canonicalAmplitudes z rho sigma)
    (hunbounded : ¬∃ B : ℝ, ∀ t ∈ Ico 0 b, ‖p t‖ ≤ B)
    (g : ℝ → TailMatrix T N × TailMatrix T N)
    (hg : ContDiffAt ℝ ∞ g 0) (hg0 : g 0 = p 0)
    (hglocal : ∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K) (g t).1 (g t).2)
    (r : ℝ) (hbr : b < r) :
    ¬∃ a : TailMatrix T N × TailMatrix T N,
      (∀ u i j, HasSum (fun n => (branchCoefficients g n).1 u i j*r^n) (a.1 u i j)) ∧
      (∀ u i j, HasSum (fun n => (branchCoefficients g n).2 u i j*r^n) (a.2 u i j)) := by
  rintro ⟨a,hD,hG⟩
  obtain ⟨q,hq0,hqa,hqr⟩ := analytic_root_of_convergence_at z rho sigma K g hg hglocal
    r (hb.trans hbr) a hD hG
  have hsub : Ico (0 : ℝ) b ⊆ Ioo (-r) r := by
    intro t ht
    exact ⟨by linarith [ht.1],ht.2.trans hbr⟩
  have hclosed : Icc (0 : ℝ) b ⊆ Ioo (-r) r := by
    intro t ht
    exact ⟨by linarith [ht.1],ht.2.trans_lt hbr⟩
  have hmatch := actual_canonical_roots_eqOn_of_preconnected z hz rho sigma hsigma hrho K hK hv
    p q (Ico 0 b) 0 (convex_Ico 0 b).isPreconnected ⟨le_rfl,hb⟩ hp
    (hqa.continuousOn.mono hsub) (hq0.trans hg0).symm hroot
    (fun t ht => hqr t (hsub ht)) hcanon
  obtain ⟨B,hB⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) b)).exists_bound_of_continuousOn
    (hqa.continuousOn.mono hclosed)
  apply hunbounded
  refine ⟨B,?_⟩
  intro t ht
  rw [hmatch ht]
  exact hB t ⟨ht.1,ht.2.le⟩

/-- Genuine common component radius is at most a finite amplitude-escape
endpoint. No conclusion about convergence AT that endpoint is asserted. -/
theorem amplitude_radius_le_escape_endpoint
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (hv : vacMix rho sigma ≠ 0)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ) (hb : 0 < b)
    (hp : ContinuousOn p (Ico 0 b))
    (hroot : ∀ t ∈ Ico 0 b, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hcanon : ∀ t ∈ Ico 0 b, p t ∈ canonicalAmplitudes z rho sigma)
    (hunbounded : ¬∃ B : ℝ, ∀ t ∈ Ico 0 b, ‖p t‖ ≤ B)
    (g : ℝ → TailMatrix T N × TailMatrix T N)
    (hg : ContDiffAt ℝ ∞ g 0) (hg0 : g 0 = p 0)
    (hglocal : ∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K) (g t).1 (g t).2) :
    amplitudeRadius (branchCoefficients g) ≤ ENNReal.ofReal b :=
  amplitudeRadius_le_of_nonconvergence (branchCoefficients g) b hb.le
    (nonconvergence_beyond_amplitude_escape z hz rho sigma hsigma hrho K hK hv p b hb hp hroot hcanon hunbounded g hg hg0 hglocal)

/-- For an actual branch specified only on its nonnegative interval, construct
the TRUE analytic germ and prove its radius upper bound at amplitude escape.
No derivatives of arbitrary negative-time values of the original branch are used. -/
theorem exists_intrinsic_germ_radius_le_escape
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (hv : vacMix rho sigma ≠ 0)
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ) (hb : 0 < b)
    (hp : ContinuousOn p (Ico 0 b))
    (hroot : ∀ t ∈ Ico 0 b, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hcanon : ∀ t ∈ Ico 0 b, p t ∈ canonicalAmplitudes z rho sigma)
    (hunbounded : ¬∃ B : ℝ, ∀ t ∈ Ico 0 b, ‖p t‖ ≤ B) :
    ∃ g : ℝ → TailMatrix T N × TailMatrix T N,
      Set.EqOn g p (Ico 0 b) ∧ AnalyticOnNhd ℝ g (Ico 0 b) ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K) (g t).1 (g t).2) ∧
      0 < amplitudeRadius (branchCoefficients g) ∧ amplitudeRadius (branchCoefficients g) ≤ ENNReal.ofReal b := by
  have hset : initialCouplings (ENNReal.ofReal b) = Ico (0 : ℝ) b := by
    ext t
    simp only [initialCouplings,mem_setOf_eq,mem_Ico]
    exact and_congr_right (fun _ => ENNReal.ofReal_lt_ofReal_iff hb)
  have hbound : 0 < ENNReal.ofReal b := ENNReal.ofReal_pos.mpr hb
  obtain ⟨g,heq,hga,hgr,_hgc,hR,_hiff⟩ := exists_canonical_series_extension z hz rho sigma hsigma hrho K hK hv
    p (ENNReal.ofReal b) hbound (by simpa only [hset] using hp)
    (by simpa only [hset] using hroot) (by simpa only [hset] using hcanon)
  rw [hset] at heq hga
  have h0 : (0 : ℝ) ∈ Ico 0 b := ⟨le_rfl,hb⟩
  exact ⟨g,heq,hga,hgr,hR,amplitude_radius_le_escape_endpoint z hz rho sigma hsigma hrho K hK hv p b hb hp hroot hcanon hunbounded
    g (hga 0 h0).contDiffAt (heq h0) hgr⟩

end FMSA.Convergence.AmplitudeEscapeRadius

/-- info: 'FMSA.Convergence.AmplitudeEscapeRadius.nonconvergence_beyond_amplitude_escape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.AmplitudeEscapeRadius.nonconvergence_beyond_amplitude_escape

/-- info: 'FMSA.Convergence.AmplitudeEscapeRadius.amplitude_radius_le_escape_endpoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.AmplitudeEscapeRadius.amplitude_radius_le_escape_endpoint

/-- info: 'FMSA.Convergence.AmplitudeEscapeRadius.exists_intrinsic_germ_radius_le_escape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.AmplitudeEscapeRadius.exists_intrinsic_germ_radius_le_escape
