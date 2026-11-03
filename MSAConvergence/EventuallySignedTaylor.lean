import FMSAPaper.ActualAnalyticTaylor

/-! Pringsheim and the actual fold radius when every component's Taylor
coefficients have one sign only from some order on. Finitely many early
coefficients of either sign are allowed; the sign premise stays a hypothesis. -/
noncomputable section
open Filter Topology
open scoped BigOperators NNReal ENNReal ContDiff
namespace FMSA.Convergence.EventuallySignedTaylor
open FMSA.Paper FMSA.ExactMSA.MultiTailMixture FMSA.Paper.TaylorRoot FMSA.Paper.FoldRadius
open FMSA.Paper.AnalyticTaylor FMSA.Paper.ActualAnalyticTaylor FMSA.ExactMSA.BSource
open FormalMultilinearSeries
variable {N : ℕ} {T : Type*} [Fintype T]

/-- Coefficients from order `m + 1` on, scaled by `s`; earlier ones removed. -/
def tailCoefficients (a : ℕ → ℝ) (s : ℝ) (m n : ℕ) : ℝ :=
  if n < m + 1 then 0 else s * a n

/-- The removed polynomial head, with the sign that cancels it. -/
def headCoefficients (a : ℕ → ℝ) (s : ℝ) (m n : ℕ) : ℝ :=
  if n < m + 1 then -(s * a n) else 0

theorem head_radius (a : ℕ → ℝ) (s : ℝ) (m : ℕ) :
    (ofScalars ℝ (headCoefficients a s m)).radius = ⊤ := by
  apply radius_eq_top_of_forall_image_add_eq_zero _ (m + 1)
  intro k
  simp only [ofScalars, headCoefficients]
  rw [if_neg (by omega), zero_smul]

theorem tail_series_eq (a : ℕ → ℝ) (s : ℝ) (m : ℕ) :
    ofScalars ℝ (tailCoefficients a s m) =
      s • ofScalars ℝ a + ofScalars ℝ (headCoefficients a s m) := by
  ext n
  by_cases hn : n < m + 1
  · simp [ofScalars, tailCoefficients, headCoefficients, hn, smul_eq_mul]
  · simp [ofScalars, tailCoefficients, headCoefficients, hn, smul_eq_mul]

theorem tail_radius (a : ℕ → ℝ) (s : ℝ) (hs : s ≠ 0) (m : ℕ) :
    (ofScalars ℝ (tailCoefficients a s m)).radius = (ofScalars ℝ a).radius := by
  rw [tail_series_eq, SignedPringsheim.radius_add_entire _ _ (head_radius a s m),
    radius_smul_eq _ hs]

theorem tail_sum (a : ℕ → ℝ) (s : ℝ) (m : ℕ) (x : ℝ)
    (hx : (‖x‖₊ : ENNReal) < (ofScalars ℝ a).radius) :
    (ofScalars ℝ (tailCoefficients a s m)).sum x =
      s * (ofScalars ℝ a).sum x + (ofScalars ℝ (headCoefficients a s m)).sum x := by
  let p := ofScalars ℝ a
  let q := ofScalars ℝ (headCoefficients a s m)
  have hq : HasFPowerSeriesOnBall q.sum q 0 p.radius :=
    (q.hasFPowerSeriesOnBall (by rw [head_radius]; exact ENNReal.zero_lt_top)).mono hx.pos
      (by rw [head_radius]; exact le_top)
  have h := ((p.hasFPowerSeriesOnBall hx.pos).const_smul (c := s)).add hq
  rw [tail_series_eq]
  have he := h.sum (mem_eball_zero_iff.mpr hx)
  simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, zero_add, p, q] using he.symm

/-- Pringsheim with one sign only from order `m` on. -/
theorem not_analyticAt_endpoint (a : ℕ → ℝ) (s : ℝ) (hs : s ≠ 0) (m : ℕ)
    (ha : ∀ n, m ≤ n → 0 <= s * a n)
    (R : ℝ) (hR : 0 < R) (hradius : (ofScalars ℝ a).radius = ENNReal.ofReal R)
    (f : ℝ → ℝ) (he : ∀ t ∈ Set.Ioo (0 : ℝ) R, f t = (ofScalars ℝ a).sum t) :
    ¬ AnalyticAt ℝ f R := by
  intro hf
  have hb : ∀ n, 0 <= tailCoefficients a s m n := by
    intro n
    by_cases hn : n < m + 1
    · simp [tailCoefficients, hn]
    · simpa only [tailCoefficients, if_neg hn] using ha n (by omega)
  have hq : AnalyticAt ℝ (ofScalars ℝ (headCoefficients a s m)).sum R :=
    (ofScalars ℝ (headCoefficients a s m)).analyticOnNhd R
      (by rw [head_radius]; exact mem_eball_zero_iff.mpr ENNReal.coe_lt_top)
  apply Pringsheim.not_analyticAt_endpoint (tailCoefficients a s m) hb R hR
    (by rw [tail_radius a s hs m, hradius])
    (fun t => s * f t + (ofScalars ℝ (headCoefficients a s m)).sum t) _
    ((analyticAt_const.mul hf).add hq)
  intro t ht
  rw [he t ht, tail_sum]
  rw [hradius, ENNReal.coe_nnreal_eq ‖t‖₊, coe_nnnorm, Real.norm_of_nonneg ht.1.le]
  exact (ENNReal.ofReal_lt_ofReal_iff hR).mpr ht.2

/-- Continuation along a positive interval bounds the radius below under
one sign from order `m` on. -/
theorem le_radius_of_analytic_continuation (a : ℕ → ℝ) (s : ℝ) (hs : s ≠ 0) (m : ℕ)
    (ha : ∀ n, m ≤ n → 0 <= s * a n)
    (hpos : 0 < (ofScalars ℝ a).radius)
    (b : ℝ) (hb : 0 < b) (f : ℝ → ℝ) (hf : AnalyticOnNhd ℝ f (Set.Ioo (0 : ℝ) b))
    (he : ∀ t ∈ Set.Ioo (0 : ℝ) b, ENNReal.ofReal t < (ofScalars ℝ a).radius →
      f t = (ofScalars ℝ a).sum t) :
    ENNReal.ofReal b <= (ofScalars ℝ a).radius := by
  by_contra h
  have hlt : (ofScalars ℝ a).radius < ENNReal.ofReal b := lt_of_not_ge h
  have hfinite : (ofScalars ℝ a).radius ≠ ⊤ := ne_top_of_lt hlt
  let R := (ofScalars ℝ a).radius.toReal
  have hR : 0 < R := ENNReal.toReal_pos hpos.ne' hfinite
  have hradius : (ofScalars ℝ a).radius = ENNReal.ofReal R := (ENNReal.ofReal_toReal hfinite).symm
  have hRb : R < b := (ENNReal.ofReal_lt_ofReal_iff hb).mp (by rwa [← hradius])
  apply not_analyticAt_endpoint a s hs m ha R hR hradius f _ (hf R ⟨hR, hRb⟩)
  intro t ht
  apply he t ⟨ht.1, ht.2.trans hRb⟩
  rw [hradius]
  exact (ENNReal.ofReal_lt_ofReal_iff hR).mpr ht.2

theorem le_jet_radius_of_eventually_signed_analytic_branch (f : ℝ → ℝ) (b : ℝ) (hb : 0 < b)
    (hf : AnalyticOnNhd ℝ f (Set.Ico 0 b))
    (s : ℝ) (hs : s ≠ 0) (m : ℕ) (ha : ∀ n, m ≤ n → 0 <= s * jet f n) :
    ENNReal.ofReal b <= (ofScalars ℝ (jet f)).radius := by
  apply le_radius_of_analytic_continuation (jet f) s hs m ha
    (jet_radius_pos f (hf 0 ⟨le_rfl, hb⟩)) b hb f
    (hf.mono (fun _ hx => ⟨hx.1.le, hx.2⟩))
  intro t ht hr
  exact eq_jet_sum_on_interval f b hf t ⟨ht.1.le, ht.2⟩ hr

theorem le_amplitudeRadius_of_eventually_signed_analytic_branch
    (p : ℝ → TailMatrix T N × TailMatrix T N) (b : ℝ) (hb : 0 < b)
    (hp : AnalyticOnNhd ℝ p (Set.Ico 0 b))
    (hD : ∀ u i j, ∃ s : ℝ, s ≠ 0 ∧ ∃ m : ℕ,
      ∀ n, m ≤ n → 0 <= s * (branchCoefficients p n).1 u i j)
    (hG : ∀ u i j, ∃ s : ℝ, s ≠ 0 ∧ ∃ m : ℕ,
      ∀ n, m ≤ n → 0 <= s * (branchCoefficients p n).2 u i j) :
    ENNReal.ofReal b <= amplitudeRadius (branchCoefficients p) := by
  apply le_iInf
  intro u
  apply le_iInf
  intro i
  apply le_iInf
  intro j
  apply le_min
  · obtain ⟨s, hs, m, ha⟩ := hD u i j
    exact le_jet_radius_of_eventually_signed_analytic_branch _ b hb
      (fun t ht => (analyticAt_components p t (hp t ht)).1 u i j) s hs m ha
  · obtain ⟨s, hs, m, ha⟩ := hG u i j
    exact le_jet_radius_of_eventually_signed_analytic_branch _ b hb
      (fun t ht => (analyticAt_components p t (hp t ht)).2 u i j) s hs m ha

/-- Fold equality for the actual polynomial MSA residual when each component
has one sign only from some order on. This weakens the all-order premise of
`actual_radius_eq_fold`, which all-attractive binary mixtures can violate at
order two. No conclusion exactly at the fold is asserted. -/
theorem actual_radius_eq_fold_of_eventually_signed
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (p : ℝ → TailMatrix T N × TailMatrix T N)
    (hp : ContinuousAt p 0)
    (hlocal : ∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (f : ℝ) (hf : 0 < f) (hpcont : ContinuousOn p (Set.Icc 0 f))
    (hproot : ∀ t ∈ Set.Ico 0 f, IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (hinv : ∀ t ∈ Set.Ico 0 f,
      ((fderiv ℝ (residual z rho sigma K) (t, p t)).comp
        (ContinuousLinearMap.inr ℝ ℝ (TailMatrix T N × TailMatrix T N))).IsInvertible)
    (htransverse : (fderiv ℝ (residual z rho sigma K) (f, p f)) (1, 0) ∉
      Set.range (fun w => (fderiv ℝ (residual z rho sigma K) (f, p f)) (0, w)))
    (hD : ∀ u i j, ∃ s : ℝ, s ≠ 0 ∧ ∃ m : ℕ,
      ∀ n, m ≤ n → 0 <= s * (branchCoefficients p n).1 u i j)
    (hG : ∀ u i j, ∃ s : ℝ, s ≠ 0 ∧ ∃ m : ℕ,
      ∀ n, m ≤ n → 0 <= s * (branchCoefficients p n).2 u i j) :
    amplitudeRadius (branchCoefficients p) = ENNReal.ofReal f := by
  have ha := ActualAnalyticBranch.actual_regular_branch_analyticOnNhd z rho sigma K p f hp hpcont
    hlocal hproot hinv
  apply le_antisymm
  · exact actual_radius_le_fold z rho sigma K p (ha 0 ⟨le_rfl, hf⟩).contDiffAt
      hlocal f hf hpcont hproot hinv htransverse
  · exact le_amplitudeRadius_of_eventually_signed_analytic_branch p f hf ha hD hG

/-- The all-order premise is the special case `m = 1`. -/
theorem eventually_signed_of_signed (a : ℕ → ℝ) (s : ℝ)
    (ha : ∀ n, 0 < n → 0 <= s * a n) : ∀ n, 1 ≤ n → 0 <= s * a n :=
  fun n hn => ha n hn

/-- info: 'FMSA.Convergence.EventuallySignedTaylor.head_radius' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.EventuallySignedTaylor.head_radius
/-- info: 'FMSA.Convergence.EventuallySignedTaylor.tail_series_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.EventuallySignedTaylor.tail_series_eq
/-- info: 'FMSA.Convergence.EventuallySignedTaylor.tail_radius' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.EventuallySignedTaylor.tail_radius
/-- info: 'FMSA.Convergence.EventuallySignedTaylor.tail_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.EventuallySignedTaylor.tail_sum
/-- info: 'FMSA.Convergence.EventuallySignedTaylor.not_analyticAt_endpoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.EventuallySignedTaylor.not_analyticAt_endpoint
/-- info: 'FMSA.Convergence.EventuallySignedTaylor.le_radius_of_analytic_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.EventuallySignedTaylor.le_radius_of_analytic_continuation
/-- info: 'FMSA.Convergence.EventuallySignedTaylor.le_jet_radius_of_eventually_signed_analytic_branch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.EventuallySignedTaylor.le_jet_radius_of_eventually_signed_analytic_branch
/-- info: 'FMSA.Convergence.EventuallySignedTaylor.le_amplitudeRadius_of_eventually_signed_analytic_branch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.EventuallySignedTaylor.le_amplitudeRadius_of_eventually_signed_analytic_branch
/-- info: 'FMSA.Convergence.EventuallySignedTaylor.actual_radius_eq_fold_of_eventually_signed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.EventuallySignedTaylor.actual_radius_eq_fold_of_eventually_signed
/-- info: 'FMSA.Convergence.EventuallySignedTaylor.eventually_signed_of_signed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.EventuallySignedTaylor.eventually_signed_of_signed
end FMSA.Convergence.EventuallySignedTaylor
