import FMSAPaper.AbsolutelyMonotone
import FMSAPaper.ActualAnalyticBranch

/-! The inverse branch of the quartic `q u = -L u² (u - a) (u - b)` through its
simple root `u = a`, for `a < b < 0` and `L > 0`. The critical points of `q` are
real and ordered `a < c₁ < b < c₂ < 0`; `q` increases on `u ≤ c₁`, so the branch
is real and regular for couplings below the fold `q c₁`. The reciprocal slope
`1 / q'` is absolutely monotone there, hence every derivative of the branch of
order at least one is nonnegative. The branch has no analytic continuation
through the fold. -/
noncomputable section
open Set Filter Topology Real
open scoped ContDiff

namespace FMSA.Paper.QuarticBranch
open AbsolutelyMonotone

variable (a b L : ℝ)

def q (u : ℝ) : ℝ := -L * u ^ 2 * (u - a) * (u - b)
def disc : ℝ := 9 * (a + b) ^ 2 - 32 * a * b
/-- The critical point between the two nonzero roots: the fold. -/
def c1 : ℝ := (3 * (a + b) - √(disc a b)) / 8
def c2 : ℝ := (3 * (a + b) + √(disc a b)) / 8
/-- `q' u = 4 L (-u) (c₁ - u) (c₂ - u)`. -/
def qd (u : ℝ) : ℝ := 4 * L * ((0 - u) * (c1 a b - u) * (c2 a b - u))
/-- The fold coupling. -/
def foldTau : ℝ := q a b L (c1 a b)
/-- Lower end of the parameter interval used for the branch. -/
def lowU : ℝ := a - 1
def lowTau : ℝ := q a b L (lowU a)
/-- The inverse branch of `q` on `[a - 1, c₁]`. -/
def branch (t : ℝ) : ℝ := Function.invFunOn (q a b L) (Icc (lowU a) (c1 a b)) t

variable {a b L}
variable (hab : a < b) (hb : b < 0) (hL : 0 < L)
include hab hb

theorem disc_pos : 0 < disc a b := by
  have : 0 < a * b := mul_pos_of_neg_of_neg (hab.trans hb) hb
  unfold disc; nlinarith [sq_nonneg (a - b)]

theorem quad_factor (u : ℝ) :
    4 * u ^ 2 - 3 * (a + b) * u + 2 * a * b = 4 * (u - c1 a b) * (u - c2 a b) := by
  have hS := Real.sq_sqrt (disc_pos hab hb).le
  unfold c1 c2 disc at *
  linear_combination (1 / 16 : ℝ) * hS

theorem c1_le_c2 : c1 a b ≤ c2 a b := by
  unfold c1 c2
  have := Real.sqrt_nonneg (disc a b)
  linarith

theorem crit_order : a < c1 a b ∧ c1 a b < b ∧ b < c2 a b ∧ c2 a b < 0 := by
  have hf := quad_factor hab hb
  have hle := c1_le_c2 hab hb
  have hrb : 4 * (b - c1 a b) * (b - c2 a b) < 0 := by
    rw [← hf]; nlinarith [mul_pos_of_neg_of_neg (hab.trans hb) hb]
  have hra : 0 < 4 * (a - c1 a b) * (a - c2 a b) := by
    rw [← hf]
    have : 0 < a * (a - b) := mul_pos_of_neg_of_neg (hab.trans hb) (by linarith)
    nlinarith
  have hr0 : 0 < 4 * (0 - c1 a b) * (0 - c2 a b) := by
    rw [← hf]; nlinarith [mul_pos_of_neg_of_neg (hab.trans hb) hb]
  have h1 : c1 a b < b ∧ b < c2 a b := by
    by_contra hcon
    rw [not_and_or] at hcon
    rcases hcon with h | h <;> push Not at h <;> nlinarith
  have h2 : a < c1 a b := by
    by_contra hcon; push Not at hcon
    nlinarith
  have h3 : c2 a b < 0 := by
    by_contra hcon; push Not at hcon
    nlinarith
  exact ⟨h2, h1.1, h1.2, h3⟩

theorem hasDerivAt_q (u : ℝ) : HasDerivAt (q a b L) (qd a b L u) u := by
  have hf := quad_factor hab hb u
  have h : HasDerivAt (q a b L) (-L * (4 * u ^ 3 - 3 * (a + b) * u ^ 2 + 2 * a * b * u)) u := by
    have e : q a b L = fun u => -L * (u ^ 4 - (a + b) * u ^ 3 + a * b * u ^ 2) := by
      funext u; unfold q; ring
    rw [e]
    have := (((hasDerivAt_pow 4 u).sub ((hasDerivAt_pow 3 u).const_mul (a + b))).add
      ((hasDerivAt_pow 2 u).const_mul (a * b))).const_mul (-L)
    exact this.congr_deriv (by
      simp only [Nat.cast_ofNat, show (4 : ℕ) - 1 = 3 from rfl, show (3 : ℕ) - 1 = 2 from rfl,
        show (2 : ℕ) - 1 = 1 from rfl, pow_one]
      ring)
  exact h.congr_deriv (by unfold qd; linear_combination (-L * u) * hf)

include hL

theorem qd_pos {u : ℝ} (hu : u < c1 a b) : 0 < qd a b L u := by
  obtain ⟨h1, h2, h3, h4⟩ := crit_order hab hb
  unfold qd
  have : 0 < 0 - u := by linarith
  have : 0 < c1 a b - u := by linarith
  have : 0 < c2 a b - u := by linarith
  positivity

omit hL in
theorem qd_c1 : qd a b L (c1 a b) = 0 := by simp [qd]

theorem q_strictMonoOn : StrictMonoOn (q a b L) (Iic (c1 a b)) := by
  apply strictMonoOn_of_deriv_pos (convex_Iic _)
  · exact fun u _ => (hasDerivAt_q hab hb u).continuousAt.continuousWithinAt
  · intro u hu
    rw [interior_Iic] at hu
    rw [(hasDerivAt_q hab hb u).deriv]
    exact qd_pos hab hb hL hu

omit hab hb hL in
theorem q_a : q a b L a = 0 := by simp [q]

theorem lowU_lt_a : lowU a < a := by unfold lowU; linarith

theorem foldTau_pos : 0 < foldTau a b L := by
  obtain ⟨h1, h2, _, _⟩ := crit_order hab hb
  have := q_strictMonoOn hab hb hL (show a ∈ Iic (c1 a b) from h1.le)
    (Set.mem_Iic.2 le_rfl) h1
  simpa [foldTau, q_a] using this

theorem lowTau_neg : lowTau a b L < 0 := by
  obtain ⟨h1, _, _, _⟩ := crit_order hab hb
  have hm := lowU_lt_a hab hb hL
  have := q_strictMonoOn hab hb hL (show lowU a ∈ Iic (c1 a b) from (hm.trans h1).le)
    (show a ∈ Iic (c1 a b) from h1.le) hm
  simpa [lowTau, q_a] using this

theorem lowU_le_c1 : lowU a ≤ c1 a b :=
  ((lowU_lt_a hab hb hL).trans (crit_order hab hb).1).le

theorem q_surj {t : ℝ} (ht : t ∈ Icc (lowTau a b L) (foldTau a b L)) :
    ∃ u ∈ Icc (lowU a) (c1 a b), q a b L u = t := by
  have hcont : ContinuousOn (q a b L) (Icc (lowU a) (c1 a b)) :=
    fun u _ => (hasDerivAt_q hab hb u).continuousAt.continuousWithinAt
  exact intermediate_value_Icc (lowU_le_c1 hab hb hL) hcont ht

theorem q_injOn : InjOn (q a b L) (Icc (lowU a) (c1 a b)) :=
  (q_strictMonoOn hab hb hL).injOn.mono (fun _ hu => hu.2)

theorem branch_mem {t : ℝ} (ht : t ∈ Icc (lowTau a b L) (foldTau a b L)) :
    branch a b L t ∈ Icc (lowU a) (c1 a b) := by
  obtain ⟨u, hu, hq⟩ := q_surj hab hb hL ht
  exact Function.invFunOn_mem ⟨u, hu, hq⟩

theorem q_branch {t : ℝ} (ht : t ∈ Icc (lowTau a b L) (foldTau a b L)) :
    q a b L (branch a b L t) = t := by
  obtain ⟨u, hu, hq⟩ := q_surj hab hb hL ht
  exact Function.invFunOn_eq ⟨u, hu, hq⟩

theorem branch_q {u : ℝ} (hu : u ∈ Icc (lowU a) (c1 a b)) : branch a b L (q a b L u) = u :=
  (q_injOn hab hb hL).leftInvOn_invFunOn hu

theorem tau_mem_of_u_mem {u : ℝ} (hu : u ∈ Icc (lowU a) (c1 a b)) :
    q a b L u ∈ Icc (lowTau a b L) (foldTau a b L) := by
  have hmono := q_strictMonoOn hab hb hL
  exact ⟨hmono.monotoneOn (show lowU a ∈ Iic (c1 a b) from lowU_le_c1 hab hb hL) hu.2 hu.1,
    hmono.monotoneOn hu.2 (Set.mem_Iic.2 le_rfl) hu.2⟩

theorem branch_zero : branch a b L 0 = a := by
  obtain ⟨h1, _, _, _⟩ := crit_order hab hb
  have := branch_q hab hb hL (show a ∈ Icc (lowU a) (c1 a b) from ⟨(lowU_lt_a hab hb hL).le, h1.le⟩)
  rwa [q_a] at this

theorem branch_fold : branch a b L (foldTau a b L) = c1 a b :=
  branch_q hab hb hL ⟨lowU_le_c1 hab hb hL, le_rfl⟩

theorem branch_strictMonoOn : StrictMonoOn (branch a b L) (Icc (lowTau a b L) (foldTau a b L)) := by
  intro s hs t ht hst
  by_contra hle; push Not at hle
  have hmono := (q_strictMonoOn hab hb hL).monotoneOn
  have := hmono (branch_mem hab hb hL ht).2 (branch_mem hab hb hL hs).2 hle
  rw [q_branch hab hb hL hs, q_branch hab hb hL ht] at this
  linarith

theorem image_branch : branch a b L '' Icc (lowTau a b L) (foldTau a b L) = Icc (lowU a) (c1 a b) := by
  apply Subset.antisymm
  · rintro _ ⟨t, ht, rfl⟩; exact branch_mem hab hb hL ht
  · intro u hu
    exact ⟨q a b L u, tau_mem_of_u_mem hab hb hL hu, branch_q hab hb hL hu⟩

theorem branch_lt_c1 {t : ℝ} (ht : t ∈ Ico (lowTau a b L) (foldTau a b L)) :
    branch a b L t < c1 a b := by
  have hlt : lowTau a b L < foldTau a b L := (lowTau_neg hab hb hL).trans (foldTau_pos hab hb hL)
  have h := branch_strictMonoOn hab hb hL ⟨ht.1, ht.2.le⟩ ⟨hlt.le, le_rfl⟩ ht.2
  rwa [branch_fold hab hb hL] at h

theorem lowU_lt_branch {t : ℝ} (ht : t ∈ Ioc (lowTau a b L) (foldTau a b L)) :
    lowU a < branch a b L t := by
  have hlow : branch a b L (lowTau a b L) = lowU a :=
    branch_q hab hb hL ⟨le_rfl, lowU_le_c1 hab hb hL⟩
  have h := branch_strictMonoOn hab hb hL
    ⟨le_rfl, (lowTau_neg hab hb hL).le.trans (foldTau_pos hab hb hL).le⟩ ⟨ht.1.le, ht.2⟩ ht.1
  rwa [hlow] at h

theorem branch_neg {t : ℝ} (ht : t ∈ Icc (lowTau a b L) (foldTau a b L)) : branch a b L t < 0 :=
  (branch_mem hab hb hL ht).2.trans_lt ((crit_order hab hb).2.1.trans hb)

theorem branch_continuousAt {t : ℝ} (ht : t ∈ Ioo (lowTau a b L) (foldTau a b L)) :
    ContinuousAt (branch a b L) t := by
  apply continuousAt_of_monotoneOn_of_image_mem_nhds (branch_strictMonoOn hab hb hL).monotoneOn
    (Icc_mem_nhds ht.1 ht.2)
  rw [image_branch hab hb hL]
  exact Icc_mem_nhds (lowU_lt_branch hab hb hL ⟨ht.1, ht.2.le⟩)
    (branch_lt_c1 hab hb hL ⟨ht.1.le, ht.2⟩)

theorem branch_continuousWithinAt_fold :
    ContinuousWithinAt (branch a b L) (Iic (foldTau a b L)) (foldTau a b L) := by
  have hlt : lowTau a b L < foldTau a b L := (lowTau_neg hab hb hL).trans (foldTau_pos hab hb hL)
  apply continuousWithinAt_left_of_monotoneOn_of_image_mem_nhdsWithin
    (branch_strictMonoOn hab hb hL).monotoneOn
    (Icc_mem_nhdsLE hlt)
  rw [image_branch hab hb hL, branch_fold hab hb hL]
  exact Icc_mem_nhdsLE ((lowU_lt_a hab hb hL).trans (crit_order hab hb).1)

/-- The scalar residual `R (t, u) = q u - t`. -/
def res (p : ℝ × ℝ) : ℝ := q a b L p.2 - p.1

omit hab hb hL in
theorem res_analyticAt (p : ℝ × ℝ) : AnalyticAt ℝ (res (a := a) (b := b) (L := L)) p := by
  have h2 : AnalyticAt ℝ (fun p : ℝ × ℝ => p.2) p := analyticAt_snd
  have h1 : AnalyticAt ℝ (fun p : ℝ × ℝ => p.1) p := analyticAt_fst
  have : (res (a := a) (b := b) (L := L)) =
      fun p : ℝ × ℝ => -L * p.2 ^ 2 * (p.2 - a) * (p.2 - b) - p.1 := by
    funext p; rfl
  rw [this]
  exact (((analyticAt_const.mul (h2.pow 2)).mul (h2.sub analyticAt_const)).mul
    (h2.sub analyticAt_const)).sub h1

theorem res_partial_isInvertible (t u : ℝ) (hu : qd a b L u ≠ 0) :
    ((fderiv ℝ (res (a := a) (b := b) (L := L)) (t, u)).comp
      (ContinuousLinearMap.inr ℝ ℝ ℝ)).IsInvertible := by
  have hR : HasFDerivAt (res (a := a) (b := b) (L := L))
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (qd a b L u)).comp
        (ContinuousLinearMap.snd ℝ ℝ ℝ) - ContinuousLinearMap.fst ℝ ℝ ℝ) (t, u) := by
    have h1 := (hasDerivAt_q (L := L) hab hb u).hasFDerivAt.comp (t, u) (hasFDerivAt_snd (𝕜 := ℝ) (p := (t, u)))
    exact h1.sub hasFDerivAt_fst
  rw [hR.fderiv]
  set f := ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (qd a b L u)).comp
        (ContinuousLinearMap.snd ℝ ℝ ℝ) - ContinuousLinearMap.fst ℝ ℝ ℝ).comp
      (ContinuousLinearMap.inr ℝ ℝ ℝ)
  have hf : f = (qd a b L u) • ContinuousLinearMap.id ℝ ℝ := by
    apply ContinuousLinearMap.ext_ring
    simp [f]
  rw [hf]
  apply ContinuousLinearMap.IsInvertible.of_inverse (g := (qd a b L u)⁻¹ • ContinuousLinearMap.id ℝ ℝ)
  · apply ContinuousLinearMap.ext_ring; simp [hu]
  · apply ContinuousLinearMap.ext_ring; simp [hu]

theorem branch_analyticAt {t : ℝ} (ht : t ∈ Ioo (lowTau a b L) (foldTau a b L)) :
    AnalyticAt ℝ (branch a b L) t := by
  apply ActualAnalyticBranch.continuous_regular_root_analyticAt
    (res (a := a) (b := b) (L := L)) (branch a b L) t (res_analyticAt _)
    (branch_continuousAt hab hb hL ht)
  · filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
    simp [res, q_branch hab hb hL hs]
  · exact res_partial_isInvertible hab hb hL t _
      (qd_pos hab hb hL (branch_lt_c1 hab hb hL ⟨ht.1.le, ht.2⟩)).ne'

theorem branch_deriv {t : ℝ} (ht : t ∈ Ioo (lowTau a b L) (foldTau a b L)) :
    deriv (branch a b L) t = (qd a b L (branch a b L t))⁻¹ := by
  have hd := (branch_analyticAt hab hb hL ht).differentiableAt.hasDerivAt
  have hcomp := (hasDerivAt_q (L := L) hab hb (branch a b L t)).comp t hd
  have hid : (q a b L ∘ branch a b L) =ᶠ[𝓝 t] id := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
    exact q_branch hab hb hL hs
  have h1 : HasDerivAt (q a b L ∘ branch a b L) 1 t := (hasDerivAt_id t).congr_of_eventuallyEq hid
  have := hcomp.unique h1
  have hq := (qd_pos hab hb hL (branch_lt_c1 hab hb hL ⟨ht.1.le, ht.2⟩)).ne'
  field_simp
  linarith

/-- `1 / q'` is absolutely monotone below the fold. -/
theorem inv_qd_absMono : AbsMonoOn (fun u => (qd a b L u)⁻¹) (Iio (c1 a b)) := by
  obtain ⟨h1, h2, h3, h4⟩ := crit_order hab hb
  have e : (fun u => (qd a b L u)⁻¹) =
      fun u => (4 * L)⁻¹ * ((0 - u)⁻¹ * ((c1 a b - u)⁻¹ * (c2 a b - u)⁻¹)) := by
    funext u; simp only [qd, mul_inv]; ring
  rw [e]
  apply AbsMonoOn.const_mul _ _ (by positivity)
  apply AbsMonoOn.mul isOpen_Iio
  · exact (inv_sub_absMono 0).mono (Iio_subset_Iio (h2.trans hb).le)
  apply AbsMonoOn.mul isOpen_Iio
  · exact inv_sub_absMono _
  · exact (inv_sub_absMono _).mono (Iio_subset_Iio (c1_le_c2 hab hb))

theorem branch_contDiffOn : ContDiffOn ℝ ∞ (branch a b L) (Ioo (lowTau a b L) (foldTau a b L)) :=
  fun t ht => ((branch_analyticAt hab hb hL ht).contDiffAt.of_le le_top).contDiffWithinAt

/-- Every derivative of order at least one of the branch is nonnegative below the fold. -/
theorem branch_iteratedDeriv_nonneg (n : ℕ) {t : ℝ} (ht : t ∈ Ioo (lowTau a b L) (foldTau a b L)) :
    0 ≤ iteratedDeriv (n + 1) (branch a b L) t :=
  iteratedDeriv_nonneg_of_ode (branch a b L) (fun u => (qd a b L u)⁻¹) _ (Iio (c1 a b))
    isOpen_Ioo isOpen_Iio (branch_contDiffOn hab hb hL) (inv_qd_absMono hab hb hL)
    (fun s hs => branch_lt_c1 hab hb hL ⟨hs.1.le, hs.2⟩)
    (fun s hs => branch_deriv hab hb hL hs) n t ht

/-- No function analytic at the fold agrees with the branch just below it. -/
theorem not_analytic_continuation (F : ℝ → ℝ) (hF : AnalyticAt ℝ F (foldTau a b L))
    (ε : ℝ) (hε : 0 < ε) (hεlow : lowTau a b L ≤ foldTau a b L - ε)
    (hFb : ∀ t ∈ Ico (foldTau a b L - ε) (foldTau a b L), F t = branch a b L t) : False := by
  set f := foldTau a b L with hfdef
  have hFf : F f = c1 a b := by
    have hlim1 : Tendsto F (𝓝[<] f) (𝓝 (F f)) :=
      hF.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hlim2 : Tendsto (branch a b L) (𝓝[<] f) (𝓝 (c1 a b)) := by
      have := (branch_continuousWithinAt_fold hab hb hL).tendsto.mono_left
        (nhdsWithin_mono _ (fun x (hx : x < f) => (le_of_lt hx : x ≤ f)))
      rwa [branch_fold hab hb hL] at this
    have heq : F =ᶠ[𝓝[<] f] branch a b L := by
      filter_upwards [Ico_mem_nhdsLT (show f - ε < f by linarith)] with t ht
      exact hFb t ht
    exact tendsto_nhds_unique (hlim1.congr' heq) hlim2
  have hd := (hasDerivAt_q (L := L) hab hb (F f)).comp f hF.differentiableAt.hasDerivAt
  rw [hFf, qd_c1 (L := L) hab hb] at hd
  have hid : EqOn (q a b L ∘ F) id (Icc (f - ε) f) := by
    intro t ht
    rcases eq_or_lt_of_le ht.2 with h | h
    · rw [h]; simp only [Function.comp, hFf, id]; rfl
    · simp only [Function.comp, hFb t ⟨ht.1, h⟩, id]
      exact q_branch hab hb hL ⟨hεlow.trans ht.1, h.le⟩
  have hmem : f ∈ Icc (f - ε) f := ⟨by linarith, le_rfl⟩
  have h1 : HasDerivWithinAt (q a b L ∘ F) 1 (Icc (f - ε) f) f :=
    (hasDerivAt_id f).hasDerivWithinAt.congr hid (hid hmem)
  have huniq := (uniqueDiffOn_Icc (show f - ε < f by linarith)) f hmem
  have h01 := huniq.eq hd.hasDerivWithinAt h1
  have := DFunLike.congr_fun h01 1
  simp at this

end FMSA.Paper.QuarticBranch

/-- info: 'FMSA.Paper.QuarticBranch.disc_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.QuarticBranch.disc_pos

/-- info: 'FMSA.Paper.QuarticBranch.quad_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.QuarticBranch.quad_factor

/-- info: 'FMSA.Paper.QuarticBranch.c1_le_c2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.QuarticBranch.c1_le_c2

/-- info: 'FMSA.Paper.QuarticBranch.crit_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.QuarticBranch.crit_order

/-- info: 'FMSA.Paper.QuarticBranch.hasDerivAt_q' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.QuarticBranch.hasDerivAt_q

/-- info: 'FMSA.Paper.QuarticBranch.qd_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.QuarticBranch.qd_pos

/-- info: 'FMSA.Paper.QuarticBranch.qd_c1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.QuarticBranch.qd_c1

/-- info: 'FMSA.Paper.QuarticBranch.q_strictMonoOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.QuarticBranch.q_strictMonoOn

/-- info: 'FMSA.Paper.QuarticBranch.q_a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.QuarticBranch.q_a

/-- info: 'FMSA.Paper.QuarticBranch.lowU_lt_a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.QuarticBranch.lowU_lt_a

/-- info: 'FMSA.Paper.QuarticBranch.foldTau_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.QuarticBranch.foldTau_pos

/-- info: 'FMSA.Paper.QuarticBranch.lowTau_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.QuarticBranch.lowTau_neg

/-- info: 'FMSA.Paper.QuarticBranch.lowU_le_c1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.QuarticBranch.lowU_le_c1

/-- info: 'FMSA.Paper.QuarticBranch.q_surj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.QuarticBranch.q_surj

/-- info: 'FMSA.Paper.QuarticBranch.q_injOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.QuarticBranch.q_injOn

/-- info: 'FMSA.Paper.QuarticBranch.branch_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.QuarticBranch.branch_mem

/-- info: 'FMSA.Paper.QuarticBranch.q_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.QuarticBranch.q_branch

/-- info: 'FMSA.Paper.QuarticBranch.branch_q' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.QuarticBranch.branch_q

/-- info: 'FMSA.Paper.QuarticBranch.tau_mem_of_u_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.QuarticBranch.tau_mem_of_u_mem

/-- info: 'FMSA.Paper.QuarticBranch.branch_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.QuarticBranch.branch_zero

/-- info: 'FMSA.Paper.QuarticBranch.branch_fold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.QuarticBranch.branch_fold

/-- info: 'FMSA.Paper.QuarticBranch.branch_strictMonoOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.QuarticBranch.branch_strictMonoOn

/-- info: 'FMSA.Paper.QuarticBranch.image_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.QuarticBranch.image_branch

/-- info: 'FMSA.Paper.QuarticBranch.branch_lt_c1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.QuarticBranch.branch_lt_c1

/-- info: 'FMSA.Paper.QuarticBranch.lowU_lt_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.QuarticBranch.lowU_lt_branch

/-- info: 'FMSA.Paper.QuarticBranch.branch_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.QuarticBranch.branch_neg

/-- info: 'FMSA.Paper.QuarticBranch.branch_continuousAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.QuarticBranch.branch_continuousAt

/-- info: 'FMSA.Paper.QuarticBranch.branch_continuousWithinAt_fold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.QuarticBranch.branch_continuousWithinAt_fold

/-- info: 'FMSA.Paper.QuarticBranch.res_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.QuarticBranch.res_analyticAt

/-- info: 'FMSA.Paper.QuarticBranch.res_partial_isInvertible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.QuarticBranch.res_partial_isInvertible

/-- info: 'FMSA.Paper.QuarticBranch.branch_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.QuarticBranch.branch_analyticAt

/-- info: 'FMSA.Paper.QuarticBranch.branch_deriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.QuarticBranch.branch_deriv

/-- info: 'FMSA.Paper.QuarticBranch.inv_qd_absMono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.QuarticBranch.inv_qd_absMono

/-- info: 'FMSA.Paper.QuarticBranch.branch_contDiffOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.QuarticBranch.branch_contDiffOn

/-- info: 'FMSA.Paper.QuarticBranch.branch_iteratedDeriv_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.QuarticBranch.branch_iteratedDeriv_nonneg

/-- info: 'FMSA.Paper.QuarticBranch.not_analytic_continuation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.QuarticBranch.not_analytic_continuation
