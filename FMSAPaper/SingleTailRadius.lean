import FMSAPaper.SingleTailParametrization
import FMSAPaper.QuarticBranch
import FMSAPaper.ActualAnalyticTaylor

/-! **Single-tail fold binds.** For one hard-sphere species and one attractive
Yukawa tail, the actual exact-MSA (Blum–Høye) PY-seeded branch has
nonnegative Taylor coefficients of every positive order in both amplitude
components, and the common Taylor radius of the coupling series equals the
explicit fold coupling. No sign, convergence or fold hypothesis is assumed:
the reduction `τ = q (u)` to a quartic with real ordered critical points,
absolute monotonicity of `1 / q'` and Pringsheim's theorem give the lower
bound; the impossibility of continuing the branch through the fold gives the
upper bound. -/
noncomputable section
open Set Filter Topology Real
open scoped ContDiff

namespace FMSA.Paper.SingleTailRadius
open ExactMSA.MultiTailMixture ExactMSA.BSource FormalMultilinearSeries
open SingleTail QuarticBranch AbsolutelyMonotone TaylorRoot FoldRadius AnalyticTaylor
open ActualAnalyticTaylor

variable {T : Type*} [Fintype T] [Unique T]
variable (z : T → ℝ) (rho sigma : Fin 1 → ℝ) (K : TailMatrix T 1)

/-- Seed root, second root and quartic coefficient of the reduction. -/
abbrev aR : ℝ := aS (z default) (rho 0) (sigma 0)
abbrev bR : ℝ := bS (z default) (rho 0) (sigma 0)
abbrev LR : ℝ := LamS (z default) (rho 0) (sigma 0) (K default 0 0)

/-- The fold coupling `τ_f = q (c₁)`, explicit in `z, ρ, σ, K`. -/
def foldCoupling : ℝ := foldTau (aR z rho sigma) (bR z rho sigma) (LR z rho sigma K)

/-- The physical branch, parametrized by the inverse quartic branch. -/
def physBranch (t : ℝ) : TailMatrix T 1 × TailMatrix T 1 :=
  (sc (DtS (z default) (rho 0) (sigma 0) (branch (aR z rho sigma) (bR z rho sigma) (LR z rho sigma K) t)),
   sc (GS (z default) (rho 0) (sigma 0) (branch (aR z rho sigma) (bR z rho sigma) (LR z rho sigma K) t)))

variable (hz : 0 < z default) (hr : 0 < rho 0) (hs : 0 < sigma 0)
  (hv : 0 < MatrixQ0.vacMix rho sigma) (hk : 0 < K default 0 0)

theorem vacMix_eq : MatrixQ0.vacMix rho sigma = vacS (rho 0) (sigma 0) := by
  simp [MatrixQ0.vacMix, MatrixQ0.etaMix, vacS]

include hz hr hs hv

theorem hw : 0 < vacS (rho 0) (sigma 0) := by rw [← vacMix_eq]; exact hv

theorem hab : aR z rho sigma < bR z rho sigma :=
  aS_lt_bS _ _ _ hz hs hr (hw z rho sigma hz hr hs hv)

theorem hb : bR z rho sigma < 0 := bS_neg _ _ _ hz hs hr (hw z rho sigma hz hr hs hv)

theorem hDd : 0 < DdS (z default) (rho 0) (sigma 0) :=
  DdS_pos _ _ _ hz hs hr (hw z rho sigma hz hr hs hv)

include hk

theorem hL : 0 < LR z rho sigma K := by
  have h1 := hDd z rho sigma hz hr hs hv
  have h2 := hw z rho sigma hz hr hs hv
  have h3 := etaS_pos (rho 0) (sigma 0) hs hr
  have h4 := xS_pos _ _ hz hs
  unfold LR LamS; positivity

/-- Abbreviation bundle used below. -/
local notation "A" => aR z rho sigma
local notation "B" => bR z rho sigma
local notation "Lq" => LR z rho sigma K
local notation "br" => branch (aR z rho sigma) (bR z rho sigma) (LR z rho sigma K)

omit hz hr hs hv hk in
theorem tauS_eq_q (v : ℝ) :
    tauS (z default) (rho 0) (sigma 0) (K default 0 0) v = q A B Lq v := rfl

theorem zero_mem_Ioo : (0 : ℝ) ∈ Ioo (lowTau A B Lq) (foldTau A B Lq) :=
  ⟨lowTau_neg (hab z rho sigma hz hr hs hv) (hb z rho sigma hz hr hs hv) (hL z rho sigma K hz hr hs hv hk),
   foldTau_pos (hab z rho sigma hz hr hs hv) (hb z rho sigma hz hr hs hv) (hL z rho sigma K hz hr hs hv hk)⟩

theorem physBranch_isRoot {t : ℝ} (ht : t ∈ Icc (lowTau A B Lq) (foldTau A B Lq)) :
    IsRoot z rho sigma (t • K) (physBranch z rho sigma K t).1 (physBranch z rho sigma K t).2 := by
  have hab' := hab z rho sigma hz hr hs hv
  have hb' := hb z rho sigma hz hr hs hv
  have hL' := hL z rho sigma K hz hr hs hv hk
  have hv0 : br t ≠ 0 := (branch_neg hab' hb' hL' ht).ne
  have h := isRoot_param z rho sigma K (K default 0 0)
    (fun u i j => by
      rw [Subsingleton.elim u default, Subsingleton.elim i 0, Subsingleton.elim j 0])
    hz.ne' hs.ne' hr.ne' (hw z rho sigma hz hr hs hv).ne' hk.ne'
    (hDd z rho sigma hz hr hs hv).ne' (br t) hv0
  rwa [tauS_eq_q, q_branch hab' hb' hL' ht] at h

theorem physBranch_zero :
    physBranch z rho sigma K 0 = (0, baseSeed z rho sigma) := by
  have hab' := hab z rho sigma hz hr hs hv
  have hb' := hb z rho sigma hz hr hs hv
  have hL' := hL z rho sigma K hz hr hs hv hk
  have hP : PS (z default) (rho 0) (sigma 0) ≠ 0 := by
    have := aS_neg _ _ _ hz hs hr (hw z rho sigma hz hr hs hv)
    simp only [aS] at this; linarith
  simp only [physBranch, branch_zero hab' hb' hL', DtS_seed,
    GS_seed _ _ _ hz.ne' hs.ne' hr.ne' (hw z rho sigma hz hr hs hv).ne'
      (hDd z rho sigma hz hr hs hv).ne' hP]
  refine Prod.ext ?_ ?_
  · funext u i j; rfl
  · funext u i j; exact (baseSeed_sc z rho sigma u i j).symm

theorem physBranch_analyticAt {t : ℝ} (ht : t ∈ Ioo (lowTau A B Lq) (foldTau A B Lq)) :
    AnalyticAt ℝ (physBranch z rho sigma K) t := by
  have hab' := hab z rho sigma hz hr hs hv
  have hb' := hb z rho sigma hz hr hs hv
  have hL' := hL z rho sigma K hz hr hs hv hk
  have hbr := branch_analyticAt hab' hb' hL' ht
  have hne : br t ≠ 0 := (branch_neg hab' hb' hL' ⟨ht.1.le, ht.2.le⟩).ne
  have hD : AnalyticAt ℝ (fun t => DtS (z default) (rho 0) (sigma 0) (br t)) t := by
    have h1 : AnalyticAt ℝ (fun t => -(π * sigma 0 ^ 2) /
        (3 * etaS (rho 0) (sigma 0) * xS (z default) (sigma 0) ^ 3 * vacS (rho 0) (sigma 0) ^ 3 *
          DdS (z default) (rho 0) (sigma 0)) * (br t * (br t - A))) t :=
      analyticAt_const.mul (hbr.mul (hbr.sub analyticAt_const))
    refine h1.congr (Filter.Eventually.of_forall (fun y => ?_))
    simp only [DtS]; ring
  have hG : AnalyticAt ℝ (fun t => GS (z default) (rho 0) (sigma 0) (br t)) t := by
    have h1 : AnalyticAt ℝ (fun t => sigma 0 ^ 2 * xS (z default) (sigma 0) /
        (12 * etaS (rho 0) (sigma 0) * DdS (z default) (rho 0) (sigma 0)) *
        ((etaS (rho 0) (sigma 0) * xS (z default) (sigma 0) ^ 2 +
          6 * etaS (rho 0) (sigma 0) * xS (z default) (sigma 0) + 12 * etaS (rho 0) (sigma 0) -
          xS (z default) (sigma 0) ^ 2) -
          vacS (rho 0) (sigma 0) ^ 3 * xS (z default) (sigma 0) ^ 5 / br t)) t :=
      analyticAt_const.mul (analyticAt_const.sub (analyticAt_const.div hbr hne))
    exact h1.congr (Filter.Eventually.of_forall (fun y => rfl))
  have hsc : ∀ f : ℝ → ℝ, AnalyticAt ℝ f t → AnalyticAt ℝ (fun t => (sc (f t) : TailMatrix T 1)) t :=
    fun f hf => analyticAt_pi_iff.mpr fun _ => analyticAt_pi_iff.mpr fun _ =>
      analyticAt_pi_iff.mpr fun _ => hf
  exact (hsc _ hD).prod (hsc _ hG)

theorem physBranch_analyticOnNhd :
    AnalyticOnNhd ℝ (physBranch z rho sigma K) (Ico 0 (foldTau A B Lq)) := fun t ht =>
  physBranch_analyticAt z rho sigma K hz hr hs hv hk
    ⟨(zero_mem_Ioo z rho sigma K hz hr hs hv hk).1.trans_le ht.1, ht.2⟩

theorem physBranch_local_root :
    ∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K)
      (physBranch z rho sigma K t).1 (physBranch z rho sigma K t).2 := by
  have h0 := zero_mem_Ioo z rho sigma K hz hr hs hv hk
  filter_upwards [Icc_mem_nhds h0.1 h0.2] with t ht
  exact physBranch_isRoot z rho sigma K hz hr hs hv hk ht

theorem branch_contDiffAt_zero (n : ℕ) : ContDiffAt ℝ n br 0 :=
  (branch_analyticAt (hab z rho sigma hz hr hs hv) (hb z rho sigma hz hr hs hv)
    (hL z rho sigma K hz hr hs hv hk) (zero_mem_Ioo z rho sigma K hz hr hs hv hk)).contDiffAt.of_le
    le_top

theorem branch_derivs_zero (k : ℕ) (hk0 : 0 < k) : 0 ≤ iteratedDeriv k br 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  exact branch_iteratedDeriv_nonneg (hab z rho sigma hz hr hs hv) (hb z rho sigma hz hr hs hv)
    (hL z rho sigma K hz hr hs hv hk) m (zero_mem_Ioo z rho sigma K hz hr hs hv hk)

theorem branch_zero_eq_seed : br 0 = A :=
  branch_zero (hab z rho sigma hz hr hs hv) (hb z rho sigma hz hr hs hv) (hL z rho sigma K hz hr hs hv hk)

/-- Every positive-order Taylor coefficient of the `G` component is nonnegative. -/
theorem G_coeff_nonneg (n : ℕ) (hn : 0 < n) :
    0 ≤ jet (fun t => GS (z default) (rho 0) (sigma 0) (br t)) n := by
  have hA := aS_neg _ _ _ hz hs hr (hw z rho sigma hz hr hs hv)
  set C1 := sigma 0 ^ 2 * xS (z default) (sigma 0) /
    (12 * etaS (rho 0) (sigma 0) * DdS (z default) (rho 0) (sigma 0)) *
      (vacS (rho 0) (sigma 0) ^ 3 * xS (z default) (sigma 0) ^ 5)
  have hC1 : 0 < C1 := by
    have := hDd z rho sigma hz hr hs hv; have := hw z rho sigma hz hr hs hv
    have := etaS_pos (rho 0) (sigma 0) hs hr; have := xS_pos _ _ hz hs
    positivity
  have he : (fun t => GS (z default) (rho 0) (sigma 0) (br t)) =
      fun t => (sigma 0 ^ 2 * xS (z default) (sigma 0) /
        (12 * etaS (rho 0) (sigma 0) * DdS (z default) (rho 0) (sigma 0)) *
        (etaS (rho 0) (sigma 0) * xS (z default) (sigma 0) ^ 2 + 6 * etaS (rho 0) (sigma 0) *
          xS (z default) (sigma 0) + 12 * etaS (rho 0) (sigma 0) - xS (z default) (sigma 0) ^ 2)) +
        C1 * ((fun v => (0 - v)⁻¹) ∘ br) t := by
    funext t; rw [GS_eq]; simp only [Function.comp, C1]; try ring
  have hg : AbsMonoOn (fun v : ℝ => (0 - v)⁻¹) (Iio 0) := inv_sub_absMono 0
  have hbr0 : br 0 ∈ Iio (0 : ℝ) := by rw [branch_zero_eq_seed z rho sigma K hz hr hs hv hk]; exact hA
  have hcomp := comp_signed (fun v => (0 - v)⁻¹) br 0 1
    (fun m => contDiffAt_of_contDiffOn isOpen_Iio hg.1 hbr0 m)
    (branch_contDiffAt_zero z rho sigma K hz hr hs hv hk)
    (fun m _ => by rw [one_mul]; exact hg.2 m _ hbr0)
    (branch_derivs_zero z rho sigma K hz hr hs hv hk) n hn
  rw [he]
  simp only [jet]
  rw [iteratedDeriv_const_add hn, iteratedDeriv_const_mul_field]
  rw [one_mul] at hcomp
  positivity

/-- Every positive-order Taylor coefficient of the `D̃` component is nonnegative. -/
theorem D_coeff_nonneg (n : ℕ) (hn : 0 < n) :
    0 ≤ jet (fun t => DtS (z default) (rho 0) (sigma 0) (br t)) n := by
  have hab' := hab z rho sigma hz hr hs hv
  have hb' := hb z rho sigma hz hr hs hv
  have hL' := hL z rho sigma K hz hr hs hv hk
  have h0 := zero_mem_Ioo z rho sigma K hz hr hs hv hk
  set M : ℝ → ℝ := (fun v => (0 - v)⁻¹ * (B - v)⁻¹) ∘ br with hM
  have hm : AbsMonoOn (fun v : ℝ => (0 - v)⁻¹ * (B - v)⁻¹) (Iio B) :=
    AbsMonoOn.mul isOpen_Iio ((inv_sub_absMono 0).mono (Iio_subset_Iio hb'.le)) (inv_sub_absMono _)
  have hbr0 : br 0 ∈ Iio B := by rw [branch_zero_eq_seed z rho sigma K hz hr hs hv hk]; exact hab'
  have hMk : ∀ k : ℕ, 0 ≤ iteratedDeriv k M 0 := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simpa [M] using hm.2 0 _ hbr0
    · have := comp_signed (fun v => (0 - v)⁻¹ * (B - v)⁻¹) br 0 1
        (fun m => contDiffAt_of_contDiffOn isOpen_Iio hm.1 hbr0 m)
        (branch_contDiffAt_zero z rho sigma K hz hr hs hv hk)
        (fun m _ => by rw [one_mul]; exact hm.2 m _ hbr0)
        (branch_derivs_zero z rho sigma K hz hr hs hv hk) k hk0
      simpa [M] using this
  have hMc : ∀ k : ℕ, ContDiffAt ℝ k M 0 := fun k =>
    (contDiffAt_of_contDiffOn isOpen_Iio hm.1 hbr0 k).comp 0
      (branch_contDiffAt_zero z rho sigma K hz hr hs hv hk k)
  set cD := cDS (z default) (rho 0) (sigma 0) (K default 0 0)
  have hcD : 0 < cD := by
    have := hDd z rho sigma hz hr hs hv; have := hw z rho sigma hz hr hs hv
    have := xS_pos _ _ hz hs
    simp only [cD, cDS]; positivity
  have heq : (fun t => DtS (z default) (rho 0) (sigma 0) (br t)) =ᶠ[𝓝 (0 : ℝ)]
      fun t => cD * (t * M t) := by
    filter_upwards [Icc_mem_nhds h0.1 h0.2] with t ht
    have hneg := branch_neg hab' hb' hL' ht
    have hltb : br t < B := (branch_mem hab' hb' hL' ht).2.trans_lt (crit_order hab' hb').2.1
    rw [DtS_eq_tau _ _ _ (K default 0 0) hz.ne' hs.ne' hr.ne' (hw z rho sigma hz hr hs hv).ne'
      hk.ne' (hDd z rho sigma hz hr hs hv).ne' _ hneg.ne hltb.ne, tauS_eq_q,
      q_branch hab' hb' hL' ht]
    simp only [M, Function.comp]; ring
  simp only [jet]
  rw [heq.iteratedDeriv_eq, iteratedDeriv_const_mul_field,
    iteratedDeriv_fun_mul (show ContDiffAt ℝ n (fun t : ℝ => t) 0 from contDiffAt_id) (hMc n)]
  simp only [iteratedDeriv_fun_id_zero]
  apply div_nonneg _ (by positivity)
  apply mul_nonneg hcD.le
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · have := hMk (n - i); positivity
  · simp

theorem physBranch_lower :
    ENNReal.ofReal (foldTau A B Lq) ≤ amplitudeRadius (branchCoefficients (physBranch z rho sigma K)) := by
  apply le_amplitudeRadius_of_signed_analytic_branch _ _
    (foldTau_pos (hab z rho sigma hz hr hs hv) (hb z rho sigma hz hr hs hv)
      (hL z rho sigma K hz hr hs hv hk))
    (physBranch_analyticOnNhd z rho sigma K hz hr hs hv hk)
  · intro u i j
    exact ⟨1, one_ne_zero, fun n hn => by
      rw [one_mul]; exact D_coeff_nonneg z rho sigma K hz hr hs hv hk n hn⟩
  · intro u i j
    exact ⟨1, one_ne_zero, fun n hn => by
      rw [one_mul]; exact G_coeff_nonneg z rho sigma K hz hr hs hv hk n hn⟩

theorem physBranch_upper :
    amplitudeRadius (branchCoefficients (physBranch z rho sigma K)) ≤ ENNReal.ofReal (foldTau A B Lq) := by
  have hab' := hab z rho sigma hz hr hs hv
  have hb' := hb z rho sigma hz hr hs hv
  have hL' := hL z rho sigma K hz hr hs hv hk
  have hf := foldTau_pos hab' hb' hL'
  set f := foldTau A B Lq with hfdef
  set gfun : ℝ → ℝ := fun t => GS (z default) (rho 0) (sigma 0) (br t) with hgfun
  have hle : amplitudeRadius (branchCoefficients (physBranch z rho sigma K)) ≤
      (ofScalars ℝ (jet gfun)).radius :=
    iInf_le_of_le default (iInf_le_of_le 0 (iInf_le_of_le 0 (min_le_right _ _)))
  refine hle.trans ?_
  by_contra hcon
  push Not at hcon
  have hAn : AnalyticOnNhd ℝ gfun (Ico 0 f) := fun t ht =>
    (ActualAnalyticTaylor.analyticAt_components _ t
      (physBranch_analyticOnNhd z rho sigma K hz hr hs hv hk t ht)).2 default 0 0
  set S := (ofScalars ℝ (jet gfun)).sum
  have hSan : AnalyticAt ℝ S f := by
    apply (ofScalars ℝ (jet gfun)).analyticOnNhd f
    rw [mem_eball_zero_iff, ← ofReal_norm, Real.norm_of_nonneg hf.le]
    exact hcon
  have hSeq : ∀ t ∈ Ico 0 f, gfun t = S t := fun t ht =>
    eq_jet_sum_on_interval gfun f hAn t ht ((ENNReal.ofReal_le_ofReal ht.2.le).trans_lt hcon)
  set C0 := sigma 0 ^ 2 * xS (z default) (sigma 0) /
    (12 * etaS (rho 0) (sigma 0) * DdS (z default) (rho 0) (sigma 0)) *
    (etaS (rho 0) (sigma 0) * xS (z default) (sigma 0) ^ 2 + 6 * etaS (rho 0) (sigma 0) *
      xS (z default) (sigma 0) + 12 * etaS (rho 0) (sigma 0) - xS (z default) (sigma 0) ^ 2)
  set C1 := sigma 0 ^ 2 * xS (z default) (sigma 0) /
    (12 * etaS (rho 0) (sigma 0) * DdS (z default) (rho 0) (sigma 0)) *
      (vacS (rho 0) (sigma 0) ^ 3 * xS (z default) (sigma 0) ^ 5)
  have hC1 : C1 ≠ 0 := by
    have := hDd z rho sigma hz hr hs hv; have := hw z rho sigma hz hr hs hv
    have := etaS_pos (rho 0) (sigma 0) hs hr; have := xS_pos _ _ hz hs
    positivity
  have hg : ∀ t, gfun t = C0 + C1 * (0 - br t)⁻¹ := fun t => by
    rw [hgfun]; exact GS_eq _ _ _ _
  have hc1 : c1 A B < 0 := (crit_order hab' hb').2.1.trans hb'
  -- the value of the sum at the fold
  have hSf : S f = C0 + C1 * (0 - c1 A B)⁻¹ := by
    have hlim1 : Tendsto S (𝓝[<] f) (𝓝 (S f)) :=
      hSan.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hcv : ContinuousAt (fun v : ℝ => C0 + C1 * (0 - v)⁻¹) (c1 A B) := by
      apply ContinuousAt.add continuousAt_const
      apply ContinuousAt.mul continuousAt_const
      exact (continuousAt_const.sub continuousAt_id).inv₀ (by simpa using hc1.ne)
    have hbrl : Tendsto br (𝓝[<] f) (𝓝 (c1 A B)) := by
      have := (branch_continuousWithinAt_fold hab' hb' hL').tendsto.mono_left
        (nhdsWithin_mono _ (fun x (hx : x < f) => (le_of_lt hx : x ≤ f)))
      rwa [branch_fold hab' hb' hL'] at this
    have hlim2 : Tendsto gfun (𝓝[<] f) (𝓝 (C0 + C1 * (0 - c1 A B)⁻¹)) := by
      have := hcv.tendsto.comp hbrl
      exact this.congr (fun t => (hg t).symm)
    have heq : S =ᶠ[𝓝[<] f] gfun := by
      filter_upwards [Ico_mem_nhdsLT hf] with t ht
      exact (hSeq t ht).symm
    exact tendsto_nhds_unique (hlim1.congr' heq) hlim2
  have hne : S f - C0 ≠ 0 := by
    rw [hSf, add_sub_cancel_left]
    exact mul_ne_zero hC1 (inv_ne_zero (by simpa using hc1.ne))
  have hF : AnalyticAt ℝ (fun t => -(C1 / (S t - C0))) f :=
    (analyticAt_const.div (hSan.sub analyticAt_const) hne).neg
  apply not_analytic_continuation hab' hb' hL' _ hF f hf
    (by have := lowTau_neg hab' hb' hL'; linarith [hfdef])
  intro t ht0
  have ht : t ∈ Ico 0 f := ⟨by have := ht0.1; linarith [hfdef], by have := ht0.2; linarith [hfdef]⟩
  have hneg := branch_neg hab' hb' hL' ⟨(lowTau_neg hab' hb' hL').le.trans ht.1, ht.2.le⟩
  rw [← hSeq t ht, hg t]
  have h0 : (0 - br t) ≠ 0 := by simpa using hneg.ne
  field_simp [hC1]
  ring

theorem physBranch_continuousAt : ContinuousAt (physBranch z rho sigma K) 0 :=
  (physBranch_analyticAt z rho sigma K hz hr hs hv hk
    (zero_mem_Ioo z rho sigma K hz hr hs hv hk)).continuousAt

theorem branchCoefficients_eq (p : ℝ → TailMatrix T 1 × TailMatrix T 1)
    (hp : ContinuousAt p 0) (hp0 : p 0 = (0, baseSeed z rho sigma))
    (hroot : ∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K) (p t).1 (p t).2) :
    branchCoefficients p = branchCoefficients (physBranch z rho sigma K) := by
  have hzu : ∀ u, 0 < z u := fun u => by rw [Subsingleton.elim u default]; exact hz
  have hrho : ∀ i, 0 ≤ rho i := fun i => by rw [Subsingleton.elim i 0]; exact hr.le
  have hsig : ∀ i, 0 < sigma i := fun i => by rw [Subsingleton.elim i 0]; exact hs
  have heq := LocalBranch.actual_seed_roots_eventuallyEq z rho sigma K hzu hv hrho hsig p
    (physBranch z rho sigma K) hp (physBranch_continuousAt z rho sigma K hz hr hs hv hk) hp0
    (physBranch_zero z rho sigma K hz hr hs hv hk) hroot
    (physBranch_local_root z rho sigma K hz hr hs hv hk)
  funext n
  refine Prod.ext ?_ ?_ <;> funext u i j <;> simp only [branchCoefficients, jet]
  · have h := (heq.fun_comp (fun x => x.1 u i j)).iteratedDeriv_eq n
    simp only [Function.comp_def] at h
    rw [h]
  · have h := (heq.fun_comp (fun x => x.2 u i j)).iteratedDeriv_eq n
    simp only [Function.comp_def] at h
    rw [h]

/-- **Main theorem.** For one hard-sphere species and one attractive Yukawa
tail, the common Taylor radius of the coupling series of every continuous
PY-seeded exact-MSA root germ equals the explicit fold coupling `q (c₁)`. -/
theorem single_tail_radius_eq_fold (p : ℝ → TailMatrix T 1 × TailMatrix T 1)
    (hp : ContinuousAt p 0) (hp0 : p 0 = (0, baseSeed z rho sigma))
    (hroot : ∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K) (p t).1 (p t).2) :
    amplitudeRadius (branchCoefficients p) = ENNReal.ofReal (foldCoupling z rho sigma K) := by
  rw [branchCoefficients_eq z rho sigma K hz hr hs hv hk p hp hp0 hroot]
  exact le_antisymm (physBranch_upper z rho sigma K hz hr hs hv hk)
    (physBranch_lower z rho sigma K hz hr hs hv hk)

/-- All positive-order Taylor coefficients of both amplitude components of
the PY-seeded branch are nonnegative (the Pringsheim sign condition holds). -/
theorem single_tail_coefficients_nonneg (p : ℝ → TailMatrix T 1 × TailMatrix T 1)
    (hp : ContinuousAt p 0) (hp0 : p 0 = (0, baseSeed z rho sigma))
    (hroot : ∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K) (p t).1 (p t).2)
    (n : ℕ) (hn : 0 < n) (u : T) (i j : Fin 1) :
    0 ≤ (branchCoefficients p n).1 u i j ∧ 0 ≤ (branchCoefficients p n).2 u i j := by
  rw [branchCoefficients_eq z rho sigma K hz hr hs hv hk p hp hp0 hroot]
  exact ⟨D_coeff_nonneg z rho sigma K hz hr hs hv hk n hn,
    G_coeff_nonneg z rho sigma K hz hr hs hv hk n hn⟩

/-- The fold coupling is positive. -/
theorem foldCoupling_pos : 0 < foldCoupling z rho sigma K :=
  foldTau_pos (hab z rho sigma hz hr hs hv) (hb z rho sigma hz hr hs hv) (hL z rho sigma K hz hr hs hv hk)

/-- The hypotheses of the main theorem are satisfiable: the explicit branch is a
continuous PY-seeded root germ, real on `[0, τ_f]`, with radius `τ_f`. -/
theorem single_tail_branch_exists :
    ∃ p : ℝ → TailMatrix T 1 × TailMatrix T 1,
      ContinuousAt p 0 ∧ p 0 = (0, baseSeed z rho sigma) ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • K) (p t).1 (p t).2) ∧
      (∀ t ∈ Icc 0 (foldCoupling z rho sigma K), IsRoot z rho sigma (t • K) (p t).1 (p t).2) ∧
      amplitudeRadius (branchCoefficients p) = ENNReal.ofReal (foldCoupling z rho sigma K) := by
  refine ⟨physBranch z rho sigma K, physBranch_continuousAt z rho sigma K hz hr hs hv hk,
    physBranch_zero z rho sigma K hz hr hs hv hk, physBranch_local_root z rho sigma K hz hr hs hv hk,
    fun t ht => physBranch_isRoot z rho sigma K hz hr hs hv hk
      ⟨(zero_mem_Ioo z rho sigma K hz hr hs hv hk).1.le.trans ht.1, ht.2⟩, ?_⟩
  exact single_tail_radius_eq_fold z rho sigma K hz hr hs hv hk _
    (physBranch_continuousAt z rho sigma K hz hr hs hv hk)
    (physBranch_zero z rho sigma K hz hr hs hv hk) (physBranch_local_root z rho sigma K hz hr hs hv hk)

end FMSA.Paper.SingleTailRadius

/-- info: 'FMSA.Paper.SingleTailRadius.vacMix_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SingleTailRadius.vacMix_eq

/-- info: 'FMSA.Paper.SingleTailRadius.hw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SingleTailRadius.hw

/-- info: 'FMSA.Paper.SingleTailRadius.hab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SingleTailRadius.hab

/-- info: 'FMSA.Paper.SingleTailRadius.hb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SingleTailRadius.hb

/-- info: 'FMSA.Paper.SingleTailRadius.hDd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SingleTailRadius.hDd

/-- info: 'FMSA.Paper.SingleTailRadius.hL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SingleTailRadius.hL

/-- info: 'FMSA.Paper.SingleTailRadius.tauS_eq_q' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SingleTailRadius.tauS_eq_q

/-- info: 'FMSA.Paper.SingleTailRadius.zero_mem_Ioo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SingleTailRadius.zero_mem_Ioo

/-- info: 'FMSA.Paper.SingleTailRadius.physBranch_isRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SingleTailRadius.physBranch_isRoot

/-- info: 'FMSA.Paper.SingleTailRadius.physBranch_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SingleTailRadius.physBranch_zero

/-- info: 'FMSA.Paper.SingleTailRadius.physBranch_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SingleTailRadius.physBranch_analyticAt

/-- info: 'FMSA.Paper.SingleTailRadius.physBranch_analyticOnNhd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SingleTailRadius.physBranch_analyticOnNhd

/-- info: 'FMSA.Paper.SingleTailRadius.physBranch_local_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SingleTailRadius.physBranch_local_root

/-- info: 'FMSA.Paper.SingleTailRadius.branch_contDiffAt_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SingleTailRadius.branch_contDiffAt_zero

/-- info: 'FMSA.Paper.SingleTailRadius.branch_derivs_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SingleTailRadius.branch_derivs_zero

/-- info: 'FMSA.Paper.SingleTailRadius.branch_zero_eq_seed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SingleTailRadius.branch_zero_eq_seed

/-- info: 'FMSA.Paper.SingleTailRadius.G_coeff_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SingleTailRadius.G_coeff_nonneg

/-- info: 'FMSA.Paper.SingleTailRadius.D_coeff_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SingleTailRadius.D_coeff_nonneg

/-- info: 'FMSA.Paper.SingleTailRadius.physBranch_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SingleTailRadius.physBranch_lower

/-- info: 'FMSA.Paper.SingleTailRadius.physBranch_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SingleTailRadius.physBranch_upper

/-- info: 'FMSA.Paper.SingleTailRadius.physBranch_continuousAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SingleTailRadius.physBranch_continuousAt

/-- info: 'FMSA.Paper.SingleTailRadius.branchCoefficients_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SingleTailRadius.branchCoefficients_eq

/-- info: 'FMSA.Paper.SingleTailRadius.single_tail_radius_eq_fold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SingleTailRadius.single_tail_radius_eq_fold

/-- info: 'FMSA.Paper.SingleTailRadius.single_tail_coefficients_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SingleTailRadius.single_tail_coefficients_nonneg

/-- info: 'FMSA.Paper.SingleTailRadius.foldCoupling_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SingleTailRadius.foldCoupling_pos

/-- info: 'FMSA.Paper.SingleTailRadius.single_tail_branch_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.SingleTailRadius.single_tail_branch_exists
