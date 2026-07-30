/-
Copyright (c) 2026. All rights reserved.
-/
import LeanCode.HSMixture.MixtureOzStar

/-!
# Matrix OZ★ — integrability side-conditions (`OZFIX.20` discharge)

The matrix 2D reindex `matDblConv_reindex` (and, via `dbl_conv_reindex_two`, its scalar core) is
stated with nine per-species integrability hypotheses.  This file discharges all nine from the
**natural regularity** of the Baxter data — the factors `Q i j` continuous, and `psi` (the entries of
`matBaxterPsi`) measurable with `|psi|` bounded on every `uIcc` — exactly the regularity the scalar
`ozstar_h…` (`BaxterOzStar.lean`) exploit for `q0_poly` (continuous) and `baxterPsi`
(measurable + `uIcc`-bounded).

The generic engine:
* `bddOn_uIcc_of_continuous`, `psiComp_bddOn` — boundedness on compact intervals from continuity;
* `swap_indicator_integrable` — the shared Fubini `(Ioi ·).indicator` engine (factors the three
  product-measure side-conditions), with `swapPM_integrable` / `swapA_integrable` specialising it;
* `constMul_psi_intervalIntegrable` — the slice side-conditions;
* `paramLo_intervalIntegrable` / `paramHi_intervalIntegrable` / `paramKernel_mul_intervalIntegrable`
  — the parametric inner-integral side-conditions.

`matDblConv_reindex_of_regular` assembles them: the matrix reindex conditional only on
`(∀ a b, Continuous (Q a b))`, `Measurable psi`, and `psi`'s `uIcc`-boundedness.
-/

open MeasureTheory Set intervalIntegral Function
namespace FMSA.MixtureOzStar
open FMSA.HardSphere
noncomputable section

/-- Generic: a continuous function is bounded (in abs) on any compact `uIcc a b`. -/
theorem bddOn_uIcc_of_continuous {f : ℝ → ℝ} (hf : Continuous f) (a b : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ s ∈ Set.uIcc a b, |f s| ≤ C := by
  have hcont := hf.abs.continuousOn (s := Set.uIcc a b)
  obtain ⟨x0, _, hx0⟩ := isCompact_uIcc.exists_isMaxOn Set.nonempty_uIcc hcont
  exact ⟨|f x0|, abs_nonneg _, fun s hs => isMaxOn_iff.mp hx0 s hs⟩

/-- Generic: `|psi ∘ h|` is bounded on `uIcc a b` for continuous `h`, from `psi`'s `uIcc`-boundedness. -/
theorem psiComp_bddOn {psi : ℝ → ℝ}
    (hpb : ∀ a b, ∃ C, 0 ≤ C ∧ ∀ s ∈ Set.uIcc a b, |psi s| ≤ C)
    {h : ℝ → ℝ} (hh : Continuous h) (a b : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ s ∈ Set.uIcc a b, |psi (h s)| ≤ C := by
  obtain ⟨M, _, hM⟩ := bddOn_uIcc_of_continuous hh a b
  obtain ⟨C, hC0, hC⟩ := hpb (-M) M
  refine ⟨C, hC0, fun s hs => ?_⟩
  refine hC (h s) ?_
  rw [Set.uIcc_of_le (by have := hM s hs; have := abs_nonneg (h s); linarith), Set.mem_Icc]
  exact ⟨(abs_le.mp (hM s hs)).1, (abs_le.mp (hM s hs)).2⟩

/-- Generic swap-integrability: the `(Ioi ·).indicator` of a measurable, box-bounded kernel is
integrable for the finite product measure.  Factors the three OZ★ Fubini side-conditions. -/
theorem swap_indicator_integrable {G : ℝ → ℝ → ℝ}
    (hG : Measurable (fun p : ℝ × ℝ => G p.1 p.2)) {sigma C : ℝ} (hC0 : 0 ≤ C)
    (hbdd : ∀ p ∈ (Set.Ioc (0 : ℝ) sigma) ×ˢ (Set.Ioc (0 : ℝ) sigma), p.1 < p.2 → |G p.1 p.2| ≤ C) :
    Integrable (Function.uncurry fun u t => (Set.Ioi u).indicator (fun t => G u t) t)
      ((volume.restrict (Set.Ioc 0 sigma)).prod (volume.restrict (Set.Ioc 0 sigma))) := by
  have heq : (Function.uncurry fun u t => (Set.Ioi u).indicator (fun t => G u t) t)
      = {p : ℝ × ℝ | p.1 < p.2}.indicator (fun p => G p.1 p.2) := by
    funext p; simp only [Function.uncurry, Set.indicator_apply, Set.mem_Ioi, Set.mem_setOf_eq]
  rw [heq]
  refine integrable_prod_restrict_of_measurable_bddOn (C := C)
    (hG.indicator (measurableSet_lt measurable_fst measurable_snd)) ?_
  intro p hp
  rw [Set.indicator_apply]
  split_ifs with h
  · exact hbdd p hp h
  · rw [abs_zero]; exact hC0

/-- Generic slice integrability: `c·g(s)·psi(h s)` is interval integrable, `g` continuous,
`psi` measurable + `uIcc`-bounded, `h` continuous. -/
theorem constMul_psi_intervalIntegrable {g psi : ℝ → ℝ} (hg : Continuous g) (hpm : Measurable psi)
    (hpb : ∀ a b, ∃ C, 0 ≤ C ∧ ∀ s ∈ Set.uIcc a b, |psi s| ≤ C) (c : ℝ)
    {h : ℝ → ℝ} (hh : Continuous h) (a b : ℝ) :
    IntervalIntegrable (fun s => c * g s * psi (h s)) volume a b := by
  obtain ⟨Cg, hCg0, hCg⟩ := bddOn_uIcc_of_continuous hg a b
  obtain ⟨Cp, hCp0, hCp⟩ := psiComp_bddOn hpb hh a b
  refine intervalIntegrable_of_aesm_bddOn (C := |c| * Cg * Cp) ?_ ?_
  · exact (((measurable_const.mul hg.measurable).mul (hpm.comp hh.measurable))).aestronglyMeasurable
  · intro x hx
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hCg x hx) (abs_nonneg c)) (hCp x hx)
      (abs_nonneg _) (mul_nonneg (abs_nonneg c) hCg0)

/-- Generic `haddI`-shape: `∫₀^t g1(t)·g2(s)·psi(r+t−s) ds` interval integrable in `t` on `[0,σ]`. -/
theorem paramLo_intervalIntegrable {g1 g2 psi : ℝ → ℝ} (hg1 : Continuous g1) (hg2 : Continuous g2)
    (hpm : Measurable psi) (hpb : ∀ a b, ∃ C, 0 ≤ C ∧ ∀ s ∈ Set.uIcc a b, |psi s| ≤ C)
    {sigma r : ℝ} (hsigma : 0 < sigma) :
    IntervalIntegrable
      (fun t => ∫ s in (0:ℝ)..t, g1 t * g2 s * psi (r + t - s)) volume 0 sigma := by
  obtain ⟨C1, hC10, hC1⟩ := bddOn_uIcc_of_continuous hg1 (-sigma) sigma
  obtain ⟨C2, hC20, hC2⟩ := bddOn_uIcc_of_continuous hg2 (-sigma) sigma
  obtain ⟨Cp, hCp0, hCp⟩ := hpb (r - sigma) (r + sigma)
  have hFmeas : Measurable (fun t => ∫ s in (0:ℝ)..t, g1 t * g2 s * psi (r + t - s)) := by
    refine measurable_intervalIntegral_param (Φ := fun t s => g1 t * g2 s * psi (r + t - s))
      (α := fun _ => 0) (β := fun t => t) ?_ measurable_const measurable_id
    exact ((hg1.measurable.comp measurable_fst).mul (hg2.measurable.comp measurable_snd)).mul
      (hpm.comp (by fun_prop))
  refine intervalIntegrable_of_aesm_bddOn (C := C1 * C2 * Cp * sigma) hFmeas.aestronglyMeasurable ?_
  intro t ht
  rw [Set.uIcc_of_le hsigma.le] at ht
  obtain ⟨ht0, ht1⟩ := ht
  have hb : |∫ s in (0:ℝ)..t, g1 t * g2 s * psi (r + t - s)| ≤ C1 * C2 * Cp * |t - 0| := by
    rw [← Real.norm_eq_abs]
    refine intervalIntegral.norm_integral_le_of_norm_le_const (fun s hs => ?_)
    rw [Set.uIoc_of_le ht0] at hs
    obtain ⟨hs0, hs1⟩ := hs
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul (hC1 t (mem_uIcc_q0 hsigma (by linarith) ht1))
      (hC2 s (mem_uIcc_q0 hsigma (by linarith) (by linarith))) (abs_nonneg _) hC10)
      (hCp (r + t - s) (mem_uIcc_psi hsigma (by linarith) (by linarith)))
      (abs_nonneg _) (mul_nonneg hC10 hC20)
  have hlen : |t - 0| ≤ sigma := by rw [abs_of_nonneg (by linarith)]; linarith
  exact le_trans hb (mul_le_mul_of_nonneg_left hlen (mul_nonneg (mul_nonneg hC10 hC20) hCp0))

/-- Generic `haddII`-shape: `∫_t^σ g1(t)·g2(s)·psi(r+t−s) ds` interval integrable in `t` on `[0,σ]`. -/
theorem paramHi_intervalIntegrable {g1 g2 psi : ℝ → ℝ} (hg1 : Continuous g1) (hg2 : Continuous g2)
    (hpm : Measurable psi) (hpb : ∀ a b, ∃ C, 0 ≤ C ∧ ∀ s ∈ Set.uIcc a b, |psi s| ≤ C)
    {sigma r : ℝ} (hsigma : 0 < sigma) :
    IntervalIntegrable
      (fun t => ∫ s in t..sigma, g1 t * g2 s * psi (r + t - s)) volume 0 sigma := by
  obtain ⟨C1, hC10, hC1⟩ := bddOn_uIcc_of_continuous hg1 (-sigma) sigma
  obtain ⟨C2, hC20, hC2⟩ := bddOn_uIcc_of_continuous hg2 (-sigma) sigma
  obtain ⟨Cp, hCp0, hCp⟩ := hpb (r - sigma) (r + sigma)
  have hFmeas : Measurable (fun t => ∫ s in t..sigma, g1 t * g2 s * psi (r + t - s)) := by
    refine measurable_intervalIntegral_param (Φ := fun t s => g1 t * g2 s * psi (r + t - s))
      (α := fun t => t) (β := fun _ => sigma) ?_ measurable_id measurable_const
    exact ((hg1.measurable.comp measurable_fst).mul (hg2.measurable.comp measurable_snd)).mul
      (hpm.comp (by fun_prop))
  refine intervalIntegrable_of_aesm_bddOn (C := C1 * C2 * Cp * sigma) hFmeas.aestronglyMeasurable ?_
  intro t ht
  rw [Set.uIcc_of_le hsigma.le] at ht
  obtain ⟨ht0, ht1⟩ := ht
  have hb : |∫ s in t..sigma, g1 t * g2 s * psi (r + t - s)| ≤ C1 * C2 * Cp * |sigma - t| := by
    rw [← Real.norm_eq_abs]
    refine intervalIntegral.norm_integral_le_of_norm_le_const (fun s hs => ?_)
    rw [Set.uIoc_of_le ht1] at hs
    obtain ⟨hs0, hs1⟩ := hs
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul (hC1 t (mem_uIcc_q0 hsigma (by linarith) ht1))
      (hC2 s (mem_uIcc_q0 hsigma (by linarith) (by linarith))) (abs_nonneg _) hC10)
      (hCp (r + t - s) (mem_uIcc_psi hsigma (by linarith) (by linarith)))
      (abs_nonneg _) (mul_nonneg hC10 hC20)
  have hlen : |sigma - t| ≤ sigma := by rw [abs_of_nonneg (by linarith)]; linarith
  exact le_trans hb (mul_le_mul_of_nonneg_left hlen (mul_nonneg (mul_nonneg hC10 hC20) hCp0))

/-- Generic `haddR`-shape: `(∫_u^σ g1(t)·g2(t−u) dt)·psi(w u)` interval integrable in `u` on `[0,σ]`,
for continuous `w`. -/
theorem paramKernel_mul_intervalIntegrable {g1 g2 psi : ℝ → ℝ} (hg1 : Continuous g1)
    (hg2 : Continuous g2) (hpm : Measurable psi)
    (hpb : ∀ a b, ∃ C, 0 ≤ C ∧ ∀ s ∈ Set.uIcc a b, |psi s| ≤ C)
    {sigma : ℝ} (hsigma : 0 < sigma) {w : ℝ → ℝ} (hw : Continuous w) :
    IntervalIntegrable
      (fun u => (∫ t in u..sigma, g1 t * g2 (t - u)) * psi (w u)) volume 0 sigma := by
  obtain ⟨C1, hC10, hC1⟩ := bddOn_uIcc_of_continuous hg1 (-sigma) sigma
  obtain ⟨C2, hC20, hC2⟩ := bddOn_uIcc_of_continuous hg2 (-sigma) sigma
  obtain ⟨Cp, hCp0, hCp⟩ := psiComp_bddOn hpb hw 0 sigma
  have hKmeas : Measurable (fun u => ∫ t in u..sigma, g1 t * g2 (t - u)) := by
    refine measurable_intervalIntegral_param (Φ := fun u t => g1 t * g2 (t - u))
      (α := fun u => u) (β := fun _ => sigma) ?_ measurable_id measurable_const
    exact (hg1.measurable.comp measurable_snd).mul
      (hg2.measurable.comp (measurable_snd.sub measurable_fst))
  refine intervalIntegrable_of_aesm_bddOn (C := C1 * C2 * sigma * Cp)
    (hKmeas.mul (hpm.comp hw.measurable)).aestronglyMeasurable ?_
  intro u hu
  rw [Set.uIcc_of_le hsigma.le] at hu
  obtain ⟨hu0, hu1⟩ := hu
  rw [abs_mul]
  have hK : |∫ t in u..sigma, g1 t * g2 (t - u)| ≤ C1 * C2 * |sigma - u| := by
    rw [← Real.norm_eq_abs]
    refine intervalIntegral.norm_integral_le_of_norm_le_const (fun t ht => ?_)
    rw [Set.uIoc_of_le hu1] at ht
    obtain ⟨ht0, ht1⟩ := ht
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hC1 t (mem_uIcc_q0 hsigma (by linarith) ht1))
      (hC2 (t - u) (mem_uIcc_q0 hsigma (by linarith) (by linarith))) (abs_nonneg _) hC10
  have hlen : |sigma - u| ≤ sigma := by rw [abs_of_nonneg (by linarith)]; linarith
  have hKb : |∫ t in u..sigma, g1 t * g2 (t - u)| ≤ C1 * C2 * sigma :=
    le_trans hK (le_trans (mul_le_mul_of_nonneg_left hlen (mul_nonneg hC10 hC20)) (le_of_eq rfl))
  refine mul_le_mul hKb (hCp u (by rw [Set.uIcc_of_le hsigma.le]; exact ⟨hu0, hu1⟩))
    (abs_nonneg _) (mul_nonneg (mul_nonneg hC10 hC20) hsigma.le)

/-- Generic swap-integrability for the `hswapP`/`hswapM` kernel shape `ga(t)·gb(t−u)·psi(w u)`. -/
theorem swapPM_integrable {ga gb psi : ℝ → ℝ} (hga : Continuous ga) (hgb : Continuous gb)
    (hpm : Measurable psi) (hpb : ∀ a b, ∃ C, 0 ≤ C ∧ ∀ s ∈ Set.uIcc a b, |psi s| ≤ C)
    {sigma : ℝ} (hsigma : 0 < sigma) {w : ℝ → ℝ} (hw : Continuous w) :
    Integrable (Function.uncurry fun u t => (Set.Ioi u).indicator
      (fun t => ga t * gb (t - u) * psi (w u)) t)
      ((volume.restrict (Set.Ioc 0 sigma)).prod (volume.restrict (Set.Ioc 0 sigma))) := by
  obtain ⟨C1, hC10, hC1⟩ := bddOn_uIcc_of_continuous hga (-sigma) sigma
  obtain ⟨C2, hC20, hC2⟩ := bddOn_uIcc_of_continuous hgb (-sigma) sigma
  obtain ⟨Cp, hCp0, hCp⟩ := psiComp_bddOn hpb hw 0 sigma
  refine swap_indicator_integrable (G := fun u t => ga t * gb (t - u) * psi (w u)) ?_
    (mul_nonneg (mul_nonneg hC10 hC20) hCp0) ?_
  · exact ((hga.measurable.comp measurable_snd).mul
      (hgb.measurable.comp (measurable_snd.sub measurable_fst))).mul
      (hpm.comp (hw.measurable.comp measurable_fst))
  · intro p hp hlt
    rw [Set.mem_prod] at hp
    obtain ⟨hp1, hp2⟩ := hp
    rw [Set.mem_Ioc] at hp1 hp2
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul (hC1 p.2 (mem_uIcc_q0 hsigma (by linarith) hp2.2))
      (hC2 (p.2 - p.1) (mem_uIcc_q0 hsigma (by linarith) (by linarith))) (abs_nonneg _) hC10)
      (hCp p.1 (by rw [Set.uIcc_of_le hsigma.le]; exact ⟨hp1.1.le, hp1.2⟩))
      (abs_nonneg _) (mul_nonneg hC10 hC20)

/-- Generic swap-integrability for the `hswapA` kernel shape `ga(t)·gb(s)·psi(r+t−s)`. -/
theorem swapA_integrable {ga gb psi : ℝ → ℝ} (hga : Continuous ga) (hgb : Continuous gb)
    (hpm : Measurable psi) (hpb : ∀ a b, ∃ C, 0 ≤ C ∧ ∀ s ∈ Set.uIcc a b, |psi s| ≤ C)
    {sigma : ℝ} (hsigma : 0 < sigma) (r : ℝ) :
    Integrable (Function.uncurry fun t s => (Set.Ioi t).indicator
      (fun s => ga t * gb s * psi (r + t - s)) s)
      ((volume.restrict (Set.Ioc 0 sigma)).prod (volume.restrict (Set.Ioc 0 sigma))) := by
  obtain ⟨C1, hC10, hC1⟩ := bddOn_uIcc_of_continuous hga (-sigma) sigma
  obtain ⟨C2, hC20, hC2⟩ := bddOn_uIcc_of_continuous hgb (-sigma) sigma
  obtain ⟨Cp, hCp0, hCp⟩ := hpb (r - sigma) (r + sigma)
  refine swap_indicator_integrable (G := fun t s => ga t * gb s * psi (r + t - s)) ?_
    (mul_nonneg (mul_nonneg hC10 hC20) hCp0) ?_
  · exact ((hga.measurable.comp measurable_fst).mul
      (hgb.measurable.comp measurable_snd)).mul (hpm.comp (by fun_prop))
  · intro p hp hlt
    rw [Set.mem_prod] at hp
    obtain ⟨hp1, hp2⟩ := hp
    rw [Set.mem_Ioc] at hp1 hp2
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul (hC1 p.1 (mem_uIcc_q0 hsigma (by linarith) hp1.2))
      (hC2 p.2 (mem_uIcc_q0 hsigma (by linarith) hp2.2)) (abs_nonneg _) hC10)
      (hCp (r + p.1 - p.2) (mem_uIcc_psi hsigma (by linarith) (by linarith)))
      (abs_nonneg _) (mul_nonneg hC10 hC20)

/-- **Matrix 2D reindex from natural regularity (`OZFIX.20` side-conditions discharged).**  All nine
integrability hypotheses of `matDblConv_reindex` follow from the Baxter factors `Q` being continuous
and `psi` being measurable + `uIcc`-bounded (the regularity of `matBaxterPsi`). -/
theorem matDblConv_reindex_of_regular {N : ℕ} (Q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (psi : ℝ → ℝ)
    {sigma : ℝ} (hsigma : 0 < sigma) (r : ℝ) (i j : Fin N)
    (hQ : ∀ a b, Continuous (Q a b)) (hpm : Measurable psi)
    (hpb : ∀ a b, ∃ C, 0 ≤ C ∧ ∀ s ∈ Set.uIcc a b, |psi s| ≤ C) :
    (∑ k, ∫ t in (0:ℝ)..sigma, Q i k t * ∫ s in (0:ℝ)..sigma, Q j k s * psi (r + t - s))
      = ∫ u in (0:ℝ)..sigma,
          (matSelfConv Q sigma u i j * psi (r + u) + matSelfConv Q sigma u j i * psi (r - u)) :=
  matDblConv_reindex Q psi hsigma r i j
    (fun k => swapPM_integrable (hQ i k) (hQ j k) hpm hpb hsigma (by fun_prop : Continuous (fun u => r + u)))
    (fun k => swapPM_integrable (hQ j k) (hQ i k) hpm hpb hsigma (by fun_prop : Continuous (fun u => r - u)))
    (fun k => swapA_integrable (hQ i k) (hQ j k) hpm hpb hsigma r)
    (fun k t => constMul_psi_intervalIntegrable (hQ j k) hpm hpb (Q i k t)
      (by fun_prop : Continuous (fun s => r + t - s)) 0 t)
    (fun k t => constMul_psi_intervalIntegrable (hQ j k) hpm hpb (Q i k t)
      (by fun_prop : Continuous (fun s => r + t - s)) t sigma)
    (fun k => paramLo_intervalIntegrable (hQ i k) (hQ j k) hpm hpb hsigma)
    (fun k => paramHi_intervalIntegrable (hQ i k) (hQ j k) hpm hpb hsigma)
    (fun k => paramKernel_mul_intervalIntegrable (hQ i k) (hQ j k) hpm hpb hsigma
      (by fun_prop : Continuous (fun u => r + u)))
    (fun k => paramKernel_mul_intervalIntegrable (hQ j k) (hQ i k) hpm hpb hsigma
      (by fun_prop : Continuous (fun u => r - u)))

end
end FMSA.MixtureOzStar
