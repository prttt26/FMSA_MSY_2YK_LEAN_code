import LeanCode.YukawaOZMix.MSAMultiTailMixtureBasis
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! A continuous right extension of the actual Baxter factor. It retains the
physical lower-edge value instead of imposing a false zero boundary value.
Its global Lipschitz bound permits spatial differentiation of correlations. -/
noncomputable section
open MeasureTheory Real Set Filter Topology
open FMSA.ExactMSA.Breakpoint MSAMixture
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

def clippedExp (z a x : ℝ) : ℝ := exp (-z * (max x a - a))

theorem clippedExp_lipschitz (z a : ℝ) (hz : 0 ≤ z) :
    LipschitzWith (Real.nnabs z) (clippedExp z a) := by
  have hder : ∀ x : ℝ, HasDerivAt (fun t => exp (-z*(t-a)))
      (-z * exp (-z*(x-a))) x := by
    intro x
    convert! (((hasDerivAt_id x).sub_const a).const_mul (-z)).exp using 1 <;> simp only [id_eq] <;> ring
  have hl : LipschitzOnWith (Real.nnabs z) (fun t => exp (-z*(t-a))) (Ici a) := by
    apply (convex_Ici a).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun x _ => (hder x).hasDerivWithinAt)
    intro x hx
    change a ≤ x at hx
    have he : exp (-z*(x-a)) ≤ 1 := exp_le_one_iff.mpr (by nlinarith [hx])
    have hp := exp_pos (-z*(x-a))
    change |-z * exp (-z*(x-a))| ≤ |z|
    rw [abs_mul, abs_neg, abs_of_nonneg hp.le]
    nlinarith [abs_nonneg z]
  apply LipschitzWith.of_dist_le_mul
  intro x y
  calc
    dist (clippedExp z a x) (clippedExp z a y) ≤ |z| * dist (max x a) (max y a) :=
      hl.dist_le_mul _ (le_max_right x a) _ (le_max_right y a)
    _ ≤ |z| * dist x y := by
      gcongr
      simpa using (LipschitzWith.id.max_const a).dist_le_mul x y

theorem clippedExp_bound (z a x : ℝ) (hz : 0 ≤ z) : |clippedExp z a x| ≤ 1 := by
  rw [clippedExp, abs_of_pos (exp_pos _)]
  apply exp_le_one_iff.mpr
  nlinarith [le_max_right x a]

def clippedPolynomial (a b qp A x : ℝ) : ℝ :=
  qp * (min (max x a) b - b) + A/2 * (min (max x a) b - b)^2

theorem clippedPolynomial_lipschitz (a b qp A : ℝ) (hab : a ≤ b) :
    LipschitzWith (Real.nnabs qp + Real.nnabs A * Real.nnabs (b-a))
      (clippedPolynomial a b qp A) := by
  have hder : ∀ x : ℝ, HasDerivAt (fun t => qp*(t-b)+A/2*(t-b)^2)
      (qp+A*(x-b)) x := by
    intro x
    convert! (((hasDerivAt_id x).sub_const b).const_mul qp).add
      ((((hasDerivAt_id x).sub_const b).pow 2).const_mul (A/2)) using 1 <;> simp only [id_eq] <;> ring
  have hl : LipschitzOnWith (Real.nnabs qp + Real.nnabs A * Real.nnabs (b-a))
      (fun t => qp*(t-b)+A/2*(t-b)^2) (Icc a b) := by
    apply (convex_Icc a b).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun x _ => (hder x).hasDerivWithinAt)
    intro x hx
    have hb : |x-b| ≤ |b-a| := by
      rw [abs_of_nonpos (by linarith [hx.2]), abs_of_nonneg (sub_nonneg.mpr hab)]
      linarith [hx.1]
    change |qp+A*(x-b)| ≤ |qp| + |A| * |b-a|
    exact (abs_add_le _ _).trans (by rw [abs_mul]; gcongr)
  have hm : ∀ x : ℝ, min (max x a) b ∈ Icc a b := fun x =>
    ⟨le_min (le_max_right x a) hab, min_le_right _ _⟩
  apply LipschitzWith.of_dist_le_mul
  intro x y
  exact (hl.dist_le_mul _ (hm x) _ (hm y)).trans (by
    gcongr
    simpa using ((LipschitzWith.id.max_const a).min_const b).dist_le_mul x y)

def qRight (z : ι → ℝ) (σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ)
    (W C : TailMatrix ι N) (i j : Fin N) (x : ℝ) : ℝ :=
  clippedPolynomial (edgeLo σ i j) (edgeHi σ i j) (qp i j) (A j) x +
    ∑ u, (W u i j * clippedExp (z u) (edgeLo σ i j) x +
      C u i j * clippedExp (z u) (edgeHi σ i j) x)

theorem qRight_eq_q (z : ι → ℝ) (σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ)
    (W C : TailMatrix ι N) (i j : Fin N) (x : ℝ) (hx : edgeLo σ i j ≤ x) :
    qRight z σ A qp W C i j x = q z σ A qp W C i j x := by
  unfold qRight clippedPolynomial clippedExp q
  rw [if_neg (not_lt.mpr hx)]
  by_cases hr : x ≤ edgeHi σ i j
  · simp [hr, max_eq_left hx, min_eq_left hr, max_eq_right hr]
  · simp [hr, max_eq_left hx, min_eq_right (not_le.mp hr).le,
      max_eq_left (not_le.mp hr).le]

theorem lipschitz_real_mul_const {f : ℝ → ℝ} {L : NNReal}
    (hf : LipschitzWith L f) (c : ℝ) : LipschitzWith (Real.nnabs c * L) (fun x => c*f x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq, ← mul_sub, abs_mul, NNReal.coe_mul, Real.coe_nnabs]
  simpa only [Real.dist_eq, mul_assoc] using
    mul_le_mul_of_nonneg_left (hf.dist_le_mul x y) (abs_nonneg c)

theorem lipschitz_real_finite_sum {κ : Type*} (s : Finset κ) (f : κ → ℝ → ℝ)
    (L : κ → NNReal) (h : ∀ u ∈ s, LipschitzWith (L u) (f u)) :
    LipschitzWith (∑ u ∈ s, L u) (fun x => ∑ u ∈ s, f u x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (LipschitzWith.const (0 : ℝ))
  | @insert u s hu ih =>
    simpa only [Finset.sum_insert hu] using
      (h u (Finset.mem_insert_self u s)).add
        (ih (fun v hv => h v (Finset.mem_insert_of_mem hv)))

/-- Actual right extension is globally Lipschitz for arbitrary real
amplitudes, internally supplying the spatial domination constant. -/
theorem qRight_lipschitz (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N)
    (hσ : ∀ i, 0 ≤ σ i) (i j : Fin N) :
    ∃ L : NNReal, LipschitzWith L (qRight z σ A qp W C i j) := by
  have he : edgeLo σ i j ≤ edgeHi σ i j := by unfold edgeLo edgeHi; linarith [hσ i]
  have hp := clippedPolynomial_lipschitz (edgeLo σ i j) (edgeHi σ i j) (qp i j) (A j) he
  have ht := lipschitz_real_finite_sum Finset.univ
    (fun u x => W u i j * clippedExp (z u) (edgeLo σ i j) x +
      C u i j * clippedExp (z u) (edgeHi σ i j) x)
    (fun u => Real.nnabs (W u i j) * Real.nnabs (z u) +
      Real.nnabs (C u i j) * Real.nnabs (z u)) (fun u _ =>
        (lipschitz_real_mul_const (clippedExp_lipschitz (z u) (edgeLo σ i j) (hz u).le) _).add
          (lipschitz_real_mul_const (clippedExp_lipschitz (z u) (edgeHi σ i j) (hz u).le) _))
  exact ⟨_, hp.add ht⟩

theorem qRight_bounded (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N)
    (hσ : ∀ i, 0 ≤ σ i) (i j : Fin N) :
    ∃ M : ℝ, ∀ x, |qRight z σ A qp W C i j x| ≤ M := by
  refine ⟨|qp i j| * σ i + |A j|/2*(σ i)^2 + ∑ u, (|W u i j|+|C u i j|), ?_⟩
  intro x
  have he : edgeHi σ i j - edgeLo σ i j = σ i := by unfold edgeHi edgeLo; ring
  have hlo : edgeLo σ i j ≤ min (max x (edgeLo σ i j)) (edgeHi σ i j) :=
    le_min (le_max_right _ _) (by linarith [hσ i])
  have hhi := min_le_right (max x (edgeLo σ i j)) (edgeHi σ i j)
  have hb : |min (max x (edgeLo σ i j)) (edgeHi σ i j) - edgeHi σ i j| ≤ σ i := by
    rw [abs_of_nonpos (sub_nonpos.mpr hhi)]
    linarith
  have hp : |clippedPolynomial (edgeLo σ i j) (edgeHi σ i j) (qp i j) (A j) x| ≤
      |qp i j| * σ i + |A j|/2*(σ i)^2 := by
    unfold clippedPolynomial
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_div, abs_of_pos (by norm_num : (0 : ℝ)<2), abs_pow]
    gcongr
  have ht : ∀ u, |W u i j * clippedExp (z u) (edgeLo σ i j) x +
      C u i j * clippedExp (z u) (edgeHi σ i j) x| ≤ |W u i j|+|C u i j| := by
    intro u
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have hL := clippedExp_bound (z u) (edgeLo σ i j) x (hz u).le
    have hR := clippedExp_bound (z u) (edgeHi σ i j) x (hz u).le
    nlinarith [abs_nonneg (W u i j), abs_nonneg (C u i j)]
  exact (abs_add_le _ _).trans (add_le_add hp
    ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun u _ => ht u))))

/-- The extension changes no actual ordered positive-r convolution. -/
theorem qRight_product_eq_of_order (z : ι → ℝ) (σ A : Fin N → ℝ)
    (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N) (i j l : Fin N)
    (horder : σ j ≤ σ i) (r : ℝ) (hr : 0 < r) (t : ℝ) :
    qRight z σ A qp W C i l (t+r) * q z σ A qp W C j l t =
      q z σ A qp W C i l (t+r) * q z σ A qp W C j l t := by
  by_cases ht : t < edgeLo σ j l
  · simp [q, ht]
  · rw [qRight_eq_q]
    have htl := not_lt.mp ht
    unfold edgeLo at htl ⊢
    linarith

theorem q_hasDerivAt_off_edges (z : ι → ℝ) (σ A : Fin N → ℝ)
    (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N)
    (hσ : ∀ i, 0 ≤ σ i) (i j : Fin N) (x : ℝ)
    (hxL : x ≠ edgeLo σ i j) (hxR : x ≠ edgeHi σ i j) :
    HasDerivAt (q z σ A qp W C i j) (qPrime z σ A qp W C i j x) x := by
  have he : edgeLo σ i j ≤ edgeHi σ i j := by unfold edgeLo edgeHi; linarith [hσ i]
  have hd : ∀ u a, HasDerivAt (fun t : ℝ => exp (-z u*(t-a)))
      (-z u*exp (-z u*(x-a))) x := by
    intro u a
    convert! (((hasDerivAt_id x).sub_const a).const_mul (-z u)).exp using 1 <;>
      simp only [id_eq] <;> ring
  by_cases hx : x < edgeLo σ i j
  · have h := hasDerivAt_const x (0 : ℝ)
    rw [qPrime, if_pos hx]
    apply h.congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hx] with t ht
    simp [q, ht]
  · have hxlo : edgeLo σ i j < x := lt_of_le_of_ne (not_lt.mp hx) hxL.symm
    by_cases hxr : x < edgeHi σ i j
    · have h := ((((hasDerivAt_id x).sub_const (edgeHi σ i j)).const_mul (qp i j)).add
        (((((hasDerivAt_id x).sub_const (edgeHi σ i j)).pow 2).const_mul (A j/2)))).add
          (HasDerivAt.fun_sum (u := Finset.univ) (fun u _ =>
            ((hd u (edgeLo σ i j)).const_mul (W u i j)).add_const (C u i j)))
      have hdq : HasDerivAt (fun t => qp i j*(t-edgeHi σ i j)+A j/2*(t-edgeHi σ i j)^2+
          ∑ u, (W u i j*exp (-z u*(t-edgeLo σ i j))+C u i j))
          (qPrime z σ A qp W C i j x) x := by
        convert! h using 1
        simp only [qPrime, if_neg hx, if_pos hxr.le, id_eq, Finset.sum_neg_distrib,
          ← Finset.mul_sum]
        have hs : (∑ u, W u i j * (-z u * exp (-z u*(x-edgeLo σ i j)))) =
            -(∑ u, z u*W u i j*exp (-z u*(x-edgeLo σ i j))) := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro u _
          ring
        rw [hs]
        ring
      apply hdq.congr_of_eventuallyEq
      filter_upwards [eventually_gt_nhds hxlo, eventually_lt_nhds hxr] with t htL htR
      simp [q, not_lt.mpr htL.le, htR.le]
    · have hxhi : edgeHi σ i j < x := lt_of_le_of_ne (not_lt.mp hxr) hxR.symm
      have h := HasDerivAt.fun_sum (u := Finset.univ) (fun u _ =>
        ((hd u (edgeLo σ i j)).const_mul (W u i j)).add
          ((hd u (edgeHi σ i j)).const_mul (C u i j)))
      have hdq : HasDerivAt (fun t => ∑ u, (W u i j*exp (-z u*(t-edgeLo σ i j))+
          C u i j*exp (-z u*(t-edgeHi σ i j)))) (qPrime z σ A qp W C i j x) x := by
        convert! h using 1
        simp only [qPrime, if_neg hx, if_neg (not_le.mpr hxhi)]
        apply Finset.sum_congr rfl
        intro u _
        ring
      apply hdq.congr_of_eventuallyEq
      filter_upwards [eventually_gt_nhds hxhi] with t ht
      simp [q, not_lt.mpr (he.trans ht.le), not_le.mpr ht]

theorem qRight_hasDerivAt_off_edges (z : ι → ℝ) (σ A : Fin N → ℝ)
    (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N)
    (hσ : ∀ i, 0 ≤ σ i) (i j : Fin N) (x : ℝ)
    (hxL : x ≠ edgeLo σ i j) (hxR : x ≠ edgeHi σ i j) :
    HasDerivAt (qRight z σ A qp W C i j) (qPrime z σ A qp W C i j x) x := by
  by_cases hx : x < edgeLo σ i j
  · have he : edgeLo σ i j ≤ edgeHi σ i j := by unfold edgeLo edgeHi; linarith [hσ i]
    have h := hasDerivAt_const x (qRight z σ A qp W C i j (edgeLo σ i j))
    rw [qPrime, if_pos hx]
    apply h.congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hx] with t ht
    simp [qRight, clippedPolynomial, clippedExp, max_eq_right ht.le,
      min_eq_left he, max_eq_right (ht.le.trans he), max_eq_right he]
  · have hxlo : edgeLo σ i j < x := lt_of_le_of_ne (not_lt.mp hx) hxL.symm
    apply (q_hasDerivAt_off_edges z σ A qp W C hσ i j x hxL hxR).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hxlo] with t ht
    exact qRight_eq_q z σ A qp W C i j t ht.le

theorem qRight_product_integrable (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N)
    (hσ : ∀ i, 0 ≤ σ i) (i j l : Fin N) (r : ℝ) :
    Integrable (fun t => qRight z σ A qp W C i l (t+r) * q z σ A qp W C j l t) := by
  obtain ⟨M, hb⟩ := qRight_bounded z hz σ A qp W C hσ i l
  obtain ⟨L, hl⟩ := qRight_lipschitz z hz σ A qp W C hσ i l
  have hm : AEStronglyMeasurable (fun t => qRight z σ A qp W C i l (t+r)) :=
    (hl.continuous.comp (continuous_id.add continuous_const)).aestronglyMeasurable
  exact (q_integrable z hz σ A qp W C hσ j l).bdd_mul hm
    (Eventually.of_forall (fun t => by simpa only [Real.norm_eq_abs] using hb (t+r)))

end FMSA.ExactMSA.MultiTailMixture
