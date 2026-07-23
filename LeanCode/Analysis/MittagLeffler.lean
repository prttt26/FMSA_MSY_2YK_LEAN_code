/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import LeanCode.Analysis.ContourDeformation
import LeanCode.Analysis.JordanLemma

/-!
# Mittag-Leffler expansion (THEOREM, derived from the contour-deformation axiom)
# + one-pole Fourier kernel (theorem), general-purpose

Group MA (`MATH_AXIOMS.md`), tasks `MA.2`/`MA.3`.

* `mittagLeffler_expansion_of_bounded_on_circles` — the classical Mittag-Leffler expansion
  theorem (Whittaker–Watson §7.4 / Titchmarsh §3.2), **proved** (2026-07-16) from Axiom 1's
  derived finite residue-sum theorem (`circleIntegral_eq_sum_two_pi_I_mul_of_simple_poles`):
  apply it to the pole kernel `f(w)/(w(w-z))` on each circle `‖w‖ = R N` — poles at `0`, `z`, and
  the `pₙ` inside, with per-pole balls shrunk to be mutually disjoint — then the ML inequality
  (`circleIntegral.norm_integral_le_of_norm_le_const`) kills the big-circle integral as `N → ∞`
  (`‖kernel‖ ~ M/R²` beats circumference `2πR`). `#print axioms` = exactly
  `circleIntegral_eq_sum_of_small_circles` + the standard three.

**History — two same-day statement corrections (2026-07-15/16), both found by proof attempts.**
The first version of this file stated the expansion as an AXIOM with an ordered-partial-sum
conclusion (`Finset.range N` over an abstract enumeration). That conclusion is **stronger than
the classical theorem and false in general**: the classical proof only controls sums grouped by
circle (all poles inside `C_N` at once); a pole pair `p, p+ε` with huge cancelling residues
`±C/ε` placed between consecutive circles keeps `f` bounded on the (adversarially chosen)
circles while an initial segment that splits the pair jumps by `~C/ε`. The corrected statement
below takes a counting function `k : ℕ → ℕ` with `n < k N ↔ ‖pₙ‖ < R N` (which simultaneously
enforces enumeration-by-modulus and per-circle finiteness) and concludes convergence of the
**circle-grouped** partial sums `Finset.range (k N)`. Deriving the corrected statement then
retired the axiom altogether. Same lesson as `JensenCounting.lean`'s literal-zero-set bug:
prove-first finds statement bugs that review and numerics miss.

* `fourier_kernel_one_pole` — genuine theorem (no axiom beyond the half-disk deformation):
  `∫_{-R}^{R} e^{ixr}/(x-k₀) dx → 2πi·e^{ik₀r}` as `R→∞`, for `Im k₀ > 0`, `r > 0`. Proof:
  half-disk residue-sum theorem at the single pole + `jordan_lemma_arc_bound` (amplitude
  `1/(z-k₀)` decays — exactly the case Jordan serves).

Together these give `OZFIX.10`'s decomposed Route B path: expand `Ĥ` via Mittag-Leffler
(`sup‖Ĥ‖` verified constant on the expanding pole-avoiding circles: 1.7453 @η=0.3, 1.1636
@η=0.45; expansion → `Ĥ` pointwise ~1e-7 by N=60), Fourier-invert each `1/(k-kₙ)` termwise, sum.
-/

open Set Metric Complex Filter Topology intervalIntegral

noncomputable section

-- Fixed-radius core: residue identity for the pole kernel f(w)/(w(w-z))
private theorem pole_kernel_circleIntegral {f : ℂ → ℂ} {p : ℕ → ℂ} {r' : ℕ → ℝ}
    {g : ℕ → ℂ → ℂ} {T : ℝ} {κ : ℕ} {z : ℂ}
    (hp0 : ∀ n, p n ≠ 0)
    (hpmono : ∀ n, ‖p n‖ ≤ ‖p (n + 1)‖)
    (hr'pos : ∀ n, 0 < r' n)
    (hdisj : ∀ m n, m ≠ n → Disjoint (closedBall (p m) (r' m)) (closedBall (p n) (r' n)))
    (hgeq : ∀ n, ∀ w ∈ closedBall (p n) (r' n), f w = g n w / (w - p n))
    (hgc : ∀ n, ContinuousOn (g n) (closedBall (p n) (r' n)))
    (hgd : ∀ n, ∀ w ∈ ball (p n) (r' n), DifferentiableAt ℂ (g n) w)
    (hfd : ∀ w : ℂ, (∀ n, w ≠ p n) → DifferentiableAt ℂ f w)
    (hk : ∀ n, n < κ ↔ ‖p n‖ < T)
    (hoff : ∀ n, ‖p n‖ ≠ T)
    (hz0 : z ≠ 0) (hzp : ∀ n, z ≠ p n) (hzT : ‖z‖ < T) :
    (∮ w in C(0, T), f w / (w * (w - z))) =
      2 * (Real.pi : ℂ) * Complex.I *
        ((∑ n ∈ Finset.range κ, g n (p n) / (p n * (p n - z))) + f 0 / (0 - z) + f z / z) := by
  classical
  have hz0' : (0:ℝ) < ‖z‖ := norm_pos_iff.mpr hz0
  have hT : (0:ℝ) < T := lt_trans hz0' hzT
  have hmn : Monotone (fun n => ‖p n‖) := monotone_nat_of_le_succ hpmono
  -- pole-ball radii
  set ρ : ℕ → ℝ := fun n =>
    min (r' n) ((1/3) * min ‖p n‖ (min ‖z - p n‖ (T - ‖p n‖))) with hρdef
  -- z-ball radius (needs the min distance to the enclosed poles)
  set dz : ℝ := if h : (Finset.range κ).Nonempty
    then (Finset.range κ).inf' h (fun n => ‖z - p n‖) else 1 with hdzdef
  set ρz : ℝ := (1/3) * min (min ‖z‖ (T - ‖z‖)) dz with hρzdef
  -- origin-ball radius
  set ρ0 : ℝ := (1/3) * min ‖z‖ (min ‖p 0‖ T) with hρ0def
  -- positivity and elementary bounds
  have hpn_pos : ∀ n, (0:ℝ) < ‖p n‖ := fun n => norm_pos_iff.mpr (hp0 n)
  have hzp_pos : ∀ n, (0:ℝ) < ‖z - p n‖ := fun n => norm_pos_iff.mpr (sub_ne_zero.mpr (hzp n))
  have hTp : ∀ n, n < κ → (0:ℝ) < T - ‖p n‖ := fun n hn => by linarith [(hk n).mp hn]
  have hρpos : ∀ n, n < κ → 0 < ρ n := by
    intro n hn
    rw [hρdef]
    apply lt_min (hr'pos n)
    have h1 := hpn_pos n
    have h2 := hzp_pos n
    have h3 := hTp n hn
    positivity
  have hdz_pos : 0 < dz := by
    rw [hdzdef]
    split
    · next h =>
      rw [Finset.lt_inf'_iff]
      exact fun n _ => hzp_pos n
    · norm_num
  have hdz_le : ∀ n, n < κ → dz ≤ ‖z - p n‖ := by
    intro n hn
    rw [hdzdef]
    have hne : (Finset.range κ).Nonempty := ⟨n, Finset.mem_range.mpr hn⟩
    rw [dif_pos hne]
    exact Finset.inf'_le _ (Finset.mem_range.mpr hn)
  have hρz_pos : 0 < ρz := by
    rw [hρzdef]
    have h1 : (0:ℝ) < T - ‖z‖ := by linarith
    positivity
  have hρ0_pos : 0 < ρ0 := by
    rw [hρ0def]
    have := hpn_pos 0
    positivity
  -- key radius bounds
  have hρ_le_r' : ∀ n, ρ n ≤ r' n := fun n => min_le_left _ _
  have hρ_le : ∀ n, ρ n ≤ (1/3) * min ‖p n‖ (min ‖z - p n‖ (T - ‖p n‖)) :=
    fun n => min_le_right _ _
  have hρ_le_pn : ∀ n, ρ n ≤ ‖p n‖ / 3 := by
    intro n
    have h := hρ_le n
    have h2 : min ‖p n‖ (min ‖z - p n‖ (T - ‖p n‖)) ≤ ‖p n‖ := min_le_left _ _
    nlinarith
  have hρ_le_zp : ∀ n, ρ n ≤ ‖z - p n‖ / 3 := by
    intro n
    have h := hρ_le n
    have h2 : min ‖p n‖ (min ‖z - p n‖ (T - ‖p n‖)) ≤ ‖z - p n‖ :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    nlinarith
  have hρ_le_T : ∀ n, ρ n ≤ (T - ‖p n‖) / 3 := by
    intro n
    have h := hρ_le n
    have h2 : min ‖p n‖ (min ‖z - p n‖ (T - ‖p n‖)) ≤ T - ‖p n‖ :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    nlinarith
  have hρz_le_z : ρz ≤ ‖z‖ / 3 := by
    rw [hρzdef]
    have h2 : min (min ‖z‖ (T - ‖z‖)) dz ≤ ‖z‖ := le_trans (min_le_left _ _) (min_le_left _ _)
    nlinarith
  have hρz_le_T : ρz ≤ (T - ‖z‖) / 3 := by
    rw [hρzdef]
    have h2 : min (min ‖z‖ (T - ‖z‖)) dz ≤ T - ‖z‖ :=
      le_trans (min_le_left _ _) (min_le_right _ _)
    nlinarith
  have hρz_le_dz : ρz ≤ dz / 3 := by
    rw [hρzdef]
    have h2 : min (min ‖z‖ (T - ‖z‖)) dz ≤ dz := min_le_right _ _
    nlinarith
  have hρ0_le_z : ρ0 ≤ ‖z‖ / 3 := by
    rw [hρ0def]
    have h2 : min ‖z‖ (min ‖p 0‖ T) ≤ ‖z‖ := min_le_left _ _
    nlinarith
  have hρ0_le_p0 : ρ0 ≤ ‖p 0‖ / 3 := by
    rw [hρ0def]
    have h2 : min ‖z‖ (min ‖p 0‖ T) ≤ ‖p 0‖ := le_trans (min_le_right _ _) (min_le_left _ _)
    nlinarith
  have hρ0_le_T : ρ0 ≤ T / 3 := by
    rw [hρ0def]
    have h2 : min ‖z‖ (min ‖p 0‖ T) ≤ T := le_trans (min_le_right _ _) (min_le_right _ _)
    nlinarith
  have hρ0_le_pn : ∀ n, ρ0 ≤ ‖p n‖ / 3 := by
    intro n
    have := hmn (Nat.zero_le n)
    simp only at this
    linarith [hρ0_le_p0]
  -- far poles (n ≥ κ) are strictly outside the big circle
  have hfar : ∀ n, ¬ n < κ → T < ‖p n‖ := by
    intro n hn
    have h1 : ¬ ‖p n‖ < T := fun h => hn ((hk n).mpr h)
    have h2 := hoff n
    push_neg at h1
    exact lt_of_le_of_ne h1 (Ne.symm h2)
  -- avoidance facts on the pole balls
  have hpole_ne0 : ∀ n, n < κ → ∀ w ∈ closedBall (p n) (ρ n), w ≠ 0 := by
    intro n hn w hw h0
    rw [mem_closedBall, h0, dist_zero_left] at hw
    linarith [hρ_le_pn n, hpn_pos n]
  have hpole_nez : ∀ n, n < κ → ∀ w ∈ closedBall (p n) (ρ n), w ≠ z := by
    intro n hn w hw hwz
    rw [mem_closedBall, hwz, dist_eq_norm] at hw
    linarith [hρ_le_zp n, hzp_pos n]
  -- avoidance facts on the origin ball
  have h0ball_nez : ∀ w ∈ closedBall (0:ℂ) ρ0, w ≠ z := by
    intro w hw hwz
    rw [mem_closedBall, hwz, dist_zero_right] at hw
    linarith [hρ0_le_z, hz0']
  have h0ball_nep : ∀ w ∈ closedBall (0:ℂ) ρ0, ∀ n, w ≠ p n := by
    intro w hw n hwp
    rw [mem_closedBall, hwp, dist_zero_right] at hw
    linarith [hρ0_le_pn n, hpn_pos n]
  -- avoidance facts on the z ball
  have hzball_ne0 : ∀ w ∈ closedBall z ρz, w ≠ 0 := by
    intro w hw h0
    rw [mem_closedBall, h0, dist_zero_left] at hw
    linarith [hρz_le_z, hz0']
  have hzball_norm : ∀ w ∈ closedBall z ρz, ‖w‖ < T := by
    intro w hw
    rw [mem_closedBall] at hw
    have h1 : dist w 0 ≤ dist w z + dist z 0 := dist_triangle _ _ _
    rw [dist_zero_right, dist_zero_right] at h1
    linarith [hρz_le_T]
  have hzball_nep : ∀ w ∈ closedBall z ρz, ∀ n, w ≠ p n := by
    intro w hw n hwp
    by_cases hn : n < κ
    · rw [mem_closedBall, hwp, dist_comm, dist_eq_norm] at hw
      linarith [hρz_le_dz, hdz_pos, hdz_le n hn]
    · have h1 := hfar n hn
      have h2 := hzball_norm w hw
      rw [hwp] at h2
      linarith
  -- hole data for the residue-sum theorem
  set c' : Fin κ ⊕ Bool → ℂ := Sum.elim (fun i => p i.val) (fun b => cond b z 0) with hc'def
  set rr : Fin κ ⊕ Bool → ℝ := Sum.elim (fun i => ρ i.val) (fun b => cond b ρz ρ0) with hrrdef
  set gg : Fin κ ⊕ Bool → ℂ → ℂ :=
    Sum.elim (fun i => fun w => g i.val w / (w * (w - z)))
      (fun b => cond b (fun w => f w / w) (fun w => f w / (w - z))) with hggdef
  have hrrpos : ∀ i, 0 < rr i := by
    rintro (i | b)
    · exact hρpos i.val i.isLt
    · cases b
      · exact hρ0_pos
      · exact hρz_pos
  have hinside : ∀ i, closedBall (c' i) (rr i) ⊆ ball (0:ℂ) T := by
    rintro (i | b) w hw
    · simp only [hc'def, hrrdef, Sum.elim_inl, mem_closedBall] at hw
      rw [mem_ball, dist_zero_right]
      have h1 : dist w 0 ≤ dist w (p i.val) + dist (p i.val) 0 := dist_triangle _ _ _
      rw [dist_zero_right, dist_zero_right] at h1
      have h2 := hρ_le_T i.val
      have h3 := hTp i.val i.isLt
      linarith [hw, h1]
    · cases b
      · simp only [hc'def, hrrdef, Sum.elim_inr, Bool.cond_false, mem_closedBall,
          dist_zero_right] at hw
        rw [mem_ball, dist_zero_right]
        linarith [hρ0_le_T]
      · simp only [hc'def, hrrdef, Sum.elim_inr, Bool.cond_true, mem_closedBall] at hw
        rw [mem_ball, dist_zero_right]
        exact hzball_norm w hw
  have hdisjP0 : ∀ n, ρ n + ρ0 < dist (p n) 0 := by
    intro n
    rw [dist_zero_right]
    linarith [hρ_le_pn n, hρ0_le_pn n, hpn_pos n]
  have hdisjPz : ∀ n, n < κ → ρ n + ρz < dist (p n) z := by
    intro n hn
    rw [dist_eq_norm, ← norm_sub_rev]
    linarith [hρ_le_zp n, hρz_le_dz, hdz_le n hn, hzp_pos n]
  have hdisj0z : ρ0 + ρz < dist (0:ℂ) z := by
    rw [dist_zero_left]
    linarith [hρ0_le_z, hρz_le_z, hz0']
  have hdisj' : ∀ i j, i ≠ j → Disjoint (closedBall (c' i) (rr i)) (closedBall (c' j) (rr j)) := by
    rintro (i | bi) (j | bj) hij
    · have hne : i.val ≠ j.val := fun h => hij (congrArg Sum.inl (Fin.val_injective h))
      exact (hdisj i.val j.val hne).mono
        (closedBall_subset_closedBall (hρ_le_r' i.val))
        (closedBall_subset_closedBall (hρ_le_r' j.val))
    · cases bj
      · exact closedBall_disjoint_closedBall (hdisjP0 i.val)
      · exact closedBall_disjoint_closedBall (hdisjPz i.val i.isLt)
    · cases bi
      · exact (closedBall_disjoint_closedBall (hdisjP0 j.val)).symm
      · exact (closedBall_disjoint_closedBall (hdisjPz j.val j.isLt)).symm
    · cases bi <;> cases bj
      · exact absurd rfl hij
      · exact closedBall_disjoint_closedBall hdisj0z
      · exact (closedBall_disjoint_closedBall hdisj0z).symm
      · exact absurd rfl hij
  -- region facts
  have hregion : ∀ w : ℂ, w ∈ closedBall (0:ℂ) T → (∀ i, w ∉ ball (c' i) (rr i)) →
      w ≠ 0 ∧ w ≠ z ∧ ∀ n, w ≠ p n := by
    intro w hwT hwnot
    refine ⟨?_, ?_, ?_⟩
    · intro h0
      exact hwnot (Sum.inr false) (by
        simp only [hc'def, hrrdef, Sum.elim_inr, Bool.cond_false]
        rw [h0]; exact mem_ball_self hρ0_pos)
    · intro hzz
      exact hwnot (Sum.inr true) (by
        simp only [hc'def, hrrdef, Sum.elim_inr, Bool.cond_true]
        rw [hzz]; exact mem_ball_self hρz_pos)
    · intro n hp
      by_cases hn : n < κ
      · exact hwnot (Sum.inl ⟨n, hn⟩) (by
          simp only [hc'def, hrrdef, Sum.elim_inl]
          rw [hp]; exact mem_ball_self (hρpos n hn))
      · rw [mem_closedBall, dist_zero_right] at hwT
        have := hfar n hn
        rw [hp] at hwT
        linarith
  -- apply the residue-sum theorem
  have key := circleIntegral_eq_sum_two_pi_I_mul_of_simple_poles
    (f := fun w => f w / (w * (w - z))) (c := 0) (R := T) hT
    (c' := c') (r' := rr) hrrpos hinside hdisj' (s := ∅) countable_empty
    (by
      -- continuity on the punctured region
      intro w hw
      obtain ⟨hwT, hwnot⟩ := hw
      obtain ⟨hne0, hnez, hnep⟩ := hregion w hwT (by
        intro i hi
        exact hwnot (mem_iUnion.mpr ⟨i, hi⟩))
      have hfw : DifferentiableAt ℂ f w := hfd w hnep
      have hden : w * (w - z) ≠ 0 := mul_ne_zero hne0 (sub_ne_zero.mpr hnez)
      exact (hfw.continuousAt.div (by fun_prop) hden).continuousWithinAt)
    (by
      intro w hw
      obtain ⟨⟨hwT, hwnot⟩, -⟩ := hw
      obtain ⟨hne0, hnez, hnep⟩ := hregion w hwT (by
        intro i hi
        exact hwnot (mem_iUnion.mpr ⟨i, ball_subset_closedBall hi⟩))
      have hfw : DifferentiableAt ℂ f w := hfd w hnep
      have hden : w * (w - z) ≠ 0 := mul_ne_zero hne0 (sub_ne_zero.mpr hnez)
      exact hfw.div (by fun_prop) hden)
    (g := gg)
    (by
      -- local pole representations
      rintro (i | b) w hw
      · simp only [hc'def, hrrdef, hggdef, Sum.elim_inl] at hw ⊢
        rw [hgeq i.val w (closedBall_subset_closedBall (hρ_le_r' i.val) hw)]
        rw [div_right_comm]
      · cases b
        · simp only [hc'def, hggdef, Sum.elim_inr, Bool.cond_false]
          rw [sub_zero, div_div, mul_comm (w - z) w]
        · simp only [hc'def, hggdef, Sum.elim_inr, Bool.cond_true]
          rw [div_div])
    (by
      -- continuity of the local numerators
      rintro (i | b)
      · simp only [hc'def, hrrdef, hggdef, Sum.elim_inl]
        apply ContinuousOn.div
        · exact (hgc i.val).mono (closedBall_subset_closedBall (hρ_le_r' i.val))
        · fun_prop
        · intro w hw
          exact mul_ne_zero (hpole_ne0 i.val i.isLt w hw)
            (sub_ne_zero.mpr (hpole_nez i.val i.isLt w hw))
      · cases b
        · simp only [hc'def, hrrdef, hggdef, Sum.elim_inr, Bool.cond_false]
          apply ContinuousOn.div
          · exact fun w hw => (hfd w (h0ball_nep w hw)).continuousAt.continuousWithinAt
          · fun_prop
          · exact fun w hw => sub_ne_zero.mpr (h0ball_nez w hw)
        · simp only [hc'def, hrrdef, hggdef, Sum.elim_inr, Bool.cond_true]
          apply ContinuousOn.div
          · exact fun w hw => (hfd w (hzball_nep w hw)).continuousAt.continuousWithinAt
          · fun_prop
          · exact fun w hw => hzball_ne0 w hw)
    (by
      -- differentiability of the local numerators
      rintro (i | b) w hw
      · obtain ⟨hw, -⟩ := hw
        simp only [hc'def, hrrdef, hggdef, Sum.elim_inl] at hw ⊢
        apply DifferentiableAt.div
        · exact hgd i.val w (ball_subset_ball (hρ_le_r' i.val) hw)
        · fun_prop
        · exact mul_ne_zero (hpole_ne0 i.val i.isLt w (ball_subset_closedBall hw))
            (sub_ne_zero.mpr (hpole_nez i.val i.isLt w (ball_subset_closedBall hw)))
      · obtain ⟨hw, -⟩ := hw
        cases b
        · simp only [hc'def, hrrdef, hggdef, Sum.elim_inr, Bool.cond_false] at hw ⊢
          apply DifferentiableAt.div
          · exact hfd w (h0ball_nep w (ball_subset_closedBall hw))
          · fun_prop
          · exact sub_ne_zero.mpr (h0ball_nez w (ball_subset_closedBall hw))
        · simp only [hc'def, hrrdef, hggdef, Sum.elim_inr, Bool.cond_true] at hw ⊢
          apply DifferentiableAt.div
          · exact hfd w (hzball_nep w (ball_subset_closedBall hw))
          · fun_prop
          · exact hzball_ne0 w (ball_subset_closedBall hw))
  -- evaluate the sum
  rw [key, Fintype.sum_sum_type]
  have hbool : ∑ b : Bool, 2 * (Real.pi : ℂ) * Complex.I * gg (Sum.inr b) (c' (Sum.inr b)) =
      2 * (Real.pi : ℂ) * Complex.I * (f 0 / (0 - z)) +
        2 * (Real.pi : ℂ) * Complex.I * (f z / z) := by
    rw [Fintype.sum_bool]
    simp only [hc'def, hggdef, Sum.elim_inr, Bool.cond_true, Bool.cond_false]
    ring
  have hfin : ∑ i : Fin κ, 2 * (Real.pi : ℂ) * Complex.I * gg (Sum.inl i) (c' (Sum.inl i)) =
      ∑ n ∈ Finset.range κ,
        2 * (Real.pi : ℂ) * Complex.I * (g n (p n) / (p n * (p n - z))) := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun n => 2 * (Real.pi : ℂ) * Complex.I * (g n (p n) / (p n * (p n - z)))) κ]
    apply Finset.sum_congr rfl
    intro i _
    simp only [hc'def, hggdef, Sum.elim_inl]
  rw [hbool, hfin, ← Finset.mul_sum]
  ring


theorem mittagLeffler_expansion_of_bounded_on_circles {f : ℂ → ℂ} {p : ℕ → ℂ} {r' : ℕ → ℝ}
    {g : ℕ → ℂ → ℂ} {R : ℕ → ℝ} {k : ℕ → ℕ} {M : ℝ}
    (hp0 : ∀ n, p n ≠ 0)
    (hpmono : ∀ n, ‖p n‖ ≤ ‖p (n + 1)‖)
    (hr'pos : ∀ n, 0 < r' n)
    (hdisj : ∀ m n, m ≠ n → Disjoint (closedBall (p m) (r' m)) (closedBall (p n) (r' n)))
    (hgeq : ∀ n, ∀ w ∈ closedBall (p n) (r' n), f w = g n w / (w - p n))
    (hgc : ∀ n, ContinuousOn (g n) (closedBall (p n) (r' n)))
    (hgd : ∀ n, ∀ w ∈ ball (p n) (r' n), DifferentiableAt ℂ (g n) w)
    (hfd : ∀ w : ℂ, (∀ n, w ≠ p n) → DifferentiableAt ℂ f w)
    (hR : Tendsto R atTop atTop)
    (hk : ∀ N n, n < k N ↔ ‖p n‖ < R N)
    (hoff : ∀ N n, ‖p n‖ ≠ R N)
    (hbound : ∀ N, ∀ w : ℂ, ‖w‖ = R N → ‖f w‖ ≤ M)
    {z : ℂ} (hz : ∀ n, z ≠ p n) :
    Tendsto (fun N => ∑ n ∈ Finset.range (k N), g n (p n) * (1 / (z - p n) + 1 / p n)) atTop
      (𝓝 (f z - f 0)) := by
  by_cases hz0 : z = 0
  · subst hz0
    have hzero : ∀ N, ∑ n ∈ Finset.range (k N),
        g n (p n) * (1 / ((0:ℂ) - p n) + 1 / p n) = 0 := by
      intro N
      apply Finset.sum_eq_zero
      intro n _
      have h1 : (1:ℂ) / ((0:ℂ) - p n) + 1 / p n = 0 := by
        rw [zero_sub, one_div, one_div, inv_neg]
        ring
      rw [h1, mul_zero]
    simp only [hzero, sub_self]
    exact tendsto_const_nhds
  · have hz0' : (0:ℝ) < ‖z‖ := norm_pos_iff.mpr hz0
    have hev : ∀ᶠ N in (atTop : Filter ℕ), ‖z‖ < R N := hR.eventually_gt_atTop ‖z‖
    have hM0 : 0 ≤ M := by
      obtain ⟨N, hN⟩ := hev.exists
      have hTN : (0:ℝ) < R N := lt_trans hz0' hN
      have h1 : ‖((R N : ℝ) : ℂ)‖ = R N := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hTN]
      exact le_trans (norm_nonneg _) (hbound N _ h1)
    have h2pi : (2 * (Real.pi:ℂ) * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    -- eventual identity via the fixed-radius residue computation
    have hident : ∀ᶠ N in (atTop : Filter ℕ),
        (∑ n ∈ Finset.range (k N), g n (p n) * (1 / (z - p n) + 1 / p n)) =
          (f z - f 0) - (z / (2 * (Real.pi:ℂ) * Complex.I)) *
            (∮ w in C(0, R N), f w / (w * (w - z))) := by
      filter_upwards [hev] with N hN
      have hkey := pole_kernel_circleIntegral hp0 hpmono hr'pos hdisj hgeq hgc hgd hfd
        (hk N) (hoff N) hz0 hz hN
      have hterm : ∀ n ∈ Finset.range (k N),
          g n (p n) * (1 / (z - p n) + 1 / p n) =
            (-z) * (g n (p n) / (p n * (p n - z))) := by
        intro n _
        have h1 : p n ≠ 0 := hp0 n
        have h2 : z - p n ≠ 0 := sub_ne_zero.mpr (hz n)
        have h3 : p n - z ≠ 0 := sub_ne_zero.mpr (fun h => (hz n) h.symm)
        field_simp
        ring
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hkey]
      have hzC : (z:ℂ) ≠ 0 := hz0
      field_simp
      linear_combination (-(f 0)) * mul_inv_cancel₀ hzC
    -- the circle integral tends to zero
    have harc : Tendsto (fun N => ∮ w in C(0, R N), f w / (w * (w - z))) atTop (𝓝 0) := by
      refine squeeze_zero_norm'
        (f := fun N : ℕ => (∮ w in C(0, R N), f w / (w * (w - z)) : ℂ))
        (a := fun N => 2 * Real.pi * M / (R N - ‖z‖)) ?_ ?_
      · filter_upwards [hev] with N hN
        have hTN : (0:ℝ) < R N := lt_trans hz0' hN
        have hsphere : ∀ w ∈ sphere (0:ℂ) (R N),
            ‖f w / (w * (w - z))‖ ≤ M / (R N * (R N - ‖z‖)) := by
          intro w hw
          rw [mem_sphere, dist_zero_right] at hw
          have hwz : R N - ‖z‖ ≤ ‖w - z‖ := by
            have := norm_sub_norm_le w z
            linarith [hw ▸ this]
          have hwne : (0:ℝ) < ‖w‖ := by rw [hw]; exact hTN
          rw [norm_div, norm_mul, hw]
          apply div_le_div₀ hM0 (hbound N w hw) (by nlinarith) ?_
          have h1 : (0:ℝ) ≤ R N := hTN.le
          nlinarith [hwz]
        have hbnd := circleIntegral.norm_integral_le_of_norm_le_const hTN.le hsphere
        refine le_trans hbnd (le_of_eq ?_)
        field_simp
      · have h1 : Tendsto (fun N => R N - ‖z‖) atTop atTop :=
          tendsto_atTop_add_const_right _ _ hR
        have h2 : Tendsto (fun N => (R N - ‖z‖)⁻¹) atTop (𝓝 0) :=
          tendsto_inv_atTop_zero.comp h1
        have h3 := h2.const_mul (2 * Real.pi * M)
        simpa [div_eq_mul_inv, mul_zero] using h3
    have hlim : Tendsto (fun N => (f z - f 0) - (z / (2 * (Real.pi:ℂ) * Complex.I)) *
        (∮ w in C(0, R N), f w / (w * (w - z)))) atTop (𝓝 (f z - f 0)) := by
      have h1 := harc.const_mul (z / (2 * (Real.pi:ℂ) * Complex.I))
      rw [mul_zero] at h1
      have h2 := Filter.Tendsto.sub
        (tendsto_const_nhds (x := f z - f 0) (f := (atTop : Filter ℕ))) h1
      simpa using h2
    exact Filter.Tendsto.congr'
      (Filter.EventuallyEq.symm (f := fun N => ∑ n ∈ Finset.range (k N),
        g n (p n) * (1 / (z - p n) + 1 / p n)) hident) hlim

/-- Finite-`R` half-disk identity for the one-pole Fourier kernel: `diameter + arc = 2πi·e^{ik₀r}`
once the pole's ball fits inside the upper half-disk. Instantiates
`halfDiskBoundary_eq_sum_two_pi_I_mul_of_simple_poles` at the single pole `k₀` with
`g z = e^{izr}`. -/
private theorem fourier_kernel_halfdisk {k0 : ℂ} (hk0 : 0 < k0.im) {r : ℝ} {R : ℝ}
    (hR : ‖k0‖ + k0.im / 2 < R) :
    ((∫ x in (-R)..R, Complex.exp (Complex.I * x * r) / ((x : ℂ) - k0)) +
        ∫ θ in (0:ℝ)..Real.pi,
          (Complex.I * (R:ℂ) * Complex.exp (θ * Complex.I)) •
            (Complex.exp (Complex.I * ((R:ℂ) * Complex.exp (θ * Complex.I)) * r) /
              ((R:ℂ) * Complex.exp (θ * Complex.I) - k0))) =
      2 * (Real.pi : ℂ) * Complex.I * Complex.exp (Complex.I * k0 * r) := by
  have hnn : (0:ℝ) ≤ ‖k0‖ := norm_nonneg k0
  have hRpos : 0 < R := by linarith [hk0]
  set rr : ℝ := k0.im / 2 with hrrdef
  have hrrpos : 0 < rr := by rw [hrrdef]; positivity
  have key := halfDiskBoundary_eq_sum_two_pi_I_mul_of_simple_poles
    (f := fun z => Complex.exp (Complex.I * z * r) / (z - k0)) (R := R) hRpos
    (ι := Fin 1) (c' := fun _ => k0) (r' := fun _ => rr)
    (fun _ => hrrpos)
    (by
      intro i z hz
      rw [mem_closedBall, dist_eq_norm] at hz
      constructor
      · calc ‖z‖ = ‖k0 + (z - k0)‖ := by ring_nf
          _ ≤ ‖k0‖ + ‖z - k0‖ := norm_add_le _ _
          _ ≤ ‖k0‖ + rr := by linarith
          _ < R := hR
      · have him : |(z - k0).im| ≤ ‖z - k0‖ := Complex.abs_im_le_norm _
        have h1 : (z - k0).im = z.im - k0.im := by simp [Complex.sub_im]
        have h2 : -rr ≤ z.im - k0.im := by
          rw [← h1]; linarith [neg_abs_le (z - k0).im, him, hz]
        have h3 : k0.im - rr ≤ z.im := by linarith
        have hhalf : k0.im - rr = k0.im / 2 := by rw [hrrdef]; ring
        linarith [hk0, hhalf ▸ h3]
    )
    (fun i j hij => absurd (Subsingleton.elim i j) hij)
    (s := ∅) countable_empty
    (by
      intro z hz
      obtain ⟨_, hznotin⟩ := hz
      have hzne : z ≠ k0 := by
        intro heq
        apply hznotin
        rw [heq]
        exact mem_iUnion.mpr ⟨0, mem_ball_self hrrpos⟩
      have hsubne : z - k0 ≠ 0 := sub_ne_zero.mpr hzne
      apply ContinuousWithinAt.div
      · exact (Complex.continuous_exp.comp (by fun_prop)).continuousWithinAt
      · fun_prop
      · exact hsubne
    )
    (by
      intro z hz
      obtain ⟨⟨_, hznotin⟩, _⟩ := hz
      have hzne : z ≠ k0 := by
        intro heq
        apply hznotin
        rw [heq]
        exact mem_iUnion.mpr ⟨0, mem_closedBall_self hrrpos.le⟩
      have hsubne : z - k0 ≠ 0 := sub_ne_zero.mpr hzne
      apply DifferentiableAt.div
      · exact Complex.differentiable_exp.differentiableAt.comp z (by fun_prop)
      · fun_prop
      · exact hsubne
    )
    (g := fun _ z => Complex.exp (Complex.I * z * r))
    (fun i z _ => rfl)
    (fun i => (Complex.continuous_exp.comp (by fun_prop)).continuousOn)
    (fun i z _ => Complex.differentiable_exp.differentiableAt.comp z (by fun_prop))
  rw [key]
  simp

/-- Arc bound for the one-pole kernel via `jordan_lemma_arc_bound`: the amplitude `1/(z-k₀)`
satisfies Jordan's decaying bound `M(R) = 1/(R-‖k₀‖)`, giving `‖arc‖ ≤ π/(r·(R-‖k₀‖))`. -/
private theorem fourier_kernel_arc_bound {k0 : ℂ} (hk0 : 0 < k0.im) {r : ℝ} (hr : 0 < r) {R : ℝ}
    (hR : ‖k0‖ + k0.im / 2 < R) :
    ‖∫ θ in (0:ℝ)..Real.pi,
        (Complex.I * (R:ℂ) * Complex.exp (θ * Complex.I)) •
          (Complex.exp (Complex.I * ((R:ℂ) * Complex.exp (θ * Complex.I)) * r) /
            ((R:ℂ) * Complex.exp (θ * Complex.I) - k0))‖ ≤
      Real.pi * (1 / (R - ‖k0‖)) / r := by
  have hnn : (0:ℝ) ≤ ‖k0‖ := norm_nonneg k0
  have hRpos : 0 < R := by linarith [hk0]
  have hRk0 : ‖k0‖ < R := by linarith [hk0]
  have hMpos : 0 < 1 / (R - ‖k0‖) := by
    apply div_pos one_pos; linarith
  have hcong : (∫ θ in (0:ℝ)..Real.pi,
      (Complex.I * (R:ℂ) * Complex.exp (θ * Complex.I)) •
        (Complex.exp (Complex.I * ((R:ℂ) * Complex.exp (θ * Complex.I)) * r) /
          ((R:ℂ) * Complex.exp (θ * Complex.I) - k0))) =
      ∫ θ in (0:ℝ)..Real.pi,
        (fun z => 1 / (z - k0)) ((R:ℂ) * Complex.exp (θ * Complex.I)) *
          Complex.exp (Complex.I * (r:ℂ) * (R:ℂ) * Complex.exp (θ * Complex.I)) *
          (Complex.I * (R:ℂ) * Complex.exp (θ * Complex.I)) := by
    congr 1
    funext θ
    simp only [smul_eq_mul]
    rw [show Complex.I * ((R:ℂ) * Complex.exp (θ * Complex.I)) * r =
        Complex.I * (r:ℂ) * (R:ℂ) * Complex.exp (θ * Complex.I) by ring]
    ring
  rw [hcong]
  refine jordan_lemma_arc_bound (g := fun z => 1 / (z - k0)) (a := r)
    (M := 1 / (R - ‖k0‖)) hRpos hr hMpos.le ?_ ?_
  · intro z hz
    obtain ⟨hznorm, _⟩ := hz
    have hzne : z - k0 ≠ 0 := by
      apply sub_ne_zero.mpr
      intro heq
      rw [heq] at hznorm
      linarith [hznorm ▸ hRk0]
    exact (continuousWithinAt_const.div (by fun_prop) hzne)
  · intro z hznorm hzim
    have hlow : R - ‖k0‖ ≤ ‖z - k0‖ := by
      have := norm_sub_norm_le z k0
      linarith [hznorm ▸ this]
    rw [norm_div, norm_one]
    apply div_le_div_of_nonneg_left one_pos.le (by linarith) hlow

/-- **One-pole Fourier kernel** (Task `MA.3`, genuine theorem, no new axiom beyond the half-disk
deformation): for `Im k₀ > 0` and `r > 0`,
`∫_{-R}^{R} e^{ixr}/(x-k₀) dx → 2πi·e^{ik₀r}` as `R → ∞`. The elementary building block for
Fourier-inverting a Mittag-Leffler pole expansion termwise. -/
theorem fourier_kernel_one_pole {k0 : ℂ} (hk0 : 0 < k0.im) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun R : ℝ => ∫ x in (-R)..R, Complex.exp (Complex.I * x * r) / ((x : ℂ) - k0))
      atTop (𝓝 (2 * (Real.pi : ℂ) * Complex.I * Complex.exp (Complex.I * k0 * r))) := by
  set C : ℂ := 2 * (Real.pi : ℂ) * Complex.I * Complex.exp (Complex.I * k0 * r) with hCdef
  set arc : ℝ → ℂ := fun R => ∫ θ in (0:ℝ)..Real.pi,
    (Complex.I * (R:ℂ) * Complex.exp (θ * Complex.I)) •
      (Complex.exp (Complex.I * ((R:ℂ) * Complex.exp (θ * Complex.I)) * r) /
        ((R:ℂ) * Complex.exp (θ * Complex.I) - k0)) with harcdef
  have hev : ∀ᶠ R in (atTop : Filter ℝ), ‖k0‖ + k0.im / 2 < R := eventually_gt_atTop _
  have hbound0 : Tendsto (fun R : ℝ => Real.pi * (1 / (R - ‖k0‖)) / r) atTop (𝓝 0) := by
    have h1 : Tendsto (fun R : ℝ => R - ‖k0‖) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_id
    have h2 : Tendsto (fun R : ℝ => (R - ‖k0‖)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp h1
    have h3 : Tendsto (fun R : ℝ => Real.pi * (R - ‖k0‖)⁻¹ / r) atTop (𝓝 (Real.pi * 0 / r)) :=
      (h2.const_mul Real.pi).div_const r
    simpa [one_div] using h3
  have harc0 : Tendsto arc atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hbound0
    filter_upwards [hev] with R hR
    exact fourier_kernel_arc_bound hk0 hr hR
  have heq : (fun R : ℝ => ∫ x in (-R)..R, Complex.exp (Complex.I * x * r) / ((x : ℂ) - k0))
      =ᶠ[atTop] fun R => C - arc R := by
    filter_upwards [hev] with R hR
    have := fourier_kernel_halfdisk hk0 (r := r) hR
    rw [harcdef, hCdef]
    linear_combination this
  have hlim : Tendsto (fun R : ℝ => C - arc R) atTop (𝓝 (C - 0)) :=
    tendsto_const_nhds.sub harc0
  rw [sub_zero] at hlim
  exact Filter.Tendsto.congr' heq.symm hlim

end
