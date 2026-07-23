/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib

/-!
# Shared chord-Newton Banach pole-family machinery

A **map-agnostic** chord-Newton Banach-contraction engine for locating zeros of an analytic
`F : ℂ → ℂ`, plus the single shared hypothesis bundle `ChordPoleFamily F` and its consequence
`zeros_infinite_of_chordPoleFamily : ChordPoleFamily F → {s | F s = 0}.Infinite`.

**Why shared.** Two infinitely-many-complex-zeros problems in this project reduce to the *same*
Banach obligation, differing only in the function `F`:

* **MZERO.5** (mixture) — `F = det(Q̂₀_c)` (`YukawaDCF/MixtureHSZeros.lean`), and
* **POLE.3** (single-component) — `F = G_baxter` (`HardSphere/BaxterPoles.lean`).

Both instantiate `ChordPoleFamily F`; the *single* remaining open task is to construct such a family
(the good-guess asymptotic pole locations + the chord contraction/decay bounds). Because `det(Q̂₀_c)`'s
rank-2 reduction is built from the *same* Baxter auxiliaries (`mAux/nAux(sσⱼ)`) as `G_baxter`, one
future asymptotic-family lemma discharges both — they close together.

**Chord-Newton** (frozen derivative `Fp1 = F′(s₁)`): `chordPhi F Fp1 s := s − F s / Fp1`. Its fixed
points are exactly the zeros of `F` (given `Fp1 ≠ 0`) *unconditionally* — no `Complex.log`, hence no
branch-safety (contrast the log-fixed-point map in `BaxterPoles`).
-/

set_option linter.style.longLine false

open Filter Topology

namespace FMSA.BanachPoleFamily

/-! ### Generic chord-Newton engine -/

/-- **Chord-Newton map** for `F` with derivative frozen at the disk centre to `Fp1` (`= F′(s₁)`):
`s ↦ s − F s / Fp1`. A fixed point is exactly a zero of `F` (given `Fp1 ≠ 0`) — see
`chordPhi_fixedPt_iff`. No `Complex.log` ⇒ no branch-safety needed. -/
noncomputable def chordPhi (F : ℂ → ℂ) (Fp1 : ℂ) (s : ℂ) : ℂ := s - F s / Fp1

/-- **Fixed point ⟺ zero of `F`**, unconditionally (given `Fp1 ≠ 0`). -/
theorem chordPhi_fixedPt_iff {F : ℂ → ℂ} {Fp1 : ℂ} (hFp1 : Fp1 ≠ 0) {s : ℂ} :
    Function.IsFixedPt (chordPhi F Fp1) s ↔ F s = 0 := by
  unfold Function.IsFixedPt chordPhi
  rw [sub_eq_self, div_eq_zero_iff]
  simp [hFp1]

/-- **Generic Banach existence wrapper (chord-Newton).** A `K`-Lipschitz self-map of a closed disk
that is `chordPhi F Fp1` (whose fixed points are `F`-zeros, discharged internally by
`chordPhi_fixedPt_iff`) has a genuine zero of `F` in the disk, by Banach's fixed-point theorem. -/
theorem chord_zero_exists_of_bounds (F : ℂ → ℂ) (Fp1 s1 : ℂ) (r : ℝ) (hr : 0 < r)
    (hFp1 : Fp1 ≠ 0) (K : NNReal) (hK1 : K < 1)
    (hMapsTo : Set.MapsTo (chordPhi F Fp1) (Metric.closedBall s1 r) (Metric.closedBall s1 r))
    (hLip : LipschitzOnWith K (chordPhi F Fp1) (Metric.closedBall s1 r)) :
    ∃ s ∈ Metric.closedBall s1 r, F s = 0 := by
  have hsc : IsComplete (Metric.closedBall s1 r) := Metric.isClosed_closedBall.isComplete
  have hcontract : ContractingWith K (hMapsTo.restrict (chordPhi F Fp1) _ _) :=
    ⟨hK1, hLip.mapsToRestrict hMapsTo⟩
  have hx0 : s1 ∈ Metric.closedBall s1 r := Metric.mem_closedBall_self hr.le
  have hxfin : edist s1 (chordPhi F Fp1 s1) ≠ ⊤ := edist_ne_top _ _
  obtain ⟨y, hys, hfp, _, _⟩ := hcontract.exists_fixedPoint' hsc hMapsTo hx0 hxfin
  exact ⟨y, hys, (chordPhi_fixedPt_iff hFp1).mp hfp⟩

/-- **Generic self-map fact**: a `K`-Lipschitz map on `closedBall s1 r` whose centre moves by
≤ `r(1−K)` maps the ball into itself — the standard Banach sufficient condition. -/
theorem mapsTo_closedBall_of_lipschitzOnWith_of_dist_le (phi : ℂ → ℂ) (s1 : ℂ) (r : ℝ)
    (hr : 0 ≤ r) (K : NNReal) (hLip : LipschitzOnWith K phi (Metric.closedBall s1 r))
    (hstep : dist s1 (phi s1) ≤ r * (1 - K)) :
    Set.MapsTo phi (Metric.closedBall s1 r) (Metric.closedBall s1 r) := by
  intro s hs
  rw [Metric.mem_closedBall] at hs ⊢
  have hs1mem : s1 ∈ Metric.closedBall s1 r := Metric.mem_closedBall_self hr
  have h1 : dist (phi s) (phi s1) ≤ K * dist s s1 :=
    hLip.dist_le_mul s (Metric.mem_closedBall.mpr hs) s1 hs1mem
  calc dist (phi s) s1 ≤ dist (phi s) (phi s1) + dist (phi s1) s1 := dist_triangle _ _ _
    _ ≤ K * dist s s1 + dist s1 (phi s1) := by rw [dist_comm (phi s1) s1]; linarith [h1]
    _ ≤ K * r + r * (1 - K) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hs (by positivity)
        · exact hstep
    _ = r := by ring

/-- **`chordPhi F Fp1` is `K`-Lipschitz on `closedBall s1 r`**, given `F` is differentiable on the
ball with derivative `F′` and the pointwise chord bound `‖1 − F′ s / Fp1‖ ≤ K` throughout the ball.
Via `Convex.lipschitzOnWith_of_nnnorm_deriv_le`. -/
theorem chordPhi_lipschitzOnWith {F F' : ℂ → ℂ} {Fp1 s1 : ℂ} {r : ℝ} (K : NNReal)
    (hderiv : ∀ s ∈ Metric.closedBall s1 r, HasDerivAt F (F' s) s)
    (hbound : ∀ s ∈ Metric.closedBall s1 r, ‖1 - F' s / Fp1‖ ≤ K) :
    LipschitzOnWith K (chordPhi F Fp1) (Metric.closedBall s1 r) := by
  have hconv : Convex ℝ (Metric.closedBall s1 r) := convex_closedBall s1 r
  have hchord : ∀ s ∈ Metric.closedBall s1 r,
      HasDerivAt (chordPhi F Fp1) (1 - F' s / Fp1) s := by
    intro s hs
    have h1 : HasDerivAt (fun x : ℂ => x) (1 : ℂ) s := hasDerivAt_id s
    have h2 : HasDerivAt (fun x : ℂ => F x / Fp1) (F' s / Fp1) s := (hderiv s hs).div_const Fp1
    exact h1.sub h2
  have hdiff : ∀ s ∈ Metric.closedBall s1 r, DifferentiableAt ℂ (chordPhi F Fp1) s :=
    fun s hs => (hchord s hs).differentiableAt
  apply hconv.lipschitzOnWith_of_nnnorm_deriv_le hdiff
  intro s hs
  rw [(hchord s hs).deriv, ← NNReal.coe_le_coe, coe_nnnorm]
  exact hbound s hs

/-! ### The shared `ChordPoleFamily` predicate + infinitude -/

/-- **The shared Banach chord-Newton pole family** for an analytic `F : ℂ → ℂ`: an indexed family of
disks `(s1 n, r)` (for `n ≥ N`), with frozen nonzero derivatives `Fp1 n`, on which the chord-Newton
map `chordPhi F (Fp1 n)` contracts (`hbound`), whose centres are good guesses (`hstep`) and pairwise
`> 2r`-separated (`hsep`). This is the **single shared open obligation** for both MZERO.5
(`F = det(Q̂₀_c)`) and POLE.3 (`F = G_baxter`); constructing it (the asymptotic pole locations + the
contraction/decay bounds) is what remains, and one asymptotic-family argument discharges both. -/
structure ChordPoleFamily (F : ℂ → ℂ) where
  /-- index threshold beyond which the family is well-behaved -/
  N : ℕ
  /-- disk centres (approximate zeros) -/
  s1 : ℕ → ℂ
  /-- frozen derivatives `Fp1 n = F′(s1 n)` -/
  Fp1 : ℕ → ℂ
  /-- a derivative function for `F` on the disks -/
  F' : ℂ → ℂ
  /-- disk radius -/
  r : ℝ
  /-- Lipschitz constant -/
  K : NNReal
  hr : 0 < r
  hK1 : K < 1
  hFp1 : ∀ n, N ≤ n → Fp1 n ≠ 0
  hderiv : ∀ n, N ≤ n → ∀ s ∈ Metric.closedBall (s1 n) r, HasDerivAt F (F' s) s
  hbound : ∀ n, N ≤ n → ∀ s ∈ Metric.closedBall (s1 n) r, ‖1 - F' s / Fp1 n‖ ≤ (K : ℝ)
  hstep : ∀ n, N ≤ n → ‖F (s1 n) / Fp1 n‖ ≤ r * (1 - (K : ℝ))
  hsep : ∀ m n, N ≤ m → N ≤ n → m ≠ n → 2 * r < dist (s1 m) (s1 n)

/-- **The shared theorem**: a `ChordPoleFamily F` ⇒ `F` has infinitely many complex zeros. Per-`n`
chord-Newton existence (`chord_zero_exists_of_bounds`) → `choose` a witness in each disk → the
witnesses are distinct because the disks are `> 2r`-separated (`hsep`) → `Set.Infinite`. -/
theorem zeros_infinite_of_chordPoleFamily {F : ℂ → ℂ} (fam : ChordPoleFamily F) :
    {s : ℂ | F s = 0}.Infinite := by
  have hwitness : ∀ n : ℕ,
      ∃ s ∈ Metric.closedBall (fam.s1 (n + fam.N)) fam.r, F s = 0 := by
    intro n
    have hm : fam.N ≤ n + fam.N := Nat.le_add_left fam.N n
    have hLip := chordPhi_lipschitzOnWith (F := F) (F' := fam.F') (Fp1 := fam.Fp1 (n + fam.N))
      (s1 := fam.s1 (n + fam.N)) (r := fam.r) fam.K (fam.hderiv (n + fam.N) hm)
      (fam.hbound (n + fam.N) hm)
    have hstep' : dist (fam.s1 (n + fam.N))
        (chordPhi F (fam.Fp1 (n + fam.N)) (fam.s1 (n + fam.N))) ≤ fam.r * (1 - (fam.K : ℝ)) := by
      simp only [chordPhi, dist_eq_norm, sub_sub_cancel]
      exact fam.hstep (n + fam.N) hm
    have hMapsTo := mapsTo_closedBall_of_lipschitzOnWith_of_dist_le
      (chordPhi F (fam.Fp1 (n + fam.N))) (fam.s1 (n + fam.N)) fam.r fam.hr.le fam.K hLip hstep'
    exact chord_zero_exists_of_bounds F (fam.Fp1 (n + fam.N)) (fam.s1 (n + fam.N)) fam.r fam.hr
      (fam.hFp1 (n + fam.N) hm) fam.K fam.hK1 hMapsTo hLip
  choose g hgmem hgzero using hwitness
  have hinj : Function.Injective g := by
    intro a b hab
    by_contra hne
    have hdist2r : dist (fam.s1 (a + fam.N)) (fam.s1 (b + fam.N)) ≤ 2 * fam.r := by
      calc dist (fam.s1 (a + fam.N)) (fam.s1 (b + fam.N))
          ≤ dist (fam.s1 (a + fam.N)) (g a) + dist (g a) (fam.s1 (b + fam.N)) := dist_triangle _ _ _
        _ = dist (g a) (fam.s1 (a + fam.N)) + dist (g b) (fam.s1 (b + fam.N)) := by
            rw [dist_comm (fam.s1 (a + fam.N)) (g a), hab]
        _ ≤ fam.r + fam.r :=
            add_le_add (Metric.mem_closedBall.mp (hgmem a)) (Metric.mem_closedBall.mp (hgmem b))
        _ = 2 * fam.r := by ring
    have hsep := fam.hsep (a + fam.N) (b + fam.N) (Nat.le_add_left _ _) (Nat.le_add_left _ _)
      (by omega)
    linarith
  exact Set.infinite_of_injective_forall_mem hinj hgzero

/-- **Growth-exposing variant of `zeros_infinite_of_chordPoleFamily`.** If, in addition, the family's
disk centres grow at least linearly (`c·n + d ≤ ‖s1 n‖` for `n ≥ N`, with `0 < c`), then the
constructed zero family `g` is injective, consists of `F`-zeros, and **inherits linear growth**
`c·n + (c·N + d − r) ≤ ‖g n‖` — each zero is within `r` of its centre (reverse triangle inequality
`norm_sub_norm_le`). This is the magnitude/growth input the summability lemmas need
(scalar `h_explicit_summable_of_pole_family` / mixture MML.5's `mixHS_summable_of_growth`), so one
construction serves both POLE.5 and MML.5-concrete. -/
theorem exists_zero_family_growth_of_chordPoleFamily {F : ℂ → ℂ} (fam : ChordPoleFamily F)
    {c d : ℝ} (hc : 0 < c)
    (hcentre : ∀ n, fam.N ≤ n → c * (n : ℝ) + d ≤ ‖fam.s1 n‖) :
    ∃ g : ℕ → ℂ, Function.Injective g ∧ (∀ n, F (g n) = 0) ∧
      ∀ n : ℕ, c * (n : ℝ) + (c * (fam.N : ℝ) + d - fam.r) ≤ ‖g n‖ := by
  have hwitness : ∀ n : ℕ,
      ∃ s ∈ Metric.closedBall (fam.s1 (n + fam.N)) fam.r, F s = 0 := by
    intro n
    have hm : fam.N ≤ n + fam.N := Nat.le_add_left fam.N n
    have hLip := chordPhi_lipschitzOnWith (F := F) (F' := fam.F') (Fp1 := fam.Fp1 (n + fam.N))
      (s1 := fam.s1 (n + fam.N)) (r := fam.r) fam.K (fam.hderiv (n + fam.N) hm)
      (fam.hbound (n + fam.N) hm)
    have hstep' : dist (fam.s1 (n + fam.N))
        (chordPhi F (fam.Fp1 (n + fam.N)) (fam.s1 (n + fam.N))) ≤ fam.r * (1 - (fam.K : ℝ)) := by
      simp only [chordPhi, dist_eq_norm, sub_sub_cancel]
      exact fam.hstep (n + fam.N) hm
    have hMapsTo := mapsTo_closedBall_of_lipschitzOnWith_of_dist_le
      (chordPhi F (fam.Fp1 (n + fam.N))) (fam.s1 (n + fam.N)) fam.r fam.hr.le fam.K hLip hstep'
    exact chord_zero_exists_of_bounds F (fam.Fp1 (n + fam.N)) (fam.s1 (n + fam.N)) fam.r fam.hr
      (fam.hFp1 (n + fam.N) hm) fam.K fam.hK1 hMapsTo hLip
  choose g hgmem hgzero using hwitness
  refine ⟨g, ?_, hgzero, ?_⟩
  · intro a b hab
    by_contra hne
    have hdist2r : dist (fam.s1 (a + fam.N)) (fam.s1 (b + fam.N)) ≤ 2 * fam.r := by
      calc dist (fam.s1 (a + fam.N)) (fam.s1 (b + fam.N))
          ≤ dist (fam.s1 (a + fam.N)) (g a) + dist (g a) (fam.s1 (b + fam.N)) := dist_triangle _ _ _
        _ = dist (g a) (fam.s1 (a + fam.N)) + dist (g b) (fam.s1 (b + fam.N)) := by
            rw [dist_comm (fam.s1 (a + fam.N)) (g a), hab]
        _ ≤ fam.r + fam.r :=
            add_le_add (Metric.mem_closedBall.mp (hgmem a)) (Metric.mem_closedBall.mp (hgmem b))
        _ = 2 * fam.r := by ring
    have hsep := fam.hsep (a + fam.N) (b + fam.N) (Nat.le_add_left _ _) (Nat.le_add_left _ _)
      (by omega)
    linarith
  · intro n
    have hm : fam.N ≤ n + fam.N := Nat.le_add_left fam.N n
    have hball : dist (g n) (fam.s1 (n + fam.N)) ≤ fam.r := Metric.mem_closedBall.mp (hgmem n)
    have hcent : c * ((n + fam.N : ℕ) : ℝ) + d ≤ ‖fam.s1 (n + fam.N)‖ := hcentre (n + fam.N) hm
    have hrev : ‖fam.s1 (n + fam.N)‖ - ‖g n‖ ≤ ‖fam.s1 (n + fam.N) - g n‖ := norm_sub_norm_le _ _
    have hdd : ‖fam.s1 (n + fam.N) - g n‖ = dist (fam.s1 (n + fam.N)) (g n) := (dist_eq_norm _ _).symm
    have hd3 : dist (fam.s1 (n + fam.N)) (g n) ≤ fam.r := by rw [dist_comm]; exact hball
    have hcast : ((n + fam.N : ℕ) : ℝ) = (n : ℝ) + (fam.N : ℝ) := by push_cast; ring
    rw [hcast] at hcent
    have hge : ‖fam.s1 (n + fam.N)‖ - fam.r ≤ ‖g n‖ := by
      have := hrev.trans (le_of_eq hdd)
      linarith [hd3]
    nlinarith [hge, hcent]

end FMSA.BanachPoleFamily
