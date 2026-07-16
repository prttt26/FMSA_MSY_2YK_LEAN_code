/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import LeanCode.Analysis.ContourDeformation
import LeanCode.Analysis.JordanLemma

/-!
# Mittag-Leffler expansion (axiom) + one-pole Fourier kernel (theorem), general-purpose

Group MA (`MATH_AXIOMS.md`), tasks `MA.2`/`MA.3`. Two pieces:

* `mittagLeffler_expansion_of_bounded_on_circles` — **axiom**: the classical Mittag-Leffler
  expansion theorem (Whittaker–Watson §7.4 / Titchmarsh §3.2): a function meromorphic with simple
  poles `p n` (enumerated by nondecreasing modulus), uniformly bounded on a sequence of expanding
  circles, equals `f(0) + Σₙ resₙ·(1/(z-pₙ) + 1/pₙ)` (partial sums in enumeration order). Absent
  from Mathlib (same reconnaissance as `ContourDeformation.lean`: no residue theorem, no
  Mittag-Leffler, tracked unformalized in Mathlib's own `docs/1000.yaml`). Numerically pre-checked
  against this project's `Ĥ(k) = Ĉ/(1-ρĈ)` at η∈{0.3,0.45}: `sup‖Ĥ‖` on the expanding
  pole-avoiding circles is constant (1.7453/1.1636), and the expansion converges pointwise to `Ĥ`
  at real and complex test points (errors → ~1e-7 by 60 pole quadruples).
* `fourier_kernel_one_pole` — **genuine theorem, no new axiom** (`#print axioms` = the half-disk
  deformation axiom + standard three): `∫_{-R}^{R} e^{ixr}/(x-k₀) dx → 2πi·e^{ik₀r}` as `R→∞`,
  for `Im k₀ > 0`, `r > 0`. Proof: the half-disk residue-sum theorem
  (`halfDiskBoundary_eq_sum_two_pi_I_mul_of_simple_poles`) gives `diameter + arc = 2πi·e^{ik₀r}`
  for each large `R`, and `jordan_lemma_arc_bound` kills the arc (`‖1/(z-k₀)‖ ≤ 1/(R-‖k₀‖) → 0` —
  exactly the decaying-amplitude case Jordan's lemma serves).

Together these decompose the previously-blocked `OZFIX.10` monolithic arc estimate
(`proof_notes_ozfix.md`): expand `Ĥ` via Mittag-Leffler (bounded on circles — verified), then
Fourier-invert each `1/(k-kₙ)` term via `fourier_kernel_one_pole`, then sum (summability from the
`POLE.5` machinery). No inadmissible "this arc vanishes" axiom needed.
-/

open Set Metric Complex Filter Topology intervalIntegral

noncomputable section

/-- **Mittag-Leffler expansion theorem** (classical; Whittaker–Watson §7.4). For `f` with simple
poles exactly at `p n` (local representation `f = g n z/(z - p n)` near each, residue
`g n (p n)`), enumerated by nondecreasing modulus, differentiable elsewhere, and uniformly
bounded on a sequence of circles `‖z‖ = R N` with `R N → ∞`: the pole expansion
`Σₙ resₙ·(1/(z-pₙ)+1/pₙ)` converges (partial sums in enumeration order) to `f z - f 0`.
Stated in Mathlib vocabulary, mirroring `circleIntegral_eq_sum_two_pi_I_mul_of_simple_poles`'s
simple-pole encoding; the ordered-`Tendsto` conclusion (not `HasSum`) matches the classical
statement — consumers with absolutely-summable residue tails can upgrade via `Summable`. -/
axiom mittagLeffler_expansion_of_bounded_on_circles {f : ℂ → ℂ} {p : ℕ → ℂ} {r' : ℕ → ℝ}
    {g : ℕ → ℂ → ℂ} {R : ℕ → ℝ} {M : ℝ}
    (hp0 : ∀ n, p n ≠ 0)
    (hpmono : ∀ n, ‖p n‖ ≤ ‖p (n + 1)‖)
    (hr'pos : ∀ n, 0 < r' n)
    (hdisj : ∀ m n, m ≠ n → Disjoint (closedBall (p m) (r' m)) (closedBall (p n) (r' n)))
    (hgeq : ∀ n, ∀ z ∈ closedBall (p n) (r' n), f z = g n z / (z - p n))
    (hgc : ∀ n, ContinuousOn (g n) (closedBall (p n) (r' n)))
    (hgd : ∀ n, ∀ z ∈ ball (p n) (r' n), DifferentiableAt ℂ (g n) z)
    (hfd : ∀ z : ℂ, (∀ n, z ≠ p n) → DifferentiableAt ℂ f z)
    (hR : Tendsto R atTop atTop)
    (hbound : ∀ N, ∀ z : ℂ, ‖z‖ = R N → ‖f z‖ ≤ M)
    {z : ℂ} (hz : ∀ n, z ≠ p n) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, g n (p n) * (1 / (z - p n) + 1 / p n)) atTop
      (𝓝 (f z - f 0))

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
