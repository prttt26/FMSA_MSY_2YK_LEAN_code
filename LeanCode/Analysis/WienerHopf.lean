/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib

/-!
# Krein / Wiener–Hopf half-line injectivity for a positive symbol — PROVED, no axiom

Group MA (`MATH_AXIOMS.md`), task `MA.12`. The operator-theoretic content of **Krein's theorem on
half-line Wiener–Hopf integral equations** (M.G. Krein, *Uspekhi Mat. Nauk* 13:5 (1958)), in the
**index-free, positive-symbol** case: a half-line Wiener–Hopf operator with a real symbol bounded
below by `ε > 0` is injective (indeed bounded below) on `L²(0,∞)`.

## Why this is a theorem, not an axiom

MA.12 was scoped (`MATH_AXIOMS.md`) as a likely axiom, on the reasoning that Mathlib has *no*
Wiener–Hopf / Toeplitz / Fredholm-index / winding-number theory (reconnaissance 2026-07-17 confirmed
this — all tracked unformalized in `docs/1000.yaml`). That reasoning is correct for the **full Krein
index theorem** (nonvanishing symbol + arbitrary winding ⇒ Fredholm with `index = −winding`), which
genuinely needs the missing machinery. But it is **false for the positive-symbol specialization**,
which has an elementary route the general theorem lacks — **coercivity via Plancherel**:

for `u ∈ L²(ℝ)` supported on `[0,∞)` (so `P₊u = u`), with real symbol `a ≥ ε > 0`,
`⟪(I−K)u, u⟫ = ⟪a·û, û⟫ = ∫ a(ξ)|û(ξ)|² dξ ≥ ε‖û‖² = ε‖u‖²` (Plancherel). If moreover `(I−K)u`
vanishes on `[0,∞)`, then `⟪(I−K)u,u⟫` (an integral supported where `u=0` or `(I−K)u=0`) is `0`,
forcing `‖u‖ = 0`. **No winding number, no Toeplitz theory.** Since the group's discipline is
prove-first and this is derivable from present Mathlib (L² Fourier isometry `Lp.fourierTransformₗᵢ`
+ Plancherel `Lp.inner_fourier_eq` + the `L²` inner-product-as-integral `L2.inner_def`), it is a
theorem. The half-line aspect needs **no Hardy-space subspace** — it is just a support hypothesis on
`u`, since the pairing over `ℝ` collapses to the `[0,∞)` pairing.

## Results

* `mulLp` — multiply an `L²` element by a bounded measurable real symbol, as an `L²` element.
* `mulLp_coercive` — `ε‖w‖² ≤ Re⟪a·w, w⟫` (the Plancherel-free half: pure `L²` integral coercivity).
* `fourierMul` — the Fourier multiplier operator `T_a u := 𝓕⁻¹(a · 𝓕 u)`.
* `fourierMul_coercive` — `ε‖u‖² ≤ Re⟪T_a u, u⟫` (previous + Plancherel `inner_fourier_eq`).
* `wienerHopf_positive_symbol_injective` — the main theorem: the half-line WH operator is injective.

All results are axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).

## Scope and honest caveats

* **Multiplier form, not convolution form.** The operator is the Fourier multiplier `T_a`; a
  consumer with a convolution operator `I − K` must identify it with `T_a` for `a = 1 − k̂` via `L²`
  convolution theorem (`Real.fourier_mul_convolution_eq` + a density argument). That step is
  application-side and deliberately out of this file (cf. `MATH_AXIOMS.md` MA.12, Q5).
* **`L²`, not bounded.** The FMSA consumer `OZ.10` (`oz_fixed_pt_unique`) needs uniqueness among
  *bounded* functions; the `L² → bounded` passage re-introduces exterior decay (the content of
  `baxter_exterior_regularity`). So MA.12 makes `OZ.10` **citable, not free** — a companion decay
  bridge stays (cf. `OZFIX.23`).
* **Positive symbol only.** The general Krein index theorem (winding ≠ 0) is *not* covered; it needs
  the winding-number/Toeplitz machinery Mathlib lacks. For the FMSA symbol `a = |1 − Q̂|² ≥ 0` the
  index is `0` for free, so this specialization is exactly what the application needs.
-/

open MeasureTheory Complex RCLike FourierTransform
open scoped ComplexInnerProductSpace

noncomputable section

variable {a : ℝ → ℝ}

/-- Multiplication of an `L²` function by a bounded measurable real symbol `a`, an `L²` element. -/
def mulLp (a : ℝ → ℝ) (ha : Measurable a) (M : ℝ) (haM : ∀ x, |a x| ≤ M)
    (w : Lp ℂ 2 (volume : Measure ℝ)) : Lp ℂ 2 (volume : Measure ℝ) :=
  (MemLp.of_le_mul (Lp.memLp w) (by
      exact ((Complex.measurable_ofReal.comp ha).aestronglyMeasurable).mul
        (Lp.aestronglyMeasurable w))
    (c := M) (by
      filter_upwards [] with x
      rw [norm_mul, Complex.norm_real]
      exact mul_le_mul_of_nonneg_right (haM x) (norm_nonneg _))).toLp
    (fun x => (a x : ℂ) * w x)

/-- Pointwise: `⟪↑c · z, z⟫_ℂ = ↑(c · ‖z‖²)` for real `c`. -/
lemma inner_ofReal_mul (c : ℝ) (z : ℂ) :
    (inner ℂ ((c : ℂ) * z) z) = ((c * ‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [RCLike.inner_apply, map_mul, Complex.conj_ofReal,
    show z * ((c : ℂ) * (starRingEnd ℂ) z) = (c : ℂ) * (z * (starRingEnd ℂ) z) from by ring,
    Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast; ring

/-- The pointwise `‖w x‖²` is integrable for `w ∈ L²`. -/
lemma integrable_norm_sq (w : Lp ℂ 2 (volume : Measure ℝ)) :
    Integrable (fun x => ‖(w : ℝ → ℂ) x‖ ^ 2) volume := by
  have h := (Lp.memLp w).integrable_norm_rpow (by norm_num) (by norm_num)
  simpa using h

/-- `∫ ‖w x‖² = ‖w‖²`. -/
lemma integral_norm_sq_eq (w : Lp ℂ 2 (volume : Measure ℝ)) :
    ∫ x, ‖(w : ℝ → ℂ) x‖ ^ 2 = ‖w‖ ^ 2 := by
  have h1 : (inner ℂ w w) = ((∫ x, ‖(w : ℝ → ℂ) x‖ ^ 2 : ℝ) : ℂ) := by
    rw [MeasureTheory.L2.inner_def, ← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [] with x
    have := inner_ofReal_mul 1 ((w : ℝ → ℂ) x)
    simp only [Complex.ofReal_one, one_mul] at this
    simp only [this]
  have h2 : (inner ℂ w w) = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  exact_mod_cast h1.symm.trans h2

/-- Coercivity of the multiplier with a positive real symbol: `ε‖w‖² ≤ Re⟪M_a w, w⟫`. -/
lemma mulLp_coercive (ha : Measurable a) (M : ℝ) (haM : ∀ x, |a x| ≤ M)
    (ε : ℝ) (haε : ∀ x, ε ≤ a x) (w : Lp ℂ 2 (volume : Measure ℝ)) :
    ε * ‖w‖ ^ 2 ≤ (inner ℂ (mulLp a ha M haM w) w).re := by
  have hrep : (mulLp a ha M haM w : ℝ → ℂ) =ᵐ[volume] fun x => (a x : ℂ) * w x :=
    MemLp.coeFn_toLp _
  have hkey : (inner ℂ (mulLp a ha M haM w) w) = ((∫ x, a x * ‖(w : ℝ → ℂ) x‖ ^ 2 : ℝ) : ℂ) := by
    rw [MeasureTheory.L2.inner_def, ← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [hrep] with x hx
    rw [hx]; exact inner_ofReal_mul (a x) ((w : ℝ → ℂ) x)
  rw [hkey, Complex.ofReal_re]
  have hgint : Integrable (fun x => ‖(w : ℝ → ℂ) x‖ ^ 2) volume := integrable_norm_sq w
  have haint : Integrable (fun x => a x * ‖(w : ℝ → ℂ) x‖ ^ 2) volume :=
    hgint.bdd_mul ha.aestronglyMeasurable (c := M)
      (by filter_upwards [] with x; rw [Real.norm_eq_abs]; exact haM x)
  have hmono : ε * (∫ x, ‖(w : ℝ → ℂ) x‖ ^ 2) ≤ ∫ x, a x * ‖(w : ℝ → ℂ) x‖ ^ 2 := by
    rw [← integral_const_mul]
    apply integral_mono (hgint.const_mul ε) haint
    intro x
    exact mul_le_mul_of_nonneg_right (haε x) (sq_nonneg _)
  rw [integral_norm_sq_eq] at hmono
  exact hmono

/-- The Fourier multiplier operator `T_a u := 𝓕⁻¹(a · 𝓕 u)` with real symbol `a`. -/
def fourierMul (a : ℝ → ℝ) (ha : Measurable a) (M : ℝ) (haM : ∀ x, |a x| ≤ M)
    (u : Lp ℂ 2 (volume : Measure ℝ)) : Lp ℂ 2 (volume : Measure ℝ) :=
  𝓕⁻ (mulLp a ha M haM (𝓕 u))

/-- Coercivity of the Fourier multiplier with positive real symbol: `ε‖u‖² ≤ Re⟪T_a u, u⟫`. -/
lemma fourierMul_coercive (ha : Measurable a) (M : ℝ) (haM : ∀ x, |a x| ≤ M)
    (ε : ℝ) (haε : ∀ x, ε ≤ a x) (u : Lp ℂ 2 (volume : Measure ℝ)) :
    ε * ‖u‖ ^ 2 ≤ (inner ℂ (fourierMul a ha M haM u) u).re := by
  have hpl : (inner ℂ (fourierMul a ha M haM u) u)
      = inner ℂ (mulLp a ha M haM (𝓕 u)) (𝓕 u) := by
    rw [fourierMul, ← Lp.inner_fourier_eq (𝓕⁻ (mulLp a ha M haM (𝓕 u))) u,
      fourier_fourierInv_eq]
  rw [hpl]
  have := mulLp_coercive ha M haM ε haε (𝓕 u)
  rwa [Lp.norm_fourier_eq] at this

/-- **Krein / Wiener–Hopf half-line injectivity for a positive symbol.** If `a` is a bounded
measurable real symbol with `a ≥ ε > 0`, then the half-line Wiener–Hopf operator built from the
Fourier multiplier `T_a` is injective: any `u ∈ L²` supported on `[0,∞)` (i.e. `u = 0` a.e. on
`(-∞,0]`) whose image `T_a u` vanishes a.e. on `[0,∞)` must be `0`. -/
theorem wienerHopf_positive_symbol_injective (ha : Measurable a) (M : ℝ) (haM : ∀ x, |a x| ≤ M)
    (ε : ℝ) (hε : 0 < ε) (haε : ∀ x, ε ≤ a x) (u : Lp ℂ 2 (volume : Measure ℝ))
    (hu : ∀ᵐ x ∂(volume : Measure ℝ), x ≤ 0 → (u : ℝ → ℂ) x = 0)
    (hTu : ∀ᵐ x ∂(volume : Measure ℝ), 0 ≤ x → (fourierMul a ha M haM u : ℝ → ℂ) x = 0) :
    u = 0 := by
  -- the WH boundary conditions force ⟪T_a u, u⟫ = 0
  have hzero : (inner ℂ (fourierMul a ha M haM u) u) = 0 := by
    rw [MeasureTheory.L2.inner_def]
    rw [show (0 : ℂ) = ∫ _ : ℝ, (0 : ℂ) from (integral_zero _ _).symm]
    apply integral_congr_ae
    filter_upwards [hu, hTu] with x hx hTx
    rcases le_total x 0 with h | h
    · rw [hx h, inner_zero_right]
    · rw [hTx h, inner_zero_left]
  -- coercivity then forces u = 0
  have hcoer := fourierMul_coercive ha M haM ε haε u
  rw [hzero, Complex.zero_re] at hcoer
  have hnn : ε * ‖u‖ ^ 2 ≤ 0 := hcoer
  have : ‖u‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖u‖, norm_nonneg u]
  have : ‖u‖ = 0 := by nlinarith [sq_nonneg ‖u‖, norm_nonneg u]
  exact norm_eq_zero.mp this

end
