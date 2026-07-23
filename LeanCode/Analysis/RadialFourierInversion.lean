/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib

/-!
# Radial Fourier inversion — PROVED (no axiom), general-purpose

Group MA (`MATH_AXIOMS.md`), task `MA.9`. The classical inversion of the 3D radial Fourier
transform (= the sine transform of `r·f(r)`), i.e. the left inverse of the project's
`radial_fourier` (`HardSphere/RadialFourier.lean`):

`F k = (4π/k)·∫₀^∞ r f(r) sin(kr) dr`  ⟹  `f r = (1/(2π²r))·∫₀^∞ k F(k) sin(kr) dk`.

**Not an axiom.** The MA.9 record asked whether this could be admitted as a math axiom; the
answer was "it joins Group MA, but as a task to PROVE" — Mathlib already has the essential
ingredient, `MeasureTheory.Integrable.fourierInv_fourier_eq` (`Analysis/Fourier/Inversion.lean`),
`𝓕⁻(𝓕 f) v = f v` on any finite-dimensional real inner-product space (here `V := ℝ`). Everything
below is derived from it; `#print axioms` on every result = the standard three. This follows the
group's precedent: `MA.2`, `MA.4`, `MA.5` were all retired by proving.

**Contents.**
* `fourier_of_odd` / `fourier_of_even` — the general bridges: `𝓕` of an odd (resp. even) function
  is `-2i` times its sine transform (resp. `2` times its cosine transform). Reusable well beyond
  this file.
* `sine_inversion_of_odd` — `ψ r = (2/π)·∫₀^∞ (sine transform of ψ)(k)·sin(kr) dk`.
* `cosine_inversion_of_even` — the even/cosine mirror.
* `radial_inversion` — MA.9's target statement (a short algebraic corollary of the sine form: the
  `4π/k` prefactor cancels, so the radial inversion *is* the sine inversion in disguise).
  Instantiate `F := radial_fourier f` with `hF := fun _ => rfl`.
* `radial_inversion_antideriv` — the **antiderivative form**, which is what a hard-sphere-type
  consumer must use (see the trap below).

**⚠ The trap (why the antiderivative form exists).** The naive pointwise inversion is *not
available* for the PY hard-sphere consumer: with `ψ(s) := s·h(s)`, `𝓕ψ(k) ~ 1/k` is **not**
integrable, so the `h'f : Integrable (𝓕 f)` hypothesis of `radial_inversion` genuinely fails —
that is the contact jump at `r = σ`, not a technicality. (Numerically confirmed, scratch
`ma9_check.py`: for an `f` with a jump, `|k·F(k)|·k` is constant in `k`, i.e. `k·F(k) ~ 1/k`.)
The fix is one antiderivative up: `Ψ(u) := ∫_u^∞ s h(s) ds` is continuous through the jump,
**even** (because `s·h(s)` is odd), and `𝓕Ψ ~ Ĥ ~ 1/k² ∈ L¹` ✓ — so `cosine_inversion_of_even`
applies to `Ψ` where `sine_inversion_of_odd` cannot apply to `ψ`. Same lesson as `OZFIX.12`'s
`Kterm` trap. Both forms were numerically pre-checked before formalizing (smooth and
discontinuous test functions; constants `1/(2π²r)` and `1/(2π²)` confirmed to ~1e-12).

**Remaining work for the consumer** (recorded honestly): `radial_inversion_antideriv` takes the
relation `hC : cosineTransform Ψ k = F k/(4π)` as a hypothesis. Deriving it from
`Ψ(u) = ∫_u^∞ s f(s) ds` is a Fubini swap on the triangular region
(`∫₀^∞ cos(kv) ∫_v^∞ s f(s) ds dv = ∫₀^∞ s f(s) ∫₀^s cos(kv) dv ds = (1/k)∫₀^∞ s f(s) sin(ks) ds`),
elementary but not yet formalized here.
-/

open MeasureTheory Real Set Filter Topology FourierTransform Complex

noncomputable section

/-- `𝓕` on `ℝ`, written out with the plain product in the exponent. -/
private lemma fourier_real_eq (f : ℝ → ℂ) (w : ℝ) :
    𝓕 f w = ∫ v : ℝ, Complex.exp (-(2 * π * v * w) * Complex.I) * f v := by
  rw [Real.fourier_eq']
  congr 1; funext v
  rw [smul_eq_mul]
  congr 2
  rw [RCLike.inner_apply]
  push_cast
  simp [mul_comm]
  ring

/-- Splitting `∫_ℝ` at the origin. -/
private lemma integral_split_zero (g : ℝ → ℂ) (hg : Integrable g) :
    (∫ v : ℝ, g v) = (∫ v in Ioi (0:ℝ), g (-v)) + ∫ v in Ioi (0:ℝ), g v := by
  rw [← integral_add_compl (measurableSet_Iic (a := (0:ℝ))) hg, compl_Iic]
  congr 1
  have := integral_comp_neg_Ioi (0:ℝ) g
  simpa using this

/-- The Fourier integrand is integrable when `ψ` is (the kernel has modulus one). -/
private lemma integrable_fourier_integrand (ψ : ℝ → ℂ) (hint : Integrable ψ) (w : ℝ) :
    Integrable (fun v : ℝ => Complex.exp (-(2 * π * v * w) * Complex.I) * ψ v) := by
  apply Integrable.bdd_mul' hint
  · exact (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
  · filter_upwards with v
    rw [Complex.norm_exp]
    have h : (-(2 * (π:ℂ) * (v:ℂ) * (w:ℂ)) * Complex.I).re = 0 := by simp [Complex.mul_re]
    rw [h, Real.exp_zero]

private lemma exp_sub_exp_eq (x : ℝ) :
    Complex.exp (-(x:ℂ) * Complex.I) - Complex.exp ((x:ℂ) * Complex.I) =
      -(2 * Complex.I) * (Real.sin x : ℂ) := by
  rw [Complex.ofReal_sin, Complex.sin]
  linear_combination (Complex.exp (-(x:ℂ) * Complex.I) - Complex.exp ((x:ℂ) * Complex.I)) *
    Complex.I_sq

private lemma exp_add_exp_eq (x : ℝ) :
    Complex.exp (-(x:ℂ) * Complex.I) + Complex.exp ((x:ℂ) * Complex.I) =
      2 * (Real.cos x : ℂ) := by
  rw [Complex.ofReal_cos, Complex.cos]
  ring

/-- **`𝓕` of an odd function is `-2i` times its sine transform.** -/
theorem fourier_of_odd (ψ : ℝ → ℂ) (hodd : ∀ v, ψ (-v) = -ψ v) (hint : Integrable ψ) (w : ℝ) :
    𝓕 ψ w = -(2 * Complex.I) * ∫ v in Ioi (0:ℝ), (Real.sin (2 * π * v * w) : ℂ) * ψ v := by
  rw [fourier_real_eq]
  set g : ℝ → ℂ := fun v => Complex.exp (-(2 * π * v * w) * Complex.I) * ψ v with hgdef
  have hgint : Integrable g := integrable_fourier_integrand ψ hint w
  rw [integral_split_zero g hgint,
    ← integral_add hgint.comp_neg.integrableOn hgint.integrableOn, ← integral_const_mul]
  apply integral_congr_ae (Filter.Eventually.of_forall _)
  intro v
  simp only [hgdef, hodd v]
  rw [show (-(2 * (π:ℂ) * ((-v : ℝ):ℂ) * (w:ℂ)) * Complex.I)
        = ((2 * π * v * w : ℝ) : ℂ) * Complex.I by push_cast; ring,
    show (-(2 * (π:ℂ) * (v:ℂ) * (w:ℂ)) * Complex.I)
        = -((2 * π * v * w : ℝ) : ℂ) * Complex.I by push_cast; ring]
  linear_combination (ψ v) * exp_sub_exp_eq (2 * π * v * w)

/-- **`𝓕` of an even function is `2` times its cosine transform.** -/
theorem fourier_of_even (Φ : ℝ → ℂ) (heven : ∀ v, Φ (-v) = Φ v) (hint : Integrable Φ) (w : ℝ) :
    𝓕 Φ w = 2 * ∫ v in Ioi (0:ℝ), (Real.cos (2 * π * v * w) : ℂ) * Φ v := by
  rw [fourier_real_eq]
  set g : ℝ → ℂ := fun v => Complex.exp (-(2 * π * v * w) * Complex.I) * Φ v with hgdef
  have hgint : Integrable g := integrable_fourier_integrand Φ hint w
  rw [integral_split_zero g hgint,
    ← integral_add hgint.comp_neg.integrableOn hgint.integrableOn, ← integral_const_mul]
  apply integral_congr_ae (Filter.Eventually.of_forall _)
  intro v
  simp only [hgdef, heven v]
  rw [show (-(2 * (π:ℂ) * ((-v : ℝ):ℂ) * (w:ℂ)) * Complex.I)
        = ((2 * π * v * w : ℝ) : ℂ) * Complex.I by push_cast; ring,
    show (-(2 * (π:ℂ) * (v:ℂ) * (w:ℂ)) * Complex.I)
        = -((2 * π * v * w : ℝ) : ℂ) * Complex.I by push_cast; ring]
  linear_combination (Φ v) * exp_add_exp_eq (2 * π * v * w)


/-- 𝓕⁻ is 𝓕 evaluated at `-w`. -/
private lemma fourierInv_eq_fourier_neg (f : ℝ → ℂ) (w : ℝ) : 𝓕⁻ f w = 𝓕 f (-w) := by
  rw [Real.fourierInv_eq, Real.fourier_eq]
  congr 1; funext v; congr 2
  rw [RCLike.inner_apply, RCLike.inner_apply]
  simp

/-- The sine transform of a real function, over the half-line. -/
noncomputable def sineTransform (ψ : ℝ → ℝ) (k : ℝ) : ℝ := ∫ v in Ioi (0:ℝ), ψ v * Real.sin (k * v)

theorem sine_inversion_of_odd (ψ : ℝ → ℝ) (hodd : ∀ v, ψ (-v) = -ψ v)
    (hint : Integrable (fun v => (ψ v : ℂ)))
    (h'f : Integrable (𝓕 (fun v => (ψ v : ℂ))))
    {r : ℝ} (hr : ContinuousAt (fun v => (ψ v : ℂ)) r) :
    ψ r = (2 / π) * ∫ k in Ioi (0:ℝ), sineTransform ψ k * Real.sin (k * r) := by
  set Ψ : ℝ → ℂ := fun v => (ψ v : ℂ) with hΨdef
  set S : ℝ → ℝ := sineTransform ψ with hSdef
  have hoddΨ : ∀ v, Ψ (-v) = -Ψ v := by
    intro v; simp only [hΨdef, hodd v]; push_cast; ring
  -- Step A: 𝓕 Ψ w = -(2I) * S(2π w)
  have hA : ∀ w : ℝ, 𝓕 Ψ w = -(2 * Complex.I) * (S (2 * π * w) : ℂ) := by
    intro w
    rw [fourier_of_odd Ψ hoddΨ hint w]
    congr 1
    rw [hSdef, sineTransform, ← integral_complex_ofReal]
    apply integral_congr_ae (Filter.Eventually.of_forall _)
    intro v
    rw [show (2 * π * v * w) = (2 * π * w * v) by ring]
    push_cast
    ring
  -- S is odd
  have hSodd : ∀ k : ℝ, S (-k) = -S k := by
    intro k
    rw [hSdef, sineTransform, sineTransform, ← integral_neg]
    apply integral_congr_ae (Filter.Eventually.of_forall _)
    intro v
    rw [show (-k * v) = -(k * v) by ring, Real.sin_neg]
    ring
  -- 𝓕 Ψ is odd
  have hoddF : ∀ w, 𝓕 Ψ (-w) = -(𝓕 Ψ w) := by
    intro w
    rw [hA, hA, show (2 * π * -w) = -(2 * π * w) by ring, hSodd]
    push_cast; ring
  -- inversion
  have key : 𝓕⁻ (𝓕 Ψ) r = Ψ r := hint.fourierInv_fourier_eq h'f hr
  rw [fourierInv_eq_fourier_neg, fourier_of_odd (𝓕 Ψ) hoddF h'f (-r)] at key
  have hpt : ∀ v : ℝ, (Real.sin (2 * π * v * -r) : ℂ) * 𝓕 Ψ v
      = (2 * Complex.I) * ((Real.sin (2 * π * v * r) * S (2 * π * v) : ℝ) : ℂ) := by
    intro v
    rw [hA v, show (2 * π * v * -r) = -(2 * π * v * r) by ring, Real.sin_neg]
    push_cast; ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
    integral_complex_ofReal] at key
  -- change of variables k = 2π v
  have hcv : (∫ v in Ioi (0:ℝ), Real.sin (2 * π * v * r) * S (2 * π * v))
      = (2 * π)⁻¹ * ∫ k in Ioi (0:ℝ), Real.sin (k * r) * S k := by
    have h := integral_comp_mul_left_Ioi (fun k => Real.sin (k * r) * S k) 0
      (by positivity : (0:ℝ) < 2 * π)
    rw [mul_zero] at h
    rw [h, smul_eq_mul]
  rw [hcv] at key
  -- conclude
  have hcomm : (∫ k in Ioi (0:ℝ), Real.sin (k * r) * S k)
      = ∫ k in Ioi (0:ℝ), S k * Real.sin (k * r) := by
    apply integral_congr_ae (Filter.Eventually.of_forall _)
    intro k; ring
  rw [hcomm] at key
  set J : ℝ := ∫ k in Ioi (0:ℝ), S k * Real.sin (k * r) with hJdef
  have h4 : (-(2 * Complex.I)) * (2 * Complex.I) = 4 := by
    rw [show (-(2 * Complex.I)) * (2 * Complex.I) = -(4 * Complex.I ^ 2) by ring, Complex.I_sq]
    ring
  rw [← mul_assoc, h4] at key
  have hπ : (π:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hfin : Ψ r = (((2 / π) * J : ℝ) : ℂ) := by
    rw [← key]; push_cast; field_simp; ring
  have hfin2 : ((ψ r : ℝ) : ℂ) = (((2 / π) * J : ℝ) : ℂ) := hfin
  exact_mod_cast hfin2


/-- The cosine transform of a real function, over the half-line. -/
noncomputable def cosineTransform (Φ : ℝ → ℝ) (k : ℝ) : ℝ := ∫ v in Ioi (0:ℝ), Φ v * Real.cos (k * v)

/-- **Cosine-transform inversion** (mirror of `sine_inversion_of_odd`). -/
theorem cosine_inversion_of_even (Φ : ℝ → ℝ) (heven : ∀ v, Φ (-v) = Φ v)
    (hint : Integrable (fun v => (Φ v : ℂ)))
    (h'f : Integrable (𝓕 (fun v => (Φ v : ℂ))))
    {u : ℝ} (hu : ContinuousAt (fun v => (Φ v : ℂ)) u) :
    Φ u = (2 / π) * ∫ k in Ioi (0:ℝ), cosineTransform Φ k * Real.cos (k * u) := by
  set Ξ : ℝ → ℂ := fun v => (Φ v : ℂ) with hΞdef
  set C : ℝ → ℝ := cosineTransform Φ with hCdef
  have hevenΞ : ∀ v, Ξ (-v) = Ξ v := by
    intro v; simp only [hΞdef, heven v]
  have hA : ∀ w : ℝ, 𝓕 Ξ w = 2 * (C (2 * π * w) : ℂ) := by
    intro w
    rw [fourier_of_even Ξ hevenΞ hint w]
    congr 1
    rw [hCdef, cosineTransform, ← integral_complex_ofReal]
    apply integral_congr_ae (Filter.Eventually.of_forall _)
    intro v
    rw [show (2 * π * v * w) = (2 * π * w * v) by ring]
    push_cast
    ring
  have hCeven : ∀ k : ℝ, C (-k) = C k := by
    intro k
    rw [hCdef, cosineTransform, cosineTransform]
    apply integral_congr_ae (Filter.Eventually.of_forall _)
    intro v
    rw [show (-k * v) = -(k * v) by ring, Real.cos_neg]
  have hevenF : ∀ w, 𝓕 Ξ (-w) = 𝓕 Ξ w := by
    intro w
    rw [hA, hA, show (2 * π * -w) = -(2 * π * w) by ring, hCeven]
  have key : 𝓕⁻ (𝓕 Ξ) u = Ξ u := hint.fourierInv_fourier_eq h'f hu
  rw [fourierInv_eq_fourier_neg, fourier_of_even (𝓕 Ξ) hevenF h'f (-u)] at key
  have hpt : ∀ v : ℝ, (Real.cos (2 * π * v * -u) : ℂ) * 𝓕 Ξ v
      = 2 * ((Real.cos (2 * π * v * u) * C (2 * π * v) : ℝ) : ℂ) := by
    intro v
    rw [hA v, show (2 * π * v * -u) = -(2 * π * v * u) by ring, Real.cos_neg]
    push_cast; ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
    integral_complex_ofReal] at key
  have hcv : (∫ v in Ioi (0:ℝ), Real.cos (2 * π * v * u) * C (2 * π * v))
      = (2 * π)⁻¹ * ∫ k in Ioi (0:ℝ), Real.cos (k * u) * C k := by
    have h := integral_comp_mul_left_Ioi (fun k => Real.cos (k * u) * C k) 0
      (by positivity : (0:ℝ) < 2 * π)
    rw [mul_zero] at h
    rw [h, smul_eq_mul]
  rw [hcv] at key
  have hcomm : (∫ k in Ioi (0:ℝ), Real.cos (k * u) * C k)
      = ∫ k in Ioi (0:ℝ), C k * Real.cos (k * u) := by
    apply integral_congr_ae (Filter.Eventually.of_forall _)
    intro k; ring
  rw [hcomm] at key
  set J : ℝ := ∫ k in Ioi (0:ℝ), C k * Real.cos (k * u) with hJdef
  have hπ : (π:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hfin : Ξ u = (((2 / π) * J : ℝ) : ℂ) := by
    rw [← key]; push_cast; field_simp
  have hfin2 : ((Φ u : ℝ) : ℂ) = (((2 / π) * J : ℝ) : ℂ) := hfin
  exact_mod_cast hfin2


/-- **Radial Fourier inversion, pointwise.** `F` is the radial (sine) transform
`F k = (4π/k)∫₀^∞ r f(r) sin(kr) dr`; then `f r = (1/(2π²r))∫₀^∞ k F(k) sin(kr) dk`. -/
theorem radial_inversion (f : ℝ → ℝ) (F : ℝ → ℝ)
    (hF : ∀ k, F k = (4 * π / k) * ∫ r in Ioi (0:ℝ), r * f r * Real.sin (k * r))
    (hint : Integrable (fun v => ((v * f |v| : ℝ) : ℂ)))
    (h'f : Integrable (𝓕 (fun v => ((v * f |v| : ℝ) : ℂ))))
    {r : ℝ} (hr0 : 0 < r) (hrc : ContinuousAt (fun v => ((v * f |v| : ℝ) : ℂ)) r) :
    f r = (1 / (2 * π ^ 2 * r)) * ∫ k in Ioi (0:ℝ), k * F k * Real.sin (k * r) := by
  set ψ : ℝ → ℝ := fun v => v * f |v| with hψdef
  have hodd : ∀ v, ψ (-v) = -ψ v := by
    intro v; simp only [hψdef, abs_neg]; ring
  have hinv := sine_inversion_of_odd ψ hodd hint h'f hrc
  have hψr : ψ r = r * f r := by rw [hψdef]; simp only [abs_of_pos hr0]
  have hkF : ∀ k, k * F k = 4 * π * sineTransform ψ k := by
    intro k
    rcases eq_or_ne k 0 with rfl | hk
    · simp [sineTransform]
    · rw [hF k, sineTransform]
      have hcg : (∫ x in Ioi (0:ℝ), x * f x * Real.sin (k * x))
          = ∫ v in Ioi (0:ℝ), ψ v * Real.sin (k * v) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro v hv
        simp only [hψdef, abs_of_pos (mem_Ioi.mp hv)]
      rw [hcg]
      field_simp
  have hIeq : (∫ k in Ioi (0:ℝ), k * F k * Real.sin (k * r))
      = 4 * π * ∫ k in Ioi (0:ℝ), sineTransform ψ k * Real.sin (k * r) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro k _
    dsimp only
    rw [show k * F k * Real.sin (k * r) = (k * F k) * Real.sin (k * r) by ring, hkF k]
    ring
  set J : ℝ := ∫ k in Ioi (0:ℝ), sineTransform ψ k * Real.sin (k * r) with hJdef
  have h1 : r * f r = (2 / π) * J := by rw [← hψr]; exact hinv
  have hπ : (π:ℝ) ≠ 0 := Real.pi_ne_zero
  have hJval : J = (π / 2) * (r * f r) := by rw [h1]; field_simp
  rw [hIeq, hJval]
  field_simp
  ring

/-- **Radial inversion, antiderivative form** — the shape a consumer with a jump discontinuity
must use (see the file docstring's trap). Given the even antiderivative `Ψ` whose cosine transform
is `F/(4π)`, `Ψ u = (1/(2π²))·∫₀^∞ F(k) cos(ku) dk`. -/
theorem radial_inversion_antideriv (Ψ : ℝ → ℝ) (F : ℝ → ℝ)
    (heven : ∀ v, Ψ (-v) = Ψ v)
    (hC : ∀ k ∈ Ioi (0:ℝ), cosineTransform Ψ k = F k / (4 * π))
    (hint : Integrable (fun v => (Ψ v : ℂ)))
    (h'f : Integrable (𝓕 (fun v => (Ψ v : ℂ))))
    {u : ℝ} (hu : ContinuousAt (fun v => (Ψ v : ℂ)) u) :
    Ψ u = (1 / (2 * π ^ 2)) * ∫ k in Ioi (0:ℝ), F k * Real.cos (k * u) := by
  rw [cosine_inversion_of_even Ψ heven hint h'f hu]
  have hrw : (∫ k in Ioi (0:ℝ), cosineTransform Ψ k * Real.cos (k * u))
      = (4 * π)⁻¹ * ∫ k in Ioi (0:ℝ), F k * Real.cos (k * u) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro k hk
    dsimp only
    rw [hC k hk]; ring
  rw [hrw]
  set K : ℝ := ∫ k in Ioi (0:ℝ), F k * Real.cos (k * u) with hKdef
  have hπ : (π:ℝ) ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-! ### Closing the antiderivative form: the tail integral and its cosine transform

`radial_inversion_antideriv` above takes the relation `hC` as a hypothesis. The two results below
discharge it from first principles for the actual tail integral `Ψ(u) = ∫_u^∞ s f(s) ds`, so a
consumer never has to supply `hC` by hand (`radial_inversion_antideriv_of_tail`). The analytic
heart is an improper integration by parts against `sin(k·)/k` rather than the Fubini swap the MA.9
record anticipated — `MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul` does it directly.
-/

/-- **FTC for a tail integral.** `u ↦ ∫_u^∞ g` has derivative `-g x` at every `x > 0`. -/
theorem hasDerivAt_integral_Ioi (g : ℝ → ℝ) (hgint : IntegrableOn g (Ioi (0:ℝ)))
    {x : ℝ} (hx : 0 < x) (hgc : ContinuousAt g x) :
    HasDerivAt (fun u => ∫ s in Ioi u, g s) (-(g x)) x := by
  have hsplit : ∀ u : ℝ, 0 < u →
      (∫ s in Ioi u, g s) = (∫ s in Ioi (0:ℝ), g s) - ∫ s in (0:ℝ)..u, g s := by
    intro u hu
    have hun : Ioc (0:ℝ) u ∪ Ioi u = Ioi (0:ℝ) := Set.Ioc_union_Ioi_eq_Ioi hu.le
    have hdisj : Disjoint (Ioc (0:ℝ) u) (Ioi u) := Set.Ioc_disjoint_Ioi le_rfl
    have h1 : (∫ s in Ioc (0:ℝ) u, g s) + ∫ s in Ioi u, g s = ∫ s in Ioi (0:ℝ), g s := by
      rw [← setIntegral_union hdisj measurableSet_Ioi
        (hgint.mono_set (by rw [← hun]; exact Set.subset_union_left))
        (hgint.mono_set (by rw [← hun]; exact Set.subset_union_right)), hun]
    rw [intervalIntegral.integral_of_le hu.le]
    linarith [h1]
  have heq : (fun u => ∫ s in Ioi u, g s)
      =ᶠ[nhds x] fun u => (∫ s in Ioi (0:ℝ), g s) - ∫ s in (0:ℝ)..u, g s := by
    filter_upwards [Ioi_mem_nhds hx] with u hu using hsplit u hu
  refine HasDerivAt.congr_of_eventuallyEq ?_ heq
  have hFTC : HasDerivAt (fun u => ∫ s in (0:ℝ)..u, g s) (g x) x := by
    apply intervalIntegral.integral_hasDerivAt_right
    · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx.le]
      exact hgint.mono_set Set.Ioc_subset_Ioi_self
    · exact ⟨Ioi 0, Ioi_mem_nhds hx, hgint.1⟩
    · exact hgc
  have h2 := (hasDerivAt_const x (∫ s in Ioi (0:ℝ), g s)).sub hFTC
  rw [zero_sub] at h2
  exact h2

/-- **The cosine transform of an antiderivative**, by improper integration by parts against
`sin(k·)/k`: if `Ψ' = -(s·f s)` on `(0,∞)`, `Ψ` has a limit at `0⁺` and vanishes at `∞`, then
`cosineTransform Ψ k = (1/k)·∫₀^∞ s f(s) sin(ks) ds`. This is the relation `hC` needs. -/
theorem cosineTransform_of_hasDerivAt (f Ψ : ℝ → ℝ) {k L : ℝ} (hk : k ≠ 0)
    (hΨ' : ∀ x ∈ Ioi (0:ℝ), HasDerivAt Ψ (-(x * f x)) x)
    (hΨ0 : Tendsto Ψ (𝓝[>] (0:ℝ)) (𝓝 L))
    (hΨinf : Tendsto Ψ atTop (𝓝 0))
    (hΨint : IntegrableOn (fun v => Ψ v * Real.cos (k * v)) (Ioi 0))
    (hfint : IntegrableOn (fun s => s * f s * Real.sin (k * s)) (Ioi 0)) :
    cosineTransform Ψ k = (1 / k) * ∫ s in Ioi (0:ℝ), s * f s * Real.sin (k * s) := by
  have hkabs : (0:ℝ) < |k| := abs_pos.mpr hk
  have hv : ∀ x ∈ Ioi (0:ℝ), HasDerivAt (fun s => Real.sin (k * s) / k) (Real.cos (k * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun s : ℝ => k * s) k x := by
      simpa using (hasDerivAt_id x).const_mul k
    refine ((h1.sin).div_const k).congr_deriv ?_
    field_simp
  have hbnd : ∀ x : ℝ, |Real.sin (k * x) / k| ≤ |k|⁻¹ := by
    intro x
    rw [abs_div, inv_eq_one_div]
    gcongr
    exact Real.abs_sin_le_one _
  have h_zero : Tendsto (fun x => Ψ x * (Real.sin (k * x) / k)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hs : Tendsto (fun s : ℝ => Real.sin (k * s) / k) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have hc : ContinuousAt (fun s : ℝ => Real.sin (k * s) / k) 0 := by fun_prop
      simpa using (hc.continuousWithinAt (s := Ioi (0:ℝ))).tendsto
    simpa using hΨ0.mul hs
  have h_infty : Tendsto (fun x => Ψ x * (Real.sin (k * x) / k)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun x => ?_) (?_ : Tendsto (fun x => ‖Ψ x‖ * |k|⁻¹) atTop (𝓝 0))
    · rw [norm_mul, Real.norm_eq_abs (Real.sin (k * x) / k)]
      gcongr
      exact hbnd x
    · simpa using hΨinf.norm.mul_const |k|⁻¹
  have hu'v : IntegrableOn ((fun x => -(x * f x)) * fun s => Real.sin (k * s) / k) (Ioi 0) := by
    rw [Pi.mul_def]
    have heq : (fun x => -(x * f x) * (Real.sin (k * x) / k))
        = fun x => (-k⁻¹) * (x * f x * Real.sin (k * x)) := by
      funext x; rw [div_eq_mul_inv]; ring
    rw [heq]
    exact hfint.const_mul _
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul (u := Ψ) (v := fun s => Real.sin (k * s) / k)
    (u' := fun x => -(x * f x)) (v' := fun x => Real.cos (k * x))
    hΨ' hv (by rw [Pi.mul_def]; exact hΨint) hu'v
    (by rw [Pi.mul_def]; exact h_zero) (by rw [Pi.mul_def]; exact h_infty)
  rw [cosineTransform, hibp]
  have hrw : (∫ x in Ioi (0:ℝ), -(x * f x) * (Real.sin (k * x) / k))
      = (-k⁻¹) * ∫ s in Ioi (0:ℝ), s * f s * Real.sin (k * s) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    dsimp only
    rw [div_eq_mul_inv]; ring
  rw [hrw]
  field_simp
  ring

/-- **Radial inversion, antiderivative form — fully closed.** No `hC` hypothesis: for the actual
tail integral `Ψ(u) = ∫_u^∞ s f(s) ds` the relation is derived (FTC + improper IBP). -/
theorem radial_inversion_antideriv_of_tail (f F Ψ : ℝ → ℝ)
    (hF : ∀ k, F k = (4 * π / k) * ∫ r in Ioi (0:ℝ), r * f r * Real.sin (k * r))
    (hfint : IntegrableOn (fun s => s * f s) (Ioi 0))
    (hfc : ∀ x ∈ Ioi (0:ℝ), ContinuousAt (fun s => s * f s) x)
    (hsin : ∀ k, IntegrableOn (fun s => s * f s * Real.sin (k * s)) (Ioi 0))
    (hΨdef : ∀ u, Ψ u = ∫ s in Ioi u, s * f s)
    (heven : ∀ v, Ψ (-v) = Ψ v)
    {L : ℝ} (hΨ0 : Tendsto Ψ (𝓝[>] (0:ℝ)) (𝓝 L))
    (hΨinf : Tendsto Ψ atTop (𝓝 0))
    (hΨcos : ∀ k, IntegrableOn (fun v => Ψ v * Real.cos (k * v)) (Ioi 0))
    (hint : Integrable (fun v => (Ψ v : ℂ)))
    (h'f : Integrable (𝓕 (fun v => (Ψ v : ℂ))))
    {u : ℝ} (hu : ContinuousAt (fun v => (Ψ v : ℂ)) u) :
    Ψ u = (1 / (2 * π ^ 2)) * ∫ k in Ioi (0:ℝ), F k * Real.cos (k * u) := by
  refine radial_inversion_antideriv Ψ F heven ?_ hint h'f hu
  intro k hk0
  have hk : k ≠ 0 := (mem_Ioi.mp hk0).ne'
  have hΨ' : ∀ x ∈ Ioi (0:ℝ), HasDerivAt Ψ (-(x * f x)) x := by
    intro x hx
    have h := hasDerivAt_integral_Ioi (fun s => s * f s) hfint (mem_Ioi.mp hx) (hfc x hx)
    have heqf : Ψ = fun u => ∫ s in Ioi u, s * f s := funext hΨdef
    rw [heqf]; exact h
  rw [cosineTransform_of_hasDerivAt f Ψ hk hΨ' hΨ0 hΨinf (hΨcos k) (hsin k), hF k]
  field_simp

end
