/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.YukawaDCF.YukawaWienerHopf
import LeanCode.HSMixture.MixtureHSZeros
import LeanCode.HSMixture.MatrixQ0
import LeanCode.Analysis.MittagLeffler

/-!
# Group MRS — Mixture Real-Space Baxter Route to the Inner DCF

The DCF route that replaces MML.8's refuted Mittag-Leffler premise. This file lands **MRS.3**, the
pivot of the whole group.

## MRS.3 — the (★) identity, and why the DCF has no HS poles

[LN] eq:OZ1_Baxter gives, for the first-order OZ equation,

    (a)   Q̂₀ᵀ(k)·Ĥ₁(k)·Q̂₀(k) = [Q̂₀(−k)]⁻¹·Ĉ₁(k)·[Q̂₀ᵀ(−k)]⁻¹

while Y1.6's `Hhat1_spec` is its partner

    (b)   Q̂₀ᵀ(k)·Ĥ₁(k)·Q̂₀(k) = B₁(k)

Equating (a) with (b) and solving for `Ĉ₁` is **pure matrix algebra** — no contour integration, no
Mittag-Leffler machinery — and yields

    (★)   Ĉ₁(k) = Q̂₀(−k)·B₁(k)·Q̂₀ᵀ(−k)

* `star_of_oz1_baxter` — the algebra: `Qm⁻¹·C₁·(Qmᵀ)⁻¹ = B₁` ⇒ `C₁ = Qm·B₁·Qmᵀ`.
* `star_of_oz1_baxter_hhat1` — the same with (b) supplied by Y1.6 `Hhat1_spec`, i.e. exactly
  "equate (a) with (b)".

## The load-bearing corollary: `det Q̂₀`'s zeros never touch the DCF

**(★) contains no `Q̂₀⁻¹`.** Since `Q̂₀` is entire (the `φ₁ ~ 1/k²`, `φ₂ ~ 1/k³` singularities at
`k = 0` are removable — `phi1_tendsto`/`phi2_tendsto`, MZERO.9's chain) and `B₁` carries only the
Yukawa poles `k = i·z_q`, the DCF `Ĉ₁` is meromorphic with **only Yukawa poles**. The zeros of
`det Q̂₀` — the whole subject of Group MZERO, and the source of MML.8's HS-pole series — **never
enter the DCF**.

* `star_entry_differentiableAt` — the Lean-checkable form: **wherever `Q̂₀(−·)` and `B₁` are
  differentiable, so is every entry of `Ĉ₁`** — with **no hypothesis on `det Q̂₀`** whatsoever. That
  absence is the whole point: a zero of `det Q̂₀` imposes no singularity on `Ĉ₁`.

Contrast the RDF `Ĥ₁ = [Q̂₀ᵀ]⁻¹·B₁·[Q̂₀]⁻¹`, which *does* carry the inverses ⇒ genuine (double) HS
poles (`MixtureInnerDCF.lean`, MML.8 Crux #1). **The `Q̂₀⁻¹`-count is the DCF/RDF dividing line:
none ⇒ DCF (this file, finite closed form); two ⇒ RDF.**

Numerically certified (2026-07-16 session): (★) at N=2 over a k-sweep, max abs err `4.4×10⁻¹³`;
exact at N=1.

Status: ✓ MRS.3 DONE (axiom-clean). MRS.1 (matrix WH factorization — the only analytic input),
MRS.2 (eq:OZ1_Baxter (a)), MRS.4, MRS.5 remain.
-/

set_option linter.style.longLine false

open Filter Topology
open scoped Matrix

namespace FMSA.MRS

/-! ### MRS.3 — the (★) identity -/

/-- **MRS.3 (★), the algebra.**  If `Qm⁻¹ · C₁ · (Qmᵀ)⁻¹ = B₁` with `Qm` invertible, then
`C₁ = Qm · B₁ · Qmᵀ`.  Instantiated with `Qm := Q̂₀(−k)` this is (★)
`Ĉ₁(k) = Q̂₀(−k)·B₁(k)·Q̂₀ᵀ(−k)` — note the conclusion contains **no inverse**. -/
theorem star_of_oz1_baxter {N : ℕ} (Qm C1 B1 : Matrix (Fin N) (Fin N) ℂ)
    (hQm : IsUnit Qm.det)
    (ha : Qm⁻¹ * C1 * (Qmᵀ)⁻¹ = B1) :
    C1 = Qm * B1 * Qmᵀ := by
  have hT : IsUnit (Qmᵀ : Matrix (Fin N) (Fin N) ℂ).det := by
    rwa [Matrix.det_transpose]
  rw [← ha]
  rw [show Qm * (Qm⁻¹ * C1 * (Qmᵀ)⁻¹) * Qmᵀ = (Qm * Qm⁻¹) * C1 * ((Qmᵀ)⁻¹ * Qmᵀ) by
        simp only [Matrix.mul_assoc],
      Matrix.mul_nonsing_inv Qm hQm, Matrix.nonsing_inv_mul (Qmᵀ) hT,
      Matrix.one_mul, Matrix.mul_one]

/-- **MRS.3 (★), equating (a) with (b).**  Given [LN] eq:OZ1_Baxter **(a)**
`Q̂₀ᵀ(k)·Ĥ₁(k)·Q̂₀(k) = [Q̂₀(−k)]⁻¹·Ĉ₁(k)·[Q̂₀ᵀ(−k)]⁻¹` — with `Ĥ₁ := Hhat1 Q0k B₁`, so that its
partner **(b)** is exactly Y1.6's `Hhat1_spec` — solving for `Ĉ₁` gives (★)
`Ĉ₁ = Q̂₀(−k)·B₁·Q̂₀ᵀ(−k)`. -/
theorem star_of_oz1_baxter_hhat1 {N : ℕ} (Q0k Qm C1 B1 : Matrix (Fin N) (Fin N) ℂ)
    (hQ0k : IsUnit Q0k.det) (hQm : IsUnit Qm.det)
    (ha : Q0kᵀ * FMSA.YukawaWH.Hhat1 Q0k B1 * Q0k = Qm⁻¹ * C1 * (Qmᵀ)⁻¹) :
    C1 = Qm * B1 * Qmᵀ := by
  have hb := FMSA.YukawaWH.Hhat1_spec Q0k B1 hQ0k
  rw [hb] at ha
  exact star_of_oz1_baxter Qm C1 B1 hQm ha.symm

/-! ### MRS.5 — the core fact: a polynomial ⋆ (exp × step) is a *finite closed form*

The inner DCF `c^{(1)}_ij` is the real-space convolution `𝒞 = 𝒬⁻ ⋆ ℬ ⋆ (𝒬⁻)ᵀ` of the (piecewise
polynomial, compactly supported) Baxter kernel `𝒬⁻` with the outer Yukawa tail `ℬ` (exponential ×
step). The claim "finite closed form, piecewise at the knots" rests on the atomic fact below: the
convolution of **any** polynomial `q` with the tail kernel `e^{−z(u−τ)}` over `[a,u]` evaluates — via
the integrating-factor antiderivative `G` (`G′ + zG = q`) — to `G(u) − G(a)·e^{−z(u−a)}`, a
**polynomial in `u` plus a single exponential** (no infinite sum, no new poles). This is what makes
each convolution `q ⋆ (exp·step)` close in finite terms; the piecewise structure comes from the
support-overlap limits, and the whole `𝒞` is a finite ℝ-linear combination of such pieces. -/

/-- **MRS.5 (atomic) — polynomial ⋆ exp-kernel = polynomial + one exponential.**  If `G` is the
integrating-factor antiderivative of `q` (`G′ τ = q τ − z·G τ`, i.e. `G′ + zG = q`), then
`∫_a^u q(τ)·e^{−z(u−τ)} dτ = G(u) − G(a)·e^{−z(u−a)}` — a *finite closed form* in `u`.  (For `q` of
degree `d`, `G` is a polynomial of degree `d`; `q = c₀,τ,τ²` give `G = c₀/z`, `τ/z−1/z²`,
`τ²/z−2τ/z²+2/z³`.)  Proof: FTC-2 with antiderivative `F(τ) = e^{−z(u−τ)}·G(τ)`, whose derivative is
exactly `q(τ)·e^{−z(u−τ)}` (the `zG` terms cancel). -/
theorem integral_poly_exp_conv (q G : ℝ → ℝ) (z a u : ℝ)
    (hG : ∀ τ, HasDerivAt G (q τ - z * G τ) τ) (hq : Continuous q) :
    (∫ τ in a..u, q τ * Real.exp (-z * (u - τ))) = G u - G a * Real.exp (-z * (u - a)) := by
  have hderiv : ∀ τ : ℝ, HasDerivAt (fun s => Real.exp (-z * (u - s)) * G s)
      (q τ * Real.exp (-z * (u - τ))) τ := by
    intro τ
    have hinner : HasDerivAt (fun s => -z * (u - s)) z τ := by
      simpa using ((hasDerivAt_const τ u).sub (hasDerivAt_id τ)).const_mul (-z)
    have hmul := hinner.exp.mul (hG τ)
    have heq : q τ * Real.exp (-z * (u - τ))
        = Real.exp (-z * (u - τ)) * z * G τ + Real.exp (-z * (u - τ)) * (q τ - z * G τ) := by ring
    rw [heq]; exact hmul
  have hcont : Continuous (fun τ => q τ * Real.exp (-z * (u - τ))) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun τ _ => hderiv τ)
      (hcont.intervalIntegrable a u)]
  simp only [sub_self, mul_zero, Real.exp_zero]
  ring

/-- **MRS.5 — the linear ⋆ exp-kernel closed form** (a concrete instance of `integral_poly_exp_conv`
for the linear part of `q_ij`).  `∫_a^u (c₀ + c₁τ)·e^{−z(u−τ)} dτ = G(u) − G(a)·e^{−z(u−a)}` with
`G(τ) = c₁/z·τ + (c₀/z − c₁/z²)` — a finite closed form, `z ≠ 0`.  (The `τ²` term extends the same
way with `G += c₂/z·τ² − 2c₂/z²·τ + 2c₂/z³`; omitted here only to keep the antiderivative
`HasDerivAt` elementary.) -/
theorem integral_linear_exp_conv (c0 c1 z a u : ℝ) (hz : z ≠ 0) :
    (∫ τ in a..u, (c0 + c1 * τ) * Real.exp (-z * (u - τ)))
      = (c1 / z * u + (c0 / z - c1 / z ^ 2))
        - (c1 / z * a + (c0 / z - c1 / z ^ 2)) * Real.exp (-z * (u - a)) := by
  refine integral_poly_exp_conv (fun τ => c0 + c1 * τ) (fun t => c1 / z * t + (c0 / z - c1 / z ^ 2))
    z a u (fun τ => ?_) (by fun_prop)
  have hd : HasDerivAt (fun t => c1 / z * t + (c0 / z - c1 / z ^ 2)) (c1 / z) τ := by
    simpa using ((hasDerivAt_id τ).const_mul (c1 / z)).add_const (c0 / z - c1 / z ^ 2)
  convert hd using 1
  field_simp
  ring

/-- **MRS.5 — the quadratic ⋆ exp-kernel closed form** (the instance the mixture `q_ij` actually
needs: `q_ij(t) = c₀ + c₁t + c₂t²` is a *quadratic*, per the Baxter inversion `_q_coeffs`).
`∫_a^u (c₀ + c₁τ + c₂τ²)·e^{−z(u−τ)} dτ = G(u) − G(a)·e^{−z(u−a)}` with the integrating-factor
antiderivative `G(τ) = c₂/z·τ² + (c₁/z − 2c₂/z²)·τ + (c₀/z − c₁/z² + 2c₂/z³)` (`z ≠ 0`), matching
the module docstring's stated `τ²/z − 2τ/z² + 2/z³` for the pure-`c₂` part.  This completes the
`integral_linear_exp_conv` family up to the degree the real-space DCF pieces require; the Python
oracle `fmsa_double_prop.px_convolve`/`_px_antideriv_u` computes the same `G` (its `γB − B_u = A`
check is exactly the `G′ + zG = q` hypothesis of `integral_poly_exp_conv`). -/
theorem integral_quadratic_exp_conv (c0 c1 c2 z a u : ℝ) (hz : z ≠ 0) :
    (∫ τ in a..u, (c0 + c1 * τ + c2 * τ ^ 2) * Real.exp (-z * (u - τ)))
      = (c2 / z * u ^ 2 + (c1 / z - 2 * c2 / z ^ 2) * u + (c0 / z - c1 / z ^ 2 + 2 * c2 / z ^ 3))
        - (c2 / z * a ^ 2 + (c1 / z - 2 * c2 / z ^ 2) * a + (c0 / z - c1 / z ^ 2 + 2 * c2 / z ^ 3))
          * Real.exp (-z * (u - a)) := by
  refine integral_poly_exp_conv (fun τ => c0 + c1 * τ + c2 * τ ^ 2)
    (fun t => c2 / z * t ^ 2 + (c1 / z - 2 * c2 / z ^ 2) * t + (c0 / z - c1 / z ^ 2 + 2 * c2 / z ^ 3))
    z a u (fun τ => ?_) (by fun_prop)
  have hpow : HasDerivAt (fun t : ℝ => t ^ 2) (2 * τ) τ := by simpa using hasDerivAt_pow 2 τ
  have e1 : HasDerivAt (fun t : ℝ => c2 / z * t ^ 2) (c2 / z * (2 * τ)) τ := hpow.const_mul (c2 / z)
  have e2 : HasDerivAt (fun t : ℝ => (c1 / z - 2 * c2 / z ^ 2) * t) (c1 / z - 2 * c2 / z ^ 2) τ := by
    simpa using (hasDerivAt_id τ).const_mul (c1 / z - 2 * c2 / z ^ 2)
  have hd : HasDerivAt
      (fun t => c2 / z * t ^ 2 + (c1 / z - 2 * c2 / z ^ 2) * t + (c0 / z - c1 / z ^ 2 + 2 * c2 / z ^ 3))
      (c2 / z * (2 * τ) + (c1 / z - 2 * c2 / z ^ 2)) τ := by
    simpa using (e1.add e2).add_const (c0 / z - c1 / z ^ 2 + 2 * c2 / z ^ 3)
  convert hd using 1
  field_simp
  ring

/-! ### MRS.5 (exponential part) — Fourier-inverting the *finite* Yukawa-pole set (reuses MA.3)

By (★)/MRS.3 the inner DCF `Ĉ₁` has **only finitely many** poles — the Yukawa poles `k = i·z_q` — so
its exponential part is a **finite** residue sum (unlike the RDF's infinite HS-pole series). MA.3
`fourier_kernel_one_pole` inverts one simple pole; summing it over the finite pole set (linearity)
gives the finite exponential closed form, with **no convergence issue and no new axiom** — the mixture
analog of the OZFIX.10 dissolution. -/

/-- **MRS.5 (exp part) — finite-pole-sum Fourier inversion.**  For a finite set of upper-half-plane
poles `k₀ q` (`Im > 0`) with residue weights `A q`, the truncated inverse-Fourier integral of the
principal part `Σ_q A_q/(x − k₀ q)` converges to the **finite exponential sum**
`Σ_q A_q · 2πi · e^{i k₀ q r}` (`r > 0`).  Direct linear combination of `fourier_kernel_one_pole`
(MA.3) — the exponential part of the inner DCF is finite-closed-form. -/
theorem fourier_kernel_finite_poles {ι : Type*} (s : Finset ι) (A k0 : ι → ℂ)
    (hk0 : ∀ q ∈ s, 0 < (k0 q).im) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun R : ℝ =>
        ∫ x in (-R)..R, ∑ q ∈ s, A q * (Complex.exp (Complex.I * x * r) / ((x : ℂ) - k0 q)))
      atTop
      (𝓝 (∑ q ∈ s, A q * (2 * (Real.pi : ℂ) * Complex.I * Complex.exp (Complex.I * k0 q * r)))) := by
  have hne : ∀ q ∈ s, ∀ x : ℝ, ((x : ℂ) - k0 q) ≠ 0 := by
    intro q hq x hx
    have him : ((x : ℂ) - k0 q).im = 0 := by rw [hx]; rfl
    rw [Complex.sub_im, Complex.ofReal_im, zero_sub, neg_eq_zero] at him
    exact (hk0 q hq).ne' him
  have hint : ∀ R : ℝ, ∀ q ∈ s,
      IntervalIntegrable (fun x : ℝ => A q * (Complex.exp (Complex.I * x * r) / ((x : ℂ) - k0 q)))
        MeasureTheory.volume (-R) R := by
    intro R q hq
    exact (Continuous.mul continuous_const
      (Continuous.div (by fun_prop) (by fun_prop) (hne q hq))).intervalIntegrable _ _
  have key : Tendsto (fun R : ℝ =>
        ∑ q ∈ s, ∫ x in (-R)..R, A q * (Complex.exp (Complex.I * x * r) / ((x : ℂ) - k0 q)))
      atTop (𝓝 (∑ q ∈ s, A q *
        (2 * (Real.pi : ℂ) * Complex.I * Complex.exp (Complex.I * k0 q * r)))) := by
    apply tendsto_finsetSum
    intro q hq
    refine ((fourier_kernel_one_pole (hk0 q hq) hr).const_mul (A q)).congr (fun R => ?_)
    rw [intervalIntegral.integral_const_mul]
  exact key.congr' (Filter.Eventually.of_forall
    (fun R => (intervalIntegral.integral_finsetSum (hint R)).symm))

/-- **MRS.5 (capstone) — a finite-pole DCF transform inverts to a finite exponential closed form.**
If the inner-DCF transform `Ĉ₁` agrees on the real axis with its finite principal-part
(Mittag-Leffler) sum `Σ_q A_q/(k − k_q)` over the finite Yukawa-pole set (all `Im k_q > 0`), then its
truncated inverse Fourier transform `∫_{−R}^R Ĉ₁(x)·e^{ixr} dx` converges to the **finite closed form**
`Σ_q A_q·2πi·e^{i k_q r}` (`r > 0`).  Together with `integral_poly_exp_conv` (the core polynomial ⋆ exp
pieces), this is the inner DCF's finite-closed-form inversion — no infinite sum, no distributions,
no new axiom (only MA.3).  What remains is purely to read off the concrete residues
`A_q = Q̂₀(−k_q)·[Res B₁]·Q̂₀ᵀ(−k_q)` from `Ĉ₁ = Q̂₀(−k)·B₁·Q̂₀ᵀ(−k)` (★). -/
theorem innerDCF_finite_closed_form {ι : Type*} (s : Finset ι) (A k0 : ι → ℂ)
    (hk0 : ∀ q ∈ s, 0 < (k0 q).im) {r : ℝ} (hr : 0 < r)
    (Chat1 : ℝ → ℂ) (hpp : ∀ x : ℝ, Chat1 x = ∑ q ∈ s, A q / ((x : ℂ) - k0 q)) :
    Tendsto (fun R : ℝ => ∫ x in (-R)..R, Chat1 x * Complex.exp (Complex.I * x * r)) atTop
      (𝓝 (∑ q ∈ s, A q * (2 * (Real.pi : ℂ) * Complex.I * Complex.exp (Complex.I * k0 q * r)))) := by
  have hrw : ∀ x : ℝ, Chat1 x * Complex.exp (Complex.I * x * r)
      = ∑ q ∈ s, A q * (Complex.exp (Complex.I * x * r) / ((x : ℂ) - k0 q)) := by
    intro x
    rw [hpp x, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun q _ => by ring)
  simp_rw [hrw]
  exact fourier_kernel_finite_poles s A k0 hk0 hr

/-! ### MRS.6 — the WH factorization frame (decomposes the old MRS.1)

The matrix WH factorization `Q̂₀(k)·Q̂₀ᵀ(−k) = I − Ĉ₀(k)` (originally MRS.1) splits into three
pure-numeric tasks:
* **MRS.6** (here) — take the factorization as the *definition* of the zeroth-order DCF matrix
  `Ĉ₀(k) := I − Q̂₀(k)·Q̂₀ᵀ(−k)`, discharging MRS.2's `hfact` for free, and **reduce** the remaining
  `hT0symm` to a clean swap identity (`Cmix0_isSymm_iff`).
* **MRS.7** — the swap identity `Q̂₀(−k)·Q̂₀ᵀ(k) = Q̂₀(k)·Q̂₀ᵀ(−k)` for the **physical** Baxter matrix
  (`Q0_mat_c` with the Lebowitz PY coefficients). The one genuinely non-trivial theorem — it *fails*
  for generic coefficients (a 5-exponential defect), holding only for the PY relations.
* **MRS.8** (deferred) — that `Ĉ₀` here equals the physical HS DCF transform (so the OZ hypotheses
  `hoz`/`hTS` of MRS.2 hold with real physical content, not just as conditional inputs).
-/

/-- **MRS.6 — the zeroth-order mixture DCF matrix**, defined by the WH factorization. -/
noncomputable def Cmix0 {N : ℕ} (Qfun : ℂ → Matrix (Fin N) (Fin N) ℂ) (k : ℂ) :
    Matrix (Fin N) (Fin N) ℂ := 1 - Qfun k * (Qfun (-k))ᵀ

/-- **MRS.6 — the factorization, by definition.**  `Q̂₀(k)·Q̂₀ᵀ(−k) = I − Ĉ₀(k)` — discharges
MRS.2's `hfact` with `T₀ := Q̂₀(k)·Q̂₀ᵀ(−k)`, `Ĉ₀ := Cmix0`. -/
theorem Cmix0_factorization {N : ℕ} (Qfun : ℂ → Matrix (Fin N) (Fin N) ℂ) (k : ℂ) :
    Qfun k * (Qfun (-k))ᵀ = 1 - Cmix0 Qfun k := by
  unfold Cmix0
  exact (sub_sub_cancel 1 (Qfun k * (Qfun (-k))ᵀ)).symm

/-- Transpose of `Ĉ₀`: `Ĉ₀(k)ᵀ = I − Q̂₀(−k)·Q̂₀ᵀ(k)`. -/
theorem Cmix0_transpose {N : ℕ} (Qfun : ℂ → Matrix (Fin N) (Fin N) ℂ) (k : ℂ) :
    (Cmix0 Qfun k)ᵀ = 1 - Qfun (-k) * (Qfun k)ᵀ := by
  unfold Cmix0
  rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul, Matrix.transpose_transpose]

/-- **MRS.6 — reduction of `hT0symm` to the swap identity.**  `Ĉ₀` is symmetric **iff**
`Q̂₀(−k)·Q̂₀ᵀ(k) = Q̂₀(k)·Q̂₀ᵀ(−k)`.  So MRS.2's `hT0symm` (`T₀ᵀ = T₀`) reduces exactly to MRS.7's
swap identity (note `T₀ᵀ = T₀ ⟺ Ĉ₀ᵀ = Ĉ₀`, since `T₀ = I − Ĉ₀`). -/
theorem Cmix0_isSymm_iff {N : ℕ} (Qfun : ℂ → Matrix (Fin N) (Fin N) ℂ) (k : ℂ) :
    (Cmix0 Qfun k)ᵀ = Cmix0 Qfun k ↔ Qfun (-k) * (Qfun k)ᵀ = Qfun k * (Qfun (-k))ᵀ := by
  rw [Cmix0_transpose]
  conv_lhs => rw [show Cmix0 Qfun k = 1 - Qfun k * (Qfun (-k))ᵀ from rfl]
  exact sub_right_inj

/-- **MRS.6 — `hT0symm` from the swap identity.**  Given MRS.7's swap identity, `T₀ = Q̂₀(k)·Q̂₀ᵀ(−k)`
is symmetric — i.e. exactly MRS.2's `hT0symm` hypothesis. -/
theorem T0_isSymm_of_swap {N : ℕ} (Qfun : ℂ → Matrix (Fin N) (Fin N) ℂ) (k : ℂ)
    (hswap : Qfun (-k) * (Qfun k)ᵀ = Qfun k * (Qfun (-k))ᵀ) :
    (Qfun k * (Qfun (-k))ᵀ)ᵀ = Qfun k * (Qfun (-k))ᵀ := by
  rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  exact hswap

/-- **MRS.6 — symmetry of a `2×2` matrix ⟺ its single off-diagonal equality** (the diagonal is
automatic).  Reduces `hT0symm` all the way to **one scalar identity** `M 0 1 = M 1 0`, which for
`M = Q̂₀(k)·Q̂₀ᵀ(−k)` is exactly MRS.7. -/
theorem fin2_transpose_eq_iff_offdiag (M : Matrix (Fin 2) (Fin 2) ℂ) :
    Mᵀ = M ↔ M 0 1 = M 1 0 := by
  constructor
  · intro h
    have := congrFun (congrFun h 1) 0
    simpa [Matrix.transpose_apply] using this
  · intro h
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply, h]

/-- **MRS.6 — `hT0symm` reduced to the off-diagonal scalar identity** (N=2).  `T₀ = Q̂₀(k)·Q̂₀ᵀ(−k)`
is symmetric **iff** `(Q̂₀(k)·Q̂₀ᵀ(−k)) 0 1 = (Q̂₀(k)·Q̂₀ᵀ(−k)) 1 0`.  MRS.7 is exactly this scalar
equality for the physical `Q̂₀`. -/
theorem T0_isSymm_iff_offdiag (Qfun : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (k : ℂ) :
    (Qfun k * (Qfun (-k))ᵀ)ᵀ = Qfun k * (Qfun (-k))ᵀ ↔
      (Qfun k * (Qfun (-k))ᵀ) 0 1 = (Qfun k * (Qfun (-k))ᵀ) 1 0 :=
  fin2_transpose_eq_iff_offdiag _

/-! ### MRS.7 (structure) — the two PY coefficient relations behind the swap identity

The swap identity `Q̂₀(−k)Q̂₀ᵀ(k) = Q̂₀(k)Q̂₀ᵀ(−k)` (MRS.7) *fails* for generic Baxter coefficients, but
the physical Lebowitz PY coefficients satisfy **two clean structural relations**, and — verified
symbolically — the swap identity holds for *any* coefficients obeying both (with `ρ,σ > 0`), with
**no** reference to the specific values. So MRS.7 factors into: these two relations (algebra, below)
+ a coefficient-free structural exp-identity (`Q0phys`/`Qppphys` no longer appear). `c := π/vac`. -/

/-- **MRS.7 — KEY relation 1.**  `Q0phys_ij = (σᵢ/2)·Qppphys_j + (π/vac)·σⱼ`.  The `ξ₂`-coupling term of
`Q0phys` is exactly `(σᵢ/2)` times that of `Qppphys`, leaving the linear `(π/vac)σⱼ` remainder. -/
theorem Q0phys_key_relation {N : ℕ} (rho sigma : Fin N → ℝ) (i j : Fin N)
    (hvac : FMSA.MatrixQ0.vacMix rho sigma ≠ 0) :
    FMSA.MatrixQ0.Q0phys rho sigma i j
      = sigma i / 2 * FMSA.MatrixQ0.Qppphys rho sigma i j
        + Real.pi / FMSA.MatrixQ0.vacMix rho sigma * sigma j := by
  unfold FMSA.MatrixQ0.Q0phys FMSA.MatrixQ0.Qppphys
  field_simp
  ring

/-- **MRS.7 — KEY relation 2.**  `Qppphys_j = 2(π/vac) + (π/vac)²·ξ₂·σⱼ` — `Qppphys` is affine in `σⱼ`
with slope `(π/vac)²ξ₂` (`ξ₂ = Σ ρσ²`). -/
theorem Qppphys_key_relation {N : ℕ} (rho sigma : Fin N → ℝ) (i j : Fin N)
    (hvac : FMSA.MatrixQ0.vacMix rho sigma ≠ 0) :
    FMSA.MatrixQ0.Qppphys rho sigma i j
      = 2 * (Real.pi / FMSA.MatrixQ0.vacMix rho sigma)
        + (Real.pi / FMSA.MatrixQ0.vacMix rho sigma) ^ 2
          * FMSA.MatrixQ0.xi2 rho sigma * sigma j := by
  unfold FMSA.MatrixQ0.Qppphys
  field_simp

/-- **MRS.7 — the coefficient-free structural swap** (N=2 off-diagonal identity).  For the Baxter
entries `q0_entry_c` with `Q0_ij = (σᵢ/2)Qpp_j + c·σⱼ` (KEY 1) and the four hypotheses KEY 2
(`Qpp_j = 2c + c²ξ₂σⱼ`), `ξ₂ = rg₀₀σ₀² + rg₁₁σ₁²`, and `rg₀₀·rg₁₁ = rg₀₁²`, the off-diagonal of
`Q̂₀(k)·Q̂₀ᵀ(−k)` is symmetric: `(Qp Qmᵀ) 0 1 = (Qp Qmᵀ) 1 0`.  Verified symbolically (defect ≡ 0);
the specific PY values are eliminated.  Proof: normalise all exponentials to the two atoms
`E₀ = e^{σ₀k/2}`, `E₁ = e^{σ₁k/2}`, then `field_simp` + `ring`. -/
theorem swap_offdiag_of_keys (σ0 σ1 c ξ2 Qpp0 Qpp1 rg00 rg01 rg11 k : ℂ) (hk : k ≠ 0)
    (hQpp0 : Qpp0 = 2 * c + c ^ 2 * ξ2 * σ0) (hQpp1 : Qpp1 = 2 * c + c ^ 2 * ξ2 * σ1)
    (hξ2 : ξ2 = rg00 * σ0 ^ 2 + rg11 * σ1 ^ 2) (hrg : rg00 * rg11 = rg01 ^ 2) :
    FMSA.Q0Complex.q0_entry_c k σ0 0 (σ0 / 2 * Qpp0 + c * σ0) Qpp0 rg00 1
        * FMSA.Q0Complex.q0_entry_c (-k) σ1 ((σ0 - σ1) / 2) (σ1 / 2 * Qpp0 + c * σ0) Qpp0 rg01 0
      + FMSA.Q0Complex.q0_entry_c k σ0 ((σ1 - σ0) / 2) (σ0 / 2 * Qpp1 + c * σ1) Qpp1 rg01 0
        * FMSA.Q0Complex.q0_entry_c (-k) σ1 0 (σ1 / 2 * Qpp1 + c * σ1) Qpp1 rg11 1
      = FMSA.Q0Complex.q0_entry_c k σ1 ((σ0 - σ1) / 2) (σ1 / 2 * Qpp0 + c * σ0) Qpp0 rg01 0
        * FMSA.Q0Complex.q0_entry_c (-k) σ0 0 (σ0 / 2 * Qpp0 + c * σ0) Qpp0 rg00 1
      + FMSA.Q0Complex.q0_entry_c k σ1 0 (σ1 / 2 * Qpp1 + c * σ1) Qpp1 rg11 1
        * FMSA.Q0Complex.q0_entry_c (-k) σ0 ((σ1 - σ0) / 2) (σ0 / 2 * Qpp1 + c * σ1) Qpp1 rg01 0 := by
  subst hQpp0 hQpp1 hξ2
  unfold FMSA.Q0Complex.q0_entry_c
  set E0 := Complex.exp (σ0 * k / 2) with hE0def
  set E1 := Complex.exp (σ1 * k / 2) with hE1def
  have hE0 : E0 ≠ 0 := Complex.exp_ne_zero _
  have hE1 : E1 ≠ 0 := Complex.exp_ne_zero _
  have e0 : Complex.exp (k * σ0) = E0 * E0 := by
    rw [hE0def, ← Complex.exp_add]; ring_nf
  have e0' : Complex.exp (-(k * σ0)) = E0⁻¹ * E0⁻¹ := by
    rw [hE0def, ← Complex.exp_neg, ← Complex.exp_add]; ring_nf
  have e1 : Complex.exp (k * σ1) = E1 * E1 := by
    rw [hE1def, ← Complex.exp_add]; ring_nf
  have e1' : Complex.exp (-(k * σ1)) = E1⁻¹ * E1⁻¹ := by
    rw [hE1def, ← Complex.exp_neg, ← Complex.exp_add]; ring_nf
  have h01 : Complex.exp ((σ0 - σ1) / 2 * k) = E0 * E1⁻¹ := by
    rw [hE0def, hE1def, ← Complex.exp_neg, ← Complex.exp_add]; ring_nf
  have h10 : Complex.exp ((σ1 - σ0) / 2 * k) = E0⁻¹ * E1 := by
    rw [hE0def, hE1def, ← Complex.exp_neg, ← Complex.exp_add]; ring_nf
  have h01' : Complex.exp (-((σ1 - σ0) / 2 * k)) = E0 * E1⁻¹ := by
    rw [hE0def, hE1def, ← Complex.exp_neg, ← Complex.exp_add]; ring_nf
  have h10' : Complex.exp (-((σ0 - σ1) / 2 * k)) = E0⁻¹ * E1 := by
    rw [hE0def, hE1def, ← Complex.exp_neg, ← Complex.exp_add]; ring_nf
  simp only [neg_mul, mul_neg, neg_neg, zero_mul, neg_zero, Complex.exp_zero,
    e0, e0', e1, e1', h01, h10, h01', h10']
  field_simp
  ring

/-- The physical (Lebowitz PY) complex Baxter matrix `Q̂₀(s)` for the N=2 mixture — `Q0_mat_c` with
the concrete `rhoGeoPhys`/`Q0phys`/`Qppphys` coefficients (cast to `ℂ`). -/
noncomputable def Qphys (sigma rho : Fin 2 → ℝ) (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  FMSA.Q0Complex.Q0_mat_c s (fun i => (sigma i : ℂ))
    (fun i j => ((FMSA.MatrixQ0.rhoGeoPhys rho i j : ℝ) : ℂ))
    (fun i j => ((FMSA.MatrixQ0.Q0phys rho sigma i j : ℝ) : ℂ))
    (fun i j => ((FMSA.MatrixQ0.Qppphys rho sigma i j : ℝ) : ℂ))

/-- **MRS.7 — the physical swap identity, fully assembled** (discharges MRS.2's `hT0symm`).  For the
concrete Lebowitz PY Baxter matrix, `T₀ = Q̂₀(k)·Q̂₀ᵀ(−k)` is symmetric.  Instantiates
`swap_offdiag_of_keys` (via `T0_isSymm_iff_offdiag`), discharging its four hypotheses from the KEY
relations + `√(ρᵢρᵢ) = ρᵢ`.  This closes the WH-factorization gate's symmetry obligation for the
physical matrix — no remaining math, only casts. -/
theorem Qphys_T0_isSymm (sigma rho : Fin 2 → ℝ) (k : ℂ)
    (hρ0 : 0 ≤ rho 0) (hρ1 : 0 ≤ rho 1) (hk : k ≠ 0)
    (hvac : FMSA.MatrixQ0.vacMix rho sigma ≠ 0) :
    (Qphys sigma rho k * (Qphys sigma rho (-k))ᵀ)ᵀ = Qphys sigma rho k * (Qphys sigma rho (-k))ᵀ := by
  rw [fin2_transpose_eq_iff_offdiag]
  have hK1 : ∀ i j : Fin 2, ((FMSA.MatrixQ0.Q0phys rho sigma i j : ℝ) : ℂ)
      = (sigma i : ℂ) / 2 * ((FMSA.MatrixQ0.Qppphys rho sigma i j : ℝ) : ℂ)
        + ((Real.pi / FMSA.MatrixQ0.vacMix rho sigma : ℝ) : ℂ) * (sigma j : ℂ) := fun i j => by
    exact_mod_cast congrArg Complex.ofReal (Q0phys_key_relation rho sigma i j hvac)
  have hrg10 : ((FMSA.MatrixQ0.rhoGeoPhys rho 1 0 : ℝ) : ℂ)
      = ((FMSA.MatrixQ0.rhoGeoPhys rho 0 1 : ℝ) : ℂ) := by
    simp only [FMSA.MatrixQ0.rhoGeoPhys, mul_comm (rho 1) (rho 0)]
  have hrg00 : ((FMSA.MatrixQ0.rhoGeoPhys rho 0 0 : ℝ) : ℂ) = ((rho 0 : ℝ) : ℂ) := by
    simp only [FMSA.MatrixQ0.rhoGeoPhys, Real.sqrt_mul_self hρ0]
  have hrg11 : ((FMSA.MatrixQ0.rhoGeoPhys rho 1 1 : ℝ) : ℂ) = ((rho 1 : ℝ) : ℂ) := by
    simp only [FMSA.MatrixQ0.rhoGeoPhys, Real.sqrt_mul_self hρ1]
  have hQpp : ∀ j : Fin 2, ((FMSA.MatrixQ0.Qppphys rho sigma 0 j : ℝ) : ℂ)
      = 2 * ((Real.pi / FMSA.MatrixQ0.vacMix rho sigma : ℝ) : ℂ)
        + ((Real.pi / FMSA.MatrixQ0.vacMix rho sigma : ℝ) : ℂ) ^ 2
          * ((FMSA.MatrixQ0.xi2 rho sigma : ℝ) : ℂ) * (sigma j : ℂ) := fun j => by
    exact_mod_cast congrArg Complex.ofReal (Qppphys_key_relation rho sigma 0 j hvac)
  have hξ2 : ((FMSA.MatrixQ0.xi2 rho sigma : ℝ) : ℂ)
      = ((FMSA.MatrixQ0.rhoGeoPhys rho 0 0 : ℝ) : ℂ) * (sigma 0 : ℂ) ^ 2
        + ((FMSA.MatrixQ0.rhoGeoPhys rho 1 1 : ℝ) : ℂ) * (sigma 1 : ℂ) ^ 2 := by
    rw [hrg00, hrg11]
    simp only [FMSA.MatrixQ0.xi2, Fin.sum_univ_two]
    push_cast
    ring
  have hrgprod : ((FMSA.MatrixQ0.rhoGeoPhys rho 0 0 : ℝ) : ℂ)
        * ((FMSA.MatrixQ0.rhoGeoPhys rho 1 1 : ℝ) : ℂ)
      = ((FMSA.MatrixQ0.rhoGeoPhys rho 0 1 : ℝ) : ℂ) ^ 2 := by
    rw [hrg00, hrg11]
    simp only [FMSA.MatrixQ0.rhoGeoPhys]
    rw [← Complex.ofReal_pow, Real.sq_sqrt (mul_nonneg hρ0 hρ1)]
    push_cast
    ring
  have hqpp_row : ∀ j : Fin 2, ((FMSA.MatrixQ0.Qppphys rho sigma 1 j : ℝ) : ℂ)
      = ((FMSA.MatrixQ0.Qppphys rho sigma 0 j : ℝ) : ℂ) := fun _ => rfl
  simp only [Qphys, FMSA.Q0Complex.Q0_mat_c, Matrix.mul_apply, Matrix.transpose_apply,
    Fin.sum_univ_two, Fin.isValue, sub_self, zero_div, Fin.reduceEq, reduceIte, hrg10, hK1,
    hqpp_row]
  exact swap_offdiag_of_keys (sigma 0) (sigma 1)
    ((Real.pi / FMSA.MatrixQ0.vacMix rho sigma : ℝ) : ℂ) ((FMSA.MatrixQ0.xi2 rho sigma : ℝ) : ℂ)
    ((FMSA.MatrixQ0.Qppphys rho sigma 0 0 : ℝ) : ℂ) ((FMSA.MatrixQ0.Qppphys rho sigma 0 1 : ℝ) : ℂ)
    ((FMSA.MatrixQ0.rhoGeoPhys rho 0 0 : ℝ) : ℂ) ((FMSA.MatrixQ0.rhoGeoPhys rho 0 1 : ℝ) : ℂ)
    ((FMSA.MatrixQ0.rhoGeoPhys rho 1 1 : ℝ) : ℂ) k hk (hQpp 0) (hQpp 1) hξ2 hrgprod

/-! ### MRS.2 — deriving (★) from the physics (first-order OZ + factorization)

MRS.3 above takes [LN] eq:OZ1_Baxter **(a)** as a hypothesis. MRS.2 *derives* (★) from the
underlying physical inputs instead — the first-order OZ equation and MRS.1's factorization — as an
independent route to the same conclusion. The algebra:

Write `T₀ := I − Ĉ₀`, `S₀ := I + Ĥ₀`. Zeroth-order OZ gives `S₀ = T₀⁻¹` (`hTS : T₀·S₀ = I`), and the
first-order OZ ([LN], notes' form) is **`Ĥ₁·T₀ = S₀·Ĉ₁`** (`hoz`). Left-multiplying by `T₀`:

    Ĉ₁ = (T₀·S₀)·Ĉ₁ = T₀·(S₀·Ĉ₁) = T₀·(Ĥ₁·T₀) = T₀·Ĥ₁·T₀.        (`oz1_C1_eq`)

Then MRS.1 `T₀ = Q̂₀(k)·Q̂₀ᵀ(−k)` (`hfact`), `T₀` symmetric (`hT0symm`, i.e. `Ĉ₀` symmetric — the pair
DCF is species-symmetric), and Y1.6 `B₁ = Q̂₀ᵀ(k)·Ĥ₁·Q̂₀(k)` (`hB1`, = `Hhat1_spec`) give

    Ĉ₁ = T₀·Ĥ₁·T₀ = (Q̂₀(k)Q̂₀ᵀ(−k))·Ĥ₁·(Q̂₀(k)Q̂₀ᵀ(−k))
       = (Q̂₀(−k)Q̂₀ᵀ(k))·Ĥ₁·(Q̂₀(k)Q̂₀ᵀ(−k))   [T₀ symmetric: Q̂₀(k)Q̂₀ᵀ(−k) = Q̂₀(−k)Q̂₀ᵀ(k)]
       = Q̂₀(−k)·(Q̂₀ᵀ(k)Ĥ₁Q̂₀(k))·Q̂₀ᵀ(−k) = Q̂₀(−k)·B₁·Q̂₀ᵀ(−k).   (★)
-/

/-- The first-order OZ step, pure algebra: if `Ĥ₁·T₀ = S₀·Ĉ₁` and `T₀·S₀ = I` then
`Ĉ₁ = T₀·Ĥ₁·T₀`. (`T₀·S₀ = I` is the zeroth-order OZ `S₀ = (I−Ĉ₀)⁻¹`; no other inverse needed.) -/
theorem oz1_C1_eq {N : ℕ} (T0 S0 H1 C1 : Matrix (Fin N) (Fin N) ℂ)
    (hoz : H1 * T0 = S0 * C1) (hTS : T0 * S0 = 1) :
    C1 = T0 * H1 * T0 := by
  calc C1 = (T0 * S0) * C1 := by rw [hTS, Matrix.one_mul]
    _ = T0 * (S0 * C1) := by rw [Matrix.mul_assoc]
    _ = T0 * (H1 * T0) := by rw [← hoz]
    _ = T0 * H1 * T0 := by rw [Matrix.mul_assoc]

/-- **MRS.2 ⇒ (★).**  From the first-order OZ (`hoz`, `hTS`), MRS.1's factorization
`T₀ = Q̂₀(k)·Q̂₀ᵀ(−k)` (`hfact`), the symmetry of `T₀ = I−Ĉ₀` (`hT0symm`, physical: the pair DCF is
species-symmetric), and Y1.6's `B₁ = Q̂₀ᵀ(k)·Ĥ₁·Q̂₀(k)` (`hB1` = `Hhat1_spec`), the (★) identity
`Ĉ₁ = Q̂₀(−k)·B₁·Q̂₀ᵀ(−k)` follows — the physical route to (★), independent of MRS.3's `(a)`-hypothesis.
Note the conclusion contains **no inverse**, so the "only Yukawa poles" corollary
(`star_entry_differentiableAt`) applies verbatim. -/
theorem star_of_first_order_oz {N : ℕ} (Qp Qm T0 S0 H1 C1 B1 : Matrix (Fin N) (Fin N) ℂ)
    (hoz : H1 * T0 = S0 * C1) (hTS : T0 * S0 = 1)
    (hfact : T0 = Qp * Qmᵀ) (hT0symm : T0ᵀ = T0)
    (hB1 : B1 = Qpᵀ * H1 * Qp) :
    C1 = Qm * B1 * Qmᵀ := by
  have hsymm : Qp * Qmᵀ = Qm * Qpᵀ := by
    have h1 : (Qp * Qmᵀ)ᵀ = Qm * Qpᵀ := by
      rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    rw [← hfact, hT0symm, hfact] at h1
    exact h1
  have hC1 : C1 = T0 * H1 * T0 := oz1_C1_eq T0 S0 H1 C1 hoz hTS
  rw [hC1, hfact, hB1]
  rw [show Qp * Qmᵀ * H1 * (Qp * Qmᵀ) = (Qp * Qmᵀ) * H1 * Qp * Qmᵀ by
        simp only [Matrix.mul_assoc]]
  rw [hsymm]
  simp only [Matrix.mul_assoc]

/-! ### MRS.3 corollary — the DCF has no HS poles -/

/-- Entry expansion of the (★) triple product: `(A·B·Aᵀ) i j = ∑_q ∑_p A i p · B p q · A j q`. -/
theorem star_entry_eq {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) :
    (A * B * Aᵀ) i j = ∑ q, ∑ p, A i p * B p q * A j q := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]

/-- **MRS.3 corollary — `det Q̂₀`'s zeros never enter the DCF.**  Every entry of
`Ĉ₁(z) = Q̂₀(−z)·B₁(z)·Q̂₀ᵀ(−z)` is differentiable at `k` as soon as the entries of `Q̂₀(−·)` and
`B₁` are — **there is no hypothesis on `det Q̂₀` at all**, because (★) contains no inverse.  So a
zero of `det Q̂₀` (Group MZERO / the MML.8 HS-pole series) imposes **no** singularity on `Ĉ₁`: the
DCF's only poles are `B₁`'s Yukawa poles.  Contrast the RDF `Ĥ₁ = [Q̂₀ᵀ]⁻¹B₁[Q̂₀]⁻¹`, where the
inverses produce genuine double HS poles. -/
theorem star_entry_differentiableAt {N : ℕ} (Qfun B1fun : ℂ → Matrix (Fin N) (Fin N) ℂ) (k : ℂ)
    (hQ : ∀ p q, DifferentiableAt ℂ (fun z => Qfun z p q) k)
    (hB : ∀ p q, DifferentiableAt ℂ (fun z => B1fun z p q) k) (i j : Fin N) :
    DifferentiableAt ℂ (fun z => (Qfun z * B1fun z * (Qfun z)ᵀ) i j) k := by
  have hrw : (fun z => (Qfun z * B1fun z * (Qfun z)ᵀ) i j)
      = fun z => ∑ q, ∑ p, Qfun z i p * B1fun z p q * Qfun z j q := by
    funext z
    exact star_entry_eq (Qfun z) (B1fun z) i j
  rw [hrw]
  apply DifferentiableAt.fun_sum
  intro q _
  apply DifferentiableAt.fun_sum
  intro p _
  exact ((hQ i p).mul (hB p q)).mul (hQ j q)

/-- **MRS.3 corollary, concrete for the mixture Baxter matrix.**  For the actual `Ĉ₁(z) =
Q̂₀(−z)·B₁(z)·Q̂₀ᵀ(−z)` with `Q̂₀ = Q0_mat_c` (Y1.1), every entry is `DifferentiableAt` at any `k ≠ 0`
where `B₁` is — with **no hypothesis on `det Q̂₀`**.  The `Q̂₀(−·)` differentiability is discharged
from `q0_entry_c_differentiableAt` (holomorphy of the Baxter entries off `s = 0`) composed with
negation.  So the DCF's only possible singularities are `k = 0` (a removable point — `φ₁,φ₂` are
regular there, `phi1_tendsto`/`phi2_tendsto`) and `B₁`'s Yukawa poles: **the `det Q̂₀` zeros of Group
MZERO never appear.** -/
theorem starMix_entry_differentiableAt {N : ℕ} (sigma : Fin N → ℂ)
    (rho_geo Qp Qpp : Fin N → Fin N → ℂ) (B1fun : ℂ → Matrix (Fin N) (Fin N) ℂ) {k : ℂ}
    (hk : k ≠ 0) (hB : ∀ p q, DifferentiableAt ℂ (fun z => B1fun z p q) k) (i j : Fin N) :
    DifferentiableAt ℂ
      (fun z => (FMSA.Q0Complex.Q0_mat_c (-z) sigma rho_geo Qp Qpp * B1fun z
        * (FMSA.Q0Complex.Q0_mat_c (-z) sigma rho_geo Qp Qpp)ᵀ) i j) k := by
  refine star_entry_differentiableAt
    (fun z => FMSA.Q0Complex.Q0_mat_c (-z) sigma rho_geo Qp Qpp) B1fun k ?_ hB i j
  intro p q
  have hneg : DifferentiableAt ℂ (fun z : ℂ => -z) k := differentiableAt_id.neg
  have hentry := FMSA.MixtureHSPoles.q0_entry_c_differentiableAt (sigma p)
    ((sigma q - sigma p) / 2) (Qp p q) (Qpp p q) (rho_geo p q) (if p = q then 1 else 0)
    (neg_ne_zero.mpr hk)
  exact hentry.comp k hneg

/-! ### MRS.4 (first piece) — the `λ_ij` delta amplitude of `q'_ij`, and the ξ₂ cancellation

The real-space Baxter entry is the quadratic `Q₀ᵢⱼ·(t−Rᵢⱼ) + Q''ⱼ·(t−Rᵢⱼ)²/2` **windowed** on
`[λᵢⱼ, Rᵢⱼ]` (`q0MixEntry`, Y1.3a `WHSupports.lean`). At the *right* endpoint `t = Rᵢⱼ` the
quadratic vanishes, so the window closes continuously there; at the **left** endpoint `t = λᵢⱼ` it
does **not** — and that jump is precisely the **delta in `q'_ij`**.

⚠ **The MRS.4 trap:** modelling `q'` as a plain function on the *open* support silently drops this
delta and proves the wrong identity. The jump is real and its amplitude is computed below. -/

/-- At the window's left endpoint, `λᵢⱼ − Rᵢⱼ = −σᵢ` (`λᵢⱼ = (σⱼ−σᵢ)/2`, `Rᵢⱼ = (σᵢ+σⱼ)/2`). -/
theorem lam_sub_R_eq {N : ℕ} (sigma : Fin N → ℝ) (i j : Fin N) :
    (sigma j - sigma i) / 2 - (sigma i + sigma j) / 2 = -sigma i := by ring

/-- At the window's right endpoint the quadratic vanishes (`Rᵢⱼ − Rᵢⱼ = 0`) — so **no** delta at
`Rᵢⱼ`; the `λᵢⱼ` end is the only one that jumps. -/
theorem q0Mix_quad_at_R {N : ℕ} (rho sigma : Fin N → ℝ) (i j : Fin N) :
    FMSA.MatrixQ0.Q0phys rho sigma i j * ((sigma i + sigma j) / 2 - (sigma i + sigma j) / 2)
      + FMSA.MatrixQ0.Qppphys rho sigma i j
        * ((sigma i + sigma j) / 2 - (sigma i + sigma j) / 2) ^ 2 / 2 = 0 := by
  simp

/-- **MRS.4 — the `λ_ij` delta amplitude, and the ξ₂ cancellation.**  With the concrete
Lebowitz/Baxter PY mixture coefficients (`Q0phys`, `Qppphys`, `MatrixQ0.lean`), the jump of the
windowed quadratic at `t = λᵢⱼ` (where `λᵢⱼ − Rᵢⱼ = −σᵢ`, `lam_sub_R_eq`) is

    Q₀ᵢⱼ·(−σᵢ) + Q''ⱼ·(−σᵢ)²/2  =  −π·σᵢ·σⱼ / vac

**The `ξ₂` terms cancel exactly** — `Q₀ᵢⱼ` contributes `−π·ξ₂·σᵢ²·σⱼ/(4·vac)` and `Q''ⱼ` contributes
`+π·ξ₂·σⱼ·σᵢ²/(4·vac)`. In the `q_ij = (1/2π)[…]` normalization this is `−σᵢσⱼ/(2·vac)`, i.e. the
`−σᵢσⱼ/(2Δ)` of the MRS handoff (`Δ = vac = 1 − η`).  Note the amplitude is **symmetric in `i,j`** —
the input to MRS.4's delta-cancellation. -/
theorem q0Mix_jump_amplitude {N : ℕ} (rho sigma : Fin N → ℝ) (i j : Fin N)
    (hvac : FMSA.MatrixQ0.vacMix rho sigma ≠ 0) :
    FMSA.MatrixQ0.Q0phys rho sigma i j * (-sigma i)
      + FMSA.MatrixQ0.Qppphys rho sigma i j * (-sigma i) ^ 2 / 2
      = -(Real.pi * sigma i * sigma j / FMSA.MatrixQ0.vacMix rho sigma) := by
  unfold FMSA.MatrixQ0.Q0phys FMSA.MatrixQ0.Qppphys
  field_simp
  ring

/-- **MRS.4 — the delta amplitude is symmetric in `i, j`.**  `−π σᵢ σⱼ/vac` is manifestly
`i↔j`-symmetric; this is the algebraic input to the delta-cancellation in the `𝒬⁻ ⋆ ℬ ⋆ (𝒬⁻)ᵀ`
convolution (MRS.5), where the `q'_ij` and `q'_ji` deltas meet. -/
theorem q0Mix_jump_amplitude_symm {N : ℕ} (rho sigma : Fin N → ℝ) (i j : Fin N)
    (hvac : FMSA.MatrixQ0.vacMix rho sigma ≠ 0) :
    FMSA.MatrixQ0.Q0phys rho sigma i j * (-sigma i)
        + FMSA.MatrixQ0.Qppphys rho sigma i j * (-sigma i) ^ 2 / 2
      = FMSA.MatrixQ0.Q0phys rho sigma j i * (-sigma j)
        + FMSA.MatrixQ0.Qppphys rho sigma j i * (-sigma j) ^ 2 / 2 := by
  rw [q0Mix_jump_amplitude rho sigma i j hvac, q0Mix_jump_amplitude rho sigma j i hvac]
  ring

end FMSA.MRS
