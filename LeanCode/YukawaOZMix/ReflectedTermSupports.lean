/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.YukawaOZMix.MixtureConvolution
import LeanCode.Analysis.VolterraBanach

/-!
# The reflected ("parity") terms of the first-order OZ equation are anti-causal

**Source: Tang & Lu, *Mol. Phys.* **84**, 89–103 (1995), §2, Eqs. (9)–(14)** — the RDF derivation
itself, checked against the paper (`pdf/sources_paywall/Analytical solution of the Ornstein-Zernike
equation for mixtures.pdf`, journal pp. 92–94).  This file formalizes their **space-analysis step**,
i.e. the claim that the *time-reversed* terms carry no weight on `[R,∞)`.

## Why the terms exist at all — the two transforms

Two different transforms are in play, and Tang & Lu define both (p. 91 and p. 92):

| object | definition | what it is |
|---|---|---|
| `H̃(k)` | `(4π√(ρᵢρⱼ)/k)∫₀^∞ r h(r) sin(kr) dr` | the **physical** 3-D radial transform — a *sine* transform, i.e. the transform of the **odd** extension of `r·h(r)` |
| `Ĥ(k)` | `2π√(ρᵢρⱼ)∫₀^∞ r h(r) e^{−ikr} dr` | the **unilateral** transform — the working object of the Wiener–Hopf machinery |

They are **not equal**; the exact link (Tang & Lu p. 92) is

```
    H̃(k) = [Ĥ(−k) − Ĥ(k)]/(ik) ,        C̃(k) = [Ĉ(−k) − Ĉ(k)]/(ik) .
```

So `H̃` is (up to `1/(ik)`) the **odd part** of `Ĥ`; the *even* part `Ĥ(k) + Ĥ(−k)` is the
"even-function pseudo-trace" one might fear.  Substituting this exact link into the Baxter-transformed
first-order OZ equation is what *generates* the reflected partners: Tang & Lu's Eq. (10) reads

```
  Q̂₀ᵀ(k)Ĥ₁(k)Q̂₀(k) = Q̂₀ᵀ(k)Ĥ₁(−k)Q̂₀(k)                     ← RDF parity partner
                      + [Q̂₀(−k)]⁻¹U₁(k)[Q̂₀ᵀ(−k)]⁻¹            ← spans ℝ, must be split
                      + [Q̂₀(−k)]⁻¹S₁(k)[Q̂₀ᵀ(−k)]⁻¹            ← inner core
                      − [Q̂₀(−k)]⁻¹Ĉ₁(−k)[Q̂₀ᵀ(−k)]⁻¹ .         ← DCF parity partner
```

**The partners are explicit in the original.**  They are then disposed of by the space analysis
(p. 93): "the first, the third, and the fourth terms on the right-hand side of equation (10) lie
either in the space `[−∞,R]` or in its subspace", so only the `U₁` term contributes to `[R,∞)`, and
(p. 94) "the left-hand side … is in `[R,∞)` space, while the right-hand side … belongs to `[−∞,R]`
space.  Both sides should vanish."

## What this file proves

The disposal is **exact support arithmetic**, not an estimate — that is the content worth pinning:

* `support_comp_neg`, `reflected_support_Iic` — real-space reflection reverses the support, so
  `Ĥ₁(−k)` (the transform of the time-reversed `h₁`) is supported on `(−∞,−R]` once `h₁` is supported
  on `[R,∞)` (the *exact* hard-core condition `h₁ = 0` inside the core, valid at every order).
* `Icc_add_Iic_subset`, `Iic_add_Icc_subset`, `Iic_add_Iic_subset` — the Minkowski arithmetic that
  `support_convolution_subset` reduces the space analysis to.
* `reflected_rdf_conj_support` — **Proof 2, RDF half**: `Q̂₀ᵀ ⋆ h₁(−·) ⋆ Q̂₀` is supported on
  `(−∞, −λ_ij]`.
* `antiCausal_triple_support` — **Proof 2, conjugation half**: a triple convolution of anti-causally
  supported factors stays anti-causal; covers both the inner-core `S₁` term and the DCF parity
  partner `Ĉ₁(−k)`.
* `causal_projection_with_reflection` / `causal_projection_with_reflection_open` — the projection
  step with the partners **present** in the equation (Y1.3b's `causal_projection_real` had only the
  inner-core term): the conclusion `L = {T_U}^{[R,∞)}` is unchanged.
* `parity_partners_causal_projection_zero` — **the headline**: the causal projection of the parity
  partners is *identically zero*.  The artifact does not "converge to a small value"; it is
  annihilated exactly, because it lives on the reflected half-line.
* the closing `example` — non-vacuity **and** the point that the partner is genuinely nonzero: the
  witness has `Wrefl ≠ 0` while the conclusion still holds.  Annihilation is not smallness.

## Scope note (the endpoint)

Tang & Lu's two spaces are `[−∞,R]` and `[R,∞]` — closed on both sides, overlapping in the single
point `r = R`.  Accordingly the sharp statements here are either on the **open** half-line `(R,∞)`
(`…_open`, no strictness assumption needed) or under the strict hypothesis `support ⊆ (−∞,R)`.  For
like pairs `λ_ii = 0` the inner-core term's support bound is exactly `(−∞,R]`, so the open form is the
one that applies without extra assumptions; the endpoint is a single point (null set), which is why
the k-space presentation can ignore it.
-/

set_option linter.style.longLine false

open MeasureTheory Set
open scoped Convolution Pointwise

namespace FMSA.ReflectedSupports

/-! ### Reflection in real space -/

/-- **Real-space reflection reverses the support.**  `Ĥ₁(−k)` is the unilateral transform evaluated
at `−k`, i.e. the transform of the *time-reversed* function `r ↦ h₁(−r)`; this lemma is the support
half of that statement. -/
theorem support_comp_neg (f : ℝ → ℝ) :
    Function.support (fun r => f (-r)) = -Function.support f := by
  ext r
  simp only [Function.mem_support, Set.mem_neg]

/-- **The time-reversed first-order RDF is anti-causal.**  `h₁` vanishes inside the core at every
order (the exact hard-core condition `h^{(γ)}(r) = 0` for `r < R`, Tang & Lu p. 91), so `h₁` is
supported on `[R,∞)` and its reflection on `(−∞,−R]`. -/
theorem reflected_support_Iic {f : ℝ → ℝ} {R : ℝ} (h : Function.support f ⊆ Set.Ici R) :
    Function.support (fun r => f (-r)) ⊆ Set.Iic (-R) := by
  intro x hx
  have hx' : f (-x) ≠ 0 := hx
  have hmem := h hx'
  rw [Set.mem_Ici] at hmem
  rw [Set.mem_Iic]
  linarith

/-! ### Minkowski arithmetic for the anti-causal half-lines -/

/-- `[a,b] + (−∞,c] ⊆ (−∞, b+c]`. -/
theorem Icc_add_Iic_subset (a b c : ℝ) : Set.Icc a b + Set.Iic c ⊆ Set.Iic (b + c) := by
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_add.mp hz
  rw [Set.mem_Icc] at hx
  rw [Set.mem_Iic] at hy ⊢
  linarith [hx.2]

/-- `(−∞,a] + [b,c] ⊆ (−∞, a+c]`. -/
theorem Iic_add_Icc_subset (a b c : ℝ) : Set.Iic a + Set.Icc b c ⊆ Set.Iic (a + c) := by
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_add.mp hz
  rw [Set.mem_Iic] at hx ⊢
  rw [Set.mem_Icc] at hy
  linarith [hy.2]

/-- `(−∞,a] + (−∞,b] ⊆ (−∞, a+b]`. -/
theorem Iic_add_Iic_subset (a b : ℝ) : Set.Iic a + Set.Iic b ⊆ Set.Iic (a + b) := by
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_add.mp hz
  rw [Set.mem_Iic] at hx hy ⊢
  linarith

/-! ### Proof 2 — the two parity partners are anti-causally supported -/

/-- **Proof 2, RDF half** (Tang & Lu p. 93, "a similar analysis shows that the first … term … lies in
the space `[−∞,R]`").  The RDF parity partner `Q̂₀ᵀ(k)·Ĥ₁(−k)·Q̂₀(k)` is, in real space, the triple
convolution of the transposed Baxter factor (supported on `[−R,−λ]`), the **time-reversed** `h₁`
(supported on `(−∞,−R]` by `reflected_support_Iic`) and the Baxter factor (supported on `[λ,R]`).
Its support is therefore contained in `(−∞, −λ_ij]` — strictly to the left of the core for every
physical `λ_ij ≥ 0`. -/
theorem reflected_rdf_conj_support {qT q h1 : ℝ → ℝ} {R lam : ℝ}
    (hqT : Function.support qT ⊆ Set.Icc (-R) (-lam))
    (hq : Function.support q ⊆ Set.Icc lam R)
    (hh : Function.support h1 ⊆ Set.Ici R) :
    Function.support
        (((qT ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (fun r => h1 (-r)))
          ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] q))
      ⊆ Set.Iic (-lam) := by
  have hinner : Function.support (qT ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (fun r => h1 (-r)))
      ⊆ Set.Iic (-lam + -R) := by
    refine (support_convolution_subset (ContinuousLinearMap.mul ℝ ℝ)).trans ?_
    exact (Set.add_subset_add hqT (reflected_support_Iic hh)).trans
      (Icc_add_Iic_subset (-R) (-lam) (-R))
  refine (support_convolution_subset (ContinuousLinearMap.mul ℝ ℝ)).trans ?_
  refine (Set.add_subset_add hinner hq).trans ?_
  refine (Iic_add_Icc_subset (-lam + -R) lam R).trans ?_
  intro x hx
  rw [Set.mem_Iic] at hx ⊢
  linarith

/-- **Proof 2, conjugation half** (Tang & Lu p. 93, and [LN] Proof 2).  A triple convolution of three
anti-causally supported factors stays anti-causal.  This covers **both** remaining right-hand terms of
Eq. (10) at once, because `[Q̂₀(−k)]⁻¹` and `[Q̂₀ᵀ(−k)]⁻¹` are anti-causal in real space:

* the inner-core term `[Q̂₀(−k)]⁻¹·S₁(k)·[Q̂₀ᵀ(−k)]⁻¹` — take `b := R` (`S₁` is the transform of
  `r c₁(r)` on `[0,R] ⊆ (−∞,R]`);
* the **DCF parity partner** `[Q̂₀(−k)]⁻¹·Ĉ₁(−k)·[Q̂₀ᵀ(−k)]⁻¹` — take `b := 0` (the time-reversed
  `c₁`, supported on `(−∞,0]`). -/
theorem antiCausal_triple_support {A f B : ℝ → ℝ} {a b c : ℝ}
    (hA : Function.support A ⊆ Set.Iic a)
    (hf : Function.support f ⊆ Set.Iic b)
    (hB : Function.support B ⊆ Set.Iic c) :
    Function.support
        (((A ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] f)
          ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] B))
      ⊆ Set.Iic (a + b + c) := by
  have hinner : Function.support (A ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] f)
      ⊆ Set.Iic (a + b) :=
    (support_convolution_subset (ContinuousLinearMap.mul ℝ ℝ)).trans
      ((Set.add_subset_add hA hf).trans (Iic_add_Iic_subset a b))
  exact (support_convolution_subset (ContinuousLinearMap.mul ℝ ℝ)).trans
    ((Set.add_subset_add hinner hB).trans (Iic_add_Iic_subset (a + b) c))

/-! ### The projection step, with the parity partners present -/

/-- **The causal projection annihilates a parity partner — identically.**  This is the statement in
its sharpest form: a term supported on `(−∞,R)` has *zero* causal projection.  Not "small", not
"convergent to zero": zero. -/
theorem parity_partners_causal_projection_zero {M : Type*} [AddCommMonoid M]
    {W : ℝ → M} {R : ℝ} (hW : Function.support W ⊆ Set.Iio R) :
    Set.indicator (Set.Ici R) W = 0 := by
  funext r
  by_cases hr : r ∈ Set.Ici R
  · rw [Set.indicator_of_mem hr]
    by_contra h
    have hmem := hW (Function.mem_support.mpr h)
    rw [Set.mem_Iio] at hmem
    rw [Set.mem_Ici] at hr
    exact absurd hmem (not_lt.mpr hr)
  · rw [Set.indicator_of_notMem hr]
    rfl

/-- **Tang & Lu Eq. (10) → Eq. (14), with the parity partners kept.**  Y1.3b's
`causal_projection_real` splits `L = T_U + T_S`; the *original* equation has two further terms, the
RDF and DCF parity partners.  Keeping them changes nothing: they are anti-causal, so the causal part
of the equation is still `L = {T_U}^{[R,∞)}`.

This is the formal content of "the even-function pseudo-trace cannot contaminate `B₁`". -/
theorem causal_projection_with_reflection {M : Type*} [AddCommMonoid M]
    {L TU TS Wrefl Wcrefl : ℝ → M} {R : ℝ}
    (hOZ : ∀ r, L r = TU r + TS r + Wrefl r + Wcrefl r)
    (hL : Function.support L ⊆ Set.Ici R)
    (hTS : Function.support TS ⊆ Set.Iio R)
    (hWrefl : Function.support Wrefl ⊆ Set.Iio R)
    (hWcrefl : Function.support Wcrefl ⊆ Set.Iio R) :
    L = Set.indicator (Set.Ici R) TU := by
  funext r
  by_cases hr : r ∈ Set.Ici R
  · have hzero : ∀ F : ℝ → M, Function.support F ⊆ Set.Iio R → F r = 0 := by
      intro F hF
      by_contra h
      have hmem := hF (Function.mem_support.mpr h)
      rw [Set.mem_Iio] at hmem
      rw [Set.mem_Ici] at hr
      exact absurd hmem (not_lt.mpr hr)
    rw [Set.indicator_of_mem hr, hOZ r, hzero TS hTS, hzero Wrefl hWrefl, hzero Wcrefl hWcrefl,
      add_zero, add_zero, add_zero]
  · have hLr : L r = 0 := by
      by_contra h
      exact hr (hL (Function.mem_support.mpr h))
    rw [Set.indicator_of_notMem hr, hLr]

/-- **The endpoint-free form.**  Tang & Lu's two spaces `[−∞,R]` and `[R,∞]` are both closed and
overlap at the single point `r = R`; for like pairs (`λ_ii = 0`) the inner-core term's support bound
is exactly `(−∞,R]`.  On the **open** half-line `(R,∞)` no strictness hypothesis is needed and the
conclusion is the pointwise identity `L = T_U`. -/
theorem causal_projection_with_reflection_open {M : Type*} [AddCommMonoid M]
    {L TU TS Wrefl Wcrefl : ℝ → M} {R : ℝ}
    (hOZ : ∀ r, L r = TU r + TS r + Wrefl r + Wcrefl r)
    (hTS : Function.support TS ⊆ Set.Iic R)
    (hWrefl : Function.support Wrefl ⊆ Set.Iic R)
    (hWcrefl : Function.support Wcrefl ⊆ Set.Iic R) :
    ∀ r, R < r → L r = TU r := by
  intro r hr
  have hzero : ∀ F : ℝ → M, Function.support F ⊆ Set.Iic R → F r = 0 := by
    intro F hF
    by_contra h
    have hmem := hF (Function.mem_support.mpr h)
    rw [Set.mem_Iic] at hmem
    exact absurd hmem (not_le.mpr hr)
  rw [hOZ r, hzero TS hTS, hzero Wrefl hWrefl, hzero Wcrefl hWcrefl, add_zero, add_zero, add_zero]

/-- **Non-vacuity — and the point.**  The hypothesis cluster is satisfiable with the parity partner
`Wrefl` **genuinely nonzero** (and `L`, `TU` nonzero): the annihilation is a statement about *where*
the partner lives, not about its size.  (Numerically the analogous reflected term on the DCF side is
an `O(1)` effect — the C++ port's `reflection` razor moves by 107 % when it is dropped — so a witness
in which the partner vanished would prove nothing.) -/
example {R : ℝ} :
    ∃ (L TU TS Wrefl Wcrefl : ℝ → ℝ),
      (∀ r, L r = TU r + TS r + Wrefl r + Wcrefl r) ∧
        Function.support L ⊆ Set.Ici R ∧
        Function.support TS ⊆ Set.Iio R ∧
        Function.support Wrefl ⊆ Set.Iio R ∧
        Function.support Wcrefl ⊆ Set.Iio R ∧
        L = Set.indicator (Set.Ici R) TU ∧
        Wrefl ≠ 0 ∧ L ≠ 0 := by
  classical
  have hsupp : ∀ (s : Set ℝ) (c : ℝ), Function.support (Set.indicator s (fun _ => c)) ⊆ s := by
    intro s c x hx
    by_contra hns
    exact hx (Set.indicator_of_notMem hns _)
  refine ⟨Set.indicator (Set.Ici R) (fun _ => (1 : ℝ)),
    Set.indicator (Set.Ici R) (fun _ => (1 : ℝ)) + Set.indicator (Set.Iio R) (fun _ => (1 : ℝ)),
    0, -Set.indicator (Set.Iio R) (fun _ => (1 : ℝ)), 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r; simp
  · exact hsupp _ _
  · simp
  · rw [Function.support_neg]
    exact hsupp _ _
  · simp
  · funext r
    by_cases hr : r ∈ Set.Ici R
    · have hnot : r ∉ Set.Iio R := by
        rw [Set.mem_Ici] at hr; rw [Set.mem_Iio]; exact not_lt.mpr hr
      simp [Set.indicator_of_mem hr, Set.indicator_of_notMem hnot]
    · simp [Set.indicator_of_notMem hr]
  · intro h
    have := congrFun h (R - 1)
    have hmem : (R - 1) ∈ Set.Iio R := by rw [Set.mem_Iio]; linarith
    simp [Set.indicator_of_mem hmem] at this
  · intro h
    have := congrFun h R
    have hmem : R ∈ Set.Ici R := le_refl R
    simp [Set.indicator_of_mem hmem] at this

/-! ### Y1.3a — discharging the atomic supports, so nothing above is assumed

The lemmas so far take the atomic supports as hypotheses.  This section supplies them from the
project's own `Mix` real-space data plus **one** physical statement (the hard-core condition), so the
annihilation is not conditional on unformalized support claims.

Three of the four atoms are constructive; the fourth (the inverse Baxter factors) is anti-causal
term-by-term, with the *sum* inheriting it modulo the same `L¹` convergence input that PYE.4 already
names — see `convIter_support_subset` and the note under it. -/

open FMSA.InnerDecomp FMSA.WHSupports

/-- **The transposed Baxter factor** `{Q̂₀ᵀ}_{ij}` in real space.  Transposition is `r → −r`
(Tang & Lu p. 92; [LN] Proof 1 "the transposed `Q₀ᵀ` is supported on `[−R_ij, −λ_ij]` since
transposition corresponds to `r → −r` in real space").  This is the atom Y1.3a did **not** have —
`WHSupports` supplies only the untransposed `q0MixEntry`. -/
noncomputable def q0MixEntryRefl {N M : ℕ} (X : Mix N M) (i j : Fin N) (r : ℝ) : ℝ :=
  X.q0MixEntry i j (-r)

/-- **[LN] Proof 1 / Tang & Lu p. 93, transposed atom.**  `{Q̂₀ᵀ}_{ij}` is supported on
`[−R_ij, −λ_ij]` — the reflection of `q0MixEntry`'s `[λ_ij, R_ij]`. -/
theorem q0MixEntryRefl_support_subset {N M : ℕ} (X : Mix N M) (i j : Fin N) :
    Function.support (q0MixEntryRefl X i j) ⊆ Set.Icc (-(X.R i j)) (-(X.lam i j)) := by
  intro x hx
  have hx' : X.q0MixEntry i j (-x) ≠ 0 := hx
  have hmem := X.q0MixEntry_support_subset i j hx'
  rw [Set.mem_Icc] at hmem
  rw [Set.mem_Icc]
  constructor <;> linarith [hmem.1, hmem.2]

/-- **The hard-core condition, as a support statement.**  Tang & Lu p. 91: `h^{(γ)}_{ij}(r) = 0` for
`r < R_ij` at every order `γ ≥ 1` — *exact*, not an approximation (it is the additive hard core, not
a closure).  This elementary bridge is what turns that physical statement into the hypothesis the
annihilation theorems consume. -/
theorem support_subset_Ici_of_hardCore {f : ℝ → ℝ} {R : ℝ} (h : ∀ r, r < R → f r = 0) :
    Function.support f ⊆ Set.Ici R := by
  intro x hx
  rw [Set.mem_Ici]
  by_contra hlt
  push_neg at hlt
  exact hx (h x hlt)

/-- **The inner-core window, as a support statement.**  `S₁` is by *definition* the transform of
`r c₁(r)` restricted to `[0, R_ij]` (Tang & Lu Eq. (10)'s split `Ĉ₁ = U₁ + S₁`), so its real-space
amplitude vanishes off that window. -/
theorem support_subset_Icc_of_window {f : ℝ → ℝ} {a b : ℝ}
    (h : ∀ r, r < a ∨ b < r → f r = 0) : Function.support f ⊆ Set.Icc a b := by
  intro x hx
  rw [Set.mem_Icc]
  refine ⟨?_, ?_⟩
  · by_contra hlt
    push_neg at hlt
    exact hx (h x (Or.inl hlt))
  · by_contra hgt
    push_neg at hgt
    exact hx (h x (Or.inr hgt))

/-- **The mixed-index edge identity.**  For the index chain `i → m → n → j` the three atomic edges
combine as `−λ_im + (−R_mn) + R_nj = R_ij − σ_m`: the intermediate species `n` cancels completely and
`m` survives only as the *margin* `σ_m`.  (Contact algebra `R_ab = (σ_a+σ_b)/2`,
`λ_ab = (σ_b−σ_a)/2` — the same cancellation pattern as `MixtureConvolution.pbp_edge_eq`.) -/
theorem reflected_rdf_edge_eq {N M : ℕ} (X : Mix N M) (i m n j : Fin N) :
    -(X.lam i m) + -(X.R m n) + X.R n j = X.R i j - X.sigma m := by
  simp only [HSMix.R, HSMix.lam]
  ring

/-- **Y1.3a discharged — the RDF parity partner, from physics only.**  For the index chain
`i → m → n → j`, `{Q̂₀ᵀ}_{im} ⋆ h₁_{mn}(−·) ⋆ {Q̂₀}_{nj}` is supported on `(−∞, R_ij − σ_m]`.  The only
input is the hard-core condition on `h₁_{mn}`; both Baxter atoms come from `WHSupports` + the
reflection lemma above.

The bound is **strictly** left of contact by the intermediate species' diameter `σ_m > 0`
(`Mix.hσ` — the structure's only physical axiom), which is why the next lemma can conclude vanishing
on the *closed* half-line `[R_ij, ∞)` with room to spare. -/
theorem reflected_rdf_conj_support_physical {N M : ℕ} (X : Mix N M) (i m n j : Fin N) (h1 : ℝ → ℝ)
    (hhard : ∀ r, r < X.R m n → h1 r = 0) :
    Function.support
        ((q0MixEntryRefl X i m ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (fun r => h1 (-r)))
          ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (X.q0MixEntry n j))
      ⊆ Set.Iic (X.R i j - X.sigma m) := by
  have hinner : Function.support
      (q0MixEntryRefl X i m ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (fun r => h1 (-r)))
      ⊆ Set.Iic (-(X.lam i m) + -(X.R m n)) := by
    refine (support_convolution_subset (ContinuousLinearMap.mul ℝ ℝ)).trans ?_
    exact (Set.add_subset_add (q0MixEntryRefl_support_subset X i m)
      (reflected_support_Iic (support_subset_Ici_of_hardCore hhard))).trans
      (Icc_add_Iic_subset (-(X.R i m)) (-(X.lam i m)) (-(X.R m n)))
  refine (support_convolution_subset (ContinuousLinearMap.mul ℝ ℝ)).trans ?_
  refine (Set.add_subset_add hinner (X.q0MixEntry_support_subset n j)).trans ?_
  refine (Iic_add_Icc_subset (-(X.lam i m) + -(X.R m n)) (X.lam n j) (X.R n j)).trans ?_
  rw [reflected_rdf_edge_eq X i m n j]

/-- **The RDF parity partner vanishes on the whole closed causal half-line `[R_ij, ∞)`.**  Not merely
on the open one: the margin `σ_m > 0` of `reflected_rdf_conj_support_physical` covers the endpoint
that Tang & Lu's overlapping spaces `[−∞,R]`/`[R,∞]` share.  So the "even pseudo-trace" contributes
nothing to `B₁` — with room to spare, from physics inputs only. -/
theorem reflected_rdf_conj_eq_zero_of_contact_le {N M : ℕ} (X : Mix N M) (i m n j : Fin N)
    (h1 : ℝ → ℝ) (hhard : ∀ r, r < X.R m n → h1 r = 0) {x : ℝ} (hx : X.R i j ≤ x) :
    ((q0MixEntryRefl X i m ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (fun r => h1 (-r)))
      ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (X.q0MixEntry n j)) x = 0 := by
  by_contra hne
  have hmem := reflected_rdf_conj_support_physical X i m n j h1 hhard hne
  rw [Set.mem_Iic] at hmem
  have hpos : 0 < X.sigma m := X.hsigma m
  linarith

/-! #### The fourth atom: the inverse Baxter factors -/

/-- Convolution iterates `A, A⋆A, A⋆A⋆A, …` — the Neumann terms of `[Q̂₀(−k)]⁻¹ = I + A + A⋆A + ⋯`
(`δ` is not a function, so the identity term is left implicit and the iteration starts at `A`). -/
noncomputable def convIter (A : ℝ → ℝ) : ℕ → (ℝ → ℝ)
  | 0 => A
  | (n + 1) => A ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (convIter A n)

/-- **Every Neumann term of an anti-causal kernel is anti-causal, with the *same* bound.**  If
`support A ⊆ (−∞,a]` with `a ≤ 0`, then every iterate stays in `(−∞,a]` — the edge `n·a` only moves
further left.  This is the support half of "`[Q̂₀(−k)]⁻¹` is anti-causal" ([LN] Proof 2/3, Tang & Lu's
appendix inverse).

**What is *not* proved here, and why it is the right place to stop.**  Passing from the terms to the
*sum* needs the Neumann series to converge in `L¹` — i.e. exactly the causal-algebra Wiener `1/f`
input that this project keeps as MA.13 (`wiener_causal_resolvent`) / MA.15, and that Group PYE names
as `WHProjectionL1`.  It is one gap, not two: the same missing theorem serves both. -/
theorem convIter_support_subset {A : ℝ → ℝ} {a : ℝ} (ha : a ≤ 0)
    (hA : Function.support A ⊆ Set.Iic a) (n : ℕ) :
    Function.support (convIter A n) ⊆ Set.Iic a := by
  induction n with
  | zero => simpa [convIter] using hA
  | succ k ih =>
      have hstep : Function.support (A ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (convIter A k))
          ⊆ Set.Iic (a + a) :=
        (support_convolution_subset (ContinuousLinearMap.mul ℝ ℝ)).trans
          ((Set.add_subset_add hA ih).trans (Iic_add_Iic_subset a a))
      intro x hx
      have hx' : x ∈ Set.Iic (a + a) := hstep hx
      rw [Set.mem_Iic] at hx' ⊢
      linarith

/-! ### Closing the chain: the inverse Baxter factor, **without** MA.13

The fourth atom asked for the inverse Baxter factor's kernel to be anti-causal, and the obvious route
— the Neumann series `I + A + A⋆A + ⋯` — **diverges** in the physical regime (`‖q‖₁ > 1`; that is
exactly why MA.13 `wiener_causal_resolvent` is a kept axiom).  It does not follow that the support
statement needs MA.13, and it does not:

> **The support question is *local*, and locally the renewal equation is unconditionally solvable.**

The resolvent is characterized by the renewal (Volterra) equation `R = q + q ⋆ R` rather than by the
series, and MA.10 — **proved, axiom-free** (`Analysis/Volterra.lean`, `Analysis/VolterraBanach.lean`)
— gives existence *and* uniqueness on every window `[0,b]` with **no smallness hypothesis**: the
factorial iterate bound `Mⁿ(b−a)ⁿ/n!` beats any `‖q‖₁`.  `volterraGlobalE` glues the windows into a
half-line solution that is **zero off `[0,∞)` by construction**.

So the two remaining terms of Tang & Lu Eq. (10) — the inner-core `S₁` term and the DCF parity
partner — get their anti-causality from MA.10, and MA.13 is **not on this path**.  (MA.13 is what the
*global `L¹`* resolvent needs — the decay/pole statements of `POLE.11` — a strictly stronger claim
than "supported on a half-line".)

What remains is a *dictionary* item, not analysis: that the physical `[Q̂₀(−k)]⁻¹` is `δ + R` with `R`
the renewal solution.  That is the real-space reading of `Q̂₀·Q̂₀⁻¹ = I` — algebra plus the transform
correspondence, recorded as the hypothesis shape of `antiCausal_conj_delta_support` below. -/

/-- **The causal renewal resolvent**, from MA.10: the unique solution of `R = q + q ⋆ R` on `[0,∞)`,
extended by `0` to the left.  No smallness hypothesis on `q` — see the section note. -/
noncomputable def renewalResolvent (q : ℝ → ℝ) (hq : Continuous q) : ℝ → ℝ :=
  FMSA.VolterraBanach.volterraGlobalE (0 : ℝ) q q hq hq

/-- **The resolvent is causal by construction** — `volterraGlobalE` is literally `0` off `[0,∞)`.
This is the step that the divergent Neumann series could not supply. -/
theorem renewalResolvent_support (q : ℝ → ℝ) (hq : Continuous q) :
    Function.support (renewalResolvent q hq) ⊆ Set.Ici 0 := by
  intro x hx
  by_contra hns
  rw [Set.mem_Ici] at hns
  push_neg at hns
  exact hx (by
    simp only [renewalResolvent, FMSA.VolterraBanach.volterraGlobalE, dif_neg (not_le.mpr hns)])

/-- The resolvent satisfies the renewal equation at every `r ≥ 0` (MA.10's `volterraGlobalE_spec`) —
recorded so that the object above is pinned by its equation, not merely by its construction. -/
theorem renewalResolvent_spec (q : ℝ → ℝ) (hq : Continuous q) {r : ℝ} (hr : 0 ≤ r) :
    renewalResolvent q hq r
      = q r + ∫ t in (0:ℝ)..r, q (r - t) * renewalResolvent q hq t :=
  FMSA.VolterraBanach.volterraGlobalE_spec (0 : ℝ) q q hq hq hr

/-- The **anti-causal** mirror — the orientation the Baxter inverse `[Q̂₀(−k)]⁻¹` actually has. -/
noncomputable def renewalResolventRefl (q : ℝ → ℝ) (hq : Continuous q) : ℝ → ℝ :=
  fun x => renewalResolvent q hq (-x)

/-- The mirrored resolvent is anti-causal: `support ⊆ (−∞, 0]`. -/
theorem renewalResolventRefl_support (q : ℝ → ℝ) (hq : Continuous q) :
    Function.support (renewalResolventRefl q hq) ⊆ Set.Iic 0 := by
  have h := reflected_support_Iic (R := (0:ℝ)) (renewalResolvent_support q hq)
  simpa [renewalResolventRefl] using h

/-- **Conjugation by `δ + (anti-causal)` preserves `(−∞,b]`.**  Writing the inverse Baxter factors as
`δ + A` and `δ + B` with `A`, `B` anti-causal (`renewalResolventRefl_support`), the product
`(δ+A) ⋆ f ⋆ (δ+B)` expands into the four displayed terms, and each stays in `(−∞,b]` when `f` does.

Applied with `f := S₁` (`b := R_ij`) and with `f := ` the time-reversed `c₁` (`b := 0`), this is what
puts the last two terms of Tang & Lu Eq. (10) on the anti-causal side — now from MA.10 rather than
from an assumption. -/
theorem antiCausal_conj_delta_support {A f B : ℝ → ℝ} {b : ℝ}
    (hA : Function.support A ⊆ Set.Iic 0)
    (hf : Function.support f ⊆ Set.Iic b)
    (hB : Function.support B ⊆ Set.Iic 0) :
    Function.support (fun x => f x
        + (A ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] f) x
        + (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] B) x
        + (A ⋆[ContinuousLinearMap.mul ℝ ℝ, volume]
            (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] B)) x)
      ⊆ Set.Iic b := by
  have hAf : Function.support (A ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] f) ⊆ Set.Iic b := by
    refine (support_convolution_subset (ContinuousLinearMap.mul ℝ ℝ)).trans ?_
    exact (Set.add_subset_add hA hf).trans (by simpa using Iic_add_Iic_subset 0 b)
  have hfB : Function.support (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] B) ⊆ Set.Iic b := by
    refine (support_convolution_subset (ContinuousLinearMap.mul ℝ ℝ)).trans ?_
    exact (Set.add_subset_add hf hB).trans (by simpa using Iic_add_Iic_subset b 0)
  have hAfB : Function.support (A ⋆[ContinuousLinearMap.mul ℝ ℝ, volume]
      (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] B)) ⊆ Set.Iic b := by
    refine (support_convolution_subset (ContinuousLinearMap.mul ℝ ℝ)).trans ?_
    exact (Set.add_subset_add hA hfB).trans (by simpa using Iic_add_Iic_subset 0 b)
  intro x hx
  by_contra hns
  rw [Set.mem_Iic] at hns
  push_neg at hns
  have h1 : f x = 0 := by
    by_contra h; exact absurd (hf h) (by simp [Set.mem_Iic]; linarith)
  have h2 : (A ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] f) x = 0 := by
    by_contra h; exact absurd (hAf h) (by simp [Set.mem_Iic]; linarith)
  have h3 : (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] B) x = 0 := by
    by_contra h; exact absurd (hfB h) (by simp [Set.mem_Iic]; linarith)
  have h4 : (A ⋆[ContinuousLinearMap.mul ℝ ℝ, volume]
      (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] B)) x = 0 := by
    by_contra h; exact absurd (hAfB h) (by simp [Set.mem_Iic]; linarith)
  exact hx (by simp [h1, h2, h3, h4])

/-- **Chain closed.**  With the inverse Baxter factors given by MA.10's renewal resolvent, *all three*
anti-causal terms of Tang & Lu Eq. (10) are supported in `(−∞, R_ij]`, so the causal projection of the
equation is `L = {T_U}^{[R,∞)}` — with **no** appeal to MA.13, and (for the RDF parity partner) no
appeal to the inverse at all. -/
theorem eq10_antiCausal_side {q1 q2 : ℝ → ℝ} (hq1 : Continuous q1) (hq2 : Continuous q2)
    {S1 crefl : ℝ → ℝ} {R : ℝ} (hR : 0 ≤ R)
    (hS1 : Function.support S1 ⊆ Set.Iic R)
    (hcrefl : Function.support crefl ⊆ Set.Iic 0) :
    Function.support (fun x => S1 x
        + (renewalResolventRefl q1 hq1 ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] S1) x
        + (S1 ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] renewalResolventRefl q2 hq2) x
        + (renewalResolventRefl q1 hq1 ⋆[ContinuousLinearMap.mul ℝ ℝ, volume]
            (S1 ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] renewalResolventRefl q2 hq2)) x)
      ⊆ Set.Iic R ∧
    Function.support (fun x => crefl x
        + (renewalResolventRefl q1 hq1 ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] crefl) x
        + (crefl ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] renewalResolventRefl q2 hq2) x
        + (renewalResolventRefl q1 hq1 ⋆[ContinuousLinearMap.mul ℝ ℝ, volume]
            (crefl ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] renewalResolventRefl q2 hq2)) x)
      ⊆ Set.Iic R :=
  ⟨antiCausal_conj_delta_support (renewalResolventRefl_support q1 hq1) hS1
      (renewalResolventRefl_support q2 hq2),
   (antiCausal_conj_delta_support (renewalResolventRefl_support q1 hq1) hcrefl
      (renewalResolventRefl_support q2 hq2)).trans
      (fun x hx => le_trans (Set.mem_Iic.mp hx) hR)⟩

end FMSA.ReflectedSupports
