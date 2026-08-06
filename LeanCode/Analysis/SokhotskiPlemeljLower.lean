/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import LeanCode.Analysis.SokhotskiPlemelj

/-!
# Sokhotski–Plemelj lower boundary value + the jump (Tang & Lu eq (14)'s `½[…]` term)

Item (b) of the eq (20) residue programme: the on-contour `y = k` real-axis pole.  The contour-sum
engine needs the Cauchy pole off the real axis; the leading-term work (`MixtureYukawaContourTerm`)
placed `k` in the *open lower* half-plane (`Im k < 0`), so the physical real-`k` value is the
**lower** boundary limit `Im k → 0⁻`.  The project's `SokhotskiPlemelj.lean` states only the upper
axiom (`sokhotski_plemelj_upper`, pole approaching from above ⇒ `P.V. + iπ·g(x₀)`); this file adds
the two pieces (b) actually needs, both derived — **no new axiom** (only `sokhotski_plemelj_upper`):

* `sokhotski_plemelj_lower` — the lower boundary value `P.V. − iπ·g(x₀)`, obtained from the upper
  axiom by **conjugation** (`f := conj ∘ g`, then conjugate the whole `Tendsto`; `conj` commutes
  with the integral (`integral_conj`), turns the lower kernel `1/(x−x₀+iε)` into the upper
  `1/(x−x₀−iε)`, and flips the `+iπ` to `−iπ`).  This is the derivation the axiom's docstring flags
  as the intended way to get the lower version.

* `sokhotski_plemelj_jump` — the **jump** `[upper] − [lower] = 2πi·g(x₀)`, i.e. the full residue of
  `g(x)/(x−x₀)` at the on-contour pole; each boundary carries the `±iπ·g(x₀)` half.  This is the
  algebraic content of Tang & Lu eq (14)'s `½[Q̂₀(−k)]⁻¹U₁(k)[Q̂₀ᵀ(−k)]⁻¹` boundary term — the `½`
  of that full residue — which, added to the closed-contour Yukawa-pole residue sum, reproduces the
  principal-value integral of eq (14).
-/

open MeasureTheory Set Complex Filter Topology

/-- **Sokhotski–Plemelj (lower boundary value).**  Derived from `sokhotski_plemelj_upper` by
conjugation: for `g` integrable, continuous at `x₀`, with principal value `L`, approaching the real
axis from *below* (`x₀ − iε`, i.e. the kernel `1/(x − x₀ + iε)`, `ε → 0⁺`) gives `L − iπ·g(x₀)`. -/
theorem sokhotski_plemelj_lower {g : ℝ → ℂ} {x0 : ℝ} {L : ℂ}
    (hgi : Integrable g) (hgc : ContinuousAt g x0)
    (hpv : Tendsto (fun δ : ℝ => ∫ x in {x : ℝ | δ ≤ |x - x0|}, g x / ((x : ℂ) - (x0 : ℂ)))
      (𝓝[>] 0) (𝓝 L)) :
    Tendsto (fun ε : ℝ => ∫ x : ℝ, g x / ((x : ℂ) - (x0 : ℂ) + Complex.I * (ε : ℂ)))
      (𝓝[>] 0) (𝓝 (L - Real.pi * Complex.I * g x0)) := by
  -- apply the upper axiom to the conjugate function `conj ∘ g`
  have hfi : Integrable (fun x => (starRingEnd ℂ) (g x)) :=
    hgi.norm.mono' (Complex.continuous_conj.comp_aestronglyMeasurable hgi.1)
      (Filter.Eventually.of_forall (fun x => le_of_eq (RCLike.norm_conj (g x))))
  have hfc : ContinuousAt (fun x => (starRingEnd ℂ) (g x)) x0 :=
    Complex.continuous_conj.continuousAt.comp hgc
  have hpvc : Tendsto (fun δ : ℝ => ∫ x in {x : ℝ | δ ≤ |x - x0|},
      (starRingEnd ℂ) (g x) / ((x : ℂ) - (x0 : ℂ))) (𝓝[>] 0) (𝓝 ((starRingEnd ℂ) L)) := by
    have hpveq : (fun δ : ℝ => ∫ x in {x : ℝ | δ ≤ |x - x0|},
          (starRingEnd ℂ) (g x) / ((x : ℂ) - (x0 : ℂ)))
        = (fun δ : ℝ => (starRingEnd ℂ)
            (∫ x in {x : ℝ | δ ≤ |x - x0|}, g x / ((x : ℂ) - (x0 : ℂ)))) := by
      funext δ
      rw [← integral_conj]
      refine setIntegral_congr_fun (by measurability) (fun x _ => ?_)
      rw [map_div₀]; congr 1; simp [Complex.conj_ofReal]
    rw [hpveq]
    exact (Complex.continuous_conj.tendsto L).comp hpv
  have hup := sokhotski_plemelj_upper hfi hfc hpvc
  -- conjugate both sides: `conj` turns the upper kernel into the lower one and `+iπ` into `−iπ`
  have hconj := (Complex.continuous_conj.tendsto _).comp hup
  have hfunpt : ∀ ε : ℝ, (starRingEnd ℂ)
      (∫ x : ℝ, (starRingEnd ℂ) (g x) / ((x : ℂ) - (x0 : ℂ) - Complex.I * (ε : ℂ)))
      = ∫ x : ℝ, g x / ((x : ℂ) - (x0 : ℂ) + Complex.I * (ε : ℂ)) := by
    intro ε
    rw [← integral_conj]
    congr 1
    funext x
    rw [map_div₀, Complex.conj_conj]
    congr 1
    simp [map_sub, map_mul, Complex.conj_I, Complex.conj_ofReal]
  have hval : (starRingEnd ℂ) ((starRingEnd ℂ) L + Real.pi * Complex.I * (starRingEnd ℂ) (g x0))
      = L - Real.pi * Complex.I * g x0 := by
    simp only [map_add, map_mul, Complex.conj_conj, Complex.conj_I, Complex.conj_ofReal]
    ring
  rw [hval] at hconj
  exact Filter.Tendsto.congr (fun ε => by rw [Function.comp_apply]; exact hfunpt ε) hconj

/-- **The Sokhotski–Plemelj jump — the on-contour pole's full residue.**  The difference of the two
boundary values is `2πi·g(x₀)`, the full residue of `g(x)/(x−x₀)` at the on-contour pole; each side
carries the `±iπ·g(x₀)` half.  This is the algebraic content of Tang & Lu eq (14)'s `½[…]` boundary
term — the `½` of that full residue. -/
theorem sokhotski_plemelj_jump {g : ℝ → ℂ} {x0 : ℝ} {L : ℂ}
    (hgi : Integrable g) (hgc : ContinuousAt g x0)
    (hpv : Tendsto (fun δ : ℝ => ∫ x in {x : ℝ | δ ≤ |x - x0|}, g x / ((x : ℂ) - (x0 : ℂ)))
      (𝓝[>] 0) (𝓝 L)) :
    Tendsto (fun ε : ℝ => (∫ x : ℝ, g x / ((x : ℂ) - (x0 : ℂ) - Complex.I * (ε : ℂ)))
        - (∫ x : ℝ, g x / ((x : ℂ) - (x0 : ℂ) + Complex.I * (ε : ℂ))))
      (𝓝[>] 0) (𝓝 (2 * Real.pi * Complex.I * g x0)) := by
  have hsub := (sokhotski_plemelj_upper hgi hgc hpv).sub (sokhotski_plemelj_lower hgi hgc hpv)
  rw [show L + Real.pi * Complex.I * g x0 - (L - Real.pi * Complex.I * g x0)
      = 2 * Real.pi * Complex.I * g x0 from by ring] at hsub
  exact hsub
