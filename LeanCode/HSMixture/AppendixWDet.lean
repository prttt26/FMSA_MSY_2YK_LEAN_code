/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import LeanCode.HSMixture.ArcAmplitudeBound

/-!
# Tang & Lu explicit Appendix `W`/`det` formulas (the `A(−iy)` amplitude)

The (iii) assembly logic (`HSMixture/ArcAmplitudeBound`) bounds the `A(−iy)` amplitude
`c·W/(Δ·det)` once concrete `‖W(−iy)‖ ≤ Wb` and `‖det(−iy) − 1‖ ≤ d` are supplied.  Those come from
Tang & Lu's **explicit Appendix formulas** — introduced here (they were not previously in the
project, whose Baxter machinery is Woodbury-based).  With `s = ik = −iy`:

* `phi1 s R = (1 − sR − e^{−sR})/s²`, `phi2 s R = (1 − sR + (sR)²/2 − e^{−sR})/s³` — the removable
  functions `φ₁`, `φ₂`; `norm_phi1_le`/`norm_phi2_le` give the arc decay `≤ (…)/‖s‖ → 0`
  (specialising `normP2_arc_decay`/`normP3_arc_decay` at `σ = R`).
* `xiMom ρ R i = ∑ₘ ρₘ Rₘⁱ` (`ξᵢ`), `Delta ρ R = 1 − (π/6)ξ₃` (`Δ`).
* `Wtl s ρ R i j`, `detTL s ρ R` — the exact `Wᵢⱼ(ik)`, `det(ik)` of Tang & Lu p. 95, finite
  `ρ`-weighted sums/products of `φ₁`, `φ₂`.

`norm_weighted_phi1_sum_le` / `norm_weighted_phi2_sum_le` bound any finite `ρ`-weighted `φ`-sum
(the shape of every `W`/`det` term) by `(…)/‖s‖ → 0` — the reusable tool for `‖Wtl‖ → 0` and
`‖detTL − 1‖ → 0`, which then feed `norm_ge_of_norm_sub_one_le` + `amplitude_norm_le`.

**Remaining to close the A-term arc bound:** (1) the finite bookkeeping bounds `‖Wtl(−iy)‖ ≤ Wb`,
`‖detTL(−iy) − 1‖ ≤ d` (each term = constant · a `φ`-sum bounded by the helpers here); (2) the
**Appendix bridge** `{[Q̂₀(k)]⁻¹}ᵢⱼ = δᵢⱼ + 2π(ρᵢρⱼ)^{1/2}Wᵢⱼ(ik)/(Δ det(ik))·e^{−ikλᵢⱼ}`, i.e.
that the project's Woodbury inverse (`Q0_mat_phys_inv_eq`) equals this `2π√W/det` form — the
derivation that ties `Wtl`/`detTL` to the actual `[Q̂₀]⁻¹`.
-/

open Complex

namespace FMSA.MixtureRDF

/-- Tang & Lu Appendix `φ₁(R) = (1 − sR − e^{−sR})/s²` (`s = ik`). -/
noncomputable def phi1 (s : ℂ) (R : ℝ) : ℂ := (1 - s * R - Complex.exp (-(s * R))) / s ^ 2

/-- Tang & Lu Appendix `φ₂(R) = (1 − sR + (sR)²/2 − e^{−sR})/s³` (`s = ik`). -/
noncomputable def phi2 (s : ℂ) (R : ℝ) : ℂ :=
  (1 - s * R + (s * R) ^ 2 / 2 - Complex.exp (-(s * R))) / s ^ 3

/-- Moment `ξᵢ = ∑ₘ ρₘ Rₘⁱ`. -/
def xiMom {N : ℕ} (ρ R : Fin N → ℝ) (i : ℕ) : ℝ := ∑ m, ρ m * R m ^ i

/-- Packing-fraction factor `Δ = 1 − (π/6)ξ₃`. -/
noncomputable def Delta {N : ℕ} (ρ R : Fin N → ℝ) : ℝ := 1 - Real.pi / 6 * xiMom ρ R 3

/-- **Tang & Lu Appendix `Wᵢⱼ(ik)`** (`s = ik`), p. 95: `φ₂(Rᵢ)(1+πξ₃/2Δ) + φ₁(Rᵢ)(Rᵢⱼ+πξ₂RᵢRⱼ/4Δ)
+ (π/2Δ)φ₁(Rᵢ)∑ₘρₘφ₁(Rₘ)(Rₘ−Rᵢ)(Rₘ−Rⱼ) + (π/2Δ)Rᵢ²∑ₘρₘφ₂(Rₘ)(Rⱼ−Rₘ)`. -/
noncomputable def Wtl {N : ℕ} (s : ℂ) (ρ R : Fin N → ℝ) (i j : Fin N) : ℂ :=
  phi2 s (R i) * (1 + Real.pi * (xiMom ρ R 3 : ℂ) / (2 * (Delta ρ R : ℂ)))
  + phi1 s (R i) * (((R i + R j) / 2 : ℝ)
      + Real.pi * (xiMom ρ R 2 : ℂ) * (R i : ℂ) * (R j : ℂ) / (4 * (Delta ρ R : ℂ)))
  + Real.pi / (2 * (Delta ρ R : ℂ)) * phi1 s (R i)
      * ∑ m, (ρ m : ℂ) * phi1 s (R m) * ((R m : ℂ) - (R i : ℂ)) * ((R m : ℂ) - (R j : ℂ))
  + Real.pi / (2 * (Delta ρ R : ℂ)) * (R i : ℂ) ^ 2
      * ∑ m, (ρ m : ℂ) * phi2 s (R m) * ((R j : ℂ) - (R m : ℂ))

/-- **Tang & Lu Appendix `det(ik)`** (`s = ik`), p. 95, the `2×2`-reduced Baxter determinant:
`1 − (2π/Δ)∑ₘρₘφ₂(Rₘ)(1+πξ₃/2Δ) − (2π/Δ)∑ₘρₘφ₁(Rₘ)(Rₘ+πξ₂Rₘ²/4Δ)
− (π²/2Δ²)∑ₘ∑ₙρₘρₙφ₁(Rₘ)φ₁(Rₙ)(Rₘ−Rₙ)²`. -/
noncomputable def detTL {N : ℕ} (s : ℂ) (ρ R : Fin N → ℝ) : ℂ :=
  1 - 2 * Real.pi / (Delta ρ R : ℂ)
        * ∑ m, (ρ m : ℂ) * phi2 s (R m) * (1 + Real.pi * (xiMom ρ R 3 : ℂ) / (2 * (Delta ρ R : ℂ)))
    - 2 * Real.pi / (Delta ρ R : ℂ)
        * ∑ m, (ρ m : ℂ) * phi1 s (R m)
            * ((R m : ℂ) + Real.pi * (xiMom ρ R 2 : ℂ) * (R m : ℂ) ^ 2 / (4 * (Delta ρ R : ℂ)))
    - Real.pi ^ 2 / (2 * (Delta ρ R : ℂ) ^ 2)
        * ∑ m, ∑ n, (ρ m : ℂ) * (ρ n : ℂ) * phi1 s (R m) * phi1 s (R n)
            * ((R m : ℂ) - (R n : ℂ)) ^ 2

/-- **Arc decay of `φ₁`.**  `‖phi1 s R‖ ≤ (2 + R)/‖s‖ → 0` for `‖s‖ ≥ 1`, `0 ≤ Re s`, `0 ≤ R`
(the arc: `s = −iy`, `Re s = R sinθ ≥ 0`).  Specialises `normP2_arc_decay` at `σ = R`. -/
theorem norm_phi1_le {s : ℂ} {R : ℝ} (hs : 1 ≤ ‖s‖) (hre : 0 ≤ s.re) (hR : 0 ≤ R) :
    ‖phi1 s R‖ ≤ (2 + R) / ‖s‖ := by
  have hre' : 0 ≤ (s * (R : ℂ)).re := by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact mul_nonneg hre hR
  have h := normP2_arc_decay (σ := (R : ℂ)) hs hre'
  rw [Complex.norm_real, Real.norm_of_nonneg hR] at h
  exact h

/-- **Arc decay of `φ₂`** — `‖phi2 s R‖ ≤ (2 + R + R²/2)/‖s‖ → 0`, specialising
`normP3_arc_decay`. -/
theorem norm_phi2_le {s : ℂ} {R : ℝ} (hs : 1 ≤ ‖s‖) (hre : 0 ≤ s.re) (hR : 0 ≤ R) :
    ‖phi2 s R‖ ≤ (2 + R + R ^ 2 / 2) / ‖s‖ := by
  have hre' : 0 ≤ (s * (R : ℂ)).re := by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact mul_nonneg hre hR
  have h := normP3_arc_decay (σ := (R : ℂ)) hs hre'
  rw [Complex.norm_real, Real.norm_of_nonneg hR] at h
  exact h

/-- **Any finite `ρ`-weighted `φ₁`-sum is `O(1/‖s‖)`** — the shape of the `W`/`det` terms.
`‖∑ₘ wₘ·φ₁(Rₘ)‖ ≤ (∑ₘ ‖wₘ‖(2+Rₘ))/‖s‖`. -/
theorem norm_weighted_phi1_sum_le {N : ℕ} {s : ℂ} {R : Fin N → ℝ} (hs : 1 ≤ ‖s‖)
    (hre : 0 ≤ s.re) (hR : ∀ m, 0 ≤ R m) (w : Fin N → ℂ) :
    ‖∑ m, w m * phi1 s (R m)‖ ≤ (∑ m, ‖w m‖ * (2 + R m)) / ‖s‖ := by
  rw [Finset.sum_div]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun m _ => ?_))
  rw [norm_mul, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (norm_phi1_le hs hre (hR m)) (norm_nonneg _)

/-- **Any finite `ρ`-weighted `φ₂`-sum is `O(1/‖s‖)`.**
`‖∑ₘ wₘ·φ₂(Rₘ)‖ ≤ (∑ₘ ‖wₘ‖(2+Rₘ+Rₘ²/2))/‖s‖`. -/
theorem norm_weighted_phi2_sum_le {N : ℕ} {s : ℂ} {R : Fin N → ℝ} (hs : 1 ≤ ‖s‖)
    (hre : 0 ≤ s.re) (hR : ∀ m, 0 ≤ R m) (w : Fin N → ℂ) :
    ‖∑ m, w m * phi2 s (R m)‖ ≤ (∑ m, ‖w m‖ * (2 + R m + R m ^ 2 / 2)) / ‖s‖ := by
  rw [Finset.sum_div]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun m _ => ?_))
  rw [norm_mul, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (norm_phi2_le hs hre (hR m)) (norm_nonneg _)

/-! ### The finite `W`/`det` bookkeeping bounds — every term is `O(1/‖s‖)` -/

/-- Termwise: `∀ m, ‖f m‖ ≤ g m/‖s‖ ⟹ ‖∑ₘ f m‖ ≤ (∑ₘ g m)/‖s‖`. -/
theorem norm_sum_le_of_termwise {N : ℕ} {s : ℂ} {g : Fin N → ℝ} {f : Fin N → ℂ}
    (h : ∀ m, ‖f m‖ ≤ g m / ‖s‖) : ‖∑ m, f m‖ ≤ (∑ m, g m) / ‖s‖ := by
  rw [Finset.sum_div]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun m _ => h m))

/-- Crude constant bound `‖phi1 s R‖ ≤ 2 + R` (from the decay, `‖s‖ ≥ 1`). -/
theorem norm_phi1_le_const {s : ℂ} {R : ℝ} (hs : 1 ≤ ‖s‖) (hre : 0 ≤ s.re) (hR : 0 ≤ R) :
    ‖phi1 s R‖ ≤ 2 + R := by
  have h := norm_phi1_le hs hre hR
  have : (2 + R) / ‖s‖ ≤ 2 + R := by rw [div_le_iff₀ (by linarith)]; nlinarith [hR]
  linarith

/-- `‖c·X‖ ≤ ‖c‖·B/‖s‖` from `‖X‖ ≤ B/‖s‖` — pulls a constant coefficient out of a term bound. -/
theorem norm_const_mul_le {s c X : ℂ} {B : ℝ} (h : ‖X‖ ≤ B / ‖s‖) :
    ‖c * X‖ ≤ ‖c‖ * B / ‖s‖ := by
  rw [norm_mul]
  calc ‖c‖ * ‖X‖ ≤ ‖c‖ * (B / ‖s‖) := by gcongr
    _ = ‖c‖ * B / ‖s‖ := (mul_div_assoc _ _ _).symm

/-- A single `ρ`-weighted `φ₁`-sum with per-`m` coefficient `κ` (the shape of `W`/`det` terms). -/
theorem norm_rhoWeighted_phi1_sum_le {N : ℕ} {s : ℂ} {ρ R : Fin N → ℝ} (hs : 1 ≤ ‖s‖)
    (hre : 0 ≤ s.re) (hR : ∀ m, 0 ≤ R m) (κ : Fin N → ℂ) :
    ‖∑ m, (ρ m : ℂ) * phi1 s (R m) * κ m‖ ≤ (∑ m, ‖(ρ m : ℂ) * κ m‖ * (2 + R m)) / ‖s‖ := by
  have heq : (∑ m, (ρ m : ℂ) * phi1 s (R m) * κ m)
      = ∑ m, ((ρ m : ℂ) * κ m) * phi1 s (R m) := by
    apply Finset.sum_congr rfl; intro m _; ring
  rw [heq]; exact norm_weighted_phi1_sum_le hs hre hR (fun m => (ρ m : ℂ) * κ m)

/-- A single `ρ`-weighted `φ₂`-sum with per-`m` coefficient `κ`. -/
theorem norm_rhoWeighted_phi2_sum_le {N : ℕ} {s : ℂ} {ρ R : Fin N → ℝ} (hs : 1 ≤ ‖s‖)
    (hre : 0 ≤ s.re) (hR : ∀ m, 0 ≤ R m) (κ : Fin N → ℂ) :
    ‖∑ m, (ρ m : ℂ) * phi2 s (R m) * κ m‖
      ≤ (∑ m, ‖(ρ m : ℂ) * κ m‖ * (2 + R m + R m ^ 2 / 2)) / ‖s‖ := by
  have heq : (∑ m, (ρ m : ℂ) * phi2 s (R m) * κ m)
      = ∑ m, ((ρ m : ℂ) * κ m) * phi2 s (R m) := by
    apply Finset.sum_congr rfl; intro m _; ring
  rw [heq]; exact norm_weighted_phi2_sum_le hs hre hR (fun m => (ρ m : ℂ) * κ m)

/-- The double `φ₁·φ₁` sum of `detTL`'s third term — `O(1/‖s‖)` (one `φ₁` crude, one decaying). -/
theorem norm_rhoRho_phi1_phi1_dsum_le {N : ℕ} {s : ℂ} {ρ R : Fin N → ℝ} (hs : 1 ≤ ‖s‖)
    (hre : 0 ≤ s.re) (hR : ∀ m, 0 ≤ R m) :
    ‖∑ m, ∑ n, (ρ m : ℂ) * (ρ n : ℂ) * phi1 s (R m) * phi1 s (R n) * ((R m : ℂ) - (R n : ℂ)) ^ 2‖
      ≤ (∑ m, ∑ n, ‖(ρ m : ℂ)‖ * ‖(ρ n : ℂ)‖ * (2 + R m)
          * ‖((R m : ℂ) - (R n : ℂ)) ^ 2‖ * (2 + R n)) / ‖s‖ := by
  rw [Finset.sum_div]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun m _ => ?_))
  refine norm_sum_le_of_termwise (fun n => ?_)
  have hpm : ‖phi1 s (R m)‖ ≤ 2 + R m := norm_phi1_le_const hs hre (hR m)
  have hpn : ‖phi1 s (R n)‖ ≤ (2 + R n) / ‖s‖ := norm_phi1_le hs hre (hR n)
  calc ‖(ρ m : ℂ) * (ρ n : ℂ) * phi1 s (R m) * phi1 s (R n) * ((R m : ℂ) - (R n : ℂ)) ^ 2‖
      = ‖(ρ m : ℂ)‖ * ‖(ρ n : ℂ)‖ * ‖phi1 s (R m)‖ * ‖phi1 s (R n)‖
          * ‖((R m : ℂ) - (R n : ℂ)) ^ 2‖ := by rw [norm_mul, norm_mul, norm_mul, norm_mul]
    _ ≤ ‖(ρ m : ℂ)‖ * ‖(ρ n : ℂ)‖ * (2 + R m) * ((2 + R n) / ‖s‖)
          * ‖((R m : ℂ) - (R n : ℂ)) ^ 2‖ := by
        gcongr
        exact mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by linarith [hR m])
    _ = ‖(ρ m : ℂ)‖ * ‖(ρ n : ℂ)‖ * (2 + R m)
          * ‖((R m : ℂ) - (R n : ℂ)) ^ 2‖ * (2 + R n) / ‖s‖ := by ring

/-- **`det(−iy) → 1` on the arc** — `‖detTL s ρ R − 1‖ ≤ Cdet/‖s‖` (a constant over `‖s‖`), so
`detTL → 1`, hence bounded below by `norm_ge_of_norm_sub_one_le`.  The three terms are bounded by
the single- and double-`φ`-sum lemmas above; each is a constant times a sum `O(1/‖s‖)`. -/
theorem norm_detTL_sub_one_le {N : ℕ} {s : ℂ} {ρ R : Fin N → ℝ}
    (hs : 1 ≤ ‖s‖) (hre : 0 ≤ s.re) (hR : ∀ m, 0 ≤ R m) :
    ‖detTL s ρ R - 1‖ ≤
      (‖2 * Real.pi / (Delta ρ R : ℂ)‖ * (∑ m, ‖(ρ m : ℂ)
            * (1 + Real.pi * (xiMom ρ R 3 : ℂ) / (2 * (Delta ρ R : ℂ)))‖ * (2 + R m + R m ^ 2 / 2))
        + ‖2 * Real.pi / (Delta ρ R : ℂ)‖ * (∑ m, ‖(ρ m : ℂ)
            * ((R m : ℂ) + Real.pi * (xiMom ρ R 2 : ℂ) * (R m : ℂ) ^ 2 / (4 * (Delta ρ R : ℂ)))‖
            * (2 + R m))
        + ‖Real.pi ^ 2 / (2 * (Delta ρ R : ℂ) ^ 2)‖ * (∑ m, ∑ n, ‖(ρ m : ℂ)‖ * ‖(ρ n : ℂ)‖
            * (2 + R m) * ‖((R m : ℂ) - (R n : ℂ)) ^ 2‖ * (2 + R n))) / ‖s‖ := by
  have h1 := norm_const_mul_le (c := 2 * Real.pi / (Delta ρ R : ℂ))
    (norm_rhoWeighted_phi2_sum_le (ρ := ρ) hs hre hR
      (fun _ => (1 + Real.pi * (xiMom ρ R 3 : ℂ) / (2 * (Delta ρ R : ℂ)))))
  have h2 := norm_const_mul_le (c := 2 * Real.pi / (Delta ρ R : ℂ))
    (norm_rhoWeighted_phi1_sum_le (ρ := ρ) hs hre hR
      (fun m => (R m : ℂ) + Real.pi * (xiMom ρ R 2 : ℂ) * (R m : ℂ) ^ 2 / (4 * (Delta ρ R : ℂ))))
  have h3 := norm_const_mul_le (c := Real.pi ^ 2 / (2 * (Delta ρ R : ℂ) ^ 2))
    (norm_rhoRho_phi1_phi1_dsum_le (ρ := ρ) hs hre hR)
  have hsub : detTL s ρ R - 1 = -(2 * Real.pi / (Delta ρ R : ℂ)
        * ∑ m, (ρ m : ℂ) * phi2 s (R m) * (1 + Real.pi * (xiMom ρ R 3 : ℂ) / (2 * (Delta ρ R : ℂ))))
      - 2 * Real.pi / (Delta ρ R : ℂ)
        * (∑ m, (ρ m : ℂ) * phi1 s (R m)
            * ((R m : ℂ) + Real.pi * (xiMom ρ R 2 : ℂ) * (R m : ℂ) ^ 2 / (4 * (Delta ρ R : ℂ))))
      - Real.pi ^ 2 / (2 * (Delta ρ R : ℂ) ^ 2)
        * (∑ m, ∑ n, (ρ m : ℂ) * (ρ n : ℂ) * phi1 s (R m) * phi1 s (R n)
            * ((R m : ℂ) - (R n : ℂ)) ^ 2) := by
    simp only [detTL]; ring
  rw [hsub, add_div, add_div]
  -- `‖(-A) - B - C‖ ≤ (‖A‖ + ‖B‖) + ‖C‖`, then the three term bounds `h1`, `h2`, `h3`
  refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add ?_ h2)) h3)
  rw [norm_neg]
  exact h1

/-! ### The `‖Wtl‖ ≤ Wb` bookkeeping bound — the analogue of `norm_detTL_sub_one_le` -/

/-- `‖φ₂(R)·c‖ ≤ ‖c‖(2+R+R²/2)/‖s‖` — a single `φ₂` times a constant (a `Wtl` term shape). -/
theorem norm_phi2_mul_le {s : ℂ} {R : ℝ} {c : ℂ} (hs : 1 ≤ ‖s‖) (hre : 0 ≤ s.re) (hR : 0 ≤ R) :
    ‖phi2 s R * c‖ ≤ ‖c‖ * (2 + R + R ^ 2 / 2) / ‖s‖ := by
  rw [norm_mul]
  calc ‖phi2 s R‖ * ‖c‖ ≤ ((2 + R + R ^ 2 / 2) / ‖s‖) * ‖c‖ := by
        gcongr; exact norm_phi2_le hs hre hR
    _ = ‖c‖ * (2 + R + R ^ 2 / 2) / ‖s‖ := by ring

/-- `‖φ₁(R)·c‖ ≤ ‖c‖(2+R)/‖s‖`. -/
theorem norm_phi1_mul_le {s : ℂ} {R : ℝ} {c : ℂ} (hs : 1 ≤ ‖s‖) (hre : 0 ≤ s.re) (hR : 0 ≤ R) :
    ‖phi1 s R * c‖ ≤ ‖c‖ * (2 + R) / ‖s‖ := by
  rw [norm_mul]
  calc ‖phi1 s R‖ * ‖c‖ ≤ ((2 + R) / ‖s‖) * ‖c‖ := by gcongr; exact norm_phi1_le hs hre hR
    _ = ‖c‖ * (2 + R) / ‖s‖ := by ring

/-- `‖c₀·φ₁(R₀)·X‖ ≤ ‖c₀‖(2+R₀)·B/‖s‖` from `‖X‖ ≤ B/‖s‖` — the `Wtl` third term (`φ₁` outside a
`φ₁`-sum: one crude, the sum decaying). -/
theorem norm_c_phi1_mul_le {s : ℂ} {R0 : ℝ} {c0 X : ℂ} {B : ℝ} (hs : 1 ≤ ‖s‖) (hre : 0 ≤ s.re)
    (hR : 0 ≤ R0) (hB : 0 ≤ B) (h : ‖X‖ ≤ B / ‖s‖) :
    ‖c0 * phi1 s R0 * X‖ ≤ ‖c0‖ * (2 + R0) * B / ‖s‖ := by
  have hc : ‖c0 * phi1 s R0‖ ≤ ‖c0‖ * (2 + R0) := by
    rw [norm_mul]; gcongr; exact norm_phi1_le_const hs hre hR
  calc ‖c0 * phi1 s R0 * X‖ ≤ ‖c0 * phi1 s R0‖ * B / ‖s‖ := norm_const_mul_le h
    _ ≤ ‖c0‖ * (2 + R0) * B / ‖s‖ := by gcongr

/-- **`W(−iy)` bounded on the arc** — `‖Wtl s ρ R i j‖ ≤ Wb/‖s‖` (a constant over `‖s‖`, `→ 0`).
The four `Wtl` terms are bounded by the `φ`-times-constant / `φ`-sum lemmas above; combined with
`norm_detTL_sub_one_le` and the (iii) assembly logic (`amplitude_norm_le`), this bounds the `A(−iy)`
amplitude on the arc. -/
theorem norm_Wtl_le {N : ℕ} {s : ℂ} {ρ R : Fin N → ℝ} (i j : Fin N)
    (hs : 1 ≤ ‖s‖) (hre : 0 ≤ s.re) (hR : ∀ m, 0 ≤ R m) :
    ‖Wtl s ρ R i j‖ ≤
      (‖1 + Real.pi * (xiMom ρ R 3 : ℂ) / (2 * (Delta ρ R : ℂ))‖ * (2 + R i + R i ^ 2 / 2)
        + ‖(R i / 2 + R j / 2 : ℝ)
            + Real.pi * (xiMom ρ R 2 : ℂ) * (R i : ℂ) * (R j : ℂ) / (4 * (Delta ρ R : ℂ))‖
            * (2 + R i)
        + ‖Real.pi / (2 * (Delta ρ R : ℂ))‖ * (2 + R i)
            * (∑ m, ‖(ρ m : ℂ) * (((R m : ℂ) - (R i : ℂ)) * ((R m : ℂ) - (R j : ℂ)))‖ * (2 + R m))
        + ‖Real.pi / (2 * (Delta ρ R : ℂ)) * (R i : ℂ) ^ 2‖
            * (∑ m, ‖(ρ m : ℂ) * ((R j : ℂ) - (R m : ℂ))‖ * (2 + R m + R m ^ 2 / 2))) / ‖s‖ := by
  have h1 := norm_phi2_mul_le (s := s) (R := R i)
    (c := 1 + Real.pi * (xiMom ρ R 3 : ℂ) / (2 * (Delta ρ R : ℂ))) hs hre (hR i)
  have h2 := norm_phi1_mul_le (s := s) (R := R i)
    (c := (R i / 2 + R j / 2 : ℝ)
      + Real.pi * (xiMom ρ R 2 : ℂ) * (R i : ℂ) * (R j : ℂ) / (4 * (Delta ρ R : ℂ))) hs hre (hR i)
  have hSA3 : ‖∑ m, (ρ m : ℂ) * phi1 s (R m)
        * ((R m : ℂ) - (R i : ℂ)) * ((R m : ℂ) - (R j : ℂ))‖
      ≤ (∑ m, ‖(ρ m : ℂ) * (((R m : ℂ) - (R i : ℂ)) * ((R m : ℂ) - (R j : ℂ)))‖ * (2 + R m))
          / ‖s‖ := by
    have heq : (∑ m, (ρ m : ℂ) * phi1 s (R m) * ((R m : ℂ) - (R i : ℂ)) * ((R m : ℂ) - (R j : ℂ)))
        = ∑ m, (ρ m : ℂ) * phi1 s (R m)
            * (((R m : ℂ) - (R i : ℂ)) * ((R m : ℂ) - (R j : ℂ))) := by
      apply Finset.sum_congr rfl; intro m _; ring
    rw [heq]
    exact norm_rhoWeighted_phi1_sum_le (ρ := ρ) hs hre hR
      (fun m => ((R m : ℂ) - (R i : ℂ)) * ((R m : ℂ) - (R j : ℂ)))
  have h3 := norm_c_phi1_mul_le (s := s) (R0 := R i)
    (c0 := Real.pi / (2 * (Delta ρ R : ℂ))) hs hre (hR i)
    (Finset.sum_nonneg (fun m _ => mul_nonneg (norm_nonneg _) (by linarith [hR m]))) hSA3
  have h4 := norm_const_mul_le (c := Real.pi / (2 * (Delta ρ R : ℂ)) * (R i : ℂ) ^ 2)
    (norm_rhoWeighted_phi2_sum_le (ρ := ρ) hs hre hR (fun m => (R j : ℂ) - (R m : ℂ)))
  unfold Wtl
  simp only [add_div]
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
    (add_le_add ((norm_add_le _ _).trans (add_le_add h1 h2)) h3)) h4)

end FMSA.MixtureRDF
