/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import LeanCode.HSMixture.Q0ComplexDetMatch

/-!
# The A6 → A7 scalar closure `det(I − VₒUₒ) = detTL` — COMPLETE (general `N`)

The A6 form `det(I − VₒUₒ) = (1 − Σρ fFunC)(1 − Σρσ gFunC) − (Σρ gFunC)(Σρσ fFunC)` (`detVU_expand`)
equals Tang & Lu's A7 (`detTL`).  Both reduce to a common canonical form
`1 − (2π/Δ)·Σ_m ρ_m·GS(m) + (π²/Δ²)·Σ_m Σ_n ρ_m ρ_n·sd(m,n)`, `GS(m) = σ_m φ1 + φ2`, differing
only in the double-sum summand `sd` (`A6sd` vs `detTLsd`), and the two summands agree under the
`sum_comm` symmetrisation (`sdMatch`).  The closure is **`det_eq_detTL`** — with
`det_Q0_mat_c_phys_eq_two_by_two` this is the general-`N` Appendix **denominator** bridge
`det Q̂₀(s) = detTL`.  Everything axiom-clean.

* **`FG_antisym`** — the key `ξ₂`-cancellation `fFunC_p gFunC_q − gFunC_p fFunC_q =
  (2π²/Δ²)(a_p φ1_q − a_q φ1_p)` (`a_p = σ_p/2·φ1 + φ2`); pure `ring` (the `ξ₂` terms cancel
  antisymmetrically), so the `2×2` double sum carries no `ξ₂`.
* **`detVU_double`** — the A6 product terms as a double sum `Σ_p Σ_q ρ_p ρ_q σ_q (fFunC_p gFunC_q −
  gFunC_p fFunC_q)`.
* **`fFunC_eq`, `gFunC_relation`** — `fFunC = (2π/Δ)·a`, `gFunC = (π/Δ)φ1 + (πξ₂/2Δ)·fFunC` (let the
  single `Σρσ gFunC` split into a `φ1` single sum plus a `ξ₂`-weighted `fFunC` sum).
* **`sum_distrib_prod`, `sum_distrib_prod2`** — pull a `Σ_n g_n` factor out of a single sum into a
  double sum (the `detTL` `ξ₂`/`ξ₃`-in-a-single-sum terms → double sums).
* **`aFun`, `A6sd`, `detTLsd`** — the canonical genuine-single kernel and the two double-sum terms
  (`ξ₂`,`ξ₃` expanded).
* **`sdMatch`** — the double-sum match `Σ∑ρρ A6sd = Σ∑ρρ detTLsd`, THE conceptual crux: the summands
  are **not** equal pointwise, but `A6sd(m,n)+A6sd(n,m) = detTLsd(m,n)+detTLsd(n,m)` (a `ring`
  after `φ2 = φ1/s + σ²/2s`) and `ρ_mρ_n` is symmetric, so `Finset.sum_comm` symmetrisation gives
  equality.  Numerically confirmed (A6 = A7 to `9e-16`; symmetrised summands agree to `1e-16`).

The closure: **`detTLtoCanon`** (A7 → canonical, via `sum_distrib_prod`/`sum_distrib_prod2` on
`detTL`'s `ξ`-products), **`A6toCanon`** (A6 → canonical, via `detVU_double` + `FG_antisym` +
`fFunC_eq` + `gFunC_relation`), then **`det_eq_detTL`** = `detVU_expand ▸ A6toCanon ▸ detTLtoCanon ▸
sdMatch`.  All lemmas here axiom-clean (`propext, Classical.choice, Quot.sound`).

**Numerator side + full entrywise bridge — DONE.**  The off-identity entry of
`[Q̂₀]⁻¹ = I + Uₒ(I−VₒUₒ)⁻¹Vₒ` is `√(ρᵢρⱼ)e^{−sλᵢⱼ}·B_ij/detTL`,
`B_ij = fFunC_i(1−m₁₁) + gFunC_i·m₁₀ + σⱼ(fFunC_i·m₀₁ + gFunC_i(1−m₀₀))` (the `2×2` `adj(I−VₒUₒ)`).
**`Bsum_combine`** collapses `B_ij`'s four `m_kl`-sums into
`Σ_p ρ_p(σⱼ−σ_p)(fFunC_i gFunC_p − gFunC_i fFunC_p)`, and **`numMatch`** proves the scalar match
`B_ij·Δ = 2π·Wtl_ij` (via `hLHS`/`hRHS`: both sides → `NS + Σ_p ρ_p·(summand)`, common non-sum
`NS = 2π(φ2_i + (σ_i+σ_j)/2·φ1_i)`, summands agree pointwise after `φ2 = φ1/s + σ²/2s` — single-sum,
no symmetrisation).  **`UadjV`** computes `Uₒ·adj(I−VₒUₒ)·Vₒ` entrywise, and
**`Q0_inv_entry_bridge`** assembles the full general-`N` Appendix bridge
`{[Q̂₀(s)]⁻¹}_ij = δ_ij + 2π√(ρᵢρⱼ)·Wtl_ij·e^{−sλᵢⱼ}/(Δ·detTL)` (Woodbury inverse + `(I−VₒUₒ)⁻¹ =
detTL⁻¹•adj` + `UadjV` + `numMatch`).  Both denominator (`det_eq_detTL`) and the entrywise inverse
(`Q0_inv_entry_bridge`) are closed.  All axiom-clean.
-/

open Complex Matrix

namespace FMSA.ComplexRankTwo

open FMSA.MatrixQ0 FMSA.Q0Complex FMSA.MixtureNoSpinodal FMSA.MixtureArcBound

/-- **Key ξ₂-cancellation** `fFunC_p gFunC_q − gFunC_p fFunC_q = (2π²/Δ²)(a_p φ1_q − a_q φ1_p)`,
`a_p = σ_p/2·φ1_p + φ2_p`.  Pure `ring` — the `ξ₂` terms cancel antisymmetrically. -/
theorem FG_antisym {N : ℕ} (s : ℂ) (sigma rho : Fin N → ℝ) (p q : Fin N) :
    fFunC rho sigma p s * gFunC rho sigma q s - gFunC rho sigma p s * fFunC rho sigma q s
      = (2 * (Real.pi : ℂ) ^ 2 / (vacMix rho sigma : ℂ) ^ 2)
        * (((sigma p : ℂ) / 2 * p1c s (sigma p) + p2c s (sigma p)) * p1c s (sigma q)
           - ((sigma q : ℂ) / 2 * p1c s (sigma q) + p2c s (sigma q)) * p1c s (sigma p)) := by
  simp only [fFunC, gFunC]; push_cast; ring

/-- `gFunC = (π/Δ)φ1 + (πξ₂/2Δ)·fFunC`. -/
theorem gFunC_relation {N : ℕ} (s : ℂ) (sigma rho : Fin N → ℝ) (q : Fin N) :
    gFunC rho sigma q s
      = ((Real.pi / vacMix rho sigma : ℝ) : ℂ) * p1c s (sigma q)
        + ((Real.pi * xi2 rho sigma / (2 * vacMix rho sigma) : ℝ) : ℂ) * fFunC rho sigma q s := by
  simp only [fFunC, gFunC]; push_cast; ring

/-- `fFunC = (2π/Δ)·(σ/2·φ1 + φ2)`. -/
theorem fFunC_eq {N : ℕ} (s : ℂ) (sigma rho : Fin N → ℝ) (p : Fin N) :
    fFunC rho sigma p s
      = ((2 * Real.pi / vacMix rho sigma : ℝ) : ℂ)
        * ((sigma p : ℂ) / 2 * p1c s (sigma p) + p2c s (sigma p)) := by
  simp only [fFunC]; push_cast; ring

/-- The A6 product terms as a double sum. -/
theorem detVU_double {N : ℕ} (s : ℂ) (sigma rho : Fin N → ℝ) :
    (∑ p, (rho p : ℂ) * fFunC rho sigma p s)
      * (∑ q, (rho q : ℂ) * (sigma q : ℂ) * gFunC rho sigma q s)
    - (∑ p, (rho p : ℂ) * gFunC rho sigma p s)
      * (∑ q, (rho q : ℂ) * (sigma q : ℂ) * fFunC rho sigma q s)
    = ∑ p, ∑ q, (rho p : ℂ) * (rho q : ℂ) * (sigma q : ℂ)
        * (fFunC rho sigma p s * gFunC rho sigma q s
           - gFunC rho sigma p s * fFunC rho sigma q s) := by
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro p _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro q _
  ring

/-- Pull a `Σ_n g_n` factor out of a single sum into a double sum:
`Σ_m f_m·(a + c·Σ_n g_n) = Σ_m f_m·a + c·Σ_m Σ_n f_m·g_n`. -/
theorem sum_distrib_prod {N : ℕ} (f g : Fin N → ℂ) (a c : ℂ) :
    (∑ m, f m * (a + c * ∑ n, g n)) = (∑ m, f m * a) + c * ∑ m, ∑ n, f m * g n := by
  simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl; intro m _
  apply Finset.sum_congr rfl; intro n _
  ring

/-- Variant with a trailing factor: `Σ_m a_m·(h_m + c·(Σ_n g_n)·f_m) = Σ_m a_m·h_m + c·Σ_m Σ_n
a_m·g_n·f_m`. -/
theorem sum_distrib_prod2 {N : ℕ} (a h f g : Fin N → ℂ) (c : ℂ) :
    (∑ m, a m * (h m + c * (∑ n, g n) * f m))
      = (∑ m, a m * h m) + c * ∑ m, ∑ n, a m * g n * f m := by
  simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl; intro m _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro n _
  ring

/-- `a_m = σ_m/2·φ1 + φ2` (the canonical Woodbury-column kernel). -/
noncomputable def aFun {N : ℕ} (s : ℂ) (sigma : Fin N → ℝ) (m : Fin N) : ℂ :=
  (sigma m : ℂ) / 2 * p1c s (sigma m) + p2c s (sigma m)

/-- A6 double-sum summand (canonical). -/
noncomputable def A6sd {N : ℕ} (s : ℂ) (sigma : Fin N → ℝ) (m n : Fin N) : ℂ :=
  -(sigma m : ℂ) * (sigma n : ℂ) ^ 2 * aFun s sigma m
    + 2 * (sigma n : ℂ) * (aFun s sigma m * p1c s (sigma n) - aFun s sigma n * p1c s (sigma m))

/-- detTL double-sum summand (canonical, `ξ₂`/`ξ₃` expanded). -/
noncomputable def detTLsd {N : ℕ} (s : ℂ) (sigma : Fin N → ℝ) (m n : Fin N) : ℂ :=
  -(sigma n : ℂ) ^ 3 * p2c s (sigma m)
    - 1 / 2 * (sigma n : ℂ) ^ 2 * (sigma m : ℂ) ^ 2 * p1c s (sigma m)
    - 1 / 2 * p1c s (sigma m) * p1c s (sigma n) * ((sigma m : ℂ) - (sigma n : ℂ)) ^ 2

/-- **The double-sum match** `Σ∑ρρ A6sd = Σ∑ρρ detTLsd` — the conceptual crux of A6 → A7.  The
summands are NOT equal pointwise; but `A6sd(m,n)+A6sd(n,m) = detTLsd(m,n)+detTLsd(n,m)` (a `ring`
identity after `φ2 = φ1/s + σ²/2s`, `p2c_eq_p1c`) and `ρ_mρ_n` is symmetric, so `Finset.sum_comm`
symmetrisation forces `2·(Σ∑ρρ(A6sd − detTLsd)) = Σ∑ρρ·0 = 0`. -/
theorem sdMatch {N : ℕ} {sigma rho : Fin N → ℝ} {s : ℂ} (hs : s ≠ 0) :
    ∑ m, ∑ n, (rho m : ℂ) * (rho n : ℂ) * A6sd s sigma m n
      = ∑ m, ∑ n, (rho m : ℂ) * (rho n : ℂ) * detTLsd s sigma m n := by
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  set F : Fin N → Fin N → ℂ := fun m n =>
    (rho m : ℂ) * (rho n : ℂ) * A6sd s sigma m n
      - (rho m : ℂ) * (rho n : ℂ) * detTLsd s sigma m n with hF
  have hanti : ∀ m n, F m n + F n m = 0 := by
    intro m n
    simp only [hF, A6sd, detTLsd, aFun,
      p2c_eq_p1c s (sigma m) hs, p2c_eq_p1c s (sigma n) hs]
    ring
  have hswap : (∑ m, ∑ n, F m n) = ∑ m, ∑ n, F n m := by rw [Finset.sum_comm]
  have h2 : (2 : ℂ) * ∑ m, ∑ n, F m n = 0 := by
    rw [two_mul]
    nth_rewrite 2 [hswap]
    rw [← Finset.sum_add_distrib]
    simp_rw [← Finset.sum_add_distrib, hanti, Finset.sum_const_zero]
  exact (mul_eq_zero.mp h2).resolve_left two_ne_zero

/-- **`detTL` in canonical form** `1 − (2π/Δ)·Σρ·GS + (π²/Δ²)·Σ∑ρρ·detTLsd`, `GS(m)=σ_m φ1 + φ2`
(A7 → canonical).  Bridge `phi→p1c/p2c`, `Delta→vacMix`, expand `ξ₂`/`ξ₃` into sums, and reshape the
two `ξ`-product terms via `sum_distrib_prod`/`sum_distrib_prod2`; then combine (`hS` singles, `hDbl`
doubles via `neg_sum2`). -/
theorem detTLtoCanon {N : ℕ} (sigma rho : Fin N → ℝ) (s : ℂ) :
    detTL s rho sigma
      = 1 - (2 * Real.pi / (vacMix rho sigma : ℂ))
            * ∑ m, (rho m : ℂ) * ((sigma m : ℂ) * p1c s (sigma m) + p2c s (sigma m))
        + ((Real.pi : ℂ) ^ 2 / (vacMix rho sigma : ℂ) ^ 2)
            * ∑ m, ∑ n, (rho m : ℂ) * (rho n : ℂ) * detTLsd s sigma m n := by
  have hD : (Delta rho sigma : ℂ) = (vacMix rho sigma : ℂ) := by
    simp only [Delta, vacMix, etaMix, xiMom]
  have hx2 : (xiMom rho sigma 2 : ℂ) = ∑ n, (rho n : ℂ) * (sigma n : ℂ) ^ 2 := by
    simp only [xiMom]; push_cast; ring
  have hx3 : (xiMom rho sigma 3 : ℂ) = ∑ n, (rho n : ℂ) * (sigma n : ℂ) ^ 3 := by
    simp only [xiMom]; push_cast; ring
  rw [detTL, hD, hx2, hx3]
  simp only [← p1c_eq_phi1, ← p2c_eq_phi2]
  set vac : ℂ := (vacMix rho sigma : ℂ) with hvac
  -- reshape + distribute term B (via sum_distrib_prod)
  rw [show (∑ m, (rho m : ℂ) * p2c s (sigma m)
        * (1 + Real.pi * (∑ n, (rho n : ℂ) * (sigma n : ℂ) ^ 3) / (2 * vac)))
      = (∑ m, ((rho m : ℂ) * p2c s (sigma m))
          * (1 + (Real.pi / (2 * vac)) * ∑ n, (rho n : ℂ) * (sigma n : ℂ) ^ 3))
      from by apply Finset.sum_congr rfl; intro m _; ring,
    sum_distrib_prod (fun m => (rho m : ℂ) * p2c s (sigma m))
      (fun n => (rho n : ℂ) * (sigma n : ℂ) ^ 3) 1 (Real.pi / (2 * vac))]
  -- reshape + distribute term C (via sum_distrib_prod2)
  rw [show (∑ m, (rho m : ℂ) * p1c s (sigma m)
        * ((sigma m : ℂ) + Real.pi * (∑ n, (rho n : ℂ) * (sigma n : ℂ) ^ 2) * (sigma m : ℂ) ^ 2
            / (4 * vac)))
      = (∑ m, ((rho m : ℂ) * p1c s (sigma m))
          * ((sigma m : ℂ) + (Real.pi / (4 * vac)) * (∑ n, (rho n : ℂ) * (sigma n : ℂ) ^ 2)
              * (sigma m : ℂ) ^ 2))
      from by apply Finset.sum_congr rfl; intro m _; ring,
    sum_distrib_prod2 (fun m => (rho m : ℂ) * p1c s (sigma m)) (fun m => (sigma m : ℂ))
      (fun m => (sigma m : ℂ) ^ 2) (fun n => (rho n : ℂ) * (sigma n : ℂ) ^ 2) (Real.pi / (4 * vac))]
  simp only [mul_one]
  have neg_sum2 : ∀ (F : Fin N → Fin N → ℂ), -(∑ m, ∑ n, F m n) = ∑ m, ∑ n, -(F m n) := by
    intro F; rw [neg_eq_neg_one_mul, Finset.mul_sum]; simp_rw [Finset.mul_sum, neg_one_mul]
  -- combine the two single sums into Σρ·GS
  have hS : (∑ m, (rho m : ℂ) * p2c s (sigma m))
        + (∑ m, (rho m : ℂ) * p1c s (sigma m) * (sigma m : ℂ))
      = ∑ m, (rho m : ℂ) * ((sigma m : ℂ) * p1c s (sigma m) + p2c s (sigma m)) := by
    rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro m _; ring
  -- combine the three double sums into Σ∑ρρ·detTLsd
  have hDbl : -(∑ m, ∑ n, (rho m : ℂ) * p2c s (sigma m) * ((rho n : ℂ) * (sigma n : ℂ) ^ 3))
        - 1 / 2 * (∑ m, ∑ n, (rho m : ℂ) * p1c s (sigma m)
            * ((rho n : ℂ) * (sigma n : ℂ) ^ 2) * (sigma m : ℂ) ^ 2)
        - 1 / 2 * (∑ m, ∑ n, (rho m : ℂ) * (rho n : ℂ) * p1c s (sigma m) * p1c s (sigma n)
            * ((sigma m : ℂ) - (sigma n : ℂ)) ^ 2)
      = ∑ m, ∑ n, (rho m : ℂ) * (rho n : ℂ) * detTLsd s sigma m n := by
    simp only [detTLsd, Finset.mul_sum]
    rw [neg_sum2]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro m _
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro n _
    ring
  rw [← hS, ← hDbl]; ring

/-- **A6 in canonical form** `1 − (2π/Δ)·Σρ·GS + (π²/Δ²)·Σ∑ρρ·A6sd` (A6 → canonical).  Expand the
product via `detVU_double`+`FG_antisym`, rewrite `fFunC`/`gFunC` via `fFunC_eq`/`gFunC_relation`,
expand `ξ₂`, reshape `SsG`'s product via `sum_distrib_prod2`; then combine (`hS`/`hDbl`). -/
theorem A6toCanon {N : ℕ} {sigma rho : Fin N → ℝ} {s : ℂ} (hvac : vacMix rho sigma ≠ 0) :
    (1 - ∑ p, (rho p : ℂ) * fFunC rho sigma p s)
      * (1 - ∑ q, (rho q : ℂ) * (sigma q : ℂ) * gFunC rho sigma q s)
    - (∑ p, (rho p : ℂ) * gFunC rho sigma p s)
      * (∑ q, (rho q : ℂ) * (sigma q : ℂ) * fFunC rho sigma q s)
    = 1 - (2 * Real.pi / (vacMix rho sigma : ℂ))
          * ∑ m, (rho m : ℂ) * ((sigma m : ℂ) * p1c s (sigma m) + p2c s (sigma m))
      + ((Real.pi : ℂ) ^ 2 / (vacMix rho sigma : ℂ) ^ 2)
          * ∑ m, ∑ n, (rho m : ℂ) * (rho n : ℂ) * A6sd s sigma m n := by
  have hvacC : (vacMix rho sigma : ℂ) ≠ 0 := by exact_mod_cast hvac
  have hx2c : (xi2 rho sigma : ℂ) = ∑ n, (rho n : ℂ) * (sigma n : ℂ) ^ 2 := by
    simp only [xi2]; push_cast; ring
  -- expand product, replace the double via detVU_double + FG_antisym
  rw [show (1 - ∑ p, (rho p : ℂ) * fFunC rho sigma p s)
        * (1 - ∑ q, (rho q : ℂ) * (sigma q : ℂ) * gFunC rho sigma q s)
      - (∑ p, (rho p : ℂ) * gFunC rho sigma p s)
        * (∑ q, (rho q : ℂ) * (sigma q : ℂ) * fFunC rho sigma q s)
      = 1 - (∑ p, (rho p : ℂ) * fFunC rho sigma p s)
          - (∑ q, (rho q : ℂ) * (sigma q : ℂ) * gFunC rho sigma q s)
        + ((∑ p, (rho p : ℂ) * fFunC rho sigma p s)
            * (∑ q, (rho q : ℂ) * (sigma q : ℂ) * gFunC rho sigma q s)
           - (∑ p, (rho p : ℂ) * gFunC rho sigma p s)
            * (∑ q, (rho q : ℂ) * (sigma q : ℂ) * fFunC rho sigma q s))
      from by ring,
    detVU_double s sigma rho]
  simp_rw [FG_antisym s sigma rho, fFunC_eq s sigma rho, gFunC_relation s sigma rho,
    fFunC_eq s sigma rho]
  simp only [A6sd, aFun]
  push_cast [hx2c]
  rw [show (∑ x, (rho x : ℂ) * (sigma x : ℂ)
        * ((Real.pi : ℂ) / (vacMix rho sigma : ℂ) * p1c s (sigma x)
           + (Real.pi : ℂ) * (∑ n, (rho n : ℂ) * (sigma n : ℂ) ^ 2) / (2 * (vacMix rho sigma : ℂ))
             * (2 * (Real.pi : ℂ) / (vacMix rho sigma : ℂ)
                * ((sigma x : ℂ) / 2 * p1c s (sigma x) + p2c s (sigma x)))))
      = (∑ x, ((rho x : ℂ) * (sigma x : ℂ))
          * ((Real.pi : ℂ) / (vacMix rho sigma : ℂ) * p1c s (sigma x)
             + ((Real.pi : ℂ) ^ 2 / (vacMix rho sigma : ℂ) ^ 2)
               * (∑ n, (rho n : ℂ) * (sigma n : ℂ) ^ 2)
               * ((sigma x : ℂ) / 2 * p1c s (sigma x) + p2c s (sigma x))))
      from by apply Finset.sum_congr rfl; intro x _; ring,
    sum_distrib_prod2 (fun x => (rho x : ℂ) * (sigma x : ℂ))
      (fun x => (Real.pi : ℂ) / (vacMix rho sigma : ℂ) * p1c s (sigma x))
      (fun x => (sigma x : ℂ) / 2 * p1c s (sigma x) + p2c s (sigma x))
      (fun n => (rho n : ℂ) * (sigma n : ℂ) ^ 2)
      ((Real.pi : ℂ) ^ 2 / (vacMix rho sigma : ℂ) ^ 2)]
  have neg_sum2 : ∀ (F : Fin N → Fin N → ℂ), -(∑ m, ∑ n, F m n) = ∑ m, ∑ n, -(F m n) := by
    intro F; rw [neg_eq_neg_one_mul, Finset.mul_sum]; simp_rw [Finset.mul_sum, neg_one_mul]
  have hS : (∑ x, (rho x : ℂ)
        * (2 * (Real.pi : ℂ) / (vacMix rho sigma : ℂ)
            * ((sigma x : ℂ) / 2 * p1c s (sigma x) + p2c s (sigma x))))
      + (∑ m, (rho m : ℂ) * (sigma m : ℂ)
          * ((Real.pi : ℂ) / (vacMix rho sigma : ℂ) * p1c s (sigma m)))
      = 2 * (Real.pi : ℂ) / (vacMix rho sigma : ℂ)
        * ∑ m, (rho m : ℂ) * ((sigma m : ℂ) * p1c s (sigma m) + p2c s (sigma m)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro m _; ring
  have hDbl : -((Real.pi : ℂ) ^ 2 / (vacMix rho sigma : ℂ) ^ 2
        * ∑ m, ∑ n, (rho m : ℂ) * (sigma m : ℂ) * ((rho n : ℂ) * (sigma n : ℂ) ^ 2)
            * ((sigma m : ℂ) / 2 * p1c s (sigma m) + p2c s (sigma m)))
      + (∑ x, ∑ x_1, (rho x : ℂ) * (rho x_1 : ℂ) * (sigma x_1 : ℂ)
          * (2 * (Real.pi : ℂ) ^ 2 / (vacMix rho sigma : ℂ) ^ 2
              * (((sigma x : ℂ) / 2 * p1c s (sigma x) + p2c s (sigma x)) * p1c s (sigma x_1)
                 - ((sigma x_1 : ℂ) / 2 * p1c s (sigma x_1) + p2c s (sigma x_1))
                   * p1c s (sigma x))))
      = (Real.pi : ℂ) ^ 2 / (vacMix rho sigma : ℂ) ^ 2
        * ∑ x, ∑ x_1, (rho x : ℂ) * (rho x_1 : ℂ)
            * (-(sigma x : ℂ) * (sigma x_1 : ℂ) ^ 2
                * ((sigma x : ℂ) / 2 * p1c s (sigma x) + p2c s (sigma x))
               + 2 * (sigma x_1 : ℂ)
                  * (((sigma x : ℂ) / 2 * p1c s (sigma x) + p2c s (sigma x)) * p1c s (sigma x_1)
                     - ((sigma x_1 : ℂ) / 2 * p1c s (sigma x_1) + p2c s (sigma x_1))
                       * p1c s (sigma x))) := by
    simp_rw [Finset.mul_sum]
    rw [neg_sum2, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro m _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro n _
    ring
  rw [← hS, ← hDbl]; ring


/-- **The A6 → A7 scalar closure** `det(I − VₒUₒ) = detTL` (general `N`, complex `s`).  Chains
`detVU_expand` (A6) → `A6toCanon` → `sdMatch` (`Σ∑ρρ A6sd = Σ∑ρρ detTLsd`) → `detTLtoCanon` (A7).
With `det_Q0_mat_c_phys_eq_two_by_two` this gives the general-`N` Appendix **denominator** bridge
`det Q̂₀(s) = detTL`. Axiom-clean. -/
theorem det_eq_detTL {N : ℕ} {sigma rho : Fin N → ℝ} {s : ℂ} (hs : s ≠ 0)
    (hvac : vacMix rho sigma ≠ 0) (hrho : ∀ i, 0 ≤ rho i) :
    (1 - VmatC s sigma rho * UmatC s sigma rho).det = detTL s rho sigma := by
  rw [detVU_expand hrho, A6toCanon hvac, detTLtoCanon sigma rho s, sdMatch hs]

/-- **Numerator-bridge B-combination.**  The off-identity entry of `[Q̂₀(s)]⁻¹ = I + Uₒ(I−VₒUₒ)⁻¹Vₒ`
is `√(ρᵢρⱼ)e^{−sλᵢⱼ}·B_ij/detTL` with `B_ij = fFunC_i(1−m₁₁) + gFunC_i·m₁₀ + σⱼ(fFunC_i·m₀₁ +
gFunC_i(1−m₀₀))` (`adj` of the `2×2` `I−VₒUₒ`, `m_kl = (VₒUₒ)_kl`).  Its four `m_kl`-sum terms
combine into the single sum `Σ_p ρ_p(σⱼ−σ_p)(fFunC_i gFunC_p − gFunC_i fFunC_p)` — whose summand
`FG_antisym` reduces to `(2π²/Δ²)(a_i φ1_p − a_p φ1_i)`.  This is the structural step of the
numerator match `B_ij·Δ = 2π·Wtl_ij` (numerically `1e-15`; single-sum, no symmetrisation — after
`φ2 = φ1/s +
σ²/2s` and expanding `ξ₂`/`ξ₃`, the non-sum parts agree at `2π(φ2_i + (σ_i+σ_j)/2·φ1_i)` and the
single sums match; the final scalar sum-bookkeeping is the remaining piece). -/
theorem Bsum_combine {N : ℕ} (s : ℂ) (sigma rho : Fin N → ℝ) (i j : Fin N) :
    -(fFunC rho sigma i s * ∑ p, (rho p : ℂ) * (sigma p : ℂ) * gFunC rho sigma p s)
      + gFunC rho sigma i s * ∑ p, (rho p : ℂ) * (sigma p : ℂ) * fFunC rho sigma p s
      + (sigma j : ℂ) * (fFunC rho sigma i s * ∑ p, (rho p : ℂ) * gFunC rho sigma p s)
      - (sigma j : ℂ) * (gFunC rho sigma i s * ∑ p, (rho p : ℂ) * fFunC rho sigma p s)
    = ∑ p, (rho p : ℂ) * ((sigma j : ℂ) - (sigma p : ℂ))
        * (fFunC rho sigma i s * gFunC rho sigma p s
           - gFunC rho sigma i s * fFunC rho sigma p s) := by
  have neg_sum1 : ∀ (F : Fin N → ℂ), -(∑ p, F p) = ∑ p, -(F p) := fun F => by
    rw [neg_eq_neg_one_mul, Finset.mul_sum]; simp_rw [neg_one_mul]
  simp_rw [Finset.mul_sum]
  rw [neg_sum1, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro p _
  ring

/-- **Wtl side, canonical form**: `2π·Wtl_ij = NS + Σ_p ρ_p·R_p`, `NS = 2π(φ2_i + (σᵢ+σⱼ)/2 φ1_i)`;
unfold `Wtl`, bridge `phi/Δ/ξ`, and combine its four `ξ`/`φ`-sums into one `Σ_p ρ_p·R_p`. -/
theorem hRHS {N : ℕ} (sigma rho : Fin N → ℝ) (s : ℂ) (i j : Fin N)
    (hvac : vacMix rho sigma ≠ 0) :
    2 * Real.pi * Wtl s rho sigma i j
    = 2 * Real.pi * (p2c s (sigma i)
          + ((sigma i : ℂ) + (sigma j : ℂ)) / 2 * p1c s (sigma i))
      + ∑ p, (rho p : ℂ) * ((Real.pi : ℂ) ^ 2 / (vacMix rho sigma : ℂ)
          * (p2c s (sigma i) * (sigma p : ℂ) ^ 3
             + 1 / 2 * p1c s (sigma i) * (sigma i : ℂ) * (sigma j : ℂ) * (sigma p : ℂ) ^ 2
             + p1c s (sigma i) * p1c s (sigma p)
                 * ((sigma p : ℂ) - (sigma i : ℂ)) * ((sigma p : ℂ) - (sigma j : ℂ))
             + (sigma i : ℂ) ^ 2 * p2c s (sigma p) * ((sigma j : ℂ) - (sigma p : ℂ)))) := by
  have hD : (Delta rho sigma : ℂ) = (vacMix rho sigma : ℂ) := by
    simp only [Delta, vacMix, etaMix, xiMom]
  have hx2 : (xiMom rho sigma 2 : ℂ) = ∑ n, (rho n : ℂ) * (sigma n : ℂ) ^ 2 := by
    simp only [xiMom]; push_cast; ring
  have hx3 : (xiMom rho sigma 3 : ℂ) = ∑ n, (rho n : ℂ) * (sigma n : ℂ) ^ 3 := by
    simp only [xiMom]; push_cast; ring
  have hvacC : (vacMix rho sigma : ℂ) ≠ 0 := by exact_mod_cast hvac
  rw [Wtl]
  simp only [← p1c_eq_phi1, ← p2c_eq_phi2, hD, hx2, hx3]
  push_cast
  rw [show (∑ p, (rho p : ℂ) * ((Real.pi : ℂ) ^ 2 / (vacMix rho sigma : ℂ)
        * (p2c s (sigma i) * (sigma p : ℂ) ^ 3
           + 1 / 2 * p1c s (sigma i) * (sigma i : ℂ) * (sigma j : ℂ) * (sigma p : ℂ) ^ 2
           + p1c s (sigma i) * p1c s (sigma p)
               * ((sigma p : ℂ) - (sigma i : ℂ)) * ((sigma p : ℂ) - (sigma j : ℂ))
           + (sigma i : ℂ) ^ 2 * p2c s (sigma p) * ((sigma j : ℂ) - (sigma p : ℂ)))))
      = (Real.pi : ℂ) ^ 2 / (vacMix rho sigma : ℂ) * p2c s (sigma i)
          * ∑ n, (rho n : ℂ) * (sigma n : ℂ) ^ 3
        + (Real.pi : ℂ) ^ 2 / (2 * (vacMix rho sigma : ℂ)) * p1c s (sigma i)
            * (sigma i : ℂ) * (sigma j : ℂ) * ∑ n, (rho n : ℂ) * (sigma n : ℂ) ^ 2
        + (Real.pi : ℂ) ^ 2 / (vacMix rho sigma : ℂ) * p1c s (sigma i)
            * ∑ x, (rho x : ℂ) * p1c s (sigma x)
                * ((sigma x : ℂ) - (sigma i : ℂ)) * ((sigma x : ℂ) - (sigma j : ℂ))
        + (Real.pi : ℂ) ^ 2 / (vacMix rho sigma : ℂ) * (sigma i : ℂ) ^ 2
            * ∑ x, (rho x : ℂ) * p2c s (sigma x) * ((sigma j : ℂ) - (sigma x : ℂ))
      from by
        symm
        simp only [Finset.mul_sum]
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro p _; ring]
  ring

/-- **B side, canonical form**: `B_ij·Δ = NS + Σ_p ρ_p·L_p`, same `NS`.  Reshape `B_ij` (via
`Bsum_combine`+`FG_antisym`), distribute `Δ`, unfold `fFunC`/`gFunC`, and combine the two sums (the
`ξ₂` sum and the FG sum) into one `Σ_p ρ_p·L_p`. -/
theorem hLHS {N : ℕ} (sigma rho : Fin N → ℝ) (s : ℂ) (i j : Fin N)
    (hvac : vacMix rho sigma ≠ 0) :
    (fFunC rho sigma i s * (1 - ∑ p, (rho p : ℂ) * (sigma p : ℂ) * gFunC rho sigma p s)
     + gFunC rho sigma i s * ∑ p, (rho p : ℂ) * (sigma p : ℂ) * fFunC rho sigma p s
     + (sigma j : ℂ) * (fFunC rho sigma i s * ∑ p, (rho p : ℂ) * gFunC rho sigma p s
        + gFunC rho sigma i s * (1 - ∑ p, (rho p : ℂ) * fFunC rho sigma p s)))
    * (vacMix rho sigma : ℂ)
    = 2 * Real.pi * (p2c s (sigma i)
          + ((sigma i : ℂ) + (sigma j : ℂ)) / 2 * p1c s (sigma i))
      + ∑ p, (rho p : ℂ) * ((sigma j : ℂ) * ((Real.pi : ℂ) ^ 2 / (vacMix rho sigma : ℂ))
          * ((sigma i : ℂ) / 2 * p1c s (sigma i) + p2c s (sigma i)) * (sigma p : ℂ) ^ 2
        + ((sigma j : ℂ) - (sigma p : ℂ)) * (2 * (Real.pi : ℂ) ^ 2 / (vacMix rho sigma : ℂ) ^ 2)
            * (((sigma i : ℂ) / 2 * p1c s (sigma i) + p2c s (sigma i)) * p1c s (sigma p)
               - ((sigma p : ℂ) / 2 * p1c s (sigma p) + p2c s (sigma p)) * p1c s (sigma i))
            * (vacMix rho sigma : ℂ)) := by
  have hvacC : (vacMix rho sigma : ℂ) ≠ 0 := by exact_mod_cast hvac
  rw [show (fFunC rho sigma i s * (1 - ∑ p, (rho p : ℂ) * (sigma p : ℂ) * gFunC rho sigma p s)
     + gFunC rho sigma i s * ∑ p, (rho p : ℂ) * (sigma p : ℂ) * fFunC rho sigma p s
     + (sigma j : ℂ) * (fFunC rho sigma i s * ∑ p, (rho p : ℂ) * gFunC rho sigma p s
        + gFunC rho sigma i s * (1 - ∑ p, (rho p : ℂ) * fFunC rho sigma p s)))
      = fFunC rho sigma i s + (sigma j : ℂ) * gFunC rho sigma i s
        + (-(fFunC rho sigma i s * ∑ p, (rho p : ℂ) * (sigma p : ℂ) * gFunC rho sigma p s)
           + gFunC rho sigma i s * ∑ p, (rho p : ℂ) * (sigma p : ℂ) * fFunC rho sigma p s
           + (sigma j : ℂ) * (fFunC rho sigma i s * ∑ p, (rho p : ℂ) * gFunC rho sigma p s)
           - (sigma j : ℂ) * (gFunC rho sigma i s * ∑ p, (rho p : ℂ) * fFunC rho sigma p s))
      from by ring,
    Bsum_combine s sigma rho i j]
  simp_rw [FG_antisym s sigma rho i]
  rw [add_mul, add_mul, Finset.sum_mul]
  simp only [fFunC, gFunC, xi2]
  push_cast
  rw [show (∑ p, (rho p : ℂ) * ((sigma j : ℂ) * ((Real.pi : ℂ) ^ 2 / (vacMix rho sigma : ℂ))
          * ((sigma i : ℂ) / 2 * p1c s (sigma i) + p2c s (sigma i)) * (sigma p : ℂ) ^ 2
        + ((sigma j : ℂ) - (sigma p : ℂ)) * (2 * (Real.pi : ℂ) ^ 2 / (vacMix rho sigma : ℂ) ^ 2)
            * (((sigma i : ℂ) / 2 * p1c s (sigma i) + p2c s (sigma i)) * p1c s (sigma p)
               - ((sigma p : ℂ) / 2 * p1c s (sigma p) + p2c s (sigma p)) * p1c s (sigma i))
            * (vacMix rho sigma : ℂ)))
      = (sigma j : ℂ) * ((Real.pi : ℂ) ^ 2 / (vacMix rho sigma : ℂ))
          * ((sigma i : ℂ) / 2 * p1c s (sigma i) + p2c s (sigma i))
          * ∑ n, (rho n : ℂ) * (sigma n : ℂ) ^ 2
        + ∑ x, (rho x : ℂ) * ((sigma j : ℂ) - (sigma x : ℂ))
            * (2 * (Real.pi : ℂ) ^ 2 / (vacMix rho sigma : ℂ) ^ 2
                * (((sigma i : ℂ) / 2 * p1c s (sigma i) + p2c s (sigma i)) * p1c s (sigma x)
                   - ((sigma x : ℂ) / 2 * p1c s (sigma x) + p2c s (sigma x)) * p1c s (sigma i)))
            * (vacMix rho sigma : ℂ)
      from by
        symm
        simp only [Finset.mul_sum]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro p _; ring]
  field_simp
  ring

/-- **Numerator scalar match** `B_ij·Δ = 2π·Wtl_ij` (general `N`, complex `s`).  `hLHS`/`hRHS` put
both sides in the canonical `NS + Σ_p ρ_p·(summand)` form with a common non-sum `NS`; the summands
`L_p`, `R_p` agree pointwise after `φ2 = φ1/s + σ²/2s` (`p2c_eq_p1c`) — `field_simp; ring`.  This is
the numerator analogue of `det_eq_detTL` (single-sum, no symmetrisation).  With the `2×2` `adj/det`
`Uₒ`/`Vₒ` assembly gives the entrywise `{[Q̂₀]⁻¹}_ij = δ_ij + 2π√(ρρ)Wtl_ij e^{−sλ}/(Δ·detTL)`. -/
theorem numMatch {N : ℕ} {sigma rho : Fin N → ℝ} {s : ℂ} (hs : s ≠ 0)
    (hvac : vacMix rho sigma ≠ 0) (i j : Fin N) :
    (fFunC rho sigma i s * (1 - ∑ p, (rho p : ℂ) * (sigma p : ℂ) * gFunC rho sigma p s)
     + gFunC rho sigma i s * ∑ p, (rho p : ℂ) * (sigma p : ℂ) * fFunC rho sigma p s
     + (sigma j : ℂ) * (fFunC rho sigma i s * ∑ p, (rho p : ℂ) * gFunC rho sigma p s
        + gFunC rho sigma i s * (1 - ∑ p, (rho p : ℂ) * fFunC rho sigma p s)))
    * (vacMix rho sigma : ℂ)
    = 2 * Real.pi * Wtl s rho sigma i j := by
  rw [hLHS sigma rho s i j hvac, hRHS sigma rho s i j hvac]
  congr 1
  apply Finset.sum_congr rfl; intro p _
  have hvacC : (vacMix rho sigma : ℂ) ≠ 0 := by exact_mod_cast hvac
  simp only [p2c_eq_p1c s (sigma i) hs, p2c_eq_p1c s (sigma p) hs]
  field_simp
  ring

/-- `Uₒ · adj(I−VₒUₒ) · Vₒ` entrywise = `√(ρᵢρⱼ)·e^{−sλ}·B_ij` (`B_ij` = the `numMatch` bracket). -/
theorem UadjV {N : ℕ} (s : ℂ) (sigma rho : Fin N → ℝ) (hrho : ∀ i, 0 ≤ rho i) (i j : Fin N) :
    (UmatC s sigma rho * (1 - VmatC s sigma rho * UmatC s sigma rho).adjugate
      * VmatC s sigma rho) i j
    = (Real.sqrt (rho i * rho j) : ℂ) * Complex.exp (-(((sigma j : ℂ) - (sigma i : ℂ)) / 2 * s))
      * (fFunC rho sigma i s * (1 - ∑ p, (rho p : ℂ) * (sigma p : ℂ) * gFunC rho sigma p s)
         + gFunC rho sigma i s * ∑ p, (rho p : ℂ) * (sigma p : ℂ) * fFunC rho sigma p s
         + (sigma j : ℂ) * (fFunC rho sigma i s * ∑ p, (rho p : ℂ) * gFunC rho sigma p s
            + gFunC rho sigma i s * (1 - ∑ p, (rho p : ℂ) * fFunC rho sigma p s))) := by
  have hrr : (Real.sqrt (rho i * rho j) : ℂ)
      = (Real.sqrt (rho i) : ℂ) * (Real.sqrt (rho j) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.sqrt_mul (hrho i)]
  have hee : Complex.exp (-(((sigma j : ℂ) - (sigma i : ℂ)) / 2 * s))
      = Complex.exp (s * (sigma i : ℂ) / 2) * Complex.exp (-(s * (sigma j : ℂ) / 2)) := by
    rw [← Complex.exp_add]; ring_nf
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.sub_apply,
    Matrix.one_apply, VU00 s sigma rho hrho, VU01 s sigma rho hrho, VU10 s sigma rho hrho,
    VU11 s sigma rho hrho, UmatC, VmatC, Fin.isValue]
  rw [hrr, hee]
  norm_num
  ring

/-- **The general-`N` Appendix entrywise inverse bridge**
`{[Q̂₀(s)]⁻¹}_ij = δ_ij + 2π√(ρᵢρⱼ)·Wtl_ij·e^{−sλᵢⱼ}/(Δ·detTL)`.  Assembles the Woodbury inverse
`[Q̂₀]⁻¹ = I + Uₒ(I−VₒUₒ)⁻¹Vₒ`, the `2×2` `(I−VₒUₒ)⁻¹ = detTL⁻¹•adj`, `UadjV`, and the scalar match
`numMatch` (`B_ij·Δ = 2π·Wtl_ij`). -/
theorem Q0_inv_entry_bridge {N : ℕ} {sigma rho : Fin N → ℝ} {s : ℂ} (hs : s ≠ 0)
    (hvac : vacMix rho sigma ≠ 0) (hrho : ∀ i, 0 ≤ rho i)
    (hdet : IsUnit (Q0_mat_c_phys s sigma rho).det) (i j : Fin N) :
    (Q0_mat_c_phys s sigma rho)⁻¹ i j
    = (if i = j then (1 : ℂ) else 0)
      + 2 * Real.pi * (Real.sqrt (rho i * rho j) : ℂ) * Wtl s rho sigma i j
          * Complex.exp (-(((sigma j : ℂ) - (sigma i : ℂ)) / 2 * s))
        / ((vacMix rho sigma : ℂ) * detTL s rho sigma) := by
  have hvacC : (vacMix rho sigma : ℂ) ≠ 0 := by exact_mod_cast hvac
  have hQdet : (Q0_mat_c_phys s sigma rho).det = detTL s rho sigma := by
    rw [det_Q0_mat_c_phys_eq_two_by_two hs hvac hrho, det_eq_detTL hs hvac hrho]
  have hdetTLne : detTL s rho sigma ≠ 0 := hQdet ▸ hdet.ne_zero
  have hinv : (1 - VmatC s sigma rho * UmatC s sigma rho)⁻¹
      = (detTL s rho sigma)⁻¹ • (1 - VmatC s sigma rho * UmatC s sigma rho).adjugate := by
    rw [Matrix.inv_def, det_eq_detTL hs hvac hrho, Ring.inverse_eq_inv]
  rw [Q0_mat_c_phys_inv_eq hs hvac hrho hdet, Matrix.add_apply, Matrix.one_apply]
  congr 1
  rw [hinv, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul,
      UadjV s sigma rho hrho i j]
  have hb := numMatch hs hvac i j
  rw [eq_div_iff (mul_ne_zero hvacC hdetTLne)]
  field_simp
  linear_combination (Real.sqrt (rho i * rho j) : ℂ) * hb

end FMSA.ComplexRankTwo
