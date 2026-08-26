/-
Copyright (c) 2026 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import LeanCode.YukawaOZMix.MSAMixtureBreakpointScheme

/-!
# BRK all-orders in-core breakpoints — the MATHEMATICAL-INDUCTION route (alternative proof)

The BRK result "every `K`-order derivative of the exact-MSA core has its only interior breakpoint at
`|λ_ij|`, no other breakpoints" is already proved in `MSAMixtureBreakpointScheme.lean` via the
coefficient/basis separation — `contDiffOn_paramDeriv_coeffBasis`, a **one-shot** using Mathlib's
`iteratedDeriv_fun_sum` / `iteratedDeriv_const_mul`.

This file gives the **explicit-induction** proof of the same result (tasks BRK.14/BRK.15).  The crux
is that the coupling `K` enters only the amplitudes: for a `K`-free `r`-basis `b k`,

    ∂ⁿ_K (Σ_k c k(K) · b k(r))  =  Σ_k (∂ⁿ_K c k)(K) · b k(r),

which we prove **by induction on `n`** (`iteratedDeriv_coeffBasis_eq`): base `iteratedDeriv 0 = id`;
step `∂^{n+1}=∂∘∂ⁿ`, with `∂` distributed over the finite sum (`deriv_fun_sum`) and past the
`K`-constant `b k r` (`deriv_mul_const`).  The whole chain (`gForm → coreForm → matCoreUneq`,
inner/outer pieces) is then re-derived on this induction — same statements as the one-shot versions,
std-3, but independent of the Mathlib `iteratedDeriv` sum/mul lemmas.
-/

open MSAMixture MSAMixtureCoreUneq
open scoped BigOperators

namespace FMSA.ExactMSA.Breakpoint

variable {N : ℕ}

/-- ⭐ **BRK.14 — the `iteratedDeriv`/coeff-basis commutation, BY INDUCTION on `n`.**  With the
coupling `K` in the coefficients only (the `r`-basis `b k` fixed), the `n`-th `K`-derivative of
`Σ_k c k(K)·b k(r)` is `Σ_k (∂ⁿ_K c k)(K)·b k(r)`.  Base: `iteratedDeriv 0 = id`.  Step:
`∂^{n+1} = ∂ ∘ ∂ⁿ`; `∂` distributes over the finite sum and past the `K`-constant `b k r`. -/
theorem iteratedDeriv_coeffBasis_eq {ι : Type*} (I : Finset ι) (c b : ι → ℝ → ℝ)
    (hc : ∀ k ∈ I, ContDiff ℝ ⊤ (c k)) (r : ℝ) (n : ℕ) :
    iteratedDeriv n (fun K => ∑ k ∈ I, c k K * b k r)
      = fun K => ∑ k ∈ I, iteratedDeriv n (c k) K * b k r := by
  induction n with
  | zero => funext K; simp [iteratedDeriv_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext K
    have hdiff : ∀ k ∈ I, DifferentiableAt ℝ (fun K => iteratedDeriv n (c k) K * b k r) K := by
      intro k hk
      exact (((hc k hk).differentiable_iteratedDeriv n
        (by exact_mod_cast lt_top_iff_ne_top.mpr (by simp))).differentiableAt).mul_const _
    rw [deriv_fun_sum hdiff]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [deriv_mul_const ((hc k hk).differentiable_iteratedDeriv n
      (by exact_mod_cast lt_top_iff_ne_top.mpr (by simp))).differentiableAt, ← iteratedDeriv_succ]

/-- **BRK.15a — abstract Step 2, BY INDUCTION.**  Same statement as
`contDiffOn_paramDeriv_coeffBasis`, but from `iteratedDeriv_coeffBasis_eq` (induction) rather than
Mathlib's `iteratedDeriv_fun_sum`: rewrite the `n`-th `K`-derivative to `Σ_k (const)·b k(r)`, a
finite sum of `ContDiffOn` functions in `r`. -/
theorem contDiffOn_paramDeriv_coeffBasis_byInduction {ι : Type*} (I : Finset ι) (c b : ι → ℝ → ℝ)
    {s : Set ℝ} (hc : ∀ k ∈ I, ContDiff ℝ ⊤ (c k)) (hb : ∀ k ∈ I, ContDiffOn ℝ ⊤ (b k) s)
    (n : ℕ) (K₀ : ℝ) :
    ContDiffOn ℝ ⊤ (fun r => iteratedDeriv n (fun K => ∑ k ∈ I, c k K * b k r) K₀) s := by
  have hrw : (fun r => iteratedDeriv n (fun K => ∑ k ∈ I, c k K * b k r) K₀)
      = (fun r => ∑ k ∈ I, iteratedDeriv n (c k) K₀ * b k r) := by
    funext r; rw [iteratedDeriv_coeffBasis_eq I c b hc r n]
  rw [hrw]
  exact ContDiffOn.sum (fun k hk => contDiffOn_const.mul (hb k hk))

/-- **BRK.15b — the 7-basis `gForm`, all orders, BY INDUCTION.**  Instantiates
`contDiffOn_paramDeriv_coeffBasis_byInduction` at `Fin 7` with the fixed
`r`-basis `{1,r,r²,r³,r⁴,e^{−zr},e^{zr}}`. -/
theorem gForm_paramDeriv_contDiffOn_byInduction (c0 c1 c2 c3 c4 cEm cEp : ℝ → ℝ) (z : ℝ)
    {s : Set ℝ} (h0 : ContDiff ℝ ⊤ c0) (h1 : ContDiff ℝ ⊤ c1) (h2 : ContDiff ℝ ⊤ c2)
    (h3 : ContDiff ℝ ⊤ c3) (h4 : ContDiff ℝ ⊤ c4) (hm : ContDiff ℝ ⊤ cEm) (hp : ContDiff ℝ ⊤ cEp)
    (n : ℕ) (K₀ : ℝ) :
    ContDiffOn ℝ ⊤ (fun r => iteratedDeriv n
      (fun K => gForm (c0 K) (c1 K) (c2 K) (c3 K) (c4 K) (cEm K) (cEp K) z r) K₀) s := by
  have hfun : (fun r => iteratedDeriv n
        (fun K => gForm (c0 K) (c1 K) (c2 K) (c3 K) (c4 K) (cEm K) (cEp K) z r) K₀)
      = (fun r => iteratedDeriv n
          (fun K => ∑ k, (![c0, c1, c2, c3, c4, cEm, cEp] : Fin 7 → ℝ → ℝ) k K *
            (![fun _ => 1, fun r => r, fun r => r ^ 2, fun r => r ^ 3, fun r => r ^ 4,
              fun r => Real.exp (-z * r), fun r => Real.exp (z * r)] : Fin 7 → ℝ → ℝ) k r) K₀) := by
    funext r; congr 1; funext K
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
      gForm]
    ring
  rw [hfun]
  refine contDiffOn_paramDeriv_coeffBasis_byInduction Finset.univ _ _ ?_ ?_ n K₀
  · intro k _
    fin_cases k <;> assumption
  · intro k _; fin_cases k
    · change ContDiffOn ℝ ⊤ (fun _ => (1 : ℝ)) s; fun_prop
    · change ContDiffOn ℝ ⊤ (fun r => r) s; fun_prop
    · change ContDiffOn ℝ ⊤ (fun r => r ^ 2) s; fun_prop
    · change ContDiffOn ℝ ⊤ (fun r => r ^ 3) s; fun_prop
    · change ContDiffOn ℝ ⊤ (fun r => r ^ 4) s; fun_prop
    · change ContDiffOn ℝ ⊤ (fun r => Real.exp (-z * r)) s; fun_prop
    · change ContDiffOn ℝ ⊤ (fun r => Real.exp (z * r)) s; fun_prop

/-- **BRK.15c — the core piece `gForm/(2π r)`, all orders, BY INDUCTION.**  Same as
`coreForm_paramDeriv_contDiffOn`, on `gForm_paramDeriv_contDiffOn_byInduction`. -/
theorem coreForm_paramDeriv_contDiffOn_byInduction (c0 c1 c2 c3 c4 cEm cEp : ℝ → ℝ) (z : ℝ)
    {s : Set ℝ} (h0 : ContDiff ℝ ⊤ c0) (h1 : ContDiff ℝ ⊤ c1) (h2 : ContDiff ℝ ⊤ c2)
    (h3 : ContDiff ℝ ⊤ c3) (h4 : ContDiff ℝ ⊤ c4) (hm : ContDiff ℝ ⊤ cEm) (hp : ContDiff ℝ ⊤ cEp)
    (hs : ∀ r ∈ s, r ≠ 0) (n : ℕ) (K₀ : ℝ) :
    ContDiffOn ℝ ⊤ (fun r => iteratedDeriv n
      (fun K => gForm (c0 K) (c1 K) (c2 K) (c3 K) (c4 K) (cEm K) (cEp K) z r /
        (2 * Real.pi * r)) K₀) s := by
  have hgK : ∀ r : ℝ, ContDiff ℝ ⊤
      (fun K => gForm (c0 K) (c1 K) (c2 K) (c3 K) (c4 K) (cEm K) (cEp K) z r) := by
    intro r; unfold gForm; fun_prop
  have hrw : (fun r => iteratedDeriv n
        (fun K => gForm (c0 K) (c1 K) (c2 K) (c3 K) (c4 K) (cEm K) (cEp K) z r /
          (2 * Real.pi * r)) K₀)
      = (fun r => iteratedDeriv n
          (fun K => gForm (c0 K) (c1 K) (c2 K) (c3 K) (c4 K) (cEm K) (cEp K) z r) K₀
            / (2 * Real.pi * r)) := by
    funext r
    have he : (fun K =>
          gForm (c0 K) (c1 K) (c2 K) (c3 K) (c4 K) (cEm K) (cEp K) z r / (2 * Real.pi * r))
        = (fun K => (1 / (2 * Real.pi * r)) *
            gForm (c0 K) (c1 K) (c2 K) (c3 K) (c4 K) (cEm K) (cEp K) z r) := by
      funext K; ring
    rw [he, iteratedDeriv_const_mul _ ((hgK r).contDiffAt.of_le le_top)]; ring
  rw [hrw]
  refine ContDiffOn.div
    (gForm_paramDeriv_contDiffOn_byInduction c0 c1 c2 c3 c4 cEm cEp z
      h0 h1 h2 h3 h4 hm hp n K₀)
    (by fun_prop) (fun r hr => mul_ne_zero (by positivity) (hs r hr))

/-- ⭐ **BRK.15 (inner, all orders, BY INDUCTION).**  Every `K`-derivative of `matCoreUneq` is
`ContDiffOn ℝ ⊤` on `(0, |λ_ij|)` — proved via the induction chain, matching
`matCoreUneq_paramDeriv_contDiffOn_inner`. -/
theorem matCoreUneq_paramDeriv_contDiffOn_inner_byInduction (z : ℝ) (σ : Fin N → ℝ)
    (ρ A : ℝ → Fin N → ℝ) (qp Wt Ct : ℝ → Fin N → Fin N → ℝ) (i j : Fin N)
    (hρ : ∀ l, ContDiff ℝ ⊤ (fun K => ρ K l)) (hA : ∀ l, ContDiff ℝ ⊤ (fun K => A K l))
    (hqp : ∀ a b, ContDiff ℝ ⊤ (fun K => qp K a b)) (hWt : ∀ a b, ContDiff ℝ ⊤ (fun K => Wt K a b))
    (hCt : ∀ a b, ContDiff ℝ ⊤ (fun K => Ct K a b)) (n : ℕ) (K₀ : ℝ) :
    ContDiffOn ℝ ⊤ (fun r => iteratedDeriv n
      (fun K => matCoreUneq z (ρ K) σ (A K) (qp K) (Wt K) (Ct K) i j r) K₀)
      (Set.Ioo 0 (lamA σ i j)) := by
  have hc0 : ContDiff ℝ ⊤ (fun K => cC0i z (ρ K) σ (A K) (qp K) (Wt K) (Ct K) i j) := by
    unfold cC0i; fun_prop
  have hc1 : ContDiff ℝ ⊤ (fun K => cC1i z (ρ K) σ (A K) (qp K) (Wt K) (Ct K) i j) := by
    unfold cC1i; fun_prop
  have hcm : ContDiff ℝ ⊤ (fun K => cEmi z (ρ K) σ (A K) (qp K) (Wt K) (Ct K) i j) := by
    unfold cEmi; fun_prop
  have hcp : ContDiff ℝ ⊤ (fun K => cEpi z (ρ K) σ (A K) (qp K) (Wt K) (Ct K) i j) := by
    unfold cEpi; fun_prop
  have hbase := coreForm_paramDeriv_contDiffOn_byInduction
    (fun K => cC0i z (ρ K) σ (A K) (qp K) (Wt K) (Ct K) i j)
    (fun K => cC1i z (ρ K) σ (A K) (qp K) (Wt K) (Ct K) i j)
    (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ))
    (fun K => cEmi z (ρ K) σ (A K) (qp K) (Wt K) (Ct K) i j)
    (fun K => cEpi z (ρ K) σ (A K) (qp K) (Wt K) (Ct K) i j) z
    hc0 hc1 contDiff_const contDiff_const contDiff_const hcm hcp
    (s := Set.Ioo 0 (lamA σ i j)) (fun r hr => ne_of_gt hr.1) n K₀
  refine ContDiffOn.congr hbase ?_
  intro r hr
  have hFG : (fun K => matCoreUneq z (ρ K) σ (A K) (qp K) (Wt K) (Ct K) i j r)
      = (fun K => gForm (cC0i z (ρ K) σ (A K) (qp K) (Wt K) (Ct K) i j)
          (cC1i z (ρ K) σ (A K) (qp K) (Wt K) (Ct K) i j) 0 0 0
          (cEmi z (ρ K) σ (A K) (qp K) (Wt K) (Ct K) i j)
          (cEpi z (ρ K) σ (A K) (qp K) (Wt K) (Ct K) i j) z r / (2 * Real.pi * r)) := by
    funext K
    unfold matCoreUneq
    rw [if_pos (le_of_lt hr.2)]
  rw [hFG]

/-- ⭐ **BRK.15 (outer, all orders, BY INDUCTION).**  Every `K`-derivative of `matCoreUneq` is
`ContDiffOn ℝ ⊤` on `(|λ_ij|, σ_ij)`. -/
theorem matCoreUneq_paramDeriv_contDiffOn_outer_byInduction (z : ℝ) (σ : Fin N → ℝ)
    (ρ A : ℝ → Fin N → ℝ) (qp Wt Ct : ℝ → Fin N → Fin N → ℝ) (i j : Fin N)
    (hρ : ∀ l, ContDiff ℝ ⊤ (fun K => ρ K l)) (hA : ∀ l, ContDiff ℝ ⊤ (fun K => A K l))
    (hqp : ∀ a b, ContDiff ℝ ⊤ (fun K => qp K a b)) (hWt : ∀ a b, ContDiff ℝ ⊤ (fun K => Wt K a b))
    (hCt : ∀ a b, ContDiff ℝ ⊤ (fun K => Ct K a b)) (n : ℕ) (K₀ : ℝ) :
    ContDiffOn ℝ ⊤ (fun r => iteratedDeriv n
      (fun K => matCoreUneq z (ρ K) σ (A K) (qp K) (Wt K) (Ct K) i j r) K₀)
      (Set.Ioo (lamA σ i j) (edgeHi σ i j)) := by
  have hc0 : ContDiff ℝ ⊤ (fun K => cC0o z (ρ K) σ (A K) (qp K) (Wt K) (Ct K) i j) := by
    unfold cC0o; fun_prop
  have hc1 : ContDiff ℝ ⊤ (fun K => cC1o z (ρ K) σ (A K) (qp K) (Wt K) (Ct K) i j) := by
    unfold cC1o; fun_prop
  have hc2 : ContDiff ℝ ⊤ (fun K => cC2o z (ρ K) σ (A K) (qp K) (Wt K) (Ct K) i j) := by
    unfold cC2o; fun_prop
  have hc3 : ContDiff ℝ ⊤ (fun K => cC3o z (ρ K) σ (A K) (qp K) (Wt K) (Ct K) i j) := by
    unfold cC3o; fun_prop
  have hc4 : ContDiff ℝ ⊤ (fun K => cC4o z (ρ K) σ (A K) (qp K) (Wt K) (Ct K) i j) := by
    unfold cC4o; fun_prop
  have hcm : ContDiff ℝ ⊤ (fun K => cEmo z (ρ K) σ (A K) (qp K) (Wt K) (Ct K) i j) := by
    unfold cEmo; fun_prop
  have hcp : ContDiff ℝ ⊤ (fun K => cEpo z (ρ K) σ (A K) (qp K) (Wt K) (Ct K) i j) := by
    unfold cEpo; fun_prop
  have h0 : (0 : ℝ) ≤ lamA σ i j := by unfold lamA; exact abs_nonneg _
  have hbase := coreForm_paramDeriv_contDiffOn_byInduction
    (fun K => cC0o z (ρ K) σ (A K) (qp K) (Wt K) (Ct K) i j)
    (fun K => cC1o z (ρ K) σ (A K) (qp K) (Wt K) (Ct K) i j)
    (fun K => cC2o z (ρ K) σ (A K) (qp K) (Wt K) (Ct K) i j)
    (fun K => cC3o z (ρ K) σ (A K) (qp K) (Wt K) (Ct K) i j)
    (fun K => cC4o z (ρ K) σ (A K) (qp K) (Wt K) (Ct K) i j)
    (fun K => cEmo z (ρ K) σ (A K) (qp K) (Wt K) (Ct K) i j)
    (fun K => cEpo z (ρ K) σ (A K) (qp K) (Wt K) (Ct K) i j) z
    hc0 hc1 hc2 hc3 hc4 hcm hcp
    (s := Set.Ioo (lamA σ i j) (edgeHi σ i j))
    (fun r hr => ne_of_gt (lt_of_le_of_lt h0 hr.1)) n K₀
  refine ContDiffOn.congr hbase ?_
  intro r hr
  have hFG : (fun K => matCoreUneq z (ρ K) σ (A K) (qp K) (Wt K) (Ct K) i j r)
      = (fun K => gForm (cC0o z (ρ K) σ (A K) (qp K) (Wt K) (Ct K) i j)
          (cC1o z (ρ K) σ (A K) (qp K) (Wt K) (Ct K) i j)
          (cC2o z (ρ K) σ (A K) (qp K) (Wt K) (Ct K) i j)
          (cC3o z (ρ K) σ (A K) (qp K) (Wt K) (Ct K) i j)
          (cC4o z (ρ K) σ (A K) (qp K) (Wt K) (Ct K) i j)
          (cEmo z (ρ K) σ (A K) (qp K) (Wt K) (Ct K) i j)
          (cEpo z (ρ K) σ (A K) (qp K) (Wt K) (Ct K) i j) z r / (2 * Real.pi * r)) := by
    funext K
    unfold matCoreUneq
    rw [if_neg (not_le.mpr hr.1)]
  rw [hFG]

end FMSA.ExactMSA.Breakpoint
