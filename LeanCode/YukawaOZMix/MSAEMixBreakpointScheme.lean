/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.YukawaOZMix.MSAEMixCoreUneq
import LeanCode.YukawaOZMix.MSAEMixBreakpointOrders

/-!
# BRK.8/9/12 — the exact-MSA core knot scheme, discharged against MSAEMIX.4 Stage 3

This file (1) discharges the abstract BRK.8/9/12 lemmas (piece smoothness, `K`-parameter
smoothness, and the `1/(2π r)`-divided core), then (2) **connects them to the concrete Stage-3 core
`MSAEMixCoreUneq.matCoreUneq`** (the `matCoreUneq_*` theorems at the end): the actual core is
`ContDiffOn`, at every `K`-order, on each side of its single interior breakpoint `|λ_ij|` — which
MSAEMIX.5 pins as the unique `σ_l`-free interior crossing.

Group **BRK** (`proof_notes_breakpoints_MSA.md`).  BRK.9 (Step 2 of the BRK.7 scheme) is the
`K`-independence of the exact-MSA core's knot set.  The *abstract* half is
`MSAEMixBreakpointOrders.contDiffOn_paramDeriv_coeffBasis` (K in coefficients only ⇒ K-derivatives
keep the fixed basis, no new knot).  The *concrete* half needs the exact-MSA core to actually have
that form — a finite sum `Σ_k coeff_k(K)·basis_k(r)` with **`K`-free piece boundaries and fixed
basis** — which is **MSAEMIX.4 Stage 3** (`MSAEMixCoreUneq`): the core is 2-piece on `(0, σ_ij)` at
the geometric breakpoint `|λ_ij|`, and *both* pieces are the single form `gForm` in the shared
7-basis `{1, r, r², r³, r⁴, e^{−zr}, e^{zr}}` (the inner piece is `gForm` with `c2 = c3 = c4 = 0`),
with `K` entering only through the coefficients (`c0,…,cEp`), never the fixed basis.

Feeding that basis into the abstract lemma closes BRK.9 concrete: **every `K`-derivative of the core
form is, in `r`, `ContDiffOn` on any set** — so no order adds a knot beyond `|λ_ij|`.
The only remaining input is that the amplitudes are themselves `ContDiff` in `K` (the coefficients
`ContDiff ℝ ⊤`), which the BH root supplies (polynomial/analytic in K); it is carried here
as an explicit hypothesis, not baked in.
-/

open MSAEMix
open MSAEMixCoreUneq

namespace FMSA.MSAExact.BRK

variable {N : ℕ}

/-- ⭐ **BRK.9 concrete.**  With `K` entering only the coefficients `c0..cEp` (`ContDiff ℝ ⊤`), every
`K`-derivative of the exact-MSA core form `gForm` is, as a function of `r`, `ContDiffOn ℝ ⊤` on any
set — the fixed basis `{1, r, r², r³, r⁴, e^{−zr}, e^{zr}}` carries no `K`, so no order adds a
knot.  Covers both pieces (the inner one is `gForm` with `c2 = c3 = c4 = 0`). -/
theorem gForm_paramDeriv_contDiffOn (c0 c1 c2 c3 c4 cEm cEp : ℝ → ℝ) (z : ℝ) {s : Set ℝ}
    (h0 : ContDiff ℝ ⊤ c0) (h1 : ContDiff ℝ ⊤ c1) (h2 : ContDiff ℝ ⊤ c2) (h3 : ContDiff ℝ ⊤ c3)
    (h4 : ContDiff ℝ ⊤ c4) (hm : ContDiff ℝ ⊤ cEm) (hp : ContDiff ℝ ⊤ cEp) (n : ℕ) (K₀ : ℝ) :
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
  refine contDiffOn_paramDeriv_coeffBasis Finset.univ _ _ ?_ ?_ n K₀
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

/-- **BRK.8 (Step 1) — geometric smoothness of a core piece.**  Each piece of the exact-MSA core is
the entire function `gForm` (polynomial + exponentials), smooth on all of `ℝ`.  So the core's only
interior knot is the geometric `|λ_ij|`, where `matCoreUneq` switches pieces. -/
theorem contDiff_gForm (c0 c1 c2 c3 c4 cEm cEp z : ℝ) :
    ContDiff ℝ ⊤ (fun r => gForm c0 c1 c2 c3 c4 cEm cEp z r) := by
  unfold gForm; fun_prop

/-- ⭐ **BRK.12 (Step 5) — the all-orders knot set of the core, via the closed form.**  The exact-MSA
core piece is `c = gForm / (2π r)` (`matCoreUneq`).  With `K` in the coefficients only, every
`K`-derivative `∂ⁿ_K c` is, in `r`, `ContDiffOn` on any set avoiding `r = 0` — so `c^{(n)}` has no
interior knot beyond `|λ_ij|`, at every order and every `N`.  Because Stage 3 supplies the core in
closed form, this follows from BRK.9 (`gForm_paramDeriv_contDiffOn`) plus the smooth `1/(2π r)`
factor, **without** the `n`-fold convolution/Leibniz resummation (BRK.10/11/12 as planned): the
closed form makes that route unnecessary. -/
theorem coreForm_paramDeriv_contDiffOn (c0 c1 c2 c3 c4 cEm cEp : ℝ → ℝ) (z : ℝ) {s : Set ℝ}
    (h0 : ContDiff ℝ ⊤ c0) (h1 : ContDiff ℝ ⊤ c1) (h2 : ContDiff ℝ ⊤ c2) (h3 : ContDiff ℝ ⊤ c3)
    (h4 : ContDiff ℝ ⊤ c4) (hm : ContDiff ℝ ⊤ cEm) (hp : ContDiff ℝ ⊤ cEp)
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
    (gForm_paramDeriv_contDiffOn c0 c1 c2 c3 c4 cEm cEp z h0 h1 h2 h3 h4 hm hp n K₀)
    (by fun_prop) (fun r hr => mul_ne_zero (by positivity) (hs r hr))

/-! ### Connecting the scheme to the concrete Stage-3 core `matCoreUneq`

The BRK.8/9/12 lemmas above are about the abstract piece form `gForm` / `gForm / (2π r)`.
Discharging them against MSAEMIX.4 Stage 3 (`MSAEMixCoreUneq.matCoreUneq`, the concrete 2-piece
exact-MSA core with `K`-free geometric split at `lamA σ i j = |λ_ij|`) gives the statement **about
the actual core**: `matCoreUneq` is `ContDiffOn` — at every `K`-order — on each side of the interior
`|λ_ij|`, which MSAEMIX.5 (`interior_breakpoint_eq_absLam`) pins as the unique `σ_l`-free interior
crossing.  So no order, and no intermediate species, adds a knot beyond `|λ_ij|`.

(The one link not carried here — that this closed-form `matCoreUneq` equals the Baxter convolution
`−Q'_ij + Σ_l ρ_l Q'_il ⋆ Q_jl` from first principles — is MSAEMIX.4 Stage 3's symbolic-`σ`
derivation, validated to `1e-14`; a Lean proof of that identity is a separate piecewise-convolution
task and is not attempted here.) -/

/-- **Value level, inner piece.**  On `(0, |λ_ij|)` the concrete core `matCoreUneq` reduces to its
inner `gForm / (2π r)` and is `ContDiffOn ℝ ⊤`. -/
theorem matCoreUneq_contDiffOn_inner (z : ℝ) (ρ σ A : Fin N → ℝ)
    (qp Wt Ct : Fin N → Fin N → ℝ) (i j : Fin N) :
    ContDiffOn ℝ ⊤ (fun r => matCoreUneq z ρ σ A qp Wt Ct i j r)
      (Set.Ioo 0 (lamA σ i j)) := by
  have hEq : Set.EqOn (fun r => matCoreUneq z ρ σ A qp Wt Ct i j r)
      (fun r => gForm (cC0i z ρ σ A qp Wt Ct i j) (cC1i z ρ σ A qp Wt Ct i j) 0 0 0
        (cEmi z ρ σ A qp Wt Ct i j) (cEpi z ρ σ A qp Wt Ct i j) z r / (2 * Real.pi * r))
      (Set.Ioo 0 (lamA σ i j)) := by
    intro r hr
    dsimp only
    unfold matCoreUneq
    rw [if_pos (le_of_lt hr.2)]
  refine ContDiffOn.congr ?_ hEq
  refine ContDiffOn.div ((contDiff_gForm _ _ _ _ _ _ _ z).contDiffOn) (by fun_prop) ?_
  intro r hr
  exact mul_ne_zero (by positivity) (ne_of_gt hr.1)

/-- **Value level, outer piece.**  On `(|λ_ij|, σ_ij)` the concrete core `matCoreUneq` reduces to
its outer `gForm / (2π r)` and is `ContDiffOn ℝ ⊤`. -/
theorem matCoreUneq_contDiffOn_outer (z : ℝ) (ρ σ A : Fin N → ℝ)
    (qp Wt Ct : Fin N → Fin N → ℝ) (i j : Fin N) :
    ContDiffOn ℝ ⊤ (fun r => matCoreUneq z ρ σ A qp Wt Ct i j r)
      (Set.Ioo (lamA σ i j) (edgeHi σ i j)) := by
  have hEq : Set.EqOn (fun r => matCoreUneq z ρ σ A qp Wt Ct i j r)
      (fun r => gForm (cC0o z ρ σ A qp Wt Ct i j) (cC1o z ρ σ A qp Wt Ct i j)
        (cC2o z ρ σ A qp Wt Ct i j) (cC3o z ρ σ A qp Wt Ct i j) (cC4o z ρ σ A qp Wt Ct i j)
        (cEmo z ρ σ A qp Wt Ct i j) (cEpo z ρ σ A qp Wt Ct i j) z r / (2 * Real.pi * r))
      (Set.Ioo (lamA σ i j) (edgeHi σ i j)) := by
    intro r hr
    dsimp only
    unfold matCoreUneq
    rw [if_neg (not_le.mpr hr.1)]
  refine ContDiffOn.congr ?_ hEq
  refine ContDiffOn.div ((contDiff_gForm _ _ _ _ _ _ _ z).contDiffOn) (by fun_prop) ?_
  intro r hr
  have h0 : (0 : ℝ) ≤ lamA σ i j := by unfold lamA; exact abs_nonneg _
  exact mul_ne_zero (by positivity) (ne_of_gt (lt_of_le_of_lt h0 hr.1))

/-- ⭐ **Capstone (value level).**  For positive diameters with `σ_i ≠ σ_j`, the concrete exact-MSA
core `matCoreUneq` is smooth on the whole core interval `(0, σ_ij)` except at the single interior
breakpoint `|λ_ij| = lamA σ i j` — which MSAEMIX.5 (`interior_breakpoint_eq_absLam`) shows is the
unique `σ_l`-free interior crossing.  This is BRK's "no other breakpoints", now **about the actual
Stage-3 core**, not just the abstract `gForm`. -/
theorem matCoreUneq_smooth_off_absLam (z : ℝ) (ρ σ A : Fin N → ℝ)
    (qp Wt Ct : Fin N → Fin N → ℝ) (i j : Fin N)
    (hi : 0 < σ i) (hj : 0 < σ j) (hne : σ i ≠ σ j) :
    lamA σ i j ∈ Set.Ioo (0 : ℝ) (edgeHi σ i j)
    ∧ ContDiffOn ℝ ⊤ (fun r => matCoreUneq z ρ σ A qp Wt Ct i j r) (Set.Ioo 0 (lamA σ i j))
    ∧ ContDiffOn ℝ ⊤ (fun r => matCoreUneq z ρ σ A qp Wt Ct i j r)
        (Set.Ioo (lamA σ i j) (edgeHi σ i j)) := by
  refine ⟨?_, matCoreUneq_contDiffOn_inner z ρ σ A qp Wt Ct i j,
    matCoreUneq_contDiffOn_outer z ρ σ A qp Wt Ct i j⟩
  exact (interior_breakpoint_eq_absLam σ i j hi hj hne).1

/-- ⭐ **All orders, inner piece.**  With every amplitude `ContDiff` in `K` (the BH root supplies
this), every `K`-derivative of `matCoreUneq` is `ContDiffOn ℝ ⊤` on `(0, |λ_ij|)`.  The geometric
split `lamA σ i j` is `K`-free, so the inner branch is selected for all `K`, and the result follows
from `coreForm_paramDeriv_contDiffOn`. -/
theorem matCoreUneq_paramDeriv_contDiffOn_inner (z : ℝ) (σ : Fin N → ℝ) (ρ A : ℝ → Fin N → ℝ)
    (qp Wt Ct : ℝ → Fin N → Fin N → ℝ) (i j : Fin N)
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
  have hbase := coreForm_paramDeriv_contDiffOn
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

/-- ⭐ **All orders, outer piece.**  With every amplitude `ContDiff` in `K`, every `K`-derivative of
`matCoreUneq` is `ContDiffOn ℝ ⊤` on `(|λ_ij|, σ_ij)`. -/
theorem matCoreUneq_paramDeriv_contDiffOn_outer (z : ℝ) (σ : Fin N → ℝ) (ρ A : ℝ → Fin N → ℝ)
    (qp Wt Ct : ℝ → Fin N → Fin N → ℝ) (i j : Fin N)
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
  have hbase := coreForm_paramDeriv_contDiffOn
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

end FMSA.MSAExact.BRK
