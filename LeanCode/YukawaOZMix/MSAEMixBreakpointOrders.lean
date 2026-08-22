/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib

/-!
# BRK.4 — mediated knots cancel *within* each order, not across (the identity theorem)

Group **BRK** (`proof_notes_breakpoints_MSA.md`).

Let `J K` be the jump of the exact-MSA `c_ij` at a candidate mediated knot `r*`, as a function of
the coupling `K`, with Taylor expansion `J K = Σ_n K^n J_n` — `J_n` the jump carried by the `n`-th
order `c^{(n)}`.  BRK.2 (`MSAEMixBreakpoints.breakpoints_sigma_l_free`, fully Lean, std-3) shows the
breakpoint *locations* `{±λ_ij, ±σ_ij}` are `σ_l`- **and** `K`-independent — geometric — so `r*` is
never among them and `J K = 0` on a whole interval of couplings; BRK.5 witnesses this numerically at
8 distinct active intra-core `r*` (`brk5_witness.py`, ≤1.9e-14).

**BRK.4 is the consequence the paper wants:** if the *total* jump vanishes on an interval and `J` is
real-analytic in `K`, then **every order's** jump vanishes — the mediated knot cannot cancel
*across* orders (a conspiracy between `c^{(1)}`, `c^{(2)}`, …), it must cancel *within* each
`c^{(n)}`.  First order is where the mechanism is visible (BRK.3 / IB.9); higher orders must too.

Pure identity theorem: analytic + zero-on-an-open-subinterval ⇒ zero on the whole connected domain
⇒ all iterated derivatives (hence all Taylor coefficients `J_n`) vanish.  The physics input — `J`
analytic in `K`, `J = 0` on an interval — is BRK.5 + the `K`-independence of BRK.2; it is *not*
re-proved here (BRK.4 predicts the cancellation, it does not exhibit `c^{(2)}`'s convolutions).
-/

open Set Filter Topology

namespace FMSA.MSAExact.BRK

/-- The iterated derivative of the zero function is zero (helper). -/
private lemma iteratedDeriv_zero_fun (n : ℕ) (x : ℝ) :
    iteratedDeriv n (0 : ℝ → ℝ) x = 0 := by
  induction n generalizing x with
  | zero => simp
  | succ k ih =>
      rw [iteratedDeriv_succ']
      have hd : deriv (0 : ℝ → ℝ) = 0 := by funext y; simp
      rw [hd]; exact ih x

/-- ⭐ **BRK.4 — every order's jump vanishes (identity theorem).**  If the jump `J` is real-analytic
on a preconnected open coupling-domain `U` and vanishes on a nondegenerate subinterval `(a,b) ⊆ U`
(BRK.5 + the `K`-independent breakpoint locations of BRK.2), then at every point `x₀ ∈ U` **all**
iterated derivatives of `J` vanish — equivalently every Taylor coefficient `J_n = 0`.  So a mediated
knot cannot be produced at one order and cancelled at another: it must be absent order by order. -/
theorem jump_all_orders_vanish
    (J : ℝ → ℝ) {U : Set ℝ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hJ : AnalyticOnNhd ℝ J U) {a b : ℝ} (hab : a < b) (hsub : Ioo a b ⊆ U)
    (hzero : EqOn J 0 (Ioo a b)) {x₀ : ℝ} (hx₀ : x₀ ∈ U) (n : ℕ) :
    iteratedDeriv n J x₀ = 0 := by
  -- the midpoint of (a,b) lies in U, and J is eventually 0 there
  have hmid : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  have hmidU : (a + b) / 2 ∈ U := hsub hmid
  have hev0 : J =ᶠ[𝓝 ((a + b) / 2)] 0 := by
    filter_upwards [isOpen_Ioo.mem_nhds hmid] with x hx using hzero hx
  -- identity theorem: J = 0 on all of U
  have hEqU : EqOn J 0 U :=
    hJ.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc hmidU hev0
  -- hence J = 0 in a neighbourhood of x₀ (U is open), so its germ is the zero function
  have hx0ev : J =ᶠ[𝓝 x₀] 0 := by
    filter_upwards [hUo.mem_nhds hx₀] with x hx using hEqU hx
  rw [hx0ev.iteratedDeriv_eq n]
  exact iteratedDeriv_zero_fun n x₀

end FMSA.MSAExact.BRK
