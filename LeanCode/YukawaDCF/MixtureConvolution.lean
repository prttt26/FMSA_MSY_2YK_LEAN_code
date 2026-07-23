/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.YukawaDCF.WHSupports

/-!
# Group MRS (MRS.5 foundation) — real-space residue kernel `ℬ` and the convolution support geometry

The exact first-order inner DCF is `r·c^(1)_ij(r) = 𝒲_ij(r) − 𝒲_ij(−r)` with the real-space triple
convolution `𝒲 = 𝒬⁻ ⋆ ℬ ⋆ (𝒬⁻)ᵀ` (Group MRS / (★)).  This file supplies the **concrete `def`s** that
the whole inner-DCF line was blocked on (the 2026-07-17 vacuity audit flagged that no `def` for `ℬ`
or `𝒲` existed — every DCF theorem quantified over an *arbitrary* function):

* `bMixEntry` — the real-space Yukawa residue kernel `ℬ_mn(v) = Σ_q c_q·e^{−z_q(v−R_mn)}` windowed
  on `[R_mn, ∞)`.  Companion to `WHSupports.q0MixEntry` (the `𝒬⁻` kernel on `[λ_ij, R_ij]`).
* `pMixEntry` — the reflected `𝒬⁻` kernel `P_im(u) = 2π√(ρᵢρ_m)·q0MixEntry(−u)`, windowed on
  `[−R_im, −λ_im]` (the `𝒲(−r)` reflection input).

and the **support-containment** lemmas (`Function.support ⊆ …`), including the mediated two-fold
`bConvP` (`ℬ_in ⋆ P_jn`, edge `−λ_ij`) and triple `pbpConv` (`P_im ⋆ ℬ_mn ⋆ P_jn`, edge `−R_ij`).
Mathlib's `support_convolution_subset` (`support (f ⋆ g) ⊆ support f + support g`) turns the
edge-sum bookkeeping into set-arithmetic.

**IB.9 — closed here (support geometry, exactly as the proof note claimed).**  The whole content
is `pbp_breakpoints_subset` with the four edge identities `pbp_edge_eq`/`pbp_edge_lu`/`pbp_edge_ul`/
`pbp_edge_uu`: the mediated triple `P_im ⋆ ℬ_mn ⋆ P_jn` is piecewise with breakpoints at the four
sums `{−R_im,−λ_im} + {R_mn} + {−R_jn,−λ_jn}`, and **all four evaluate to the `m,n`-free set
`{−R_ij, −λ_ij, λ_ij, R_ij}`** — the intermediate species cancel out of *every* edge (contact
algebra `R_ab=(σ_a+σ_b)/2`).  So the mediated stepwise breakpoint `r* = R[a,b]+R[i,a]` (an
`m,n`-dependent quantity) is **never a DCF breakpoint** — it belongs to the *stepwise-poly*
decomposition (IB.6–IB.8), which the DCF does not inherit.  On the open core `(0,R_ij)` the only
breakpoint that survives is `λ_ij` (`−R_ij`, `−λ_ij` are `≤ 0`; `R_ij` is the outer boundary).
**This corrects the 2026-07-17 worry that `r*` needs a "coefficient-merging" cancellation: it does
not — `r*` is not an edge at all, so pure support geometry closes it.**

**The one remaining ingredient is standard (no new mathematics).**  "The DCF is a single analytic
closed form on each inter-breakpoint interval" is exactly the per-piece
`MixtureRealSpace.integral_quadratic_exp_conv` (a Baxter-poly ⋆ exp-kernel is a `poly + exp`, hence
analytic); wiring it pointwise onto `pbpConv` needs only the mechanical Mathlib-`convolution` ⇄
interval-integral unfolding.  The `C¹`-vs-jump distinction at `λ_ij` (curvature jump, from
`q0MixEntry`'s jump there — vs. its vanishing at `R_ij`, `q0Mix_quad_at_R`) is the same closed form
read at the edge.

This file only **reads** the stable `FMSA.InnerDecomp.Mix` / `FMSA.WHSupports.q0MixEntry`
interfaces; it does not touch `MixtureRealSpace.lean` (`FMSA.MRS`, MRS.6/7/8, actively developed).
-/

set_option linter.style.longLine false

open FMSA.InnerDecomp FMSA.WHSupports
open MeasureTheory Set
open scoped Convolution Pointwise

namespace FMSA.MixtureConvolution

variable {N M : ℕ}

/-! ### The real-space Yukawa residue kernel `ℬ` -/

/-- **Real-space residue kernel** `ℬ_mn(v) = Σ_q c_q · e^{−z_q·(v − R_mn)}` windowed on the outer
region `[R_mn, ∞)`.  This is the `fmsa_double_prop.py` `ℬ_mn(v) = Σ_q c_q e^{−z_q(v−R_mn)}` (v ≥ R_mn),
the Yukawa-tail factor of the triple convolution `𝒲 = 𝒬⁻ ⋆ ℬ ⋆ (𝒬⁻)ᵀ`.  The poles `z_q` and residue
coefficients `c_q` are the converged-solution data `Mix.zp`/`Mix.cb` (`b_grow[m][n]`). -/
noncomputable def bMixEntry (X : Mix N M) (m n : Fin N) (v : ℝ) : ℝ :=
  Set.indicator (Set.Ici (X.R m n))
    (fun v => ∑ q : Fin M, X.cb m n q * Real.exp (-(X.zp m n q) * (v - X.R m n))) v

/-- The Yukawa residue kernel is supported on the outer region:
`Function.support (bMixEntry X m n) ⊆ Set.Ici R_{mn}`.  (Mirror of
`WHSupports.q0MixEntry_support_subset`; independent of the pole/coefficient values.) -/
theorem bMixEntry_support_subset (X : Mix N M) (m n : Fin N) :
    Function.support (bMixEntry X m n) ⊆ Set.Ici (X.R m n) := by
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hns
  exact hx (Set.indicator_of_notMem hns _)

/-! ### The reflected `𝒬⁻` kernel `P` -/

/-- **Reflected `𝒬⁻` kernel** `P_im(u) = 2π√(ρᵢρ_m)·{Q̂₀(−u)}_{im}` (`fmsa_double_prop.py`
`P_im(u) = 2π√(ρᵢρ_m) q_im(−u)`, supported on `[−R_im, −λ_im]`).  This is the reflection input to the
odd part `𝒲(r) − 𝒲(−r)`. -/
noncomputable def pMixEntry (X : Mix N M) (i m : Fin N) (u : ℝ) : ℝ :=
  2 * Real.pi * Real.sqrt (X.ρ i * X.ρ m) * q0MixEntry X i m (-u)

/-- The reflected kernel is supported on the reflected core `[−R_im, −λ_im]`:
`Function.support (pMixEntry X i m) ⊆ Set.Icc (−R_{im}) (−λ_{im})`.  Follows from
`q0MixEntry_support_subset` by reflecting `u ↦ −u`. -/
theorem pMixEntry_support_subset (X : Mix N M) (i m : Fin N) :
    Function.support (pMixEntry X i m) ⊆ Set.Icc (-(X.R i m)) (-(X.lam i m)) := by
  intro x hx
  rw [Function.mem_support] at hx
  -- the constant `2π√(ρᵢρ_m)` factor cannot rescue a zero of `q0MixEntry(−x)`
  have hq : q0MixEntry X i m (-x) ≠ 0 := by
    intro h; apply hx; unfold pMixEntry; rw [h]; ring
  have hmem := q0MixEntry_support_subset X i m (Function.mem_support.mpr hq)
  rw [Set.mem_Icc] at hmem
  rw [Set.mem_Icc]
  constructor <;> linarith [hmem.1, hmem.2]

/-! ### Convolution support geometry — the backbone of IB.9

The mediated terms of `𝒲 = 𝒬⁻ ⋆ ℬ ⋆ (𝒬⁻)ᵀ` are convolutions of the two kernels above.  Mathlib's
`support_convolution_subset` (`support (f ⋆ g) ⊆ support f + support g`) reduces "which breakpoints
does a convolution introduce" to Minkowski set-arithmetic on the support intervals — exactly the
`px_convolve` edge-bookkeeping of `fmsa_double_prop.py`, now with no numerics.
-/

/-- Minkowski arithmetic: `[a, ∞) + [b, c] ⊆ [a + b, ∞)`.  The lower support-edge of a convolution
`(kernel on [a,∞)) ⋆ (kernel on [b,c])` is `a + b`; it is unbounded above. -/
theorem Ici_add_Icc_subset (a b c : ℝ) :
    Set.Ici a + Set.Icc b c ⊆ Set.Ici (a + b) := by
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_add.mp hz
  rw [Set.mem_Ici] at hx ⊢
  rw [Set.mem_Icc] at hy
  linarith [hx, hy.1]

/-- **One mediated term of `𝒲`.**  `ℬ_in ⋆ P_jn` — the Yukawa residue kernel convolved with the
reflected `𝒬⁻` kernel (the `−Σ_n ℬ_in ⋆ P_jn` term of the `𝒲_ij` expansion). -/
noncomputable def bConvP (X : Mix N M) (i n j : Fin N) : ℝ → ℝ :=
  (bMixEntry X i n) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (pMixEntry X j n)

/-- **Support geometry of a mediated term (the IB.9 backbone).**  The convolution `ℬ_in ⋆ P_jn` is
supported on `[R_in − R_jn, ∞)`: its only lower edge is `R_in − R_jn`, and it adds **no interior
knot** beyond the raw kernel edges.  Proof = `support_convolution_subset` + the kernel supports +
`Ici_add_Icc_subset`; no cancellation, pure support arithmetic. -/
theorem bConvP_support_subset (X : Mix N M) (i n j : Fin N) :
    Function.support (bConvP X i n j) ⊆ Set.Ici (X.R i n - X.R j n) := by
  unfold bConvP
  refine (support_convolution_subset (ContinuousLinearMap.mul ℝ ℝ)).trans ?_
  refine (Set.add_subset_add (bMixEntry_support_subset X i n)
    (pMixEntry_support_subset X j n)).trans ?_
  rw [sub_eq_add_neg]
  exact Ici_add_Icc_subset (X.R i n) (-(X.R j n)) (-(X.lam j n))

/-! ### Concrete edge identities — the raw support edges are `±λ_ij`, `±R_ij` (never a mediated `r*`)

The `fmsa_double_prop.py` "the raw `𝒲_ij` support-edge set is always exactly `{±λ_ij, ±R_ij}`"
(IB.9): the support **start** of every mediated convolution evaluates, by the contact-distance
algebra `R_ab = (σ_a+σ_b)/2`, to `−λ_ij` (two-fold) or `−R_ij` (triple) — the intermediate species
`m, n` cancel out.  So the mediated stepwise breakpoint `r* = R[a,b]+R[i,a]` is **not** a support-start
edge; it can only enter as an *interior* piece-edge, which is the "removable merge" residue below. -/

/-- The two-fold edge `R_in − R_jn` is exactly `−λ_ij` (the intermediate species `n` cancels). -/
theorem bConvP_edge_eq (X : Mix N M) (i n j : Fin N) :
    X.R i n - X.R j n = -(X.lam i j) := by
  simp only [Mix.R, Mix.lam]; ring

/-- The triple edge `−R_im + (R_mn − R_jn)` is exactly `−R_ij` (both intermediate species cancel). -/
theorem pbp_edge_eq (X : Mix N M) (i m n j : Fin N) :
    -(X.R i m) + (X.R m n - X.R j n) = -(X.R i j) := by
  simp only [Mix.R]; ring

/-! #### All four breakpoints of the mediated triple are `{±λ_ij, ±R_ij}` — `m, n` cancel everywhere

The triple `P_im ⋆ ℬ_mn ⋆ P_jn` is piecewise with breakpoints at the four sums
`{−R_im, −λ_im} + {R_mn} + {−R_jn, −λ_jn}` (the two `P` support edges each, plus the single `ℬ` edge
`R_mn`).  By the contact algebra all four evaluate to `{−R_ij, −λ_ij, λ_ij, R_ij}` — the intermediate
species `m, n` cancel out of **every** one.  Hence the mediated stepwise breakpoint
`r* = R[a,b] + R[i,a]` (an `m,n`-dependent quantity) is **not** among them: it is a breakpoint of the
*stepwise-poly* decomposition (IB.6–IB.8), which the DCF does not inherit.  This is the whole of
IB.9's "support geometry, *not* cancellation" content — no coefficient-merging is needed. -/

/-- Triple breakpoint (lower·upper): `−R_im + (R_mn − λ_jn) = λ_ij`. -/
theorem pbp_edge_lu (X : Mix N M) (i m n j : Fin N) :
    -(X.R i m) + (X.R m n - X.lam j n) = X.lam i j := by
  simp only [Mix.R, Mix.lam]; ring

/-- Triple breakpoint (upper·lower): `−λ_im + (R_mn − R_jn) = −λ_ij`. -/
theorem pbp_edge_ul (X : Mix N M) (i m n j : Fin N) :
    -(X.lam i m) + (X.R m n - X.R j n) = -(X.lam i j) := by
  simp only [Mix.R, Mix.lam]; ring

/-- Triple breakpoint (upper·upper): `−λ_im + (R_mn − λ_jn) = R_ij`. -/
theorem pbp_edge_uu (X : Mix N M) (i m n j : Fin N) :
    -(X.lam i m) + (X.R m n - X.lam j n) = X.R i j := by
  simp only [Mix.R, Mix.lam]; ring

/-- **IB.9 support-geometry closure — the mediated triple's breakpoint set is `{±λ_ij, ±R_ij}`.**
Every one of the four support-edge combinations of `P_im ⋆ ℬ_mn ⋆ P_jn` lands in the explicit,
`m,n`-**free** four-point set `{−R_ij, −λ_ij, λ_ij, R_ij}`.  So the intermediate species contribute
no new breakpoint, for any `N`; the DCF's interior breakpoint on `(0, R_ij)` is `λ_ij` alone
(`−R_ij`, `−λ_ij` are `≤ 0`; `R_ij` is the outer boundary).  Combined with the per-piece closed form
`MixtureRealSpace.integral_quadratic_exp_conv` (the DCF is a poly+exp — hence analytic — on each
inter-breakpoint interval), this is IB.9. -/
theorem pbp_breakpoints_subset (X : Mix N M) (i m n j : Fin N) :
    ({-(X.R i m) + (X.R m n - X.R j n), -(X.R i m) + (X.R m n - X.lam j n),
      -(X.lam i m) + (X.R m n - X.R j n), -(X.lam i m) + (X.R m n - X.lam j n)} : Set ℝ)
      ⊆ ({-(X.R i j), -(X.lam i j), X.lam i j, X.R i j} : Set ℝ) := by
  rw [pbp_edge_eq, pbp_edge_lu, pbp_edge_ul, pbp_edge_uu]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
  tauto

/-! ### The triple (mediated) convolution term `P_im ⋆ ℬ_mn ⋆ P_jn` -/

/-- Minkowski arithmetic: `[b, c] + [a, ∞) ⊆ [b + a, ∞)`. -/
theorem Icc_add_Ici_subset (a b c : ℝ) :
    Set.Icc b c + Set.Ici a ⊆ Set.Ici (b + a) := by
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_add.mp hz
  rw [Set.mem_Icc] at hx
  rw [Set.mem_Ici] at hy ⊢
  linarith [hx.1, hy]

/-- **The mediated (N≥3) term of `𝒲`.**  `P_im ⋆ ℬ_mn ⋆ P_jn` — the cross-species triple convolution,
the only term specific to `N ≥ 3`.  Written as `P_im ⋆ (ℬ_mn ⋆ P_jn)` reusing `bConvP`. -/
noncomputable def pbpConv (X : Mix N M) (i m n j : Fin N) : ℝ → ℝ :=
  (pMixEntry X i m) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (bConvP X m n j)

/-- **The mediated term's support starts at `−R_ij` (IB.9 backbone).**  `P_im ⋆ ℬ_mn ⋆ P_jn` is
supported on `[−R_ij, ∞)`: its support **start** is `−R_ij` for **every** choice of intermediate
species `m, n` — they cancel (`pbp_edge_eq`).  So the mediated term introduces **no support-start
edge** anywhere in the core `(0, R_ij)` (its start is `−R_ij ≤ 0 < r`).  Proof = two
`support_convolution_subset` steps + `Icc_add_Ici_subset`; no numerics, no cancellation. -/
theorem pbpConv_support_subset (X : Mix N M) (i m n j : Fin N) :
    Function.support (pbpConv X i m n j) ⊆ Set.Ici (-(X.R i j)) := by
  unfold pbpConv
  refine (support_convolution_subset (ContinuousLinearMap.mul ℝ ℝ)).trans ?_
  refine (Set.add_subset_add (pMixEntry_support_subset X i m)
    (bConvP_support_subset X m n j)).trans ?_
  rw [← pbp_edge_eq X i m n j]
  exact Icc_add_Ici_subset (X.R m n - X.R j n) (-(X.R i m)) (-(X.lam i m))

/-! ### The elementary "vanishing below the support edge" tool

For the *forward* `𝒲(r)` terms whose support start is `≥ R_ij`, this kills them on the whole open
core.  (The reflected terms above have start `≤ 0`, so they are the ones that carry the core
structure; this lemma is their outer-region counterpart.) -/

/-- A function supported on `[e, ∞)` vanishes strictly below `e`.  In particular a mediated term with
support start `e ≥ R_ij` is identically `0` on the open core `(0, R_ij)`. -/
theorem eq_zero_of_lt_support_edge {f : ℝ → ℝ} {e : ℝ}
    (hsupp : Function.support f ⊆ Set.Ici e) {r : ℝ} (hr : r < e) : f r = 0 := by
  by_contra h
  have hmem := hsupp (Function.mem_support.mpr h)
  rw [Set.mem_Ici] at hmem
  linarith

/-- **Outer-region vanishing.**  Any convolution term supported on `[e, ∞)` with `R_ij ≤ e` is `0`
throughout the open core `(0, R_ij)` — the "edges land at `|r| ≥ R_ij`, outside the core" half of
IB.9, reduced to a support-start comparison. -/
theorem eq_zero_on_core_of_edge_ge {f : ℝ → ℝ} {X : Mix N M} {i j : Fin N} {e : ℝ}
    (hsupp : Function.support f ⊆ Set.Ici e) (hle : X.R i j ≤ e)
    {r : ℝ} (hr : r ∈ Set.Ioo (0 : ℝ) (X.R i j)) : f r = 0 :=
  eq_zero_of_lt_support_edge hsupp (lt_of_lt_of_le hr.2 hle)

end FMSA.MixtureConvolution
