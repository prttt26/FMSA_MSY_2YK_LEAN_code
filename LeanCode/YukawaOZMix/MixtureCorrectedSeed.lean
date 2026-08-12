/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import LeanCode.YukawaOZMix.MixtureRowSum
import LeanCode.HSMixture.MixtureSeedExtended

/-!
# The fully-corrected matrix seed — reflecting the `r−u` linear arm (MML.8, unequal diameters)

The current second Baxter convolution `matBaxterUQm` and the prototype `matBaxterUQmSym` both build
on the UN-transposed first convolution `matBaxterU`, so they put the un-reflected factor `Qᵢₖ`
on BOTH shell arms (`MixtureRowSum.lean:1026-1035`).  `matOzStar_of_asymK`'s `matShellConvAsym K Kᵀ`
needs the **reflected** `Qₖᵢ` on the `r−u` arm — the "genuine remaining seed-level obstacle", which
"changes the renewal".

This file closes that obstacle.  The key observation is that the transposed first convolution
`matBaxterUt` is exactly `matBaxterU` at the transposed kernel `Qᵀ` (`matBaxterUt_eq_transpose`), so
the "changed renewal" is fully constructible: transposed claim `(A)`/`(B)` are the existing
`matBaxterU_outer`/`matBaxterU_core` at `Qᵀ`.  Building the second convolution on `matBaxterUt`
gives the **fully-corrected seed** `matBaxterUQmSymFull`, whose two linear arms are `Qᵢₖ` (`r+u`)
and `Qₖᵢ` (`r−u`) — the `K`/`Kᵀ` pair, for ANY diameters.

The seed identity `matBaxterUQmSymFull ≡ r·Φ` is then reduced (outer half + core truncation,
mirroring `matBaxterUQm_*`) to the SINGLE remaining input `hseed`, the reflected-arm Wertheim–Thiele
moment identity (the corrected analog of `baxter_core_seed`; delta-free for equal diameters).

Status: ✓ axiom-clean.
-/

open MeasureTheory Set

namespace FMSA.MixtureOzStar

variable {N : ℕ}

-- `matBaxterUt_eq_transpose` is generic Matrix machinery; moved to the HSMixture layer
-- (`HSMixture/MixtureSeedExtended.lean`, same `FMSA.MixtureOzStar` namespace), re-used by import.

/-- **Transposed claim `(A)` — `matBaxterUt` vanishes on `[σ,∞)`.**  The corrected seed's `r−u`
linear arm needs the *reflected* factor `Qₖᵢ`, i.e. the first convolution transposed.  Its
outer vanishing is `matBaxterU_outer` at `Qᵀ`: it needs `Ψ` to satisfy the **transposed** renewal
(kernel `Qₖᵢ`), which the Volterra construction supplies for `Qᵀ` exactly as for `Q` — so the
"changes the renewal" step is fully constructible, not a blocker. -/
theorem matBaxterUt_outer (sigma : ℝ) (hsigma : 0 < sigma)
    (Psi Psicore Q Fmat : Matrix (Fin N) (Fin N) (ℝ → ℝ))
    (hQcont : ∀ i k, Continuous (Q i k))
    (hQsupp : ∀ i k v, sigma ≤ v → Q i k v = 0)
    (hcore_cont : ∀ k j, Continuous (Psicore k j))
    (hcore : ∀ k j s, s ∈ Set.Ioo (0 : ℝ) sigma → Psi k j s = Psicore k j s)
    (houter_cont : ∀ k j b, ContinuousOn (Psi k j) (Set.Icc sigma b))
    (hforcing : ∀ i j r, sigma ≤ r →
      Fmat i j r = ∑ k, ∫ s in (0 : ℝ)..sigma, Q k i (r - s) * Psicore k j s)
    (hrenewal : ∀ i j r, sigma ≤ r →
      Psi i j r = Fmat i j r + ∑ k, ∫ t in sigma..r, Q k i (r - t) * Psi k j t)
    {r : ℝ} (hr : sigma ≤ r) (i j : Fin N) :
    matBaxterUt Psi Q sigma i j r = 0 := by
  rw [matBaxterUt_eq_transpose]
  exact matBaxterU_outer sigma hsigma Psi Psicore (fun a b => Q b a) Fmat
    (fun i k => hQcont k i) (fun i k v hv => hQsupp k i v hv) hcore_cont hcore houter_cont
    hforcing hrenewal hr i j

/-- **Transposed claim `(B)` — `matBaxterUt` is affine on the core, with COLUMN moments.**  The
`matBaxterU_core` computation at `Qᵀ`: on `0 < r < σ`, `matBaxterUt = r·(∑ₖ M₀ₖᵢ − 1) − ∑ₖ M₁ₖᵢ`
with `M₀ₖᵢ = ∫₀^σ Qₖᵢ`, `M₁ₖᵢ = ∫₀^σ t·Qₖᵢ` — the transpose swaps row moments for column
moments (`Qₖᵢ`), matching the reflected linear factor. -/
theorem matBaxterUt_core (sigma : ℝ) (hsigma : 0 < sigma)
    (Psi Q : Matrix (Fin N) (Fin N) (ℝ → ℝ))
    (hQ0 : ∀ i k, IntervalIntegrable (Q k i) volume 0 sigma)
    (hQ1 : ∀ i k, IntervalIntegrable (fun t => t * Q k i t) volume 0 sigma)
    (hcore : ∀ (k j : Fin N) (v : ℝ), v ∈ Set.Ioo (-sigma) sigma → Psi k j v = -v)
    {r : ℝ} (hr : r ∈ Set.Ioo (0 : ℝ) sigma) (i j : Fin N) :
    matBaxterUt Psi Q sigma i j r
      = r * ((∑ k, ∫ t in (0 : ℝ)..sigma, Q k i t) - 1)
        - ∑ k, ∫ t in (0 : ℝ)..sigma, t * Q k i t := by
  rw [matBaxterUt_eq_transpose]
  exact matBaxterU_core sigma hsigma Psi (fun a b => Q b a) hQ0 hQ1 hcore hr i j

/-- **The fully-corrected matrix seed** — the second Baxter convolution built on the *transposed*
first convolution `matBaxterUt`: `matBaxterUQmSymFullᵢⱼ(r) = matBaxterUtᵢⱼ(r) − ∑ₖ ∫₀^σ
Qᵢₖ(t)·matBaxterUtₖⱼ(r+t) dt`.  Contrast `matBaxterUQm`/`matBaxterUQmSym` (both `matBaxterU`
outer, un-reflected `Qᵢₖ` on
`r−u`): using `matBaxterUt` for the leading arm puts the **reflected** `Qₖᵢ` on `r−u`, so the seed's
two linear arms are `Qᵢₖ` (`r+u`) and `Qₖᵢ` (`r−u`) — exactly the `K`/`Kᵀ` pair that
`matShellConvAsym K Kᵀ` needs, for ANY diameters. -/
noncomputable def matBaxterUQmSymFull (Psi Q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma : ℝ)
    (i j : Fin N) (r : ℝ) : ℝ :=
  matBaxterUt Psi Q sigma i j r
    - ∑ k, ∫ t in (0 : ℝ)..sigma, Q i k t * matBaxterUt Psi Q sigma k j (r + t)

/-- **Outer half of the corrected seed — `≡ 0` on `[σ,∞)`.**  Once `matBaxterUt` vanishes outer
(transposed claim `(A)`), both the leading term and every `r+t ≥ σ` sample vanish.  Mirror of
`matBaxterUQm_zero_of_uOuter` with `matBaxterU → matBaxterUt`. -/
theorem matBaxterUQmSymFull_zero_of_utOuter (Psi Q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma : ℝ)
    (hsigma : 0 < sigma)
    (hUtouter : ∀ i j r, sigma ≤ r → matBaxterUt Psi Q sigma i j r = 0)
    {r : ℝ} (hr : sigma ≤ r) (i j : Fin N) :
    matBaxterUQmSymFull Psi Q sigma i j r = 0 := by
  rw [matBaxterUQmSymFull, hUtouter i j r hr, zero_sub, neg_eq_zero]
  refine Finset.sum_eq_zero (fun k _ => ?_)
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_, intervalIntegral.integral_zero]
  intro t ht
  rw [Set.uIcc_of_le hsigma.le] at ht
  dsimp only
  rw [hUtouter k j (r + t) (by linarith [ht.1]), mul_zero]

/-- **Core truncation of the corrected seed** — on `0 < r < σ` the `[0,σ]` integral collapses to
`[0,σ−r]` (the `[σ−r,σ]` tail vanishes exactly, `r+t ≥ σ` outer).  Mirror of
`matBaxterUQm_core_reduce`. -/
theorem matBaxterUQmSymFull_core_reduce (Psi Q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma : ℝ)
    (hUtouter : ∀ i j r, sigma ≤ r → matBaxterUt Psi Q sigma i j r = 0)
    (hint : ∀ (i j k : Fin N) (r : ℝ), IntervalIntegrable
      (fun t => Q i k t * matBaxterUt Psi Q sigma k j (r + t)) volume 0 sigma)
    {r : ℝ} (hr : r ∈ Set.Ioo (0 : ℝ) sigma) (i j : Fin N) :
    matBaxterUQmSymFull Psi Q sigma i j r
      = matBaxterUt Psi Q sigma i j r
        - ∑ k, ∫ t in (0 : ℝ)..(sigma - r), Q i k t * matBaxterUt Psi Q sigma k j (r + t) := by
  obtain ⟨hr0, hrlt⟩ := hr
  have hsr : (0 : ℝ) ≤ sigma - r := by linarith
  unfold matBaxterUQmSymFull
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hIa : IntervalIntegrable (fun t => Q i k t * matBaxterUt Psi Q sigma k j (r + t))
      volume 0 (sigma - r) :=
    (hint i j k r).mono_set (Set.uIcc_subset_uIcc
      (by rw [Set.mem_uIcc]; exact Or.inl ⟨le_refl 0, by linarith⟩)
      (by rw [Set.mem_uIcc]; exact Or.inl ⟨hsr, by linarith⟩))
  have hIb : IntervalIntegrable (fun t => Q i k t * matBaxterUt Psi Q sigma k j (r + t))
      volume (sigma - r) sigma :=
    (hint i j k r).mono_set (Set.uIcc_subset_uIcc
      (by rw [Set.mem_uIcc]; exact Or.inl ⟨hsr, by linarith⟩)
      (by rw [Set.mem_uIcc]; exact Or.inl ⟨by linarith, le_refl sigma⟩))
  have htail : (∫ t in (sigma - r)..sigma, Q i k t * matBaxterUt Psi Q sigma k j (r + t)) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_, intervalIntegral.integral_zero]
    intro t ht
    rw [Set.uIcc_of_le (by linarith : sigma - r ≤ sigma)] at ht
    dsimp only
    rw [hUtouter k j (r + t) (by linarith [ht.1]), mul_zero]
  rw [← intervalIntegral.integral_add_adjacent_intervals hIa hIb, htail, add_zero]

/-- **The corrected matrix `OZFIX.15` seed — `Ψ ⋆ Qᵀ₊ ⋆ Q₋ = r·Φ` on `(0,∞)`, reflected arm.**
The fully-corrected second convolution equals `r·Φ` on all `r > 0`, given: transposed claim `(A)`
outer vanishing (`hUtouter`, from `matBaxterUt_outer` = `matBaxterU_outer` at `Qᵀ`), `Φ` outer
vanishing, integrability, and the single corrected **core-seed** hypothesis `hseed` (reflected-arm
Wertheim–Thiele moments — the ONLY genuine remaining input, everything else discharged here).
The corrected analog of `matBaxterUQm_eq_rPhi_of_seed`; its output feeds `matOzStar_of_asymK`'s
`hclaimA` in the `matShellConvAsym K Kᵀ` form (linear `Qᵢₖ` on `r+u`, reflected `Qₖᵢ` on `r−u`). -/
theorem matBaxterUQmSymFull_eq_rPhi_of_seed (Psi Q Phi : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma : ℝ)
    (hsigma : 0 < sigma)
    (hUtouter : ∀ i j r, sigma ≤ r → matBaxterUt Psi Q sigma i j r = 0)
    (hPhiOuter : ∀ i j r, sigma ≤ r → Phi i j r = 0)
    (hint : ∀ (i j k : Fin N) (r : ℝ), IntervalIntegrable
      (fun t => Q i k t * matBaxterUt Psi Q sigma k j (r + t)) volume 0 sigma)
    (hseed : ∀ (i j : Fin N), ∀ r ∈ Set.Ioo (0 : ℝ) sigma,
      matBaxterUt Psi Q sigma i j r
        - ∑ k, ∫ t in (0 : ℝ)..(sigma - r), Q i k t * matBaxterUt Psi Q sigma k j (r + t)
      = r * Phi i j r)
    {r : ℝ} (hr : 0 < r) (i j : Fin N) :
    matBaxterUQmSymFull Psi Q sigma i j r = r * Phi i j r := by
  rcases lt_or_ge r sigma with hrs | hrs
  · rw [matBaxterUQmSymFull_core_reduce Psi Q sigma hUtouter hint ⟨hr, hrs⟩ i j]
    exact hseed i j r ⟨hr, hrs⟩
  · rw [matBaxterUQmSymFull_zero_of_utOuter Psi Q sigma hsigma hUtouter hrs i j,
      hPhiOuter i j r hrs, mul_zero]

/-! ### Seed→shell reindex plumbing — `hclaimA` for the windowed Baxter kernel `K`.
`matBaxterUQmSymFull`'s double convolution reindexes (`matDbl_eq_selfConvShell`, via
`matDblConv_reindex` per outer species) to the reflected self-conv shell; combined with the oddExt
bridge (`oddExt_div_self_eq_of_odd`) and the KDEF `ρK = Q − matSelfConv`, the corrected seed obeys
`Ψᵢⱼ(r) = r·Φᵢⱼ(r) + ρ·matShellConvAsym K Kᵀ (Ψ/·)ᵢⱼ(r)` (`correctedSeed_hclaimA`) — the exact
`matOzStar_of_asymK(_ae)` renewal input.  `K` here is the WINDOWED Baxter kernel; feeding the
assembly then needs only the (windowed) `K` a.e.-symmetry + `hbridge`. -/

/-- **General oddExt bridge — `oddExt (g/·) = g` for odd `g` with `g 0 = 0`.**  Generalizes
`oddExt_div_self_eq_baxterPsi`: `oddExt (g/·)(v) = v·g(|v|)/|v| = g v` (the `v<0` case uses oddness,
`v=0` both sides `0`). -/
theorem oddExt_div_self_eq_of_odd {g : ℝ → ℝ} (hodd : ∀ x, g (-x) = -g x) (h0 : g 0 = 0) :
    FMSA.HardSphere.oddExt (fun x => g x / x) = g := by
  funext v
  rcases eq_or_ne v 0 with hv | hv
  · subst hv; simp only [FMSA.HardSphere.oddExt, abs_zero, zero_mul]; rw [h0]
  · rcases lt_or_gt_of_ne hv with hneg | hpos
    · simp only [FMSA.HardSphere.oddExt, abs_of_neg hneg]
      rw [hodd v]; field_simp
    · simp only [FMSA.HardSphere.oddExt, abs_of_pos hpos]; field_simp

/-- **Shell form in raw `Ψ` — `matShellConvAsym K Kᵀ (Ψ/·)` with `oddExt` removed.**  For odd `Ψₖⱼ`
(the physical Baxter solution, `Ψ(−v) = −Ψ(v)`, `Ψ(0)=0`) the shell convolution's `oddExt(Ψₖⱼ/·)`
collapses to raw `Ψₖⱼ`: `matShellConvAsym K Kᵀ (Ψ/·)ᵢⱼ(r) = ∑ₖ ∫₀^σ (Kᵢₖ(u)·Ψₖⱼ(r+u) +
Kₖᵢ(u)·Ψₖⱼ(r−u)) du` — the raw form the seed produces. -/
theorem matShellConvAsym_transpose_raw (K Psi : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma r : ℝ)
    (i j : Fin N) (hodd : ∀ k, (∀ x, Psi k j (-x) = -Psi k j x) ∧ Psi k j 0 = 0) :
    matShellConvAsym K (fun a b => fun u => K b a u) (fun k l => fun x => Psi k l x / x) sigma r i j
      = ∑ k, ∫ u in (0 : ℝ)..sigma, (K i k u * Psi k j (r + u) + K k i u * Psi k j (r - u)) := by
  unfold matShellConvAsym
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hbridge : FMSA.HardSphere.oddExt (fun x => Psi k j x / x) = Psi k j :=
    oddExt_div_self_eq_of_odd (hodd k).1 (hodd k).2
  refine intervalIntegral.integral_congr (fun u _ => ?_)
  show K i k u * FMSA.HardSphere.oddExt (fun x => Psi k j x / x) (r + u)
      + K k i u * FMSA.HardSphere.oddExt (fun x => Psi k j x / x) (r - u)
    = K i k u * Psi k j (r + u) + K k i u * Psi k j (r - u)
  rw [hbridge]

/-- **Shell side, KDEF form.**  `ρ·matShellConvAsym K Kᵀ (Ψ/·)` in explicit raw form, substituting
the matrix KDEF `ρKₐᵦ = Qₐᵦ − matSelfConvₐᵦ`: `= ∑ₖ ∫₀^σ ((Qᵢₖ − matSelfConvᵢₖ)·Ψₖⱼ(r+u) + (Qₖᵢ −
matSelfConvₖᵢ)·Ψₖⱼ(r−u)) du` — the reflected-linear + reflected-selfconv structure the corrected
seed must match. -/
theorem rho_matShellConvAsym_transpose_kdef (K Q Psi : Matrix (Fin N) (Fin N) (ℝ → ℝ))
    (rho sigma r : ℝ) (hsigma : 0 < sigma) (i j : Fin N)
    (hodd : ∀ k, (∀ x, Psi k j (-x) = -Psi k j x) ∧ Psi k j 0 = 0)
    (hKDEF : ∀ a b u, u ∈ Set.Ioo (0 : ℝ) sigma →
      rho * K a b u = Q a b u - matSelfConv Q sigma u a b) :
    rho * matShellConvAsym K (fun a b => fun u => K b a u)
        (fun k l => fun x => Psi k l x / x) sigma r i j
      = ∑ k, ∫ u in (0 : ℝ)..sigma, ((Q i k u - matSelfConv Q sigma u i k) * Psi k j (r + u)
          + (Q k i u - matSelfConv Q sigma u k i) * Psi k j (r - u)) := by
  rw [matShellConvAsym_transpose_raw K Psi sigma r i j hodd, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr_ae ?_
  rw [Set.uIoc_of_le hsigma.le]
  have hne : ∀ᵐ x : ℝ, x ≠ sigma := by rw [MeasureTheory.ae_iff]; simp
  filter_upwards [hne] with u hune hmem
  have hu : u ∈ Set.Ioo (0 : ℝ) sigma := ⟨hmem.1, lt_of_le_of_ne hmem.2 hune⟩
  show rho * (K i k u * Psi k j (r + u) + K k i u * Psi k j (r - u))
      = (Q i k u - matSelfConv Q sigma u i k) * Psi k j (r + u)
        + (Q k i u - matSelfConv Q sigma u k i) * Psi k j (r - u)
  rw [show rho * (K i k u * Psi k j (r + u) + K k i u * Psi k j (r - u))
        = (rho * K i k u) * Psi k j (r + u) + (rho * K k i u) * Psi k j (r - u) from by ring,
    hKDEF i k u hu, hKDEF k i u hu]

/-- **The double convolution reindexes to the self-conv shell.**  Pulling the inner species sum out,
swapping `∑ₖ∑ₘ`, and applying `matDblConv_reindex` per outer species `m`: the corrected seed's raw
double term `∑ₖ ∫ Qᵢₖ(t)·∑ₘ ∫ Qₘₖ(s)·Ψₘⱼ(r+t−s)` equals `∑ₘ ∫₀^σ (matSelfConvᵢₘ·Ψₘⱼ(r+u) +
matSelfConvₘᵢ·Ψₘⱼ(r−u))` — the reflected self-conv shell. -/
theorem matDbl_eq_selfConvShell (Psi Q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma r : ℝ) (i j : Fin N)
    (hInner : ∀ k m, IntervalIntegrable
      (fun t => Q i k t * ∫ s in (0 : ℝ)..sigma, Q m k s * Psi m j (r + t - s)) volume 0 sigma)
    (hreindex : ∀ m, (∑ k, ∫ t in (0 : ℝ)..sigma,
        Q i k t * ∫ s in (0 : ℝ)..sigma, Q m k s * Psi m j (r + t - s))
      = ∫ u in (0 : ℝ)..sigma,
          (matSelfConv Q sigma u i m * Psi m j (r + u)
            + matSelfConv Q sigma u m i * Psi m j (r - u))) :
    (∑ k, ∫ t in (0 : ℝ)..sigma,
        Q i k t * ∑ m, ∫ s in (0 : ℝ)..sigma, Q m k s * Psi m j (r + t - s))
      = ∑ m, ∫ u in (0 : ℝ)..sigma,
          (matSelfConv Q sigma u i m * Psi m j (r + u)
            + matSelfConv Q sigma u m i * Psi m j (r - u)) := by
  have step1 : ∀ k, (∫ t in (0 : ℝ)..sigma,
        Q i k t * ∑ m, ∫ s in (0 : ℝ)..sigma, Q m k s * Psi m j (r + t - s))
      = ∑ m, ∫ t in (0 : ℝ)..sigma,
          Q i k t * ∫ s in (0 : ℝ)..sigma, Q m k s * Psi m j (r + t - s) := by
    intro k
    rw [← intervalIntegral.integral_finsetSum (fun m _ => hInner k m)]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    rw [Finset.mul_sum]
  simp_rw [step1]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun m _ => hreindex m)

/-- **Seed side — the corrected seed in raw shell form.**  `matBaxterUQmSymFull = Ψᵢⱼ(r) − ∑ₖ ∫₀^σ
((Qᵢₖ − matSelfConvᵢₖ)·Ψₖⱼ(r+u) + (Qₖᵢ − matSelfConvₖᵢ)·Ψₖⱼ(r−u))` — unfolding the transposed
arm (reflected `Qₖᵢ` on `r−u`) and reindexing the double term (`matDbl_eq_selfConvShell`).  This
is exactly `rho_matShellConvAsym_transpose_kdef`'s RHS, so `matBaxterUQmSymFull = Ψᵢⱼ −
ρ·matShellConvAsym K Kᵀ` under the KDEF — the seed→shell bridge. -/
theorem matBaxterUQmSymFull_eq_psi_sub_rawShell (Psi Q : Matrix (Fin N) (Fin N) (ℝ → ℝ))
    (sigma r : ℝ) (i j : Fin N)
    (hInner : ∀ k m, IntervalIntegrable
      (fun t => Q i k t * ∫ s in (0 : ℝ)..sigma, Q m k s * Psi m j (r + t - s)) volume 0 sigma)
    (hreindex : ∀ m, (∑ k, ∫ t in (0 : ℝ)..sigma,
        Q i k t * ∫ s in (0 : ℝ)..sigma, Q m k s * Psi m j (r + t - s))
      = ∫ u in (0 : ℝ)..sigma,
          (matSelfConv Q sigma u i m * Psi m j (r + u)
            + matSelfConv Q sigma u m i * Psi m j (r - u)))
    (hLinP : ∀ k, IntervalIntegrable (fun u => Q i k u * Psi k j (r + u)) volume 0 sigma)
    (hDbl : ∀ k, IntervalIntegrable
      (fun t => Q i k t * ∑ m, ∫ s in (0 : ℝ)..sigma, Q m k s * Psi m j (r + t - s)) volume 0 sigma)
    (hLinM : ∀ k, IntervalIntegrable (fun u => Q k i u * Psi k j (r - u)) volume 0 sigma)
    (hscP : ∀ k, IntervalIntegrable
      (fun u => matSelfConv Q sigma u i k * Psi k j (r + u)) volume 0 sigma)
    (hscM : ∀ k, IntervalIntegrable
      (fun u => matSelfConv Q sigma u k i * Psi k j (r - u)) volume 0 sigma) :
    matBaxterUQmSymFull Psi Q sigma i j r
      = Psi i j r - ∑ k, ∫ u in (0 : ℝ)..sigma,
          ((Q i k u - matSelfConv Q sigma u i k) * Psi k j (r + u)
          + (Q k i u - matSelfConv Q sigma u k i) * Psi k j (r - u)) := by
  -- LHS unfold: matBaxterUt(i,j,r) − ∑ₖ ∫ Qᵢₖ · matBaxterUt(k,j,r+t)
  have hlead : matBaxterUt Psi Q sigma i j r
      = Psi i j r - ∑ k, ∫ s in (0 : ℝ)..sigma, Q k i s * Psi k j (r - s) := rfl
  have hsum2 : (∑ k, ∫ t in (0 : ℝ)..sigma, Q i k t * matBaxterUt Psi Q sigma k j (r + t))
      = (∑ k, ∫ u in (0 : ℝ)..sigma, Q i k u * Psi k j (r + u))
        - ∑ m, ∫ u in (0 : ℝ)..sigma,
            (matSelfConv Q sigma u i m * Psi m j (r + u)
            + matSelfConv Q sigma u m i * Psi m j (r - u)) := by
    rw [← matDbl_eq_selfConvShell Psi Q sigma r i j hInner hreindex, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← intervalIntegral.integral_sub (hLinP k) (hDbl k)]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    show Q i k t * matBaxterUt Psi Q sigma k j (r + t)
        = Q i k t * Psi k j (r + t)
            - Q i k t * ∑ m, ∫ s in (0 : ℝ)..sigma, Q m k s * Psi m j (r + t - s)
    rw [← mul_sub]; rfl
  rw [matBaxterUQmSymFull, hlead, hsum2]
  -- RHS split: ∑ₖ ∫ ((Q−mSC)·Ψ(r+u) + (Qᵀ−mSCᵀ)·Ψ(r−u)) = (Aplus + Aminus) − SelfConvShell
  rw [show (∑ k, ∫ u in (0 : ℝ)..sigma, ((Q i k u - matSelfConv Q sigma u i k) * Psi k j (r + u)
          + (Q k i u - matSelfConv Q sigma u k i) * Psi k j (r - u)))
        = ((∑ k, ∫ u in (0 : ℝ)..sigma, Q i k u * Psi k j (r + u))
            + ∑ k, ∫ u in (0 : ℝ)..sigma, Q k i u * Psi k j (r - u))
          - ∑ k, ∫ u in (0 : ℝ)..sigma,
              (matSelfConv Q sigma u i k * Psi k j (r + u)
                + matSelfConv Q sigma u k i * Psi k j (r - u))
        from ?_]
  · ring
  · rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← intervalIntegral.integral_add (hLinP k) (hLinM k),
      ← intervalIntegral.integral_sub
        ((hLinP k).add (hLinM k)) ((hscP k).add (hscM k))]
    refine intervalIntegral.integral_congr (fun u _ => ?_)
    ring

/-- **Seed→shell bridge — `matBaxterUQmSymFull = Ψ − ρ·matShellConvAsym K Kᵀ`.**  Combining the seed
side (`matBaxterUQmSymFull_eq_psi_sub_rawShell`) with the shell side
(`rho_matShellConvAsym_transpose_kdef`): the corrected seed's double convolution IS `ρ` times the
asymmetric shell convolution of the windowed Baxter kernel `K` (`ρK = Q − matSelfConv`). -/
theorem matBaxterUQmSymFull_eq_psi_sub_shell (K Q Psi : Matrix (Fin N) (Fin N) (ℝ → ℝ))
    (rho sigma r : ℝ) (hsigma : 0 < sigma) (i j : Fin N)
    (hodd : ∀ k, (∀ x, Psi k j (-x) = -Psi k j x) ∧ Psi k j 0 = 0)
    (hKDEF : ∀ a b u, u ∈ Set.Ioo (0 : ℝ) sigma →
      rho * K a b u = Q a b u - matSelfConv Q sigma u a b)
    (hInner : ∀ k m, IntervalIntegrable
      (fun t => Q i k t * ∫ s in (0 : ℝ)..sigma, Q m k s * Psi m j (r + t - s)) volume 0 sigma)
    (hreindex : ∀ m, (∑ k, ∫ t in (0 : ℝ)..sigma,
        Q i k t * ∫ s in (0 : ℝ)..sigma, Q m k s * Psi m j (r + t - s))
      = ∫ u in (0 : ℝ)..sigma,
          (matSelfConv Q sigma u i m * Psi m j (r + u)
            + matSelfConv Q sigma u m i * Psi m j (r - u)))
    (hLinP : ∀ k, IntervalIntegrable (fun u => Q i k u * Psi k j (r + u)) volume 0 sigma)
    (hDbl : ∀ k, IntervalIntegrable
      (fun t => Q i k t * ∑ m, ∫ s in (0 : ℝ)..sigma, Q m k s * Psi m j (r + t - s)) volume 0 sigma)
    (hLinM : ∀ k, IntervalIntegrable (fun u => Q k i u * Psi k j (r - u)) volume 0 sigma)
    (hscP : ∀ k, IntervalIntegrable
      (fun u => matSelfConv Q sigma u i k * Psi k j (r + u)) volume 0 sigma)
    (hscM : ∀ k, IntervalIntegrable
      (fun u => matSelfConv Q sigma u k i * Psi k j (r - u)) volume 0 sigma) :
    matBaxterUQmSymFull Psi Q sigma i j r
      = Psi i j r - rho * matShellConvAsym K (fun a b => fun u => K b a u)
          (fun k l => fun x => Psi k l x / x) sigma r i j := by
  rw [matBaxterUQmSymFull_eq_psi_sub_rawShell Psi Q sigma r i j hInner hreindex hLinP hDbl hLinM
      hscP hscM,
    rho_matShellConvAsym_transpose_kdef K Q Psi rho sigma r hsigma i j hodd hKDEF]

/-- **The corrected seed's `hclaimA` (the `matOzStar_of_asymK` renewal input).**  Combining the seed
identity `matBaxterUQmSymFull ≡ r·Φ` (`matBaxterUQmSymFull_eq_rPhi_of_seed`) with the seed→shell
bridge:
`Ψᵢⱼ(r) = r·Φᵢⱼ(r) + ρ·matShellConvAsym K Kᵀ (Ψ/·)ᵢⱼ(r)` — exactly the `hclaimA` shape
`matOzStar_of_asymK`/`matOzStar_of_asymK_ae` consumes.  So the corrected seed + reindex plumbing
supply `hclaimA` for the WINDOWED Baxter kernel `K` (`ρK = Q − matSelfConv`); feeding
`matOzStar_of_asymK_ae`
then needs only the (windowed) `K` a.e.-symmetry + `hbridge`. -/
theorem correctedSeed_hclaimA (K Q Psi Phi : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (rho sigma : ℝ)
    (hsigma : 0 < sigma) (i j : Fin N) {r : ℝ} (hr : 0 < r)
    (hUtouter : ∀ i j r, sigma ≤ r → matBaxterUt Psi Q sigma i j r = 0)
    (hPhiOuter : ∀ i j r, sigma ≤ r → Phi i j r = 0)
    (hintR : ∀ (i j k : Fin N) (r : ℝ), IntervalIntegrable
      (fun t => Q i k t * matBaxterUt Psi Q sigma k j (r + t)) volume 0 sigma)
    (hseed : ∀ (i j : Fin N), ∀ r ∈ Set.Ioo (0 : ℝ) sigma,
      matBaxterUt Psi Q sigma i j r
        - ∑ k, ∫ t in (0 : ℝ)..(sigma - r), Q i k t * matBaxterUt Psi Q sigma k j (r + t)
      = r * Phi i j r)
    (hodd : ∀ k, (∀ x, Psi k j (-x) = -Psi k j x) ∧ Psi k j 0 = 0)
    (hKDEF : ∀ a b u, u ∈ Set.Ioo (0 : ℝ) sigma →
      rho * K a b u = Q a b u - matSelfConv Q sigma u a b)
    (hInner : ∀ k m, IntervalIntegrable
      (fun t => Q i k t * ∫ s in (0 : ℝ)..sigma, Q m k s * Psi m j (r + t - s)) volume 0 sigma)
    (hreindex : ∀ m, (∑ k, ∫ t in (0 : ℝ)..sigma,
        Q i k t * ∫ s in (0 : ℝ)..sigma, Q m k s * Psi m j (r + t - s))
      = ∫ u in (0 : ℝ)..sigma,
          (matSelfConv Q sigma u i m * Psi m j (r + u)
            + matSelfConv Q sigma u m i * Psi m j (r - u)))
    (hLinP : ∀ k, IntervalIntegrable (fun u => Q i k u * Psi k j (r + u)) volume 0 sigma)
    (hDbl : ∀ k, IntervalIntegrable
      (fun t => Q i k t * ∑ m, ∫ s in (0 : ℝ)..sigma, Q m k s * Psi m j (r + t - s)) volume 0 sigma)
    (hLinM : ∀ k, IntervalIntegrable (fun u => Q k i u * Psi k j (r - u)) volume 0 sigma)
    (hscP : ∀ k, IntervalIntegrable
      (fun u => matSelfConv Q sigma u i k * Psi k j (r + u)) volume 0 sigma)
    (hscM : ∀ k, IntervalIntegrable
      (fun u => matSelfConv Q sigma u k i * Psi k j (r - u)) volume 0 sigma) :
    Psi i j r = r * Phi i j r
      + rho * matShellConvAsym K (fun a b => fun u => K b a u)
          (fun k l => fun x => Psi k l x / x) sigma r i j := by
  have h1 := matBaxterUQmSymFull_eq_rPhi_of_seed Psi Q Phi sigma hsigma hUtouter hPhiOuter hintR
    hseed hr i j
  have h2 := matBaxterUQmSymFull_eq_psi_sub_shell K Q Psi rho sigma r hsigma i j hodd hKDEF hInner
    hreindex hLinP hDbl hLinM hscP hscM
  linarith

/-! ### Windowed↔full-line: folding the shell to a `[−σ,σ]` convolution.
`matShellConvAsym_fold` rewrites the seed's two-armed windowed shell as one `[−σ,σ]` integral over
`foldKernel K`; `foldKernel_transpose_odd` shows that kernel is transpose-odd (`D(i,k,−v)=D(k,i,v)`)
— whereas OZ★'s symmetric shell needs it EVEN, the difference being exactly the (false)
windowed `K` symmetry.  So the residual reconciliation (fold = an even/full-line DCF kernel, valid
under the integral against the odd solution `Ψ`) is the Baxter-factorization⟹OZ content — the MML.8
crux, needing the Fourier/factorization route, not a short real-space identity. -/

/-- **The folded (full-line) DCF kernel** — `Dᵢₖ(v) = Kᵢₖ(v)` for `v > 0`, `= Kₖᵢ(−v)` for `v ≤ 0`.
Folds the asymmetric shell's `K` (`r+u` arm) and `Kᵀ` (`r−u` arm) onto one `[−σ,σ]` kernel (the
`r−u` arm becomes the `v < 0` half by `u ↦ −v`).  By construction `Dᵢₖ(−v) = Dₖᵢ(v)`
(transpose-odd), so `D` is even (`Dᵢₖ(−v) = Dᵢₖ(v)` — what OZ★'s symmetric kernel needs) **iff**
the windowed `K` is symmetric — exactly the gap. -/
noncomputable def foldKernel (K : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (i k : Fin N) (v : ℝ) : ℝ :=
  if 0 < v then K i k v else K k i (-v)

/-- **Folding — the windowed asymmetric shell IS a single `[−σ,σ]` full-line convolution.**
`matShellConvAsym K Kᵀ (Ψ/·)ᵢⱼ(r) = ∑ₖ ∫_{−σ}^σ foldKernel K i k v · Ψₖⱼ(r+v) dv`.  The `r−u` arm
folds to the negative half by `u ↦ −v` (`intervalIntegral.integral_comp_neg`).  Converts the seed's
two-armed windowed form into a one-integral full-line form — the representation on which the
windowed↔full-line reconciliation is stated.  No symmetry used; only substitution + additivity. -/
theorem matShellConvAsym_fold (K Psi : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma r : ℝ) (i j : Fin N)
    (hsigma : 0 ≤ sigma)
    (hodd : ∀ k, (∀ x, Psi k j (-x) = -Psi k j x) ∧ Psi k j 0 = 0)
    (hP : ∀ k, IntervalIntegrable (fun u => K i k u * Psi k j (r + u)) volume 0 sigma)
    (hMraw : ∀ k, IntervalIntegrable (fun u => K k i u * Psi k j (r - u)) volume 0 sigma)
    (hFlo : ∀ k, IntervalIntegrable
      (fun v => foldKernel K i k v * Psi k j (r + v)) volume (-sigma) 0)
    (hFhi : ∀ k, IntervalIntegrable
      (fun v => foldKernel K i k v * Psi k j (r + v)) volume 0 sigma) :
    matShellConvAsym K (fun a b => fun u => K b a u) (fun k l => fun x => Psi k l x / x) sigma r i j
      = ∑ k, ∫ v in (-sigma)..sigma, foldKernel K i k v * Psi k j (r + v) := by
  rw [matShellConvAsym_transpose_raw K Psi sigma r i j hodd]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hhi : (∫ v in (0 : ℝ)..sigma, foldKernel K i k v * Psi k j (r + v))
      = ∫ u in (0 : ℝ)..sigma, K i k u * Psi k j (r + u) := by
    refine intervalIntegral.integral_congr_ae ?_
    have hne : ∀ᵐ v : ℝ, v ≠ (0 : ℝ) := by rw [MeasureTheory.ae_iff]; simp
    filter_upwards [hne] with v hv0 hmem
    rw [Set.uIoc_of_le hsigma] at hmem
    rw [foldKernel, if_pos hmem.1]
  have hsub : (∫ u in (0 : ℝ)..sigma, K k i u * Psi k j (r - u))
      = ∫ v in (-sigma)..(0 : ℝ), K k i (-v) * Psi k j (r + v) := by
    have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := sigma)
      (f := fun v => K k i (-v) * Psi k j (r + v))
    simp only [neg_neg, neg_zero, ← sub_eq_add_neg] at h
    exact h
  have hlo : (∫ v in (-sigma)..(0 : ℝ), foldKernel K i k v * Psi k j (r + v))
      = ∫ u in (0 : ℝ)..sigma, K k i u * Psi k j (r - u) := by
    rw [hsub]
    refine intervalIntegral.integral_congr_ae ?_
    have hne : ∀ᵐ v : ℝ, v ≠ (0 : ℝ) := by rw [MeasureTheory.ae_iff]; simp
    filter_upwards [hne] with v hv0 hmem
    rw [Set.uIoc_of_le (by linarith : -sigma ≤ (0 : ℝ))] at hmem
    have hvneg : ¬ (0 < v) := not_lt.mpr hmem.2
    rw [foldKernel, if_neg hvneg]
  rw [← intervalIntegral.integral_add_adjacent_intervals (hFlo k) (hFhi k), hhi, hlo,
    intervalIntegral.integral_add (hP k) (hMraw k), add_comm]

/-- **The folded kernel is transpose-odd** — `foldKernel K i k (−v) = foldKernel K k i v` (`v ≠ 0`),
automatic from the fold, no hypothesis on `K`.  Contrast the OZ★ symmetric shell, whose folded
kernel is **even** (`D i k (−v) = D i k v`).  So `foldKernel K` is even ⟺ `foldKernel K i k v =
foldKernel K k i v` ⟺ the windowed `K` is symmetric (`K i k = K k i`) — the precise gap:
the seed's fold is transpose-odd, OZ★ needs it even, the difference is exactly the (false) windowed
symmetry. -/
theorem foldKernel_transpose_odd (K : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (i k : Fin N) {v : ℝ}
    (hv : v ≠ 0) : foldKernel K i k (-v) = foldKernel K k i v := by
  simp only [foldKernel]
  rcases lt_or_gt_of_ne hv with hneg | hpos
  · rw [if_pos (by linarith : (0 : ℝ) < -v), if_neg (by linarith : ¬(0 : ℝ) < v)]
  · rw [if_neg (by linarith : ¬(0 : ℝ) < -v), if_pos hpos, neg_neg]

/-- **Fold-split of the symbol** — the folded kernel's symbol `∫_{−σ}^σ foldKernel K i k v·e^{zv}`
splits into two one-sided Baxter-kernel transforms `∫₀^σ K(i,k)·e^{zv} + ∫₀^σ K(k,i)·e^{−zv}`.
The `v<0` half becomes the reflected (`e^{−zv}`, transposed `K(k,i)`) transform by `u ↦ −v`
(`integral_comp_neg`).  Concrete unfolding of `foldShell_laplace`'s symbol; combined with the KDEF
`ρK = Q − matSelfConv`, matching it to `Cmix0` is the remaining factorization content. -/
theorem foldKernel_laplace_split (K : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma : ℝ) (hsig : 0 ≤ sigma)
    (z : ℂ) (i k : Fin N)
    (hlo : IntervalIntegrable (fun v => (foldKernel K i k v : ℂ) * Complex.exp (z * (v : ℂ)))
      volume (-sigma) 0)
    (hhi : IntervalIntegrable (fun v => (foldKernel K i k v : ℂ) * Complex.exp (z * (v : ℂ)))
      volume 0 sigma) :
    (∫ v in (-sigma)..sigma, (foldKernel K i k v : ℂ) * Complex.exp (z * (v : ℂ)))
      = (∫ v in (0 : ℝ)..sigma, (K i k v : ℂ) * Complex.exp (z * (v : ℂ)))
        + ∫ v in (0 : ℝ)..sigma, (K k i v : ℂ) * Complex.exp (-(z * (v : ℂ))) := by
  have hhi_eq : (∫ v in (0 : ℝ)..sigma, (foldKernel K i k v : ℂ) * Complex.exp (z * (v : ℂ)))
      = ∫ v in (0 : ℝ)..sigma, (K i k v : ℂ) * Complex.exp (z * (v : ℂ)) := by
    refine intervalIntegral.integral_congr_ae ?_
    have hne : ∀ᵐ v : ℝ, v ≠ (0 : ℝ) := by rw [MeasureTheory.ae_iff]; simp
    filter_upwards [hne] with v hv0 hmem
    rw [Set.uIoc_of_le hsig] at hmem
    rw [foldKernel, if_pos hmem.1]
  have hsub : (∫ v in (0 : ℝ)..sigma, (K k i v : ℂ) * Complex.exp (-(z * (v : ℂ))))
      = ∫ v in (-sigma)..(0 : ℝ), (K k i (-v) : ℂ) * Complex.exp (z * (v : ℂ)) := by
    have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := sigma)
      (f := fun v => (K k i (-v) : ℂ) * Complex.exp (z * (v : ℂ)))
    simp only [neg_neg, neg_zero, Complex.ofReal_neg, mul_neg] at h
    exact h
  have hlo_eq : (∫ v in (-sigma)..(0 : ℝ), (foldKernel K i k v : ℂ) * Complex.exp (z * (v : ℂ)))
      = ∫ v in (0 : ℝ)..sigma, (K k i v : ℂ) * Complex.exp (-(z * (v : ℂ))) := by
    rw [hsub]
    refine intervalIntegral.integral_congr_ae ?_
    have hne : ∀ᵐ v : ℝ, v ≠ (0 : ℝ) := by rw [MeasureTheory.ae_iff]; simp
    filter_upwards [hne] with v hv0 hmem
    rw [Set.uIoc_of_le (by linarith : -sigma ≤ (0 : ℝ))] at hmem
    rw [foldKernel, if_neg (not_lt.mpr hmem.2)]
  rw [← intervalIntegral.integral_add_adjacent_intervals hlo hhi, hlo_eq, hhi_eq, add_comm]

/-! ### Extending the seed renewal to full-line `∫_ℝ` convolutions.
The `[0,σ]` chain drops the sub-zero Baxter tail `[λᵢₖ,0)` when `σₖ<σᵢ`; the full-line
the full-line `matBaxterU*Ext` defs integrate over the factor's true support, so their fold-kernel
is the full-line DCF `matDCFfull` (symbol `Cmix0`).  The transposed relation is
still `rfl`; `matBaxterUExt_eq_matBaxterU_sub_tail` isolates the recovered tail. -/

-- `matBaxterUExt` / `matBaxterUtExt` / `matBaxterUtExt_eq_transpose` are generic Matrix machinery;
-- moved to the HSMixture layer (`HSMixture/MixtureSeedExtended.lean`, same `FMSA.MixtureOzStar`
-- namespace), re-used by import.

/-- **The fully-corrected extended seed** — the second Baxter convolution on the transposed extended
first convolution `matBaxterUtExt`, all `∫_ℝ`: `matBaxterUQmSymFullExtᵢⱼ(r) = matBaxterUtExtᵢⱼ(r)
− ∑ₖ ∫_ℝ Qᵢₖ(t)·matBaxterUtExtₖⱼ(r+t)`.  Its fold-kernel is the full-line DCF `matDCFfull`
(reflected `Qₖᵢ` on `r−u`, `Qᵢₖ` on `r+u`, full-support self-conv `matCorr`), symbol `Cmix0`, so the
windowed↔full-line gap does not arise. -/
noncomputable def matBaxterUQmSymFullExt (Psi Q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (i j : Fin N)
    (r : ℝ) : ℝ :=
  matBaxterUtExt Psi Q i j r - ∑ k, ∫ t, Q i k t * matBaxterUtExt Psi Q k j (r + t)

-- `matBaxterUExt_eq_matBaxterU_sub_tail` is generic Matrix machinery; moved to the HSMixture layer
-- (`HSMixture/MixtureSeedExtended.lean`, same `FMSA.MixtureOzStar` namespace), re-used by import.

/-- **Outer half of the extended seed, with the SHIFTED bound `σ − λ`.**  For the full-line seed the
outer-vanishing bound is `σ − λ`, not `σ` (`λ` a lower support bound, `Q i k t = 0` for `t < λ`,
`λ ≤ 0`).  For `r ≥ σ − λ` the leading term vanishes (`r ≥ σ`) and every `t` with `Qᵢₖ(t) ≠ 0` has
`t ≥ λ`, so `r + t ≥ σ` and `matBaxterUtExtₖⱼ(r+t) = 0` (integrand `0`).  So the outer branch is
`r ≥ σ − λ`, pinning the gap `[σ, σ−λ)` where neither this nor the core applies. -/
theorem matBaxterUQmSymFullExt_zero_outer (Psi Q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma lam : ℝ)
    (hlam : lam ≤ 0)
    (hUtouter : ∀ i j r, sigma ≤ r → matBaxterUtExt Psi Q i j r = 0)
    (hQlam : ∀ i k t, t < lam → Q i k t = 0)
    {r : ℝ} (hr : sigma - lam ≤ r) (i j : Fin N) :
    matBaxterUQmSymFullExt Psi Q i j r = 0 := by
  unfold matBaxterUQmSymFullExt
  rw [hUtouter i j r (by linarith), zero_sub, neg_eq_zero]
  refine Finset.sum_eq_zero (fun k _ => ?_)
  have hz : (fun t => Q i k t * matBaxterUtExt Psi Q k j (r + t))
      =ᵐ[volume] (fun _ => (0 : ℝ)) := by
    filter_upwards with t
    rcases lt_or_ge t lam with ht | ht
    · rw [hQlam i k t ht, zero_mul]
    · rw [hUtouter k j (r + t) (by linarith), mul_zero]
  rw [integral_congr_ae hz, integral_zero]

/-- **The gap reduces to the sub-zero tail moment.**  On the gap `σ ≤ r ≤ σ−λ` (`Φ = c_HS = 0`, so
the seed identity needs `= 0`): the leading term vanishes (`r ≥ σ`) and the integrand vanishes off
`[λ, σ−r]` (below `λ`: `Qᵢₖ = 0`; above `σ−r`: `r+t ≥ σ` ⇒ `matBaxterUtExt = 0`), so
`matBaxterUQmSymFullExt = − ∑ₖ ∫ t in λ..(σ−r), Qᵢₖ(t)·matBaxterUtExtₖⱼ(r+t)`.  So the gap collapses
to this **sub-zero tail moment**; its vanishing is the one remaining input (the core seed, on the
recovered `[λ,0)` tail). -/
theorem matBaxterUQmSymFullExt_gap_reduce (Psi Q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma lam : ℝ)
    (hUtouter : ∀ i j r, sigma ≤ r → matBaxterUtExt Psi Q i j r = 0)
    (hQlam : ∀ i k t, t < lam → Q i k t = 0)
    {r : ℝ} (hr : sigma ≤ r) (hr2 : lam ≤ sigma - r) (i j : Fin N) :
    matBaxterUQmSymFullExt Psi Q i j r
      = - ∑ k, ∫ t in lam..(sigma - r), Q i k t * matBaxterUtExt Psi Q k j (r + t) := by
  unfold matBaxterUQmSymFullExt
  rw [hUtouter i j r hr, zero_sub]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [intervalIntegral.integral_of_le hr2, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  refine (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (fun t ht => ?_)).symm
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
  rcases ht with ht | ht
  · rw [hQlam i k t ht, zero_mul]
  · rw [hUtouter k j (r + t) (by linarith), mul_zero]

/-- **Per-species truncation of the extended second convolution.**  For `λ ≤ σ − r`, the full-line
`∫_ℝ Qᵢₖ(t)·matBaxterUtExtₖⱼ(r+t) dt` truncates to `∫_λ^{σ−r}` (below `λ`: `Qᵢₖ = 0`; above `σ−r`:
`r+t ≥ σ` ⇒ `matBaxterUtExt = 0`).  The full-support (`[λ, σ−r]`) analog of the `[0,σ]` chain's
`[0,σ−r]` truncation — this is where the recovered `[λ,0)` tail enters. -/
theorem matBaxterUtExt_conv_trunc (Psi Q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma lam : ℝ)
    (hUtouter : ∀ i j r, sigma ≤ r → matBaxterUtExt Psi Q i j r = 0)
    (hQlam : ∀ i k t, t < lam → Q i k t = 0)
    {r : ℝ} (hr2 : lam ≤ sigma - r) (i k j : Fin N) :
    (∫ t, Q i k t * matBaxterUtExt Psi Q k j (r + t))
      = ∫ t in lam..(sigma - r), Q i k t * matBaxterUtExt Psi Q k j (r + t) := by
  rw [intervalIntegral.integral_of_le hr2, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  refine (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (fun t ht => ?_)).symm
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
  rcases ht with ht | ht
  · rw [hQlam i k t ht, zero_mul]
  · rw [hUtouter k j (r + t) (by linarith), mul_zero]

/-- **Core truncation of the extended seed** — on `λ ≤ σ − r` (covers the core `0<r<σ` and the gap
`σ≤r≤σ−λ`) the extended seed collapses to the leading `matBaxterUtExt` minus the full-support
truncated second convolution.  Full-line analog of `matBaxterUQmSymFull_core_reduce`. -/
theorem matBaxterUQmSymFullExt_core_reduce (Psi Q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma lam : ℝ)
    (hUtouter : ∀ i j r, sigma ≤ r → matBaxterUtExt Psi Q i j r = 0)
    (hQlam : ∀ i k t, t < lam → Q i k t = 0)
    {r : ℝ} (hr2 : lam ≤ sigma - r) (i j : Fin N) :
    matBaxterUQmSymFullExt Psi Q i j r
      = matBaxterUtExt Psi Q i j r
        - ∑ k, ∫ t in lam..(sigma - r), Q i k t * matBaxterUtExt Psi Q k j (r + t) := by
  unfold matBaxterUQmSymFullExt
  congr 1
  exact Finset.sum_congr rfl
    (fun k _ => matBaxterUtExt_conv_trunc Psi Q sigma lam hUtouter hQlam hr2 i k j)

/-- **The extended seed produces `r·Φ` on all `r > 0` — all three regimes.**  From the extended core
moment seed `hseed` on `(0, σ−λ)` (for `r<σ` the core Wertheim–Thiele identity; for `σ≤r<σ−λ`, where
`Φ=0`, the sub-zero **tail-moment vanishing**), `Φ`-outer, `hUtouter` (claim-`(A)`), and the support
bound `hQlam`, the extended seed `≡ r·Φ`.  Split: `0<r<σ−λ` uses
`_core_reduce` + `hseed`; `r ≥ σ−λ` uses `_zero_outer` (`= 0 = r·Φ`).  Full-line analog of
`matBaxterUQmSymFull_eq_rPhi_of_seed`, gap absorbed into the single `hseed` on `(0, σ−λ)`. -/
theorem matBaxterUQmSymFullExt_eq_rPhi_of_seed (Psi Q Phi : Matrix (Fin N) (Fin N) (ℝ → ℝ))
    (sigma lam : ℝ) (hlam : lam ≤ 0)
    (hUtouter : ∀ i j r, sigma ≤ r → matBaxterUtExt Psi Q i j r = 0)
    (hQlam : ∀ i k t, t < lam → Q i k t = 0)
    (hPhiOuter : ∀ i j r, sigma ≤ r → Phi i j r = 0)
    (hseed : ∀ (i j : Fin N), ∀ r ∈ Set.Ioo (0 : ℝ) (sigma - lam),
      matBaxterUtExt Psi Q i j r
        - ∑ k, ∫ t in lam..(sigma - r), Q i k t * matBaxterUtExt Psi Q k j (r + t)
      = r * Phi i j r)
    {r : ℝ} (hr : 0 < r) (i j : Fin N) :
    matBaxterUQmSymFullExt Psi Q i j r = r * Phi i j r := by
  rcases lt_or_ge r (sigma - lam) with hrs | hrs
  · rw [matBaxterUQmSymFullExt_core_reduce Psi Q sigma lam hUtouter hQlam (by linarith) i j]
    exact hseed i j r ⟨hr, hrs⟩
  · rw [matBaxterUQmSymFullExt_zero_outer Psi Q sigma lam hlam hUtouter hQlam hrs i j,
      hPhiOuter i j r (by linarith), mul_zero]

/-- **Extended claim `(B)` — `matBaxterUExt` affine on the core, with FULL-SUPPORT moments.**  The
full-line analog of `matBaxterU_core`: for `Ψ` with core value `Ψₖⱼ(v) = −v` on `(−σ,σ)`, on the
range `0 < r < σ + λ` (so every `t` in support `[λ,σ]` keeps `r−t` in `(−σ,σ)`): `matBaxterUExt =
r·(∑ₖ M₀ᵢₖ − 1) − ∑ₖ M₁ᵢₖ` with **full-support** moments `M₀ᵢₖ = ∫_ℝ Qᵢₖ`, `M₁ᵢₖ = ∫_ℝ t·Qᵢₖ`
(`= ∫_{λ}^{R}`, recovering the `[λ,0)` tail the `[0,σ]` moments dropped). -/
theorem matBaxterUExt_core (sigma lam : ℝ) (hlam : lam ≤ 0)
    (Psi Q : Matrix (Fin N) (Fin N) (ℝ → ℝ))
    (hQ0 : ∀ i k, Integrable (Q i k))
    (hQ1 : ∀ i k, Integrable (fun t => t * Q i k t))
    (hQsupp : ∀ i k t, t < lam ∨ sigma < t → Q i k t = 0)
    (hcore : ∀ (k j : Fin N) (v : ℝ), v ∈ Set.Ioo (-sigma) sigma → Psi k j v = -v)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < sigma + lam) (i j : Fin N) :
    matBaxterUExt Psi Q i j r
      = r * ((∑ k, ∫ t, Q i k t) - 1) - ∑ k, ∫ t, t * Q i k t := by
  unfold matBaxterUExt
  have hpr : Psi i j r = -r := hcore i j r ⟨by linarith, by linarith⟩
  have hcongr : (∑ k, ∫ t, Q i k t * Psi k j (r - t))
      = ∑ k, ∫ t, (t * Q i k t - r * Q i k t) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
    dsimp only
    rcases em (t < lam ∨ sigma < t) with ht | ht
    · rw [hQsupp i k t ht]; ring
    · simp only [not_or, not_lt] at ht
      rw [hcore k j (r - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩]; ring
  rw [hpr, hcongr]
  have hsplit : ∀ k : Fin N, (∫ t, (t * Q i k t - r * Q i k t))
      = (∫ t, t * Q i k t) - r * ∫ t, Q i k t := by
    intro k
    rw [integral_sub (hQ1 i k) ((hQ0 i k).const_mul r), MeasureTheory.integral_const_mul]
  simp_rw [hsplit]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- **Extended transposed claim `(B)` — `matBaxterUtExt` affine on the core, COLUMN full-support
moments.**  `matBaxterUExt_core` at `Qᵀ` (via `matBaxterUtExt_eq_transpose`): the column moments
`∫_ℝ Qₖᵢ`, `∫_ℝ t·Qₖᵢ` (full-support, recovering the reflected tail). -/
theorem matBaxterUtExt_core (sigma lam : ℝ) (hlam : lam ≤ 0)
    (Psi Q : Matrix (Fin N) (Fin N) (ℝ → ℝ))
    (hQ0 : ∀ i k, Integrable (Q k i))
    (hQ1 : ∀ i k, Integrable (fun t => t * Q k i t))
    (hQsupp : ∀ i k t, t < lam ∨ sigma < t → Q k i t = 0)
    (hcore : ∀ (k j : Fin N) (v : ℝ), v ∈ Set.Ioo (-sigma) sigma → Psi k j v = -v)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < sigma + lam) (i j : Fin N) :
    matBaxterUtExt Psi Q i j r
      = r * ((∑ k, ∫ t, Q k i t) - 1) - ∑ k, ∫ t, t * Q k i t := by
  rw [matBaxterUtExt_eq_transpose]
  exact matBaxterUExt_core sigma lam hlam Psi (fun a b => Q b a) hQ0 hQ1 hQsupp hcore hr0 hr1 i j

/-! ### Equal-diameter collapse — the extended seed reduces to the windowed prototype (`λ=0`).
At equal diameters the factor is supported in `[0,σ]` (no sub-zero tail) and symmetric, so `∫_ℝ =
∫₀^σ` and `matBaxterUt = matBaxterU`; the extended seed collapses to `matBaxterUQmSym`, inheriting
its row-collapse to `r·c_HS` verbatim. -/

/-- **Full-line = windowed when the factor is supported in `[0,σ]`** (equal diameters, `λ=0`).  Then
`∫_ℝ Qᵢₖ·Ψₖⱼ(r−t) = ∫₀^σ`, so `matBaxterUExt = matBaxterU`: the extended and windowed first
convolutions COINCIDE — the extension recovers no tail, because there is none. -/
theorem matBaxterUExt_eq_matBaxterU_of_support (Psi Q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma : ℝ)
    (hsigma : 0 ≤ sigma) (hQsupp : ∀ i k t, t < 0 ∨ sigma < t → Q i k t = 0) (i j : Fin N) (r : ℝ) :
    matBaxterUExt Psi Q i j r = matBaxterU Psi Q sigma i j r := by
  unfold matBaxterUExt matBaxterU
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [intervalIntegral.integral_of_le hsigma, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  refine (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (fun t ht => ?_)).symm
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
  rcases ht with ht | ht
  · rw [hQsupp i k t (Or.inl ht), zero_mul]
  · rw [hQsupp i k t (Or.inr ht), zero_mul]

/-- **Transposed full-line = windowed on `[0,σ]`** — `matBaxterUExt_eq_matBaxterU_of_support`
at `Qᵀ` (via `matBaxterUt(Ext)_eq_transpose`). -/
theorem matBaxterUtExt_eq_matBaxterUt_of_support (Psi Q : Matrix (Fin N) (Fin N) (ℝ → ℝ))
    (sigma : ℝ) (hsigma : 0 ≤ sigma) (hQsupp : ∀ i k t, t < 0 ∨ sigma < t → Q i k t = 0)
    (i j : Fin N) (r : ℝ) :
    matBaxterUtExt Psi Q i j r = matBaxterUt Psi Q sigma i j r := by
  rw [matBaxterUtExt_eq_transpose, matBaxterUt_eq_transpose]
  exact matBaxterUExt_eq_matBaxterU_of_support Psi (fun a b => Q b a) sigma hsigma
    (fun i k t ht => hQsupp k i t ht) i j r

/-- **The extended seed COINCIDES with the windowed corrected seed on `[0,σ]`** (equal diam).
So `matBaxterUQmSymFullExt = matBaxterUQmSymFull`, and the windowed chain's equal-diameter collapse
(`matBaxterUQmSym_of_symm` + `q0MixEntry` row-sum + `baxter_core_seed`) carries over — no tail, no
recursive range split. -/
theorem matBaxterUQmSymFullExt_eq_matBaxterUQmSymFull_of_support
    (Psi Q : Matrix (Fin N) (Fin N) (ℝ → ℝ))
    (sigma : ℝ) (hsigma : 0 ≤ sigma) (hQsupp : ∀ i k t, t < 0 ∨ sigma < t → Q i k t = 0)
    (i j : Fin N) (r : ℝ) :
    matBaxterUQmSymFullExt Psi Q i j r = matBaxterUQmSymFull Psi Q sigma i j r := by
  unfold matBaxterUQmSymFullExt matBaxterUQmSymFull
  rw [matBaxterUtExt_eq_matBaxterUt_of_support Psi Q sigma hsigma hQsupp i j r]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hUt : ∀ t, matBaxterUtExt Psi Q k j (r + t) = matBaxterUt Psi Q sigma k j (r + t) :=
    fun t => matBaxterUtExt_eq_matBaxterUt_of_support Psi Q sigma hsigma hQsupp k j (r + t)
  simp_rw [hUt]
  rw [intervalIntegral.integral_of_le hsigma, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  refine (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (fun t ht => ?_)).symm
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
  rcases ht with ht | ht
  · rw [hQsupp i k t (Or.inl ht), zero_mul]
  · rw [hQsupp i k t (Or.inr ht), zero_mul]

/-- **The corrected seed = the prototype at symmetric `Q`.**  `matBaxterUQmSymFull`
differs only in the leading arm (`matBaxterUt` vs `matBaxterU`); at symmetric
`Q` the transpose is invisible (`matBaxterUt_of_symm`), so they coincide.  Bridge to the existing
row-collapse (`matBaxterUQmSym_of_symm` → `matBaxterUQm` → `baxter_core_seed`). -/
theorem matBaxterUQmSymFull_eq_matBaxterUQmSym_of_symm (Psi Q : Matrix (Fin N) (Fin N) (ℝ → ℝ))
    (sigma : ℝ) (hsym : ∀ i j, Q i j = Q j i) (i j : Fin N) (r : ℝ) :
    matBaxterUQmSymFull Psi Q sigma i j r = matBaxterUQmSym Psi Q sigma i j r := by
  rw [matBaxterUQmSymFull, matBaxterUQmSym, matBaxterUt_of_symm Psi Q sigma hsym i j r]

/-- **Equal-diameter collapse of the EXTENDED seed to the prototype.**  Combining the support
reduction (`…_of_support`, `λ=0` no tail) with symmetry (`…_of_symm`): for a factor supported in
`[0,σ]` and symmetric (the equal-diameter physical Baxter factor), `matBaxterUQmSymFullExt =
matBaxterUQmSym` — so the extended seed inherits the windowed prototype's row-collapse to `r·c_HS`
verbatim, with NO tail and NO recursive range split. -/
theorem matBaxterUQmSymFullExt_eq_matBaxterUQmSym_of_equalDiam
    (Psi Q : Matrix (Fin N) (Fin N) (ℝ → ℝ))
    (sigma : ℝ) (hsigma : 0 ≤ sigma) (hQsupp : ∀ i k t, t < 0 ∨ sigma < t → Q i k t = 0)
    (hsym : ∀ i j, Q i j = Q j i) (i j : Fin N) (r : ℝ) :
    matBaxterUQmSymFullExt Psi Q i j r = matBaxterUQmSym Psi Q sigma i j r := by
  rw [matBaxterUQmSymFullExt_eq_matBaxterUQmSymFull_of_support Psi Q sigma hsigma hQsupp i j r,
    matBaxterUQmSymFull_eq_matBaxterUQmSym_of_symm Psi Q sigma hsym i j r]

/-! ### Unequal diameters — the recursive range split of the core moment reduction.
For `λ<0` the inner sample `r+t` in the seed's core term exits the moment-clean core at `t=σ+λ−r`;
`matBaxterUtExt_conv_boundary_split` decomposes the inner integral there, and
`matBaxterUtExt_conv_moment_part` reduces the below-boundary part to explicit column moments —
leaving the above-boundary **outer part** (Yukawa/renewal `Ψ`) as the remaining Wertheim–Thiele
input. -/

/-- **The seed's inner integral splits at the moment/outer boundary `σ+λ−r`.**  In the seed's core
term `∫_λ^{σ−r} Qᵢₖ·matBaxterUtExtₖⱼ(r+t)` the inner arg is `r+t ∈ [r+λ, σ)`.  The moment form
(`matBaxterUtExt_core`, core value `−v`) applies only where `r+t < σ+λ`, i.e. `t < σ+λ−r`.  So the
integral splits at `t = σ+λ−r` into the **moment part** `∫_λ^{σ+λ−r}` (arg `< σ+λ`) and the **outer
part** `∫_{σ+λ−r}^{σ−r}` (arg `∈ [σ+λ, σ)`, where `matBaxterUtExt` carries the Yukawa/renewal — NOT
`−v` — values).  Makes the recursive regime structure explicit: the gap recurs one level down at
exactly `σ+λ−r`. -/
theorem matBaxterUtExt_conv_boundary_split (Psi Q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma lam : ℝ)
    (i k j : Fin N) {r : ℝ}
    (hint1 : IntervalIntegrable (fun t => Q i k t * matBaxterUtExt Psi Q k j (r + t))
      volume lam (sigma + lam - r))
    (hint2 : IntervalIntegrable (fun t => Q i k t * matBaxterUtExt Psi Q k j (r + t))
      volume (sigma + lam - r) (sigma - r)) :
    (∫ t in lam..(sigma - r), Q i k t * matBaxterUtExt Psi Q k j (r + t))
      = (∫ t in lam..(sigma + lam - r), Q i k t * matBaxterUtExt Psi Q k j (r + t))
        + ∫ t in (sigma + lam - r)..(sigma - r), Q i k t * matBaxterUtExt Psi Q k j (r + t) :=
  (intervalIntegral.integral_add_adjacent_intervals hint1 hint2).symm

/-- **The moment part reduces to explicit column moments** (unequal diameters, `|λ| < r < σ`).  On
the sub-interval `[λ, σ+λ−r]` the inner arg `r+t ∈ (0, σ+λ)` stays in the moment-clean core, so
`matBaxterUtExtₖⱼ(r+t) = (r+t)·(∑ₗ M₀ₗₖ − 1) − ∑ₗ M₁ₗₖ` (`matBaxterUtExt_core`), turning the moment
part into an explicit `Q`-weighted moment polynomial in `r+t`.  The genuine remaining input is the
**outer part** `∫_{σ+λ−r}^{σ−r}` (arg `∈ [σ+λ, σ)`), where `matBaxterUtExt` is the renewal/Yukawa
solution — the mixture Wertheim–Thiele contribution the `[0,σ]` chain never met. -/
theorem matBaxterUtExt_conv_moment_part (sigma lam : ℝ) (hlam : lam ≤ 0)
    (Psi Q : Matrix (Fin N) (Fin N) (ℝ → ℝ))
    (hQ0 : ∀ i k, Integrable (Q k i))
    (hQ1 : ∀ i k, Integrable (fun t => t * Q k i t))
    (hQsupp : ∀ i k t, t < lam ∨ sigma < t → Q k i t = 0)
    (hcore : ∀ (k j : Fin N) (v : ℝ), v ∈ Set.Ioo (-sigma) sigma → Psi k j v = -v)
    {r : ℝ} (hrlo : -lam < r) (hrhi : r < sigma) (i k j : Fin N) :
    (∫ t in lam..(sigma + lam - r), Q i k t * matBaxterUtExt Psi Q k j (r + t))
      = ∫ t in lam..(sigma + lam - r),
          Q i k t * ((r + t) * ((∑ l, ∫ s, Q l k s) - 1) - ∑ l, ∫ s, s * Q l k s) := by
  refine intervalIntegral.integral_congr_ae ?_
  have hne : ∀ᵐ t : ℝ, t ≠ sigma + lam - r := by rw [MeasureTheory.ae_iff]; simp
  filter_upwards [hne] with t hne2 hmem
  rw [Set.uIoc_of_le (by linarith : lam ≤ sigma + lam - r)] at hmem
  have hlt : t < sigma + lam - r := lt_of_le_of_ne hmem.2 hne2
  rw [matBaxterUtExt_core sigma lam hlam Psi Q hQ0 hQ1 hQsupp hcore
    (by linarith [hmem.1] : 0 < r + t) (by linarith [hlt] : r + t < sigma + lam) k j]

/-- **The outer-`Ψ` convolution IS the mixture renewal integral.**  Substituting `w = v − s`, the
outer part of `matBaxterUtExt`'s convolution — `∫_λ^{v−σ} Q(s)·Ψ(v−s)` (with `v−s ∈ [σ, v−λ]`, where
`Ψ` has left the core) — equals the **renewal-form** `∫_σ^{v−λ} Q(v−w)·Ψ(w) dw`.  That is the
mixture Wiener–Hopf renewal convolution `∑ₘ ∫_σ^· Qₘₖ(·−w)·Ψₘⱼ(w)` determining `Ψ` on `[σ,∞)`
(`matBaxterPsiOuter`/`MatRenewalEq`).  So the residual outer-`Ψ` Wertheim–Thiele contribution is
governed by the renewal — NOT a new object, but the value of the ALREADY-CONSTRUCTED renewal
solution on `[σ, v−λ]`.  This pins the last unequal-diameter input to the renewal `Ψ`-outer values,
which exist; the momentum route (`matDCFfull_shell_laplace`) sidesteps it entirely. -/
theorem outer_conv_eq_renewal_form (Q Psi : ℝ → ℝ) (lam sigma v : ℝ) :
    (∫ s in lam..(v - sigma), Q s * Psi (v - s))
      = ∫ w in sigma..(v - lam), Q (v - w) * Psi w := by
  have hF : (∫ s in lam..(v - sigma), Q s * Psi (v - s))
      = ∫ s in lam..(v - sigma), (fun x => Q (v - x) * Psi x) (v - s) := by
    refine intervalIntegral.integral_congr (fun s _ => ?_)
    simp only [sub_sub_cancel]
  rw [hF, intervalIntegral.integral_comp_sub_left (fun x => Q (v - x) * Psi x) v,
    show v - (v - sigma) = sigma from by ring]

/-! ### Renewal-`Ψ` closure — the intermediate-region seed grounded in `matBaxterPsiOuter`.
The recursive range split left the intermediate-region seed depending on `Ψ` OUTSIDE the core
(`v−s ≥ σ`), the mixture Wertheim–Thiele contribution the `[0,σ]` chain never met.  These two
lemmas close it: the convolution at the moment/renewal boundary `v−σ` splits into a **renewal
part** (`= MatRenewalEq`'s convolution, the ALREADY-BUILT `matBaxterPsiOuter`) plus a **core part**
(`Ψ = −v`, reduces to moments).  So the last unequal-diameter input is a renewal convolution of the
existing outer solution — no new object, and the momentum route sidesteps it entirely. -/

/-- **The intermediate convolution splits into renewal + core (scalar).**  At the moment/renewal
boundary `s = v−σ`, `∫_λ^σ Q(s)·Ψ(v−s) ds` = the **renewal part** `∫_σ^{v−λ} Q(v−w)·Ψ(w) dw`
(the `v−s ≥ σ` samples, via `outer_conv_eq_renewal_form`; this is `MatRenewalEq`'s convolution,
grounded in `matBaxterPsiOuter`) + the **core part** `∫_{v−σ}^σ Q(s)·Ψ(v−s) ds` (the `v−s ≤ σ`
samples, where `Ψ = −v` reduces to moments). -/
theorem convolution_split_renewal_core (Q Psi : ℝ → ℝ) (lam sigma v : ℝ)
    (hlo : IntervalIntegrable (fun s => Q s * Psi (v - s)) volume lam (v - sigma))
    (hhi : IntervalIntegrable (fun s => Q s * Psi (v - s)) volume (v - sigma) sigma) :
    (∫ s in lam..sigma, Q s * Psi (v - s))
      = (∫ w in sigma..(v - lam), Q (v - w) * Psi w)
        + ∫ s in (v - sigma)..sigma, Q s * Psi (v - s) := by
  rw [← intervalIntegral.integral_add_adjacent_intervals hlo hhi, outer_conv_eq_renewal_form]

/-- **`matBaxterUtExt`'s intermediate value = `Ψ − (renewal conv) − (core conv)`.**  Applying the
scalar split entry-by-entry (with `∫_ℝ = ∫_λ^σ` from the `[λ,σ]` support of the physical factor):
`matBaxterUtExtᵢⱼ(v) = Ψᵢⱼ(v) − ∑ₘ[∫_σ^{v−λ} Qₘᵢ(v−w)·Ψₘⱼ(w) + ∫_{v−σ}^σ Qₘᵢ(s)·Ψₘⱼ(v−s)]`.  The
first sum is the mixture Wiener–Hopf renewal convolution of the ALREADY-CONSTRUCTED outer solution
`matBaxterPsiOuter` (`MatRenewalEq`); the second is the core piece that reduces to moments.  So the
final unequal-diameter input is pinned to an EXISTING construction — the real-space route closes to
`matBaxterPsiOuter`, and the operator route (`matDCFfull_shell_laplace`) closes without it. -/
theorem matBaxterUtExt_intermediate_decomp (Psi Q : Matrix (Fin N) (Fin N) (ℝ → ℝ))
    (sigma lam : ℝ) (hlamsig : lam ≤ sigma)
    (hQsupp : ∀ i k t, t < lam ∨ sigma < t → Q k i t = 0)
    (i j : Fin N) (v : ℝ)
    (hlo : ∀ m, IntervalIntegrable (fun s => Q m i s * Psi m j (v - s)) volume lam (v - sigma))
    (hhi : ∀ m, IntervalIntegrable (fun s => Q m i s * Psi m j (v - s)) volume (v - sigma) sigma) :
    matBaxterUtExt Psi Q i j v
      = Psi i j v
        - ∑ m, ((∫ w in sigma..(v - lam), Q m i (v - w) * Psi m j w)
            + ∫ s in (v - sigma)..sigma, Q m i s * Psi m j (v - s)) := by
  unfold matBaxterUtExt
  congr 1
  refine Finset.sum_congr rfl (fun m _ => ?_)
  have hfull : (∫ s, Q m i s * Psi m j (v - s))
      = ∫ s in lam..sigma, Q m i s * Psi m j (v - s) := by
    rw [intervalIntegral.integral_of_le hlamsig, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    refine (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (fun s hs => ?_)).symm
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hs
    rcases hs with hs | hs
    · rw [hQsupp i m s (Or.inl hs), zero_mul]
    · rw [hQsupp i m s (Or.inr hs), zero_mul]
  rw [hfull, convolution_split_renewal_core (Q m i) (Psi m j) lam sigma v (hlo m) (hhi m)]

/-! ### Unequal-diameter arm — the complete intermediate-region closed form

The three regions of `matBaxterUtExt` on the unequal-diameter arm (`λ < 0`, the contracted factor):
* **core** `0 < v < σ+λ` — `matBaxterUtExt_core`: the pure moment form `v·(∑ₖ∫Q − 1) − ∑ₖ∫ t·Q`;
* **intermediate** `σ+λ ≤ v < σ` — `matBaxterUtExt_intermediate_closed` (this lemma): the
  genuinely unequal-diameter piece, where the convolution straddles `σ`;
* **outer** `v ≥ σ` — `matBaxterUtExt = 0` (claim `(A)`, discharged by the renewal via
  `matBaxterU_outer` at `Qᵀ`; consumed as `hUtouter`).
At equal diameters (`λ = 0`) the intermediate region `[σ+λ, σ) = [σ, σ)` is EMPTY, so this lemma
is the whole unequal-diameter content, and the arm is fully explicit end-to-end. -/

/-- **The complete intermediate-region closed form of `matBaxterUtExt`.**  On `σ+λ ≤ v < σ` (implied
by `0 < v < σ`), reducing `matBaxterUtExt_intermediate_decomp` by the core values `Ψ = −·`:
`matBaxterUtExtᵢⱼ(v) = −v − ∑ₘ[∫_σ^{v−λ} Qₘᵢ(v−w)·Ψₘⱼ(w) + (∫_{v−σ}^σ s·Qₘᵢ − v·∫_{v−σ}^σ Qₘᵢ)]`.
The first inner integral is `Ψouter` (the constructed Banach solution, `w ≥ σ`) against `Q`'s
sub-zero tail; the parenthesised part is the explicit `[v−σ, σ]` moments of `Qₘᵢ`.  Every term is a
constant, a moment of the Baxter factor, or the constructed outer solution — no fixed point. -/
theorem matBaxterUtExt_intermediate_closed (Psi Q : Matrix (Fin N) (Fin N) (ℝ → ℝ))
    (sigma lam : ℝ) (hlamsig : lam ≤ sigma)
    (hQsupp : ∀ i k t, t < lam ∨ sigma < t → Q k i t = 0)
    (hcore : ∀ (k j : Fin N) (v : ℝ), v ∈ Set.Ioo (-sigma) sigma → Psi k j v = -v)
    (i j : Fin N) {v : ℝ} (hv0 : 0 < v) (hvs : v < sigma)
    (hlo : ∀ m, IntervalIntegrable (fun s => Q m i s * Psi m j (v - s)) volume lam (v - sigma))
    (hhi : ∀ m, IntervalIntegrable (fun s => Q m i s * Psi m j (v - s)) volume (v - sigma) sigma)
    (hQII : ∀ m, IntervalIntegrable (Q m i) volume (v - sigma) sigma)
    (hQII1 : ∀ m, IntervalIntegrable (fun s => s * Q m i s) volume (v - sigma) sigma) :
    matBaxterUtExt Psi Q i j v
      = -v - ∑ m, ((∫ w in sigma..(v - lam), Q m i (v - w) * Psi m j w)
          + ((∫ s in (v - sigma)..sigma, s * Q m i s)
              - v * ∫ s in (v - sigma)..sigma, Q m i s)) := by
  rw [matBaxterUtExt_intermediate_decomp Psi Q sigma lam hlamsig hQsupp i j v hlo hhi,
    hcore i j v ⟨by linarith, hvs⟩]
  congr 1
  refine Finset.sum_congr rfl (fun m _ => ?_)
  congr 1
  have hcp : (∫ s in (v - sigma)..sigma, Q m i s * Psi m j (v - s))
      = ∫ s in (v - sigma)..sigma, (s * Q m i s - v * Q m i s) := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall (fun s hmem => ?_))
    rw [Set.uIoc_of_le (by linarith : v - sigma ≤ sigma)] at hmem
    rw [hcore m j (v - s) ⟨by linarith [hmem.2], by linarith [hmem.1]⟩]; ring
  rw [hcp, intervalIntegral.integral_sub (hQII1 m) ((hQII m).const_mul v),
    intervalIntegral.integral_const_mul]

/-! ### Unequal-diameter complete assembly of `matBaxterUQmSymFullExt`

The master reduction `matBaxterUQmSymFullExt_eq_rPhi_of_seed` reduces the corrected extended seed to
a single `hseed` on `(0, σ−λ)`.  This lemma assembles that seed's LHS on `−λ < r < σ` into a form
where EVERY sub-piece has an established closed form — the culmination of the unequal-diameter arm:
* the **leading** `matBaxterUtExtᵢⱼ(r)` — `matBaxterUtExt_core` (moments, `r<σ+λ`) or
  `matBaxterUtExt_intermediate_closed` (`σ+λ≤r<σ`);
* the **moment part** `∫_λ^{σ+λ−r} Qᵢₖ·[(r+t)(∑M₀−1) − ∑M₁]` — explicit column moments
  (`matBaxterUtExt_conv_moment_part`, since `r+t < σ+λ` there);
* the **outer part** `∫_{σ+λ−r}^{σ−r} Qᵢₖ·matBaxterUtExtₖⱼ(r+t)` — the inner arg `r+t ∈ [σ+λ, σ)` is
  the INTERMEDIATE region, whose integrand is exactly `matBaxterUtExt_intermediate_closed`.
So the seed is fully explicit up to the classical Wertheim–Thiele identity `= r·Φ`; no piece is an
implicit fixed point.  (The outer part carries the `Ψouter` integrals — the genuinely
unequal-diameter contribution the `[0,σ]` chain never met, now closed-form via the intermediate
lemma.) -/

/-- **Complete assembly of the corrected extended seed on `−λ < r < σ`.**  Chaining
`matBaxterUQmSymFullExt_core_reduce` (`= matBaxterUtExt − ∑ₖ ∫_λ^{σ−r} Qᵢₖ·matBaxterUtExtₖⱼ(r+t)`),
`matBaxterUtExt_conv_boundary_split` (split the inner integral at `σ+λ−r`), and
`matBaxterUtExt_conv_moment_part` (reduce the `[λ,σ+λ−r]` moment part to explicit column moments):
`matBaxterUQmSymFullExtᵢⱼ(r) = matBaxterUtExtᵢⱼ(r) − ∑ₖ[momentPolyᵢₖ + outerPartᵢₖⱼ]`, with the
moment part explicit and the outer part `∫_{σ+λ−r}^{σ−r} Qᵢₖ·matBaxterUtExtₖⱼ(r+t)` the intermediate
integral (integrand `= matBaxterUtExt_intermediate_closed`). -/
theorem matBaxterUQmSymFullExt_core_assembled (Psi Q : Matrix (Fin N) (Fin N) (ℝ → ℝ))
    (sigma lam : ℝ) (hlam : lam ≤ 0)
    (hUtouter : ∀ i j r, sigma ≤ r → matBaxterUtExt Psi Q i j r = 0)
    (hQlam : ∀ i k t, t < lam → Q i k t = 0)
    (hQ0 : ∀ i k, Integrable (Q k i)) (hQ1 : ∀ i k, Integrable (fun t => t * Q k i t))
    (hQsupp : ∀ i k t, t < lam ∨ sigma < t → Q k i t = 0)
    (hcore : ∀ (k j : Fin N) (v : ℝ), v ∈ Set.Ioo (-sigma) sigma → Psi k j v = -v)
    {r : ℝ} (hrlo : -lam < r) (hrhi : r < sigma) (i j : Fin N)
    (hint1 : ∀ k, IntervalIntegrable (fun t => Q i k t * matBaxterUtExt Psi Q k j (r + t))
      volume lam (sigma + lam - r))
    (hint2 : ∀ k, IntervalIntegrable (fun t => Q i k t * matBaxterUtExt Psi Q k j (r + t))
      volume (sigma + lam - r) (sigma - r)) :
    matBaxterUQmSymFullExt Psi Q i j r
      = matBaxterUtExt Psi Q i j r
        - ∑ k, ((∫ t in lam..(sigma + lam - r),
                Q i k t * ((r + t) * ((∑ l, ∫ s, Q l k s) - 1) - ∑ l, ∫ s, s * Q l k s))
            + ∫ t in (sigma + lam - r)..(sigma - r), Q i k t * matBaxterUtExt Psi Q k j (r + t)) :=
    by
  rw [matBaxterUQmSymFullExt_core_reduce Psi Q sigma lam hUtouter hQlam
        (by linarith : lam ≤ sigma - r) i j]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [matBaxterUtExt_conv_boundary_split Psi Q sigma lam i k j (hint1 k) (hint2 k),
    matBaxterUtExt_conv_moment_part sigma lam hlam Psi Q hQ0 hQ1 hQsupp hcore hrlo hrhi i k j]

/-! ### Outer part → `matBaxterUtExt_intermediate_closed`: the fully-explicit corrected seed

`matBaxterUQmSymFullExt_core_assembled` left the outer part
`∫_{σ+λ−r}^{σ−r} Qᵢₖ·matBaxterUtExtₖⱼ(r+t)` symbolic.  Its inner arg `r+t ∈ [σ+λ, σ)` is the
INTERMEDIATE region, so `matBaxterUtExt_intermediate_closed` substitutes its closed form under the
integral — eliminating the last symbolic `matBaxterUtExt` and giving a seed in which every integral
is an explicit moment or `Ψouter` integral of the Baxter factor. -/

/-- **Outer part in closed form.**  On `[σ+λ−r, σ−r]` the inner arg `r+t ∈ [σ+λ, σ)` (using
`0 ≤ σ+λ`), so `matBaxterUtExtₖⱼ(r+t)` is replaced by `matBaxterUtExt_intermediate_closed` under the
integral (a.e., excluding the null endpoint `t = σ−r`). -/
theorem matBaxterUtExt_conv_outer_part_closed (Psi Q : Matrix (Fin N) (Fin N) (ℝ → ℝ))
    (sigma lam : ℝ) (hlam : lam ≤ 0) (hlamsig : lam ≤ sigma) (hsl : 0 ≤ sigma + lam)
    (hQsupp : ∀ i k t, t < lam ∨ sigma < t → Q k i t = 0)
    (hcore : ∀ (k j : Fin N) (v : ℝ), v ∈ Set.Ioo (-sigma) sigma → Psi k j v = -v)
    (i k j : Fin N) {r : ℝ}
    (hlo : ∀ t, ∀ m, IntervalIntegrable (fun s => Q m k s * Psi m j (r + t - s)) volume
      lam (r + t - sigma))
    (hhi : ∀ t, ∀ m, IntervalIntegrable (fun s => Q m k s * Psi m j (r + t - s)) volume
      (r + t - sigma) sigma)
    (hQII : ∀ t, ∀ m, IntervalIntegrable (Q m k) volume (r + t - sigma) sigma)
    (hQII1 : ∀ t, ∀ m, IntervalIntegrable (fun s => s * Q m k s) volume (r + t - sigma) sigma) :
    (∫ t in (sigma + lam - r)..(sigma - r), Q i k t * matBaxterUtExt Psi Q k j (r + t))
      = ∫ t in (sigma + lam - r)..(sigma - r),
          Q i k t * (-(r + t)
            - ∑ m, ((∫ w in sigma..(r + t - lam), Q m k (r + t - w) * Psi m j w)
              + ((∫ s in (r + t - sigma)..sigma, s * Q m k s)
                  - (r + t) * ∫ s in (r + t - sigma)..sigma, Q m k s))) := by
  refine intervalIntegral.integral_congr_ae ?_
  have hne : ∀ᵐ t : ℝ, t ≠ sigma - r := by rw [MeasureTheory.ae_iff]; simp
  filter_upwards [hne] with t hne2 hmem
  rw [Set.uIoc_of_le (by linarith : sigma + lam - r ≤ sigma - r)] at hmem
  have hvhi : r + t < sigma := by have := lt_of_le_of_ne hmem.2 hne2; linarith
  have hvlo : 0 < r + t := by linarith [hmem.1]
  rw [matBaxterUtExt_intermediate_closed Psi Q sigma lam hlamsig hQsupp hcore k j
    hvlo hvhi (hlo t) (hhi t) (hQII t) (hQII1 t)]

/-- **The corrected extended seed, FULLY explicit on `−λ < r < σ`.**
`matBaxterUQmSymFullExt_core_assembled` with its outer part replaced by
`matBaxterUtExt_conv_outer_part_closed`: `matBaxterUQmSymFullExtᵢⱼ(r) = matBaxterUtExtᵢⱼ(r) −
∑ₖ[momentPolyᵢₖ + outerClosedᵢₖⱼ]`, the moment part explicit column moments and the outer part now
the closed intermediate form (no symbolic `matBaxterUtExt` under any integral).  The only remaining
leading `matBaxterUtExtᵢⱼ(r)` is a single boundary value (`matBaxterUtExt_core` for `r<σ+λ`, else
`matBaxterUtExt_intermediate_closed`).  So the seed is explicit up to the classical WT `= r·Φ`. -/
theorem matBaxterUQmSymFullExt_core_fully_explicit (Psi Q : Matrix (Fin N) (Fin N) (ℝ → ℝ))
    (sigma lam : ℝ) (hlam : lam ≤ 0) (hlamsig : lam ≤ sigma) (hsl : 0 ≤ sigma + lam)
    (hUtouter : ∀ i j r, sigma ≤ r → matBaxterUtExt Psi Q i j r = 0)
    (hQlam : ∀ i k t, t < lam → Q i k t = 0)
    (hQ0 : ∀ i k, Integrable (Q k i)) (hQ1 : ∀ i k, Integrable (fun t => t * Q k i t))
    (hQsupp : ∀ i k t, t < lam ∨ sigma < t → Q k i t = 0)
    (hcore : ∀ (k j : Fin N) (v : ℝ), v ∈ Set.Ioo (-sigma) sigma → Psi k j v = -v)
    {r : ℝ} (hrlo : -lam < r) (hrhi : r < sigma) (i j : Fin N)
    (hint1 : ∀ k, IntervalIntegrable (fun t => Q i k t * matBaxterUtExt Psi Q k j (r + t))
      volume lam (sigma + lam - r))
    (hint2 : ∀ k, IntervalIntegrable (fun t => Q i k t * matBaxterUtExt Psi Q k j (r + t))
      volume (sigma + lam - r) (sigma - r))
    (hOlo : ∀ k t m, IntervalIntegrable (fun s => Q m k s * Psi m j (r + t - s)) volume
      lam (r + t - sigma))
    (hOhi : ∀ k t m, IntervalIntegrable (fun s => Q m k s * Psi m j (r + t - s)) volume
      (r + t - sigma) sigma)
    (hOQII : ∀ k t m, IntervalIntegrable (Q m k) volume (r + t - sigma) sigma)
    (hOQII1 : ∀ k t m, IntervalIntegrable (fun s => s * Q m k s) volume (r + t - sigma) sigma) :
    matBaxterUQmSymFullExt Psi Q i j r
      = matBaxterUtExt Psi Q i j r
        - ∑ k, ((∫ t in lam..(sigma + lam - r),
                Q i k t * ((r + t) * ((∑ l, ∫ s, Q l k s) - 1) - ∑ l, ∫ s, s * Q l k s))
            + ∫ t in (sigma + lam - r)..(sigma - r),
                Q i k t * (-(r + t)
                  - ∑ m, ((∫ w in sigma..(r + t - lam), Q m k (r + t - w) * Psi m j w)
                    + ((∫ s in (r + t - sigma)..sigma, s * Q m k s)
                        - (r + t) * ∫ s in (r + t - sigma)..sigma, Q m k s)))) := by
  rw [matBaxterUQmSymFullExt_core_assembled Psi Q sigma lam hlam hUtouter hQlam hQ0 hQ1
    hQsupp hcore hrlo hrhi i j hint1 hint2]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [matBaxterUtExt_conv_outer_part_closed Psi Q sigma lam hlam hlamsig hsl hQsupp hcore i k j
    (hOlo k) (hOhi k) (hOQII k) (hOQII1 k)]

/-! ### Leading boundary value substituted — zero symbolic `matBaxterUtExt`

`matBaxterUQmSymFullExt_core_fully_explicit` left one symbolic term: the LEADING boundary value
`matBaxterUtExtᵢⱼ(r)`.  Substituting its own closed form (`matBaxterUtExt_core` for `r<σ+λ`,
`matBaxterUtExt_intermediate_closed` for `σ+λ≤r<σ`) removes it too — the two lemmas below cover the
whole `−λ < r < σ`, so the corrected extended seed becomes an expression in the Baxter factor `Q`
and the constructed outer solution `Ψouter` with NO `matBaxterUtExt` anywhere. -/

/-- **Fully-explicit seed, moment leading (`−λ < r < σ+λ`).**  On the core-leading sub-region the
leading `matBaxterUtExtᵢⱼ(r) = matBaxterUtExt_core` (pure moments), so composing with
`matBaxterUQmSymFullExt_core_fully_explicit` gives the seed with NO symbolic `matBaxterUtExt`
anywhere — every term a `Q`-moment or `Ψouter` integral. -/
theorem matBaxterUQmSymFullExt_fully_explicit_momentLead
    (Psi Q : Matrix (Fin N) (Fin N) (ℝ → ℝ))
    (sigma lam : ℝ) (hlam : lam ≤ 0) (hlamsig : lam ≤ sigma) (hsl : 0 ≤ sigma + lam)
    (hUtouter : ∀ i j r, sigma ≤ r → matBaxterUtExt Psi Q i j r = 0)
    (hQlam : ∀ i k t, t < lam → Q i k t = 0)
    (hQ0 : ∀ i k, Integrable (Q k i)) (hQ1 : ∀ i k, Integrable (fun t => t * Q k i t))
    (hQsupp : ∀ i k t, t < lam ∨ sigma < t → Q k i t = 0)
    (hcore : ∀ (k j : Fin N) (v : ℝ), v ∈ Set.Ioo (-sigma) sigma → Psi k j v = -v)
    {r : ℝ} (hrlo : -lam < r) (hrhi2 : r < sigma + lam) (i j : Fin N)
    (hint1 : ∀ k, IntervalIntegrable (fun t => Q i k t * matBaxterUtExt Psi Q k j (r + t))
      volume lam (sigma + lam - r))
    (hint2 : ∀ k, IntervalIntegrable (fun t => Q i k t * matBaxterUtExt Psi Q k j (r + t))
      volume (sigma + lam - r) (sigma - r))
    (hOlo : ∀ k t m, IntervalIntegrable (fun s => Q m k s * Psi m j (r + t - s)) volume
      lam (r + t - sigma))
    (hOhi : ∀ k t m, IntervalIntegrable (fun s => Q m k s * Psi m j (r + t - s)) volume
      (r + t - sigma) sigma)
    (hOQII : ∀ k t m, IntervalIntegrable (Q m k) volume (r + t - sigma) sigma)
    (hOQII1 : ∀ k t m, IntervalIntegrable (fun s => s * Q m k s) volume (r + t - sigma) sigma) :
    matBaxterUQmSymFullExt Psi Q i j r
      = (r * ((∑ k, ∫ t, Q k i t) - 1) - ∑ k, ∫ t, t * Q k i t)
        - ∑ k, ((∫ t in lam..(sigma + lam - r),
                Q i k t * ((r + t) * ((∑ l, ∫ s, Q l k s) - 1) - ∑ l, ∫ s, s * Q l k s))
            + ∫ t in (sigma + lam - r)..(sigma - r),
                Q i k t * (-(r + t)
                  - ∑ m, ((∫ w in sigma..(r + t - lam), Q m k (r + t - w) * Psi m j w)
                    + ((∫ s in (r + t - sigma)..sigma, s * Q m k s)
                        - (r + t) * ∫ s in (r + t - sigma)..sigma, Q m k s)))) := by
  rw [matBaxterUQmSymFullExt_core_fully_explicit Psi Q sigma lam hlam hlamsig hsl hUtouter hQlam
      hQ0 hQ1 hQsupp hcore hrlo (by linarith : r < sigma) i j hint1 hint2 hOlo hOhi hOQII hOQII1,
    matBaxterUtExt_core sigma lam hlam Psi Q hQ0 hQ1 hQsupp hcore (by linarith : 0 < r) hrhi2 i j]

/-- **Fully-explicit seed, intermediate leading (`σ+λ ≤ r < σ`).**  On the outer-leading sub-region
the leading `matBaxterUtExtᵢⱼ(r) = matBaxterUtExt_intermediate_closed`, removing the last symbolic
`matBaxterUtExt`.  Together with `…_momentLead` this covers all of `−λ < r < σ`. -/
theorem matBaxterUQmSymFullExt_fully_explicit_intermediateLead
    (Psi Q : Matrix (Fin N) (Fin N) (ℝ → ℝ))
    (sigma lam : ℝ) (hlam : lam ≤ 0) (hlamsig : lam ≤ sigma) (hsl : 0 ≤ sigma + lam)
    (hUtouter : ∀ i j r, sigma ≤ r → matBaxterUtExt Psi Q i j r = 0)
    (hQlam : ∀ i k t, t < lam → Q i k t = 0)
    (hQ0 : ∀ i k, Integrable (Q k i)) (hQ1 : ∀ i k, Integrable (fun t => t * Q k i t))
    (hQsupp : ∀ i k t, t < lam ∨ sigma < t → Q k i t = 0)
    (hcore : ∀ (k j : Fin N) (v : ℝ), v ∈ Set.Ioo (-sigma) sigma → Psi k j v = -v)
    {r : ℝ} (hrlo : -lam < r) (hrhi : r < sigma) (i j : Fin N)
    (hint1 : ∀ k, IntervalIntegrable (fun t => Q i k t * matBaxterUtExt Psi Q k j (r + t))
      volume lam (sigma + lam - r))
    (hint2 : ∀ k, IntervalIntegrable (fun t => Q i k t * matBaxterUtExt Psi Q k j (r + t))
      volume (sigma + lam - r) (sigma - r))
    (hOlo : ∀ k t m, IntervalIntegrable (fun s => Q m k s * Psi m j (r + t - s)) volume
      lam (r + t - sigma))
    (hOhi : ∀ k t m, IntervalIntegrable (fun s => Q m k s * Psi m j (r + t - s)) volume
      (r + t - sigma) sigma)
    (hOQII : ∀ k t m, IntervalIntegrable (Q m k) volume (r + t - sigma) sigma)
    (hOQII1 : ∀ k t m, IntervalIntegrable (fun s => s * Q m k s) volume (r + t - sigma) sigma)
    (hLlo : ∀ m, IntervalIntegrable (fun s => Q m i s * Psi m j (r - s)) volume lam (r - sigma))
    (hLhi : ∀ m, IntervalIntegrable (fun s => Q m i s * Psi m j (r - s)) volume (r - sigma) sigma)
    (hLQII : ∀ m, IntervalIntegrable (Q m i) volume (r - sigma) sigma)
    (hLQII1 : ∀ m, IntervalIntegrable (fun s => s * Q m i s) volume (r - sigma) sigma) :
    matBaxterUQmSymFullExt Psi Q i j r
      = (-r - ∑ m, ((∫ w in sigma..(r - lam), Q m i (r - w) * Psi m j w)
            + ((∫ s in (r - sigma)..sigma, s * Q m i s)
                - r * ∫ s in (r - sigma)..sigma, Q m i s)))
        - ∑ k, ((∫ t in lam..(sigma + lam - r),
                Q i k t * ((r + t) * ((∑ l, ∫ s, Q l k s) - 1) - ∑ l, ∫ s, s * Q l k s))
            + ∫ t in (sigma + lam - r)..(sigma - r),
                Q i k t * (-(r + t)
                  - ∑ m, ((∫ w in sigma..(r + t - lam), Q m k (r + t - w) * Psi m j w)
                    + ((∫ s in (r + t - sigma)..sigma, s * Q m k s)
                        - (r + t) * ∫ s in (r + t - sigma)..sigma, Q m k s)))) := by
  rw [matBaxterUQmSymFullExt_core_fully_explicit Psi Q sigma lam hlam hlamsig hsl hUtouter hQlam
      hQ0 hQ1 hQsupp hcore hrlo hrhi i j hint1 hint2 hOlo hOhi hOQII hOQII1,
    matBaxterUtExt_intermediate_closed Psi Q sigma lam hlamsig hQsupp hcore i j
      (by linarith : 0 < r) hrhi hLlo hLhi hLQII hLQII1]

/-! ### The Wertheim–Thiele numerical identity `= r·Φ` — proved at equal diameters

`matBaxterUQmSymFullExt_eq_rPhi_of_seed` reduces the corrected extended seed `= r·Φ` to a single
`hseed` — the Wertheim–Thiele numerical identity, now with a fully-explicit LHS
(`…_fully_explicit_*`).  At **equal diameters** (`λ=0`, symmetric factor) the intermediate region is
empty, the `Ψouter` coupling drops out, and the identity is the pure-moment `baxter_core_seed`: the
lemma below proves
`matBaxterUQmSymFullExt = r·c_HS` OUTRIGHT (no held seed), chaining the equal-diameter collapse to
the matrix moment seed and thence to the proved scalar `baxter_core_seed`
(`matBaxterUQm_eq_rcHS_of_rowSum`).

So the WT identity is genuinely PROVED wherever the factor is symmetric.  For unequal diameters
(`λ<0`) the identity additionally couples the explicit `Q`-moments with the `Ψouter` integrals of
`…_fully_explicit_intermediateLead` / `…_conv_outer_part_closed` — the classical Lebowitz mixture
`c_HS` result, the sole numerical input of the seed route.  The non-circular value route
`matOzStar_unique` (`MixtureRDFUniqueness.lean`) discharges MML.8 without it. -/

open FMSA.HardSphere in
/-- **WT identity at equal diameters — `matBaxterUQmSymFullExt = r·c_HS`, PROVED.**  For a symmetric
factor supported in `[0,σ]` with the equal-diameter row-sum `∑ₖ Qᵢₖ = q0_poly` (`hrow`), the
corrected extended seed equals `r·c_HS` on all `r > 0`.  Chain: `…_eq_matBaxterUQmSym_of_equalDiam`
(`λ=0` no tail) → `matBaxterUQmSym_of_symm` → `matBaxterUQm_eq_rcHS_of_rowSum` (grounded in the
scalar `baxter_core_seed`).  No held moment seed — the equal-diameter WT identity is discharged. -/
theorem matBaxterUQmSymFullExt_eq_rcHS_of_equalDiam
    (Psi Q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) {eta sigma rho : ℝ}
    (hsigma : 0 < sigma) (heta : eta < 1) (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6)
    (hQsupp : ∀ i k t, t < 0 ∨ sigma < t → Q i k t = 0)
    (hsym : ∀ i j, Q i j = Q j i)
    (hUouter : ∀ i j r, sigma ≤ r → matBaxterU Psi Q sigma i j r = 0)
    (hint : ∀ (i j k : Fin N) (r : ℝ), IntervalIntegrable
      (fun t => Q i k t * matBaxterU Psi Q sigma k j (r + t)) volume 0 sigma)
    (hrow : ∀ (i : Fin N) (u : ℝ), u ∈ Set.Icc (0:ℝ) sigma → ∑ k, Q i k u = q0_poly eta sigma rho u)
    (hQ0 : ∀ i k, IntervalIntegrable (Q i k) volume 0 sigma)
    (hQ1 : ∀ i k, IntervalIntegrable (fun t => t * Q i k t) volume 0 sigma)
    (hcore : ∀ (k j : Fin N) (v : ℝ), v ∈ Set.Ioo (-sigma) sigma → Psi k j v = -v)
    {r : ℝ} (hr : 0 < r) (i j : Fin N) :
    matBaxterUQmSymFullExt Psi Q i j r = r * c_HS eta sigma r := by
  rw [matBaxterUQmSymFullExt_eq_matBaxterUQmSym_of_equalDiam Psi Q sigma hsigma.le hQsupp hsym i j
      r, matBaxterUQmSym_of_symm Psi Q sigma hsym i j r]
  exact matBaxterUQm_eq_rcHS_of_rowSum Psi Q hsigma heta heta_def hUouter hint hrow hQ0 hQ1 hcore hr
    i j

open FMSA.HardSphere in
/-- **`hseed` DISCHARGED at equal diameters.**  The `hseed` hypothesis of
`matBaxterUQmSymFullExt_eq_rPhi_of_seed` / `correctedSeedExt_hclaimA` (`lam = 0`, `Φ = c_HS`) is
proved outright at equal diameters: its LHS is `matBaxterUQmSymFullExt` on the core
(`…_core_reduce`), which `…_eq_rcHS_of_equalDiam` shows equals `r·c_HS` (grounded
in the proved scalar `baxter_core_seed`). -/
theorem hseed_equalDiam (Psi Q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) {eta sigma rho : ℝ}
    (hsigma : 0 < sigma) (heta : eta < 1) (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6)
    (hQsupp : ∀ i k t, t < 0 ∨ sigma < t → Q i k t = 0)
    (hsym : ∀ i j, Q i j = Q j i)
    (hUtouter : ∀ i j r, sigma ≤ r → matBaxterUtExt Psi Q i j r = 0)
    (hUouter : ∀ i j r, sigma ≤ r → matBaxterU Psi Q sigma i j r = 0)
    (hint : ∀ (i j k : Fin N) (r : ℝ), IntervalIntegrable
      (fun t => Q i k t * matBaxterU Psi Q sigma k j (r + t)) volume 0 sigma)
    (hrow : ∀ (i : Fin N) (u : ℝ), u ∈ Set.Icc (0:ℝ) sigma → ∑ k, Q i k u = q0_poly eta sigma rho u)
    (hQ0 : ∀ i k, IntervalIntegrable (Q i k) volume 0 sigma)
    (hQ1 : ∀ i k, IntervalIntegrable (fun t => t * Q i k t) volume 0 sigma)
    (hcore : ∀ (k j : Fin N) (v : ℝ), v ∈ Set.Ioo (-sigma) sigma → Psi k j v = -v) :
    ∀ (i j : Fin N), ∀ r ∈ Set.Ioo (0 : ℝ) (sigma - 0),
      matBaxterUtExt Psi Q i j r
        - ∑ k, ∫ t in (0:ℝ)..(sigma - r), Q i k t * matBaxterUtExt Psi Q k j (r + t)
      = r * c_HS eta sigma r := by
  intro i j r hr
  rw [Set.mem_Ioo] at hr
  rw [← matBaxterUQmSymFullExt_core_reduce Psi Q sigma 0 hUtouter
      (fun i' k' t ht => hQsupp i' k' t (Or.inl ht)) (by linarith [hr.2]) i j]
  exact matBaxterUQmSymFullExt_eq_rcHS_of_equalDiam Psi Q hsigma heta heta_def hQsupp hsym hUouter
    hint hrow hQ0 hQ1 hcore hr.1 i j

/-! ### Unequal-diameter WT identity — the `Ψouter` coupling IS the constructed solution

For unequal diameters the WT identity `= r·Φ` couples the explicit `Q`-moments with `Ψouter`
integrals (`…_fully_explicit_intermediateLead`).  Those integrals `∫_σ^{v−λ} Q(v−w)·Ψₘⱼ(w)` sample
`Ψ` only on `w ≥ σ`, where the glued solution `matBaxterPsi Ψouter Ψcore σ` equals `Ψouter`.  So the
coupling is not a free unknown: it is a concrete integral of the CONSTRUCTED `matBaxterPsiOuter`.
This pins the sole unequal-diameter numerical input to the built outer solution; the non-circular
`matOzStar_unique` still discharges MML.8 without evaluating it. -/

/-- **The `Ψouter` coupling IS the constructed outer solution.**  In the renewal-form coupling
`∫_σ^{v−λ} Q(v−w)·Ψₘⱼ(w)` the argument `w ∈ [σ, v−λ]` is outer, so for the glued solution
`Ψ = matBaxterPsi Ψouter Ψcore σ` (`matBaxterPsi_outer`) the abstract `Ψ` is exactly the constructed
`Ψouter`. -/
theorem renewalForm_eq_outer (Po Pc : Matrix (Fin N) (Fin N) (ℝ → ℝ))
    (Q : ℝ → ℝ) (sigma lam v : ℝ) (hle : sigma ≤ v - lam) (m j : Fin N) :
    (∫ w in sigma..(v - lam), Q (v - w) * matBaxterPsi Po Pc sigma m j w)
      = ∫ w in sigma..(v - lam), Q (v - w) * Po m j w := by
  refine intervalIntegral.integral_congr (fun w hw => ?_)
  rw [Set.uIcc_of_le hle] at hw
  rw [matBaxterPsi_outer Po Pc m j hw.1]

/-- **Intermediate closed form of the glued solution, coupling shown as `Ψouter`.**  On the
intermediate region `σ+λ ≤ v < σ`, `matBaxterUtExt_intermediate_closed` for `Ψ = matBaxterPsi Ψouter
Ψcore σ` with the renewal-form rewritten by `renewalForm_eq_outer`: the coupling term is
`∫_σ^{v−λ} Qₘᵢ(v−w)·Ψouterₘⱼ(w)`
— the constructed `matBaxterPsiOuter`, not an abstract `Ψ`.  So the unequal-diameter WT identity's
`Ψouter` coupling is a concrete integral of the built solution. -/
theorem matBaxterUtExt_intermediate_closed_outer (Po Pc Q : Matrix (Fin N) (Fin N) (ℝ → ℝ))
    (sigma lam : ℝ) (hlamsig : lam ≤ sigma)
    (hQsupp : ∀ i k t, t < lam ∨ sigma < t → Q k i t = 0)
    (hcore : ∀ (k j : Fin N) (v : ℝ), v ∈ Set.Ioo (-sigma) sigma →
      matBaxterPsi Po Pc sigma k j v = -v)
    (i j : Fin N) {v : ℝ} (hv0 : 0 < v) (hvs : v < sigma) (hvlead : sigma + lam ≤ v)
    (hlo : ∀ m, IntervalIntegrable
      (fun s => Q m i s * matBaxterPsi Po Pc sigma m j (v - s)) volume lam (v - sigma))
    (hhi : ∀ m, IntervalIntegrable
      (fun s => Q m i s * matBaxterPsi Po Pc sigma m j (v - s)) volume (v - sigma) sigma)
    (hQII : ∀ m, IntervalIntegrable (Q m i) volume (v - sigma) sigma)
    (hQII1 : ∀ m, IntervalIntegrable (fun s => s * Q m i s) volume (v - sigma) sigma) :
    matBaxterUtExt (matBaxterPsi Po Pc sigma) Q i j v
      = -v - ∑ m, ((∫ w in sigma..(v - lam), Q m i (v - w) * Po m j w)
          + ((∫ s in (v - sigma)..sigma, s * Q m i s)
              - v * ∫ s in (v - sigma)..sigma, Q m i s)) := by
  rw [matBaxterUtExt_intermediate_closed (matBaxterPsi Po Pc sigma) Q sigma lam hlamsig hQsupp
    hcore i j hv0 hvs hlo hhi hQII hQII1]
  congr 1
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [renewalForm_eq_outer Po Pc (Q m i) sigma lam v (by linarith : sigma ≤ v - lam) m j]

/-- **Fully-explicit intermediate lead, entirely in `Ψouter`.**  For the glued solution
`Ψ = matBaxterPsi Ψouter Ψcore σ`, `…_fully_explicit_intermediateLead` with BOTH
coupling terms (the leading `∫_σ^{r−λ}` and the intermediate `∫_σ^{r+t−λ}`) rewritten by
`renewalForm_eq_outer` — so the entire fully-explicit unequal-diameter WT LHS is `Q`-moments plus
concrete integrals of the CONSTRUCTED `matBaxterPsiOuter`, with no abstract `Ψ` remaining. -/
theorem matBaxterUQmSymFullExt_fully_explicit_intermediateLead_outer
    (Po Pc Q : Matrix (Fin N) (Fin N) (ℝ → ℝ))
    (sigma lam : ℝ) (hlam : lam ≤ 0) (hlamsig : lam ≤ sigma) (hsl : 0 ≤ sigma + lam)
    (hUtouter : ∀ i j r, sigma ≤ r → matBaxterUtExt (matBaxterPsi Po Pc sigma) Q i j r = 0)
    (hQlam : ∀ i k t, t < lam → Q i k t = 0)
    (hQ0 : ∀ i k, Integrable (Q k i)) (hQ1 : ∀ i k, Integrable (fun t => t * Q k i t))
    (hQsupp : ∀ i k t, t < lam ∨ sigma < t → Q k i t = 0)
    (hcore : ∀ (k j : Fin N) (v : ℝ), v ∈ Set.Ioo (-sigma) sigma →
      matBaxterPsi Po Pc sigma k j v = -v)
    {r : ℝ} (hrlo : -lam < r) (hrhi : r < sigma) (hrlead : sigma + lam ≤ r) (i j : Fin N)
    (hint1 : ∀ k, IntervalIntegrable
      (fun t => Q i k t * matBaxterUtExt (matBaxterPsi Po Pc sigma) Q k j (r + t))
      volume lam (sigma + lam - r))
    (hint2 : ∀ k, IntervalIntegrable
      (fun t => Q i k t * matBaxterUtExt (matBaxterPsi Po Pc sigma) Q k j (r + t))
      volume (sigma + lam - r) (sigma - r))
    (hOlo : ∀ k t m, IntervalIntegrable
      (fun s => Q m k s * matBaxterPsi Po Pc sigma m j (r + t - s)) volume lam (r + t - sigma))
    (hOhi : ∀ k t m, IntervalIntegrable
      (fun s => Q m k s * matBaxterPsi Po Pc sigma m j (r + t - s)) volume (r + t - sigma) sigma)
    (hOQII : ∀ k t m, IntervalIntegrable (Q m k) volume (r + t - sigma) sigma)
    (hOQII1 : ∀ k t m, IntervalIntegrable (fun s => s * Q m k s) volume (r + t - sigma) sigma)
    (hLlo : ∀ m, IntervalIntegrable
      (fun s => Q m i s * matBaxterPsi Po Pc sigma m j (r - s)) volume lam (r - sigma))
    (hLhi : ∀ m, IntervalIntegrable
      (fun s => Q m i s * matBaxterPsi Po Pc sigma m j (r - s)) volume (r - sigma) sigma)
    (hLQII : ∀ m, IntervalIntegrable (Q m i) volume (r - sigma) sigma)
    (hLQII1 : ∀ m, IntervalIntegrable (fun s => s * Q m i s) volume (r - sigma) sigma) :
    matBaxterUQmSymFullExt (matBaxterPsi Po Pc sigma) Q i j r
      = (-r - ∑ m, ((∫ w in sigma..(r - lam), Q m i (r - w) * Po m j w)
            + ((∫ s in (r - sigma)..sigma, s * Q m i s)
                - r * ∫ s in (r - sigma)..sigma, Q m i s)))
        - ∑ k, ((∫ t in lam..(sigma + lam - r),
                Q i k t * ((r + t) * ((∑ l, ∫ s, Q l k s) - 1) - ∑ l, ∫ s, s * Q l k s))
            + ∫ t in (sigma + lam - r)..(sigma - r),
                Q i k t * (-(r + t)
                  - ∑ m, ((∫ w in sigma..(r + t - lam), Q m k (r + t - w) * Po m j w)
                    + ((∫ s in (r + t - sigma)..sigma, s * Q m k s)
                        - (r + t) * ∫ s in (r + t - sigma)..sigma, Q m k s)))) := by
  rw [matBaxterUQmSymFullExt_fully_explicit_intermediateLead (matBaxterPsi Po Pc sigma) Q sigma lam
      hlam hlamsig hsl hUtouter hQlam hQ0 hQ1 hQsupp hcore hrlo hrhi i j hint1 hint2 hOlo hOhi
      hOQII hOQII1 hLlo hLhi hLQII hLQII1]
  congr 1
  · congr 1
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [renewalForm_eq_outer Po Pc (Q m i) sigma lam r (by linarith : sigma ≤ r - lam) m j]
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    congr 1
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [Set.uIcc_of_le (by linarith : sigma + lam - r ≤ sigma - r), Set.mem_Icc] at ht
    congr 1
    congr 1
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [renewalForm_eq_outer Po Pc (Q m k) sigma lam (r + t)
      (by linarith [ht.1] : sigma ≤ r + t - lam) m j]

/-! ### Full-line seed → DCF-shell reindex (`hclaimA` in the genuinely-symmetric kernel).
The `[0,σ]`-windowed `correctedSeed_hclaimA` supplies `hclaimA` for the windowed Baxter kernel
(`ρK = Q − matSelfConv`), whose a.e.-symmetry is FALSE at unequal diameters.  These lemmas instead
reindex the FULL-LINE extended seed `matBaxterUQmSymFullExt` (no `[0,σ]` truncation) directly onto
the full-line DCF fold kernel `Ĉ₀ᵢₖ(v) = Qᵢₖ(v) + Qₖᵢ(−v) − (matCorrFull Q)ᵢₖ(v)` — the genuinely
(a.e.) transpose-symmetric object that `matOzStar_of_matDCF_ae` consumes.  The double convolution
reindexes to the full-line correlation `matCorrFull` (`km_reindex`/`dblConvFull_reindex`, Fubini +
`integral_sub_left_eq_self`), giving `matBaxterUQmSymFullExt = Ψ − ∑ₖ ∫_ℝ Ĉ₀·Ψ` and hence the
DCF-shell `hclaimA` `Ψ = r·Φ + ∑ₖ ∫_ℝ Ĉ₀·Ψ` (`correctedSeedExt_hclaimA`). -/

noncomputable def matCorrFull (Q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (i k : Fin N) (v : ℝ) : ℝ :=
  ∑ m, ∫ t, Q i m t * Q k m (t - v)

/-- Per-pair double-convolution reindex: `∫ₜ Qᵢₖ(t)·(∫ₛ Qₘₖ(s)Ψₘⱼ(r+t−s)ds)dt
= ∫ᵥ (∫ₜ Qᵢₖ(t)Qₘₖ(t−v)dt)·Ψₘⱼ(r+v)dv`. -/
theorem km_reindex (Q Psi : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (r : ℝ) (i j k m : Fin N)
    (hfub : Integrable (Function.uncurry fun t v =>
      Q i k t * Q m k (t - v) * Psi m j (r + v)) (volume.prod volume)) :
    (∫ t, Q i k t * ∫ s, Q m k s * Psi m j (r + t - s))
      = ∫ v, (∫ t, Q i k t * Q m k (t - v)) * Psi m j (r + v) := by
  have hinner : ∀ t : ℝ, (∫ s, Q m k s * Psi m j (r + t - s))
      = ∫ v, Q m k (t - v) * Psi m j (r + v) := by
    intro t
    rw [← integral_sub_left_eq_self (fun s => Q m k s * Psi m j (r + t - s)) volume t]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    dsimp only
    rw [show r + t - (t - x) = r + x from by ring]
  simp_rw [hinner]
  have h2 : ∀ t : ℝ, Q i k t * (∫ v, Q m k (t - v) * Psi m j (r + v))
      = ∫ v, Q i k t * Q m k (t - v) * Psi m j (r + v) := by
    intro t
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun v => by ring))
  simp_rw [h2]
  rw [integral_integral_swap hfub]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
  dsimp only
  rw [← integral_mul_const]

theorem dblConvFull_reindex (Q Psi : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (r : ℝ) (i j : Fin N)
    (hI1 : ∀ k m, Integrable (fun t => Q i k t * ∫ s, Q m k s * Psi m j (r + t - s)))
    (hfub : ∀ k m, Integrable (Function.uncurry fun t v =>
      Q i k t * Q m k (t - v) * Psi m j (r + v)) (volume.prod volume))
    (hI2 : ∀ k m, Integrable (fun v => (∫ t, Q i k t * Q m k (t - v)) * Psi m j (r + v))) :
    (∑ k, ∫ t, Q i k t * ∑ m, ∫ s, Q m k s * Psi m j (r + t - s))
      = ∑ m, ∫ v, matCorrFull Q i m v * Psi m j (r + v) := by
  -- Step 1: pull the m-sum out of the t-integral, per k
  have step1 : ∀ k, (∫ t, Q i k t * ∑ m, ∫ s, Q m k s * Psi m j (r + t - s))
      = ∑ m, ∫ t, Q i k t * ∫ s, Q m k s * Psi m j (r + t - s) := by
    intro k
    rw [← integral_finset_sum _ (fun m _ => hI1 k m)]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
    dsimp only
    rw [Finset.mul_sum]
  simp_rw [step1]
  -- Step 2: swap the k, m sums
  rw [Finset.sum_comm]
  -- Step 3+4: km_reindex per pair, then pull k-sum into the v-integral
  refine Finset.sum_congr rfl (fun m _ => ?_)
  have step3 : ∀ k, (∫ t, Q i k t * ∫ s, Q m k s * Psi m j (r + t - s))
      = ∫ v, (∫ t, Q i k t * Q m k (t - v)) * Psi m j (r + v) :=
    fun k => km_reindex Q Psi r i j k m (hfub k m)
  simp_rw [step3]
  rw [← integral_finset_sum _ (fun k _ => hI2 k m)]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
  dsimp only
  rw [matCorrFull, Finset.sum_mul]

/-- **Full-line seed → DCF-shell reindex (separated form).**  The corrected extended seed equals
`Ψᵢⱼ(r)` minus the full-line DCF shell against `Ψ`: the forward Baxter term `Qᵢₖ(v)`, the reflected
term `Qₖᵢ(−v)`, and the full-line correlation `matCorrFull`, each integrated against `Ψₖⱼ(r+v)`. -/
theorem matBaxterUQmSymFullExt_eq_psi_sub_dcfShell_sep (Q Psi : Matrix (Fin N) (Fin N) (ℝ → ℝ))
    (r : ℝ) (i j : Fin N)
    (hB : ∀ k, Integrable (fun t => Q i k t * Psi k j (r + t)))
    (hI1 : ∀ k m, Integrable (fun t => Q i k t * ∫ s, Q m k s * Psi m j (r + t - s)))
    (hfub : ∀ k m, Integrable (Function.uncurry fun t v =>
      Q i k t * Q m k (t - v) * Psi m j (r + v)) (volume.prod volume))
    (hI2 : ∀ k m, Integrable (fun v => (∫ t, Q i k t * Q m k (t - v)) * Psi m j (r + v))) :
    matBaxterUQmSymFullExt Psi Q i j r
      = Psi i j r
        - (∑ k, ∫ v, Q i k v * Psi k j (r + v))
        - (∑ k, ∫ v, Q k i (-v) * Psi k j (r + v))
        + ∑ k, ∫ v, matCorrFull Q i k v * Psi k j (r + v) := by
  have hCk : ∀ k, Integrable (fun t => Q i k t * ∑ m, ∫ s, Q m k s * Psi m j (r + t - s)) := by
    intro k
    have he : (fun t => Q i k t * ∑ m, ∫ s, Q m k s * Psi m j (r + t - s))
        = fun t => ∑ m, Q i k t * ∫ s, Q m k s * Psi m j (r + t - s) := by
      funext t; rw [Finset.mul_sum]
    rw [he]; exact integrable_finset_sum _ (fun m _ => hI1 k m)
  -- Term A reindex
  have hTA : (∑ m, ∫ s, Q m i s * Psi m j (r - s)) = ∑ k, ∫ v, Q k i (-v) * Psi k j (r + v) := by
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [← integral_neg_eq_self (fun s => Q m i s * Psi m j (r - s)) volume]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
    dsimp only
    rw [show r - -v = r + v from by ring]
  -- Term C reindex
  have hTC := dblConvFull_reindex Q Psi r i j hI1 hfub hI2
  -- outer split
  have hsplit : (∑ k, ∫ t, Q i k t * (Psi k j (r + t)
        - ∑ m, ∫ s, Q m k s * Psi m j (r + t - s)))
      = (∑ k, ∫ t, Q i k t * Psi k j (r + t))
        - ∑ k, ∫ t, Q i k t * ∑ m, ∫ s, Q m k s * Psi m j (r + t - s) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← integral_sub (hB k) (hCk k)]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
    dsimp only
    rw [mul_sub]
  simp only [matBaxterUQmSymFullExt, matBaxterUtExt]
  rw [hsplit, hTA, hTC]
  ring

/-- The full-line **DCF fold kernel** `Ĉ₀ᵢₖ(v) = Qᵢₖ(v) + Qₖᵢ(−v) − (matCorrFull Q)ᵢₖ(v)` — the
real-space image of `1 − Q̂₀(k)Q̂₀ᵀ(−k)` function part (forward + reflected linear − correlation),
the genuinely (a.e.) transpose-symmetric object (`Ĉ₀ᵢₖ(v) = Ĉ₀ₖᵢ(v)` a.e.). -/
noncomputable def matDCFfoldKernel (Q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (i k : Fin N) (v : ℝ) : ℝ :=
  Q i k v + Q k i (-v) - matCorrFull Q i k v

/-- **Full-line seed → DCF-shell reindex (combined form).**  `matBaxterUQmSymFullExtᵢⱼ(r) = Ψᵢⱼ(r)
− ∑ₖ ∫_ℝ Ĉ₀ᵢₖ(v)·Ψₖⱼ(r+v) dv` — the corrected extended seed is `Ψ` minus the full-line DCF shell
against `Ψ`.  The DCF-kernel analog of `matBaxterUQmSymFull_eq_psi_sub_rawShell`. -/
theorem matBaxterUQmSymFullExt_eq_psi_sub_dcfShell (Q Psi : Matrix (Fin N) (Fin N) (ℝ → ℝ))
    (r : ℝ) (i j : Fin N)
    (hB : ∀ k, Integrable (fun t => Q i k t * Psi k j (r + t)))
    (hA : ∀ k, Integrable (fun v => Q k i (-v) * Psi k j (r + v)))
    (hC : ∀ k, Integrable (fun v => matCorrFull Q i k v * Psi k j (r + v)))
    (hI1 : ∀ k m, Integrable (fun t => Q i k t * ∫ s, Q m k s * Psi m j (r + t - s)))
    (hfub : ∀ k m, Integrable (Function.uncurry fun t v =>
      Q i k t * Q m k (t - v) * Psi m j (r + v)) (volume.prod volume))
    (hI2 : ∀ k m, Integrable (fun v => (∫ t, Q i k t * Q m k (t - v)) * Psi m j (r + v))) :
    matBaxterUQmSymFullExt Psi Q i j r
      = Psi i j r - ∑ k, ∫ v, matDCFfoldKernel Q i k v * Psi k j (r + v) := by
  rw [matBaxterUQmSymFullExt_eq_psi_sub_dcfShell_sep Q Psi r i j hB hI1 hfub hI2]
  have hmerge : (∑ k, ∫ v, matDCFfoldKernel Q i k v * Psi k j (r + v))
      = (∑ k, ∫ v, Q i k v * Psi k j (r + v))
        + (∑ k, ∫ v, Q k i (-v) * Psi k j (r + v))
        - ∑ k, ∫ v, matCorrFull Q i k v * Psi k j (r + v) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have e1 : (∫ v, Q i k v * Psi k j (r + v)) + (∫ v, Q k i (-v) * Psi k j (r + v))
        = ∫ v, (Q i k v * Psi k j (r + v) + Q k i (-v) * Psi k j (r + v)) :=
      (integral_add (hB k) (hA k)).symm
    have e2 : (∫ v, (Q i k v * Psi k j (r + v) + Q k i (-v) * Psi k j (r + v)))
          - (∫ v, matCorrFull Q i k v * Psi k j (r + v))
        = ∫ v, (Q i k v * Psi k j (r + v) + Q k i (-v) * Psi k j (r + v)
            - matCorrFull Q i k v * Psi k j (r + v)) :=
      (integral_sub ((hB k).add (hA k)) (hC k)).symm
    rw [e1, e2]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
    simp only [matDCFfoldKernel]; ring
  rw [hmerge]; ring

/-- **The corrected extended seed's `hclaimA` (full-line DCF-shell form).**  Combining the extended
seed identity `matBaxterUQmSymFullExt ≡ r·Φ` (`matBaxterUQmSymFullExt_eq_rPhi_of_seed`) with the
DCF-shell reindex: `Ψᵢⱼ(r) = r·Φᵢⱼ(r) + ∑ₖ ∫_ℝ Ĉ₀ᵢₖ(v)·Ψₖⱼ(r+v) dv` — the OZ-renewal `hclaimA`
shape expressed in the genuinely (a.e.) symmetric full-line DCF kernel `matDCFfoldKernel`, replacing
the windowed (non-symmetric) `matSelfConv` kernel of `correctedSeed_hclaimA`. -/
theorem correctedSeedExt_hclaimA (Q Psi Phi : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma lam : ℝ)
    (hlam : lam ≤ 0) (i j : Fin N) {r : ℝ} (hr : 0 < r)
    (hUtouter : ∀ i j r, sigma ≤ r → matBaxterUtExt Psi Q i j r = 0)
    (hQlam : ∀ i k t, t < lam → Q i k t = 0)
    (hPhiOuter : ∀ i j r, sigma ≤ r → Phi i j r = 0)
    (hseed : ∀ (i j : Fin N), ∀ r ∈ Set.Ioo (0 : ℝ) (sigma - lam),
      matBaxterUtExt Psi Q i j r
        - ∑ k, ∫ t in lam..(sigma - r), Q i k t * matBaxterUtExt Psi Q k j (r + t)
      = r * Phi i j r)
    (hB : ∀ k, Integrable (fun t => Q i k t * Psi k j (r + t)))
    (hA : ∀ k, Integrable (fun v => Q k i (-v) * Psi k j (r + v)))
    (hC : ∀ k, Integrable (fun v => matCorrFull Q i k v * Psi k j (r + v)))
    (hI1 : ∀ k m, Integrable (fun t => Q i k t * ∫ s, Q m k s * Psi m j (r + t - s)))
    (hfub : ∀ k m, Integrable (Function.uncurry fun t v =>
      Q i k t * Q m k (t - v) * Psi m j (r + v)) (volume.prod volume))
    (hI2 : ∀ k m, Integrable (fun v => (∫ t, Q i k t * Q m k (t - v)) * Psi m j (r + v))) :
    Psi i j r = r * Phi i j r
      + ∑ k, ∫ v, matDCFfoldKernel Q i k v * Psi k j (r + v) := by
  have h1 := matBaxterUQmSymFullExt_eq_rPhi_of_seed Psi Q Phi sigma lam hlam hUtouter hQlam
    hPhiOuter hseed hr i j
  have h2 := matBaxterUQmSymFullExt_eq_psi_sub_dcfShell Q Psi r i j hB hA hC hI1 hfub hI2
  rw [h2] at h1
  linarith

/-! ### Fold-repackage: the full-line DCF shell = `matShellConvAsym (Ĉ₀/ρ) (Ĉ₀/ρ)ᵀ (Ψ/·)`.
`correctedSeedExt_hclaimA` gives the `hclaimA` as `Ψ − ∑ₖ ∫_ℝ Ĉ₀·Ψ` (raw full-line shell); these
repackage that into the `[0,σ]`-two-arm/`oddExt` `matShellConvAsym` form `matOzStar_of_matDCF_ae`
consumes.  The DCF fold kernel is transpose-odd (`matDCFfoldKernel_transpose_odd`, unconditional),
so for a compactly-supported `Ĉ₀` the `∫_ℝ` splits at `0` into the forward (`r+u`) and reflected
(`r−u`) arms (`matDCFfold_to_twoArm`), matching `matShellConvAsym_transpose_raw` under `ρ·(Ĉ₀/ρ)`
(`dcfShell_eq_rho_matShellConvAsym`).  Capstone `correctedSeedExt_hclaimA_matShellConvAsym`. -/

/-- `matCorrFull` is transpose-odd: `(matCorrFull Q)ᵢₖ(−v) = (matCorrFull Q)ₖᵢ(v)` — the correlation
`∑ₘ∫ Qᵢₘ(t)Qₖₘ(t−v)` under `v ↦ −v` is a shift `t ↦ t+v` swapping the two factors' roles. -/
theorem matCorrFull_neg_swap (Q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (i k : Fin N) (v : ℝ) :
    matCorrFull Q i k (-v) = matCorrFull Q k i v := by
  simp only [matCorrFull]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [← integral_add_right_eq_self (fun x => Q k m x * Q i m (x - v)) v]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
  dsimp only
  rw [show t - -v = t + v from by ring, show t + v - v = t from by ring, mul_comm]

/-- The DCF fold kernel is **transpose-odd** — `Ĉ₀ᵢₖ(−v) = Ĉ₀ₖᵢ(v)` unconditionally (fwd↔refl
linear swap + `matCorrFull_neg_swap`).  This is the a.e.-symmetry hook: transpose-odd + a.e.
symmetric ⟹ even, exactly the fold OZ★ needs. -/
theorem matDCFfoldKernel_transpose_odd (Q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (i k : Fin N) (v : ℝ) :
    matDCFfoldKernel Q i k (-v) = matDCFfoldKernel Q k i v := by
  simp only [matDCFfoldKernel, matCorrFull_neg_swap, neg_neg]
  ring

/-- **The fold — full-line DCF shell folds to the `[0,σ]` two-arm form.**  For a DCF fold kernel
`Ĉ₀ᵢₖ` compactly supported in `[−σ,σ]`, `∫_ℝ Ĉ₀ᵢₖ(v)·Ψₖⱼ(r+v) dv = ∫₀^σ Ĉ₀ᵢₖ(u)·Ψₖⱼ(r+u) du +
∫₀^σ Ĉ₀ₖᵢ(u)·Ψₖⱼ(r−u) du`: split at `0`, the `v < 0` half maps to the reflected `r−u` arm by
`u ↦ −v` with `Ĉ₀ᵢₖ(−u) = Ĉ₀ₖᵢ(u)` (transpose-odd). -/
theorem matDCFfold_to_twoArm (Q Psi : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma r : ℝ)
    (hsig : 0 ≤ sigma) (i k j : Fin N)
    (hint : Integrable (fun v => matDCFfoldKernel Q i k v * Psi k j (r + v)))
    (hsupp : ∀ v, sigma < |v| → matDCFfoldKernel Q i k v = 0) :
    (∫ v, matDCFfoldKernel Q i k v * Psi k j (r + v))
      = (∫ u in (0:ℝ)..sigma, matDCFfoldKernel Q i k u * Psi k j (r + u))
        + ∫ u in (0:ℝ)..sigma, matDCFfoldKernel Q k i u * Psi k j (r - u) := by
  have hfz : ∀ v, v ∉ Set.Icc (-sigma) sigma →
      matDCFfoldKernel Q i k v * Psi k j (r + v) = 0 := by
    intro v hv
    have hσv : sigma < |v| := by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hv
      rcases hv with h | h
      · rw [abs_of_neg (by linarith : v < 0)]; linarith
      · rw [abs_of_pos (by linarith : (0:ℝ) < v)]; linarith
    rw [hsupp v hσv, zero_mul]
  have hfull : (∫ v, matDCFfoldKernel Q i k v * Psi k j (r + v))
      = ∫ v in (-sigma)..sigma, matDCFfoldKernel Q i k v * Psi k j (r + v) := by
    rw [intervalIntegral.integral_of_le (by linarith : -sigma ≤ sigma),
      ← MeasureTheory.integral_Icc_eq_integral_Ioc,
      setIntegral_eq_integral_of_forall_compl_eq_zero hfz]
  rw [hfull, ← intervalIntegral.integral_add_adjacent_intervals
      (b := (0:ℝ)) hint.intervalIntegrable hint.intervalIntegrable, add_comm]
  congr 1
  have hcn := intervalIntegral.integral_comp_neg (a := (0:ℝ)) (b := sigma)
    (fun v => matDCFfoldKernel Q i k v * Psi k j (r + v))
  rw [neg_zero] at hcn
  rw [← hcn]
  refine intervalIntegral.integral_congr (fun u _ => ?_)
  rw [matDCFfoldKernel_transpose_odd, show r + -u = r - u from by ring]

/-- **Fold-repackage — the full-line DCF shell IS `ρ·matShellConvAsym` of `Ĉ₀/ρ`.**  Assembling the
per-`k` fold (`matDCFfold_to_twoArm`) with the `oddExt`/raw bridge `matShellConvAsym_transpose_raw`:
`∑ₖ ∫_ℝ Ĉ₀ᵢₖ(v)·Ψₖⱼ(r+v) dv = ρ·matShellConvAsym (Ĉ₀/ρ) (Ĉ₀/ρ)ᵀ (Ψ/·)ᵢⱼ(r)` — exactly the shell
term `matOzStar_of_matDCF_ae` consumes, with `Kmat = Ĉ₀/ρ`. -/
theorem dcfShell_eq_rho_matShellConvAsym (Q Psi : Matrix (Fin N) (Fin N) (ℝ → ℝ))
    (rho sigma r : ℝ) (hsig : 0 ≤ sigma) (hrho : rho ≠ 0) (i j : Fin N)
    (hodd : ∀ k, (∀ x, Psi k j (-x) = -Psi k j x) ∧ Psi k j 0 = 0)
    (hint : ∀ k, Integrable (fun v => matDCFfoldKernel Q i k v * Psi k j (r + v)))
    (hsupp : ∀ k v, sigma < |v| → matDCFfoldKernel Q i k v = 0)
    (hIfwd : ∀ k, IntervalIntegrable
      (fun u => matDCFfoldKernel Q i k u * Psi k j (r + u)) volume 0 sigma)
    (hIbwd : ∀ k, IntervalIntegrable
      (fun u => matDCFfoldKernel Q k i u * Psi k j (r - u)) volume 0 sigma) :
    (∑ k, ∫ v, matDCFfoldKernel Q i k v * Psi k j (r + v))
      = rho * matShellConvAsym (fun a b u => matDCFfoldKernel Q a b u / rho)
          (fun a b u => matDCFfoldKernel Q b a u / rho)
          (fun k l => fun x => Psi k l x / x) sigma r i j := by
  rw [matShellConvAsym_transpose_raw (fun a b u => matDCFfoldKernel Q a b u / rho) Psi sigma r i j
      hodd, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [matDCFfold_to_twoArm Q Psi sigma r hsig i k j (hint k) (hsupp k),
    ← intervalIntegral.integral_add (hIfwd k) (hIbwd k),
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun u _ => ?_)
  show matDCFfoldKernel Q i k u * Psi k j (r + u) + matDCFfoldKernel Q k i u * Psi k j (r - u)
      = rho * (matDCFfoldKernel Q i k u / rho * Psi k j (r + u)
          + matDCFfoldKernel Q k i u / rho * Psi k j (r - u))
  field_simp

/-- **The extended seed's `hclaimA` in `matShellConvAsym` form (the `matOzStar_of_matDCF_ae`
input).**  Chaining `correctedSeedExt_hclaimA` (seed `≡ r·Φ` + DCF reindex) with the fold-repackage
`dcfShell_eq_rho_matShellConvAsym`: `Ψᵢⱼ(r) = r·Φᵢⱼ(r) + ρ·matShellConvAsym (Ĉ₀/ρ) (Ĉ₀/ρ)ᵀ (Ψ/·)`
— EXACTLY the `hclaimA` `matOzStar_of_matDCF_ae` consumes, with `Kmat = Ĉ₀/ρ = matDCFfoldKernel Q/ρ`
the genuinely (a.e.) transpose-symmetric DCF kernel.  Only the physical identification
`matDCFfoldKernel Q = matDCFreCore` (for `Q = q0MixEntry`) then remains. -/
theorem correctedSeedExt_hclaimA_matShellConvAsym (Q Psi Phi : Matrix (Fin N) (Fin N) (ℝ → ℝ))
    (rho sigma lam : ℝ) (hlam : lam ≤ 0) (hsig : 0 ≤ sigma) (hrho : rho ≠ 0)
    (i j : Fin N) {r : ℝ} (hr : 0 < r)
    (hUtouter : ∀ i j r, sigma ≤ r → matBaxterUtExt Psi Q i j r = 0)
    (hQlam : ∀ i k t, t < lam → Q i k t = 0)
    (hPhiOuter : ∀ i j r, sigma ≤ r → Phi i j r = 0)
    (hseed : ∀ (i j : Fin N), ∀ r ∈ Set.Ioo (0 : ℝ) (sigma - lam),
      matBaxterUtExt Psi Q i j r
        - ∑ k, ∫ t in lam..(sigma - r), Q i k t * matBaxterUtExt Psi Q k j (r + t)
      = r * Phi i j r)
    (hB : ∀ k, Integrable (fun t => Q i k t * Psi k j (r + t)))
    (hA : ∀ k, Integrable (fun v => Q k i (-v) * Psi k j (r + v)))
    (hC : ∀ k, Integrable (fun v => matCorrFull Q i k v * Psi k j (r + v)))
    (hI1 : ∀ k m, Integrable (fun t => Q i k t * ∫ s, Q m k s * Psi m j (r + t - s)))
    (hfub : ∀ k m, Integrable (Function.uncurry fun t v =>
      Q i k t * Q m k (t - v) * Psi m j (r + v)) (volume.prod volume))
    (hI2 : ∀ k m, Integrable (fun v => (∫ t, Q i k t * Q m k (t - v)) * Psi m j (r + v)))
    (hodd : ∀ k, (∀ x, Psi k j (-x) = -Psi k j x) ∧ Psi k j 0 = 0)
    (hint : ∀ k, Integrable (fun v => matDCFfoldKernel Q i k v * Psi k j (r + v)))
    (hsupp : ∀ k v, sigma < |v| → matDCFfoldKernel Q i k v = 0)
    (hIfwd : ∀ k, IntervalIntegrable
      (fun u => matDCFfoldKernel Q i k u * Psi k j (r + u)) volume 0 sigma)
    (hIbwd : ∀ k, IntervalIntegrable
      (fun u => matDCFfoldKernel Q k i u * Psi k j (r - u)) volume 0 sigma) :
    Psi i j r = r * Phi i j r
      + rho * matShellConvAsym (fun a b u => matDCFfoldKernel Q a b u / rho)
          (fun a b u => matDCFfoldKernel Q b a u / rho)
          (fun k l => fun x => Psi k l x / x) sigma r i j := by
  rw [correctedSeedExt_hclaimA Q Psi Phi sigma lam hlam i j hr hUtouter hQlam hPhiOuter hseed
      hB hA hC hI1 hfub hI2,
    dcfShell_eq_rho_matShellConvAsym Q Psi rho sigma r hsig hrho i j hodd hint hsupp hIfwd hIbwd]

/-! ### The general-N mixture DCF from the renewal seed (`= c_HS` at equal diameters)

The correct general-N hard-sphere-mixture DCF is the shell-kernel inverse of the renewal seed
`matBaxterUQmSymFullExt` (the fully-corrected, full-line `= r·Φ` object), NOT the odd part of the
naive self-convolution `MixtureHSDCF.c_HS_mix` — which is DEGENERATE on the diagonal
(`c_HS_mix_diag_eq_zero`) and, for unequal diameters, is not even symmetric.  `cHSmixRenewal` below
packages this correct object; it equals the scalar `c_HS` at equal diameters (grounded in the proved
scalar `baxter_core_seed`) and vanishes outside the core.  Its explicit UNEQUAL-diameter value is
the classical Lebowitz mixture result — the acknowledged open numerical residual, which the
axiom-free `matOzStar_unique` route makes unnecessary for MML.8. -/

open FMSA.HardSphere in
/-- **General-N mixture hard-sphere DCF (renewal-seed form)** — `c^HS_ij(r) := r⁻¹ ·
matBaxterUQmSymFullExt Psi Q i j r`.  The renewal seed is the shell-kernel `= r·Φ` object; dividing
by `r` gives the DCF.  This is the CORRECT N-species object — unlike the degenerate odd-extraction
`MixtureHSDCF.c_HS_mix` — with the scalar `c_HS` as its equal-diameter specialization. -/
noncomputable def cHSmixRenewal (Psi Q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (i j : Fin N)
    (r : ℝ) : ℝ :=
  matBaxterUQmSymFullExt Psi Q i j r / r

open FMSA.HardSphere in
/-- **⭐ Equal-diameter reduction — the renewal-seed mixture DCF IS the scalar `c_HS`.**  From
`matBaxterUQmSymFullExt_eq_rcHS_of_equalDiam` (`= r·c_HS`, grounded in `baxter_core_seed`), dividing
by `r > 0`: at equal diameters the general-N mixture DCF collapses to the one-component PY
`c_HS(η)`.  This is the correct N-species analog the disproved `c_HS_mix` diagonal failed to
provide. -/
theorem cHSmixRenewal_eq_cHS_of_equalDiam
    (Psi Q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) {eta sigma rho : ℝ}
    (hsigma : 0 < sigma) (heta : eta < 1) (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6)
    (hQsupp : ∀ i k t, t < 0 ∨ sigma < t → Q i k t = 0)
    (hsym : ∀ i j, Q i j = Q j i)
    (hUouter : ∀ i j r, sigma ≤ r → matBaxterU Psi Q sigma i j r = 0)
    (hint : ∀ (i j k : Fin N) (r : ℝ), IntervalIntegrable
      (fun t => Q i k t * matBaxterU Psi Q sigma k j (r + t)) volume 0 sigma)
    (hrow : ∀ (i : Fin N) (u : ℝ), u ∈ Set.Icc (0:ℝ) sigma → ∑ k, Q i k u = q0_poly eta sigma rho u)
    (hQ0 : ∀ i k, IntervalIntegrable (Q i k) volume 0 sigma)
    (hQ1 : ∀ i k, IntervalIntegrable (fun t => t * Q i k t) volume 0 sigma)
    (hcore : ∀ (k j : Fin N) (v : ℝ), v ∈ Set.Ioo (-sigma) sigma → Psi k j v = -v)
    {r : ℝ} (hr : 0 < r) (i j : Fin N) :
    cHSmixRenewal Psi Q i j r = c_HS eta sigma r := by
  rw [cHSmixRenewal, matBaxterUQmSymFullExt_eq_rcHS_of_equalDiam Psi Q hsigma heta heta_def
    hQsupp hsym hUouter hint hrow hQ0 hQ1 hcore hr i j,
    mul_comm r (c_HS eta sigma r), mul_div_assoc, div_self (ne_of_gt hr), mul_one]

/-- **Outer vanishing** — the renewal-seed mixture DCF is `0` for `r ≥ σ − λ` (from the seed's
`matBaxterUQmSymFullExt_zero_outer`): the DCF is supported inside the core. -/
theorem cHSmixRenewal_zero_outer (Psi Q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma lam : ℝ)
    (hlam : lam ≤ 0)
    (hUtouter : ∀ i j r, sigma ≤ r → matBaxterUtExt Psi Q i j r = 0)
    (hQlam : ∀ i k t, t < lam → Q i k t = 0)
    {r : ℝ} (hr : sigma - lam ≤ r) (i j : Fin N) :
    cHSmixRenewal Psi Q i j r = 0 := by
  rw [cHSmixRenewal, matBaxterUQmSymFullExt_zero_outer Psi Q sigma lam hlam hUtouter hQlam hr i j,
    zero_div]

/-! ## The corrected-seed route to MML.8 — complete end-to-end summary

Together with `MixtureDCFAEInjective.lean`, `MixtureOzStar.lean`, `MixturePoleExhaustion.lean` and
`MixtureRDFUniqueness.lean`, this file assembles the **real-space seed route** to the
unequal-diameter mixture RDF identity `matBaxterUQmSymFullExt = r·Φ` (MML.8).  Steps are std-3.

**The chain (obstruction → resolution).**
1. `matDCF_ae_symm` — a.e.-symmetry of the full-line DCF (dissolves obstruction (b)) via Fourier
   a.e.-injectivity.
2. corrected seed `matBaxterUt = matBaxterU` at `Qᵀ` (rfl) — transposes the first convolution,
   dissolving "the seed changes the renewal".
3. `Qphys_prod_eq_one_sub_dcf_transform` — the momentum linchpin `Q̂₀·Q̂₀ᵀ = 1 − 𝓛[matDCFfull]`.
4. `laplace_shift`/`foldShell_laplace` (convolution theorem) and `matDCFfull_shell_laplace` (the
   symbol identity) close the windowed↔full-line gap at the transform level.
5. `matBaxterUExt`/`matBaxterUtExt` — the full-line extension;
   `matBaxterUExt_eq_matBaxterU_sub_tail` makes the `[λ,0)` sub-zero tail (the unequal-diameter
   content) explicit.
6. `matBaxterUtExt_core` (core moments), `matBaxterUtExt_intermediate_closed` (intermediate),
   claim `(A)` (`matBaxterUtExt = 0` outer, from the renewal) — the THREE-REGION closed form of the
   first convolution: every term a `Q`-moment or a `Ψouter` integral.
7. `matBaxterUQmSymFullExt_core_reduce` → `_conv_boundary_split` → `_conv_moment_part` →
   `_core_assembled`, then `_conv_outer_part_closed` + `_core_fully_explicit` +
   `_fully_explicit_momentLead`/`_intermediateLead` — the second convolution assembled and every
   `matBaxterUtExt` substituted, giving the seed with ZERO symbolic `matBaxterUtExt`: an explicit
   expression in `Q` and the constructed `matBaxterPsiOuter`.
8. `matRenewalConv_eq_sub`/`matRenewal_contact` (read-out), `renewalForm_peel_subzero_tail`/
   `subzero_tail_eq`/`matRenewalForm_readout_add_tail` (sub-zero-tail alignment),
   `renewalForm_eq_outer`/`matBaxterUtExt_intermediate_closed_outer` — pin the `Ψouter` coupling to
   the constructed Banach–Volterra solution `matBaxterPsiOuter` (built, with read-out algebra).

**The terminus — the Wertheim–Thiele numerical identity `= r·Φ`.**
`matBaxterUQmSymFullExt_eq_rPhi_of_seed` reduces the whole `= r·Φ` to one `hseed` (the WT identity,
LHS now fully explicit).  At EQUAL diameters `matBaxterUQmSymFullExt_eq_rcHS_of_equalDiam` proves
`= r·c_HS` OUTRIGHT (grounded in the proved scalar `baxter_core_seed`).  At UNEQUAL diameters the
identity is the classical Lebowitz `c_HS_mix` result, numerically confirmed to `<1e-3`
(`mixwt_lebowitz_check.py`; exact Lebowitz coeffs, `Ψouter` = renewal Picard, claim A ~1e-8).

**Two routes, and the pole-exhaustion dead end.**
The seed route is one of TWO routes to MML.8.  The **non-circular value route** `matOzStar_unique`
(`MixtureRDFUniqueness.lean`) discharges MML.8 axiom-free from the coercive structure factor
`det Q̂₀ ≠ 0` (`mixtureDet_pole_free_N` + `pyhs_mixture_no_spinodal`) — no seed, no poles.
The LITERAL pole-series route is provably BLOCKED: `even_subfamily_not_exhaustive`
(`MixturePoleExhaustion.lean`) shows `MZERO.1` infinitude can never yield the pole-exhaustion the
collapse needs, so `MixRDFInnerCollapse` stays a `Prop`.

**Status.** Every structural step is axiom-clean; the equal-diameter WT identity is proved; the
unequal-diameter WT identity is numerically confirmed and its `Ψouter` coupling pinned to a
constructed object; and MML.8 is discharged by the axiom-free `matOzStar_unique` regardless. -/

end FMSA.MixtureOzStar
