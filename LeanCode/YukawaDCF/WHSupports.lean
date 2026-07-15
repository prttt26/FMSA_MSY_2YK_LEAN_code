/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HardSphere.BaxterRealSpace
import LeanCode.YukawaDCF.InnerDecomp
import LeanCode.HardSphere.Splitting

/-!
# Task Y1.3a — Wiener–Hopf support lemmas ([LN] §6.3.2, Eq. 55–57)

The Wiener–Hopf isolation of the causal part `B₁ = {T_U}^{[R,∞)}` ([LN] §6.3, the analytic heart of
Group Y1 = the concrete-C.5 derivation) rests on real-space **support** facts: the Baxter factor is
compactly supported inside the core, `h^{(1)}` vanishes in the hard core, and the inner DCF `S₁` is
core-supported.  This file records the *atomic* support statements and the
half-line ⇄ full-line transform bridges.  The **combination** of these (support-orthogonality / FT
injectivity, i.e. that `L = Q̂₀ᵀ Ĥ₁ Q̂₀` is `[R,∞)`-supported by a convolution-of-supports argument)
is the hard core Y1.3b, deferred.

Following the codebase's method (Group 3 `Splitting.lean`, Group BAXTER) the split is done
algebraically via support statements + residues — **not** via the Hilbert transform / Cauchy P.V. of
[LN] §6.3's literal presentation (Mathlib lacks that machinery).

## Results

* `q0_poly_support_subset` — packages `FMSA.HardSphere.q0_poly_outer` as a support containment:
  the monodisperse real-space Baxter factor has `Function.support ⊆ Set.Iic σ`.
* `q0MixEntry` / `q0MixEntry_support_subset` — the mixture real-space Baxter entry `{Q̂₀(r)}_{ij}`
  ([LN] Eq. 10), the Baxter polynomial windowed on the core `[λ_{ij}, R_{ij}]` (built from the
  `FMSA.InnerDecomp.Mix` data `R`/`lam`/`Q0`/`Qpp`), with `Function.support ⊆ Set.Icc λ_{ij} R_{ij}`
  ([LN] Eq. 56).
* `integral_Iic_eq_of_support` / `integral_Ici_eq_of_support` — reusable core: a function supported
  on a half-line integrates the same over that half-line as over all of `ℝ`.
* `fourier_Iic_eq_full` (anti-causal, inner `S₁` side) / `fourier_Ici_eq_full` (causal, outer
  `h^{(1)}` side) — the half-line Fourier integral equals the full-line one, for an integrand
  `f·e^{−ikr}` whose amplitude `f` is half-line-supported.  The `Set.Iic`/`Set.Ici` analogues of
  `Splitting.lean`'s `T_S_eq_fourier_of_innerCore` (`[0,R]` case).

Status: ✓ DONE (Y1.3a), axiom-clean.  Y1.3b (FT injectivity on disjoint supports) deferred.
-/

set_option linter.style.longLine false

open MeasureTheory Set

namespace FMSA.WHSupports

open FMSA.InnerDecomp

variable {N M : ℕ}

/-! ### 1. Real-space Baxter support ([LN] Eq. 56) -/

/-- **Monodisperse anchor.**  The real-space Baxter polynomial factor `q̃₀(r)`
(`FMSA.HardSphere.q0_poly`) is supported inside the core: `Function.support ⊆ Set.Iic σ`.  Repackages
`FMSA.HardSphere.q0_poly_outer` (`q̃₀(r) = 0` for `r > σ`) as a support containment. -/
theorem q0_poly_support_subset (eta sigma rho : ℝ) :
    Function.support (FMSA.HardSphere.q0_poly eta sigma rho) ⊆ Set.Iic sigma := by
  intro x hx
  rw [Function.mem_support] at hx
  rw [Set.mem_Iic]
  by_contra hns
  exact hx (FMSA.HardSphere.q0_poly_outer (not_le.mp hns))

/-- Real-space mixture Baxter entry `{Q̂₀(r)}_{ij}` ([LN] Eq. 10): the Baxter polynomial
`Q'_{ij}(r−R_{ij}) + Q''_j(r−R_{ij})²/2` windowed on the core `[λ_{ij}, R_{ij}]`, built from the
converged-solution `Mix` data.  (Coefficients enter only as amplitudes; the support statement below
is independent of their values.) -/
noncomputable def q0MixEntry (X : Mix N M) (i j : Fin N) (r : ℝ) : ℝ :=
  Set.indicator (Set.Icc (X.lam i j) (X.R i j))
    (fun r => X.Q0 i j * (r - X.R i j) + X.Qpp j * (r - X.R i j) ^ 2 / 2) r

/-- **[LN] Eq. 56 (mixture).**  The mixture real-space Baxter entry is compactly supported inside the
core: `Function.support (q0MixEntry X i j) ⊆ Set.Icc λ_{ij} R_{ij}`. -/
theorem q0MixEntry_support_subset (X : Mix N M) (i j : Fin N) :
    Function.support (q0MixEntry X i j) ⊆ Set.Icc (X.lam i j) (X.R i j) := by
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hns
  exact hx (Set.indicator_of_notMem hns _)

/-! ### 2. Half-line ⇄ full-line integral bridges (reuse of `Splitting.lean`'s method) -/

/-- A complex function supported on `(−∞, R]` integrates the same over `Set.Iic R` as over `ℝ`. -/
theorem integral_Iic_eq_of_support {g : ℝ → ℂ} {R : ℝ}
    (hsupp : Function.support g ⊆ Set.Iic R) :
    ∫ r in Set.Iic R, g r = ∫ r, g r := by
  rw [← MeasureTheory.integral_indicator measurableSet_Iic, Set.indicator_eq_self.mpr hsupp]

/-- A complex function supported on `[R, ∞)` integrates the same over `Set.Ici R` as over `ℝ`. -/
theorem integral_Ici_eq_of_support {g : ℝ → ℂ} {R : ℝ}
    (hsupp : Function.support g ⊆ Set.Ici R) :
    ∫ r in Set.Ici R, g r = ∫ r, g r := by
  rw [← MeasureTheory.integral_indicator measurableSet_Ici, Set.indicator_eq_self.mpr hsupp]

/-- **Anti-causal (inner `S₁`) side.**  For an amplitude `f` supported on `(−∞, R]`, the half-line
Fourier integral over `Set.Iic R` equals the full-line one.  The `Set.Iic R` analogue of
`FMSA.WienerHopf.T_S_eq_fourier_of_innerCore` (`[0,R]` case). -/
theorem fourier_Iic_eq_full {f : ℝ → ℂ} {R : ℝ} (k : ℝ)
    (hsupp : Function.support f ⊆ Set.Iic R) :
    ∫ r in Set.Iic R, f r * Complex.exp (-Complex.I * k * r)
      = ∫ r, f r * Complex.exp (-Complex.I * k * r) := by
  apply integral_Iic_eq_of_support
  intro x hx
  rw [Function.mem_support] at hx
  refine hsupp ?_
  rw [Function.mem_support]
  exact left_ne_zero_of_mul hx

/-- **Causal (outer `h^{(1)}`) side.**  For an amplitude `f` supported on `[R, ∞)` (the hard-core
vanishing of `h^{(1)}`), the half-line Fourier integral over `Set.Ici R` equals the full-line one. -/
theorem fourier_Ici_eq_full {f : ℝ → ℂ} {R : ℝ} (k : ℝ)
    (hsupp : Function.support f ⊆ Set.Ici R) :
    ∫ r in Set.Ici R, f r * Complex.exp (-Complex.I * k * r)
      = ∫ r, f r * Complex.exp (-Complex.I * k * r) := by
  apply integral_Ici_eq_of_support
  intro x hx
  rw [Function.mem_support] at hx
  refine hsupp ?_
  rw [Function.mem_support]
  exact left_ne_zero_of_mul hx

end FMSA.WHSupports
