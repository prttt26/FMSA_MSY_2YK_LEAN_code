/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HardSphere.BaxterRealSpace
import LeanCode.HardSphere.PYDCF
import LeanCode.HardSphere.RadialLaplace
import LeanCode.HardSphere.RadialFourierCHS
import LeanCode.Analysis.Volterra

/-!
# Task OZFIX.15 — the Wertheim–Thiele core seed (real-space Baxter route)

The **axiom-free** route to `hcollapse`/`oz_core_closure`, and the one place where the Fourier
side's circularity (`OZFIX.14`: the contour is *value-neutral*, so `hcollapse ⟺ core closure`)
does **not** apply. The reason is structural: on the Fourier side the core value must be
*reproduced* by the residue series; in real space it is **definitional** — `oz_operator`'s own
`if r < sigma then -1` branch means `OzFixedPt h → h ≡ -1` inside, so with `ψ(v) := v·h(|v|)`
(odd) we get `ψ(v) = -v` on `(-σ,σ)` for free.

## The route

Writing `φ(v) := v·c_HS(|v|)` (odd, supported `[-σ,σ]`), `Q₊ := δ - q0_poly·1_{[0,σ]}` (so that
`F[Q₊](k) = 1 - Qhat_complex k`), and `Q₋(r) := Q₊(-r)`, the **already-proved**
`baxter_wiener_hopf_complex` (`OZFIX.2`) reads in real space as

  `ψ ⋆ Q₊ ⋆ Q₋ = φ`

(the `Q`-product is `k ↔ -k` symmetric, so there is no convention clash). Put `u := ψ ⋆ Q₊`, i.e.
`u(r) = ψ(r) - ∫₀^σ q0_poly(t)·ψ(r-t)dt`. Then:

* **(A)** `u ≡ 0` on `(σ,∞)` — the renewal / Volterra equation, which *defines* `ψ` outside;
* **(B)** `u(r) = r·(M₀-1) - M₁` on `(0,σ)` — **explicit**, because for `0 < r < σ` and `t ∈ [0,σ]`
  the sample point `r-t` lies in `(-σ,σ)` where `ψ = -v` is definitional. Here
  `M₀ := ∫₀^σ q0_poly`, `M₁ := ∫₀^σ t·q0_poly` (`baxterM0`/`baxterM1` below);
* **(C)** `u ⋆ Q₋ = φ` — with (A)+(B) making `u` fully explicit, this is a **pure polynomial
  identity**. That is `baxter_core_seed`, the content of this file.

(A)+(B)+(C) give `ψ ⋆ Q₊ ⋆ Q₋ = φ`, hence (via the convolution theorem — the project has the
proved 3D-radial `radial_fourier_conv` and its ingredient `sin_triangle_integral`) the OZ equation
for **all** `r > 0`; with `oz_forcing_add_linear_op_eq_radial3d_conv` and `oz_fixed_pt_unique` that
identifies `oz_h` and makes **`oz_core_closure` a theorem** (Phase C). Only `r > 0` needs checking:
`ψ` is odd and `Q₊ ⋆ Q₋` is even (`(Q₊⋆Q₋)(r) = ∫Q₊(s)Q₊(s-r)ds` is symmetric in `r ↔ -r`), so
`ψ ⋆ Q₊ ⋆ Q₋` is odd, as is `φ`. On `(σ,∞)` (C) is trivial (`u = 0` there and `r+t > σ`), so the
whole content sits on `(0,σ)` — this file.

## Verification before formalizing (project discipline)

* Numerically (`ozfix15_realspace_check.py`, scratch; η=0.3, σ=1, 300 Newton-refined poles;
  `q0_poly`/`c_HS` transcribed verbatim from this codebase): **(B)** holds to `3e-16`, **(C)** to
  `5e-15`, and `Qhat_complex(kₙ) = 1` at every pole and mirror to `1e-16`…`1e-13`.
* **Symbolically** (by hand, σ=1, `Δ := (1-η)²`, `P := 1+2η`, `S := 2+η`): under `heta_def`
  (`πρσ³ = 6η`), `α := ρQ′ = 6ηS/Δ`, `β := ρQ″ = 12ηP/Δ`, so `M₀ = η(η-4)/Δ`, `M₁ = -3η/(2Δ)` and
  the key simplification `M₀ - 1 = -P/Δ`. Multiplying (C) by `Δ²` and collecting powers of `r`:
  `r⁰ : (3η/2)(1-η)² + 9η²S/2 - 3η²P - ηPS + ηP²/2 = 0` ✓ (RHS has no `r⁰`);
  `r¹ : P[-(1-η)² - 3ηS + 2ηP] = -P²` ✓;  `r² : 3ηS[P - 3η/2] = 3ηS²/2` ✓;
  `r³ : ηP[S + 3η - 2P] = 0` ✓;  `r⁴ : ηP²(-2 + 3/2) = -ηP²/2` ✓ — all five match, so (C) is an
  identity in `η`, not an η=0.3 coincidence.

## Relation to the rest of the project

`baxter_factorization_inner` (`BaxterRealSpace.lean`) is the **other** half of the same Baxter
pair (the `c ↔ q` relation), already proved by exactly this technique (FTC + `field_simp`/`ring`
under `heta_def`) — so both the technique and its precedent are in hand. `baxter_core_seed` is the
`h`-half, and it is the piece the Fourier route provably cannot supply.

**Status:** ✓ `baxterM0`/`baxterM1` + their moment lemmas + `baxter_core_seed`. Steps (A)/(1) (the
Volterra construction) and the `1D-odd ↔ 3D-radial` bridge remain — see `proof_notes_ozfix.md`
`OZFIX.15`.
-/

open MeasureTheory Set intervalIntegral

namespace FMSA.HardSphere

noncomputable section

/-! ### The two moments of `q0_poly` -/

/-- `M₀ := ∫₀^σ q0_poly = -ρQ′σ²/2 + ρQ″σ³/6`. -/
def baxterM0 (eta sigma rho : ℝ) : ℝ :=
  -(rho * q_prime_py eta sigma * sigma ^ 2 / 2) +
    rho * q_doubleprime_py eta * sigma ^ 3 / 6

/-- `M₁ := ∫₀^σ t·q0_poly(t)dt = -ρQ′σ³/6 + ρQ″σ⁴/24`. -/
def baxterM1 (eta sigma rho : ℝ) : ℝ :=
  -(rho * q_prime_py eta sigma * sigma ^ 3 / 6) +
    rho * q_doubleprime_py eta * sigma ^ 4 / 24

/-- `baxterM0` is the zeroth moment of `q0_poly`. -/
theorem baxterM0_eq {eta sigma rho : ℝ} (hsigma : 0 < sigma) :
    (∫ t in (0:ℝ)..sigma, q0_poly eta sigma rho t) = baxterM0 eta sigma rho := by
  set α := rho * q_prime_py eta sigma with hα_def
  set β := rho * q_doubleprime_py eta with hβ_def
  have hcongr : (∫ t in (0:ℝ)..sigma, q0_poly eta sigma rho t) =
      ∫ t in (0:ℝ)..sigma, (α * (t - sigma) + β * (t - sigma) ^ 2 / 2) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hsigma.le] at ht
    rw [q0_poly_inner ht.2, ← hα_def, ← hβ_def]
  rw [hcongr]
  have hint : IntervalIntegrable (fun t : ℝ => α * (t - sigma) + β * (t - sigma) ^ 2 / 2)
      volume 0 sigma := by
    apply Continuous.intervalIntegrable; fun_prop
  have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) sigma,
      HasDerivAt (fun y : ℝ => α / 2 * (y - sigma) ^ 2 + β / 6 * (y - sigma) ^ 3)
        (α * (x - sigma) + β * (x - sigma) ^ 2 / 2) x := by
    intro x _
    have hin : HasDerivAt (fun y : ℝ => y - sigma) 1 x := by
      have h := (hasDerivAt_id x).sub (hasDerivAt_const x sigma)
      simp only [sub_zero] at h; exact h
    have h2 : HasDerivAt (fun y : ℝ => (y - sigma) ^ 2) (2 * (x - sigma)) x :=
      (hin.pow 2).congr_deriv (by push_cast; ring)
    have h3 : HasDerivAt (fun y : ℝ => (y - sigma) ^ 3) (3 * (x - sigma) ^ 2) x :=
      (hin.pow 3).congr_deriv (by push_cast; ring)
    have hA1 : HasDerivAt (fun y : ℝ => α / 2 * (y - sigma) ^ 2)
        (α / 2 * (2 * (x - sigma))) x := h2.const_mul _
    have hA2 : HasDerivAt (fun y : ℝ => β / 6 * (y - sigma) ^ 3)
        (β / 6 * (3 * (x - sigma) ^ 2)) x := h3.const_mul _
    refine ((hA1.add hA2).congr_of_eventuallyEq ?_).congr_deriv ?_
    · exact Filter.Eventually.of_forall fun y => by simp [Pi.add_apply]
    · ring
  rw [integral_eq_sub_of_hasDerivAt hderiv hint, baxterM0, ← hα_def, ← hβ_def]
  ring

/-- `baxterM1` is the first moment of `q0_poly`. -/
theorem baxterM1_eq {eta sigma rho : ℝ} (hsigma : 0 < sigma) :
    (∫ t in (0:ℝ)..sigma, t * q0_poly eta sigma rho t) = baxterM1 eta sigma rho := by
  set α := rho * q_prime_py eta sigma with hα_def
  set β := rho * q_doubleprime_py eta with hβ_def
  have hcongr : (∫ t in (0:ℝ)..sigma, t * q0_poly eta sigma rho t) =
      ∫ t in (0:ℝ)..sigma, t * (α * (t - sigma) + β * (t - sigma) ^ 2 / 2) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hsigma.le] at ht
    dsimp only []
    rw [q0_poly_inner ht.2, ← hα_def, ← hβ_def]
  rw [hcongr]
  have hint : IntervalIntegrable (fun t : ℝ => t * (α * (t - sigma) + β * (t - sigma) ^ 2 / 2))
      volume 0 sigma := by
    apply Continuous.intervalIntegrable; fun_prop
  have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) sigma,
      HasDerivAt (fun y : ℝ => α / 3 * (y - sigma) ^ 3 + β / 8 * (y - sigma) ^ 4 +
          α * sigma / 2 * (y - sigma) ^ 2 + β * sigma / 6 * (y - sigma) ^ 3)
        (x * (α * (x - sigma) + β * (x - sigma) ^ 2 / 2)) x := by
    intro x _
    have hin : HasDerivAt (fun y : ℝ => y - sigma) 1 x := by
      have h := (hasDerivAt_id x).sub (hasDerivAt_const x sigma)
      simp only [sub_zero] at h; exact h
    have h2 : HasDerivAt (fun y : ℝ => (y - sigma) ^ 2) (2 * (x - sigma)) x :=
      (hin.pow 2).congr_deriv (by push_cast; ring)
    have h3 : HasDerivAt (fun y : ℝ => (y - sigma) ^ 3) (3 * (x - sigma) ^ 2) x :=
      (hin.pow 3).congr_deriv (by push_cast; ring)
    have h4 : HasDerivAt (fun y : ℝ => (y - sigma) ^ 4) (4 * (x - sigma) ^ 3) x :=
      (hin.pow 4).congr_deriv (by push_cast; ring)
    have hA1 : HasDerivAt (fun y : ℝ => α / 3 * (y - sigma) ^ 3)
        (α / 3 * (3 * (x - sigma) ^ 2)) x := h3.const_mul _
    have hA2 : HasDerivAt (fun y : ℝ => β / 8 * (y - sigma) ^ 4)
        (β / 8 * (4 * (x - sigma) ^ 3)) x := h4.const_mul _
    have hA3 : HasDerivAt (fun y : ℝ => α * sigma / 2 * (y - sigma) ^ 2)
        (α * sigma / 2 * (2 * (x - sigma))) x := h2.const_mul _
    have hA4 : HasDerivAt (fun y : ℝ => β * sigma / 6 * (y - sigma) ^ 3)
        (β * sigma / 6 * (3 * (x - sigma) ^ 2)) x := h3.const_mul _
    refine ((((hA1.add hA2).add hA3).add hA4).congr_of_eventuallyEq ?_).congr_deriv ?_
    · exact Filter.Eventually.of_forall fun y => by simp [Pi.add_apply]
    · ring
  rw [integral_eq_sub_of_hasDerivAt hderiv hint, baxterM1, ← hα_def, ← hβ_def]
  ring

/-! ### Claim (A): the Volterra construction of `ψ` on `[σ, ∞)` (MA.10 instantiated)

The renewal equation `ψ(r) = ∫₀^σ q0(t)·ψ(r-t) dt` becomes, after `s := r - t`,
`ψ(r) = ∫_{r-σ}^{r} q0(r-s)·ψ(s) ds`.  Because `q0` is supported in `[0,σ]` (`q0_poly_outer`),
`q0(r-s) = 0` whenever `s < r-σ`, so the *core* contribution can be written **uniformly** as
`∫₀^σ q0(r-s)·(-s) ds` (the samples with `s < r-σ` silently contribute `0`), and the equation takes
exactly `MA.10`'s convolution/renewal shape

  `ψ(r) = baxterForcing(r) + ∫_σ^r q0(r-s)·ψ(s) ds`   on `[σ, b]`.
-/

/-- The forcing that the *core* values `ψ = -s` on `(0,σ)` feed into the renewal equation:
`g(r) := ∫₀^σ q0(r-s)·(-s) ds`.  Uniform in `r`: for `r ≥ 2σ` every sample has `r - s ≥ σ`, so
`q0(r-s) = 0` and `g` vanishes identically — which is exactly claim (A)'s "`u ≡ 0` beyond `2σ`". -/
noncomputable def baxterForcing (eta sigma rho : ℝ) (r : ℝ) : ℝ :=
  ∫ s in (0:ℝ)..sigma, q0_poly eta sigma rho (r - s) * (-s)

theorem baxterForcing_continuous (eta sigma rho : ℝ) :
    Continuous (baxterForcing eta sigma rho) := by
  unfold baxterForcing
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (r : ℝ) (s : ℝ) => q0_poly eta sigma rho (r - s) * (-s))
  have h : Continuous fun p : ℝ × ℝ => q0_poly eta sigma rho (p.1 - p.2) * (-p.2) :=
    ((q0_poly_continuous eta sigma rho).comp (continuous_fst.sub continuous_snd)).mul
      continuous_snd.neg
  exact h

/-- **`OZFIX.15` claim (A) — the Volterra construction, MA.10 instantiated.**

On every compact `[σ, b]` there is a **unique** continuous `ψ` solving the renewal equation

  `ψ(r) = baxterForcing(r) + ∫_σ^r q0(r-t)·ψ(t) dt`,

i.e. (unfolding the forcing) `ψ(r) = ∫₀^σ q0(t)·ψ(r-t) dt` once `ψ` is glued to the core value
`-s` on `(0,σ)`.  Equivalently `u := ψ ⋆ Q₊ ≡ 0` on `(σ, b)` — claim (A) — **by construction**.

Direct instantiation of `MA.10`'s `volterra_convolution_existsUnique` at the kernel `q := q0_poly`
and forcing `g := baxterForcing`; both continuous (`q0_poly_continuous`,
`baxterForcing_continuous`).  **No compactness/Fredholm is involved** — a one-sided (Volterra)
kernel is quasi-nilpotent, which is precisely why the Baxter factorisation sidesteps the
non-compact half-line Wiener–Hopf obstruction that stalled `OZ.10`. -/
theorem baxter_psi_volterra_existsUnique {eta sigma rho : ℝ} {b : ℝ} (hb : sigma ≤ b) :
    ∃! u : C(Set.Icc sigma b, ℝ), ∀ r : Set.Icc sigma b,
      u r = baxterForcing eta sigma rho r
        + ∫ t in sigma..(r : ℝ),
            q0_poly eta sigma rho ((r : ℝ) - t) * Set.IccExtend hb u t :=
  volterra_convolution_existsUnique hb (q0_poly eta sigma rho) (baxterForcing eta sigma rho)
    (q0_poly_continuous eta sigma rho) (baxterForcing_continuous eta sigma rho)

/-! ### `OZFIX.15` — from the local solutions to a single global `ψ` on `[σ,∞)`

`MA.10` produces a solution on each **compact** `[σ, b]` separately, as an element of the dependent
type `C(Icc σ b, ℝ)`.  The assembly needs **one** function on `[σ,∞)`.  The glue is uniqueness
itself: a solution on the longer interval, restricted, still solves the shorter equation (the
integration range `[σ,r]` never leaves `[σ,b]`, so the integrand is untouched), hence **is** the
shorter solution.  Evaluating the `b := r` solution at its own right endpoint therefore defines a
single global `ψ` that satisfies the renewal equation at every `r ≥ σ`. -/

/-- The local Volterra solution on `[a,b]` (`MA.10`'s `∃!`, named). -/
def volterraSol {a b : ℝ} (hab : a ≤ b) (q g : ℝ → ℝ)
    (hq : Continuous q) (hg : Continuous g) : C(Set.Icc a b, ℝ) :=
  (volterra_convolution_existsUnique hab q g hq hg).choose

theorem volterraSol_spec {a b : ℝ} (hab : a ≤ b) (q g : ℝ → ℝ)
    (hq : Continuous q) (hg : Continuous g) (r : Set.Icc a b) :
    volterraSol hab q g hq hg r = g r + ∫ t in a..(r : ℝ),
      q ((r : ℝ) - t) * Set.IccExtend hab (volterraSol hab q g hq hg) t :=
  (volterra_convolution_existsUnique hab q g hq hg).choose_spec.1 r

theorem volterraSol_unique {a b : ℝ} (hab : a ≤ b) (q g : ℝ → ℝ)
    (hq : Continuous q) (hg : Continuous g) (v : C(Set.Icc a b, ℝ))
    (hv : ∀ r : Set.Icc a b, v r = g r + ∫ t in a..(r : ℝ),
      q ((r : ℝ) - t) * Set.IccExtend hab v t) :
    v = volterraSol hab q g hq hg :=
  (volterra_convolution_existsUnique hab q g hq hg).choose_spec.2 v hv

/-- **Compatibility: the local solutions agree on overlaps.**

Restricting the `[a,b']` solution to `[a,b]` (`b ≤ b'`) still solves the `[a,b]` equation — for
`r ≤ b` the integration range `[a,r]` lies inside `[a,b]`, where the two `IccExtend`s agree
pointwise — so uniqueness on `[a,b]` forces it to *be* the `[a,b]` solution. -/
theorem volterraSol_compat {a b b' : ℝ} (hab : a ≤ b) (hab' : a ≤ b') (hbb' : b ≤ b')
    (q g : ℝ → ℝ) (hq : Continuous q) (hg : Continuous g) (r : ℝ) (hr : r ∈ Set.Icc a b) :
    volterraSol hab' q g hq hg ⟨r, ⟨hr.1, le_trans hr.2 hbb'⟩⟩
      = volterraSol hab q g hq hg ⟨r, hr⟩ := by
  have hsub : Set.Icc a b ⊆ Set.Icc a b' := Set.Icc_subset_Icc_right hbb'
  -- the restriction of the long solution to the short interval
  set v : C(Set.Icc a b, ℝ) :=
    (volterraSol hab' q g hq hg).comp ⟨Set.inclusion hsub, continuous_inclusion hsub⟩ with hvdef
  have hvapp : ∀ x : Set.Icc a b, v x = volterraSol hab' q g hq hg (Set.inclusion hsub x) :=
    fun _ => rfl
  -- on `[a,b]` the two extensions agree
  have hext : ∀ t ∈ Set.Icc a b,
      Set.IccExtend hab' (volterraSol hab' q g hq hg) t = Set.IccExtend hab v t := by
    intro t ht
    rw [Set.IccExtend_of_mem hab' _ (hsub ht), Set.IccExtend_of_mem hab _ ht, hvapp ⟨t, ht⟩]
  have hv : ∀ x : Set.Icc a b, v x = g x + ∫ t in a..(x : ℝ),
      q ((x : ℝ) - t) * Set.IccExtend hab v t := by
    intro x
    have hx := volterraSol_spec hab' q g hq hg (Set.inclusion hsub x)
    have hxv : ((Set.inclusion hsub x : Set.Icc a b') : ℝ) = (x : ℝ) := rfl
    rw [hxv] at hx
    rw [hvapp x, hx]
    congr 1
    refine intervalIntegral.integral_congr ?_
    intro t ht
    dsimp only []
    rw [Set.uIcc_of_le x.2.1] at ht
    have htmem : t ∈ Set.Icc a b := ⟨ht.1, le_trans ht.2 x.2.2⟩
    rw [hext t htmem]
  have hvu := volterraSol_unique hab q g hq hg v hv
  calc volterraSol hab' q g hq hg ⟨r, ⟨hr.1, le_trans hr.2 hbb'⟩⟩
      = v ⟨r, hr⟩ := rfl
    _ = volterraSol hab q g hq hg ⟨r, hr⟩ := by rw [hvu]

/-- **The global Volterra solution on `[a,∞)`** — evaluate the `b := r` local solution at its own
right endpoint.  Off `[a,∞)` it is `0` (the core branch supplies those values separately). -/
def volterraGlobal (a : ℝ) (q g : ℝ → ℝ) (hq : Continuous q) (hg : Continuous g) (r : ℝ) : ℝ :=
  if h : a ≤ r then volterraSol h q g hq hg ⟨r, ⟨h, le_refl r⟩⟩ else 0

/-- `volterraGlobal` agrees with every local solution on that solution's own interval. -/
theorem volterraGlobal_eq_sol {a b : ℝ} (hab : a ≤ b) (q g : ℝ → ℝ)
    (hq : Continuous q) (hg : Continuous g) (r : ℝ) (hr : r ∈ Set.Icc a b) :
    volterraGlobal a q g hq hg r = volterraSol hab q g hq hg ⟨r, hr⟩ := by
  rw [volterraGlobal, dif_pos hr.1]
  exact (volterraSol_compat (b := r) (b' := b) hr.1 hab hr.2 q g hq hg r
    ⟨hr.1, le_refl r⟩).symm

/-- **`OZFIX.15` claim (A), globalised — one `ψ` on all of `[a,∞)`.**

`volterraGlobal` satisfies the renewal equation at **every** `r ≥ a`, with the *same* function under
the integral sign.  This is the form the assembly needs: `MA.10` alone gives a different
`C(Icc a b, ℝ)` for each `b`, which cannot be fed to a convolution identity on `ℝ`. -/
theorem volterraGlobal_spec {a : ℝ} (q g : ℝ → ℝ) (hq : Continuous q) (hg : Continuous g)
    {r : ℝ} (hr : a ≤ r) :
    volterraGlobal a q g hq hg r
      = g r + ∫ t in a..r, q (r - t) * volterraGlobal a q g hq hg t := by
  have hmem : r ∈ Set.Icc a r := ⟨hr, le_refl r⟩
  rw [volterraGlobal_eq_sol hr q g hq hg r hmem, volterraSol_spec hr q g hq hg ⟨r, hmem⟩]
  congr 1
  refine intervalIntegral.integral_congr ?_
  intro t ht
  dsimp only []
  rw [Set.uIcc_of_le hr] at ht
  rw [volterraGlobal_eq_sol hr q g hq hg t ht, Set.IccExtend_of_mem hr _ ht]

/-! ### The glued `ψ` on all of `ℝ` -/

/-- **The outer branch of `ψ`** — `MA.10`'s solution, globalised to all of `[σ,∞)`. -/
def baxterPsiOuter (eta sigma rho : ℝ) : ℝ → ℝ :=
  volterraGlobal sigma (q0_poly eta sigma rho) (baxterForcing eta sigma rho)
    (q0_poly_continuous eta sigma rho) (baxterForcing_continuous eta sigma rho)

/-- `baxterPsiOuter` satisfies the renewal equation at **every** `r ≥ σ`. -/
theorem baxterPsiOuter_spec {eta sigma rho : ℝ} {r : ℝ} (hr : sigma ≤ r) :
    baxterPsiOuter eta sigma rho r
      = baxterForcing eta sigma rho r
        + ∫ t in sigma..r, q0_poly eta sigma rho (r - t) * baxterPsiOuter eta sigma rho t :=
  volterraGlobal_spec _ _ _ _ hr

/-- **The glued `ψ` on `ℝ`.**

Three branches: the *definitional* core value `-v` on `(-σ,σ)` (this is what `oz_operator`'s
`if r < σ then -1` branch forces on any `OzFixedPt`, and it is why the real-space route escapes
`OZFIX.14`'s circularity — nothing has to *reproduce* the core value), the Volterra solution on
`[σ,∞)`, and the odd reflection on `(-∞,-σ]`.

The branches are consistent at `v = ±σ` because the `sigma ≤ v` test fires first, and `-σ` lands in
the reflected branch (for `σ > 0`), giving `-ψ(σ)` — exactly what oddness demands. -/
def baxterPsi (eta sigma rho : ℝ) (v : ℝ) : ℝ :=
  if sigma ≤ v then baxterPsiOuter eta sigma rho v
  else if v ≤ -sigma then -baxterPsiOuter eta sigma rho (-v)
  else -v

/-- **The core value is definitional** — `ψ(v) = -v` on `(-σ,σ)`, with no proof obligation.
This is the hypothesis `baxter_u_core` (claim (B)) asks for. -/
theorem baxterPsi_core {eta sigma rho : ℝ} {v : ℝ} (hv : v ∈ Set.Ioo (-sigma) sigma) :
    baxterPsi eta sigma rho v = -v := by
  rw [baxterPsi, if_neg (not_le.mpr hv.2), if_neg (not_le.mpr hv.1)]

/-- `ψ` agrees with the Volterra solution on `[σ,∞)`. -/
theorem baxterPsi_outer {eta sigma rho : ℝ} {v : ℝ} (hv : sigma ≤ v) :
    baxterPsi eta sigma rho v = baxterPsiOuter eta sigma rho v := by
  rw [baxterPsi, if_pos hv]

/-- **`ψ` is odd** — the property the bridge (`OZFIX.16`) consumes, since `ψ = oddExt h`. -/
theorem baxterPsi_odd {eta sigma rho : ℝ} (hsigma : 0 < sigma) (v : ℝ) :
    baxterPsi eta sigma rho (-v) = -baxterPsi eta sigma rho v := by
  rcases le_or_gt sigma v with hv | hv
  · -- `v ≥ σ`: outer on the right, reflected branch on the left
    have h1 : ¬ (sigma ≤ -v) := by intro h; linarith
    have h2 : -v ≤ -sigma := by linarith
    rw [baxterPsi, if_neg h1, if_pos h2, neg_neg, baxterPsi, if_pos hv]
  · rcases le_or_gt v (-sigma) with hv2 | hv2
    · -- `v ≤ -σ`: reflected branch on the right, outer on the left
      have h1 : sigma ≤ -v := by linarith
      rw [baxterPsi, if_pos h1, baxterPsi, if_neg (not_le.mpr hv), if_pos hv2, neg_neg]
    · -- core: `-σ < v < σ`
      rw [baxterPsi_core ⟨by linarith, by linarith⟩,
        baxterPsi_core (v := v) ⟨hv2, hv⟩, neg_neg]

/-- The global solution is continuous on every compact `[a,b]` (it *is* the local solution there,
and that one is a bundled `C(Icc a b, ℝ)`). -/
theorem volterraGlobal_continuousOn {a b : ℝ} (hab : a ≤ b) (q g : ℝ → ℝ)
    (hq : Continuous q) (hg : Continuous g) :
    ContinuousOn (volterraGlobal a q g hq hg) (Set.Icc a b) := by
  rw [continuousOn_iff_continuous_restrict]
  have heq : Set.restrict (Set.Icc a b) (volterraGlobal a q g hq hg)
      = fun x => volterraSol hab q g hq hg x := by
    funext x
    exact volterraGlobal_eq_sol hab q g hq hg (x : ℝ) x.2
  rw [heq]
  exact (volterraSol hab q g hq hg).continuous

theorem baxterPsiOuter_continuousOn {eta sigma rho : ℝ} {b : ℝ} (hb : sigma ≤ b) :
    ContinuousOn (baxterPsiOuter eta sigma rho) (Set.Icc sigma b) :=
  volterraGlobal_continuousOn hb _ _ _ _

/-- **`OZFIX.15` claim (A), in its final usable form: `u := ψ ⋆ Q₊ ≡ 0` outside the core.**

  `ψ(r) = ∫₀^σ q0(t)·ψ(r-t) dt`   for every `r ≥ σ`.

This is what `MA.10` was *for*: the abstract renewal equation (`volterraGlobal_spec`, phrased with
the forcing `baxterForcing` and the range `[σ,r]`) becomes the **convolution** statement
`u := ψ ⋆ Q₊ ≡ 0`, which is the object the Baxter identity `ψ ⋆ Q₊ ⋆ Q₋ = φ` is built from.

**The mapping (no case split on `r ≷ 2σ`).** Substituting `s := r-t` turns `∫₀^σ q0(t)ψ(r-t)dt`
into `∫_{r-σ}^r q0(r-s)ψ(s)ds`. Because `q0` is supported in `[0,σ]` (`q0_poly_outer`), the sample
`q0(r-s)` vanishes for `s < r-σ`, so the range may be *opened up* to `[0,r]` for free — and `[0,r]`
splits at `σ` into exactly `baxterForcing r` (the core part, where `ψ(s) = -s` is definitional) plus
`∫_σ^r q0(r-s)ψ(s)ds` (the outer part). No `min`/`max` and no `r ≷ 2σ` case analysis survives; and
for `r ≥ 2σ` the forcing vanishes identically, which is the exact `r ≥ 2σ` vanishing previously seen
only numerically at `1e-17`.

**Where the two `a.e.`s come from.** `ψ` jumps at `σ`, so on `[0,σ]` it agrees with the continuous
`-s` only *up to the single point* `σ` — hence `Ioo_ae_eq_Ioc` rather than a pointwise congruence.
Likewise `q0(r-s)` vanishes on `Ioo 0 (r-σ)` but the endpoint `s = r-σ` must be dropped. Both bad
sets are singletons. -/
theorem baxter_u_outer {eta sigma rho : ℝ} (hsigma : 0 < sigma) {r : ℝ} (hr : sigma ≤ r) :
    baxterPsi eta sigma rho r
      = ∫ t in (0:ℝ)..sigma, q0_poly eta sigma rho t * baxterPsi eta sigma rho (r - t) := by
  have hr0 : (0:ℝ) ≤ r := le_trans hsigma.le hr
  have hrs : (0:ℝ) ≤ r - sigma := by linarith
  -- Step 1: substitute `s := r - t`.
  have hstep1 : (∫ t in (0:ℝ)..sigma, q0_poly eta sigma rho t * baxterPsi eta sigma rho (r - t))
      = ∫ s in (r - sigma)..r, q0_poly eta sigma rho (r - s) * baxterPsi eta sigma rho s := by
    have h := intervalIntegral.integral_comp_sub_left (a := (0:ℝ)) (b := sigma)
      (f := fun s => q0_poly eta sigma rho (r - s) * baxterPsi eta sigma rho s) r
    simpa only [sub_sub_cancel, sub_zero] using h
  -- On `[0,σ]` the integrand agrees a.e. with the continuous core integrand.
  have hae0 : (fun s => q0_poly eta sigma rho (r - s) * baxterPsi eta sigma rho s)
      =ᵐ[MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) sigma)]
      (fun s => q0_poly eta sigma rho (r - s) * (-s)) := by
    rw [← MeasureTheory.Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with s hs
    rw [baxterPsi_core (v := s) ⟨by linarith [hs.1], hs.2⟩]
  have hcore_cont : Continuous (fun s => q0_poly eta sigma rho (r - s) * (-s)) :=
    ((q0_poly_continuous eta sigma rho).comp (continuous_const.sub continuous_id)).mul
      continuous_id.neg
  have hIa : IntervalIntegrable (fun s => q0_poly eta sigma rho (r - s) * baxterPsi eta sigma rho s)
      MeasureTheory.volume 0 sigma := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hsigma.le]
    exact ((hcore_cont.integrableOn_Icc (a := 0) (b := sigma)).mono_set
      Set.Ioc_subset_Icc_self).congr_fun_ae hae0.symm
  -- On `[σ,r]` the integrand is continuous (`ψ = ψ_outer` there).
  have hcongr_outer : Set.EqOn (fun s => q0_poly eta sigma rho (r - s) * baxterPsi eta sigma rho s)
      (fun s => q0_poly eta sigma rho (r - s) * baxterPsiOuter eta sigma rho s)
      (Set.uIcc sigma r) := by
    intro s hs
    rw [Set.uIcc_of_le hr] at hs
    dsimp only []
    rw [baxterPsi_outer hs.1]
  have hIb : IntervalIntegrable (fun s => q0_poly eta sigma rho (r - s) * baxterPsi eta sigma rho s)
      MeasureTheory.volume sigma r := by
    apply ContinuousOn.intervalIntegrable
    refine ContinuousOn.congr ?_ hcongr_outer
    rw [Set.uIcc_of_le hr]
    exact (((q0_poly_continuous eta sigma rho).comp
      (continuous_const.sub continuous_id)).continuousOn).mul (baxterPsiOuter_continuousOn hr)
  have hI0r : IntervalIntegrable
      (fun s => q0_poly eta sigma rho (r - s) * baxterPsi eta sigma rho s)
      MeasureTheory.volume 0 r := hIa.trans hIb
  have hI0rs : IntervalIntegrable
      (fun s => q0_poly eta sigma rho (r - s) * baxterPsi eta sigma rho s)
      MeasureTheory.volume 0 (r - sigma) :=
    hI0r.mono_set (Set.uIcc_subset_uIcc (by rw [Set.mem_uIcc]; left; constructor <;> linarith)
      (by rw [Set.mem_uIcc]; left; constructor <;> linarith))
  -- Step 2: the `[0, r-σ]` piece vanishes — `q0(r-s) = 0` there.
  -- a single point is `volume`-null, which is all the two `a.e.`s below need
  have hne : ∀ c : ℝ, ∀ᵐ (x : ℝ), x ≠ c := by
    intro c
    rw [MeasureTheory.ae_iff]
    simpa using MeasureTheory.measure_singleton c
  have hvanish : (∫ s in (0:ℝ)..(r - sigma),
      q0_poly eta sigma rho (r - s) * baxterPsi eta sigma rho s) = 0 := by
    rw [intervalIntegral.integral_congr_ae (g := fun _ => (0:ℝ)) ?_, intervalIntegral.integral_zero]
    rw [Set.uIoc_of_le hrs]
    filter_upwards [hne (r - sigma)] with s hs hmem
    have hlt : s < r - sigma := lt_of_le_of_ne hmem.2 hs
    rw [q0_poly_outer (by linarith : sigma < r - s), zero_mul]
  -- Step 3: open the range up to `[0,r]`, then split at `σ`.
  have hopen : (∫ s in (r - sigma)..r,
      q0_poly eta sigma rho (r - s) * baxterPsi eta sigma rho s)
      = ∫ s in (0:ℝ)..r, q0_poly eta sigma rho (r - s) * baxterPsi eta sigma rho s := by
    rw [← intervalIntegral.integral_interval_sub_left hI0r hI0rs, hvanish, sub_zero]
  have hsplit : (∫ s in (0:ℝ)..r, q0_poly eta sigma rho (r - s) * baxterPsi eta sigma rho s)
      = (∫ s in (0:ℝ)..sigma, q0_poly eta sigma rho (r - s) * baxterPsi eta sigma rho s)
        + ∫ s in sigma..r, q0_poly eta sigma rho (r - s) * baxterPsi eta sigma rho s :=
    (intervalIntegral.integral_add_adjacent_intervals hIa hIb).symm
  -- Step 4: identify the two pieces with `baxterForcing` and the outer integral.
  have hpiece1 : (∫ s in (0:ℝ)..sigma,
      q0_poly eta sigma rho (r - s) * baxterPsi eta sigma rho s)
      = baxterForcing eta sigma rho r := by
    rw [baxterForcing]
    refine intervalIntegral.integral_congr_ae ?_
    rw [Set.uIoc_of_le hsigma.le]
    filter_upwards [hne sigma] with s hs hmem
    have hlt : s < sigma := lt_of_le_of_ne hmem.2 hs
    rw [baxterPsi_core (v := s) ⟨by linarith [hmem.1], hlt⟩]
  have hpiece2 : (∫ s in sigma..r, q0_poly eta sigma rho (r - s) * baxterPsi eta sigma rho s)
      = ∫ s in sigma..r, q0_poly eta sigma rho (r - s) * baxterPsiOuter eta sigma rho s :=
    intervalIntegral.integral_congr hcongr_outer
  rw [hstep1, hopen, hsplit, hpiece1, hpiece2, baxterPsi_outer hr]
  exact baxterPsiOuter_spec hr

/-! ### Claim (B): `u := ψ ⋆ Q₊` is explicit on the core -/

/-- **`OZFIX.15` claim (B) — `u := ψ ⋆ Q₊` is explicit on the core.**

For any `ψ` carrying the *definitional* core value `ψ(v) = -v` on `(-σ, σ)` — which every
`OzFixedPt` does, via `oz_operator`'s `if r < σ then -1` branch — the convolution
`u(r) := ψ(r) - ∫₀^σ q0_poly(t)·ψ(r-t) dt` is the explicit affine function

  `u(r) = r·(M₀ - 1) - M₁`  on `(0, σ)`.

This needs **no series and no Volterra solve**: for `0 < r < σ` and `t ∈ [0, σ]` the sample point
`r - t` stays in `(-σ, σ)`, i.e. the *whole* sampling range is inside the core, so `ψ(r-t)` is
known outright.  Then `u(r) = -r + ∫₀^σ q0(t)(r-t)dt = -r + r·M₀ - M₁`, using
`baxterM0_eq`/`baxterM1_eq`.

This is the brick that justifies the affine `u` **hard-coded** in `baxter_core_seed`'s statement:
together they give `(u ⋆ Q₋)(r) = r·c_HS(r)` for the *actual* `ψ`, not just for an assumed form. -/
theorem baxter_u_core {eta sigma rho : ℝ} (hsigma : 0 < sigma) {psi : ℝ → ℝ}
    (hcore : ∀ v ∈ Set.Ioo (-sigma) sigma, psi v = -v)
    {r : ℝ} (hr : r ∈ Set.Ioo (0:ℝ) sigma) :
    psi r - (∫ t in (0:ℝ)..sigma, q0_poly eta sigma rho t * psi (r - t))
      = r * (baxterM0 eta sigma rho - 1) - baxterM1 eta sigma rho := by
  obtain ⟨hr0, hrlt⟩ := hr
  have hpr : psi r = -r := hcore r ⟨by linarith, hrlt⟩
  -- On `[0,σ]` the whole sampling range `r - t` lies in the core, so `ψ(r-t) = -(r-t)`.
  have hcongr : (∫ t in (0:ℝ)..sigma, q0_poly eta sigma rho t * psi (r - t))
      = ∫ t in (0:ℝ)..sigma,
          (-r * q0_poly eta sigma rho t + t * q0_poly eta sigma rho t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hsigma.le] at ht
    dsimp only []
    rw [hcore (r - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩]
    ring
  rw [hcongr, hpr]
  have hc : Continuous (q0_poly eta sigma rho) := q0_poly_continuous eta sigma rho
  have h1 : IntervalIntegrable (fun t : ℝ => -r * q0_poly eta sigma rho t) volume 0 sigma :=
    (hc.const_mul _).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun t : ℝ => t * q0_poly eta sigma rho t) volume 0 sigma :=
    (continuous_id.mul hc).intervalIntegrable _ _
  rw [intervalIntegral.integral_add h1 h2, intervalIntegral.integral_const_mul,
      baxterM0_eq hsigma, baxterM1_eq hsigma]
  ring

/-! ### The Wertheim–Thiele core seed -/

/-- **`OZFIX.15` — the Wertheim–Thiele core seed.**

For `0 < r < σ`, with `u(v) := v·(M₀-1) - M₁` (which is `(ψ ⋆ Q₊)(v)` on the core — explicit,
because the core value `ψ = -v` is definitional in `OzFixedPt`) and `u ≡ 0` on `(σ,∞)`:

  `(u ⋆ Q₋)(r) = u(r) - ∫₀^{σ-r} q0_poly(t)·u(r+t)dt = r·c_HS(r) = φ(r)`.

(The integral stops at `σ-r` precisely because `u(r+t) = 0` once `r+t > σ`.) This is the `h`-half
of Baxter's pair — the piece the Fourier route provably cannot supply (`OZFIX.14`) — and, per the
file header, a genuine identity in `η`, verified symbolically coefficient by coefficient before
formalizing. Same technique as `baxter_factorization_inner`, the `c`-half: expand `q0_poly` on the
core, FTC against an explicit quartic antiderivative, then `field_simp` + `ring` under `heta_def`. -/
theorem baxter_core_seed {eta sigma rho : ℝ} (hsigma : 0 < sigma) (heta : eta < 1)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) :
    ∀ r ∈ Set.Ioo (0:ℝ) sigma,
      (r * (baxterM0 eta sigma rho - 1) - baxterM1 eta sigma rho) -
          (∫ t in (0:ℝ)..(sigma - r), q0_poly eta sigma rho t *
            ((r + t) * (baxterM0 eta sigma rho - 1) - baxterM1 eta sigma rho)) =
        r * c_HS eta sigma r := by
  intro r hr
  obtain ⟨hr0, hrlt⟩ := hr
  have hsr : (0:ℝ) ≤ sigma - r := by linarith
  set α := rho * q_prime_py eta sigma with hα_def
  set β := rho * q_doubleprime_py eta with hβ_def
  set K := baxterM0 eta sigma rho - 1 with hK_def
  set L := baxterM1 eta sigma rho with hL_def
  set c := K * (r + sigma) - L with hc_def
  -- expand `q0_poly` on `[0, σ-r] ⊆ [0,σ]`
  have hcongr : (∫ t in (0:ℝ)..(sigma - r), q0_poly eta sigma rho t * ((r + t) * K - L)) =
      ∫ t in (0:ℝ)..(sigma - r),
        (α * (t - sigma) + β * (t - sigma) ^ 2 / 2) * ((r + t) * K - L) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hsr] at ht
    dsimp only []
    rw [q0_poly_inner (by linarith [ht.2] : t ≤ sigma), ← hα_def, ← hβ_def]
  rw [hcongr]
  have hint : IntervalIntegrable
      (fun t : ℝ => (α * (t - sigma) + β * (t - sigma) ^ 2 / 2) * ((r + t) * K - L))
      volume 0 (sigma - r) := by
    apply Continuous.intervalIntegrable; fun_prop
  -- FTC against the explicit quartic antiderivative.  With `s := x - σ` the integrand is
  -- `(α s + β s²/2)(K s + c)` where `c = K(r+σ) - L`, whose antiderivative in `s` is
  -- `(βK/8)s⁴ + ((αK + βc/2)/3)s³ + (αc/2)s²`.
  have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) (sigma - r),
      HasDerivAt (fun y : ℝ => β * K / 8 * (y - sigma) ^ 4 +
          (α * K + β * c / 2) / 3 * (y - sigma) ^ 3 + α * c / 2 * (y - sigma) ^ 2)
        ((α * (x - sigma) + β * (x - sigma) ^ 2 / 2) * ((r + x) * K - L)) x := by
    intro x _
    have hin : HasDerivAt (fun y : ℝ => y - sigma) 1 x := by
      have h := (hasDerivAt_id x).sub (hasDerivAt_const x sigma)
      simp only [sub_zero] at h; exact h
    have h2 : HasDerivAt (fun y : ℝ => (y - sigma) ^ 2) (2 * (x - sigma)) x :=
      (hin.pow 2).congr_deriv (by push_cast; ring)
    have h3 : HasDerivAt (fun y : ℝ => (y - sigma) ^ 3) (3 * (x - sigma) ^ 2) x :=
      (hin.pow 3).congr_deriv (by push_cast; ring)
    have h4 : HasDerivAt (fun y : ℝ => (y - sigma) ^ 4) (4 * (x - sigma) ^ 3) x :=
      (hin.pow 4).congr_deriv (by push_cast; ring)
    have hA1 : HasDerivAt (fun y : ℝ => β * K / 8 * (y - sigma) ^ 4)
        (β * K / 8 * (4 * (x - sigma) ^ 3)) x := h4.const_mul _
    have hA2 : HasDerivAt (fun y : ℝ => (α * K + β * c / 2) / 3 * (y - sigma) ^ 3)
        ((α * K + β * c / 2) / 3 * (3 * (x - sigma) ^ 2)) x := h3.const_mul _
    have hA3 : HasDerivAt (fun y : ℝ => α * c / 2 * (y - sigma) ^ 2)
        (α * c / 2 * (2 * (x - sigma))) x := h2.const_mul _
    refine (((hA1.add hA2).add hA3).congr_of_eventuallyEq ?_).congr_deriv ?_
    · exact Filter.Eventually.of_forall fun y => by simp [Pi.add_apply]
    · rw [hc_def]; ring
  rw [integral_eq_sub_of_hasDerivAt hderiv hint, c_HS_inner hrlt]
  -- Everything is polynomial now.  NB: eliminate `rho` in favour of `eta` (NOT `eta` in favour of
  -- `rho`, the direction `baxter_factorization_inner` uses): here the moments `M₀`, `M₁` are
  -- themselves degree-1 in `rho`, so their products push the denominator up to `(6-πρσ³)⁴`, which
  -- `field_simp` cannot discharge.  Eliminating `rho` keeps every denominator `(1-eta)`-atomic
  -- (`M₀ = η(η-4)/(1-η)²`, `M₁ = -3ησ/(2(1-η)²)`).
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hsig : sigma ≠ 0 := hsigma.ne'
  have hone : (1 : ℝ) - eta ≠ 0 := ne_of_gt (by linarith)
  have hrho_eq : rho = 6 * eta / (Real.pi * sigma ^ 3) := by
    rw [heta_def]; field_simp
  simp only [hc_def, hK_def, hL_def, hα_def, hβ_def, baxterM0, baxterM1, py_a0, py_a1, py_a3,
    q_prime_py, q_doubleprime_py, hrho_eq]
  field_simp
  ring

/-! ### `u := ψ ⋆ Q₊` at the concrete glued `ψ` — (A)+(B)+(C) with no hypotheses left over

`baxter_u_core` (B) and `baxter_core_seed` (C) were stated for a *hypothetical* `ψ` carrying the core
value, and for the *explicit affine* `u` respectively.  With `baxterPsi` constructed and `baxter_u_outer`
proved, both instantiate at the real object: `baxterPsi_core` discharges (B)'s `hcore`, and
`baxterU_outer`/`baxterU_core` show the real `u` **is** the function (C) assumes. -/

/-- `u := ψ ⋆ Q₊` at the concrete glued `ψ`. -/
def baxterU (eta sigma rho : ℝ) (r : ℝ) : ℝ :=
  baxterPsi eta sigma rho r
    - ∫ t in (0:ℝ)..sigma, q0_poly eta sigma rho t * baxterPsi eta sigma rho (r - t)

/-- **(A) at the concrete `ψ`** — `u ≡ 0` on `[σ,∞)`, by construction of the Volterra branch. -/
theorem baxterU_outer {eta sigma rho : ℝ} (hsigma : 0 < sigma) {r : ℝ} (hr : sigma ≤ r) :
    baxterU eta sigma rho r = 0 := by
  rw [baxterU, ← baxter_u_outer hsigma hr, sub_self]

/-- **(B) at the concrete `ψ`** — `u` is the explicit affine `r·(M₀-1) - M₁` on `(0,σ)`.
The `hcore` hypothesis of `baxter_u_core` is discharged by `baxterPsi_core`, which is *definitional*. -/
theorem baxterU_core {eta sigma rho : ℝ} (hsigma : 0 < sigma) {r : ℝ}
    (hr : r ∈ Set.Ioo (0:ℝ) sigma) :
    baxterU eta sigma rho r = r * (baxterM0 eta sigma rho - 1) - baxterM1 eta sigma rho :=
  baxter_u_core hsigma (fun _ hv => baxterPsi_core hv) hr

/-- **`OZFIX.15` — the Wertheim–Thiele seed for the REAL `u`.**

  `(u ⋆ Q₋)(r) = u(r) - ∫₀^{σ-r} q0(t)·u(r+t) dt = r·c_HS(r) = φ(r)`   on `(0,σ)`,

now with `u := baxterU` the **constructed** `ψ ⋆ Q₊`, not a hypothetical affine function. The
integral stops at `σ-r` exactly because `u(r+t) = 0` once `r+t ≥ σ` (`baxterU_outer`) — the same
support fact that ran the `[0,σ]`-opening in `baxter_u_outer`.

The `a.e.` is again a single endpoint: at `t = σ-r` the sample sits at `r+t = σ`, where `u` has
already switched to the outer branch (`u(σ) = 0`), so the affine description holds on `Ioc 0 (σ-r)`
only up to that one point. -/
theorem baxter_seed_at_psi {eta sigma rho : ℝ} (hsigma : 0 < sigma) (heta : eta < 1)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) :
    ∀ r ∈ Set.Ioo (0:ℝ) sigma,
      baxterU eta sigma rho r
        - (∫ t in (0:ℝ)..(sigma - r), q0_poly eta sigma rho t * baxterU eta sigma rho (r + t))
        = r * c_HS eta sigma r := by
  intro r hr
  obtain ⟨hr0, hrlt⟩ := hr
  have hsr : (0:ℝ) ≤ sigma - r := by linarith
  have hne : ∀ᵐ (x : ℝ), x ≠ sigma - r := by
    rw [MeasureTheory.ae_iff]; simpa using MeasureTheory.measure_singleton (sigma - r)
  have hint : (∫ t in (0:ℝ)..(sigma - r), q0_poly eta sigma rho t * baxterU eta sigma rho (r + t))
      = ∫ t in (0:ℝ)..(sigma - r), q0_poly eta sigma rho t *
          ((r + t) * (baxterM0 eta sigma rho - 1) - baxterM1 eta sigma rho) := by
    refine intervalIntegral.integral_congr_ae ?_
    rw [Set.uIoc_of_le hsr]
    filter_upwards [hne] with t ht hmem
    have hlt : t < sigma - r := lt_of_le_of_ne hmem.2 ht
    rw [baxterU_core hsigma ⟨by linarith [hmem.1], by linarith⟩]
  rw [hint, baxterU_core hsigma ⟨hr0, hrlt⟩]
  exact baxter_core_seed hsigma heta heta_def r ⟨hr0, hrlt⟩

/-- `(u ⋆ Q₋)(r) = u(r) - ∫₀^σ q0(t)·u(r+t) dt` — the **second** Baxter factor applied to
`u := ψ ⋆ Q₊`.  `Q₋(v) := Q₊(-v)`, which is why the sample runs `r+t` rather than `r-t`. -/
def baxterUQm (eta sigma rho : ℝ) (r : ℝ) : ℝ :=
  baxterU eta sigma rho r
    - ∫ t in (0:ℝ)..sigma, q0_poly eta sigma rho t * baxterU eta sigma rho (r + t)

/-- **`OZFIX.15` COMPLETE — `ψ ⋆ Q₊ ⋆ Q₋ = φ` on all of `(0,∞)`.**

  `(ψ ⋆ Q₊ ⋆ Q₋)(r) = r · c_HS(r) = φ(r)`   for every `r > 0`.

This is the goal the whole real-space route was built for, now with **every** object concrete: `ψ` is
`baxterPsi` (constructed), `u = ψ ⋆ Q₊` is `baxterU`, and the two claims (A)/(B) that make `u`
explicit are `baxterU_outer`/`baxterU_core`.

**No Fubini, no associativity side-condition.** The identity is *parenthesised* `(ψ ⋆ Q₊) ⋆ Q₋` — the
route builds `u := ψ ⋆ Q₊` first and applies `Q₋` to it — so `baxterUQm` **is** the left-hand side by
definition and there is nothing to re-associate.

Two regimes, and **no exceptional point** (`c_HS_outer` holds at `r = σ` too, on the closed side):
* `0 < r < σ`: the tail `∫_{σ-r}^σ` vanishes **exactly** (not merely a.e.) since `r+t ≥ σ` there
  ⇒ `baxterU_outer` ⇒ integrand `≡ 0`; what is left is `baxter_seed_at_psi`, the Wertheim–Thiele seed.
* `r ≥ σ`: `u(r) = 0` and `u(r+t) = 0` for every `t ∈ [0,σ]`, so the left side is `0`; and
  `c_HS_outer` makes the right side `r·0 = 0`. -/
theorem baxter_psi_conv_eq_phi {eta sigma rho : ℝ} (hsigma : 0 < sigma) (heta : eta < 1)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) {r : ℝ} (hr : 0 < r) :
    baxterUQm eta sigma rho r = r * c_HS eta sigma r := by
  rcases lt_or_ge r sigma with hrs | hrs
  · -- core: `0 < r < σ`
    have hsr : (0:ℝ) ≤ sigma - r := by linarith
    -- the `[σ-r, σ]` tail vanishes identically
    have htail : (∫ t in (sigma - r)..sigma,
        q0_poly eta sigma rho t * baxterU eta sigma rho (r + t)) = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) ?_, intervalIntegral.integral_zero]
      intro t ht
      rw [Set.uIcc_of_le (by linarith : sigma - r ≤ sigma)] at ht
      dsimp only []
      rw [baxterU_outer hsigma (by linarith [ht.1] : sigma ≤ r + t), mul_zero]
    -- integrability on `[0, σ-r]` (affine up to the single endpoint `t = σ-r`) …
    have haeA : (fun t => q0_poly eta sigma rho t * baxterU eta sigma rho (r + t))
        =ᵐ[MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) (sigma - r))]
        (fun t => q0_poly eta sigma rho t *
          ((r + t) * (baxterM0 eta sigma rho - 1) - baxterM1 eta sigma rho)) := by
      rw [← MeasureTheory.Measure.restrict_congr_set Ioo_ae_eq_Ioc]
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with t ht
      rw [baxterU_core hsigma ⟨by linarith [ht.1], by linarith [ht.2]⟩]
    have hcontA : Continuous (fun t => q0_poly eta sigma rho t *
        ((r + t) * (baxterM0 eta sigma rho - 1) - baxterM1 eta sigma rho)) :=
      (q0_poly_continuous eta sigma rho).mul
        (((continuous_const.add continuous_id).mul continuous_const).sub continuous_const)
    have hIa : IntervalIntegrable
        (fun t => q0_poly eta sigma rho t * baxterU eta sigma rho (r + t))
        MeasureTheory.volume 0 (sigma - r) := by
      rw [intervalIntegrable_iff, Set.uIoc_of_le hsr]
      exact ((hcontA.integrableOn_Icc (a := 0) (b := sigma - r)).mono_set
        Set.Ioc_subset_Icc_self).congr_fun_ae haeA.symm
    -- … and on `[σ-r, σ]`, where it is the zero function
    have hIb : IntervalIntegrable
        (fun t => q0_poly eta sigma rho t * baxterU eta sigma rho (r + t))
        MeasureTheory.volume (sigma - r) sigma := by
      apply ContinuousOn.intervalIntegrable
      refine ContinuousOn.congr (continuousOn_const (c := (0:ℝ))) ?_
      intro t ht
      rw [Set.uIcc_of_le (by linarith : sigma - r ≤ sigma)] at ht
      dsimp only []
      rw [baxterU_outer hsigma (by linarith [ht.1] : sigma ≤ r + t), mul_zero]
    have hsplit : (∫ t in (0:ℝ)..sigma, q0_poly eta sigma rho t * baxterU eta sigma rho (r + t))
        = (∫ t in (0:ℝ)..(sigma - r), q0_poly eta sigma rho t * baxterU eta sigma rho (r + t))
          + ∫ t in (sigma - r)..sigma, q0_poly eta sigma rho t * baxterU eta sigma rho (r + t) :=
      (intervalIntegral.integral_add_adjacent_intervals hIa hIb).symm
    rw [baxterUQm, hsplit, htail, add_zero]
    exact baxter_seed_at_psi hsigma heta heta_def r ⟨hr, hrs⟩
  · -- outer: `r ≥ σ` — both sides are `0`
    have h2 : (∫ t in (0:ℝ)..sigma, q0_poly eta sigma rho t * baxterU eta sigma rho (r + t)) = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) ?_, intervalIntegral.integral_zero]
      intro t ht
      rw [Set.uIcc_of_le hsigma.le] at ht
      dsimp only []
      rw [baxterU_outer hsigma (by linarith [ht.1] : sigma ≤ r + t), mul_zero]
    rw [baxterUQm, baxterU_outer hsigma hrs, h2, c_HS_outer hrs]
    ring

/-! ### The odd extension, and killing `radial3d_conv`'s absolute value

The first brick of the `1D-odd ↔ 3D-radial` bridge (`OZFIX.15` step 3). `radial3d_conv`'s inner
shell integral carries an `|r-t|`, which is what forces the `max`/case-split machinery all through
`OZFIX.5`/`OZFIX.11`/`OZFIX.12`. Written against the **odd extension** `g̃(v) := v·g|v|` the
absolute value simply disappears — because an odd function integrates to `0` over any interval
symmetric about the origin, which is exactly the `[r-t, |r-t|]` overhang when `r < t`. -/

/-- `g̃(v) := v · g |v|` — the odd extension of `r ↦ r·g(r)`. This is the object in which Baxter's
real-space identity `ψ ⋆ Q₊ ⋆ Q₋ = φ` is stated (`ψ = oddExt h`, `φ = oddExt c_HS`). -/
def oddExt (g : ℝ → ℝ) (v : ℝ) : ℝ := v * g |v|

@[simp] theorem oddExt_neg (g : ℝ → ℝ) (v : ℝ) : oddExt g (-v) = -oddExt g v := by
  unfold oddExt; rw [abs_neg]; ring

theorem oddExt_of_nonneg {g : ℝ → ℝ} {v : ℝ} (hv : 0 ≤ v) : oddExt g v = v * g v := by
  unfold oddExt; rw [abs_of_nonneg hv]

/-- An odd function integrates to zero over an interval symmetric about the origin. -/
theorem integral_oddExt_symm (g : ℝ → ℝ) (a : ℝ)
    (hint : IntervalIntegrable (oddExt g) MeasureTheory.volume (-a) a) :
    (∫ v in (-a)..a, oddExt g v) = 0 := by
  have h0 : (0:ℝ) ∈ Set.uIcc (-a) a := by
    rw [Set.mem_uIcc]
    rcases le_total (0:ℝ) a with h | h
    · left; constructor <;> linarith
    · right; constructor <;> linarith
  have hint1 : IntervalIntegrable (oddExt g) MeasureTheory.volume (-a) 0 :=
    hint.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc h0)
  have hint2 : IntervalIntegrable (oddExt g) MeasureTheory.volume 0 a :=
    hint.mono_set (Set.uIcc_subset_uIcc h0 Set.right_mem_uIcc)
  rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
  have hrefl : (∫ v in (-a)..(0:ℝ), oddExt g v) = -∫ v in (0:ℝ)..a, oddExt g v := by
    have h := intervalIntegral.integral_comp_neg (a := (0:ℝ)) (b := a) (f := oddExt g)
    rw [neg_zero] at h
    rw [← h]
    simp only [oddExt_neg]
    exact intervalIntegral.integral_neg
  rw [hrefl]; ring

/-- **`OZFIX.15` bridge brick — the absolute value disappears.**

`radial3d_conv`'s inner shell integral `∫_{|r-t|}^{r+t} s·g(s)ds` equals the *plain* integral
`∫_{r-t}^{r+t} g̃(s)ds` of the odd extension — no `|·|`, no case split. When `r ≥ t` the two agree
pointwise; when `r < t` the extra piece `[r-t, t-r]` is symmetric about `0`, so the odd integrand
contributes nothing (`integral_oddExt_symm`). Note `0 ≤ r` is exactly what makes the overhang fit
inside the interval (`-(r-t) ≤ r+t ⟺ 0 ≤ r`). -/
theorem integral_shell_eq_oddExt {g : ℝ → ℝ} {r t : ℝ} (hr : 0 ≤ r) (ht : 0 ≤ t)
    (hint : IntervalIntegrable (oddExt g) MeasureTheory.volume (r - t) (r + t)) :
    (∫ s in (|r - t|)..(r + t), s * g s) = ∫ s in (r - t)..(r + t), oddExt g s := by
  have hlt : r - t ≤ r + t := by linarith
  rcases le_or_gt 0 (r - t) with h | h
  · rw [abs_of_nonneg h]
    refine (intervalIntegral.integral_congr ?_).symm
    intro s hs
    rw [Set.uIcc_of_le hlt] at hs
    exact oddExt_of_nonneg (le_trans h hs.1)
  · rw [abs_of_neg h]
    have hle1 : r - t ≤ -(r - t) := by linarith
    have hle2 : -(r - t) ≤ r + t := by linarith
    have hmem : -(r - t) ∈ Set.uIcc (r - t) (r + t) := by
      rw [Set.mem_uIcc]; left; exact ⟨hle1, hle2⟩
    have hint1 : IntervalIntegrable (oddExt g) MeasureTheory.volume (r - t) (-(r - t)) :=
      hint.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc hmem)
    have hint2 : IntervalIntegrable (oddExt g) MeasureTheory.volume (-(r - t)) (r + t) :=
      hint.mono_set (Set.uIcc_subset_uIcc hmem Set.right_mem_uIcc)
    rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
    have hsym : (∫ s in (r - t)..(-(r - t)), oddExt g s) = 0 := by
      have h' := integral_oddExt_symm g (-(r - t)) (by simpa using hint1)
      simpa using h'
    rw [hsym, zero_add]
    refine (intervalIntegral.integral_congr ?_).symm
    intro s hs
    rw [Set.uIcc_of_le hle2] at hs
    exact oddExt_of_nonneg (le_trans (by linarith) hs.1)

/-- **`OZFIX.16` brick — the fold: two half-lines ⇒ one 1D convolution.**

The whole-line convolution of the odd extensions collapses onto `Ioi 0`:

  `(f̃ ⋆ g̃)(r) = ∫_ℝ f̃(t)·g̃(r-t) dt = -∫_{Ioi 0} t·f(t)·(g̃(r+t) - g̃(r-t)) dt`.

Proof: split `ℝ = Ioi 0 ∪ Iic 0` (`integral_add_compl`, `compl_Ioi`) and reflect the `Iic 0` half by
`t ↦ -t` (`integral_comp_neg_Ioi`).  On `Ioi 0` we have `f̃(t) = t·f(t)`, while the reflected half
contributes `f̃(-t)·g̃(r+t) = -t·f(t)·g̃(r+t)` — the two halves therefore differ exactly by the
`g̃(r+t)` vs `g̃(r-t)` sampling, which is the shape produced by differentiating
`radial3d_conv_eq_oddExt`'s inner shell integral `∫_{r-t}^{r+t} g̃`.

**No differentiation is used here** — this is the purely measure-theoretic half of `OZFIX.16`, and it
is what turns `d/dr[r·(f ⊛₃ g)(r)] = 2π∫_{Ioi 0} t·f(t)·(g̃(r+t) - g̃(r-t))` into the target
`-2π·(f̃ ⋆ g̃)(r)`. -/
theorem oddExt_conv_fold {f g : ℝ → ℝ} {r : ℝ}
    (hint : MeasureTheory.Integrable (fun t => oddExt f t * oddExt g (r - t))) :
    (∫ t, oddExt f t * oddExt g (r - t))
      = -∫ t in Set.Ioi (0:ℝ), t * f t * (oddExt g (r + t) - oddExt g (r - t)) := by
  set F : ℝ → ℝ := fun t => oddExt f t * oddExt g (r - t) with hF
  -- ℝ = Ioi 0 ⊎ Iic 0
  have hsplit : (∫ t in Set.Ioi (0:ℝ), F t) + (∫ t in Set.Iic (0:ℝ), F t) = ∫ t, F t := by
    have h := MeasureTheory.integral_add_compl (measurableSet_Ioi (a := (0:ℝ))) hint
    rwa [Set.compl_Ioi] at h
  -- reflect the negative half
  have hrefl : (∫ t in Set.Iic (0:ℝ), F t) = ∫ t in Set.Ioi (0:ℝ), F (-t) := by
    simpa using (integral_comp_neg_Ioi (0:ℝ) F).symm
  -- pointwise identifications on Ioi 0
  have hpos : ∀ t ∈ Set.Ioi (0:ℝ), F t = t * f t * oddExt g (r - t) := by
    intro t ht
    simp only [hF, oddExt_of_nonneg (Set.mem_Ioi.mp ht).le]
  have hneg : ∀ t ∈ Set.Ioi (0:ℝ), F (-t) = -(t * f t * oddExt g (r + t)) := by
    intro t ht
    have hrt : r - -t = r + t := by ring
    simp only [hF, oddExt_neg, hrt, oddExt_of_nonneg (Set.mem_Ioi.mp ht).le]
    ring
  rw [← hsplit, hrefl,
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hpos,
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hneg]
  -- `∫ A - ∫ B = -∫ (B - A)` on `Ioi 0`
  have hIA : MeasureTheory.IntegrableOn (fun t : ℝ => t * f t * oddExt g (r - t))
      (Set.Ioi (0:ℝ)) := by
    have h := (hint.integrableOn (s := Set.Ioi (0:ℝ)))
    refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
    exact hpos t ht
  have hIB : MeasureTheory.IntegrableOn (fun t : ℝ => t * f t * oddExt g (r + t))
      (Set.Ioi (0:ℝ)) := by
    have h : MeasureTheory.IntegrableOn (fun t : ℝ => F (-t)) (Set.Ioi (0:ℝ)) :=
      (hint.comp_neg).integrableOn (s := Set.Ioi (0:ℝ))
    have h2 : MeasureTheory.IntegrableOn (fun t : ℝ => -(t * f t * oddExt g (r + t)))
        (Set.Ioi (0:ℝ)) := h.congr_fun (fun t ht => hneg t ht) measurableSet_Ioi
    simpa using h2.neg
  rw [MeasureTheory.integral_neg, ← sub_eq_add_neg, ← MeasureTheory.integral_sub hIA hIB,
      ← MeasureTheory.integral_neg]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t _ => by ring)

/-- **`radial3d_conv` with the absolute value removed.**

The payoff of `integral_shell_eq_oddExt`, at the level of `radial3d_conv` itself: for `r > 0`,

  `radial3d_conv f g r = (2π/r) · ∫ t in Ioi 0, t·f(t) · ∫ s in (r-t)..(r+t), g̃(s) ds`

— the inner shell integral's `|r-t|` is gone, so no `max`/case-split on `r-t ≷ 0` survives. This
is the shape in which Baxter's real-space identity `ψ ⋆ Q₊ ⋆ Q₋ = φ` meets `radial3d_conv`
(`OZFIX.15` step 3): differentiating in `r` turns the inner `∫_{r-t}^{r+t} g̃` into
`g̃(r+t) - g̃(r-t)`, and folding the `t`-integral against the odd extension `f̃` of `f` gives
exactly `-2π·(f̃ ⋆ g̃)(r)` — the 1D convolution. -/
theorem radial3d_conv_eq_oddExt {f g : ℝ → ℝ} {r : ℝ} (hr : 0 < r)
    (hint : ∀ t ∈ Set.Ioi (0:ℝ),
      IntervalIntegrable (oddExt g) MeasureTheory.volume (r - t) (r + t)) :
    radial3d_conv f g r =
      (2 * Real.pi / r) * ∫ t in Set.Ioi (0:ℝ), t * f t * ∫ s in (r - t)..(r + t), oddExt g s := by
  unfold radial3d_conv
  rw [if_neg (not_le.mpr hr)]
  congr 1
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
  intro t ht
  dsimp only []
  have ht0 : (0:ℝ) ≤ t := (Set.mem_Ioi.mp ht).le
  have hlt : |r - t| ≤ r + t := by
    rw [abs_le]; constructor <;> linarith
  have hIcc : (∫ s in Set.Icc (|r - t|) (r + t), s * g s) = ∫ s in (|r - t|)..(r + t), s * g s := by
    rw [intervalIntegral.integral_of_le hlt, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [hIcc, integral_shell_eq_oddExt hr.le ht0 (hint t ht)]

/-! ### `OZFIX.16` — the analytic half: differentiating under the `t`-integral

With `radial3d_conv_eq_oddExt` the shell is `∫_{r-t}^{r+t} g̃`, whose `r`-derivative is
`g̃(r+t) - g̃(r-t)` by the FTC. Pushing that derivative through the `t`-integral and folding the
result with `oddExt_conv_fold` gives the bridge `d/dr[r·(f ⊛₃ g)(r)] = -2π·(f̃ ⋆ g̃)(r)`.

**Why the FTC endpoints, and not a global smoothness hypothesis, are the right currency.** The
physical `g` is `oz_h`, which *jumps at contact* (`|v| = σ`), so `g̃` is not continuous and no
"differentiate a smooth integrand" lemma applies. The escape is that
`hasDerivAt_integral_of_dominated_loc_of_lip` demands `HasDerivAt` **only at the base point `r`**,
and only for **a.e. `t`** — whereas the more familiar
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` would demand it for all `x` in a ball, which is
*false* here (for each `t` the shell fails to be differentiable at the isolated `x` with
`x ± t = ±σ`, and every ball around `r` catches a positive-measure set of such `t`). At a fixed `r`
only the two values `t = |σ ∓ r|` are bad — a measure-zero set of `t`. Regularity across the ball is
supplied instead by the *Lipschitz* hypothesis `h_lip`, which a jump does not destroy. -/

/-- A locally integrable function is interval-integrable on every interval (`Ι a b ⊆ uIcc a b`,
which is compact). -/
theorem intervalIntegrable_of_locallyIntegrable {φ : ℝ → ℝ}
    (hφ : MeasureTheory.LocallyIntegrable φ) (a b : ℝ) :
    IntervalIntegrable φ MeasureTheory.volume a b := by
  rw [intervalIntegrable_iff]
  exact (hφ.integrableOn_isCompact isCompact_uIcc).mono_set Set.Ioc_subset_Icc_self

/-- **`OZFIX.16` analytic brick 1 — the FTC on the shell.**

`d/dx ∫_{x-t}^{x+t} φ = φ(r+t) - φ(r-t)` at `x = r`, needing continuity of `φ` **only at the two
endpoints** `r ± t`. Both halves are `integral_hasDerivAt_right` against a common base point,
composed with `x ↦ x ± t`. -/
theorem hasDerivAt_shell {φ : ℝ → ℝ} {r t : ℝ}
    (hφ : MeasureTheory.LocallyIntegrable φ)
    (hcp : ContinuousAt φ (r + t)) (hcm : ContinuousAt φ (r - t)) :
    HasDerivAt (fun x => ∫ s in (x - t)..(x + t), φ s) (φ (r + t) - φ (r - t)) r := by
  have hmeas : ∀ x : ℝ, StronglyMeasurableAtFilter φ (nhds x) := fun x =>
    ⟨Set.univ, Filter.univ_mem, by
      rw [MeasureTheory.Measure.restrict_univ]; exact hφ.aestronglyMeasurable⟩
  set G : ℝ → ℝ := fun u => ∫ s in (0:ℝ)..u, φ s with hGdef
  have hGp : HasDerivAt G (φ (r + t)) (r + t) :=
    intervalIntegral.integral_hasDerivAt_right
      (intervalIntegrable_of_locallyIntegrable hφ 0 (r + t)) (hmeas _) hcp
  have hGm : HasDerivAt G (φ (r - t)) (r - t) :=
    intervalIntegral.integral_hasDerivAt_right
      (intervalIntegrable_of_locallyIntegrable hφ 0 (r - t)) (hmeas _) hcm
  have hdp : HasDerivAt (fun x : ℝ => G (x + t)) (φ (r + t)) r := hGp.comp_add_const r t
  have hdm : HasDerivAt (fun x : ℝ => G (x - t)) (φ (r - t)) r := hGm.comp_sub_const r t
  refine (hdp.sub hdm).congr_of_eventuallyEq ?_
  filter_upwards with x
  rw [hGdef]
  exact (intervalIntegral.integral_interval_sub_left
    (intervalIntegrable_of_locallyIntegrable hφ 0 (x + t))
    (intervalIntegrable_of_locallyIntegrable hφ 0 (x - t))).symm

set_option maxHeartbeats 1000000 in
/-- **`OZFIX.16` analytic brick 2 — differentiation under the `t`-integral.**

The `r`-derivative of `∫_{Ioi 0} t·f(t)·(∫_{x-t}^{x+t} g̃)` is obtained by moving `d/dx` inside, via
`hasDerivAt_integral_of_dominated_loc_of_lip`. The domination data (`s`, `bound`, `h_lip`) is left as
hypotheses: for the FMSA consumers `f` is compactly supported (`q0_poly` on `[0,σ]`) and `g̃` is
locally bounded, so `bound t := |t·f t|·2·(sup |g̃| near r)` discharges them. The `hcont` hypothesis
is the a.e.-in-`t` endpoint continuity of brick 1 — satisfied by a jump function like `g̃` because,
at fixed `r`, only `t = |σ ∓ r|` is bad. -/
theorem hasDerivAt_tIntegral_shell {f g : ℝ → ℝ} {r : ℝ} {bound : ℝ → ℝ} {s : Set ℝ}
    (hg : MeasureTheory.LocallyIntegrable (oddExt g))
    (hs : s ∈ nhds r)
    (hF_meas : ∀ᶠ x in nhds r, MeasureTheory.AEStronglyMeasurable
      (fun t => t * f t * ∫ u in (x - t)..(x + t), oddExt g u)
      (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hF_int : MeasureTheory.IntegrableOn
      (fun t => t * f t * ∫ u in (r - t)..(r + t), oddExt g u) (Set.Ioi 0))
    (hF'_meas : MeasureTheory.AEStronglyMeasurable
      (fun t => t * f t * (oddExt g (r + t) - oddExt g (r - t)))
      (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (h_lip : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))),
      LipschitzOnWith (Real.nnabs (bound t))
        (fun x => t * f t * ∫ u in (x - t)..(x + t), oddExt g u) s)
    (hbound : MeasureTheory.IntegrableOn bound (Set.Ioi 0))
    (hcont : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))),
      ContinuousAt (oddExt g) (r + t) ∧ ContinuousAt (oddExt g) (r - t)) :
    HasDerivAt (fun x => ∫ t in Set.Ioi (0:ℝ), t * f t * ∫ u in (x - t)..(x + t), oddExt g u)
      (∫ t in Set.Ioi (0:ℝ), t * f t * (oddExt g (r + t) - oddExt g (r - t))) r := by
  refine (hasDerivAt_integral_of_dominated_loc_of_lip (μ := MeasureTheory.volume.restrict
      (Set.Ioi (0:ℝ))) (bound := bound) (s := s) (x₀ := r)
    (F := fun x t => t * f t * ∫ u in (x - t)..(x + t), oddExt g u)
    (F' := fun t => t * f t * (oddExt g (r + t) - oddExt g (r - t)))
    hs hF_meas hF_int hF'_meas h_lip hbound ?_).2
  filter_upwards [hcont] with t ht
  exact (hasDerivAt_shell hg ht.1 ht.2).const_mul (t * f t)

/-- **`OZFIX.16` — the `1D-odd ↔ 3D-radial` bridge.**

  `d/dr [ r · (f ⊛₃ g)(r) ] = -2π · (f̃ ⋆ g̃)(r)`

The 3D radial convolution, once weighted by `r` and differentiated, **is** an ordinary 1D
convolution of the odd extensions. This is what turns the real-space Baxter identity
`ψ ⋆ Q₊ ⋆ Q₋ = φ` (a 1D statement, `OZFIX.15`) into the OZ equation for all `r > 0` (a 3D
statement) — the two sides of `OZFIX.17`'s chain.

Assembled from the three pieces: `radial3d_conv_eq_oddExt` (kill the `|r-t|`), brick 2
`hasDerivAt_tIntegral_shell` (move `d/dr` inside the `t`-integral, its inner FTC being brick 1
`hasDerivAt_shell`), and `oddExt_conv_fold` (fold the two half-lines into one 1D convolution). The
`hint` hypothesis of `radial3d_conv_eq_oddExt` is discharged here from `hg` alone.

The bridge is **non-circular** — it is pure analysis (`OZFIX.2`'s proved WH factorization + this
convolution identity), with no physics input, so `OZFIX.14`'s value-neutrality trap does not apply. -/
theorem hasDerivAt_radial3d_conv_bridge {f g : ℝ → ℝ} {r : ℝ} {bound : ℝ → ℝ} {s : Set ℝ}
    (hr : 0 < r)
    (hg : MeasureTheory.LocallyIntegrable (oddExt g))
    (hs : s ∈ nhds r)
    (hF_meas : ∀ᶠ x in nhds r, MeasureTheory.AEStronglyMeasurable
      (fun t => t * f t * ∫ u in (x - t)..(x + t), oddExt g u)
      (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hF_int : MeasureTheory.IntegrableOn
      (fun t => t * f t * ∫ u in (r - t)..(r + t), oddExt g u) (Set.Ioi 0))
    (hF'_meas : MeasureTheory.AEStronglyMeasurable
      (fun t => t * f t * (oddExt g (r + t) - oddExt g (r - t)))
      (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (h_lip : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))),
      LipschitzOnWith (Real.nnabs (bound t))
        (fun x => t * f t * ∫ u in (x - t)..(x + t), oddExt g u) s)
    (hbound : MeasureTheory.IntegrableOn bound (Set.Ioi 0))
    (hcont : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))),
      ContinuousAt (oddExt g) (r + t) ∧ ContinuousAt (oddExt g) (r - t))
    (hconv : MeasureTheory.Integrable (fun t => oddExt f t * oddExt g (r - t))) :
    HasDerivAt (fun x => x * radial3d_conv f g x)
      (-(2 * Real.pi) * ∫ t, oddExt f t * oddExt g (r - t)) r := by
  have key :=
    (hasDerivAt_tIntegral_shell hg hs hF_meas hF_int hF'_meas h_lip hbound hcont).const_mul
      (2 * Real.pi)
  have hval : (2 * Real.pi) *
      (∫ t in Set.Ioi (0:ℝ), t * f t * (oddExt g (r + t) - oddExt g (r - t)))
      = -(2 * Real.pi) * ∫ t, oddExt f t * oddExt g (r - t) := by
    rw [oddExt_conv_fold (f := f) (g := g) (r := r) hconv]; ring
  rw [hval] at key
  refine key.congr_of_eventuallyEq ?_
  filter_upwards [eventually_gt_nhds hr] with x hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  rw [radial3d_conv_eq_oddExt hx (fun t _ => intervalIntegrable_of_locallyIntegrable hg _ _)]
  field_simp

/-! ### Baxter's `K` function — the object that makes the factorization a *real-space* identity

`OZFIX.17` must turn `ψ ⋆ Q₊ ⋆ Q₋ = φ` (`baxter_psi_conv_eq_phi`) into OZ, using the proved
factorization `(1 - Q̂(k))(1 - Q̂(-k)) = 1 - ρĈ(k)` (`OZFIX.2`, `baxter_wiener_hopf_complex`). The
subtlety that decides the whole route: **`Q̂` is a 1D transform but `Ĉ` is a 3D radial one**
(`radial_fourier`), so `1 - ρĈ(k)` is *not* the transform of `δ - ρ·c̃`. The two differ by the
multiplier `2πi/k` — an **antiderivative** — which is exactly the `d/dr` sitting on the left of
`OZFIX.16`'s bridge.

The object that repairs this is Baxter's `K`:

  `K(v) := 2π ∫_{|v|}^σ s·c_HS(s) ds`,   and then   `F[K](k) = radial_fourier(c_HS)(k) = Ĉ(k)`

(integrate by parts: the boundary term dies and `(4π/k)∫₀^∞ s·c(s) sin(ks) ds` reappears). So the
real-space factorization reads `Q₊ ⋆ Q₋ = δ - ρ·K`, and `ψ ⋆ (δ - ρK) = φ` is `ψ = φ + ρ·(ψ ⋆ K)`
— which is `r·h(r) = r·c(r) + ρ·r·(c ⊛₃ h)(r)`, i.e. **OZ**, via the *antiderivative form* of the
bridge `r·(f ⊛₃ g)(r) = (g̃ ⋆ K_f)(r)`.

Two facts below make this concrete and show `K` is the right object: `K` is **compactly supported**
(no improper integral — `c_HS` vanishes off `[0,σ]`), and `K' = -2π·c̃` on `(0,∞)`, which is precisely
`OZFIX.16`'s bridge integrand. `OZFIX.16` is the *derivative* of the identity `OZFIX.17` needs. -/

/-- **Baxter's `K` function**, `K(v) := 2π ∫_{|v|}^σ s·c_HS(s) ds`.  Even by construction, and
compactly supported because `c_HS` is. -/
def baxterK (eta sigma : ℝ) (v : ℝ) : ℝ :=
  2 * Real.pi * ∫ s in |v|..sigma, s * c_HS eta sigma s

@[simp] theorem baxterK_neg (eta sigma : ℝ) (v : ℝ) :
    baxterK eta sigma (-v) = baxterK eta sigma v := by
  unfold baxterK; rw [abs_neg]

/-- `K` vanishes off the core — so no improper integral ever appears. -/
theorem baxterK_outer {eta sigma : ℝ} {v : ℝ} (hv : sigma ≤ |v|) : baxterK eta sigma v = 0 := by
  unfold baxterK
  have h : (∫ s in |v|..sigma, s * c_HS eta sigma s) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) ?_, intervalIntegral.integral_zero]
    intro s hs
    rw [Set.uIcc_of_ge hv] at hs
    dsimp only []
    rw [c_HS_outer hs.1, mul_zero]
  rw [h, mul_zero]

/-- **`K' = -2π·c̃` on the core `(0,σ)`** — `K` is an antiderivative of `OZFIX.16`'s bridge integrand.

This is the precise sense in which `OZFIX.16` (`d/dr[r·(f ⊛₃ g)] = -2π·(f̃ ⋆ g̃)`) is the
*differentiated* form of the identity `OZFIX.17` needs (`r·(f ⊛₃ g)(r) = (g̃ ⋆ K_f)(r)`): the two
differ by an antiderivative, and `K` supplies it with the constant already pinned (both sides vanish
off the core, by `baxterK_outer`).

**`v < σ` is not a convenience hypothesis.** `c_HS` **jumps at contact** (`c_HS_inner` vs
`c_HS_outer`), so `s ↦ s·c_HS(s)` is *not* continuous and the FTC's `ContinuousAt` genuinely fails at
`v = σ`. The same jump is why integrability on `[v,σ]` has to be routed through an a.e. congruence
with the *polynomial* branch rather than `Continuous.intervalIntegrable` — the bad set is again the
single endpoint `σ`. (For `v > σ`, `K ≡ 0` near `v` by `baxterK_outer`, so the derivative is `0`
there and the interesting content is exactly the core statement below.) -/
theorem hasDerivAt_baxterK {eta sigma : ℝ} {v : ℝ} (hv0 : 0 < v) (hvs : v < sigma) :
    HasDerivAt (baxterK eta sigma) (-(2 * Real.pi) * oddExt (c_HS eta sigma) v) v := by
  set cpoly : ℝ → ℝ := fun s =>
    s * (-(py_a0 eta + py_a1 eta * (s / sigma) + py_a3 eta * (s / sigma) ^ 3)) with hcpoly
  have hcontpoly : Continuous cpoly := by unfold cpoly; fun_prop
  -- `s·c_HS(s)` agrees with the polynomial branch strictly below `σ`
  have heqOn : Set.EqOn cpoly (fun s : ℝ => s * c_HS eta sigma s) (Set.Iio sigma) := by
    intro s hs
    rw [hcpoly]
    dsimp only []
    rw [c_HS_inner hs]
  -- integrability on `[v,σ]`: a.e. equal to the continuous polynomial branch (bad set = `{σ}`)
  have hae : (fun s : ℝ => s * c_HS eta sigma s)
      =ᵐ[MeasureTheory.volume.restrict (Set.Ioc v sigma)] cpoly := by
    rw [← MeasureTheory.Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with s hs
    exact (heqOn hs.2).symm
  have hII : IntervalIntegrable (fun s : ℝ => s * c_HS eta sigma s)
      MeasureTheory.volume v sigma := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hvs.le]
    exact ((hcontpoly.integrableOn_Icc (a := v) (b := sigma)).mono_set
      Set.Ioc_subset_Icc_self).congr_fun_ae hae.symm
  -- near `v` the function *is* the polynomial branch
  have hnear : ∀ᶠ s in nhds v, cpoly s = s * c_HS eta sigma s := by
    filter_upwards [Iio_mem_nhds hvs] with s hs
    exact heqOn hs
  have hca : ContinuousAt (fun s : ℝ => s * c_HS eta sigma s) v :=
    hcontpoly.continuousAt.congr hnear
  have hsmaf : StronglyMeasurableAtFilter (fun s : ℝ => s * c_HS eta sigma s) (nhds v) := by
    refine ⟨Set.Iio sigma, Iio_mem_nhds hvs, ?_⟩
    refine (hcontpoly.aestronglyMeasurable.restrict (s := Set.Iio sigma)).congr ?_
    exact heqOn.eventuallyEq_of_mem (MeasureTheory.self_mem_ae_restrict measurableSet_Iio)
  have hleft : HasDerivAt (fun x : ℝ => ∫ s in x..sigma, s * c_HS eta sigma s)
      (-(v * c_HS eta sigma v)) v :=
    intervalIntegral.integral_hasDerivAt_left hII hsmaf hca
  -- on `(0,∞)` the `|·|` in `baxterK` is inert
  have habs : baxterK eta sigma
      =ᶠ[nhds v] (fun x => (2 * Real.pi) * ∫ s in x..sigma, s * c_HS eta sigma s) := by
    filter_upwards [eventually_gt_nhds hv0] with x hx
    unfold baxterK; rw [abs_of_pos hx]
  refine HasDerivAt.congr_of_eventuallyEq ?_ habs
  rw [oddExt_of_nonneg hv0.le]
  exact (hleft.const_mul (2 * Real.pi)).congr_deriv (by ring)

/-- **`OZFIX.18` sub-lemma — `F[K] = Ĉ`.**

  `2 ∫₀^σ K(v)·cos(kv) dv = radial_fourier(c_HS)(k)`   for `k ≠ 0`.

The left side is `F[K](k)` (`K` is even, so `∫_ℝ K·cos = 2∫₀^∞ K·cos`, and `K` is supported on
`[0,σ]`); the right is Baxter's `Ĉ`. This is the identity that lets the *Fourier-side* factorization
`(1-Q̂)(1-Q̂(-k)) = 1-ρĈ` (`OZFIX.2`) be read in **real space** as `Q₊ ⋆ Q₋ = δ - ρ·K`
(`OZFIX.18`): it matches `ρĈ` with `F[ρK]`.

Proof = **one integration by parts**, using the already-proved `hasDerivAt_baxterK` (`K' =
-2π·c̃`): with `v ↦ sin(kv)/k` (whose derivative is `cos(kv)`), the boundary term `[K·sin(kv)/k]₀^σ`
vanishes (`K(σ)=0` by `baxterK_outer`, `sin(0)=0`), leaving `∫₀^σ K·cos = (2π/k)∫₀^σ v·c(v)·sin(kv)`,
and the `2·` and the support reduction `∫_{Ioi 0} = ∫₀^σ` finish it. **No decay needed** — `K` and
`c_HS` are compactly supported, so every integral is proper. -/
theorem baxterK_cos_eq_radial_fourier {eta sigma : ℝ} (hsigma : 0 < sigma) {k : ℝ} (hk : k ≠ 0) :
    2 * ∫ v in (0:ℝ)..sigma, baxterK eta sigma v * Real.cos (k * v)
      = radial_fourier (c_HS eta sigma) k := by
  set polyC : ℝ → ℝ :=
    fun s => s * (-(py_a0 eta + py_a1 eta * (s / sigma) + py_a3 eta * (s / sigma) ^ 3)) with hpolyC
  have hcontpolyC : Continuous polyC := by rw [hpolyC]; fun_prop
  set Kp : ℝ → ℝ := fun v => -(2 * Real.pi) * oddExt (c_HS eta sigma) v with hKp
  -- `s ↦ s·c_HS(s)` is interval-integrable on `[0,σ]` (a.e. the polynomial branch)
  have hcHS_II : IntervalIntegrable (fun s : ℝ => s * c_HS eta sigma s)
      MeasureTheory.volume 0 sigma := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hsigma.le]
    have hae : (fun s : ℝ => s * c_HS eta sigma s)
        =ᵐ[MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) sigma)] polyC := by
      rw [← MeasureTheory.Measure.restrict_congr_set Ioo_ae_eq_Ioc]
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with s hs
      rw [hpolyC, c_HS_inner hs.2]
    exact ((hcontpolyC.integrableOn_Icc (a := 0) (b := sigma)).mono_set
      Set.Ioc_subset_Icc_self).congr_fun_ae hae.symm
  -- `Kp = -2π·(s·c_HS)` on `[0,σ]` (oddExt of a nonneg argument), hence interval-integrable
  have hKp_II : IntervalIntegrable Kp MeasureTheory.volume 0 sigma := by
    have hbase : IntervalIntegrable (fun s : ℝ => -(2 * Real.pi) * (s * c_HS eta sigma s))
        MeasureTheory.volume 0 sigma := hcHS_II.const_mul _
    refine hbase.congr ?_
    rw [Set.uIoc_of_le hsigma.le]
    intro s hs
    simp only [hKp, oddExt_of_nonneg (le_of_lt hs.1)]
  -- continuity of `K` on `[0,σ]` — it equals `2π·(-∫_σ^v polyC)` there (an antiderivative)
  have hKcont : ContinuousOn (baxterK eta sigma) (Set.uIcc (0:ℝ) sigma) := by
    have hEqOn : Set.EqOn (baxterK eta sigma)
        (fun v => 2 * Real.pi * (-(∫ s in sigma..v, polyC s))) (Set.uIcc (0:ℝ) sigma) := by
      intro v hv
      rw [Set.uIcc_of_le hsigma.le] at hv
      have hcong : (∫ s in v..sigma, s * c_HS eta sigma s) = ∫ s in v..sigma, polyC s := by
        refine intervalIntegral.integral_congr_ae ?_
        rw [Set.uIoc_of_le hv.2]
        have hne : ∀ᵐ (x : ℝ), x ≠ sigma := by
          rw [MeasureTheory.ae_iff]; simpa using MeasureTheory.measure_singleton sigma
        filter_upwards [hne] with s hs hmem
        rw [hpolyC, c_HS_inner (lt_of_le_of_ne hmem.2 hs)]
      show baxterK eta sigma v = 2 * Real.pi * (-(∫ s in sigma..v, polyC s))
      rw [baxterK, abs_of_nonneg hv.1, hcong, intervalIntegral.integral_symm v sigma]
      ring
    refine (Continuous.continuousOn ?_).congr hEqOn
    exact (((intervalIntegral.continuous_primitive
      (fun a b => hcontpolyC.intervalIntegrable a b) sigma).neg).const_mul (2 * Real.pi))
  -- IBP against `w := sin(k·)/k` (whose derivative is `cos(k·)`)
  set w : ℝ → ℝ := fun x => Real.sin (k * x) / k with hw
  set w' : ℝ → ℝ := fun x => Real.cos (k * x) with hw'
  have hwderiv : ∀ x, HasDerivAt w (w' x) x := by
    intro x
    have hlin : HasDerivAt (fun x => k * x) k x := by
      simpa using (hasDerivAt_id x).const_mul k
    have h1 : HasDerivAt (fun x => Real.sin (k * x)) (Real.cos (k * x) * k) x := hlin.sin
    have h2 : HasDerivAt w (Real.cos (k * x) * k / k) x := h1.div_const k
    rw [hw']
    exact h2.congr_deriv (by field_simp)
  have hwcont : Continuous w := by rw [hw]; fun_prop
  have hw'cont : Continuous w' := by rw [hw']; fun_prop
  -- the integration-by-parts identity: boundary terms vanish
  have hibp := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt
    (u := baxterK eta sigma) (v := w) (u' := Kp) (v' := w')
    hKcont hwcont.continuousOn
    (fun x hx => by
      rw [min_eq_left hsigma.le, max_eq_right hsigma.le] at hx
      exact hasDerivAt_baxterK hx.1 hx.2)
    (fun x _ => hwderiv x)
    hKp_II (hw'cont.intervalIntegrable _ _)
  -- boundary term is 0: `baxterK σ = 0` and `w 0 = 0`
  have hKsigma : baxterK eta sigma sigma = 0 := baxterK_outer (by rw [abs_of_pos hsigma])
  have hw0 : w 0 = 0 := by rw [hw]; simp
  rw [hKsigma, hw0] at hibp
  simp only [zero_mul, mul_zero, sub_zero] at hibp
  -- split the sum, giving `∫ K·cos = -∫ Kp·w`
  have hI1 : IntervalIntegrable (fun x => Kp x * w x) MeasureTheory.volume 0 sigma :=
    hKp_II.mul_continuousOn hwcont.continuousOn
  have hI2 : IntervalIntegrable (fun x => baxterK eta sigma x * w' x) MeasureTheory.volume 0 sigma :=
    (hw'cont.intervalIntegrable 0 sigma).continuousOn_mul hKcont
  rw [intervalIntegral.integral_add hI1 hI2] at hibp
  have hmain : (∫ x in (0:ℝ)..sigma, baxterK eta sigma x * w' x)
      = -(∫ x in (0:ℝ)..sigma, Kp x * w x) := by linarith [hibp]
  -- rewrite `-∫ Kp·w` as `(2π/k)·∫ x·c_HS(x)·sin(kx)`
  have hrhs : -(∫ x in (0:ℝ)..sigma, Kp x * w x)
      = (2 * Real.pi / k) * ∫ x in (0:ℝ)..sigma, x * c_HS eta sigma x * Real.sin (k * x) := by
    rw [← intervalIntegral.integral_neg, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr ?_
    intro x hx
    rw [Set.uIcc_of_le hsigma.le] at hx
    simp only [hKp, hw, oddExt_of_nonneg hx.1]
    field_simp
  rw [hrhs] at hmain
  rw [radial_fourier_c_HS_eq_intervalIntegral eta sigma k hsigma]
  rw [show (fun x => baxterK eta sigma x * w' x) = fun x => baxterK eta sigma x * Real.cos (k * x)
    from rfl] at hmain
  rw [hmain]
  ring

/-- **`OZFIX.18` — the real-space Baxter factorization, core form.**

  `ρ·K(v) = q0(v) − ∫_v^σ q0(t)·q0(t−v) dt`   for `v ∈ (0,σ)`.

This is the real-space content of `(1 − Q̂(k))(1 − Q̂(−k)) = 1 − ρĈ(k)` (`OZFIX.2`): writing
`Q₊ = δ − q0·1_{[0,σ]}`, `Q₋(v) = Q₊(−v)`, the factor product is `Q₊ ⋆ Q₋ = δ − ρK`, whose core
slice (`0<v<σ`) reads exactly as above (the double integral is `(q0·1_{[0,σ]} ⋆ q0(−·)·1_{[−σ,0]})(v)
= ∫_v^σ q0(t)q0(t−v)dt`).

**Proof: two FTC evaluations + `ring`** (no Fourier, no injectivity), mirroring
`baxter_factorization_inner`.  `K(v) = 2π∫_v^σ s·c(s)ds` with `s·c(s)` the degree-4 inner polynomial
(antiderivative `Gpoly`); `∫_v^σ q0(t)q0(t−v)dt` has the degree-5 antiderivative `Fpoly`.  Both are
polynomial identities in `η,σ,ρ,π` closed by `field_simp`/`ring` under `heta_def`.  Numerically and
symbolically verified before formalizing (5 param sets to `1e-15`; sympy `LHS−RHS ≡ 0`). -/
theorem rho_baxterK_eq_q0_self_conv {eta sigma rho : ℝ} (hsigma : 0 < sigma) (heta : eta < 1)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) {v : ℝ} (hv : v ∈ Set.Ioo (0:ℝ) sigma) :
    rho * baxterK eta sigma v
      = q0_poly eta sigma rho v
        - ∫ t in v..sigma, q0_poly eta sigma rho t * q0_poly eta sigma rho (t - v) := by
  obtain ⟨hv0, hvs⟩ := hv
  set α := rho * q_prime_py eta sigma with hα
  set β := rho * q_doubleprime_py eta with hβ
  have hσ : sigma ≠ 0 := ne_of_gt hsigma
  -- (1) baxterK(v) = 2π (Gpoly σ − Gpoly v)
  set Gpoly : ℝ → ℝ := fun s => -(py_a0 eta * s ^ 2 / 2 + py_a1 eta * s ^ 3 / (3 * sigma)
    + py_a3 eta * s ^ 5 / (5 * sigma ^ 3)) with hGdef
  have hcHSint : (∫ s in v..sigma, s * c_HS eta sigma s) = Gpoly sigma - Gpoly v := by
    have hne : ∀ᵐ (x : ℝ), x ≠ sigma := by
      rw [MeasureTheory.ae_iff]; simpa using MeasureTheory.measure_singleton sigma
    rw [intervalIntegral.integral_congr_ae (g := fun s => s * (-(py_a0 eta + py_a1 eta * (s / sigma)
        + py_a3 eta * (s / sigma) ^ 3))) ?_]
    · refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => ?_) ?_
      · have h2 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * s) s := by simpa using hasDerivAt_pow 2 s
        have h3 : HasDerivAt (fun s : ℝ => s ^ 3) (3 * s ^ 2) s := by simpa using hasDerivAt_pow 3 s
        have h5 : HasDerivAt (fun s : ℝ => s ^ 5) (5 * s ^ 4) s := by simpa using hasDerivAt_pow 5 s
        have hd := (((h2.const_mul (py_a0 eta / 2)).add
          (h3.const_mul (py_a1 eta / (3 * sigma)))).add
          (h5.const_mul (py_a3 eta / (5 * sigma ^ 3)))).neg
        rw [hGdef]
        refine (hd.congr_of_eventuallyEq ?_).congr_deriv ?_
        · filter_upwards with y
          simp only [Pi.neg_apply, Pi.add_apply]
          ring
        · field_simp
      · apply Continuous.intervalIntegrable; fun_prop
    · rw [Set.uIoc_of_le hvs.le]
      filter_upwards [hne] with s hs hmem
      rw [c_HS_inner (lt_of_le_of_ne hmem.2 hs)]
  have hbaxK : baxterK eta sigma v = 2 * Real.pi * (Gpoly sigma - Gpoly v) := by
    rw [baxterK, abs_of_pos hv0, hcHSint]
  -- (2) ∫_v^σ q0(t)q0(t-v) dt = Fpoly σ − Fpoly v
  set Fpoly : ℝ → ℝ := fun x =>
    β ^ 2 / 20 * x ^ 5
      + (α * β / 4 - β ^ 2 * sigma / 4 - β ^ 2 * v / 8) * x ^ 4
      + (α ^ 2 / 3 - α * β * sigma - α * β * v / 2 + β ^ 2 * sigma ^ 2 / 2
          + β ^ 2 * sigma * v / 2 + β ^ 2 * v ^ 2 / 12) * x ^ 3
      + (-(α ^ 2 * sigma) - α ^ 2 * v / 2 + 3 * α * β * sigma ^ 2 / 2 + 3 * α * β * sigma * v / 2
          + α * β * v ^ 2 / 4 - β ^ 2 * sigma ^ 3 / 2 - 3 * β ^ 2 * sigma ^ 2 * v / 4
          - β ^ 2 * sigma * v ^ 2 / 4) * x ^ 2
      + (α ^ 2 * sigma ^ 2 + α ^ 2 * sigma * v - α * β * sigma ^ 3 - 3 * α * β * sigma ^ 2 * v / 2
          - α * β * sigma * v ^ 2 / 2 + β ^ 2 * sigma ^ 4 / 4 + β ^ 2 * sigma ^ 3 * v / 2
          + β ^ 2 * sigma ^ 2 * v ^ 2 / 4) * x
    with hFdef
  have hprodint : (∫ t in v..sigma, q0_poly eta sigma rho t * q0_poly eta sigma rho (t - v))
      = Fpoly sigma - Fpoly v := by
    have hcongr : (∫ t in v..sigma, q0_poly eta sigma rho t * q0_poly eta sigma rho (t - v))
        = ∫ t in v..sigma, (α * (t - sigma) + β * (t - sigma) ^ 2 / 2)
            * (α * (t - v - sigma) + β * (t - v - sigma) ^ 2 / 2) := by
      refine intervalIntegral.integral_congr ?_
      intro t ht
      rw [Set.uIcc_of_le hvs.le] at ht
      show q0_poly eta sigma rho t * q0_poly eta sigma rho (t - v)
        = (α * (t - sigma) + β * (t - sigma) ^ 2 / 2)
          * (α * (t - v - sigma) + β * (t - v - sigma) ^ 2 / 2)
      rw [q0_poly_inner ht.2, q0_poly_inner (by linarith [ht.2, hv0.le] : t - v ≤ sigma), ← hα, ← hβ]
    rw [hcongr]
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => ?_) ?_
    · have hp : ∀ n : ℕ, HasDerivAt (fun x : ℝ => x ^ n) (n * t ^ (n - 1)) t :=
        fun n => hasDerivAt_pow n t
      have h1 : HasDerivAt (fun x : ℝ => x) 1 t := hasDerivAt_id t
      have h2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * t) t := by simpa using hasDerivAt_pow 2 t
      have h3 : HasDerivAt (fun x : ℝ => x ^ 3) (3 * t ^ 2) t := by simpa using hasDerivAt_pow 3 t
      have h4 : HasDerivAt (fun x : ℝ => x ^ 4) (4 * t ^ 3) t := by simpa using hasDerivAt_pow 4 t
      have h5 : HasDerivAt (fun x : ℝ => x ^ 5) (5 * t ^ 4) t := by simpa using hasDerivAt_pow 5 t
      have hd := ((((h5.const_mul (β ^ 2 / 20)).add
        (h4.const_mul (α * β / 4 - β ^ 2 * sigma / 4 - β ^ 2 * v / 8))).add
        (h3.const_mul (α ^ 2 / 3 - α * β * sigma - α * β * v / 2 + β ^ 2 * sigma ^ 2 / 2
          + β ^ 2 * sigma * v / 2 + β ^ 2 * v ^ 2 / 12))).add
        (h2.const_mul (-(α ^ 2 * sigma) - α ^ 2 * v / 2 + 3 * α * β * sigma ^ 2 / 2
          + 3 * α * β * sigma * v / 2 + α * β * v ^ 2 / 4 - β ^ 2 * sigma ^ 3 / 2
          - 3 * β ^ 2 * sigma ^ 2 * v / 4 - β ^ 2 * sigma * v ^ 2 / 4))).add
        (h1.const_mul (α ^ 2 * sigma ^ 2 + α ^ 2 * sigma * v - α * β * sigma ^ 3
          - 3 * α * β * sigma ^ 2 * v / 2 - α * β * sigma * v ^ 2 / 2 + β ^ 2 * sigma ^ 4 / 4
          + β ^ 2 * sigma ^ 3 * v / 2 + β ^ 2 * sigma ^ 2 * v ^ 2 / 4))
      rw [hFdef]
      refine (hd.congr_of_eventuallyEq ?_).congr_deriv ?_
      · filter_upwards with y
        simp only [Pi.add_apply]
      · ring
    · apply Continuous.intervalIntegrable; fun_prop
  -- (3) assemble and close by ring under heta_def
  rw [hbaxK, hprodint, q0_poly_inner hvs.le]
  simp only [hGdef, hFdef, hα, hβ, q_prime_py, q_doubleprime_py, py_a0, py_a1, py_a3]
  have h1e : (1 : ℝ) - eta ≠ 0 := by
    rw [sub_ne_zero]; exact fun h => absurd h.symm (ne_of_lt heta)
  rw [heta_def]
  field_simp
  ring

/-! ### `OZFIX.19` — the antiderivative bridge is just Fubini

`r·(c_HS ⊛₃ g)(r) = (K ⋆ g̃)(r)`, the un-differentiated `OZFIX.16`.  **Not a differentiation
argument** — expanding `K(u) = 2π∫_{|u|}^σ s·c(s)ds` and swapping the order of the resulting double
integral turns `K ⋆ g̃` straight into `radial3d_conv`'s shell form.  Fubini (not IBP) is the robust
tool here because `g̃ = ψ` **jumps** at `±σ`, which would break any differentiate-in-`u` route at the
interior point `u = σ − r` — but the swap only needs integrability, which a jump does not spoil. -/

/-- **Triangle Fubini on `[0,a]`**: `∫₀^a (∫_u^a p) q(u) du = ∫₀^a p(s) (∫₀^s q) ds`.

The joint integrability of `(u,s) ↦ 1_{u<s}·p(s)·q(u)` on `(0,a]²` is the only hypothesis — for the
`OZFIX.19` use `p = s·c(s)` and `q` are bounded on the compact, so it is discharged by boundedness. -/
theorem intervalIntegral_triangle_swap {a : ℝ} (ha : 0 ≤ a) (p q : ℝ → ℝ)
    (hint : MeasureTheory.Integrable
      (Function.uncurry fun u s => (Set.Ioi u).indicator p s * q u)
      ((MeasureTheory.volume.restrict (Set.Ioc 0 a)).prod
        (MeasureTheory.volume.restrict (Set.Ioc 0 a)))) :
    (∫ u in (0:ℝ)..a, (∫ s in u..a, p s) * q u)
      = ∫ s in (0:ℝ)..a, p s * ∫ u in (0:ℝ)..s, q u := by
  have hmeasp : ∀ u : ℝ, MeasurableSet (Set.Ioi u) := fun u => measurableSet_Ioi
  -- LHS as an iterated integral over `Ioc 0 a`, inner slice via the `Ioi u` indicator
  have hLHS : (∫ u in (0:ℝ)..a, (∫ s in u..a, p s) * q u)
      = ∫ u in Set.Ioc 0 a, (∫ s in Set.Ioc 0 a, (Set.Ioi u).indicator p s) * q u := by
    rw [intervalIntegral.integral_of_le ha]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc ?_
    intro u hu
    have hua : u ≤ a := hu.2
    have hInter : Set.Ioc 0 a ∩ Set.Ioi u = Set.Ioc u a := by
      ext s
      simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ioc]
      constructor
      · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨hu.1.trans h1, h2⟩, h1⟩
    have hslice : (∫ s in u..a, p s) = ∫ s in Set.Ioc 0 a, (Set.Ioi u).indicator p s := by
      rw [intervalIntegral.integral_of_le hua,
        MeasureTheory.setIntegral_indicator (hmeasp u), hInter]
    show (∫ s in u..a, p s) * q u = (∫ s in Set.Ioc 0 a, (Set.Ioi u).indicator p s) * q u
    rw [hslice]
  -- pull `q u` inside, swap, then read off the `s`-slice
  rw [hLHS]
  have hpull : ∀ u : ℝ,
      (∫ s in Set.Ioc 0 a, (Set.Ioi u).indicator p s) * q u
        = ∫ s in Set.Ioc 0 a, (Set.Ioi u).indicator p s * q u := by
    intro u; rw [MeasureTheory.integral_mul_const]
  simp_rw [hpull]
  rw [MeasureTheory.integral_integral_swap hint]
  -- RHS: for each `s`, the `u`-integral collapses to `p s · ∫₀^s q`
  rw [intervalIntegral.integral_of_le ha]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc ?_
  intro s hs
  have hInter2 : Set.Ioc 0 a ∩ Set.Iio s = Set.Ioo 0 s := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioc, Set.mem_Ioo]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, le_of_lt (lt_of_lt_of_le h2 hs.2)⟩, h2⟩
  have hslice2 : (∫ u in Set.Ioc 0 a, (Set.Ioi u).indicator p s * q u)
      = p s * ∫ u in (0:ℝ)..s, q u := by
    have hrw : ∀ u : ℝ, (Set.Ioi u).indicator p s * q u
        = (Set.Iio s).indicator (fun u => p s * q u) u := by
      intro u
      by_cases huv : u < s
      · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr huv : s ∈ Set.Ioi u),
          Set.indicator_of_mem (Set.mem_Iio.mpr huv : u ∈ Set.Iio s)]
      · rw [Set.indicator_of_notMem (by simpa using huv : s ∉ Set.Ioi u),
          Set.indicator_of_notMem (by simpa using huv : u ∉ Set.Iio s), zero_mul]
    simp_rw [hrw]
    rw [MeasureTheory.setIntegral_indicator measurableSet_Iio, hInter2,
      MeasureTheory.integral_const_mul, intervalIntegral.integral_of_le hs.1.le,
      ← MeasureTheory.integral_Ioc_eq_integral_Ioo]
  show (∫ u in Set.Ioc 0 a, (Set.Ioi u).indicator p s * q u) = p s * ∫ u in (0:ℝ)..s, q u
  rw [hslice2]

/-- **General triangle Fubini** (2-variable integrand): `∫₀^a ∫_u^a f(u,s) ds du = ∫₀^a ∫₀^s f(u,s) du
ds`.  Same `integral_integral_swap` + indicator argument as `intervalIntegral_triangle_swap`, but the
integrand `f u s` need not factor as `p(s)·q(u)`.  Used by `OZFIX.20` where the integrand
`H(u)·q0(t)·q0(t−u)` couples both variables through `q0(t−u)`. -/
theorem intervalIntegral_triangle_swap_gen {a : ℝ} (ha : 0 ≤ a) (f : ℝ → ℝ → ℝ)
    (hint : MeasureTheory.Integrable
      (Function.uncurry fun u s => (Set.Ioi u).indicator (f u) s)
      ((MeasureTheory.volume.restrict (Set.Ioc 0 a)).prod
        (MeasureTheory.volume.restrict (Set.Ioc 0 a)))) :
    (∫ u in (0:ℝ)..a, ∫ s in u..a, f u s) = ∫ s in (0:ℝ)..a, ∫ u in (0:ℝ)..s, f u s := by
  have hmeasp : ∀ u : ℝ, MeasurableSet (Set.Ioi u) := fun u => measurableSet_Ioi
  have hLHS : (∫ u in (0:ℝ)..a, ∫ s in u..a, f u s)
      = ∫ u in Set.Ioc 0 a, ∫ s in Set.Ioc 0 a, (Set.Ioi u).indicator (f u) s := by
    rw [intervalIntegral.integral_of_le ha]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc ?_
    intro u hu
    have hua : u ≤ a := hu.2
    have hInter : Set.Ioc 0 a ∩ Set.Ioi u = Set.Ioc u a := by
      ext s
      simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ioc]
      constructor
      · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨hu.1.trans h1, h2⟩, h1⟩
    show (∫ s in u..a, f u s) = ∫ s in Set.Ioc 0 a, (Set.Ioi u).indicator (f u) s
    rw [intervalIntegral.integral_of_le hua, MeasureTheory.setIntegral_indicator (hmeasp u), hInter]
  rw [hLHS, MeasureTheory.integral_integral_swap hint,
    intervalIntegral.integral_of_le ha]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc ?_
  intro s hs
  have hInter2 : Set.Ioc 0 a ∩ Set.Iio s = Set.Ioo 0 s := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioc, Set.mem_Ioo]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, le_of_lt (lt_of_lt_of_le h2 hs.2)⟩, h2⟩
  show (∫ u in Set.Ioc 0 a, (Set.Ioi u).indicator (f u) s) = ∫ u in (0:ℝ)..s, f u s
  have hrw : ∀ u : ℝ, (Set.Ioi u).indicator (f u) s
      = (Set.Iio s).indicator (fun u => f u s) u := by
    intro u
    by_cases huv : u < s
    · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr huv : s ∈ Set.Ioi u),
        Set.indicator_of_mem (Set.mem_Iio.mpr huv : u ∈ Set.Iio s)]
    · rw [Set.indicator_of_notMem (by simpa using huv : s ∉ Set.Ioi u),
        Set.indicator_of_notMem (by simpa using huv : u ∉ Set.Iio s)]
  simp_rw [hrw]
  rw [MeasureTheory.setIntegral_indicator measurableSet_Iio, hInter2,
    intervalIntegral.integral_of_le hs.1.le, ← MeasureTheory.integral_Ioc_eq_integral_Ioo]

/-- **`OZFIX.19` — the antiderivative bridge (as Fubini).**

  `r · (c_HS ⊛₃ g)(r) = ∫₀^σ K(u)·(g̃(r−u) + g̃(r+u)) du`   for `r > 0`,

the shell form of `radial3d_conv` re-expressed against Baxter's `K`.  The right side is `(K ⋆ g̃)(r)`
folded onto `[0,σ]` (`K` even), so with the reflection lemma this is `r·(c ⊛₃ g)(r) = (K ⋆ g̃)(r)`.

Proof: `radial3d_conv_eq_oddExt` writes the left side as `2π ∫_{Ioi 0} t·c(t)·∫_{r−t}^{r+t} g̃`;
`c_HS` is supported on `[0,σ]` so this reduces to `2π ∫₀^σ`.  On the right, `K(u) = 2π∫_u^σ s·c(s)ds`
on `[0,σ]`, and `intervalIntegral_triangle_swap` turns `∫₀^σ (∫_u^σ s c) H(u) du` into
`∫₀^σ s c(s) (∫₀^s H) ds`, whose inner integral is exactly `∫_{r−s}^{r+s} g̃` by two changes of
variable.  **Fubini, not differentiation** — jump-proof. -/
theorem radial3d_conv_eq_baxterK_shell {eta sigma : ℝ} (hsigma : 0 < sigma) {g : ℝ → ℝ}
    {r : ℝ} (hr : 0 < r)
    (hshell : ∀ t ∈ Set.Ioi (0:ℝ),
      IntervalIntegrable (oddExt g) MeasureTheory.volume (r - t) (r + t))
    (hjoint : MeasureTheory.Integrable
      (Function.uncurry fun u s => (Set.Ioi u).indicator (fun s => s * c_HS eta sigma s) s
        * (oddExt g (r - u) + oddExt g (r + u)))
      ((MeasureTheory.volume.restrict (Set.Ioc 0 sigma)).prod
        (MeasureTheory.volume.restrict (Set.Ioc 0 sigma)))) :
    r * radial3d_conv (c_HS eta sigma) g r
      = ∫ u in (0:ℝ)..sigma, baxterK eta sigma u * (oddExt g (r - u) + oddExt g (r + u)) := by
  set H : ℝ → ℝ := fun u => oddExt g (r - u) + oddExt g (r + u) with hH
  -- LHS: shell form, then reduce `Ioi 0 → [0,σ]` (integrand vanishes past σ)
  rw [radial3d_conv_eq_oddExt hr hshell]
  have hr0 : r ≠ 0 := ne_of_gt hr
  rw [show r * (2 * Real.pi / r *
      ∫ t in Set.Ioi (0:ℝ), t * c_HS eta sigma t * ∫ s in (r - t)..(r + t), oddExt g s)
      = 2 * Real.pi *
      ∫ t in Set.Ioi (0:ℝ), t * c_HS eta sigma t * ∫ s in (r - t)..(r + t), oddExt g s by
    field_simp]
  -- support reduction on the LHS `t`-integral
  have hLred : (∫ t in Set.Ioi (0:ℝ), t * c_HS eta sigma t * ∫ s in (r - t)..(r + t), oddExt g s)
      = ∫ t in (0:ℝ)..sigma, t * c_HS eta sigma t * ∫ s in (r - t)..(r + t), oddExt g s := by
    rw [intervalIntegral.integral_of_le hsigma.le]
    have hEq : Set.EqOn
        (fun t => t * c_HS eta sigma t * ∫ s in (r - t)..(r + t), oddExt g s)
        ((Set.Ioc 0 sigma).indicator
          (fun t => t * c_HS eta sigma t * ∫ s in (r - t)..(r + t), oddExt g s))
        (Set.Ioi 0) := by
      intro t ht
      by_cases htσ : t ∈ Set.Ioc 0 sigma
      · rw [Set.indicator_of_mem htσ]
      · rw [Set.indicator_of_notMem htσ]
        have htge : sigma ≤ t := by
          rcases not_and_or.mp htσ with h | h
          · exact absurd ht h
          · exact (not_le.mp h).le
        show t * c_HS eta sigma t * (∫ s in (r - t)..(r + t), oddExt g s) = 0
        rw [c_HS_outer htge, mul_zero, zero_mul]
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hEq,
      MeasureTheory.setIntegral_indicator measurableSet_Ioc,
      Set.inter_eq_self_of_subset_right Set.Ioc_subset_Ioi_self]
  rw [hLred]
  -- RHS: `K(u) = 2π ∫_u^σ s c(s)` on `[0,σ]`, then triangle-swap
  have hKrw : (∫ u in (0:ℝ)..sigma, baxterK eta sigma u * H u)
      = 2 * Real.pi * ∫ u in (0:ℝ)..sigma, (∫ s in u..sigma, s * c_HS eta sigma s) * H u := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr ?_
    intro u hu
    rw [Set.uIcc_of_le hsigma.le] at hu
    show baxterK eta sigma u * H u = 2 * Real.pi * ((∫ s in u..sigma, s * c_HS eta sigma s) * H u)
    rw [baxterK, abs_of_nonneg hu.1]; ring
  rw [hKrw,
    intervalIntegral_triangle_swap hsigma.le (fun s => s * c_HS eta sigma s) H hjoint]
  -- inner: `∫₀^s H = ∫_{r-s}^{r+s} g̃`
  congr 1
  refine intervalIntegral.integral_congr ?_
  intro s hs
  rw [Set.uIcc_of_le hsigma.le] at hs
  -- at `s = 0` the `s`-prefactor kills both sides; otherwise use `hshell`
  rcases eq_or_lt_of_le hs.1 with h0 | h0
  · show s * c_HS eta sigma s * (∫ w in (r - s)..(r + s), oddExt g w)
      = s * c_HS eta sigma s * ∫ u in (0:ℝ)..s, H u
    rw [← h0]; simp
  have hsIoi : s ∈ Set.Ioi (0:ℝ) := h0
  have hIL : IntervalIntegrable (oddExt g) MeasureTheory.volume (r - s) r :=
    (hshell s hsIoi).mono_set (Set.uIcc_subset_uIcc
      (by rw [Set.mem_uIcc]; left; exact ⟨le_refl _, by linarith [hs.1]⟩)
      (by rw [Set.mem_uIcc]; left; exact ⟨by linarith [hs.1], by linarith [hs.1]⟩))
  have hIR : IntervalIntegrable (oddExt g) MeasureTheory.volume r (r + s) :=
    (hshell s hsIoi).mono_set (Set.uIcc_subset_uIcc
      (by rw [Set.mem_uIcc]; left; exact ⟨by linarith [hs.1], by linarith [hs.1]⟩)
      (by rw [Set.mem_uIcc]; left; exact ⟨by linarith [hs.1], le_refl _⟩))
  have hinner : (∫ u in (0:ℝ)..s, H u) = ∫ w in (r - s)..(r + s), oddExt g w := by
    have h1 : (∫ u in (0:ℝ)..s, oddExt g (r - u)) = ∫ w in (r - s)..r, oddExt g w := by
      have := intervalIntegral.integral_comp_sub_left (a := (0:ℝ)) (b := s)
        (f := oddExt g) r
      simpa using this
    have h2 : (∫ u in (0:ℝ)..s, oddExt g (r + u)) = ∫ w in r..(r + s), oddExt g w := by
      have := intervalIntegral.integral_comp_add_left (a := (0:ℝ)) (b := s)
        (f := oddExt g) r
      simpa using this
    -- integrability of the two composed integrands on `0..s`
    have hcs : IntervalIntegrable (fun u => oddExt g (r - u)) MeasureTheory.volume 0 s := by
      have := (hIL.symm).comp_sub_left (f := oddExt g) r
      simpa using this
    have hca : IntervalIntegrable (fun u => oddExt g (r + u)) MeasureTheory.volume 0 s := by
      have := hIR.comp_add_left (f := oddExt g) r
      simpa using this
    rw [hH, intervalIntegral.integral_add hcs hca, h1, h2,
      intervalIntegral.integral_add_adjacent_intervals hIL hIR]
  show s * c_HS eta sigma s * (∫ w in (r - s)..(r + s), oddExt g w)
    = s * c_HS eta sigma s * ∫ u in (0:ℝ)..s, H u
  rw [hinner]

/-! ### `OZFIX.20` — the double-convolution reindex (associativity)

The identity that turns `(A + B − A⋆B) ⋆ ψ = ρK ⋆ ψ` (the `OZFIX.18` kernel factorization convolved
with ψ) into an equality of the *concrete* double integrals appearing in `baxterUQm` and `ρ(K⋆ψ)`:

  `∫₀^σ∫₀^σ q0(t)q0(s)ψ(r+t−s) ds dt = ∫₀^σ (∫_u^σ q0(t)q0(t−u)dt)·(ψ(r−u)+ψ(r+u)) du`.

**Both sides reduce to `∫ t in 0..σ, ∫ s in 0..t, q0(t)q0(s)·(ψ(r−t+s)+ψ(r+t−s))`** — the right side by
`intervalIntegral_triangle_swap_gen` + the inner change of variable `s = t−u`; the left side by
splitting the inner integral at the diagonal `s = t` and mapping the `{t<s}` half onto `{s<t}` by a
second `..._gen` swap (bound-variable relabel + the evenness of `u ↦ ψ(r−u)+ψ(r+u)`).  Holds for any
`ψ` (numerically verified for three unrelated `ψ` to `1e-16`); a pure change-of-variables/Fubini fact,
so it is stated with the requisite integrability as hypotheses (dischargeable for the concrete
`baxterPsi`, bounded on compacts). -/
theorem dbl_conv_reindex {sigma : ℝ} (hsigma : 0 < sigma) (q0 psi : ℝ → ℝ) (r : ℝ)
    (hswapD : MeasureTheory.Integrable
      (Function.uncurry fun u t => (Set.Ioi u).indicator
        (fun t => q0 t * q0 (t - u) * (psi (r - u) + psi (r + u))) t)
      ((MeasureTheory.volume.restrict (Set.Ioc 0 sigma)).prod
        (MeasureTheory.volume.restrict (Set.Ioc 0 sigma))))
    (hswapA : MeasureTheory.Integrable
      (Function.uncurry fun t s => (Set.Ioi t).indicator
        (fun s => q0 t * q0 s * psi (r + t - s)) s)
      ((MeasureTheory.volume.restrict (Set.Ioc 0 sigma)).prod
        (MeasureTheory.volume.restrict (Set.Ioc 0 sigma))))
    (hsliceL : ∀ t : ℝ, IntervalIntegrable (fun s => q0 t * q0 s * psi (r + t - s))
      MeasureTheory.volume 0 t)
    (hsliceR : ∀ t : ℝ, IntervalIntegrable (fun s => q0 t * q0 s * psi (r + t - s))
      MeasureTheory.volume t sigma)
    (hsliceL2 : ∀ t : ℝ, IntervalIntegrable (fun s => q0 s * q0 t * psi (r + s - t))
      MeasureTheory.volume 0 t)
    (haddI : IntervalIntegrable (fun t => ∫ s in (0:ℝ)..t, q0 t * q0 s * psi (r + t - s))
      MeasureTheory.volume 0 sigma)
    (haddII : IntervalIntegrable (fun t => ∫ s in t..sigma, q0 t * q0 s * psi (r + t - s))
      MeasureTheory.volume 0 sigma)
    (haddI2 : IntervalIntegrable (fun t => ∫ s in (0:ℝ)..t, q0 s * q0 t * psi (r + s - t))
      MeasureTheory.volume 0 sigma) :
    (∫ t in (0:ℝ)..sigma, q0 t * ∫ s in (0:ℝ)..sigma, q0 s * psi (r + t - s))
      = ∫ u in (0:ℝ)..sigma,
          (∫ t in u..sigma, q0 t * q0 (t - u)) * (psi (r - u) + psi (r + u)) := by
  set T : ℝ := ∫ t in (0:ℝ)..sigma, ∫ s in (0:ℝ)..t,
    q0 t * q0 s * (psi (r + t - s) + psi (r + s - t)) with hT
  -- RHS = T
  have hRHS : (∫ u in (0:ℝ)..sigma,
      (∫ t in u..sigma, q0 t * q0 (t - u)) * (psi (r - u) + psi (r + u))) = T := by
    have hstep1 : (∫ u in (0:ℝ)..sigma,
        (∫ t in u..sigma, q0 t * q0 (t - u)) * (psi (r - u) + psi (r + u)))
        = ∫ u in (0:ℝ)..sigma, ∫ t in u..sigma,
            q0 t * q0 (t - u) * (psi (r - u) + psi (r + u)) := by
      refine intervalIntegral.integral_congr fun u _ => ?_
      show (∫ t in u..sigma, q0 t * q0 (t - u)) * (psi (r - u) + psi (r + u))
        = ∫ t in u..sigma, q0 t * q0 (t - u) * (psi (r - u) + psi (r + u))
      rw [intervalIntegral.integral_mul_const]
    rw [hstep1, intervalIntegral_triangle_swap_gen hsigma.le
      (fun u t => q0 t * q0 (t - u) * (psi (r - u) + psi (r + u))) hswapD, hT]
    refine intervalIntegral.integral_congr fun t _ => ?_
    show (∫ u in (0:ℝ)..t, q0 t * q0 (t - u) * (psi (r - u) + psi (r + u)))
      = ∫ s in (0:ℝ)..t, q0 t * q0 s * (psi (r + t - s) + psi (r + s - t))
    have hcv := intervalIntegral.integral_comp_sub_left (a := (0:ℝ)) (b := t)
      (f := fun s => q0 t * q0 s * (psi (r + t - s) + psi (r + s - t))) t
    simp only [sub_zero, sub_self] at hcv
    rw [← hcv]
    refine intervalIntegral.integral_congr fun u _ => ?_
    show q0 t * q0 (t - u) * (psi (r - u) + psi (r + u))
      = q0 t * q0 (t - u) * (psi (r + t - (t - u)) + psi (r + (t - u) - t))
    rw [show r + t - (t - u) = r + u by ring, show r + (t - u) - t = r - u by ring]
    ring
  -- LHS = T
  have hLHS : (∫ t in (0:ℝ)..sigma, q0 t * ∫ s in (0:ℝ)..sigma, q0 s * psi (r + t - s)) = T := by
    have hpull : (∫ t in (0:ℝ)..sigma, q0 t * ∫ s in (0:ℝ)..sigma, q0 s * psi (r + t - s))
        = ∫ t in (0:ℝ)..sigma, ∫ s in (0:ℝ)..sigma, q0 t * q0 s * psi (r + t - s) := by
      refine intervalIntegral.integral_congr fun t _ => ?_
      show q0 t * (∫ s in (0:ℝ)..sigma, q0 s * psi (r + t - s))
        = ∫ s in (0:ℝ)..sigma, q0 t * q0 s * psi (r + t - s)
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun s _ => ?_
      show q0 t * (q0 s * psi (r + t - s)) = q0 t * q0 s * psi (r + t - s)
      ring
    have hsplit : (∫ t in (0:ℝ)..sigma, ∫ s in (0:ℝ)..sigma, q0 t * q0 s * psi (r + t - s))
        = (∫ t in (0:ℝ)..sigma, ∫ s in (0:ℝ)..t, q0 t * q0 s * psi (r + t - s))
          + ∫ t in (0:ℝ)..sigma, ∫ s in t..sigma, q0 t * q0 s * psi (r + t - s) := by
      rw [← intervalIntegral.integral_add haddI haddII]
      refine intervalIntegral.integral_congr fun t _ => ?_
      show (∫ s in (0:ℝ)..sigma, q0 t * q0 s * psi (r + t - s))
        = (∫ s in (0:ℝ)..t, q0 t * q0 s * psi (r + t - s))
          + ∫ s in t..sigma, q0 t * q0 s * psi (r + t - s)
      rw [intervalIntegral.integral_add_adjacent_intervals (hsliceL t) (hsliceR t)]
    have hI2 : (∫ t in (0:ℝ)..sigma, ∫ s in t..sigma, q0 t * q0 s * psi (r + t - s))
        = ∫ t in (0:ℝ)..sigma, ∫ s in (0:ℝ)..t, q0 s * q0 t * psi (r + s - t) := by
      rw [intervalIntegral_triangle_swap_gen hsigma.le
        (fun t s => q0 t * q0 s * psi (r + t - s)) hswapA]
    rw [hpull, hsplit, hI2, hT, ← intervalIntegral.integral_add haddI haddI2]
    refine intervalIntegral.integral_congr fun t _ => ?_
    show (∫ s in (0:ℝ)..t, q0 t * q0 s * psi (r + t - s))
        + ∫ s in (0:ℝ)..t, q0 s * q0 t * psi (r + s - t)
      = ∫ s in (0:ℝ)..t, q0 t * q0 s * (psi (r + t - s) + psi (r + s - t))
    rw [← intervalIntegral.integral_add (hsliceL t) (hsliceL2 t)]
    refine intervalIntegral.integral_congr fun s _ => ?_
    show q0 t * q0 s * psi (r + t - s) + q0 s * q0 t * psi (r + s - t)
      = q0 t * q0 s * (psi (r + t - s) + psi (r + s - t))
    ring
  rw [hLHS, hRHS]

/-! ### `OZFIX.21` — consolidation bricks -/

/-- **`OZFIX.21` brick — `oddExt (baxterPsi/·) = baxterPsi`.**

The bridge `OZFIX.19` outputs `∫₀^σ K(u)·(g̃(r∓u))du` with `g̃ = oddExt g`; for the OZ★ assembly the
relevant `g` is `h* := baxterPsi/·`, and its odd extension is `baxterPsi` itself.  Immediate from
`baxterPsi` being odd (`baxterPsi_odd`): `oddExt (baxterPsi/·)(v) = v·(baxterPsi|v|/|v|) = baxterPsi v`
(the `v<0` case uses `baxterPsi(−v)=−baxterPsi v`; `v=0` both sides `0`). -/
theorem oddExt_div_self_eq_baxterPsi {eta sigma rho : ℝ} (hsigma : 0 < sigma) :
    oddExt (fun x => baxterPsi eta sigma rho x / x) = baxterPsi eta sigma rho := by
  funext v
  rcases eq_or_ne v 0 with hv | hv
  · subst hv
    simp only [oddExt, abs_zero, zero_mul]
    rw [baxterPsi_core (v := (0:ℝ)) ⟨by linarith, hsigma⟩]
    ring
  · rcases lt_or_gt_of_ne hv with hneg | hpos
    · have hvne : v ≠ 0 := ne_of_lt hneg
      simp only [oddExt, abs_of_neg hneg]
      rw [baxterPsi_odd hsigma v]
      field_simp
    · have hvne : v ≠ 0 := ne_of_gt hpos
      simp only [oddExt, abs_of_pos hpos]
      field_simp

/-- **`OZFIX.21` linchpin — OZ★: the real-space Ornstein–Zernike relation for `baxterPsi`.**

  `baxterPsi(r) = r·c_HS(r) + ρ·r·(c_HS ⊛₃ (baxterPsi/·))(r)`   for every `r > 0`.

This is the concrete OZ equation solved by the constructed `baxterPsi` (with `h⋆ := baxterPsi/·`
the radial `h`, `φ = r·c_HS`).  It is the **shared linchpin** for both consolidations of the three
OZ axioms: it *identifies* `baxterPsi/·` as an OZ fixed point (Consolidation B) and — with a decay
input — as the *unique* one (Consolidation A), **without itself needing any decay**: it is a finite
algebraic identity among already-proved decay-free pieces.

**Assembly.**
* `baxter_psi_conv_eq_phi` (`OZFIX.15`) gives `baxterUQm r = r·c_HS r`; expanding `baxterUQm`
  definitionally rearranges to `baxterPsi r = r·c_HS r + (Aminus + Aplus − Adouble)` (`claimA`),
  where `Aminus = ∫₀^σ q0(u)ψ(r−u)`, `Aplus = ∫₀^σ q0(t)ψ(r+t)`,
  `Adouble = ∫₀^σ q0(t)∫₀^σ q0(s)ψ(r+t−s)`.
* `radial3d_conv_eq_baxterK_shell` (`OZFIX.19`) with `g = baxterPsi/·` and
  `oddExt_div_self_eq_baxterPsi` turns `r·(c⊛₃g)(r)` into `∫₀^σ K(u)(ψ(r−u)+ψ(r+u))du`;
  `rho_baxterK_eq_q0_self_conv` (`OZFIX.18` KDEF) rewrites `ρK(u) = q0(u) − ∫_u^σ q0 q0`, and
  `dbl_conv_reindex` (`OZFIX.20`) collapses the self-convolution term to `Adouble`, giving
  `ρ·r·(c⊛₃g)(r) = Aminus + Aplus − Adouble` (`claimB`).

`claimA` and `claimB` share the same right-hand side, so subtracting proves OZ★.

Stated **conditional on integrability** — the products and parametric integrals below are interval-
or jointly integrable.  These are decay-free (dischargeable from `baxterPsi`'s piecewise continuity)
and are exactly the hypotheses of the consumed `OZFIX.19`/`OZFIX.20` lemmas specialised to
`q0 := q0_poly` and `ψ := baxterPsi`. -/
theorem baxterPsi_eq_phi_add_rho_conv {eta sigma rho : ℝ} (hsigma : 0 < sigma) (heta : eta < 1)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) {r : ℝ} (hr : 0 < r)
    (hAminus : IntervalIntegrable
      (fun u => q0_poly eta sigma rho u * baxterPsi eta sigma rho (r - u))
      MeasureTheory.volume 0 sigma)
    (hAplus : IntervalIntegrable
      (fun t => q0_poly eta sigma rho t * baxterPsi eta sigma rho (r + t))
      MeasureTheory.volume 0 sigma)
    (hAdbl : IntervalIntegrable
      (fun t => q0_poly eta sigma rho t
        * ∫ s in (0:ℝ)..sigma, q0_poly eta sigma rho s * baxterPsi eta sigma rho (r + t - s))
      MeasureTheory.volume 0 sigma)
    (hKdblH : IntervalIntegrable
      (fun u => (∫ t in u..sigma, q0_poly eta sigma rho t * q0_poly eta sigma rho (t - u))
        * (baxterPsi eta sigma rho (r - u) + baxterPsi eta sigma rho (r + u)))
      MeasureTheory.volume 0 sigma)
    (hshell : ∀ t ∈ Set.Ioi (0:ℝ),
      IntervalIntegrable (baxterPsi eta sigma rho) MeasureTheory.volume (r - t) (r + t))
    (hjoint : MeasureTheory.Integrable
      (Function.uncurry fun u s => (Set.Ioi u).indicator (fun s => s * c_HS eta sigma s) s
        * (baxterPsi eta sigma rho (r - u) + baxterPsi eta sigma rho (r + u)))
      ((MeasureTheory.volume.restrict (Set.Ioc 0 sigma)).prod
        (MeasureTheory.volume.restrict (Set.Ioc 0 sigma))))
    (hswapD : MeasureTheory.Integrable
      (Function.uncurry fun u t => (Set.Ioi u).indicator
        (fun t => q0_poly eta sigma rho t * q0_poly eta sigma rho (t - u)
          * (baxterPsi eta sigma rho (r - u) + baxterPsi eta sigma rho (r + u))) t)
      ((MeasureTheory.volume.restrict (Set.Ioc 0 sigma)).prod
        (MeasureTheory.volume.restrict (Set.Ioc 0 sigma))))
    (hswapA : MeasureTheory.Integrable
      (Function.uncurry fun t s => (Set.Ioi t).indicator
        (fun s => q0_poly eta sigma rho t * q0_poly eta sigma rho s
          * baxterPsi eta sigma rho (r + t - s)) s)
      ((MeasureTheory.volume.restrict (Set.Ioc 0 sigma)).prod
        (MeasureTheory.volume.restrict (Set.Ioc 0 sigma))))
    (hsliceL : ∀ t : ℝ, IntervalIntegrable
      (fun s => q0_poly eta sigma rho t * q0_poly eta sigma rho s
        * baxterPsi eta sigma rho (r + t - s)) MeasureTheory.volume 0 t)
    (hsliceR : ∀ t : ℝ, IntervalIntegrable
      (fun s => q0_poly eta sigma rho t * q0_poly eta sigma rho s
        * baxterPsi eta sigma rho (r + t - s)) MeasureTheory.volume t sigma)
    (hsliceL2 : ∀ t : ℝ, IntervalIntegrable
      (fun s => q0_poly eta sigma rho s * q0_poly eta sigma rho t
        * baxterPsi eta sigma rho (r + s - t)) MeasureTheory.volume 0 t)
    (haddI : IntervalIntegrable
      (fun t => ∫ s in (0:ℝ)..t, q0_poly eta sigma rho t * q0_poly eta sigma rho s
        * baxterPsi eta sigma rho (r + t - s)) MeasureTheory.volume 0 sigma)
    (haddII : IntervalIntegrable
      (fun t => ∫ s in t..sigma, q0_poly eta sigma rho t * q0_poly eta sigma rho s
        * baxterPsi eta sigma rho (r + t - s)) MeasureTheory.volume 0 sigma)
    (haddI2 : IntervalIntegrable
      (fun t => ∫ s in (0:ℝ)..t, q0_poly eta sigma rho s * q0_poly eta sigma rho t
        * baxterPsi eta sigma rho (r + s - t)) MeasureTheory.volume 0 sigma) :
    baxterPsi eta sigma rho r
      = r * c_HS eta sigma r
        + rho * (r * radial3d_conv (c_HS eta sigma)
            (fun x => baxterPsi eta sigma rho x / x) r) := by
  -- odd-extension bridge (OZFIX.21 brick): `oddExt (ψ/·) = ψ`
  have hg_eq : oddExt (fun x => baxterPsi eta sigma rho x / x) = baxterPsi eta sigma rho :=
    oddExt_div_self_eq_baxterPsi hsigma
  -- `OZFIX.19` hypotheses in `oddExt` form
  have hshell' : ∀ t ∈ Set.Ioi (0:ℝ),
      IntervalIntegrable (oddExt (fun x => baxterPsi eta sigma rho x / x))
        MeasureTheory.volume (r - t) (r + t) := by
    intro t ht; rw [hg_eq]; exact hshell t ht
  have hjoint' : MeasureTheory.Integrable
      (Function.uncurry fun u s => (Set.Ioi u).indicator (fun s => s * c_HS eta sigma s) s
        * (oddExt (fun x => baxterPsi eta sigma rho x / x) (r - u)
          + oddExt (fun x => baxterPsi eta sigma rho x / x) (r + u)))
      ((MeasureTheory.volume.restrict (Set.Ioc 0 sigma)).prod
        (MeasureTheory.volume.restrict (Set.Ioc 0 sigma))) := by
    simpa only [hg_eq] using hjoint
  -- `q0·(ψ(r-·)+ψ(r+·))` is interval-integrable (sum of the two halves)
  have hKq0H : IntervalIntegrable
      (fun u => q0_poly eta sigma rho u
        * (baxterPsi eta sigma rho (r - u) + baxterPsi eta sigma rho (r + u)))
      MeasureTheory.volume 0 sigma := by
    have h := hAminus.add hAplus
    have hfe : (fun u => q0_poly eta sigma rho u * baxterPsi eta sigma rho (r - u)
        + q0_poly eta sigma rho u * baxterPsi eta sigma rho (r + u))
        = (fun u => q0_poly eta sigma rho u
          * (baxterPsi eta sigma rho (r - u) + baxterPsi eta sigma rho (r + u))) := by
      funext u; ring
    rwa [hfe] at h
  -- KDEF under the integral (a.e. on the open core `(0,σ)`)
  have hcongr : (∫ u in (0:ℝ)..sigma, rho * (baxterK eta sigma u
        * (baxterPsi eta sigma rho (r - u) + baxterPsi eta sigma rho (r + u))))
      = ∫ u in (0:ℝ)..sigma,
          (q0_poly eta sigma rho u
            - ∫ t in u..sigma, q0_poly eta sigma rho t * q0_poly eta sigma rho (t - u))
          * (baxterPsi eta sigma rho (r - u) + baxterPsi eta sigma rho (r + u)) := by
    have hne : ∀ᵐ (x : ℝ), x ≠ sigma := by
      rw [MeasureTheory.ae_iff]; simpa using MeasureTheory.measure_singleton sigma
    refine intervalIntegral.integral_congr_ae ?_
    rw [Set.uIoc_of_le hsigma.le]
    filter_upwards [hne] with u hune hmem
    have hu : u ∈ Set.Ioo (0:ℝ) sigma := ⟨hmem.1, lt_of_le_of_ne hmem.2 hune⟩
    rw [show rho * (baxterK eta sigma u
          * (baxterPsi eta sigma rho (r - u) + baxterPsi eta sigma rho (r + u)))
        = (rho * baxterK eta sigma u)
          * (baxterPsi eta sigma rho (r - u) + baxterPsi eta sigma rho (r + u)) by ring,
      rho_baxterK_eq_q0_self_conv hsigma heta heta_def hu]
  -- split the KDEF integrand across the subtraction
  have hsplitB : (∫ u in (0:ℝ)..sigma,
        (q0_poly eta sigma rho u
          - ∫ t in u..sigma, q0_poly eta sigma rho t * q0_poly eta sigma rho (t - u))
        * (baxterPsi eta sigma rho (r - u) + baxterPsi eta sigma rho (r + u)))
      = (∫ u in (0:ℝ)..sigma, q0_poly eta sigma rho u
          * (baxterPsi eta sigma rho (r - u) + baxterPsi eta sigma rho (r + u)))
        - ∫ u in (0:ℝ)..sigma,
            (∫ t in u..sigma, q0_poly eta sigma rho t * q0_poly eta sigma rho (t - u))
            * (baxterPsi eta sigma rho (r - u) + baxterPsi eta sigma rho (r + u)) := by
    rw [← intervalIntegral.integral_sub hKq0H hKdblH]
    refine intervalIntegral.integral_congr fun u _ => ?_
    show (q0_poly eta sigma rho u
          - ∫ t in u..sigma, q0_poly eta sigma rho t * q0_poly eta sigma rho (t - u))
        * (baxterPsi eta sigma rho (r - u) + baxterPsi eta sigma rho (r + u))
      = q0_poly eta sigma rho u
          * (baxterPsi eta sigma rho (r - u) + baxterPsi eta sigma rho (r + u))
        - (∫ t in u..sigma, q0_poly eta sigma rho t * q0_poly eta sigma rho (t - u))
          * (baxterPsi eta sigma rho (r - u) + baxterPsi eta sigma rho (r + u))
    ring
  -- first piece = Aminus + Aplus
  have hFirst : (∫ u in (0:ℝ)..sigma, q0_poly eta sigma rho u
        * (baxterPsi eta sigma rho (r - u) + baxterPsi eta sigma rho (r + u)))
      = (∫ u in (0:ℝ)..sigma, q0_poly eta sigma rho u * baxterPsi eta sigma rho (r - u))
        + ∫ t in (0:ℝ)..sigma, q0_poly eta sigma rho t * baxterPsi eta sigma rho (r + t) := by
    rw [← intervalIntegral.integral_add hAminus hAplus]
    refine intervalIntegral.integral_congr fun u _ => ?_
    show q0_poly eta sigma rho u
        * (baxterPsi eta sigma rho (r - u) + baxterPsi eta sigma rho (r + u))
      = q0_poly eta sigma rho u * baxterPsi eta sigma rho (r - u)
        + q0_poly eta sigma rho u * baxterPsi eta sigma rho (r + u)
    ring
  -- second piece = Adouble (OZFIX.20)
  have hSecond : (∫ u in (0:ℝ)..sigma,
        (∫ t in u..sigma, q0_poly eta sigma rho t * q0_poly eta sigma rho (t - u))
        * (baxterPsi eta sigma rho (r - u) + baxterPsi eta sigma rho (r + u)))
      = ∫ t in (0:ℝ)..sigma, q0_poly eta sigma rho t
          * ∫ s in (0:ℝ)..sigma, q0_poly eta sigma rho s * baxterPsi eta sigma rho (r + t - s) :=
    (dbl_conv_reindex hsigma (q0_poly eta sigma rho) (baxterPsi eta sigma rho) r
      hswapD hswapA hsliceL hsliceR hsliceL2 haddI haddII haddI2).symm
  -- Claim A — from `OZFIX.15` (`baxterUQm = r·c_HS`), definitionally expanded
  have claimA : baxterPsi eta sigma rho r
      = r * c_HS eta sigma r
        + ((∫ u in (0:ℝ)..sigma, q0_poly eta sigma rho u * baxterPsi eta sigma rho (r - u))
          + (∫ t in (0:ℝ)..sigma, q0_poly eta sigma rho t * baxterPsi eta sigma rho (r + t))
          - (∫ t in (0:ℝ)..sigma, q0_poly eta sigma rho t
              * ∫ s in (0:ℝ)..sigma, q0_poly eta sigma rho s
                * baxterPsi eta sigma rho (r + t - s))) := by
    have hkey := baxter_psi_conv_eq_phi hsigma heta heta_def hr
    have hsecond : (∫ t in (0:ℝ)..sigma, q0_poly eta sigma rho t
          * (baxterPsi eta sigma rho (r + t)
            - ∫ s in (0:ℝ)..sigma, q0_poly eta sigma rho s
              * baxterPsi eta sigma rho (r + t - s)))
        = (∫ t in (0:ℝ)..sigma, q0_poly eta sigma rho t * baxterPsi eta sigma rho (r + t))
          - ∫ t in (0:ℝ)..sigma, q0_poly eta sigma rho t
              * ∫ s in (0:ℝ)..sigma, q0_poly eta sigma rho s
                * baxterPsi eta sigma rho (r + t - s) := by
      rw [← intervalIntegral.integral_sub hAplus hAdbl]
      refine intervalIntegral.integral_congr fun t _ => ?_
      show q0_poly eta sigma rho t
          * (baxterPsi eta sigma rho (r + t)
            - ∫ s in (0:ℝ)..sigma, q0_poly eta sigma rho s
              * baxterPsi eta sigma rho (r + t - s))
        = q0_poly eta sigma rho t * baxterPsi eta sigma rho (r + t)
          - q0_poly eta sigma rho t
            * ∫ s in (0:ℝ)..sigma, q0_poly eta sigma rho s
              * baxterPsi eta sigma rho (r + t - s)
      ring
    unfold baxterUQm baxterU at hkey
    rw [hsecond] at hkey
    linear_combination hkey
  -- Claim B — from `OZFIX.19` + KDEF + `OZFIX.20`
  have claimB : rho * (r * radial3d_conv (c_HS eta sigma)
        (fun x => baxterPsi eta sigma rho x / x) r)
      = ((∫ u in (0:ℝ)..sigma, q0_poly eta sigma rho u * baxterPsi eta sigma rho (r - u))
          + (∫ t in (0:ℝ)..sigma, q0_poly eta sigma rho t * baxterPsi eta sigma rho (r + t))
          - (∫ t in (0:ℝ)..sigma, q0_poly eta sigma rho t
              * ∫ s in (0:ℝ)..sigma, q0_poly eta sigma rho s
                * baxterPsi eta sigma rho (r + t - s))) := by
    rw [radial3d_conv_eq_baxterK_shell hsigma hr hshell' hjoint']
    simp only [hg_eq]
    rw [← intervalIntegral.integral_const_mul, hcongr, hsplitB, hFirst, hSecond]
  rw [claimA, claimB]

end

end FMSA.HardSphere
