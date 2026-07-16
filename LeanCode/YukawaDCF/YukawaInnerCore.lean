/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.YukawaDCF.YukawaCausalProjection
import LeanCode.FMSAPoly.EijStructure
import LeanCode.FMSAPoly.OriginConstraint

/-!
# Task Y1.7 — inner-core `S₁`, origin constraint, contact matching ([LN] §7, §9)

The Group Y1 capstone.  The first-order amplitude splits as `b₁ = U₁ + S₁` ([LN] Eq. 43): the
outside-core Yukawa part `U₁` (Y1.2) plus the **inside-core** contribution
`{S₁(k)}_{ij} = 2π√(ρρ) ∫₀^{R_{ij}} r c_{ij}(r) e^{−ikr} dr` (Eq. 45).  Section 9 (*"First-Order DCF
Inside the Hard Core: r < R_{ij}"*) shows `S₁` is supported strictly inside the core, so (Proof 2) it
is anti-causal — it contributes nothing to the `[R_{ij},∞)` part.  This is exactly this session's
**Y1.3b** `causal_projection_fourier`, and here it is instantiated for the concrete inner core.

Everything reuses existing infrastructure:
* the anti-causal projection is Y1.3b (`YukawaCausalProjection.lean`);
* the origin constraint `A_{ij} = −Σ_n 𝓔_n(0)` ([LN] Eq. 76) is the P.2 origin-regularity condition
  (`FMSA.OriginConstraint.origin_necessity`) + `FMSA.EijStructure.eij_at_origin`;
* contact matching (§7) is Group 5.1 (`FMSA.Contact.soft_core_contact_limit`) /
  `FMSA.EijStructure.eij_at_contact`.

## Results

* `innerS1` / `innerS1_support_subset_Iio` — the inside-core amplitude `r c_{ij}(r)` on `[0,R)`
  ([LN] §9, Eq. 45) and Proof 2: `Function.support ⊆ Set.Iio R` (anti-causal).
* `b1_causal_eq_U1_fourier` — [LN] §9.3: from `b₁ = U₁ + S₁` (Eq. 43) with `b₁` causal
  (`support ⊆ [R,∞)`), the causal Fourier transform of `b₁` equals the half-line transform of `U₁`
  (`{U₁}^{[R,∞)} = B₁`, Eq. 62) — `S₁` drops out.  Instantiates `causal_projection_fourier` (Y1.3b).
* `origin_constraint_eq76` — [LN] Eq. 76: origin regularity forces the inside-core constant
  `P_{ij}(0) = −Σ_k A_k e^{−z_k R} = −𝓔_{ij}(0)`.
* `innerS1_contact_value` — §7: the inner-core `E_{ij}` at contact is `Σ_k A_k` (via `eij_at_contact`).

Status: ✓ DONE (Y1.7), axiom-clean.  Completes Group Y1.
-/

set_option linter.style.longLine false

open MeasureTheory Set Filter Topology

namespace FMSA.YukawaWH

/-! ### (A) Inside-core `S₁` and its anti-causal support ([LN] §9, Eq. 45, Proof 2) -/

/-- Inside-core first-order amplitude `{S₁}` ([LN] Eq. 45): the integrand `r·c_{ij}(r)` supported on
the strict core `[0, R)` (§9 is *"…Inside the Hard Core: r < R_{ij}"*). -/
noncomputable def innerS1 (c : ℝ → ℝ) (R : ℝ) : ℝ → ℂ :=
  Set.indicator (Set.Ico 0 R) (fun r => (r * c r : ℂ))

/-- **[LN] Proof 2 — `S₁` is anti-causal.**  The inside-core amplitude is supported on `(−∞, R)`
(here `[0,R) ⊆ Iio R`), so it contributes nothing to the causal `[R,∞)` part. -/
theorem innerS1_support_subset_Iio (c : ℝ → ℝ) (R : ℝ) :
    Function.support (innerS1 c R) ⊆ Set.Iio R := by
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hns
  rw [Set.mem_Iio] at hns
  exact hx (Set.indicator_of_notMem (fun hmem => hns (Set.mem_Ico.mp hmem).2) _)

/-- **[LN] §9.3 — the inside core drops out of the causal part** (`B₁ = {U₁}^{[R,∞)}`, Eq. 62).
From the split `b₁ = U₁ + S₁` (Eq. 43) with `b₁` causal (`support ⊆ [R,∞)`, the Baxter-transformed
`Q̂₀ᵀĤ₁Q̂₀` on the hard core), the Fourier transform of `b₁` equals the half-line (`[R,∞)`) transform
of the outer term `U₁` — the anti-causal `S₁` contributes nothing.  Instantiates Y1.3b's
`causal_projection_fourier` with `T_S = innerS1`. -/
theorem b1_causal_eq_U1_fourier {c : ℝ → ℝ} {R : ℝ} (k : ℝ) {U1 b1 : ℝ → ℂ}
    (hsplit : ∀ r, b1 r = U1 r + innerS1 c R r)
    (hb1 : Function.support b1 ⊆ Set.Ici R) :
    ∫ r, b1 r * Complex.exp (-Complex.I * k * r)
      = ∫ r in Set.Ici R, U1 r * Complex.exp (-Complex.I * k * r) :=
  causal_projection_fourier k hsplit hb1 (innerS1_support_subset_Iio c R)

/-! ### (B) Origin regularity constraint ([LN] Eq. 76) -/

/-- **[LN] Eq. 76 — origin regularity constraint.**  For the inside-core ratio
`c_{ij}(r) = (𝓔_{ij}(r) + P_{ij}(r))/(2π√(ρρ)·r)` to stay finite as `r → 0`, the inside-core polynomial
constant is forced to `P_{ij}(0) = −Σ_k A_k e^{−z_k R} = −𝓔_{ij}(0)` (`= −Σ_n 𝓔_n(0)`).  Combines the
P.2 origin-necessity limit with `eij_at_origin`. -/
theorem origin_constraint_eq76 {n : ℕ} (Amp z : Fin n → ℝ) (R : ℝ) (P : ℝ → ℝ)
    (hcP : ContinuousAt P 0) {L : ℝ}
    (hL : Filter.Tendsto (fun r => (FMSA.EijStructure.eij Amp z R r + P r) / r)
      (𝓝[≠] (0 : ℝ)) (𝓝 L)) :
    P 0 = -∑ k : Fin n, Amp k * Real.exp (-(z k) * R) := by
  have hcont : Continuous (FMSA.EijStructure.eij Amp z R) := by
    unfold FMSA.EijStructure.eij; fun_prop
  have h := FMSA.OriginConstraint.origin_necessity (FMSA.EijStructure.eij Amp z R) P
    hcont.continuousAt hcP hL
  rw [FMSA.EijStructure.eij_at_origin] at h
  linarith

/-! ### (C) Contact matching ([LN] §7) -/

/-- **[LN] §7 — inner-core value at contact.**  The inside-core `𝓔_{ij}` evaluated at `r = R_{ij}` is
`Σ_k A_k` (every exponential factor collapses to 1).  Restates `FMSA.EijStructure.eij_at_contact` in
the `S₁` context.  Full inner/outer continuity of `c_{ij}` at contact is Group 5.1
(`FMSA.Contact.soft_core_contact_limit`), modulo the MSA closure `K ↔ A` relation Group 5.1 flags as
external data. -/
theorem innerS1_contact_value {n : ℕ} (Amp z : Fin n → ℝ) (R : ℝ) :
    FMSA.EijStructure.eij Amp z R R = ∑ k : Fin n, Amp k :=
  FMSA.EijStructure.eij_at_contact Amp z R

end FMSA.YukawaWH
