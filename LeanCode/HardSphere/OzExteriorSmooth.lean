/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HardSphere.BaxterOzStar
import LeanCode.HardSphere.OzExteriorDerivBundle
import LeanCode.HardSphere.BaxterExteriorRegularityGeneral
import LeanCode.HardSphere.OzExteriorIntegrability
import LeanCode.HardSphere.BaxterRenewalDiff
import LeanCode.HardSphere.BaxterExteriorDerivIntegrable
import LeanCode.HardSphere.OzExteriorFromBaxter

/-!
# Smooth exterior representative of `ozBaxterFixedPt` — retiring the false clause 6a

`ozBaxterFixedPt` *jumps* at the contact point `σ` (`-1` on the core, `baxterPsiOuter/·` on the
exterior), so it is not two-sidedly differentiable there — clause 6a of the old axiom
`baxter_exterior_regularity` (`HasDerivAt ozBaxterFixedPt … σ`) is *false*
(`ozBaxterFixedPt_deriv_bundle_endpoint_false`).

The fix follows the design already in `radial_fourier_jump_asymptotic` (JumpAsymptotic.lean):
that theorem asks for a **smooth** representative `g` (two-sided differentiable on `[σ,∞)`) together
with the actual jumping function `f`, related by `f = g` only on `(σ,∞)`.  Here we introduce that
smooth representative via two split real-analysis axioms (`ozExterior_smooth_repr` +
`ozExterior_deriv_integrable`) and package the
usable bundle (`ozBaxterFixedPt_smooth_deriv_bundle`).

## The math axioms (split 2026-07-19)
* `ozExterior_smooth_repr` (**regularity**): `baxterPsiOuter/·` admits a `C¹` extension `g` across
  `σ` (it is `C¹` on `(σ,∞)` with a finite right-derivative at `σ`, extendable — e.g. linearly —
  below `σ`).
* `ozExterior_deriv_integrable` (**integrability**): `d/dr(r·g) = g + r·g'` (which equals
  `baxterPsiOuter'` on the exterior, hence is independent of which representative `g` is chosen) is
  integrable on `(σ,∞)`.

Both are pure real-analysis facts about the constructed Volterra renewal solution `baxterPsiOuter`;
the jump is entirely in the `-1` core clamp of `ozBaxterFixedPt`, not in `baxterPsiOuter/·`, which is
genuinely `C¹` on the closed exterior and linearly extendable.  Neither is a physics postulate.
**Both are discharged at once by (★DIFF), the differentiated renewal equation — see the section
comment below.**
-/

open MeasureTheory Set Real Filter Topology

namespace FMSA.HardSphere

noncomputable section

/-! ### The former `ozExterior_smooth_deriv`, SPLIT into its two independent halves

The old single axiom bundled two unrelated claims: **(a)** `C¹` regularity of the renewal solution
across `σ`, and **(b)** `IntegrableOn (g + r·g') (Ioi σ)`.  They are split below so each can be
attacked (and retired) separately.

**KEY STRUCTURAL FINDING (2026-07-19): both halves reduce to ONE shared missing lemma** — the
*differentiated renewal equation*.  From `baxterPsiOuter_spec`,
`ψ(r) = baxterForcing(r) + ∫_σ^r q0(r−t)·ψ(t)dt`, Leibniz (variable upper limit **and**
`r`-dependent integrand) gives

  `ψ'(r) = baxterForcing'(r) + q0(0)·ψ(r) + ∫_σ^r q0'(r−t)·ψ(t)dt`.        (★DIFF)

* **(a) follows**: `ψ` is then `C¹` on `[σ,∞)` (RHS continuous), so `ψ/·` is `C¹` there (`r ≥ σ > 0`),
  and `g` := that, extended linearly below `σ`, is `C¹` across `σ`.
* **(b) follows**: `g + r·g' = (r·g)' = ψ'` on `(σ,∞)`, and each (★DIFF) summand is `L¹(Ioi σ)` —
  `baxterForcing'` is compactly supported (`baxterForcing = 0` for `r ≥ 2σ`), `q0(0)·ψ` is `L¹`
  because **`IntegrableOn ψ (Ioi σ)` is ALREADY PROVEN** (`baxterPsiOuter_integrableOn`, from MA.13's
  strengthened conclusion), and `q0' ⋆ ψ` is `L¹` by Young (compactly-supported bounded `q0'`).

So **proving (★DIFF) retires BOTH axioms below outright** — strictly better than relocating or
abstracting either. Mathlib tooling for (★DIFF): `hasDerivAt_integral_of_dominated_loc_of_lip`
(`r`-dependence of the integrand) + `intervalIntegral.integral_hasDerivAt_right` (upper limit); the
same pattern already used for `hasDerivAt_tIntegral_shell` (`BaxterRenewal.lean`, OZFIX.16). -/

/-- **(a) RETIRED AXIOM → THEOREM (OZFIX.25, 2026-07-19).**  `C¹` representative of the exterior
solution across `σ`, now PROVED via (★DIFF) — see `ozExterior_smooth_repr_proved`
(`BaxterRenewalDiff.lean`).  Original note:  `baxterPsiOuter/·`
admits a `C¹` extension `g` across the contact point `σ` (`C¹` on `(σ,∞)` with a finite
right-derivative at `σ`, extended e.g. linearly below `σ`).  Pure real-analysis regularity of the
constructed Volterra renewal solution; NOT a physics postulate.

**Discharge route:** (★DIFF) above ⇒ `ψ` is `C¹` on `[σ,∞)` ⇒ `ψ/·` is, then extend linearly. -/
theorem ozExterior_smooth_repr {eta sigma rho : ℝ} (hsigma : 0 < sigma) :
    ∃ g g' : ℝ → ℝ,
      (∀ r ∈ Set.Ici sigma, HasDerivAt g (g' r) r) ∧
      (∀ r, sigma ≤ r → g r = baxterPsiOuter eta sigma rho r / r) :=
  ozExterior_smooth_repr_proved hsigma

/-- **(b) RETIRED AXIOM → THEOREM (OZFIX.25, 2026-07-19).**  The exterior derivative is
integrable, now PROVED — see `ozExterior_deriv_integrable_proved`
(`BaxterExteriorDerivIntegrable.lean`).  Original note:  For *any* `C¹` representative `g`
of `baxterPsiOuter/·` on `[σ,∞)`, the derivative of `r·g` (which equals `baxterPsiOuter'` there, so
the statement does not depend on the choice of representative) is integrable on `(σ,∞)`.

⚠ **STATEMENT BUG FIXED 2026-07-19.**  This was originally stated with only `hsigma`, i.e. for
*arbitrary* `eta, rho`.  In that generality it is **FALSE**: without the physical relation
`heta_def` the kernel mass `∫₀^σ|q0_poly|` scales linearly in `ρ` and can be made arbitrarily large,
so the renewal solution `baxterPsiOuter` grows exponentially and is neither `L¹` nor has an `L¹`
derivative.  The physical hypotheses are exactly what `baxterPsiOuter_integrableOn` needs, and the
sole consumer (`ozBaxterFixedPt_smooth_deriv_bundle`) already carries them — so adding them costs
nothing.  Same species of over-general statement as the false clause 6a.

**Discharge route:** (★DIFF) above; the `q0(0)·ψ` summand is already covered by the *proven*
`baxterPsiOuter_integrableOn`, the forcing term is compactly supported, and `q0' ⋆ ψ` is `L¹` by
Young. This is an integrability statement, NOT a regularity one — hence split off from (a). -/
theorem ozExterior_deriv_integrable {eta sigma rho : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (hrho : 0 < rho) (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6)
    {g g' : ℝ → ℝ}
    (hderiv : ∀ r ∈ Set.Ici sigma, HasDerivAt g (g' r) r)
    (hg_eq : ∀ r, sigma ≤ r → g r = baxterPsiOuter eta sigma rho r / r) :
    MeasureTheory.IntegrableOn (fun r => g r + r * g' r) (Set.Ioi sigma) :=
  ozExterior_deriv_integrable_proved heta0 heta1 hsigma hrho heta_def hderiv hg_eq

/-- **Smooth-`g` derivative/decay bundle for `ozBaxterFixedPt`.**  Provides a `C¹` exterior
representative `g` (agreeing with `ozBaxterFixedPt` on `(σ,∞)`, equal at `σ`), plus the decay
(`r·ozBaxterFixedPt → 0`) and integrability facts.  Combines the regularity axiom
`ozExterior_smooth_repr`/`ozExterior_deriv_integrable` with the already-proven exterior decay/integrability
(`r_mul_ozBaxterFixedPt_tendsto_zero`, `r_mul_ozBaxterFixedPt_integrableOn`). -/
theorem ozBaxterFixedPt_smooth_deriv_bundle {eta sigma rho : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (hrho : 0 < rho) (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) :
    ∃ g g' : ℝ → ℝ,
      (∀ r ∈ Set.Ici sigma, HasDerivAt g (g' r) r) ∧
      (∀ r ∈ Set.Ioi sigma, ozBaxterFixedPt eta sigma rho r = g r) ∧
      g sigma = ozBaxterFixedPt eta sigma rho sigma ∧
      Tendsto (fun r => r * ozBaxterFixedPt eta sigma rho r) atTop (𝓝 0) ∧
      IntegrableOn (fun r => r * ozBaxterFixedPt eta sigma rho r) (Set.Ioi sigma) ∧
      IntegrableOn (fun r => g r + r * g' r) (Set.Ioi sigma) := by
  obtain ⟨g, g', hderiv, hg_eq⟩ := ozExterior_smooth_repr (eta := eta) (rho := rho) hsigma
  have hg'_int : MeasureTheory.IntegrableOn (fun r => g r + r * g' r) (Set.Ioi sigma) :=
    ozExterior_deriv_integrable (eta := eta) (rho := rho) heta0 heta1 hsigma hrho heta_def
      hderiv hg_eq
  refine ⟨g, g', hderiv, ?_, ?_,
    r_mul_ozBaxterFixedPt_tendsto_zero heta0 heta1 hsigma hrho heta_def,
    r_mul_ozBaxterFixedPt_integrableOn heta0 heta1 hsigma hrho heta_def, hg'_int⟩
  · intro r hr
    have hσr : sigma ≤ r := le_of_lt hr
    have hr0 : 0 < r := lt_trans hsigma hr
    rw [ozBaxterFixedPt_eq_div hsigma hr0, baxterPsi_outer hσr, ← hg_eq r hσr]
  · rw [hg_eq sigma (le_refl sigma), ozBaxterFixedPt_eq_div hsigma hsigma,
      baxterPsi_outer (le_refl sigma)]

end

end FMSA.HardSphere
