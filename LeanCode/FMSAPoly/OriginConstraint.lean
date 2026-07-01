/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib

/-!
# Task P.2 — Origin constraint: p0 = -E_ij(0) is necessary and sufficient

For like pairs (λ_ij = 0), the FMSA_poly inner-core DCF decomposes as
```
c^(1)_ij(r) = [E_ij(r) + P_ij(r)] / (2π√(rhoirhoj) · r)
```
This has a 1/r singularity.  The ratio is finite at r → 0 **iff** `E_ij(0) + P_ij(0) = 0`,
i.e., the polynomial constant term satisfies `p0 = -E_ij(0)`.

## Proof strategy for `origin_finiteness`

`HasDerivAt f f' x ↔ Tendsto (slope f x) (𝓝[≠] x) (𝓝 f')` via
`hasDerivAt_iff_tendsto_slope`.  Since `slope f 0 r = (f r - f 0)/(r - 0)` and `f 0 = 0`,
the slope equals `(E r + P r)/r` exactly.  Combining `hE.add hP` with this identification
closes the proof via two rewrites.

## Proof strategy for `origin_necessity`

Along `𝓝[≠] 0`: `(E r + P r)/r → L` and `r → 0`, so eventually
`E r + P r = r · ((E r + P r)/r)` and both factors → 0 and L, giving `E r + P r → 0`.
Continuity gives a second limit `E 0 + P 0`.  Since `𝓝[≠] 0` is NeBot in ℝ,
`tendsto_nhds_unique` forces `E 0 + P 0 = 0`.

## Main results

- `origin_finiteness` : `E 0 + P 0 = 0` + differentiability ⟹ limit is `e0 + p1`
- `origin_necessity`  : limit finite + continuity ⟹ `E 0 + P 0 = 0`
-/

set_option linter.style.longLine false
set_option linter.style.whitespace false

namespace FMSA.OriginConstraint

/-! ## Sufficiency -/

/-- **Origin finiteness — sufficiency (Task P.2):**
If `E 0 + P 0 = 0` and `E`, `P` have derivatives `e0`, `p1` at 0, then
```
  lim_{r → 0, r ≠ 0}  (E r + P r) / r  =  e0 + p1
```
This is the FMSA_poly renormalisation condition: setting `p0 = -E_ij(0)` kills the
1/r singularity and the L'Hôpital limit gives `E_ij'(0) + p1`. -/
theorem origin_finiteness {e0 p1 : ℝ} (E P : ℝ → ℝ) (h : E 0 + P 0 = 0)
    (hE : HasDerivAt E e0 0) (hP : HasDerivAt P p1 0) :
    Filter.Tendsto (fun r => (E r + P r) / r) (nhdsWithin 0 (Set.compl {0})) (nhds (e0 + p1)) := by
  -- Combine: HasDerivAt (E+P) (e0+p1) 0
  have hEP : HasDerivAt (fun r => E r + P r) (e0 + p1) 0 := hE.add hP
  -- Rewrite as a slope limit: Tendsto (slope (E+P) 0) (𝓝[≠] 0) (𝓝 (e0+p1))
  rw [hasDerivAt_iff_tendsto_slope] at hEP
  -- Since E 0 + P 0 = 0, the slope (E+P) 0 r = (E r + P r)/r
  -- Note: slope uses -ᵥ (AddTorsor subtraction); for ℝ, vsub_eq_sub converts it to -
  have key : slope (fun r => E r + P r) 0 = fun r => (E r + P r) / r := by
    funext r
    unfold slope
    simp only [sub_zero, smul_eq_mul, vsub_eq_sub]
    rw [h, sub_zero]
    ring
  rwa [key] at hEP

/-! ## Necessity -/

/-- **Origin finiteness — necessity (Task P.2):**
If `E`, `P` are continuous at 0 and `(E r + P r)/r` converges to `L`, then `E 0 + P 0 = 0`.

Proof: eventually `E r + P r = r · ((E r + P r)/r) → 0 · L = 0` along `𝓝[≠] 0`,
while continuity gives `E r + P r → E 0 + P 0`.  Since `𝓝[≠] 0` is NeBot,
`tendsto_nhds_unique` forces `E 0 + P 0 = 0`. -/
theorem origin_necessity (E P : ℝ → ℝ)
    (hcE : ContinuousAt E 0) (hcP : ContinuousAt P 0)
    {L : ℝ} (hL : Filter.Tendsto (fun r => (E r + P r) / r) (nhdsWithin 0 (Set.compl {0})) (nhds L)) :
    E 0 + P 0 = 0 := by
  -- id(r) = r → 0 along 𝓝[≠] 0
  have hr : Filter.Tendsto (fun r : ℝ => r) (nhdsWithin 0 (Set.compl {0})) (nhds 0) :=
    Filter.tendsto_id.mono_left nhdsWithin_le_nhds
  -- (E r + P r) → 0: use bound |E r + P r| = |r| · |(E r + P r)/r|
  have h0 : Filter.Tendsto (fun r => E r + P r) (nhdsWithin 0 (Set.compl {0})) (nhds 0) := by
    -- step 1: r * ((E r + P r) / r) → 0 * L = 0
    have hprod : Filter.Tendsto (fun r : ℝ => r * ((E r + P r) / r))
        (nhdsWithin 0 (Set.compl {0})) (nhds 0) := by
      have hmul : Filter.Tendsto (fun r : ℝ => r * ((E r + P r) / r))
                  (nhdsWithin 0 (Set.compl {0})) (nhds (0 * L)) :=
        Filter.Tendsto.mul (a := (0 : ℝ)) (b := L) hr hL
      simpa [zero_mul] using hmul
    -- step 2: for r ≠ 0, r * ((E r + P r) / r) = E r + P r
    refine hprod.congr' (eventually_nhdsWithin_of_forall fun r hne => ?_)
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hne
    field_simp [hne]
  -- By continuity, E r + P r → E 0 + P 0 along 𝓝[≠] 0
  have hcont : Filter.Tendsto (fun r => E r + P r) (nhdsWithin 0 (Set.compl {0})) (nhds (E 0 + P 0)) :=
    (hcE.add hcP).tendsto.mono_left nhdsWithin_le_nhds
  -- 𝓝[≠] 0 is NeBot: ℝ has no isolated points
  haveI : Filter.NeBot (nhdsWithin (0 : ℝ) (Set.compl {0})) := inferInstance
  exact (tendsto_nhds_unique h0 hcont).symm

end FMSA.OriginConstraint
