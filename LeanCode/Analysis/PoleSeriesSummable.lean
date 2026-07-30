/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib

/-!
# Summability of a Mittag-Leffler pole series

The term `Bcoef n / (sfam n)ᵏ`-style summand of a pole expansion, and two summability criteria for
it. Both coefficient sequences `Bcoef sfam : ℕ → ℂ` are **arbitrary** — no hard-sphere or Yukawa
object enters, which is why this lives in `Analysis/` (split out of
`YukawaDCF/MixtureMLSeries.lean` on 2026-07-19, so that `MixtureMLBound` — which uses only these —
no longer has to import the Yukawa-carrying half).

* `poleExpTerm_summable_of_decay` — a direct `‖term n‖ ≤ C·(n+1)^p`, `p < −1` comparison.
* `poleExpTerm_summable_of_growth` — the usable form: linear growth `c·n + d ≤ ‖sfam n‖` of the pole
  moduli plus `‖term n‖ ≤ C·‖sfam n‖^p` again gives summability.

The identifiers were **renamed to content-descriptive names 2026-07-27** (`MRS.9d`): the historical
`mixHS*` prefix (from the mixture hard-sphere development they were extracted from) reflected no
dependency — the statements are generic — so `mixHSterm`/`mixHS_series`/`mixHS_summable`/
`mixHS_summable_of_growth` became `poleExpTerm`/`poleExpSeriesRe`/`poleExpTerm_summable_of_decay`/
`poleExpTerm_summable_of_growth`. The domain-layer *derived* objects (`mixHSterm2`, `mixHS_series2`,
`mixHSAntideriv*`, `detF_mixHS_summable`) keep their `mixHS*` names — they are genuinely mixture-HS
specific and live in `YukawaDCF/`/`HSMixture/`, where a domain prefix is correct.
-/

set_option linter.style.longLine false

open Filter Topology

namespace FMSA.PoleSeries

/-- **MML.4 — per-pole HS-pole term** `B_k · exp(−s_k · r)` over abstract coefficient/pole
families `Bcoef`, `sfam`. -/
noncomputable def poleExpTerm (Bcoef sfam : ℕ → ℂ) (r : ℝ) (n : ℕ) : ℂ :=
  Bcoef n * Complex.exp (-(sfam n) * (r : ℂ))

/-- **MML.4 — the HS-pole Mittag-Leffler series** `Σ_k 2·Re[B_k · exp(−s_k · r)]` (term (II) of
the inner DCF). Written as `2·Re` of the complex tsum; when `poleExpTerm` is `Summable` this equals
`∑' n, 2·Re[poleExpTerm n]`. -/
noncomputable def poleExpSeriesRe (Bcoef sfam : ℕ → ℂ) (r : ℝ) : ℝ :=
  2 * (∑' n : ℕ, poleExpTerm Bcoef sfam r n).re

/-- **MML.5 (abstract) — summability of the HS-pole Mittag-Leffler series.**  Given the magnitude
decay `‖poleExpTerm n‖ ≤ C·(n+1)^p` with `p < −1`, the term family is `Summable`.  Mirrors the scalar
`h_explicit_summable` (`HardSphere/BaxterResidue.lean`): reduce to `Summable (n ↦ (n+1)^p)` via
`Real.summable_nat_rpow` (`p < −1`) + index shift, then `Summable.of_norm_bounded`.  The decay-law
hypothesis is discharged concretely by the deferred **MML.5-concrete** gate (POLE.5-analog for
`detC`). -/
theorem poleExpTerm_summable_of_decay {Bcoef sfam : ℕ → ℂ} {r : ℝ} {C p : ℝ} (hp : p < -1)
    (hbound : ∀ n : ℕ, ‖poleExpTerm Bcoef sfam r n‖ ≤ C * ((n : ℝ) + 1) ^ p) :
    Summable (poleExpTerm Bcoef sfam r) := by
  have h0 : Summable (fun n : ℕ => (n : ℝ) ^ p) := Real.summable_nat_rpow.mpr hp
  have h1 : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ p) :=
    (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ p) 1).mpr h0
  have hg : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ p) := by
    convert h1 using 2 with n
    push_cast
    ring
  exact Summable.of_norm_bounded (hg.mul_left C) hbound

/-- **MML.5 (pole-family reduction) — summability from linear pole growth + a `‖s_k‖`-power bound.**
Given the pole family grows at least linearly (`c·n+d ≤ ‖sfam n‖`, `c,d>0`) and each term obeys the
power bound `‖poleExpTerm n‖ ≤ C·‖sfam n‖^p` with `p < −1` (the shape a POLE.5-analog for `detC` would
produce), the series is `Summable`. Converts the `‖s_k‖`-power bound to the `n`-indexed
`(n+1)^p` form of `poleExpTerm_summable_of_decay` via the negative-exponent `rpow` antitone step
(`Real.rpow_le_rpow_iff_of_neg`) — mirrors `h_explicit_summable_of_pole_family`. With
`exists_zero_family_growth_of_chordPoleFamily` supplying the growth witness, this reduces
MML.5-concrete to the **single** isolated obligation: the per-pole magnitude bound
`‖B_k‖·e^{−r·Re s_k} ≤ C·‖s_k‖^p`. -/
theorem poleExpTerm_summable_of_growth {Bcoef sfam : ℕ → ℂ} {r : ℝ} {C p c d : ℝ}
    (hp : p < -1) (hC : 0 ≤ C) (hc : 0 < c) (hd : 0 < d)
    (hgrowth : ∀ n : ℕ, c * (n : ℝ) + d ≤ ‖sfam n‖)
    (hbound : ∀ n : ℕ, ‖poleExpTerm Bcoef sfam r n‖ ≤ C * ‖sfam n‖ ^ p) :
    Summable (poleExpTerm Bcoef sfam r) := by
  have hpneg : p < 0 := by linarith
  apply poleExpTerm_summable_of_decay (C := C * (min c d) ^ p) hp
  intro n
  have hcd : 0 < min c d := lt_min hc hd
  have hpos : (0 : ℝ) < c * (n : ℝ) + d := by positivity
  have hsfampos : 0 < ‖sfam n‖ := lt_of_lt_of_le hpos (hgrowth n)
  have h1 : ‖sfam n‖ ^ p ≤ (c * (n : ℝ) + d) ^ p :=
    (Real.rpow_le_rpow_iff_of_neg hsfampos hpos hpneg).mpr (hgrowth n)
  have hcdn : (min c d) * ((n : ℝ) + 1) ≤ c * (n : ℝ) + d := by
    rcases le_or_gt c d with hle | hle
    · rw [min_eq_left hle]; nlinarith [Nat.cast_nonneg n (α := ℝ)]
    · rw [min_eq_right hle.le]; nlinarith [Nat.cast_nonneg n (α := ℝ), hle]
  have hmincdnp1 : (0 : ℝ) < (min c d) * ((n : ℝ) + 1) := by positivity
  have h2 : (c * (n : ℝ) + d) ^ p ≤ ((min c d) * ((n : ℝ) + 1)) ^ p :=
    (Real.rpow_le_rpow_iff_of_neg hpos hmincdnp1 hpneg).mpr hcdn
  have h3 : ((min c d) * ((n : ℝ) + 1)) ^ p = (min c d) ^ p * ((n : ℝ) + 1) ^ p :=
    Real.mul_rpow hcd.le (by positivity)
  calc ‖poleExpTerm Bcoef sfam r n‖
      ≤ C * ‖sfam n‖ ^ p := hbound n
    _ ≤ C * (c * (n : ℝ) + d) ^ p := mul_le_mul_of_nonneg_left h1 hC
    _ ≤ C * ((min c d) ^ p * ((n : ℝ) + 1) ^ p) := by
        rw [← h3]; exact mul_le_mul_of_nonneg_left h2 hC
    _ = C * (min c d) ^ p * ((n : ℝ) + 1) ^ p := by ring

end FMSA.PoleSeries
