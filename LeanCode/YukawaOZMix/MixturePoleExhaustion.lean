/-
Copyright (c) 2026 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.YukawaOZMix.MixtureInnerDCF

/-!
# MML.8 — pole-exhaustion: the completeness bundle, and why MZERO.1 cannot supply it

`MixRDFInnerCollapse` (`MixtureInnerDCF.lean`) is held as a `Prop`, not an axiom, because a naive
axiom form — quantifying only over "`(α, β, sfam)` is *some* injective growth-family of `det Q̂₀`
zeros" — would be **false**: a strict sub-family satisfies exactly those constraints yet sums the
Mittag–Leffler series to the wrong value (the OZFIX.12/14 sub-family trap). What an axiom form is
missing is the **completeness bundle**: exhaustion of the upper-half-plane zeros of `det Q̂₀` up to
the mirror pairing `z ↦ −z̄`.  `MZERO.1` (`detC_zeros_infinite`) supplies *infinitude*, not
exhaustion.

This file makes that gap a **theorem** rather than a numeric observation.  Working abstractly over
any `detF : ℂ → ℂ` (take `detF := fun z => (q0Mat P z).det`, the mixture Baxter determinant
whose UHP zeros are exactly the structure-factor `S₀` poles of `MixtureRDFStructureFactor.lean`):

* `PoleExhaustion detF kfam` — the completeness predicate: every UHP zero of `detF` is some `kfam n`
  or its mirror `−conj (kfam n)`.
* `MirrorFree kfam` — non-degeneracy of the pairing (no representative is another's mirror).
* `even_subfamily_meets_constraints` — the even sub-family `n ↦ kfam (2n)` satisfies EVERY
  constraint the collapse's consumer imposes (injective, all values UHP zeros, same growth bound).
* `even_subfamily_not_exhaustive` — **yet it is NOT pole-exhaustive** (it misses `kfam 1`).  So no
  amount of MZERO.1-style infinitude/injectivity/growth data pins the exhaustive family:
  exhaustion is a genuine extra input, and the naive axiom form of `MixRDFInnerCollapse` would be
  dischargeable by a wrong-summing sub-family.  This is the scalar OZFIX.14 counterexample,
  upgraded to a family-independent theorem.

**Consequence for MML.8.** The literal pole-series route (`MixRDFInnerCollapse`) is blocked on
exactly this exhaustion — an argument-principle pole-count that `detC_zeros_infinite` does not
give, and whose contour derivation is provably Fourier-circular (OZFIX.12/14).  The project
therefore closes MML.8 by the **non-circular** value route `matOzStar_unique`
(`MixtureRDFUniqueness.lean`): matrix
`oz_fixed_pt_unique` from the coercive structure factor `det Q̂₀ ≠ 0` (`mixtureDet_pole_free_N` +
`pyhs_mixture_no_spinodal`), which needs no pole enumeration at all.  This file records why the
alternative route stays a hypothesis.
-/

namespace FMSA.MixtureMLSeries
open FMSA.MixtureHSPoles

open Complex

/-- **Pole-exhaustion — the completeness bundle `MixRDFInnerCollapse` needs.**  Every
upper-half-plane zero of `detF` is caught by the family up to the mirror pairing `z ↦ −z̄`.  For
`detF = det Q̂₀` this is exhaustion of the structure-factor poles, `MZERO.1` (infinitude) misses. -/
def PoleExhaustion (detF : ℂ → ℂ) (kfam : ℕ → ℂ) : Prop :=
  ∀ z : ℂ, 0 < z.im → detF z = 0 → ∃ n, z = kfam n ∨ z = -(starRingEnd ℂ) (kfam n)

/-- **Mirror-free family** — non-degeneracy of the pairing: no representative equals another's
mirror `−conj`.  (The `m = n` case rules out purely-imaginary poles, which would double-count.) -/
def MirrorFree (kfam : ℕ → ℂ) : Prop :=
  ∀ m n, kfam m ≠ -(starRingEnd ℂ) (kfam n)

/-- The even sub-family inherits injectivity. -/
theorem even_subfamily_injective {kfam : ℕ → ℂ} (hinj : Function.Injective kfam) :
    Function.Injective (fun n => kfam (2 * n)) := by
  intro a b hab
  have h : 2 * a = 2 * b := hinj hab
  omega

/-- The even sub-family inherits the growth bound (same constants, `c ≥ 0`). -/
theorem even_subfamily_growth {kfam : ℕ → ℂ} {c d : ℝ} (hc : 0 ≤ c)
    (hg : ∀ n : ℕ, c * (n : ℝ) + d ≤ ‖kfam n‖) (n : ℕ) :
    c * (n : ℝ) + d ≤ ‖kfam (2 * n)‖ := by
  have h := hg (2 * n)
  push_cast at h
  nlinarith [h, hc, Nat.cast_nonneg (α := ℝ) n]

/-- **The even sub-family meets every constraint the collapse's consumer imposes** — injective, all
values UHP zeros, and the same growth bound.  So the constraint pack MZERO.1 + the growth lemmas
supply is satisfied by this sub-family. -/
theorem even_subfamily_meets_constraints {detF : ℂ → ℂ} {kfam : ℕ → ℂ} {c d : ℝ} (hc : 0 ≤ c)
    (him : ∀ n, 0 < (kfam n).im) (hzero : ∀ n, detF (kfam n) = 0)
    (hinj : Function.Injective kfam) (hg : ∀ n : ℕ, c * (n : ℝ) + d ≤ ‖kfam n‖) :
    Function.Injective (fun n => kfam (2 * n))
      ∧ (∀ n, 0 < (kfam (2 * n)).im)
      ∧ (∀ n, detF (kfam (2 * n)) = 0)
      ∧ (∀ n : ℕ, c * (n : ℝ) + d ≤ ‖kfam (2 * n)‖) :=
  ⟨even_subfamily_injective hinj, fun _ => him _, fun _ => hzero _,
    fun n => even_subfamily_growth hc hg n⟩

/-- **Pole-exhaustion is STRICTLY stronger than the infinitude/injectivity/growth pack.**  Given a
family whose values are all UHP zeros (`him`, `hzero`), injective (`hinj`), and mirror-free (`hmf`)
— every constraint the collapse's consumer imposes — its even sub-family `n ↦ kfam (2n)` STILL meets
all of them (`even_subfamily_meets_constraints`) yet is NOT pole-exhaustive: it misses `kfam 1`
(odd index, so `≠ kfam (2n)` by injectivity; `≠ -conj (kfam (2n))` by mirror-freeness).  So the
MZERO.1 infinitude/growth data can never pin the exhaustive family — exhaustion is a genuine
input, and the naive axiom form of `MixRDFInnerCollapse` (over only the constraint pack) would be
dischargeable by this wrong-summing sub-family.  This is the scalar OZFIX.14 numeric counterexample,
upgraded to a family-independent theorem. -/
theorem even_subfamily_not_exhaustive {detF : ℂ → ℂ} {kfam : ℕ → ℂ}
    (him : ∀ n, 0 < (kfam n).im) (hzero : ∀ n, detF (kfam n) = 0)
    (hinj : Function.Injective kfam) (hmf : MirrorFree kfam) :
    ¬ PoleExhaustion detF (fun n => kfam (2 * n)) := by
  intro hex
  obtain ⟨n, hn⟩ := hex (kfam 1) (him 1) (hzero 1)
  rcases hn with hn | hn
  · have h1 : (1 : ℕ) = 2 * n := hinj hn
    omega
  · exact hmf 1 (2 * n) hn

end FMSA.MixtureMLSeries
