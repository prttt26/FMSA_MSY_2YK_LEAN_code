/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HardSphere.BaxterDilutePoleLocation
import LeanCode.HardSphere.BaxterNoSpinodalEquiv
import LeanCode.HardSphere.BaxterLowerHalfPlane

/-!
# Hermite–Biehler root location of the PY-HS Baxter symbol — Group MA axiom (awaiting processing)

Registry: `MATH_AXIOMS.md`, task `MA.14` (Hermite–Biehler root location). **Status: axiom on a
*bounded core*, awaiting processing (retire-by-proving intended — HB looks provable via `MA.11` + an
explicit winding count).**

## Goal and the elementary reduction

Task `POLE.11`'s root-location premise: for every physical `(η,σ,ρ)` (`0<η<1`, `σ>0`, `ρ>0`,
`η=πρσ³/6`), `G_baxter(k) = Npoly(k) − Dpoly(k)·e^{−ikσ}` has no zero on the closed lower half-plane
`{Im k ≤ 0}` away from `k = 0`; equivalently `Q̂ ≠ 1` there (every Baxter pole in the open UHP).

A zero in `{Im k ≤ 0}` forces `‖Npoly(k)‖ = ‖Dpoly(k)‖·e^{σ·Im k} ≤ ‖Dpoly(k)‖` (`e^{σ·Im k}≤1`).
So on the **norm-dominant outer region** `{‖Dpoly(k)‖ < ‖Npoly(k)‖}` there is **no zero, for all
`η<1`** — elementary (`G_baxter_ne_zero_of_norm_dominant`).  Since `‖Npoly‖ ∼ ‖k‖³` overtakes
`‖Dpoly‖ ∼ ‖k‖`, the complementary **core** `{‖Npoly(k)‖ ≤ ‖Dpoly(k)‖}` is **bounded** (compact
around the origin).  Thus the only genuinely non-elementary content of MA.14 is:

  **no zero of `G_baxter` on the bounded core `{Im k ≤ 0, k≠0, ‖Npoly‖ ≤ ‖Dpoly‖}`**  — Axiom 6.

## Why the core is still an axiom (for now), and why it is safe

On the core the norm bound is powerless (it fails worst on the **negative imaginary axis**, where
`G_baxter(−bi)` is *real* — verified — and where `‖Npoly‖ < ‖Dpoly‖`); nonvanishing there is a
**phase** fact.  It is TRUE for all `η<1` (numerically confirmed, incl. `G_baxter(−bi)<0` ∀`b>0`).

**It is NOT abstractable to a general quasi-polynomial — this is physics-contingent, not deferred.**
The property is *equivalent* to the PY-HS structure factor having **no spinodal** (no gas–liquid
transition), plus the Baxter factorization being the canonical Wiener–Hopf plus-factor. Precisely: a
spinodal ⟺ `1−ρĈ(k₀)=0` for some *real* `k₀` ⟺ `Q̂(k₀)=1` on the real axis (via the factorization
`1−ρĈ = (1−Q̂(k))(1−Q̂(−k))`) ⟺ a Baxter pole *on* `{Im k = 0}` — so `{Im k ≤ 0}`-nonvanishing already
*contains* "no spinodal", and additionally excludes the strict LHP. A general-coefficient
`cubic − linear·e^{−ikσ}` modelling a **spinodal-bearing** system therefore **violates** the
statement; only for PY-HS (proven spinodal-free — this *is* `BAXTER.16`) does it hold. Any
`Analysis/` abstraction would have to *carry* a no-spinodal / structure-factor-positivity hypothesis
(`= BAXTER.16`), so the axiom stays about the *defined* PY-HS symbol by necessity. **Retire-by-proving
is still open** (prove it for *this* symbol via `MA.11` + an explicit winding count on a lower
semicircle — which subsumes `BAXTER.16` as its real-axis boundary input), but **retire-by-abstracting
is off the table.** The dilute regime `η < (3−√7)/2` is already unconditional
(`baxter_pole_im_pos_of_dilute`), so the core axiom is invoked only for `η ≥ (3−√7)/2`.

## Consequences

`G_baxter_ne_zero_of_im_nonpos` / `qhat_complex_ne_one_of_im_nonpos` (full closed lower half-plane),
then `baxter_pole_im_pos` (every nonzero `G_baxter` zero in the open UHP), for all physical `η < 1`.
-/

open Complex

namespace FMSA.HardSphere

/-- **Baxter poles avoid the OPEN lower half-plane, bounded core — RETIRED AXIOM → THEOREM
(`MA.14`, 2026-07-21).**  `G_baxter ≠ 0` on the *strict* bounded core `{Im k < 0, k≠0,
‖Npoly‖ ≤ ‖Dpoly‖}`.  Formerly a domain-referencing math axiom; now proved (the `hcore` hypothesis is
not even needed — the stronger open-half-plane statement holds) via the `η`-homotopy of the zero
count, `Qhat_complex_ne_one_of_im_neg` (`BaxterLowerHalfPlane.lean`).  The only remaining input is the
pure-analysis homotopy-invariance axiom `zeroFree_lowerHalfPlane_of_homotopy`
(`Analysis/ZeroCountHomotopy.lean`), which is Mathlib's genuine gap (no Rouché / parametric argument
principle) — see `proof_notes_pole.md` → "POLE.11-general / MA.14". -/
theorem baxter_no_open_lhp_pole_core {eta sigma rho : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (hrho : 0 < rho) (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6)
    {k : ℂ} (hk : k.im < 0) (hk0 : k ≠ 0)
    (_hcore : ‖Npoly eta sigma rho k‖ ≤ ‖Dpoly eta sigma rho k‖) :
    G_baxter eta sigma rho k ≠ 0 := by
  intro hG
  have h1 : (1 : ℂ) - Qhat_complex eta sigma rho k = 0 :=
    (Qhat_pole_iff_G_baxter_zero eta sigma rho hsigma hk0).mpr hG
  exact Qhat_complex_ne_one_of_im_neg heta0 heta1 hsigma heta_def hk (sub_eq_zero.mp h1).symm

/-- **`G_baxter ≠ 0` on the closed lower half-plane** (`k ≠ 0`), all physical `η < 1`.  Three cases:
`‖Dpoly‖<‖Npoly‖` (elementary norm bound); else on the core `‖Npoly‖≤‖Dpoly‖`, `Im k < 0` (open-LHP
core axiom) or `Im k = 0` (real axis, via the **no-spinodal axiom** `qhat_complex_ne_one_of_real`
and the `(-ik)³` bridge). -/
theorem G_baxter_ne_zero_of_im_nonpos {eta sigma rho : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (hrho : 0 < rho) (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6)
    {k : ℂ} (hk : k.im ≤ 0) (hk0 : k ≠ 0) :
    G_baxter eta sigma rho k ≠ 0 := by
  rcases lt_or_ge ‖Dpoly eta sigma rho k‖ ‖Npoly eta sigma rho k‖ with hdom | hcore
  · exact G_baxter_ne_zero_of_norm_dominant hsigma hk hdom
  · rcases lt_or_eq_of_le hk with him | him
    · exact baxter_no_open_lhp_pole_core heta0 heta1 hsigma hrho heta_def him hk0 hcore
    · -- k.im = 0: real axis, discharge via the no-spinodal axiom
      have hkre : k = ((k.re : ℝ) : ℂ) := by
        rw [Complex.ext_iff]; refine ⟨rfl, ?_⟩; rw [Complex.ofReal_im]; exact him
      have hre0 : (k.re : ℝ) ≠ 0 := by
        intro hre; apply hk0; rw [Complex.ext_iff]; simp [hre, him]
      have hQ : Qhat_complex eta sigma rho k ≠ 1 := by
        rw [hkre]; exact qhat_complex_ne_one_of_real heta0 heta1 hsigma hrho heta_def hre0
      rw [← baxter_cube_mul_F_eq_G eta sigma rho hsigma hk0]
      exact mul_ne_zero (pow_ne_zero 3 (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hk0))
        (sub_ne_zero.mpr hQ.symm)

/-- **Hermite–Biehler root location of the PY-HS symbol.**  `Q̂ ≠ 1` on the closed lower half-plane,
all physical `η < 1` — via `G_baxter = (-ik)³(1-Q̂)`. -/
theorem qhat_complex_ne_one_of_im_nonpos {eta sigma rho : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (hrho : 0 < rho) (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6)
    {k : ℂ} (hk : k.im ≤ 0) (hk0 : k ≠ 0) :
    Qhat_complex eta sigma rho k ≠ 1 := by
  intro h
  have hG : G_baxter eta sigma rho k = 0 := by
    rw [← baxter_cube_mul_F_eq_G eta sigma rho hsigma hk0, h, sub_self, mul_zero]
  exact G_baxter_ne_zero_of_im_nonpos heta0 heta1 hsigma hrho heta_def hk hk0 hG

/-- **POLE.11 root-location premise, all physical `η < 1`.**  Every nonzero zero of `G_baxter` lies
in the open upper half-plane.  Consumes the Hermite–Biehler core axiom through the axiom-clean
reduction `baxter_pole_im_pos_of_symbol_ne_one`. -/
theorem baxter_pole_im_pos {eta sigma rho : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (hrho : 0 < rho) (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6)
    {k : ℂ} (hk_zero : G_baxter eta sigma rho k = 0) (hk0 : k ≠ 0) :
    0 < k.im :=
  baxter_pole_im_pos_of_symbol_ne_one hsigma
    (fun _z hz hz0 => qhat_complex_ne_one_of_im_nonpos heta0 heta1 hsigma hrho heta_def hz hz0)
    hk_zero hk0

end FMSA.HardSphere
