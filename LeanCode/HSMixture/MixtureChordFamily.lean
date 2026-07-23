/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HSMixture.MixtureHSZeros
import LeanCode.HardSphere.BaxterChordFamily

/-!
# MZERO.5 — a concrete `ChordPoleFamily` for the N=2 mixture determinant `detC`

Constructs, for physical parameters (`0 < σ₀ < σ₁`, all `ρ`-geometric and Baxter `Q'`, `Q''`
entries positive), a `FMSA.BanachPoleFamily.ChordPoleFamily (detC …)` and fires the shared
`zeros_infinite_of_chordPoleFamily` to conclude that `det(Q̂₀_c)` has infinitely many complex
zeros — the mixture side of the shared MZERO.5/POLE.3 obligation, mirroring the 1-frequency
template `LeanCode/HardSphere/BaxterChordFamily.lean`.

## Skeleton

* **Monomial bridge**: `s⁶·detC(s) = Mc(s) + M₀(s)e^{-sσ₀} + M₁(s)e^{-sσ₁} + M₀₁(s)e^{-s(σ₀+σ₁)}`
  with four explicit polynomials (`detC_monomial_eq`), from `detC_lam_free`.
* **Log-lift guess** at anchors `i·Y`, `Y = 2πn/σ₁`, with exact phase kill
  `e^{-g σ₁} = t := ‖Mc(iY)‖/‖M₁(iY)‖`.
* **Anchor envelopes** `Y⁶/2 ≤ ‖Mc(iY)‖ ≤ 2Y⁶`, `(μ/2)Y⁴ ≤ ‖M₁(iY)‖ ≤ (μ+K₁)Y⁴` and the
  branch-safety sign `0 ≤ Re(Mc·conj(−M₁))` at the anchor.
* **Chord bounds** on disks of radius `1/(20σ₁)` for `F' = (W' − 6s⁵detC)/s⁶`, with the
  crude two-point polynomial estimates replacing MVT drifts (the budget has a full power of
  `Y` slack), and the `σ₀ < σ₁` gap killing the `e^{-sσ₀}` perturbations.

## MML.5-concrete (Stage B) — the per-pole magnitude gate

Building on the same family, the file also delivers the decay input of the mixture Mittag-Leffler
series (`YukawaDCF/MixtureMLSeries.lean`):

* `detF_zero_family_in_disks` — the chord-Newton zeros **with** their disk membership (the generic
  `exists_zero_family_growth_of_chordPoleFamily` forgets it, and the magnitude bounds need it).
* `detF_zero_family_growth` — injective zero family with linear growth `c·n + d ≤ ‖g n‖`.
* `disk_facts` — the three uniform facts on each disk: `‖s‖ ≥ 1`, the log-lift deviation
  `|(−Re s) − 2·log‖s‖/σ₁| ≤ Kdev`, and the **`Θ(1)` derivative floor**
  `‖F′(s)‖ ≥ σ₁μ/(24(μ+K₁))`.
* `q01_norm_le` — envelope for the `(0,1)` Baxter entry `q01` (= `Q̂₀_c(s) 0 1`, `q01_eq`).
* `magnitude_bound_at` / `detF_family_magnitude_bound` — the MML.5 gate
  `‖q01(g n)‖·e^{r·Re(g n)}/‖F′(g n)‖ ≤ Cmag·‖g n‖^{p(r)}` with
  `p(r) = max((σ₀−σ₁−2r)/σ₁, (−σ₀−2r)/σ₁) < −1` for `r > max(σ₀/2, (σ₁−σ₀)/2)`.
-/

set_option linter.style.longLine false

open Filter Topology
open FMSA.BanachPoleFamily

namespace FMSA.MixtureHSPoles

noncomputable section

/-! ### Parameter pack and the polynomial building blocks -/

/-- The physical data of the N=2 mixture determinant: diameters `sig0 < sig1`, geometric
density matrix `rr`, Baxter contact data `Qp` (`Q'`) and `Qpp` (`Q''`). -/
structure MixParams where
  /-- diameter of species 0 -/
  sig0 : ℝ
  /-- diameter of species 1 -/
  sig1 : ℝ
  /-- geometric density matrix `√(ρᵢρⱼ)`-type weights -/
  rr : Fin 2 → Fin 2 → ℝ
  /-- Baxter `Q'` contact matrix -/
  Qp : Fin 2 → Fin 2 → ℝ
  /-- Baxter `Q''` contact matrix -/
  Qpp : Fin 2 → Fin 2 → ℝ

/-- Physicality: ordered positive diameters and entrywise positive matrices. -/
def MixParams.Phys (P : MixParams) : Prop :=
  0 < P.sig0 ∧ P.sig0 < P.sig1 ∧ (∀ i j, 0 < P.rr i j) ∧
    (∀ i j, 0 < P.Qp i j) ∧ (∀ i j, 0 < P.Qpp i j)

/-- The mixture determinant as a function of the parameter pack (thin wrapper over `detC`). -/
def MixParams.detF (P : MixParams) : ℂ → ℂ :=
  detC ![P.sig0, P.sig1] (fun i j => (P.rr i j : ℂ)) (fun i j => (P.Qp i j : ℂ))
    (fun i j => (P.Qpp i j : ℂ))

/-- Quadratic Baxter bracket polynomial: `s³·(Q'φ₁ + Q''φ₂)` with the `e^{-sσ}` part removed. -/
def polyB (qp qpp sg : ℝ) (s : ℂ) : ℂ :=
  (qp : ℂ) * s * (1 - s * (sg : ℂ)) +
    (qpp : ℂ) * (1 - s * (sg : ℂ) + (s * (sg : ℂ)) ^ 2 / 2)

/-- Linear exponential-coefficient polynomial: the `e^{-sσ}` coefficient `Q'·s + Q''`. -/
def polyF (qp qpp : ℝ) (s : ℂ) : ℂ := (qp : ℂ) * s + (qpp : ℂ)

/-- Derivative of `polyB`. -/
def polyBD (qp qpp sg : ℝ) (s : ℂ) : ℂ :=
  (qp : ℂ) * (1 - 2 * s * (sg : ℂ)) + (qpp : ℂ) * (-(sg : ℂ) + s * (sg : ℂ) ^ 2)

/-- Cleared diagonal entry: `s³·dᵢ(s)` with the exponential part removed. -/
def dNum (rho qp qpp sg : ℝ) (s : ℂ) : ℂ := s ^ 3 - (rho : ℂ) * polyB qp qpp sg s

/-- Derivative of `dNum`. -/
def dNumD (rho qp qpp sg : ℝ) (s : ℂ) : ℂ := 3 * s ^ 2 - (rho : ℂ) * polyBD qp qpp sg s

/-! ### The four monomial-coefficient polynomials of `s⁶·detC` -/

/-- Exponential-free coefficient (degree 6, leading coefficient 1). -/
def McNum (P : MixParams) (s : ℂ) : ℂ :=
  dNum (P.rr 0 0) (P.Qp 0 0) (P.Qpp 0 0) P.sig0 s *
      dNum (P.rr 1 1) (P.Qp 1 1) (P.Qpp 1 1) P.sig1 s -
    ((P.rr 0 1 * P.rr 1 0 : ℝ) : ℂ) *
      (polyB (P.Qp 0 1) (P.Qpp 0 1) P.sig0 s * polyB (P.Qp 1 0) (P.Qpp 1 0) P.sig1 s)

/-- Coefficient of `e^{-s σ₀}` (degree 4). -/
def M0Num (P : MixParams) (s : ℂ) : ℂ :=
  ((P.rr 0 0 : ℝ) : ℂ) * polyF (P.Qp 0 0) (P.Qpp 0 0) s *
      dNum (P.rr 1 1) (P.Qp 1 1) (P.Qpp 1 1) P.sig1 s +
    ((P.rr 0 1 * P.rr 1 0 : ℝ) : ℂ) *
      (polyF (P.Qp 0 1) (P.Qpp 0 1) s * polyB (P.Qp 1 0) (P.Qpp 1 0) P.sig1 s)

/-- Coefficient of `e^{-s σ₁}` (degree 4, leading coefficient `μ = rr₁₁·Q'₁₁ > 0`). -/
def M1Num (P : MixParams) (s : ℂ) : ℂ :=
  dNum (P.rr 0 0) (P.Qp 0 0) (P.Qpp 0 0) P.sig0 s *
      (((P.rr 1 1 : ℝ) : ℂ) * polyF (P.Qp 1 1) (P.Qpp 1 1) s) +
    ((P.rr 0 1 * P.rr 1 0 : ℝ) : ℂ) *
      (polyB (P.Qp 0 1) (P.Qpp 0 1) P.sig0 s * polyF (P.Qp 1 0) (P.Qpp 1 0) s)

/-- Coefficient of `e^{-s(σ₀+σ₁)}` (degree 2). -/
def M01Num (P : MixParams) (s : ℂ) : ℂ :=
  ((P.rr 0 0 : ℝ) : ℂ) * polyF (P.Qp 0 0) (P.Qpp 0 0) s *
      (((P.rr 1 1 : ℝ) : ℂ) * polyF (P.Qp 1 1) (P.Qpp 1 1) s) -
    ((P.rr 0 1 * P.rr 1 0 : ℝ) : ℂ) *
      (polyF (P.Qp 0 1) (P.Qpp 0 1) s * polyF (P.Qp 1 0) (P.Qpp 1 0) s)

/-- The leading coefficient `μ := rr₁₁·Q'₁₁` of `M1Num`. -/
def MixParams.mu (P : MixParams) : ℝ := P.rr 1 1 * P.Qp 1 1

/-- The entire monomial form `W(s) := s⁶·detC(s)` (equality holding for `s ≠ 0`). -/
def Wfun (P : MixParams) (s : ℂ) : ℂ :=
  McNum P s + M0Num P s * Complex.exp (-(s * (P.sig0 : ℂ))) +
    M1Num P s * Complex.exp (-(s * (P.sig1 : ℂ))) +
    M01Num P s * Complex.exp (-(s * ((P.sig0 + P.sig1 : ℝ) : ℂ)))

/-! ### Derivative polynomials and `HasDerivAt` facts -/

/-- Derivative polynomial of `McNum` (product-rule shape). -/
def McD (P : MixParams) (s : ℂ) : ℂ :=
  dNumD (P.rr 0 0) (P.Qp 0 0) (P.Qpp 0 0) P.sig0 s *
      dNum (P.rr 1 1) (P.Qp 1 1) (P.Qpp 1 1) P.sig1 s +
    dNum (P.rr 0 0) (P.Qp 0 0) (P.Qpp 0 0) P.sig0 s *
      dNumD (P.rr 1 1) (P.Qp 1 1) (P.Qpp 1 1) P.sig1 s -
    ((P.rr 0 1 * P.rr 1 0 : ℝ) : ℂ) *
      (polyBD (P.Qp 0 1) (P.Qpp 0 1) P.sig0 s * polyB (P.Qp 1 0) (P.Qpp 1 0) P.sig1 s +
        polyB (P.Qp 0 1) (P.Qpp 0 1) P.sig0 s * polyBD (P.Qp 1 0) (P.Qpp 1 0) P.sig1 s)

/-- Derivative polynomial of `M0Num`. -/
def M0D (P : MixParams) (s : ℂ) : ℂ :=
  ((P.rr 0 0 : ℝ) : ℂ) * (P.Qp 0 0 : ℂ) *
      dNum (P.rr 1 1) (P.Qp 1 1) (P.Qpp 1 1) P.sig1 s +
    ((P.rr 0 0 : ℝ) : ℂ) * polyF (P.Qp 0 0) (P.Qpp 0 0) s *
      dNumD (P.rr 1 1) (P.Qp 1 1) (P.Qpp 1 1) P.sig1 s +
    ((P.rr 0 1 * P.rr 1 0 : ℝ) : ℂ) *
      ((P.Qp 0 1 : ℂ) * polyB (P.Qp 1 0) (P.Qpp 1 0) P.sig1 s +
        polyF (P.Qp 0 1) (P.Qpp 0 1) s * polyBD (P.Qp 1 0) (P.Qpp 1 0) P.sig1 s)

/-- Derivative polynomial of `M1Num`. -/
def M1D (P : MixParams) (s : ℂ) : ℂ :=
  dNumD (P.rr 0 0) (P.Qp 0 0) (P.Qpp 0 0) P.sig0 s *
      (((P.rr 1 1 : ℝ) : ℂ) * polyF (P.Qp 1 1) (P.Qpp 1 1) s) +
    dNum (P.rr 0 0) (P.Qp 0 0) (P.Qpp 0 0) P.sig0 s *
      (((P.rr 1 1 : ℝ) : ℂ) * (P.Qp 1 1 : ℂ)) +
    ((P.rr 0 1 * P.rr 1 0 : ℝ) : ℂ) *
      (polyBD (P.Qp 0 1) (P.Qpp 0 1) P.sig0 s * polyF (P.Qp 1 0) (P.Qpp 1 0) s +
        polyB (P.Qp 0 1) (P.Qpp 0 1) P.sig0 s * (P.Qp 1 0 : ℂ))

/-- Derivative polynomial of `M01Num`. -/
def M01D (P : MixParams) (s : ℂ) : ℂ :=
  ((P.rr 0 0 : ℝ) : ℂ) * (P.Qp 0 0 : ℂ) *
      (((P.rr 1 1 : ℝ) : ℂ) * polyF (P.Qp 1 1) (P.Qpp 1 1) s) +
    ((P.rr 0 0 : ℝ) : ℂ) * polyF (P.Qp 0 0) (P.Qpp 0 0) s *
      (((P.rr 1 1 : ℝ) : ℂ) * (P.Qp 1 1 : ℂ)) -
    ((P.rr 0 1 * P.rr 1 0 : ℝ) : ℂ) *
      ((P.Qp 0 1 : ℂ) * polyF (P.Qp 1 0) (P.Qpp 1 0) s +
        polyF (P.Qp 0 1) (P.Qpp 0 1) s * (P.Qp 1 0 : ℂ))

/-- Derivative of the entire monomial form `Wfun`. -/
def WD (P : MixParams) (s : ℂ) : ℂ :=
  McD P s +
    (M0D P s - (P.sig0 : ℂ) * M0Num P s) * Complex.exp (-(s * (P.sig0 : ℂ))) +
    (M1D P s - (P.sig1 : ℂ) * M1Num P s) * Complex.exp (-(s * (P.sig1 : ℂ))) +
    (M01D P s - ((P.sig0 + P.sig1 : ℝ) : ℂ) * M01Num P s) *
      Complex.exp (-(s * ((P.sig0 + P.sig1 : ℝ) : ℂ)))

/-- `polyB` differentiates to `polyBD`. -/
theorem polyB_hasDerivAt (qp qpp sg : ℝ) (s : ℂ) :
    HasDerivAt (polyB qp qpp sg) (polyBD qp qpp sg s) s := by
  have hu : HasDerivAt (fun s : ℂ => (qp : ℂ) * s) ((qp : ℂ) * 1) s :=
    (hasDerivAt_id s).const_mul (qp : ℂ)
  have hv : HasDerivAt (fun s : ℂ => 1 - s * (sg : ℂ)) (-(1 * (sg : ℂ))) s :=
    ((hasDerivAt_id s).mul_const (sg : ℂ)).const_sub 1
  have hw : HasDerivAt (fun s : ℂ => s * (sg : ℂ)) (1 * (sg : ℂ)) s :=
    (hasDerivAt_id s).mul_const (sg : ℂ)
  have hsq : HasDerivAt (fun s : ℂ => (s * (sg : ℂ)) ^ 2)
      ((2 : ℕ) * (s * (sg : ℂ)) ^ 1 * (1 * (sg : ℂ))) s := hw.pow 2
  have hinner : HasDerivAt (fun s : ℂ => 1 - s * (sg : ℂ) + (s * (sg : ℂ)) ^ 2 / 2)
      (-(1 * (sg : ℂ)) + (2 : ℕ) * (s * (sg : ℂ)) ^ 1 * (1 * (sg : ℂ)) / 2) s :=
    hv.add (hsq.div_const 2)
  have h := (hu.mul hv).add (hinner.const_mul (qpp : ℂ))
  refine h.congr_deriv ?_
  unfold polyBD
  push_cast
  ring

/-- `polyF` differentiates to the constant `qp`. -/
theorem polyF_hasDerivAt (qp qpp : ℝ) (s : ℂ) :
    HasDerivAt (polyF qp qpp) ((qp : ℂ)) s := by
  have h := ((hasDerivAt_id s).const_mul (qp : ℂ)).add_const (qpp : ℂ)
  exact h.congr_deriv (by ring)

/-- `dNum` differentiates to `dNumD`. -/
theorem dNum_hasDerivAt (rho qp qpp sg : ℝ) (s : ℂ) :
    HasDerivAt (dNum rho qp qpp sg) (dNumD rho qp qpp sg s) s := by
  have h := (hasDerivAt_pow 3 s).sub ((polyB_hasDerivAt qp qpp sg s).const_mul (rho : ℂ))
  refine h.congr_deriv ?_
  unfold dNumD
  push_cast
  ring

/-- `McNum` differentiates to `McD`. -/
theorem McNum_hasDerivAt (P : MixParams) (s : ℂ) :
    HasDerivAt (McNum P) (McD P s) s := by
  have h := ((dNum_hasDerivAt (P.rr 0 0) (P.Qp 0 0) (P.Qpp 0 0) P.sig0 s).mul
      (dNum_hasDerivAt (P.rr 1 1) (P.Qp 1 1) (P.Qpp 1 1) P.sig1 s)).sub
    (((polyB_hasDerivAt (P.Qp 0 1) (P.Qpp 0 1) P.sig0 s).mul
      (polyB_hasDerivAt (P.Qp 1 0) (P.Qpp 1 0) P.sig1 s)).const_mul
        ((P.rr 0 1 * P.rr 1 0 : ℝ) : ℂ))
  refine h.congr_deriv ?_
  unfold McD
  ring

/-- `M0Num` differentiates to `M0D`. -/
theorem M0Num_hasDerivAt (P : MixParams) (s : ℂ) :
    HasDerivAt (M0Num P) (M0D P s) s := by
  have h := (((polyF_hasDerivAt (P.Qp 0 0) (P.Qpp 0 0) s).const_mul
      ((P.rr 0 0 : ℝ) : ℂ)).mul
      (dNum_hasDerivAt (P.rr 1 1) (P.Qp 1 1) (P.Qpp 1 1) P.sig1 s)).add
    (((polyF_hasDerivAt (P.Qp 0 1) (P.Qpp 0 1) s).mul
      (polyB_hasDerivAt (P.Qp 1 0) (P.Qpp 1 0) P.sig1 s)).const_mul
        ((P.rr 0 1 * P.rr 1 0 : ℝ) : ℂ))
  refine h.congr_deriv ?_
  unfold M0D
  ring

/-- `M1Num` differentiates to `M1D`. -/
theorem M1Num_hasDerivAt (P : MixParams) (s : ℂ) :
    HasDerivAt (M1Num P) (M1D P s) s := by
  have h := ((dNum_hasDerivAt (P.rr 0 0) (P.Qp 0 0) (P.Qpp 0 0) P.sig0 s).mul
      ((polyF_hasDerivAt (P.Qp 1 1) (P.Qpp 1 1) s).const_mul ((P.rr 1 1 : ℝ) : ℂ))).add
    (((polyB_hasDerivAt (P.Qp 0 1) (P.Qpp 0 1) P.sig0 s).mul
      (polyF_hasDerivAt (P.Qp 1 0) (P.Qpp 1 0) s)).const_mul
        ((P.rr 0 1 * P.rr 1 0 : ℝ) : ℂ))
  refine h.congr_deriv ?_
  unfold M1D
  ring

/-- `M01Num` differentiates to `M01D`. -/
theorem M01Num_hasDerivAt (P : MixParams) (s : ℂ) :
    HasDerivAt (M01Num P) (M01D P s) s := by
  have h := (((polyF_hasDerivAt (P.Qp 0 0) (P.Qpp 0 0) s).const_mul
      ((P.rr 0 0 : ℝ) : ℂ)).mul
      ((polyF_hasDerivAt (P.Qp 1 1) (P.Qpp 1 1) s).const_mul ((P.rr 1 1 : ℝ) : ℂ))).sub
    (((polyF_hasDerivAt (P.Qp 0 1) (P.Qpp 0 1) s).mul
      (polyF_hasDerivAt (P.Qp 1 0) (P.Qpp 1 0) s)).const_mul
        ((P.rr 0 1 * P.rr 1 0 : ℝ) : ℂ))
  refine h.congr_deriv ?_
  unfold M01D
  ring

/-- The decaying exponential factor differentiates with slope `-c`. -/
theorem cexp_neg_mul_hasDerivAt (c : ℝ) (s : ℂ) :
    HasDerivAt (fun s : ℂ => Complex.exp (-(s * (c : ℂ))))
      (-(c : ℂ) * Complex.exp (-(s * (c : ℂ)))) s := by
  have h1 : HasDerivAt (fun s : ℂ => -(s * (c : ℂ))) (-(1 * (c : ℂ))) s :=
    ((hasDerivAt_id s).mul_const (c : ℂ)).neg
  refine h1.cexp.congr_deriv ?_
  ring

/-- **`Wfun` differentiates to `WD`** (everywhere on `ℂ`). -/
theorem Wfun_hasDerivAt (P : MixParams) (s : ℂ) :
    HasDerivAt (Wfun P) (WD P s) s := by
  have h := (((McNum_hasDerivAt P s).add
      ((M0Num_hasDerivAt P s).mul (cexp_neg_mul_hasDerivAt P.sig0 s))).add
      ((M1Num_hasDerivAt P s).mul (cexp_neg_mul_hasDerivAt P.sig1 s))).add
      ((M01Num_hasDerivAt P s).mul (cexp_neg_mul_hasDerivAt (P.sig0 + P.sig1) s))
  refine h.congr_deriv ?_
  unfold WD
  ring

/-! ### The monomial bridge `s⁶·detC = Mc + M₀·E₀ + M₁·E₁ + M₀₁·E₀E₁` -/

set_option maxHeartbeats 1600000 in
/-- **Monomial bridge**: for `s ≠ 0` the `s⁶`-cleared determinant is the explicit
2-frequency exponential polynomial `Wfun`. Proved from `detC_lam_free` by clearing
denominators, treating the two exponentials as atoms. -/
theorem detC_monomial_eq (P : MixParams) {s : ℂ} (hs : s ≠ 0) :
    s ^ 6 * P.detF s = Wfun P s := by
  have hcb : ∀ qp qpp sg : ℝ,
      (qp : ℂ) * ((1 - s * (sg : ℂ) - Complex.exp (-(s * (sg : ℂ)))) / s ^ 2) +
        (qpp : ℂ) * ((1 - s * (sg : ℂ) + (s * (sg : ℂ)) ^ 2 / 2 -
          Complex.exp (-(s * (sg : ℂ)))) / s ^ 3) =
      (polyB qp qpp sg s - polyF qp qpp s * Complex.exp (-(s * (sg : ℂ)))) / s ^ 3 := by
    intro qp qpp sg
    unfold polyB polyF
    field_simp
    ring
  have h := detC_lam_free ![P.sig0, P.sig1] (fun i j => (P.rr i j : ℂ))
      (fun i j => (P.Qp i j : ℂ)) (fun i j => (P.Qpp i j : ℂ)) s
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
  simp only [hcb] at h
  have hE : Complex.exp (-(s * ((P.sig0 + P.sig1 : ℝ) : ℂ)))
      = Complex.exp (-(s * (P.sig0 : ℂ))) * Complex.exp (-(s * (P.sig1 : ℂ))) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  unfold MixParams.detF
  rw [h]
  unfold Wfun McNum M0Num M1Num M01Num dNum
  rw [hE]
  field_simp
  push_cast
  ring

/-! ### Elementary norm bounds for the building blocks -/

/-- Scalar-envelope constant for `polyB`: `‖polyB(s)‖ ≤ cB·M²` on `‖s‖ ≤ M`, `1 ≤ M`. -/
def cB (qp qpp sg : ℝ) : ℝ := qp * (1 + sg) + qpp * (1 + sg + sg ^ 2 / 2)

/-- Scalar-envelope constant for `polyBD`: `‖polyBD(s)‖ ≤ cBD·M`. -/
def cBD (qp qpp sg : ℝ) : ℝ := qp * (1 + 2 * sg) + qpp * (sg + sg ^ 2)

/-- Real nonnegative scalars pull out of complex norms. -/
theorem norm_real_mul {a : ℝ} (ha : 0 ≤ a) (z : ℂ) : ‖(a : ℂ) * z‖ = a * ‖z‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha]

/-- Envelope for `polyB` on the disk `‖s‖ ≤ M` (with `1 ≤ M`). -/
theorem polyB_norm_le {qp qpp sg : ℝ} (hqp : 0 ≤ qp) (hqpp : 0 ≤ qpp) (hsg : 0 ≤ sg)
    {M : ℝ} (hM : 1 ≤ M) {s : ℂ} (hs : ‖s‖ ≤ M) :
    ‖polyB qp qpp sg s‖ ≤ cB qp qpp sg * M ^ 2 := by
  have hM0 : (0 : ℝ) ≤ M := by linarith
  have hssg : ‖s * (sg : ℂ)‖ ≤ M * sg := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsg]
    exact mul_le_mul_of_nonneg_right hs hsg
  have h1 : ‖(qp : ℂ) * s * (1 - s * (sg : ℂ))‖ ≤ qp * (M * (1 + M * sg)) := by
    rw [mul_assoc, norm_real_mul hqp]
    have ha : ‖s * (1 - s * (sg : ℂ))‖ ≤ M * (1 + M * sg) := by
      rw [norm_mul]
      have hb : ‖1 - s * (sg : ℂ)‖ ≤ 1 + M * sg := by
        calc ‖1 - s * (sg : ℂ)‖ ≤ ‖(1 : ℂ)‖ + ‖s * (sg : ℂ)‖ := norm_sub_le _ _
          _ ≤ 1 + M * sg := by rw [norm_one]; linarith [hssg]
      exact mul_le_mul hs hb (norm_nonneg _) hM0
    exact mul_le_mul_of_nonneg_left ha hqp
  have h2 : ‖(qpp : ℂ) * (1 - s * (sg : ℂ) + (s * (sg : ℂ)) ^ 2 / 2)‖ ≤
      qpp * (1 + M * sg + (M * sg) ^ 2 / 2) := by
    rw [norm_real_mul hqpp]
    have ha : ‖1 - s * (sg : ℂ) + (s * (sg : ℂ)) ^ 2 / 2‖ ≤ 1 + M * sg + (M * sg) ^ 2 / 2 := by
      calc ‖1 - s * (sg : ℂ) + (s * (sg : ℂ)) ^ 2 / 2‖
          ≤ ‖1 - s * (sg : ℂ)‖ + ‖(s * (sg : ℂ)) ^ 2 / 2‖ := norm_add_le _ _
        _ ≤ 1 + M * sg + (M * sg) ^ 2 / 2 := by
            have hb : ‖1 - s * (sg : ℂ)‖ ≤ 1 + M * sg := by
              calc ‖1 - s * (sg : ℂ)‖ ≤ ‖(1 : ℂ)‖ + ‖s * (sg : ℂ)‖ := norm_sub_le _ _
                _ ≤ 1 + M * sg := by rw [norm_one]; linarith [hssg]
            have hc : ‖(s * (sg : ℂ)) ^ 2 / 2‖ ≤ (M * sg) ^ 2 / 2 := by
              rw [norm_div, norm_pow]
              have : ‖(2 : ℂ)‖ = 2 := by norm_num
              rw [this]
              have := pow_le_pow_left₀ (norm_nonneg _) hssg 2
              linarith
            linarith
    exact mul_le_mul_of_nonneg_left ha hqpp
  have htot := le_trans (norm_add_le _ _) (add_le_add h1 h2)
  have hM2 : M ≤ M ^ 2 := by nlinarith
  have h1M2 : (1 : ℝ) ≤ M ^ 2 := by nlinarith
  unfold polyB cB
  have e1 : qp * M ≤ qp * M ^ 2 := mul_le_mul_of_nonneg_left hM2 hqp
  have e2 : qpp * 1 ≤ qpp * M ^ 2 := mul_le_mul_of_nonneg_left h1M2 hqpp
  have e3 : qpp * sg * M ≤ qpp * sg * M ^ 2 :=
    mul_le_mul_of_nonneg_left hM2 (mul_nonneg hqpp hsg)
  nlinarith [htot]

/-- Envelope for `polyF` on the disk `‖s‖ ≤ M` (with `1 ≤ M`). -/
theorem polyF_norm_le {qp qpp : ℝ} (hqp : 0 ≤ qp) (hqpp : 0 ≤ qpp)
    {M : ℝ} (hM : 1 ≤ M) {s : ℂ} (hs : ‖s‖ ≤ M) :
    ‖polyF qp qpp s‖ ≤ (qp + qpp) * M := by
  have h1 : ‖(qp : ℂ) * s‖ ≤ qp * M := by
    rw [norm_real_mul hqp]; exact mul_le_mul_of_nonneg_left hs hqp
  have h2 : ‖((qpp : ℝ) : ℂ)‖ = qpp := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hqpp]
  have htot : ‖(qp : ℂ) * s + ((qpp : ℝ) : ℂ)‖ ≤ qp * M + qpp := by
    refine le_trans (norm_add_le _ _) ?_
    rw [h2]
    linarith [h1]
  unfold polyF
  nlinarith [htot, mul_le_mul_of_nonneg_left hM hqpp]

/-- Envelope for `polyBD` on the disk `‖s‖ ≤ M` (with `1 ≤ M`). -/
theorem polyBD_norm_le {qp qpp sg : ℝ} (hqp : 0 ≤ qp) (hqpp : 0 ≤ qpp) (hsg : 0 ≤ sg)
    {M : ℝ} (hM : 1 ≤ M) {s : ℂ} (hs : ‖s‖ ≤ M) :
    ‖polyBD qp qpp sg s‖ ≤ cBD qp qpp sg * M := by
  have hM0 : (0 : ℝ) ≤ M := by linarith
  have h1 : ‖(qp : ℂ) * (1 - 2 * s * (sg : ℂ))‖ ≤ qp * (1 + 2 * M * sg) := by
    rw [norm_real_mul hqp]
    refine mul_le_mul_of_nonneg_left ?_ hqp
    calc ‖1 - 2 * s * (sg : ℂ)‖ ≤ ‖(1 : ℂ)‖ + ‖2 * s * (sg : ℂ)‖ := norm_sub_le _ _
      _ ≤ 1 + 2 * M * sg := by
          rw [norm_one, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg hsg]
          have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
          rw [h2]
          nlinarith [norm_nonneg s, hs]
  have h2 : ‖(qpp : ℂ) * (-(sg : ℂ) + s * (sg : ℂ) ^ 2)‖ ≤ qpp * (sg + M * sg ^ 2) := by
    rw [norm_real_mul hqpp]
    refine mul_le_mul_of_nonneg_left ?_ hqpp
    calc ‖-(sg : ℂ) + s * (sg : ℂ) ^ 2‖ ≤ ‖-(sg : ℂ)‖ + ‖s * (sg : ℂ) ^ 2‖ := norm_add_le _ _
      _ ≤ sg + M * sg ^ 2 := by
          rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsg, norm_mul,
            norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsg]
          nlinarith [norm_nonneg s, hs, sq_nonneg sg]
  have htot := le_trans (norm_add_le _ _) (add_le_add h1 h2)
  unfold polyBD cBD
  have e1 : qp * 1 ≤ qp * M := mul_le_mul_of_nonneg_left hM hqp
  have e2 : qpp * sg * 1 ≤ qpp * sg * M := mul_le_mul_of_nonneg_left hM (mul_nonneg hqpp hsg)
  nlinarith [htot]

/-- Product norm bound from factor bounds. -/
theorem norm_mul_le_bound {a b : ℝ} {x y : ℂ} (hx : ‖x‖ ≤ a) (hy : ‖y‖ ≤ b) :
    ‖x * y‖ ≤ a * b := by
  rw [norm_mul]
  exact mul_le_mul hx hy (norm_nonneg _) (le_trans (norm_nonneg _) hx)

/-- Three-piece triangle inequality in the `a + b - c` shape. -/
theorem norm_add_add_sub_le (a b c : ℂ) : ‖a + b - c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
  calc ‖a + b - c‖ ≤ ‖a + b‖ + ‖c‖ := norm_sub_le _ _
    _ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by linarith [norm_add_le a b]

/-- `cB` is nonnegative for nonnegative data. -/
theorem cB_nonneg {qp qpp sg : ℝ} (hqp : 0 ≤ qp) (hqpp : 0 ≤ qpp) (hsg : 0 ≤ sg) :
    0 ≤ cB qp qpp sg := by
  unfold cB; positivity

/-- `cBD` is nonnegative for nonnegative data. -/
theorem cBD_nonneg {qp qpp sg : ℝ} (hqp : 0 ≤ qp) (hqpp : 0 ≤ qpp) (hsg : 0 ≤ sg) :
    0 ≤ cBD qp qpp sg := by
  unfold cBD; positivity

/-- Envelope for `dNum` on the disk `‖s‖ ≤ M` (with `1 ≤ M`). -/
theorem dNum_norm_le {rho qp qpp sg : ℝ} (hrho : 0 ≤ rho) (hqp : 0 ≤ qp) (hqpp : 0 ≤ qpp)
    (hsg : 0 ≤ sg) {M : ℝ} (hM : 1 ≤ M) {s : ℂ} (hs : ‖s‖ ≤ M) :
    ‖dNum rho qp qpp sg s‖ ≤ (1 + rho * cB qp qpp sg) * M ^ 3 := by
  have hM0 : (0 : ℝ) ≤ M := by linarith
  have h1 : ‖s ^ 3‖ ≤ M ^ 3 := by
    rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg s) hs 3
  have h2 : ‖(rho : ℂ) * polyB qp qpp sg s‖ ≤ rho * (cB qp qpp sg * M ^ 2) := by
    rw [norm_real_mul hrho]
    exact mul_le_mul_of_nonneg_left (polyB_norm_le hqp hqpp hsg hM hs) hrho
  have h23 : M ^ 2 ≤ M ^ 3 := pow_le_pow_right₀ hM (by norm_num)
  have hcB0 : 0 ≤ cB qp qpp sg := by unfold cB; positivity
  have htot := le_trans (norm_sub_le _ _) (add_le_add h1 h2)
  unfold dNum
  nlinarith [htot, mul_le_mul_of_nonneg_left h23 (mul_nonneg hrho hcB0)]

/-- Envelope for `dNumD` on the disk `‖s‖ ≤ M` (with `1 ≤ M`). -/
theorem dNumD_norm_le {rho qp qpp sg : ℝ} (hrho : 0 ≤ rho) (hqp : 0 ≤ qp) (hqpp : 0 ≤ qpp)
    (hsg : 0 ≤ sg) {M : ℝ} (hM : 1 ≤ M) {s : ℂ} (hs : ‖s‖ ≤ M) :
    ‖dNumD rho qp qpp sg s‖ ≤ (3 + rho * cBD qp qpp sg) * M ^ 2 := by
  have hM0 : (0 : ℝ) ≤ M := by linarith
  have h1 : ‖3 * s ^ 2‖ ≤ 3 * M ^ 2 := by
    rw [norm_mul, norm_pow]
    have h3 : ‖(3 : ℂ)‖ = 3 := by norm_num
    rw [h3]
    have := pow_le_pow_left₀ (norm_nonneg s) hs 2
    linarith
  have h2 : ‖(rho : ℂ) * polyBD qp qpp sg s‖ ≤ rho * (cBD qp qpp sg * M) := by
    rw [norm_real_mul hrho]
    exact mul_le_mul_of_nonneg_left (polyBD_norm_le hqp hqpp hsg hM hs) hrho
  have h12 : M ≤ M ^ 2 := by nlinarith
  have hcBD0 : 0 ≤ cBD qp qpp sg := by unfold cBD; positivity
  have htot := le_trans (norm_sub_le _ _) (add_le_add h1 h2)
  unfold dNumD
  nlinarith [htot, mul_le_mul_of_nonneg_left h12 (mul_nonneg hrho hcBD0)]

/-! ### Envelope constants for the four monomial coefficients -/

/-- Remainder constant: `‖McNum(s) − s⁶‖ ≤ KMc·M⁵`. -/
def MixParams.KMc (P : MixParams) : ℝ :=
  P.rr 0 0 * cB (P.Qp 0 0) (P.Qpp 0 0) P.sig0 *
      (1 + P.rr 1 1 * cB (P.Qp 1 1) (P.Qpp 1 1) P.sig1) +
    P.rr 1 1 * cB (P.Qp 1 1) (P.Qpp 1 1) P.sig1 +
    P.rr 0 1 * P.rr 1 0 * (cB (P.Qp 0 1) (P.Qpp 0 1) P.sig0 * cB (P.Qp 1 0) (P.Qpp 1 0) P.sig1)

/-- Remainder constant: `‖M1Num(s) − μ·s⁴‖ ≤ K1·M³`. -/
def MixParams.K1 (P : MixParams) : ℝ :=
  P.rr 1 1 * P.Qpp 1 1 +
    P.rr 0 0 * cB (P.Qp 0 0) (P.Qpp 0 0) P.sig0 * (P.rr 1 1 * (P.Qp 1 1 + P.Qpp 1 1)) +
    P.rr 0 1 * P.rr 1 0 *
      (cB (P.Qp 0 1) (P.Qpp 0 1) P.sig0 * (P.Qp 1 0 + P.Qpp 1 0))

/-- Envelope constant: `‖M0Num(s)‖ ≤ K0·M⁴`. -/
def MixParams.K0 (P : MixParams) : ℝ :=
  P.rr 0 0 * (P.Qp 0 0 + P.Qpp 0 0) * (1 + P.rr 1 1 * cB (P.Qp 1 1) (P.Qpp 1 1) P.sig1) +
    P.rr 0 1 * P.rr 1 0 * ((P.Qp 0 1 + P.Qpp 0 1) * cB (P.Qp 1 0) (P.Qpp 1 0) P.sig1)

/-- Envelope constant: `‖M01Num(s)‖ ≤ K01·M²`. -/
def MixParams.K01 (P : MixParams) : ℝ :=
  P.rr 0 0 * (P.Qp 0 0 + P.Qpp 0 0) * (P.rr 1 1 * (P.Qp 1 1 + P.Qpp 1 1)) +
    P.rr 0 1 * P.rr 1 0 * ((P.Qp 0 1 + P.Qpp 0 1) * (P.Qp 1 0 + P.Qpp 1 0))

/-- **`McNum` remainder envelope**: `‖McNum(s) − s⁶‖ ≤ KMc·M⁵` on `‖s‖ ≤ M`, `1 ≤ M`. -/
theorem McNum_sub_norm_le (P : MixParams) (hP : P.Phys) {M : ℝ} (hM : 1 ≤ M)
    {s : ℂ} (hs : ‖s‖ ≤ M) : ‖McNum P s - s ^ 6‖ ≤ P.KMc * M ^ 5 := by
  obtain ⟨hsg0, hsg01, hrr, hqp, hqpp⟩ := hP
  have hsg0' : 0 ≤ P.sig0 := hsg0.le
  have hsg1' : 0 ≤ P.sig1 := by linarith
  have hdec : McNum P s - s ^ 6 =
      -(((P.rr 0 0 : ℝ) : ℂ) * polyB (P.Qp 0 0) (P.Qpp 0 0) P.sig0 s) *
          dNum (P.rr 1 1) (P.Qp 1 1) (P.Qpp 1 1) P.sig1 s +
        s ^ 3 * -(((P.rr 1 1 : ℝ) : ℂ) * polyB (P.Qp 1 1) (P.Qpp 1 1) P.sig1 s) -
        ((P.rr 0 1 * P.rr 1 0 : ℝ) : ℂ) *
          (polyB (P.Qp 0 1) (P.Qpp 0 1) P.sig0 s * polyB (P.Qp 1 0) (P.Qpp 1 0) P.sig1 s) := by
    unfold McNum dNum
    ring
  have hp1 : ‖-(((P.rr 0 0 : ℝ) : ℂ) * polyB (P.Qp 0 0) (P.Qpp 0 0) P.sig0 s) *
      dNum (P.rr 1 1) (P.Qp 1 1) (P.Qpp 1 1) P.sig1 s‖ ≤
      (P.rr 0 0 * cB (P.Qp 0 0) (P.Qpp 0 0) P.sig0 *
        (1 + P.rr 1 1 * cB (P.Qp 1 1) (P.Qpp 1 1) P.sig1)) * M ^ 5 := by
    have h1 : ‖-(((P.rr 0 0 : ℝ) : ℂ) * polyB (P.Qp 0 0) (P.Qpp 0 0) P.sig0 s)‖ ≤
        P.rr 0 0 * (cB (P.Qp 0 0) (P.Qpp 0 0) P.sig0 * M ^ 2) := by
      rw [norm_neg, norm_real_mul (hrr 0 0).le]
      exact mul_le_mul_of_nonneg_left
        (polyB_norm_le (hqp 0 0).le (hqpp 0 0).le hsg0' hM hs) (hrr 0 0).le
    have h2 := dNum_norm_le (hrr 1 1).le (hqp 1 1).le (hqpp 1 1).le hsg1' hM hs
    calc ‖-(((P.rr 0 0 : ℝ) : ℂ) * polyB (P.Qp 0 0) (P.Qpp 0 0) P.sig0 s) *
        dNum (P.rr 1 1) (P.Qp 1 1) (P.Qpp 1 1) P.sig1 s‖
        ≤ (P.rr 0 0 * (cB (P.Qp 0 0) (P.Qpp 0 0) P.sig0 * M ^ 2)) *
          ((1 + P.rr 1 1 * cB (P.Qp 1 1) (P.Qpp 1 1) P.sig1) * M ^ 3) :=
          norm_mul_le_bound h1 h2
      _ = (P.rr 0 0 * cB (P.Qp 0 0) (P.Qpp 0 0) P.sig0 *
          (1 + P.rr 1 1 * cB (P.Qp 1 1) (P.Qpp 1 1) P.sig1)) * M ^ 5 := by ring
  have hp2 : ‖s ^ 3 * -(((P.rr 1 1 : ℝ) : ℂ) * polyB (P.Qp 1 1) (P.Qpp 1 1) P.sig1 s)‖ ≤
      (P.rr 1 1 * cB (P.Qp 1 1) (P.Qpp 1 1) P.sig1) * M ^ 5 := by
    have h1 : ‖s ^ 3‖ ≤ M ^ 3 := by
      rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg s) hs 3
    have h2 : ‖-(((P.rr 1 1 : ℝ) : ℂ) * polyB (P.Qp 1 1) (P.Qpp 1 1) P.sig1 s)‖ ≤
        P.rr 1 1 * (cB (P.Qp 1 1) (P.Qpp 1 1) P.sig1 * M ^ 2) := by
      rw [norm_neg, norm_real_mul (hrr 1 1).le]
      exact mul_le_mul_of_nonneg_left
        (polyB_norm_le (hqp 1 1).le (hqpp 1 1).le hsg1' hM hs) (hrr 1 1).le
    calc ‖s ^ 3 * -(((P.rr 1 1 : ℝ) : ℂ) * polyB (P.Qp 1 1) (P.Qpp 1 1) P.sig1 s)‖
        ≤ M ^ 3 * (P.rr 1 1 * (cB (P.Qp 1 1) (P.Qpp 1 1) P.sig1 * M ^ 2)) :=
          norm_mul_le_bound h1 h2
      _ = (P.rr 1 1 * cB (P.Qp 1 1) (P.Qpp 1 1) P.sig1) * M ^ 5 := by ring
  have hp3 : ‖((P.rr 0 1 * P.rr 1 0 : ℝ) : ℂ) *
      (polyB (P.Qp 0 1) (P.Qpp 0 1) P.sig0 s * polyB (P.Qp 1 0) (P.Qpp 1 0) P.sig1 s)‖ ≤
      (P.rr 0 1 * P.rr 1 0 *
        (cB (P.Qp 0 1) (P.Qpp 0 1) P.sig0 * cB (P.Qp 1 0) (P.Qpp 1 0) P.sig1)) * M ^ 5 := by
    have hc : 0 ≤ P.rr 0 1 * P.rr 1 0 := mul_nonneg (hrr 0 1).le (hrr 1 0).le
    have h1 := polyB_norm_le (hqp 0 1).le (hqpp 0 1).le hsg0' hM hs
    have h2 := polyB_norm_le (hqp 1 0).le (hqpp 1 0).le hsg1' hM hs
    have h45 : M ^ 4 ≤ M ^ 5 := pow_le_pow_right₀ hM (by norm_num)
    have hcB1 : 0 ≤ cB (P.Qp 0 1) (P.Qpp 0 1) P.sig0 :=
      cB_nonneg (hqp 0 1).le (hqpp 0 1).le hsg0'
    have hcB2 : 0 ≤ cB (P.Qp 1 0) (P.Qpp 1 0) P.sig1 :=
      cB_nonneg (hqp 1 0).le (hqpp 1 0).le hsg1'
    have h3 : ‖polyB (P.Qp 0 1) (P.Qpp 0 1) P.sig0 s * polyB (P.Qp 1 0) (P.Qpp 1 0) P.sig1 s‖ ≤
        cB (P.Qp 0 1) (P.Qpp 0 1) P.sig0 * cB (P.Qp 1 0) (P.Qpp 1 0) P.sig1 * M ^ 4 := by
      calc ‖polyB (P.Qp 0 1) (P.Qpp 0 1) P.sig0 s * polyB (P.Qp 1 0) (P.Qpp 1 0) P.sig1 s‖
          ≤ (cB (P.Qp 0 1) (P.Qpp 0 1) P.sig0 * M ^ 2) *
            (cB (P.Qp 1 0) (P.Qpp 1 0) P.sig1 * M ^ 2) := norm_mul_le_bound h1 h2
        _ = cB (P.Qp 0 1) (P.Qpp 0 1) P.sig0 * cB (P.Qp 1 0) (P.Qpp 1 0) P.sig1 * M ^ 4 := by
            ring
    rw [norm_real_mul hc]
    calc P.rr 0 1 * P.rr 1 0 *
        ‖polyB (P.Qp 0 1) (P.Qpp 0 1) P.sig0 s * polyB (P.Qp 1 0) (P.Qpp 1 0) P.sig1 s‖
        ≤ P.rr 0 1 * P.rr 1 0 *
          (cB (P.Qp 0 1) (P.Qpp 0 1) P.sig0 * cB (P.Qp 1 0) (P.Qpp 1 0) P.sig1 * M ^ 4) :=
          mul_le_mul_of_nonneg_left h3 hc
      _ ≤ P.rr 0 1 * P.rr 1 0 *
          (cB (P.Qp 0 1) (P.Qpp 0 1) P.sig0 * cB (P.Qp 1 0) (P.Qpp 1 0) P.sig1) * M ^ 5 := by
          nlinarith [mul_le_mul_of_nonneg_left h45
            (mul_nonneg hc (mul_nonneg hcB1 hcB2))]
  rw [hdec]
  refine le_trans (norm_add_add_sub_le _ _ _) ?_
  unfold MixParams.KMc
  linarith [hp1, hp2, hp3]

/-- `K1` is nonnegative for physical parameters. -/
theorem K1_nonneg (P : MixParams) (hP : P.Phys) : 0 ≤ P.K1 := by
  obtain ⟨hsg0, hsg01, hrr, hqp, hqpp⟩ := hP
  have hsg0' : 0 ≤ P.sig0 := hsg0.le
  have hcB := cB_nonneg (hqp 0 0).le (hqpp 0 0).le hsg0'
  have hcB' := cB_nonneg (hqp 0 1).le (hqpp 0 1).le hsg0'
  have h1 := (hrr 1 1).le; have h2 := (hqpp 1 1).le; have h3 := (hrr 0 0).le
  have h4 := (hqp 1 1).le; have h5 := (hrr 0 1).le; have h6 := (hrr 1 0).le
  have h7 := (hqp 1 0).le; have h8 := (hqpp 1 0).le
  unfold MixParams.K1
  positivity

/-- **`M1Num` remainder envelope**: `‖M1Num(s) − μ·s⁴‖ ≤ K1·M³` on `‖s‖ ≤ M`, `1 ≤ M`. -/
theorem M1Num_sub_norm_le (P : MixParams) (hP : P.Phys) {M : ℝ} (hM : 1 ≤ M)
    {s : ℂ} (hs : ‖s‖ ≤ M) : ‖M1Num P s - ((P.mu : ℝ) : ℂ) * s ^ 4‖ ≤ P.K1 * M ^ 3 := by
  obtain ⟨hsg0, hsg01, hrr, hqp, hqpp⟩ := hP
  have hsg0' : 0 ≤ P.sig0 := hsg0.le
  have hsg1' : 0 ≤ P.sig1 := by linarith
  have hdec : M1Num P s - ((P.mu : ℝ) : ℂ) * s ^ 4 =
      s ^ 3 * ((P.rr 1 1 * P.Qpp 1 1 : ℝ) : ℂ) +
        -(((P.rr 0 0 : ℝ) : ℂ) * polyB (P.Qp 0 0) (P.Qpp 0 0) P.sig0 s) *
          (((P.rr 1 1 : ℝ) : ℂ) * polyF (P.Qp 1 1) (P.Qpp 1 1) s) +
        ((P.rr 0 1 * P.rr 1 0 : ℝ) : ℂ) *
          (polyB (P.Qp 0 1) (P.Qpp 0 1) P.sig0 s * polyF (P.Qp 1 0) (P.Qpp 1 0) s) := by
    unfold M1Num dNum polyF MixParams.mu
    push_cast
    ring
  have hp1 : ‖s ^ 3 * ((P.rr 1 1 * P.Qpp 1 1 : ℝ) : ℂ)‖ ≤ P.rr 1 1 * P.Qpp 1 1 * M ^ 3 := by
    have h1 : ‖s ^ 3‖ ≤ M ^ 3 := by
      rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg s) hs 3
    have h2 : ‖((P.rr 1 1 * P.Qpp 1 1 : ℝ) : ℂ)‖ = P.rr 1 1 * P.Qpp 1 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (hrr 1 1).le (hqpp 1 1).le)]
    calc ‖s ^ 3 * ((P.rr 1 1 * P.Qpp 1 1 : ℝ) : ℂ)‖
        ≤ M ^ 3 * (P.rr 1 1 * P.Qpp 1 1) := norm_mul_le_bound h1 (le_of_eq h2)
      _ = P.rr 1 1 * P.Qpp 1 1 * M ^ 3 := by ring
  have hp2 : ‖-(((P.rr 0 0 : ℝ) : ℂ) * polyB (P.Qp 0 0) (P.Qpp 0 0) P.sig0 s) *
      (((P.rr 1 1 : ℝ) : ℂ) * polyF (P.Qp 1 1) (P.Qpp 1 1) s)‖ ≤
      P.rr 0 0 * cB (P.Qp 0 0) (P.Qpp 0 0) P.sig0 * (P.rr 1 1 * (P.Qp 1 1 + P.Qpp 1 1)) *
        M ^ 3 := by
    have h1 : ‖-(((P.rr 0 0 : ℝ) : ℂ) * polyB (P.Qp 0 0) (P.Qpp 0 0) P.sig0 s)‖ ≤
        P.rr 0 0 * (cB (P.Qp 0 0) (P.Qpp 0 0) P.sig0 * M ^ 2) := by
      rw [norm_neg, norm_real_mul (hrr 0 0).le]
      exact mul_le_mul_of_nonneg_left
        (polyB_norm_le (hqp 0 0).le (hqpp 0 0).le hsg0' hM hs) (hrr 0 0).le
    have h2 : ‖((P.rr 1 1 : ℝ) : ℂ) * polyF (P.Qp 1 1) (P.Qpp 1 1) s‖ ≤
        P.rr 1 1 * ((P.Qp 1 1 + P.Qpp 1 1) * M) := by
      rw [norm_real_mul (hrr 1 1).le]
      exact mul_le_mul_of_nonneg_left
        (polyF_norm_le (hqp 1 1).le (hqpp 1 1).le hM hs) (hrr 1 1).le
    calc ‖-(((P.rr 0 0 : ℝ) : ℂ) * polyB (P.Qp 0 0) (P.Qpp 0 0) P.sig0 s) *
        (((P.rr 1 1 : ℝ) : ℂ) * polyF (P.Qp 1 1) (P.Qpp 1 1) s)‖
        ≤ (P.rr 0 0 * (cB (P.Qp 0 0) (P.Qpp 0 0) P.sig0 * M ^ 2)) *
          (P.rr 1 1 * ((P.Qp 1 1 + P.Qpp 1 1) * M)) := norm_mul_le_bound h1 h2
      _ = P.rr 0 0 * cB (P.Qp 0 0) (P.Qpp 0 0) P.sig0 *
          (P.rr 1 1 * (P.Qp 1 1 + P.Qpp 1 1)) * M ^ 3 := by ring
  have hp3 : ‖((P.rr 0 1 * P.rr 1 0 : ℝ) : ℂ) *
      (polyB (P.Qp 0 1) (P.Qpp 0 1) P.sig0 s * polyF (P.Qp 1 0) (P.Qpp 1 0) s)‖ ≤
      P.rr 0 1 * P.rr 1 0 *
        (cB (P.Qp 0 1) (P.Qpp 0 1) P.sig0 * (P.Qp 1 0 + P.Qpp 1 0)) * M ^ 3 := by
    have hc : 0 ≤ P.rr 0 1 * P.rr 1 0 := mul_nonneg (hrr 0 1).le (hrr 1 0).le
    have h1 := polyB_norm_le (hqp 0 1).le (hqpp 0 1).le hsg0' hM hs
    have h2 := polyF_norm_le (hqp 1 0).le (hqpp 1 0).le hM hs
    rw [norm_real_mul hc]
    calc P.rr 0 1 * P.rr 1 0 *
        ‖polyB (P.Qp 0 1) (P.Qpp 0 1) P.sig0 s * polyF (P.Qp 1 0) (P.Qpp 1 0) s‖
        ≤ P.rr 0 1 * P.rr 1 0 * ((cB (P.Qp 0 1) (P.Qpp 0 1) P.sig0 * M ^ 2) *
          ((P.Qp 1 0 + P.Qpp 1 0) * M)) :=
          mul_le_mul_of_nonneg_left (norm_mul_le_bound h1 h2) hc
      _ = P.rr 0 1 * P.rr 1 0 *
          (cB (P.Qp 0 1) (P.Qpp 0 1) P.sig0 * (P.Qp 1 0 + P.Qpp 1 0)) * M ^ 3 := by ring
  rw [hdec]
  refine le_trans (norm_add₃_le) ?_
  unfold MixParams.K1
  linarith [hp1, hp2, hp3]

/-- `M1Num` upper envelope: `‖M1Num(s)‖ ≤ (μ + K1)·M⁴`. -/
theorem M1Num_norm_le (P : MixParams) (hP : P.Phys) {M : ℝ} (hM : 1 ≤ M)
    {s : ℂ} (hs : ‖s‖ ≤ M) : ‖M1Num P s‖ ≤ (P.mu + P.K1) * M ^ 4 := by
  have hsub := M1Num_sub_norm_le P hP hM hs
  have hmu0 : 0 ≤ P.mu := by
    obtain ⟨_, _, hrr, hqp, _⟩ := hP
    exact mul_nonneg (hrr 1 1).le (hqp 1 1).le
  have hK10 := K1_nonneg P hP
  have h34 : M ^ 3 ≤ M ^ 4 := pow_le_pow_right₀ hM (by norm_num)
  have hlead : ‖((P.mu : ℝ) : ℂ) * s ^ 4‖ ≤ P.mu * M ^ 4 := by
    rw [norm_real_mul hmu0, norm_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg s) hs 4) hmu0
  have hsplit : M1Num P s = (M1Num P s - ((P.mu : ℝ) : ℂ) * s ^ 4) +
      ((P.mu : ℝ) : ℂ) * s ^ 4 := by ring
  calc ‖M1Num P s‖ = ‖(M1Num P s - ((P.mu : ℝ) : ℂ) * s ^ 4) +
      ((P.mu : ℝ) : ℂ) * s ^ 4‖ := by rw [← hsplit]
    _ ≤ ‖M1Num P s - ((P.mu : ℝ) : ℂ) * s ^ 4‖ + ‖((P.mu : ℝ) : ℂ) * s ^ 4‖ :=
        norm_add_le _ _
    _ ≤ (P.mu + P.K1) * M ^ 4 := by nlinarith [mul_le_mul_of_nonneg_left h34 hK10]

/-- **`M0Num` envelope**: `‖M0Num(s)‖ ≤ K0·M⁴` on `‖s‖ ≤ M`, `1 ≤ M`. -/
theorem M0Num_norm_le (P : MixParams) (hP : P.Phys) {M : ℝ} (hM : 1 ≤ M)
    {s : ℂ} (hs : ‖s‖ ≤ M) : ‖M0Num P s‖ ≤ P.K0 * M ^ 4 := by
  obtain ⟨hsg0, hsg01, hrr, hqp, hqpp⟩ := hP
  have hsg1' : 0 ≤ P.sig1 := by linarith [hsg0.le]
  have hp1 : ‖((P.rr 0 0 : ℝ) : ℂ) * polyF (P.Qp 0 0) (P.Qpp 0 0) s *
      dNum (P.rr 1 1) (P.Qp 1 1) (P.Qpp 1 1) P.sig1 s‖ ≤
      P.rr 0 0 * (P.Qp 0 0 + P.Qpp 0 0) *
        (1 + P.rr 1 1 * cB (P.Qp 1 1) (P.Qpp 1 1) P.sig1) * M ^ 4 := by
    have h1 : ‖((P.rr 0 0 : ℝ) : ℂ) * polyF (P.Qp 0 0) (P.Qpp 0 0) s‖ ≤
        P.rr 0 0 * ((P.Qp 0 0 + P.Qpp 0 0) * M) := by
      rw [norm_real_mul (hrr 0 0).le]
      exact mul_le_mul_of_nonneg_left
        (polyF_norm_le (hqp 0 0).le (hqpp 0 0).le hM hs) (hrr 0 0).le
    have h2 := dNum_norm_le (hrr 1 1).le (hqp 1 1).le (hqpp 1 1).le hsg1' hM hs
    calc ‖((P.rr 0 0 : ℝ) : ℂ) * polyF (P.Qp 0 0) (P.Qpp 0 0) s *
        dNum (P.rr 1 1) (P.Qp 1 1) (P.Qpp 1 1) P.sig1 s‖
        ≤ (P.rr 0 0 * ((P.Qp 0 0 + P.Qpp 0 0) * M)) *
          ((1 + P.rr 1 1 * cB (P.Qp 1 1) (P.Qpp 1 1) P.sig1) * M ^ 3) :=
          norm_mul_le_bound h1 h2
      _ = P.rr 0 0 * (P.Qp 0 0 + P.Qpp 0 0) *
          (1 + P.rr 1 1 * cB (P.Qp 1 1) (P.Qpp 1 1) P.sig1) * M ^ 4 := by ring
  have hp2 : ‖((P.rr 0 1 * P.rr 1 0 : ℝ) : ℂ) *
      (polyF (P.Qp 0 1) (P.Qpp 0 1) s * polyB (P.Qp 1 0) (P.Qpp 1 0) P.sig1 s)‖ ≤
      P.rr 0 1 * P.rr 1 0 * ((P.Qp 0 1 + P.Qpp 0 1) * cB (P.Qp 1 0) (P.Qpp 1 0) P.sig1) *
        M ^ 4 := by
    have hc : 0 ≤ P.rr 0 1 * P.rr 1 0 := mul_nonneg (hrr 0 1).le (hrr 1 0).le
    have h1 := polyF_norm_le (hqp 0 1).le (hqpp 0 1).le hM hs
    have h2 := polyB_norm_le (hqp 1 0).le (hqpp 1 0).le hsg1' hM hs
    have h34 : M ^ 3 ≤ M ^ 4 := pow_le_pow_right₀ hM (by norm_num)
    have hc2 : 0 ≤ P.rr 0 1 * P.rr 1 0 * ((P.Qp 0 1 + P.Qpp 0 1) *
        cB (P.Qp 1 0) (P.Qpp 1 0) P.sig1) := by
      have := cB_nonneg (hqp 1 0).le (hqpp 1 0).le hsg1'
      have h3 := (hqp 0 1).le; have h4 := (hqpp 0 1).le
      positivity
    rw [norm_real_mul hc]
    calc P.rr 0 1 * P.rr 1 0 *
        ‖polyF (P.Qp 0 1) (P.Qpp 0 1) s * polyB (P.Qp 1 0) (P.Qpp 1 0) P.sig1 s‖
        ≤ P.rr 0 1 * P.rr 1 0 * (((P.Qp 0 1 + P.Qpp 0 1) * M) *
          (cB (P.Qp 1 0) (P.Qpp 1 0) P.sig1 * M ^ 2)) :=
          mul_le_mul_of_nonneg_left (norm_mul_le_bound h1 h2) hc
      _ = P.rr 0 1 * P.rr 1 0 * ((P.Qp 0 1 + P.Qpp 0 1) *
          cB (P.Qp 1 0) (P.Qpp 1 0) P.sig1) * M ^ 3 := by ring
      _ ≤ P.rr 0 1 * P.rr 1 0 * ((P.Qp 0 1 + P.Qpp 0 1) *
          cB (P.Qp 1 0) (P.Qpp 1 0) P.sig1) * M ^ 4 :=
          mul_le_mul_of_nonneg_left h34 hc2
  unfold M0Num MixParams.K0
  refine le_trans (norm_add_le _ _) ?_
  linarith [hp1, hp2]

/-- **`M01Num` envelope**: `‖M01Num(s)‖ ≤ K01·M²` on `‖s‖ ≤ M`, `1 ≤ M`. -/
theorem M01Num_norm_le (P : MixParams) (hP : P.Phys) {M : ℝ} (hM : 1 ≤ M)
    {s : ℂ} (hs : ‖s‖ ≤ M) : ‖M01Num P s‖ ≤ P.K01 * M ^ 2 := by
  obtain ⟨hsg0, hsg01, hrr, hqp, hqpp⟩ := hP
  have hp1 : ‖((P.rr 0 0 : ℝ) : ℂ) * polyF (P.Qp 0 0) (P.Qpp 0 0) s *
      (((P.rr 1 1 : ℝ) : ℂ) * polyF (P.Qp 1 1) (P.Qpp 1 1) s)‖ ≤
      P.rr 0 0 * (P.Qp 0 0 + P.Qpp 0 0) * (P.rr 1 1 * (P.Qp 1 1 + P.Qpp 1 1)) * M ^ 2 := by
    have h1 : ‖((P.rr 0 0 : ℝ) : ℂ) * polyF (P.Qp 0 0) (P.Qpp 0 0) s‖ ≤
        P.rr 0 0 * ((P.Qp 0 0 + P.Qpp 0 0) * M) := by
      rw [norm_real_mul (hrr 0 0).le]
      exact mul_le_mul_of_nonneg_left
        (polyF_norm_le (hqp 0 0).le (hqpp 0 0).le hM hs) (hrr 0 0).le
    have h2 : ‖((P.rr 1 1 : ℝ) : ℂ) * polyF (P.Qp 1 1) (P.Qpp 1 1) s‖ ≤
        P.rr 1 1 * ((P.Qp 1 1 + P.Qpp 1 1) * M) := by
      rw [norm_real_mul (hrr 1 1).le]
      exact mul_le_mul_of_nonneg_left
        (polyF_norm_le (hqp 1 1).le (hqpp 1 1).le hM hs) (hrr 1 1).le
    calc ‖((P.rr 0 0 : ℝ) : ℂ) * polyF (P.Qp 0 0) (P.Qpp 0 0) s *
        (((P.rr 1 1 : ℝ) : ℂ) * polyF (P.Qp 1 1) (P.Qpp 1 1) s)‖
        ≤ (P.rr 0 0 * ((P.Qp 0 0 + P.Qpp 0 0) * M)) *
          (P.rr 1 1 * ((P.Qp 1 1 + P.Qpp 1 1) * M)) := norm_mul_le_bound h1 h2
      _ = P.rr 0 0 * (P.Qp 0 0 + P.Qpp 0 0) *
          (P.rr 1 1 * (P.Qp 1 1 + P.Qpp 1 1)) * M ^ 2 := by ring
  have hp2 : ‖((P.rr 0 1 * P.rr 1 0 : ℝ) : ℂ) *
      (polyF (P.Qp 0 1) (P.Qpp 0 1) s * polyF (P.Qp 1 0) (P.Qpp 1 0) s)‖ ≤
      P.rr 0 1 * P.rr 1 0 * ((P.Qp 0 1 + P.Qpp 0 1) * (P.Qp 1 0 + P.Qpp 1 0)) * M ^ 2 := by
    have hc : 0 ≤ P.rr 0 1 * P.rr 1 0 := mul_nonneg (hrr 0 1).le (hrr 1 0).le
    have h1 := polyF_norm_le (hqp 0 1).le (hqpp 0 1).le hM hs
    have h2 := polyF_norm_le (hqp 1 0).le (hqpp 1 0).le hM hs
    rw [norm_real_mul hc]
    calc P.rr 0 1 * P.rr 1 0 *
        ‖polyF (P.Qp 0 1) (P.Qpp 0 1) s * polyF (P.Qp 1 0) (P.Qpp 1 0) s‖
        ≤ P.rr 0 1 * P.rr 1 0 * (((P.Qp 0 1 + P.Qpp 0 1) * M) *
          ((P.Qp 1 0 + P.Qpp 1 0) * M)) :=
          mul_le_mul_of_nonneg_left (norm_mul_le_bound h1 h2) hc
      _ = P.rr 0 1 * P.rr 1 0 *
          ((P.Qp 0 1 + P.Qpp 0 1) * (P.Qp 1 0 + P.Qpp 1 0)) * M ^ 2 := by ring
  unfold M01Num MixParams.K01
  refine le_trans (norm_sub_le _ _) ?_
  linarith [hp1, hp2]

/-! ### Envelopes for the derivative polynomials -/

/-- Envelope constant: `‖McD(s)‖ ≤ KMcD·M⁵`. -/
def MixParams.KMcD (P : MixParams) : ℝ :=
  (3 + P.rr 0 0 * cBD (P.Qp 0 0) (P.Qpp 0 0) P.sig0) *
      (1 + P.rr 1 1 * cB (P.Qp 1 1) (P.Qpp 1 1) P.sig1) +
    (1 + P.rr 0 0 * cB (P.Qp 0 0) (P.Qpp 0 0) P.sig0) *
      (3 + P.rr 1 1 * cBD (P.Qp 1 1) (P.Qpp 1 1) P.sig1) +
    P.rr 0 1 * P.rr 1 0 *
      (cBD (P.Qp 0 1) (P.Qpp 0 1) P.sig0 * cB (P.Qp 1 0) (P.Qpp 1 0) P.sig1 +
        cB (P.Qp 0 1) (P.Qpp 0 1) P.sig0 * cBD (P.Qp 1 0) (P.Qpp 1 0) P.sig1)

/-- Envelope constant: `‖M1D(s)‖ ≤ K1D·M³`. -/
def MixParams.K1D (P : MixParams) : ℝ :=
  (3 + P.rr 0 0 * cBD (P.Qp 0 0) (P.Qpp 0 0) P.sig0) * (P.rr 1 1 * (P.Qp 1 1 + P.Qpp 1 1)) +
    (1 + P.rr 0 0 * cB (P.Qp 0 0) (P.Qpp 0 0) P.sig0) * (P.rr 1 1 * P.Qp 1 1) +
    P.rr 0 1 * P.rr 1 0 *
      (cBD (P.Qp 0 1) (P.Qpp 0 1) P.sig0 * (P.Qp 1 0 + P.Qpp 1 0) +
        cB (P.Qp 0 1) (P.Qpp 0 1) P.sig0 * P.Qp 1 0)

/-- **`McD` envelope**: `‖McD(s)‖ ≤ KMcD·M⁵` on `‖s‖ ≤ M`, `1 ≤ M`. -/
theorem McD_norm_le (P : MixParams) (hP : P.Phys) {M : ℝ} (hM : 1 ≤ M)
    {s : ℂ} (hs : ‖s‖ ≤ M) : ‖McD P s‖ ≤ P.KMcD * M ^ 5 := by
  obtain ⟨hsg0, hsg01, hrr, hqp, hqpp⟩ := hP
  have hsg0' : 0 ≤ P.sig0 := hsg0.le
  have hsg1' : 0 ≤ P.sig1 := by linarith
  have hp1 : ‖dNumD (P.rr 0 0) (P.Qp 0 0) (P.Qpp 0 0) P.sig0 s *
      dNum (P.rr 1 1) (P.Qp 1 1) (P.Qpp 1 1) P.sig1 s‖ ≤
      (3 + P.rr 0 0 * cBD (P.Qp 0 0) (P.Qpp 0 0) P.sig0) *
        (1 + P.rr 1 1 * cB (P.Qp 1 1) (P.Qpp 1 1) P.sig1) * M ^ 5 := by
    have h1 := dNumD_norm_le (hrr 0 0).le (hqp 0 0).le (hqpp 0 0).le hsg0' hM hs
    have h2 := dNum_norm_le (hrr 1 1).le (hqp 1 1).le (hqpp 1 1).le hsg1' hM hs
    calc ‖dNumD (P.rr 0 0) (P.Qp 0 0) (P.Qpp 0 0) P.sig0 s *
        dNum (P.rr 1 1) (P.Qp 1 1) (P.Qpp 1 1) P.sig1 s‖
        ≤ ((3 + P.rr 0 0 * cBD (P.Qp 0 0) (P.Qpp 0 0) P.sig0) * M ^ 2) *
          ((1 + P.rr 1 1 * cB (P.Qp 1 1) (P.Qpp 1 1) P.sig1) * M ^ 3) :=
          norm_mul_le_bound h1 h2
      _ = (3 + P.rr 0 0 * cBD (P.Qp 0 0) (P.Qpp 0 0) P.sig0) *
          (1 + P.rr 1 1 * cB (P.Qp 1 1) (P.Qpp 1 1) P.sig1) * M ^ 5 := by ring
  have hp2 : ‖dNum (P.rr 0 0) (P.Qp 0 0) (P.Qpp 0 0) P.sig0 s *
      dNumD (P.rr 1 1) (P.Qp 1 1) (P.Qpp 1 1) P.sig1 s‖ ≤
      (1 + P.rr 0 0 * cB (P.Qp 0 0) (P.Qpp 0 0) P.sig0) *
        (3 + P.rr 1 1 * cBD (P.Qp 1 1) (P.Qpp 1 1) P.sig1) * M ^ 5 := by
    have h1 := dNum_norm_le (hrr 0 0).le (hqp 0 0).le (hqpp 0 0).le hsg0' hM hs
    have h2 := dNumD_norm_le (hrr 1 1).le (hqp 1 1).le (hqpp 1 1).le hsg1' hM hs
    calc ‖dNum (P.rr 0 0) (P.Qp 0 0) (P.Qpp 0 0) P.sig0 s *
        dNumD (P.rr 1 1) (P.Qp 1 1) (P.Qpp 1 1) P.sig1 s‖
        ≤ ((1 + P.rr 0 0 * cB (P.Qp 0 0) (P.Qpp 0 0) P.sig0) * M ^ 3) *
          ((3 + P.rr 1 1 * cBD (P.Qp 1 1) (P.Qpp 1 1) P.sig1) * M ^ 2) :=
          norm_mul_le_bound h1 h2
      _ = (1 + P.rr 0 0 * cB (P.Qp 0 0) (P.Qpp 0 0) P.sig0) *
          (3 + P.rr 1 1 * cBD (P.Qp 1 1) (P.Qpp 1 1) P.sig1) * M ^ 5 := by ring
  have hp3 : ‖((P.rr 0 1 * P.rr 1 0 : ℝ) : ℂ) *
      (polyBD (P.Qp 0 1) (P.Qpp 0 1) P.sig0 s * polyB (P.Qp 1 0) (P.Qpp 1 0) P.sig1 s +
        polyB (P.Qp 0 1) (P.Qpp 0 1) P.sig0 s * polyBD (P.Qp 1 0) (P.Qpp 1 0) P.sig1 s)‖ ≤
      P.rr 0 1 * P.rr 1 0 *
        (cBD (P.Qp 0 1) (P.Qpp 0 1) P.sig0 * cB (P.Qp 1 0) (P.Qpp 1 0) P.sig1 +
          cB (P.Qp 0 1) (P.Qpp 0 1) P.sig0 * cBD (P.Qp 1 0) (P.Qpp 1 0) P.sig1) * M ^ 5 := by
    have hc : 0 ≤ P.rr 0 1 * P.rr 1 0 := mul_nonneg (hrr 0 1).le (hrr 1 0).le
    have h1 := norm_mul_le_bound (polyBD_norm_le (hqp 0 1).le (hqpp 0 1).le hsg0' hM hs)
      (polyB_norm_le (hqp 1 0).le (hqpp 1 0).le hsg1' hM hs)
    have h2 := norm_mul_le_bound (polyB_norm_le (hqp 0 1).le (hqpp 0 1).le hsg0' hM hs)
      (polyBD_norm_le (hqp 1 0).le (hqpp 1 0).le hsg1' hM hs)
    have h35 : M ^ 3 ≤ M ^ 5 := pow_le_pow_right₀ hM (by norm_num)
    have hd1 := cBD_nonneg (hqp 0 1).le (hqpp 0 1).le hsg0'
    have hd2 := cB_nonneg (hqp 1 0).le (hqpp 1 0).le hsg1'
    have hd3 := cB_nonneg (hqp 0 1).le (hqpp 0 1).le hsg0'
    have hd4 := cBD_nonneg (hqp 1 0).le (hqpp 1 0).le hsg1'
    rw [norm_real_mul hc]
    have hsum : ‖polyBD (P.Qp 0 1) (P.Qpp 0 1) P.sig0 s * polyB (P.Qp 1 0) (P.Qpp 1 0) P.sig1 s +
        polyB (P.Qp 0 1) (P.Qpp 0 1) P.sig0 s * polyBD (P.Qp 1 0) (P.Qpp 1 0) P.sig1 s‖ ≤
        (cBD (P.Qp 0 1) (P.Qpp 0 1) P.sig0 * cB (P.Qp 1 0) (P.Qpp 1 0) P.sig1 +
          cB (P.Qp 0 1) (P.Qpp 0 1) P.sig0 * cBD (P.Qp 1 0) (P.Qpp 1 0) P.sig1) * M ^ 3 := by
      refine le_trans (norm_add_le _ _) ?_
      nlinarith [h1, h2]
    have := mul_le_mul_of_nonneg_left hsum hc
    nlinarith [this, mul_le_mul_of_nonneg_left h35 (mul_nonneg hc
      (add_nonneg (mul_nonneg hd1 hd2) (mul_nonneg hd3 hd4)))]
  unfold McD MixParams.KMcD
  refine le_trans (norm_add_add_sub_le _ _ _) ?_
  linarith [hp1, hp2, hp3]

/-- **`M1D` envelope**: `‖M1D(s)‖ ≤ K1D·M³` on `‖s‖ ≤ M`, `1 ≤ M`. -/
theorem M1D_norm_le (P : MixParams) (hP : P.Phys) {M : ℝ} (hM : 1 ≤ M)
    {s : ℂ} (hs : ‖s‖ ≤ M) : ‖M1D P s‖ ≤ P.K1D * M ^ 3 := by
  obtain ⟨hsg0, hsg01, hrr, hqp, hqpp⟩ := hP
  have hsg0' : 0 ≤ P.sig0 := hsg0.le
  have hp1 : ‖dNumD (P.rr 0 0) (P.Qp 0 0) (P.Qpp 0 0) P.sig0 s *
      (((P.rr 1 1 : ℝ) : ℂ) * polyF (P.Qp 1 1) (P.Qpp 1 1) s)‖ ≤
      (3 + P.rr 0 0 * cBD (P.Qp 0 0) (P.Qpp 0 0) P.sig0) *
        (P.rr 1 1 * (P.Qp 1 1 + P.Qpp 1 1)) * M ^ 3 := by
    have h1 := dNumD_norm_le (hrr 0 0).le (hqp 0 0).le (hqpp 0 0).le hsg0' hM hs
    have h2 : ‖((P.rr 1 1 : ℝ) : ℂ) * polyF (P.Qp 1 1) (P.Qpp 1 1) s‖ ≤
        P.rr 1 1 * ((P.Qp 1 1 + P.Qpp 1 1) * M) := by
      rw [norm_real_mul (hrr 1 1).le]
      exact mul_le_mul_of_nonneg_left
        (polyF_norm_le (hqp 1 1).le (hqpp 1 1).le hM hs) (hrr 1 1).le
    calc ‖dNumD (P.rr 0 0) (P.Qp 0 0) (P.Qpp 0 0) P.sig0 s *
        (((P.rr 1 1 : ℝ) : ℂ) * polyF (P.Qp 1 1) (P.Qpp 1 1) s)‖
        ≤ ((3 + P.rr 0 0 * cBD (P.Qp 0 0) (P.Qpp 0 0) P.sig0) * M ^ 2) *
          (P.rr 1 1 * ((P.Qp 1 1 + P.Qpp 1 1) * M)) := norm_mul_le_bound h1 h2
      _ = (3 + P.rr 0 0 * cBD (P.Qp 0 0) (P.Qpp 0 0) P.sig0) *
          (P.rr 1 1 * (P.Qp 1 1 + P.Qpp 1 1)) * M ^ 3 := by ring
  have hp2 : ‖dNum (P.rr 0 0) (P.Qp 0 0) (P.Qpp 0 0) P.sig0 s *
      (((P.rr 1 1 : ℝ) : ℂ) * (P.Qp 1 1 : ℂ))‖ ≤
      (1 + P.rr 0 0 * cB (P.Qp 0 0) (P.Qpp 0 0) P.sig0) * (P.rr 1 1 * P.Qp 1 1) * M ^ 3 := by
    have h1 := dNum_norm_le (hrr 0 0).le (hqp 0 0).le (hqpp 0 0).le hsg0' hM hs
    have h2 : ‖((P.rr 1 1 : ℝ) : ℂ) * (P.Qp 1 1 : ℂ)‖ ≤ P.rr 1 1 * P.Qp 1 1 := by
      rw [norm_real_mul (hrr 1 1).le, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hqp 1 1).le]
    calc ‖dNum (P.rr 0 0) (P.Qp 0 0) (P.Qpp 0 0) P.sig0 s *
        (((P.rr 1 1 : ℝ) : ℂ) * (P.Qp 1 1 : ℂ))‖
        ≤ ((1 + P.rr 0 0 * cB (P.Qp 0 0) (P.Qpp 0 0) P.sig0) * M ^ 3) *
          (P.rr 1 1 * P.Qp 1 1) := norm_mul_le_bound h1 h2
      _ = (1 + P.rr 0 0 * cB (P.Qp 0 0) (P.Qpp 0 0) P.sig0) *
          (P.rr 1 1 * P.Qp 1 1) * M ^ 3 := by ring
  have hp3 : ‖((P.rr 0 1 * P.rr 1 0 : ℝ) : ℂ) *
      (polyBD (P.Qp 0 1) (P.Qpp 0 1) P.sig0 s * polyF (P.Qp 1 0) (P.Qpp 1 0) s +
        polyB (P.Qp 0 1) (P.Qpp 0 1) P.sig0 s * (P.Qp 1 0 : ℂ))‖ ≤
      P.rr 0 1 * P.rr 1 0 *
        (cBD (P.Qp 0 1) (P.Qpp 0 1) P.sig0 * (P.Qp 1 0 + P.Qpp 1 0) +
          cB (P.Qp 0 1) (P.Qpp 0 1) P.sig0 * P.Qp 1 0) * M ^ 3 := by
    have hc : 0 ≤ P.rr 0 1 * P.rr 1 0 := mul_nonneg (hrr 0 1).le (hrr 1 0).le
    have h1 := norm_mul_le_bound (polyBD_norm_le (hqp 0 1).le (hqpp 0 1).le hsg0' hM hs)
      (polyF_norm_le (hqp 1 0).le (hqpp 1 0).le hM hs)
    have h2 : ‖polyB (P.Qp 0 1) (P.Qpp 0 1) P.sig0 s * (P.Qp 1 0 : ℂ)‖ ≤
        (cB (P.Qp 0 1) (P.Qpp 0 1) P.sig0 * M ^ 2) * P.Qp 1 0 :=
      norm_mul_le_bound (polyB_norm_le (hqp 0 1).le (hqpp 0 1).le hsg0' hM hs)
        (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hqp 1 0).le])
    have h23 : M ^ 2 ≤ M ^ 3 := pow_le_pow_right₀ hM (by norm_num)
    have hd1 := cBD_nonneg (hqp 0 1).le (hqpp 0 1).le hsg0'
    have hd3 := cB_nonneg (hqp 0 1).le (hqpp 0 1).le hsg0'
    rw [norm_real_mul hc]
    have hsum : ‖polyBD (P.Qp 0 1) (P.Qpp 0 1) P.sig0 s * polyF (P.Qp 1 0) (P.Qpp 1 0) s +
        polyB (P.Qp 0 1) (P.Qpp 0 1) P.sig0 s * (P.Qp 1 0 : ℂ)‖ ≤
        (cBD (P.Qp 0 1) (P.Qpp 0 1) P.sig0 * (P.Qp 1 0 + P.Qpp 1 0) +
          cB (P.Qp 0 1) (P.Qpp 0 1) P.sig0 * P.Qp 1 0) * M ^ 3 := by
      refine le_trans (norm_add_le _ _) ?_
      have e1 : cB (P.Qp 0 1) (P.Qpp 0 1) P.sig0 * M ^ 2 * P.Qp 1 0 ≤
          cB (P.Qp 0 1) (P.Qpp 0 1) P.sig0 * P.Qp 1 0 * M ^ 3 := by
        nlinarith [mul_le_mul_of_nonneg_left h23 (mul_nonneg hd3 (hqp 1 0).le)]
      have e0 : cBD (P.Qp 0 1) (P.Qpp 0 1) P.sig0 * (P.Qp 1 0 + P.Qpp 1 0) * M ^ 2 ≤
          cBD (P.Qp 0 1) (P.Qpp 0 1) P.sig0 * (P.Qp 1 0 + P.Qpp 1 0) * M ^ 3 := by
        nlinarith [mul_le_mul_of_nonneg_left h23
          (mul_nonneg hd1 (add_nonneg (hqp 1 0).le (hqpp 1 0).le))]
      nlinarith [h1, h2, e1, e0]
    have := mul_le_mul_of_nonneg_left hsum hc
    nlinarith [this]
  unfold M1D MixParams.K1D
  refine le_trans (norm_add₃_le) ?_
  linarith [hp1, hp2, hp3]

/-- Envelope constant: `‖M0D(s)‖ ≤ K0D·M³`. -/
def MixParams.K0D (P : MixParams) : ℝ :=
  P.rr 0 0 * P.Qp 0 0 * (1 + P.rr 1 1 * cB (P.Qp 1 1) (P.Qpp 1 1) P.sig1) +
    P.rr 0 0 * (P.Qp 0 0 + P.Qpp 0 0) * (3 + P.rr 1 1 * cBD (P.Qp 1 1) (P.Qpp 1 1) P.sig1) +
    P.rr 0 1 * P.rr 1 0 *
      (P.Qp 0 1 * cB (P.Qp 1 0) (P.Qpp 1 0) P.sig1 +
        (P.Qp 0 1 + P.Qpp 0 1) * cBD (P.Qp 1 0) (P.Qpp 1 0) P.sig1)

/-- Envelope constant: `‖M01D(s)‖ ≤ K01D·M`. -/
def MixParams.K01D (P : MixParams) : ℝ :=
  P.rr 0 0 * P.Qp 0 0 * (P.rr 1 1 * (P.Qp 1 1 + P.Qpp 1 1)) +
    P.rr 0 0 * (P.Qp 0 0 + P.Qpp 0 0) * (P.rr 1 1 * P.Qp 1 1) +
    P.rr 0 1 * P.rr 1 0 *
      (P.Qp 0 1 * (P.Qp 1 0 + P.Qpp 1 0) + (P.Qp 0 1 + P.Qpp 0 1) * P.Qp 1 0)

/-- **`M0D` envelope**: `‖M0D(s)‖ ≤ K0D·M³` on `‖s‖ ≤ M`, `1 ≤ M`. -/
theorem M0D_norm_le (P : MixParams) (hP : P.Phys) {M : ℝ} (hM : 1 ≤ M)
    {s : ℂ} (hs : ‖s‖ ≤ M) : ‖M0D P s‖ ≤ P.K0D * M ^ 3 := by
  obtain ⟨hsg0, hsg01, hrr, hqp, hqpp⟩ := hP
  have hsg1' : 0 ≤ P.sig1 := by linarith [hsg0.le]
  have hcast : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → ‖((a : ℝ) : ℂ) * ((b : ℝ) : ℂ)‖ ≤ a * b := by
    intro a b ha hb
    rw [norm_real_mul ha, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb]
  have hp1 : ‖((P.rr 0 0 : ℝ) : ℂ) * (P.Qp 0 0 : ℂ) *
      dNum (P.rr 1 1) (P.Qp 1 1) (P.Qpp 1 1) P.sig1 s‖ ≤
      P.rr 0 0 * P.Qp 0 0 * (1 + P.rr 1 1 * cB (P.Qp 1 1) (P.Qpp 1 1) P.sig1) * M ^ 3 := by
    have h2 := dNum_norm_le (hrr 1 1).le (hqp 1 1).le (hqpp 1 1).le hsg1' hM hs
    calc ‖((P.rr 0 0 : ℝ) : ℂ) * (P.Qp 0 0 : ℂ) *
        dNum (P.rr 1 1) (P.Qp 1 1) (P.Qpp 1 1) P.sig1 s‖
        ≤ (P.rr 0 0 * P.Qp 0 0) *
          ((1 + P.rr 1 1 * cB (P.Qp 1 1) (P.Qpp 1 1) P.sig1) * M ^ 3) :=
          norm_mul_le_bound (hcast _ _ (hrr 0 0).le (hqp 0 0).le) h2
      _ = P.rr 0 0 * P.Qp 0 0 *
          (1 + P.rr 1 1 * cB (P.Qp 1 1) (P.Qpp 1 1) P.sig1) * M ^ 3 := by ring
  have hp2 : ‖((P.rr 0 0 : ℝ) : ℂ) * polyF (P.Qp 0 0) (P.Qpp 0 0) s *
      dNumD (P.rr 1 1) (P.Qp 1 1) (P.Qpp 1 1) P.sig1 s‖ ≤
      P.rr 0 0 * (P.Qp 0 0 + P.Qpp 0 0) *
        (3 + P.rr 1 1 * cBD (P.Qp 1 1) (P.Qpp 1 1) P.sig1) * M ^ 3 := by
    have h1 : ‖((P.rr 0 0 : ℝ) : ℂ) * polyF (P.Qp 0 0) (P.Qpp 0 0) s‖ ≤
        P.rr 0 0 * ((P.Qp 0 0 + P.Qpp 0 0) * M) := by
      rw [norm_real_mul (hrr 0 0).le]
      exact mul_le_mul_of_nonneg_left
        (polyF_norm_le (hqp 0 0).le (hqpp 0 0).le hM hs) (hrr 0 0).le
    have h2 := dNumD_norm_le (hrr 1 1).le (hqp 1 1).le (hqpp 1 1).le hsg1' hM hs
    calc ‖((P.rr 0 0 : ℝ) : ℂ) * polyF (P.Qp 0 0) (P.Qpp 0 0) s *
        dNumD (P.rr 1 1) (P.Qp 1 1) (P.Qpp 1 1) P.sig1 s‖
        ≤ (P.rr 0 0 * ((P.Qp 0 0 + P.Qpp 0 0) * M)) *
          ((3 + P.rr 1 1 * cBD (P.Qp 1 1) (P.Qpp 1 1) P.sig1) * M ^ 2) :=
          norm_mul_le_bound h1 h2
      _ = P.rr 0 0 * (P.Qp 0 0 + P.Qpp 0 0) *
          (3 + P.rr 1 1 * cBD (P.Qp 1 1) (P.Qpp 1 1) P.sig1) * M ^ 3 := by ring
  have hp3 : ‖((P.rr 0 1 * P.rr 1 0 : ℝ) : ℂ) *
      ((P.Qp 0 1 : ℂ) * polyB (P.Qp 1 0) (P.Qpp 1 0) P.sig1 s +
        polyF (P.Qp 0 1) (P.Qpp 0 1) s * polyBD (P.Qp 1 0) (P.Qpp 1 0) P.sig1 s)‖ ≤
      P.rr 0 1 * P.rr 1 0 *
        (P.Qp 0 1 * cB (P.Qp 1 0) (P.Qpp 1 0) P.sig1 +
          (P.Qp 0 1 + P.Qpp 0 1) * cBD (P.Qp 1 0) (P.Qpp 1 0) P.sig1) * M ^ 3 := by
    have hc : 0 ≤ P.rr 0 1 * P.rr 1 0 := mul_nonneg (hrr 0 1).le (hrr 1 0).le
    have h1 : ‖(P.Qp 0 1 : ℂ) * polyB (P.Qp 1 0) (P.Qpp 1 0) P.sig1 s‖ ≤
        P.Qp 0 1 * (cB (P.Qp 1 0) (P.Qpp 1 0) P.sig1 * M ^ 2) := by
      rw [norm_real_mul (hqp 0 1).le]
      exact mul_le_mul_of_nonneg_left
        (polyB_norm_le (hqp 1 0).le (hqpp 1 0).le hsg1' hM hs) (hqp 0 1).le
    have h2 := norm_mul_le_bound (polyF_norm_le (hqp 0 1).le (hqpp 0 1).le hM hs)
      (polyBD_norm_le (hqp 1 0).le (hqpp 1 0).le hsg1' hM hs)
    have h23 : M ^ 2 ≤ M ^ 3 := pow_le_pow_right₀ hM (by norm_num)
    have hd2 := cB_nonneg (hqp 1 0).le (hqpp 1 0).le hsg1'
    have hd4 := cBD_nonneg (hqp 1 0).le (hqpp 1 0).le hsg1'
    rw [norm_real_mul hc]
    have hsum : ‖(P.Qp 0 1 : ℂ) * polyB (P.Qp 1 0) (P.Qpp 1 0) P.sig1 s +
        polyF (P.Qp 0 1) (P.Qpp 0 1) s * polyBD (P.Qp 1 0) (P.Qpp 1 0) P.sig1 s‖ ≤
        (P.Qp 0 1 * cB (P.Qp 1 0) (P.Qpp 1 0) P.sig1 +
          (P.Qp 0 1 + P.Qpp 0 1) * cBD (P.Qp 1 0) (P.Qpp 1 0) P.sig1) * M ^ 3 := by
      refine le_trans (norm_add_le _ _) ?_
      have e1 : P.Qp 0 1 * cB (P.Qp 1 0) (P.Qpp 1 0) P.sig1 * M ^ 2 ≤
          P.Qp 0 1 * cB (P.Qp 1 0) (P.Qpp 1 0) P.sig1 * M ^ 3 := by
        nlinarith [mul_le_mul_of_nonneg_left h23 (mul_nonneg (hqp 0 1).le hd2)]
      have e2 : (P.Qp 0 1 + P.Qpp 0 1) * cBD (P.Qp 1 0) (P.Qpp 1 0) P.sig1 * M ^ 2 ≤
          (P.Qp 0 1 + P.Qpp 0 1) * cBD (P.Qp 1 0) (P.Qpp 1 0) P.sig1 * M ^ 3 := by
        nlinarith [mul_le_mul_of_nonneg_left h23
          (mul_nonneg (add_nonneg (hqp 0 1).le (hqpp 0 1).le) hd4)]
      nlinarith [h1, h2, e1, e2]
    have := mul_le_mul_of_nonneg_left hsum hc
    nlinarith [this]
  unfold M0D MixParams.K0D
  refine le_trans (norm_add₃_le) ?_
  linarith [hp1, hp2, hp3]

/-- **`M01D` envelope**: `‖M01D(s)‖ ≤ K01D·M` on `‖s‖ ≤ M`, `1 ≤ M`. -/
theorem M01D_norm_le (P : MixParams) (hP : P.Phys) {M : ℝ} (hM : 1 ≤ M)
    {s : ℂ} (hs : ‖s‖ ≤ M) : ‖M01D P s‖ ≤ P.K01D * M := by
  obtain ⟨hsg0, hsg01, hrr, hqp, hqpp⟩ := hP
  have hcast : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → ‖((a : ℝ) : ℂ) * ((b : ℝ) : ℂ)‖ ≤ a * b := by
    intro a b ha hb
    rw [norm_real_mul ha, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb]
  have hp1 : ‖((P.rr 0 0 : ℝ) : ℂ) * (P.Qp 0 0 : ℂ) *
      (((P.rr 1 1 : ℝ) : ℂ) * polyF (P.Qp 1 1) (P.Qpp 1 1) s)‖ ≤
      P.rr 0 0 * P.Qp 0 0 * (P.rr 1 1 * (P.Qp 1 1 + P.Qpp 1 1)) * M := by
    have h2 : ‖((P.rr 1 1 : ℝ) : ℂ) * polyF (P.Qp 1 1) (P.Qpp 1 1) s‖ ≤
        P.rr 1 1 * ((P.Qp 1 1 + P.Qpp 1 1) * M) := by
      rw [norm_real_mul (hrr 1 1).le]
      exact mul_le_mul_of_nonneg_left
        (polyF_norm_le (hqp 1 1).le (hqpp 1 1).le hM hs) (hrr 1 1).le
    calc ‖((P.rr 0 0 : ℝ) : ℂ) * (P.Qp 0 0 : ℂ) *
        (((P.rr 1 1 : ℝ) : ℂ) * polyF (P.Qp 1 1) (P.Qpp 1 1) s)‖
        ≤ (P.rr 0 0 * P.Qp 0 0) * (P.rr 1 1 * ((P.Qp 1 1 + P.Qpp 1 1) * M)) :=
          norm_mul_le_bound (hcast _ _ (hrr 0 0).le (hqp 0 0).le) h2
      _ = P.rr 0 0 * P.Qp 0 0 * (P.rr 1 1 * (P.Qp 1 1 + P.Qpp 1 1)) * M := by ring
  have hp2 : ‖((P.rr 0 0 : ℝ) : ℂ) * polyF (P.Qp 0 0) (P.Qpp 0 0) s *
      (((P.rr 1 1 : ℝ) : ℂ) * (P.Qp 1 1 : ℂ))‖ ≤
      P.rr 0 0 * (P.Qp 0 0 + P.Qpp 0 0) * (P.rr 1 1 * P.Qp 1 1) * M := by
    have h1 : ‖((P.rr 0 0 : ℝ) : ℂ) * polyF (P.Qp 0 0) (P.Qpp 0 0) s‖ ≤
        P.rr 0 0 * ((P.Qp 0 0 + P.Qpp 0 0) * M) := by
      rw [norm_real_mul (hrr 0 0).le]
      exact mul_le_mul_of_nonneg_left
        (polyF_norm_le (hqp 0 0).le (hqpp 0 0).le hM hs) (hrr 0 0).le
    calc ‖((P.rr 0 0 : ℝ) : ℂ) * polyF (P.Qp 0 0) (P.Qpp 0 0) s *
        (((P.rr 1 1 : ℝ) : ℂ) * (P.Qp 1 1 : ℂ))‖
        ≤ (P.rr 0 0 * ((P.Qp 0 0 + P.Qpp 0 0) * M)) * (P.rr 1 1 * P.Qp 1 1) :=
          norm_mul_le_bound h1 (hcast _ _ (hrr 1 1).le (hqp 1 1).le)
      _ = P.rr 0 0 * (P.Qp 0 0 + P.Qpp 0 0) * (P.rr 1 1 * P.Qp 1 1) * M := by ring
  have hp3 : ‖((P.rr 0 1 * P.rr 1 0 : ℝ) : ℂ) *
      ((P.Qp 0 1 : ℂ) * polyF (P.Qp 1 0) (P.Qpp 1 0) s +
        polyF (P.Qp 0 1) (P.Qpp 0 1) s * (P.Qp 1 0 : ℂ))‖ ≤
      P.rr 0 1 * P.rr 1 0 *
        (P.Qp 0 1 * (P.Qp 1 0 + P.Qpp 1 0) + (P.Qp 0 1 + P.Qpp 0 1) * P.Qp 1 0) * M := by
    have hc : 0 ≤ P.rr 0 1 * P.rr 1 0 := mul_nonneg (hrr 0 1).le (hrr 1 0).le
    have h1 : ‖(P.Qp 0 1 : ℂ) * polyF (P.Qp 1 0) (P.Qpp 1 0) s‖ ≤
        P.Qp 0 1 * ((P.Qp 1 0 + P.Qpp 1 0) * M) := by
      rw [norm_real_mul (hqp 0 1).le]
      exact mul_le_mul_of_nonneg_left
        (polyF_norm_le (hqp 1 0).le (hqpp 1 0).le hM hs) (hqp 0 1).le
    have h2 : ‖polyF (P.Qp 0 1) (P.Qpp 0 1) s * (P.Qp 1 0 : ℂ)‖ ≤
        ((P.Qp 0 1 + P.Qpp 0 1) * M) * P.Qp 1 0 :=
      norm_mul_le_bound (polyF_norm_le (hqp 0 1).le (hqpp 0 1).le hM hs)
        (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hqp 1 0).le])
    rw [norm_real_mul hc]
    have hsum := le_trans (norm_add_le _ _) (add_le_add h1 h2)
    have := mul_le_mul_of_nonneg_left hsum hc
    nlinarith [this]
  unfold M01D MixParams.K01D
  refine le_trans (norm_add_add_sub_le _ _ _) ?_
  linarith [hp1, hp2, hp3]

/-! ### The anchor `i·Y` and the modulus ratio `t` -/

/-- The purely imaginary anchor point `i·Y`. -/
def aI (Y : ℝ) : ℂ := Complex.I * (Y : ℂ)

/-- `‖i·Y‖ = Y` for `Y ≥ 0`. -/
theorem aI_norm {Y : ℝ} (hY : 0 ≤ Y) : ‖aI Y‖ = Y := by
  unfold aI
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hY]

/-- `(i·Y)⁶ = −Y⁶`. -/
theorem aI_pow_six (Y : ℝ) : aI Y ^ 6 = -((Y : ℂ) ^ 6) := by
  unfold aI
  have h : Complex.I ^ 6 = -1 := by
    rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, Complex.I_sq]
    norm_num
  rw [mul_pow, h]
  ring

/-- `(i·Y)⁴ = Y⁴`. -/
theorem aI_pow_four (Y : ℝ) : aI Y ^ 4 = (Y : ℂ) ^ 4 := by
  unfold aI
  have h : Complex.I ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Complex.I_sq]
    norm_num
  rw [mul_pow, h]
  ring

/-- The anchor modulus ratio `t(Y) := ‖Mc(iY)‖ / ‖M₁(iY)‖`. -/
def tRat (P : MixParams) (Y : ℝ) : ℝ := ‖McNum P (aI Y)‖ / ‖M1Num P (aI Y)‖

/-- Anchor lower envelope for `Mc`: `Y⁶/2 ≤ ‖Mc(iY)‖` once `Y ≥ max(1, 2·KMc)`. -/
theorem McNum_anchor_lower (P : MixParams) (hP : P.Phys) {Y : ℝ} (hY : 1 ≤ Y)
    (hYK : 2 * P.KMc ≤ Y) : Y ^ 6 / 2 ≤ ‖McNum P (aI Y)‖ := by
  have hY0 : (0 : ℝ) ≤ Y := by linarith
  have hsub := McNum_sub_norm_le P hP hY (le_of_eq (aI_norm hY0))
  have h6 : ‖aI Y ^ 6‖ = Y ^ 6 := by rw [norm_pow, aI_norm hY0]
  have htri : ‖aI Y ^ 6‖ ≤ ‖McNum P (aI Y)‖ + ‖McNum P (aI Y) - aI Y ^ 6‖ := by
    calc ‖aI Y ^ 6‖ = ‖McNum P (aI Y) - (McNum P (aI Y) - aI Y ^ 6)‖ := by congr 1; ring
      _ ≤ ‖McNum P (aI Y)‖ + ‖McNum P (aI Y) - aI Y ^ 6‖ := norm_sub_le _ _
  rw [h6] at htri
  nlinarith [pow_nonneg hY0 5, hsub, htri]

/-- Anchor upper envelope for `Mc`: `‖Mc(iY)‖ ≤ 2·Y⁶` once `Y ≥ max(1, KMc)`. -/
theorem McNum_anchor_upper (P : MixParams) (hP : P.Phys) {Y : ℝ} (hY : 1 ≤ Y)
    (hYK : P.KMc ≤ Y) : ‖McNum P (aI Y)‖ ≤ 2 * Y ^ 6 := by
  have hY0 : (0 : ℝ) ≤ Y := by linarith
  have hsub := McNum_sub_norm_le P hP hY (le_of_eq (aI_norm hY0))
  have h6 : ‖aI Y ^ 6‖ = Y ^ 6 := by rw [norm_pow, aI_norm hY0]
  have htri : ‖McNum P (aI Y)‖ ≤ ‖McNum P (aI Y) - aI Y ^ 6‖ + ‖aI Y ^ 6‖ := by
    calc ‖McNum P (aI Y)‖ = ‖(McNum P (aI Y) - aI Y ^ 6) + aI Y ^ 6‖ := by congr 1; ring
      _ ≤ ‖McNum P (aI Y) - aI Y ^ 6‖ + ‖aI Y ^ 6‖ := norm_add_le _ _
  rw [h6] at htri
  nlinarith [pow_nonneg hY0 5, hsub, htri]

/-- Anchor lower envelope for `M₁`: `(μ/2)·Y⁴ ≤ ‖M₁(iY)‖` once `Y ≥ 1`, `μY ≥ 2·K1`. -/
theorem M1Num_anchor_lower (P : MixParams) (hP : P.Phys) {Y : ℝ} (hY : 1 ≤ Y)
    (hYK : 2 * P.K1 ≤ P.mu * Y) : P.mu / 2 * Y ^ 4 ≤ ‖M1Num P (aI Y)‖ := by
  have hY0 : (0 : ℝ) ≤ Y := by linarith
  have hsub := M1Num_sub_norm_le P hP hY (le_of_eq (aI_norm hY0))
  have hmu0 : 0 ≤ P.mu := by
    obtain ⟨_, _, hrr, hqp, _⟩ := hP
    exact mul_nonneg (hrr 1 1).le (hqp 1 1).le
  have h4 : ‖((P.mu : ℝ) : ℂ) * aI Y ^ 4‖ = P.mu * Y ^ 4 := by
    rw [norm_real_mul hmu0, norm_pow, aI_norm hY0]
  have htri : ‖((P.mu : ℝ) : ℂ) * aI Y ^ 4‖ ≤
      ‖M1Num P (aI Y)‖ + ‖M1Num P (aI Y) - ((P.mu : ℝ) : ℂ) * aI Y ^ 4‖ := by
    calc ‖((P.mu : ℝ) : ℂ) * aI Y ^ 4‖
        = ‖M1Num P (aI Y) - (M1Num P (aI Y) - ((P.mu : ℝ) : ℂ) * aI Y ^ 4)‖ := by
          congr 1; ring
      _ ≤ ‖M1Num P (aI Y)‖ + ‖M1Num P (aI Y) - ((P.mu : ℝ) : ℂ) * aI Y ^ 4‖ :=
          norm_sub_le _ _
  rw [h4] at htri
  nlinarith [pow_nonneg hY0 3, hsub, htri]

/-- Anchor positivity of `‖M₁(iY)‖` (strict), under the same thresholds plus `μ > 0`. -/
theorem M1Num_anchor_pos (P : MixParams) (hP : P.Phys) {Y : ℝ} (hY : 1 ≤ Y)
    (hYK : 2 * P.K1 ≤ P.mu * Y) : 0 < ‖M1Num P (aI Y)‖ := by
  have hmu : 0 < P.mu := by
    obtain ⟨_, _, hrr, hqp, _⟩ := hP
    exact mul_pos (hrr 1 1) (hqp 1 1)
  have h := M1Num_anchor_lower P hP hY hYK
  have hY0 : (0 : ℝ) < Y := by linarith
  nlinarith [pow_pos hY0 4]

/-- Anchor positivity of `‖Mc(iY)‖` (strict). -/
theorem McNum_anchor_pos (P : MixParams) (hP : P.Phys) {Y : ℝ} (hY : 1 ≤ Y)
    (hYK : 2 * P.KMc ≤ Y) : 0 < ‖McNum P (aI Y)‖ := by
  have h := McNum_anchor_lower P hP hY hYK
  have hY0 : (0 : ℝ) < Y := by linarith
  nlinarith [pow_pos hY0 6]

/-- **Ratio lower envelope**: `Y²/(2(μ+K1)) ≤ t(Y)` under the anchor thresholds. -/
theorem tRat_lower (P : MixParams) (hP : P.Phys) {Y : ℝ} (hY : 1 ≤ Y)
    (hYMc : 2 * P.KMc ≤ Y) (hYM1 : 2 * P.K1 ≤ P.mu * Y) :
    Y ^ 2 / (2 * (P.mu + P.K1)) ≤ tRat P Y := by
  have hY0 : (0 : ℝ) < Y := by linarith
  have hmu : 0 < P.mu := by
    obtain ⟨_, _, hrr, hqp, _⟩ := hP
    exact mul_pos (hrr 1 1) (hqp 1 1)
  have hK10 := K1_nonneg P hP
  have hMc := McNum_anchor_lower P hP hY hYMc
  have hM1up := M1Num_norm_le P hP hY (le_of_eq (aI_norm hY0.le))
  have hM1pos := M1Num_anchor_pos P hP hY hYM1
  have hdiv : (Y ^ 6 / 2) / ((P.mu + P.K1) * Y ^ 4) ≤
      ‖McNum P (aI Y)‖ / ‖M1Num P (aI Y)‖ :=
    FMSA.HardSphere.div_le_div_bound hMc (le_trans (by positivity) hMc) hM1pos hM1up
  have heq : (Y ^ 6 / 2) / ((P.mu + P.K1) * Y ^ 4) = Y ^ 2 / (2 * (P.mu + P.K1)) := by
    rw [div_eq_div_iff (by positivity) (by positivity)]
    ring
  rw [heq] at hdiv
  exact hdiv

/-- **Ratio upper envelope**: `t(Y) ≤ (4/μ)·Y²` under the anchor thresholds. -/
theorem tRat_upper (P : MixParams) (hP : P.Phys) {Y : ℝ} (hY : 1 ≤ Y)
    (hYMc : P.KMc ≤ Y) (hYM1 : 2 * P.K1 ≤ P.mu * Y) :
    tRat P Y ≤ 4 / P.mu * Y ^ 2 := by
  have hY0 : (0 : ℝ) < Y := by linarith
  have hmu : 0 < P.mu := by
    obtain ⟨_, _, hrr, hqp, _⟩ := hP
    exact mul_pos (hrr 1 1) (hqp 1 1)
  have hMc := McNum_anchor_upper P hP hY hYMc
  have hM1 := M1Num_anchor_lower P hP hY hYM1
  have hM1pos : 0 < P.mu / 2 * Y ^ 4 := by positivity
  have hdiv : ‖McNum P (aI Y)‖ / ‖M1Num P (aI Y)‖ ≤
      (2 * Y ^ 6) / (P.mu / 2 * Y ^ 4) :=
    FMSA.HardSphere.div_le_div_bound hMc (by positivity) hM1pos hM1
  have heq : (2 * Y ^ 6) / (P.mu / 2 * Y ^ 4) = 4 / P.mu * Y ^ 2 := by
    field_simp
    ring
  rw [heq] at hdiv
  exact hdiv

/-! ### Branch safety at the anchor: the sign of `Re(Mc·conj(−M₁))` -/

/-- Combined remainder constant for the anchor product bounds. -/
def MixParams.KIm (P : MixParams) : ℝ := P.K1 + P.mu * P.KMc + P.KMc * P.K1

/-- Triangle inequality in the `a - b - c` shape. -/
theorem norm_sub_sub_le (a b c : ℂ) : ‖a - b - c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
  calc ‖a - b - c‖ ≤ ‖a - b‖ + ‖c‖ := norm_sub_le _ _
    _ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by linarith [norm_sub_le a b]

/-- **Anchor product decomposition**: `Mc(iY)·conj(−M₁(iY)) = μY¹⁰ + w` with the explicit
remainder `w` built from `Rc := Mc − (iY)⁶` and `R1 := M₁ − μ(iY)⁴` (using `(iY)⁶ = −Y⁶`,
`(iY)⁴ = Y⁴`). -/
theorem anchor_conj_prod (P : MixParams) (Y : ℝ) :
    McNum P (aI Y) * (starRingEnd ℂ) (-(M1Num P (aI Y))) =
      ((P.mu * Y ^ 10 : ℝ) : ℂ) +
        (((Y ^ 6 : ℝ) : ℂ) *
            (starRingEnd ℂ) (M1Num P (aI Y) - ((P.mu : ℝ) : ℂ) * aI Y ^ 4) -
          ((P.mu * Y ^ 4 : ℝ) : ℂ) * (McNum P (aI Y) - aI Y ^ 6) -
          (McNum P (aI Y) - aI Y ^ 6) *
            (starRingEnd ℂ) (M1Num P (aI Y) - ((P.mu : ℝ) : ℂ) * aI Y ^ 4)) := by
  set Rc : ℂ := McNum P (aI Y) - aI Y ^ 6 with hRc
  set R1 : ℂ := M1Num P (aI Y) - ((P.mu : ℝ) : ℂ) * aI Y ^ 4 with hR1
  have hMc : McNum P (aI Y) = -(((Y ^ 6 : ℝ)) : ℂ) + Rc := by
    rw [hRc, aI_pow_six]
    push_cast
    ring
  have hM1 : -(M1Num P (aI Y)) = -(((P.mu * Y ^ 4 : ℝ)) : ℂ) - R1 := by
    rw [hR1, aI_pow_four]
    push_cast
    ring
  have hconj : (starRingEnd ℂ) (-(M1Num P (aI Y))) =
      -(((P.mu * Y ^ 4 : ℝ)) : ℂ) - (starRingEnd ℂ) R1 := by
    rw [hM1, map_sub, map_neg, Complex.conj_ofReal]
  rw [hMc, hconj]
  push_cast
  ring

/-- `KMc` is nonnegative for physical parameters. -/
theorem KMc_nonneg (P : MixParams) (hP : P.Phys) : 0 ≤ P.KMc := by
  obtain ⟨hsg0, hsg01, hrr, hqp, hqpp⟩ := hP
  have hsg0' : 0 ≤ P.sig0 := hsg0.le
  have hsg1' : 0 ≤ P.sig1 := by linarith
  have hcB1 := cB_nonneg (hqp 0 0).le (hqpp 0 0).le hsg0'
  have hcB2 := cB_nonneg (hqp 1 1).le (hqpp 1 1).le hsg1'
  have hcB3 := cB_nonneg (hqp 0 1).le (hqpp 0 1).le hsg0'
  have hcB4 := cB_nonneg (hqp 1 0).le (hqpp 1 0).le hsg1'
  have h1 := (hrr 0 0).le; have h2 := (hrr 1 1).le
  have h3 := (hrr 0 1).le; have h4 := (hrr 1 0).le
  unfold MixParams.KMc
  positivity

/-- Norm bound on the anchor product remainder `w`: `‖w‖ ≤ KIm·Y⁹` for `Y ≥ 1`. -/
theorem anchor_w_norm_le (P : MixParams) (hP : P.Phys) {Y : ℝ} (hY : 1 ≤ Y) :
    ‖((Y ^ 6 : ℝ) : ℂ) * (starRingEnd ℂ) (M1Num P (aI Y) - ((P.mu : ℝ) : ℂ) * aI Y ^ 4) -
        ((P.mu * Y ^ 4 : ℝ) : ℂ) * (McNum P (aI Y) - aI Y ^ 6) -
        (McNum P (aI Y) - aI Y ^ 6) *
          (starRingEnd ℂ) (M1Num P (aI Y) - ((P.mu : ℝ) : ℂ) * aI Y ^ 4)‖ ≤
      P.KIm * Y ^ 9 := by
  have hY0 : (0 : ℝ) ≤ Y := by linarith
  have hmu0 : 0 ≤ P.mu := by
    obtain ⟨_, _, hrr, hqp, _⟩ := hP
    exact mul_nonneg (hrr 1 1).le (hqp 1 1).le
  have hKMc0 := KMc_nonneg P hP
  have hK10 := K1_nonneg P hP
  have hRc := McNum_sub_norm_le P hP hY (le_of_eq (aI_norm hY0))
  have hR1 := M1Num_sub_norm_le P hP hY (le_of_eq (aI_norm hY0))
  have hR1c : ‖(starRingEnd ℂ) (M1Num P (aI Y) - ((P.mu : ℝ) : ℂ) * aI Y ^ 4)‖ ≤
      P.K1 * Y ^ 3 := by rw [Complex.norm_conj]; exact hR1
  have hc1 : ‖((Y ^ 6 : ℝ) : ℂ)‖ ≤ Y ^ 6 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hc2 : ‖((P.mu * Y ^ 4 : ℝ) : ℂ)‖ ≤ P.mu * Y ^ 4 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hp1 : ‖((Y ^ 6 : ℝ) : ℂ) *
      (starRingEnd ℂ) (M1Num P (aI Y) - ((P.mu : ℝ) : ℂ) * aI Y ^ 4)‖ ≤ P.K1 * Y ^ 9 := by
    calc ‖((Y ^ 6 : ℝ) : ℂ) *
        (starRingEnd ℂ) (M1Num P (aI Y) - ((P.mu : ℝ) : ℂ) * aI Y ^ 4)‖
        ≤ Y ^ 6 * (P.K1 * Y ^ 3) := norm_mul_le_bound hc1 hR1c
      _ = P.K1 * Y ^ 9 := by ring
  have hp2 : ‖((P.mu * Y ^ 4 : ℝ) : ℂ) * (McNum P (aI Y) - aI Y ^ 6)‖ ≤
      P.mu * P.KMc * Y ^ 9 := by
    calc ‖((P.mu * Y ^ 4 : ℝ) : ℂ) * (McNum P (aI Y) - aI Y ^ 6)‖
        ≤ P.mu * Y ^ 4 * (P.KMc * Y ^ 5) := norm_mul_le_bound hc2 hRc
      _ = P.mu * P.KMc * Y ^ 9 := by ring
  have hp3 : ‖(McNum P (aI Y) - aI Y ^ 6) *
      (starRingEnd ℂ) (M1Num P (aI Y) - ((P.mu : ℝ) : ℂ) * aI Y ^ 4)‖ ≤
      P.KMc * P.K1 * Y ^ 9 := by
    have h89 : Y ^ 8 ≤ Y ^ 9 := pow_le_pow_right₀ hY (by norm_num)
    calc ‖(McNum P (aI Y) - aI Y ^ 6) *
        (starRingEnd ℂ) (M1Num P (aI Y) - ((P.mu : ℝ) : ℂ) * aI Y ^ 4)‖
        ≤ (P.KMc * Y ^ 5) * (P.K1 * Y ^ 3) := norm_mul_le_bound hRc hR1c
      _ = P.KMc * P.K1 * Y ^ 8 := by ring
      _ ≤ P.KMc * P.K1 * Y ^ 9 :=
          mul_le_mul_of_nonneg_left h89 (mul_nonneg hKMc0 hK10)
  refine le_trans (norm_sub_sub_le _ _ _) ?_
  unfold MixParams.KIm
  linarith [hp1, hp2, hp3]

/-- **Branch safety at the anchor**: `0 ≤ Re(Mc(iY)·conj(−M₁(iY)))` once `μY ≥ KIm`. -/
theorem anchor_re_nonneg (P : MixParams) (hP : P.Phys) {Y : ℝ} (hY : 1 ≤ Y)
    (hYK : P.KIm ≤ P.mu * Y) :
    0 ≤ (McNum P (aI Y) * (starRingEnd ℂ) (-(M1Num P (aI Y)))).re := by
  have hY0 : (0 : ℝ) ≤ Y := by linarith
  have hw := anchor_w_norm_le P hP hY
  rw [anchor_conj_prod P Y, Complex.add_re, Complex.ofReal_re]
  set w : ℂ := ((Y ^ 6 : ℝ) : ℂ) *
      (starRingEnd ℂ) (M1Num P (aI Y) - ((P.mu : ℝ) : ℂ) * aI Y ^ 4) -
    ((P.mu * Y ^ 4 : ℝ) : ℂ) * (McNum P (aI Y) - aI Y ^ 6) -
    (McNum P (aI Y) - aI Y ^ 6) *
      (starRingEnd ℂ) (M1Num P (aI Y) - ((P.mu : ℝ) : ℂ) * aI Y ^ 4) with hwdef
  have hre : |w.re| ≤ ‖w‖ := Complex.abs_re_le_norm w
  have h9 : P.KIm * Y ^ 9 ≤ P.mu * Y ^ 10 := by
    have := mul_le_mul_of_nonneg_right hYK (pow_nonneg hY0 9)
    nlinarith [this]
  have habs := abs_le.mp (le_trans hre hw)
  linarith [habs.1, h9]

/-- **Anchor phase-mismatch bound**: `|Im(Mc(iY)·conj(−M₁(iY)))| ≤ KIm·Y⁹` for `Y ≥ 1`. -/
theorem anchor_im_le (P : MixParams) (hP : P.Phys) {Y : ℝ} (hY : 1 ≤ Y) :
    |(McNum P (aI Y) * (starRingEnd ℂ) (-(M1Num P (aI Y)))).im| ≤ P.KIm * Y ^ 9 := by
  have hw := anchor_w_norm_le P hP hY
  rw [anchor_conj_prod P Y, Complex.add_im, Complex.ofReal_im]
  set w : ℂ := ((Y ^ 6 : ℝ) : ℂ) *
      (starRingEnd ℂ) (M1Num P (aI Y) - ((P.mu : ℝ) : ℂ) * aI Y ^ 4) -
    ((P.mu * Y ^ 4 : ℝ) : ℂ) * (McNum P (aI Y) - aI Y ^ 6) -
    (McNum P (aI Y) - aI Y ^ 6) *
      (starRingEnd ℂ) (M1Num P (aI Y) - ((P.mu : ℝ) : ℂ) * aI Y ^ 4) with hwdef
  have him : |w.im| ≤ ‖w‖ := Complex.abs_im_le_norm w
  simpa using le_trans him hw

/-- **Anchor residual (chord-step third term)**: after the phase kill,
`‖Mc(iY) + t·M₁(iY)‖ ≤ (4KIm/μ)·Y⁵` — the generic `norm_sub_ratio_mul_le` applied with
`A := Mc`, `B := −M₁`. -/
theorem anchor_residual_le (P : MixParams) (hP : P.Phys) {Y : ℝ} (hY : 1 ≤ Y)
    (hYM1 : 2 * P.K1 ≤ P.mu * Y) (hYre : P.KIm ≤ P.mu * Y) :
    ‖McNum P (aI Y) + ((tRat P Y : ℝ) : ℂ) * M1Num P (aI Y)‖ ≤
      4 * P.KIm / P.mu * Y ^ 5 := by
  have hY0 : (0 : ℝ) < Y := lt_of_lt_of_le one_pos hY
  have hmu : 0 < P.mu := by
    obtain ⟨_, _, hrr, hqp, _⟩ := hP
    exact mul_pos (hrr 1 1) (hqp 1 1)
  have hM1pos := M1Num_anchor_pos P hP hY hYM1
  have hM1low := M1Num_anchor_lower P hP hY hYM1
  have hBne : -(M1Num P (aI Y)) ≠ 0 :=
    neg_ne_zero.mpr (norm_pos_iff.mp hM1pos)
  have h := FMSA.HardSphere.norm_sub_ratio_mul_le (McNum P (aI Y)) (-(M1Num P (aI Y)))
    hBne (anchor_re_nonneg P hP hY hYre)
  rw [norm_neg] at h
  have harg : McNum P (aI Y) -
      ((‖McNum P (aI Y)‖ / ‖M1Num P (aI Y)‖ : ℝ) : ℂ) * -(M1Num P (aI Y)) =
      McNum P (aI Y) + ((tRat P Y : ℝ) : ℂ) * M1Num P (aI Y) := by
    unfold tRat
    ring
  rw [harg] at h
  refine le_trans h ?_
  have him := anchor_im_le P hP hY
  have hKIm0 : 0 ≤ P.KIm := by
    have h1 := K1_nonneg P hP
    have h2 := KMc_nonneg P hP
    have h3 := hmu.le
    unfold MixParams.KIm
    positivity
  have hdiv : 2 * |(McNum P (aI Y) * (starRingEnd ℂ) (-(M1Num P (aI Y)))).im| /
      ‖M1Num P (aI Y)‖ ≤ (2 * (P.KIm * Y ^ 9)) / (P.mu / 2 * Y ^ 4) :=
    FMSA.HardSphere.div_le_div_bound (by linarith)
      (by positivity) (by positivity) hM1low
  refine le_trans hdiv ?_
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < P.mu / 2 * Y ^ 4)]
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hmu]
  ring_nf
  nlinarith [pow_nonneg hY0.le 9, hmu]

/-! ### The log-lift guess and the exact phase kill -/

/-- **The log-lift guess**: `sGuess n := −log(t(Yₙ))/σ₁ + i·Yₙ` with `Yₙ := 2πn/σ₁`. Its
imaginary part makes `σ₁·Im = 2πn` exact; its real part is the log-lift that kills the
oscillation of `e^{-sσ₁}`. -/
def sGuess (P : MixParams) (n : ℕ) : ℂ :=
  ((-Real.log (tRat P (2 * Real.pi * n / P.sig1)) / P.sig1 : ℝ) : ℂ) +
    aI (2 * Real.pi * n / P.sig1)

/-- Real part of the guess. -/
theorem sGuess_re (P : MixParams) (n : ℕ) :
    (sGuess P n).re = -Real.log (tRat P (2 * Real.pi * n / P.sig1)) / P.sig1 := by
  unfold sGuess aI
  simp

/-- Imaginary part of the guess. -/
theorem sGuess_im (P : MixParams) (n : ℕ) :
    (sGuess P n).im = 2 * Real.pi * n / P.sig1 := by
  unfold sGuess aI
  simp

/-- Norm of the decaying exponential at any point: `‖e^{-sc}‖ = e^{-Re(s)·c}`. -/
theorem norm_exp_neg_mul (s : ℂ) (c : ℝ) :
    ‖Complex.exp (-(s * (c : ℂ)))‖ = Real.exp (-(s.re * c)) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

/-- `‖e^z‖ ≤ e^{‖z‖}`. -/
theorem norm_exp_le_exp_norm (z : ℂ) : ‖Complex.exp z‖ ≤ Real.exp ‖z‖ :=
  (Complex.norm_exp z) ▸ Real.exp_le_exp.mpr (Complex.re_le_norm z)

/-- **Exact phase kill at the guess**: `e^{-sGuess(n)·σ₁} = t(Yₙ)` — the imaginary part
contributes the exact `2πn` phase and the real part exponentiates the log back to the
positive real ratio. -/
theorem exp_at_sGuess (P : MixParams) (hs1 : 0 < P.sig1) (n : ℕ)
    (ht : 0 < tRat P (2 * Real.pi * n / P.sig1)) :
    Complex.exp (-(sGuess P n * (P.sig1 : ℂ))) =
      ((tRat P (2 * Real.pi * n / P.sig1) : ℝ) : ℂ) := by
  set L : ℝ := Real.log (tRat P (2 * Real.pi * n / P.sig1)) with hL
  have hk : sGuess P n =
      ((-L / P.sig1 : ℝ) : ℂ) + Complex.I * ((2 * Real.pi * n / P.sig1 : ℝ) : ℂ) := by
    rw [hL]
    rfl
  have hexp_arg : -(sGuess P n * (P.sig1 : ℂ)) =
      (L : ℂ) + ((-(n : ℤ) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    rw [hk]
    have h1 : ((-L / P.sig1 : ℝ) : ℂ) * (P.sig1 : ℂ) = ((-L : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul]
      congr 1
      field_simp
    have h2 : ((2 * Real.pi * n / P.sig1 : ℝ) : ℂ) * (P.sig1 : ℂ) =
        2 * (Real.pi : ℂ) * (n : ℂ) := by
      rw [← Complex.ofReal_mul]
      have hval : 2 * Real.pi * n / P.sig1 * P.sig1 = 2 * Real.pi * n := by
        field_simp
      rw [hval]
      push_cast
      ring
    calc -((((-L / P.sig1 : ℝ) : ℂ) + Complex.I * ((2 * Real.pi * n / P.sig1 : ℝ) : ℂ)) *
          (P.sig1 : ℂ))
        = -(((-L / P.sig1 : ℝ) : ℂ) * (P.sig1 : ℂ)) -
            Complex.I * (((2 * Real.pi * n / P.sig1 : ℝ) : ℂ) * (P.sig1 : ℂ)) := by ring
      _ = -(((-L : ℝ) : ℂ)) - Complex.I * (2 * (Real.pi : ℂ) * (n : ℂ)) := by rw [h1, h2]
      _ = (L : ℂ) + ((-(n : ℤ) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
          push_cast
          ring
  rw [hexp_arg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one,
    ← Complex.ofReal_exp, hL, Real.exp_log ht]

/-- Norm of any decaying exponential at the guess: `‖e^{-sGuess(n)·c}‖ = e^{c·L/σ₁}` where
`L = log t(Yₙ)`. -/
theorem sGuess_exp_norm (P : MixParams) (hs1 : 0 < P.sig1) (n : ℕ) (c : ℝ) :
    ‖Complex.exp (-(sGuess P n * (c : ℂ)))‖ =
      Real.exp (c * Real.log (tRat P (2 * Real.pi * n / P.sig1)) / P.sig1) := by
  rw [norm_exp_neg_mul, sGuess_re]
  congr 1
  field_simp

/-- Every point of a closed disk has imaginary part at least `Im(centre) − radius`. -/
theorem mem_closedBall_im_ge {c k : ℂ} {r : ℝ} (hk : k ∈ Metric.closedBall c r) :
    c.im - r ≤ k.im := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hk
  have h1 : |(k - c).im| ≤ ‖k - c‖ := Complex.abs_im_le_norm _
  rw [Complex.sub_im] at h1
  have h2 := abs_le.mp (le_trans h1 hk)
  linarith [h2.1]

/-- The guess dominates its imaginary part: `Yₙ ≤ ‖sGuess n‖`. -/
theorem sGuess_norm_ge (P : MixParams) (hs1 : 0 < P.sig1) (n : ℕ) :
    2 * Real.pi * n / P.sig1 ≤ ‖sGuess P n‖ := by
  have h := Complex.abs_im_le_norm (sGuess P n)
  rw [sGuess_im] at h
  have hY0 : 0 ≤ 2 * Real.pi * n / P.sig1 := by positivity
  calc 2 * Real.pi * n / P.sig1 = |2 * Real.pi * n / P.sig1| := (abs_of_nonneg hY0).symm
    _ ≤ ‖sGuess P n‖ := h

/-- Norm cap for the guess under the log cap `40L ≤ σ₁Y`: `‖sGuess n‖ ≤ (41/40)·Yₙ`. -/
theorem sGuess_norm_le (P : MixParams) (hs1 : 0 < P.sig1) (n : ℕ)
    (h0L : 0 ≤ Real.log (tRat P (2 * Real.pi * n / P.sig1)))
    (hLcap : 40 * Real.log (tRat P (2 * Real.pi * n / P.sig1)) ≤
      P.sig1 * (2 * Real.pi * n / P.sig1)) :
    ‖sGuess P n‖ ≤ 41 / 40 * (2 * Real.pi * n / P.sig1) := by
  set L : ℝ := Real.log (tRat P (2 * Real.pi * n / P.sig1)) with hL
  set Y : ℝ := 2 * Real.pi * n / P.sig1 with hY
  have hY0 : 0 ≤ Y := by rw [hY]; positivity
  have h1 : ‖sGuess P n‖ ≤ |(sGuess P n).re| + |(sGuess P n).im| :=
    Complex.norm_le_abs_re_add_abs_im _
  rw [sGuess_re, sGuess_im, ← hL, ← hY] at h1
  have h2 : |(-L) / P.sig1| = L / P.sig1 := by
    rw [abs_div, abs_neg, abs_of_nonneg h0L, abs_of_pos hs1]
  have h3 : L / P.sig1 ≤ Y / 40 := by
    rw [div_le_div_iff₀ hs1 (by norm_num : (0 : ℝ) < 40)]
    linarith [hLcap]
  have h4 : |Y| = Y := abs_of_nonneg hY0
  rw [h2, h4] at h1
  linarith [h1, h3]

/-! ### Elementary power-difference bounds (two-point drift control, no MVT) -/

/-- `‖u⁶ − v⁶‖ ≤ 6M⁵‖u − v‖` for `‖u‖, ‖v‖ ≤ M`. -/
theorem pow_six_sub_norm_le (u v : ℂ) {M : ℝ} (hu : ‖u‖ ≤ M) (hv : ‖v‖ ≤ M) :
    ‖u ^ 6 - v ^ 6‖ ≤ 6 * M ^ 5 * ‖u - v‖ := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg u) hu
  have hfact : u ^ 6 - v ^ 6 =
      (u - v) * (u ^ 5 + u ^ 4 * v + u ^ 3 * v ^ 2 + u ^ 2 * v ^ 3 + u * v ^ 4 + v ^ 5) := by
    ring
  have hupow : ∀ i : ℕ, ‖u ^ i‖ ≤ M ^ i := fun i => by
    rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hu i
  have hvpow : ∀ i : ℕ, ‖v ^ i‖ ≤ M ^ i := fun i => by
    rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hv i
  have e0 := hupow 5
  have e1 : ‖u ^ 4 * v‖ ≤ M ^ 5 := by
    calc ‖u ^ 4 * v‖ ≤ M ^ 4 * M := norm_mul_le_bound (hupow 4) hv
      _ = M ^ 5 := by ring
  have e2 : ‖u ^ 3 * v ^ 2‖ ≤ M ^ 5 := by
    calc ‖u ^ 3 * v ^ 2‖ ≤ M ^ 3 * M ^ 2 := norm_mul_le_bound (hupow 3) (hvpow 2)
      _ = M ^ 5 := by ring
  have e3 : ‖u ^ 2 * v ^ 3‖ ≤ M ^ 5 := by
    calc ‖u ^ 2 * v ^ 3‖ ≤ M ^ 2 * M ^ 3 := norm_mul_le_bound (hupow 2) (hvpow 3)
      _ = M ^ 5 := by ring
  have e4 : ‖u * v ^ 4‖ ≤ M ^ 5 := by
    calc ‖u * v ^ 4‖ ≤ M * M ^ 4 := norm_mul_le_bound hu (hvpow 4)
      _ = M ^ 5 := by ring
  have e5 := hvpow 5
  have t1 := norm_add_le (u ^ 5 + u ^ 4 * v + u ^ 3 * v ^ 2 + u ^ 2 * v ^ 3 + u * v ^ 4)
    (v ^ 5)
  have t2 := norm_add_le (u ^ 5 + u ^ 4 * v + u ^ 3 * v ^ 2 + u ^ 2 * v ^ 3) (u * v ^ 4)
  have t3 := norm_add_le (u ^ 5 + u ^ 4 * v + u ^ 3 * v ^ 2) (u ^ 2 * v ^ 3)
  have t4 := norm_add_le (u ^ 5 + u ^ 4 * v) (u ^ 3 * v ^ 2)
  have t5 := norm_add_le (u ^ 5) (u ^ 4 * v)
  have hsum : ‖u ^ 5 + u ^ 4 * v + u ^ 3 * v ^ 2 + u ^ 2 * v ^ 3 + u * v ^ 4 + v ^ 5‖ ≤
      6 * M ^ 5 := by linarith [e0, e1, e2, e3, e4, e5, t1, t2, t3, t4, t5]
  calc ‖u ^ 6 - v ^ 6‖
      = ‖u - v‖ * ‖u ^ 5 + u ^ 4 * v + u ^ 3 * v ^ 2 + u ^ 2 * v ^ 3 + u * v ^ 4 + v ^ 5‖ := by
        rw [hfact, norm_mul]
    _ ≤ ‖u - v‖ * (6 * M ^ 5) := mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
    _ = 6 * M ^ 5 * ‖u - v‖ := by ring

/-- `‖u⁴ − v⁴‖ ≤ 4M³‖u − v‖` for `‖u‖, ‖v‖ ≤ M`. -/
theorem pow_four_sub_norm_le (u v : ℂ) {M : ℝ} (hu : ‖u‖ ≤ M) (hv : ‖v‖ ≤ M) :
    ‖u ^ 4 - v ^ 4‖ ≤ 4 * M ^ 3 * ‖u - v‖ := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg u) hu
  have hfact : u ^ 4 - v ^ 4 = (u - v) * (u ^ 3 + u ^ 2 * v + u * v ^ 2 + v ^ 3) := by ring
  have hupow : ∀ i : ℕ, ‖u ^ i‖ ≤ M ^ i := fun i => by
    rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hu i
  have hvpow : ∀ i : ℕ, ‖v ^ i‖ ≤ M ^ i := fun i => by
    rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hv i
  have e0 := hupow 3
  have e1 : ‖u ^ 2 * v‖ ≤ M ^ 3 := by
    calc ‖u ^ 2 * v‖ ≤ M ^ 2 * M := norm_mul_le_bound (hupow 2) hv
      _ = M ^ 3 := by ring
  have e2 : ‖u * v ^ 2‖ ≤ M ^ 3 := by
    calc ‖u * v ^ 2‖ ≤ M * M ^ 2 := norm_mul_le_bound hu (hvpow 2)
      _ = M ^ 3 := by ring
  have e3 := hvpow 3
  have t1 := norm_add_le (u ^ 3 + u ^ 2 * v + u * v ^ 2) (v ^ 3)
  have t2 := norm_add_le (u ^ 3 + u ^ 2 * v) (u * v ^ 2)
  have t3 := norm_add_le (u ^ 3) (u ^ 2 * v)
  have hsum : ‖u ^ 3 + u ^ 2 * v + u * v ^ 2 + v ^ 3‖ ≤ 4 * M ^ 3 := by
    linarith [e0, e1, e2, e3, t1, t2, t3]
  calc ‖u ^ 4 - v ^ 4‖
      = ‖u - v‖ * ‖u ^ 3 + u ^ 2 * v + u * v ^ 2 + v ^ 3‖ := by rw [hfact, norm_mul]
    _ ≤ ‖u - v‖ * (4 * M ^ 3) := mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
    _ = 4 * M ^ 3 * ‖u - v‖ := by ring

/-! ### Budget helpers for the residual estimate -/

/-- Generic budget step: a `C·Y⁵` term fits in a `(μ/2000)·t·Y⁴` budget once
`4000·C·(μ+K1) ≤ μY`, via the ratio lower envelope `t ≥ Y²/(2(μ+K1))`. -/
theorem budget_via_tlow {mu K1c Y t C : ℝ} (hmu : 0 < mu) (hK10 : 0 ≤ K1c) (hY0 : 0 < Y)
    (htlow : Y ^ 2 / (2 * (mu + K1c)) ≤ t)
    (hC : 4000 * C * (mu + K1c) ≤ mu * Y) :
    C * Y ^ 5 ≤ mu / 2000 * (t * Y ^ 4) := by
  have hA : 0 < mu + K1c := by linarith
  have h2 : mu / 2000 * (Y ^ 2 / (2 * (mu + K1c)) * Y ^ 4) ≤ mu / 2000 * (t * Y ^ 4) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact mul_le_mul_of_nonneg_right htlow (by positivity)
  refine le_trans ?_ h2
  rw [show mu / 2000 * (Y ^ 2 / (2 * (mu + K1c)) * Y ^ 4) =
    mu * Y ^ 6 / (4000 * (mu + K1c)) by field_simp; ring]
  rw [le_div_iff₀ (by positivity)]
  calc C * Y ^ 5 * (4000 * (mu + K1c)) = 4000 * C * (mu + K1c) * Y ^ 5 := by ring
    _ ≤ mu * Y * Y ^ 5 := mul_le_mul_of_nonneg_right hC (by positivity)
    _ = mu * Y ^ 6 := by ring

/-- Splitting the exponential ratio: `e^{σ₀L/σ₁}·e^{((σ₁−σ₀)/σ₁)L} = e^L`. -/
theorem exp_ratio_split {sg0 sg1 L : ℝ} (hs1 : sg1 ≠ 0) :
    Real.exp (sg0 * L / sg1) * Real.exp ((sg1 - sg0) / sg1 * L) = Real.exp L := by
  rw [← Real.exp_add]
  congr 1
  field_simp
  ring

/-- **Two-point drift for `McNum`** (crude, no MVT): the leading powers move by
`6M⁵‖u−v‖` and both remainders are `≤ KMc·M⁵`. -/
theorem McNum_two_point_le (P : MixParams) (hP : P.Phys) {M : ℝ} (hM : 1 ≤ M)
    {u v : ℂ} (hu : ‖u‖ ≤ M) (hv : ‖v‖ ≤ M) :
    ‖McNum P u - McNum P v‖ ≤ 6 * M ^ 5 * ‖u - v‖ + 2 * P.KMc * M ^ 5 := by
  have hdec : McNum P u - McNum P v =
      (u ^ 6 - v ^ 6) + (McNum P u - u ^ 6) - (McNum P v - v ^ 6) := by ring
  rw [hdec]
  refine le_trans (norm_add_add_sub_le _ _ _) ?_
  have h1 := pow_six_sub_norm_le u v hu hv
  have h2 := McNum_sub_norm_le P hP hM hu
  have h3 := McNum_sub_norm_le P hP hM hv
  linarith

/-- **Two-point drift for `M1Num`**: `μ·4M³‖u−v‖` from the leading power plus `2K1·M³`. -/
theorem M1Num_two_point_le (P : MixParams) (hP : P.Phys) {M : ℝ} (hM : 1 ≤ M)
    {u v : ℂ} (hu : ‖u‖ ≤ M) (hv : ‖v‖ ≤ M) :
    ‖M1Num P u - M1Num P v‖ ≤ P.mu * (4 * M ^ 3 * ‖u - v‖) + 2 * P.K1 * M ^ 3 := by
  have hmu0 : 0 ≤ P.mu := by
    obtain ⟨_, _, hrr, hqp, _⟩ := hP
    exact mul_nonneg (hrr 1 1).le (hqp 1 1).le
  have hdec : M1Num P u - M1Num P v =
      ((P.mu : ℝ) : ℂ) * (u ^ 4 - v ^ 4) + (M1Num P u - ((P.mu : ℝ) : ℂ) * u ^ 4) -
        (M1Num P v - ((P.mu : ℝ) : ℂ) * v ^ 4) := by ring
  rw [hdec]
  refine le_trans (norm_add_add_sub_le _ _ _) ?_
  have h1 : ‖((P.mu : ℝ) : ℂ) * (u ^ 4 - v ^ 4)‖ ≤ P.mu * (4 * M ^ 3 * ‖u - v‖) := by
    rw [norm_real_mul hmu0]
    exact mul_le_mul_of_nonneg_left (pow_four_sub_norm_le u v hu hv) hmu0
  have h2 := M1Num_sub_norm_le P hP hM hu
  have h3 := M1Num_sub_norm_le P hP hM hv
  linarith

/-- `K0` is nonnegative for physical parameters. -/
theorem K0_nonneg (P : MixParams) (hP : P.Phys) : 0 ≤ P.K0 := by
  obtain ⟨hsg0, hsg01, hrr, hqp, hqpp⟩ := hP
  have hsg1' : 0 ≤ P.sig1 := by linarith [hsg0.le]
  have hcB2 := cB_nonneg (hqp 1 1).le (hqpp 1 1).le hsg1'
  have hcB4 := cB_nonneg (hqp 1 0).le (hqpp 1 0).le hsg1'
  have h1 := (hrr 0 0).le; have h2 := (hrr 1 1).le
  have h3 := (hrr 0 1).le; have h4 := (hrr 1 0).le
  have h5 := (hqp 0 0).le; have h6 := (hqpp 0 0).le
  have h7 := (hqp 0 1).le; have h8 := (hqpp 0 1).le
  unfold MixParams.K0
  positivity

/-- `K01` is nonnegative for physical parameters. -/
theorem K01_nonneg (P : MixParams) (hP : P.Phys) : 0 ≤ P.K01 := by
  obtain ⟨hsg0, hsg01, hrr, hqp, hqpp⟩ := hP
  have h1 := (hrr 0 0).le; have h2 := (hrr 1 1).le
  have h3 := (hrr 0 1).le; have h4 := (hrr 1 0).le
  have h5 := (hqp 0 0).le; have h6 := (hqpp 0 0).le
  have h7 := (hqp 0 1).le; have h8 := (hqpp 0 1).le
  have h9 := (hqp 1 1).le; have h10 := (hqpp 1 1).le
  have h11 := (hqp 1 0).le; have h12 := (hqpp 1 0).le
  unfold MixParams.K01
  positivity

set_option maxHeartbeats 1600000 in
/-- **The chord-step residual at the guess**: after the exact phase kill, the five pieces
(anchor residual, `Mc`/`M₁` drifts over the log-lift, and the `e^{-sσ₀}`/`e^{-s(σ₀+σ₁)}`
perturbations) each fit in a `(μ/2000)·t·Y⁴` budget, so `‖W(sGuess n)‖ ≤ (μ/200)·t·Y⁴`. -/
theorem Wfun_at_sGuess_le (P : MixParams) (hP : P.Phys) (n : ℕ) {Y : ℝ}
    (hYdef : Y = 2 * Real.pi * n / P.sig1)
    (h1 : 1 ≤ Y) (hMc2 : 2 * P.KMc ≤ Y) (hM12 : 2 * P.K1 ≤ P.mu * Y)
    (hre : P.KIm ≤ P.mu * Y) (ht1 : 2 * (P.mu + P.K1) ≤ Y)
    (hLcap : 40 * Real.log (tRat P Y) ≤ P.sig1 * Y)
    (hT0 : 16000 * P.KIm * (P.mu + P.K1) ≤ P.mu ^ 2 * Y)
    (hT1 : 12000 * P.KMc * (P.mu + P.K1) ≤ P.mu * Y)
    (hT2 : 9600 * P.K1 ≤ P.mu * Y)
    (hL2 : 32000 * (P.mu + P.K1) * Real.log (tRat P Y) ≤ P.sig1 * P.mu * Y)
    (hL3 : 18800 * Real.log (tRat P Y) ≤ P.sig1 * Y)
    (hE0 : 2500 * P.K0 ≤ P.mu *
      Real.exp ((P.sig1 - P.sig0) / P.sig1 * Real.log (tRat P Y)))
    (hE01 : 16000 * P.K01 ≤ P.mu ^ 2 *
      Real.exp ((P.sig1 - P.sig0) / P.sig1 * Real.log (tRat P Y))) :
    ‖Wfun P (sGuess P n)‖ ≤ P.mu / 200 * (tRat P Y * Y ^ 4) := by
  have hs0 : 0 < P.sig0 := hP.1
  have hs1 : 0 < P.sig1 := lt_trans hP.1 hP.2.1
  have hmu : 0 < P.mu := mul_pos (hP.2.2.1 1 1) (hP.2.2.2.1 1 1)
  have hK10 := K1_nonneg P hP
  have hKMc0 := KMc_nonneg P hP
  have hK00 := K0_nonneg P hP
  have hK010 := K01_nonneg P hP
  have hY0 : (0 : ℝ) < Y := lt_of_lt_of_le one_pos h1
  set t : ℝ := tRat P Y with htdef
  set L : ℝ := Real.log t with hLdef
  have hA : 0 < P.mu + P.K1 := by linarith
  have htlow : Y ^ 2 / (2 * (P.mu + P.K1)) ≤ t := tRat_lower P hP h1 hMc2 hM12
  have htup : t ≤ 4 / P.mu * Y ^ 2 :=
    tRat_upper P hP h1 (by linarith [hKMc0]) hM12
  have ht1' : 1 ≤ t := by
    have hYsq : Y ≤ Y ^ 2 := by nlinarith
    have h2A : 2 * (P.mu + P.K1) ≤ Y ^ 2 := by linarith
    have : 1 ≤ Y ^ 2 / (2 * (P.mu + P.K1)) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    linarith [htlow]
  have htpos : 0 < t := lt_of_lt_of_le one_pos ht1'
  have h0L : 0 ≤ L := by rw [hLdef]; exact Real.log_nonneg ht1'
  -- phase kill and geometry
  have hPK : Complex.exp (-(sGuess P n * (P.sig1 : ℂ))) = ((t : ℝ) : ℂ) := by
    have h := exp_at_sGuess P hs1 n (by rw [← hYdef]; exact htpos)
    rw [← hYdef] at h
    exact h
  have hgeq : sGuess P n = ((-L / P.sig1 : ℝ) : ℂ) + aI Y := by
    rw [hLdef, htdef, hYdef]
    rfl
  have hganorm : ‖sGuess P n - aI Y‖ = L / P.sig1 := by
    rw [show sGuess P n - aI Y = ((-L / P.sig1 : ℝ) : ℂ) by rw [hgeq]; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_div, abs_neg, abs_of_nonneg h0L,
      abs_of_pos hs1]
  have hL0 : 0 ≤ L / P.sig1 := by positivity
  have hgle : ‖sGuess P n‖ ≤ 21 / 20 * Y := by
    have h := sGuess_norm_le P hs1 n (by rw [← hYdef, ← htdef, ← hLdef]; exact h0L)
      (by rw [← hYdef, ← htdef, ← hLdef]; exact hLcap)
    rw [← hYdef] at h
    nlinarith [h, hY0.le]
  have haIle : ‖aI Y‖ ≤ 21 / 20 * Y := by rw [aI_norm hY0.le]; linarith
  have hM21 : (1 : ℝ) ≤ 21 / 20 * Y := by linarith
  have hpow5 : (21 / 20 * Y) ^ 5 ≤ 4 / 3 * Y ^ 5 := by nlinarith [pow_nonneg hY0.le 5]
  have hpow4 : (21 / 20 * Y) ^ 4 ≤ 5 / 4 * Y ^ 4 := by nlinarith [pow_nonneg hY0.le 4]
  have hpow3 : (21 / 20 * Y) ^ 3 ≤ 7 / 6 * Y ^ 3 := by nlinarith [pow_nonneg hY0.le 3]
  have hpow2 : (21 / 20 * Y) ^ 2 ≤ 2 * Y ^ 2 := by nlinarith [pow_nonneg hY0.le 2]
  -- piece 0: the anchor residual
  have hp0 : ‖McNum P (aI Y) + ((t : ℝ) : ℂ) * M1Num P (aI Y)‖ ≤
      4 * P.KIm / P.mu * Y ^ 5 := by
    have h := anchor_residual_le P hP h1 hM12 hre
    rw [← htdef] at h
    exact h
  have hb0 : 4 * P.KIm / P.mu * Y ^ 5 ≤ P.mu / 2000 * (t * Y ^ 4) := by
    refine budget_via_tlow hmu hK10 hY0 htlow ?_
    rw [show 4000 * (4 * P.KIm / P.mu) * (P.mu + P.K1) =
      16000 * P.KIm * (P.mu + P.K1) / P.mu by ring, div_le_iff₀ hmu]
    calc 16000 * P.KIm * (P.mu + P.K1) ≤ P.mu ^ 2 * Y := hT0
      _ = P.mu * Y * P.mu := by ring
  -- piece 1: the `Mc` drift
  have hp1 : ‖McNum P (sGuess P n) - McNum P (aI Y)‖ ≤
      8 * L / P.sig1 * Y ^ 5 + 3 * P.KMc * Y ^ 5 := by
    have h := McNum_two_point_le P hP hM21 hgle haIle
    rw [hganorm] at h
    have e1 : 6 * (21 / 20 * Y) ^ 5 * (L / P.sig1) ≤ 8 * L / P.sig1 * Y ^ 5 := by
      have h6 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow5 hL0)
        (by norm_num : (0 : ℝ) ≤ 6)
      calc 6 * (21 / 20 * Y) ^ 5 * (L / P.sig1)
          = 6 * ((21 / 20 * Y) ^ 5 * (L / P.sig1)) := by ring
        _ ≤ 6 * (4 / 3 * Y ^ 5 * (L / P.sig1)) := h6
        _ = 8 * L / P.sig1 * Y ^ 5 := by ring
    have e2 : 2 * P.KMc * (21 / 20 * Y) ^ 5 ≤ 3 * P.KMc * Y ^ 5 := by
      nlinarith [mul_le_mul_of_nonneg_left hpow5 hKMc0, mul_nonneg hKMc0 (pow_nonneg hY0.le 5)]
    linarith [h, e1, e2]
  have hb1a : 8 * L / P.sig1 * Y ^ 5 ≤ P.mu / 2000 * (t * Y ^ 4) := by
    refine budget_via_tlow hmu hK10 hY0 htlow ?_
    rw [show 4000 * (8 * L / P.sig1) * (P.mu + P.K1) =
      32000 * (P.mu + P.K1) * L / P.sig1 by ring, div_le_iff₀ hs1]
    linarith [hL2]
  have hb1b : 3 * P.KMc * Y ^ 5 ≤ P.mu / 2000 * (t * Y ^ 4) := by
    refine budget_via_tlow hmu hK10 hY0 htlow ?_
    rw [show 4000 * (3 * P.KMc) * (P.mu + P.K1) =
      12000 * P.KMc * (P.mu + P.K1) by ring]
    exact hT1
  -- piece 2: the `M₁` drift (carries the exact `t` from the phase kill)
  have hp2 : ‖((t : ℝ) : ℂ) * (M1Num P (sGuess P n) - M1Num P (aI Y))‖ ≤
      t * ((P.mu * (14 / 3 * (L / P.sig1)) + 7 / 3 * P.K1) * Y ^ 3) := by
    rw [norm_real_mul htpos.le]
    refine mul_le_mul_of_nonneg_left ?_ htpos.le
    have h := M1Num_two_point_le P hP hM21 hgle haIle
    rw [hganorm] at h
    have e1 : P.mu * (4 * (21 / 20 * Y) ^ 3 * (L / P.sig1)) ≤
        P.mu * (14 / 3 * (L / P.sig1)) * Y ^ 3 := by
      have h3L := mul_le_mul_of_nonneg_right hpow3 hL0
      nlinarith [mul_le_mul_of_nonneg_left h3L hmu.le]
    have e2 : 2 * P.K1 * (21 / 20 * Y) ^ 3 ≤ 7 / 3 * P.K1 * Y ^ 3 := by
      nlinarith [mul_le_mul_of_nonneg_left hpow3 hK10,
        mul_nonneg hK10 (pow_nonneg hY0.le 3)]
    linarith [h, e1, e2]
  have hb2 : t * ((P.mu * (14 / 3 * (L / P.sig1)) + 7 / 3 * P.K1) * Y ^ 3) ≤
      2 * (P.mu / 2000 * (t * Y ^ 4)) := by
    have c1 : P.mu * (14 / 3 * (L / P.sig1)) ≤ P.mu / 2000 * Y := by
      have hLs : L / P.sig1 ≤ Y / 18800 := by
        rw [div_le_div_iff₀ hs1 (by norm_num)]
        linarith [hL3]
      nlinarith [mul_le_mul_of_nonneg_left hLs hmu.le, mul_nonneg hmu.le hY0.le]
    have c2 : 7 / 3 * P.K1 ≤ P.mu / 2000 * Y := by linarith [hT2]
    have c3 : (P.mu * (14 / 3 * (L / P.sig1)) + 7 / 3 * P.K1) * Y ^ 3 ≤
        2 * (P.mu / 2000) * Y * Y ^ 3 := by
      nlinarith [mul_le_mul_of_nonneg_right (add_le_add c1 c2) (pow_nonneg hY0.le 3)]
    calc t * ((P.mu * (14 / 3 * (L / P.sig1)) + 7 / 3 * P.K1) * Y ^ 3)
        ≤ t * (2 * (P.mu / 2000) * Y * Y ^ 3) := mul_le_mul_of_nonneg_left c3 htpos.le
      _ = 2 * (P.mu / 2000 * (t * Y ^ 4)) := by ring
  -- piece 3: the `e^{-sσ₀}` perturbation
  have hE0norm : ‖Complex.exp (-(sGuess P n * (P.sig0 : ℂ)))‖ =
      Real.exp (P.sig0 * L / P.sig1) := by
    have h := sGuess_exp_norm P hs1 n P.sig0
    rw [← hYdef, ← htdef, ← hLdef] at h
    exact h
  have hp3 : ‖M0Num P (sGuess P n) * Complex.exp (-(sGuess P n * (P.sig0 : ℂ)))‖ ≤
      5 / 4 * P.K0 * Y ^ 4 * Real.exp (P.sig0 * L / P.sig1) := by
    rw [norm_mul, hE0norm]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    have h := M0Num_norm_le P hP hM21 hgle
    nlinarith [h, mul_le_mul_of_nonneg_left hpow4 hK00]
  have hb3 : 5 / 4 * P.K0 * Y ^ 4 * Real.exp (P.sig0 * L / P.sig1) ≤
      P.mu / 2000 * (t * Y ^ 4) := by
    have hsplit : Real.exp (P.sig0 * L / P.sig1) *
        Real.exp ((P.sig1 - P.sig0) / P.sig1 * L) = t := by
      rw [exp_ratio_split hs1.ne', hLdef, Real.exp_log htpos]
    calc 5 / 4 * P.K0 * Y ^ 4 * Real.exp (P.sig0 * L / P.sig1)
        = (5 / 4 * P.K0) * (Real.exp (P.sig0 * L / P.sig1) * Y ^ 4) := by ring
      _ ≤ (P.mu / 2000 * Real.exp ((P.sig1 - P.sig0) / P.sig1 * L)) *
          (Real.exp (P.sig0 * L / P.sig1) * Y ^ 4) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          linarith [hE0]
      _ = P.mu / 2000 * ((Real.exp (P.sig0 * L / P.sig1) *
          Real.exp ((P.sig1 - P.sig0) / P.sig1 * L)) * Y ^ 4) := by ring
      _ = P.mu / 2000 * (t * Y ^ 4) := by rw [hsplit]
  -- piece 4: the `e^{-s(σ₀+σ₁)}` perturbation
  have hE01norm : ‖Complex.exp (-(sGuess P n * ((P.sig0 + P.sig1 : ℝ) : ℂ)))‖ =
      Real.exp ((P.sig0 + P.sig1) * L / P.sig1) := by
    have h := sGuess_exp_norm P hs1 n (P.sig0 + P.sig1)
    rw [← hYdef, ← htdef, ← hLdef] at h
    exact h
  have hp4 : ‖M01Num P (sGuess P n) *
      Complex.exp (-(sGuess P n * ((P.sig0 + P.sig1 : ℝ) : ℂ)))‖ ≤
      2 * P.K01 * Y ^ 2 * Real.exp ((P.sig0 + P.sig1) * L / P.sig1) := by
    rw [norm_mul, hE01norm]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    have h := M01Num_norm_le P hP hM21 hgle
    nlinarith [h, mul_le_mul_of_nonneg_left hpow2 hK010]
  have hb4 : 2 * P.K01 * Y ^ 2 * Real.exp ((P.sig0 + P.sig1) * L / P.sig1) ≤
      P.mu / 2000 * (t * Y ^ 4) := by
    have hexpL : Real.exp L = t := by rw [hLdef]; exact Real.exp_log htpos
    have hsplit2 : Real.exp ((P.sig0 + P.sig1) * L / P.sig1) =
        t * Real.exp (P.sig0 * L / P.sig1) := by
      rw [← hexpL, ← Real.exp_add]
      congr 1
      field_simp
      ring
    have hsplit : Real.exp (P.sig0 * L / P.sig1) *
        Real.exp ((P.sig1 - P.sig0) / P.sig1 * L) = t := by
      rw [exp_ratio_split hs1.ne', hLdef, Real.exp_log htpos]
    set X : ℝ := Real.exp (P.sig0 * L / P.sig1) with hXdef
    set E : ℝ := Real.exp ((P.sig1 - P.sig0) / P.sig1 * L) with hEdef
    have hXpos : 0 < X := Real.exp_pos _
    have hEpos : 0 < E := Real.exp_pos _
    rw [hsplit2]
    -- goal: 2K01·Y²·(t·X) ≤ (μ/2000)(t·Y⁴); reduce along X·E = t
    have hgoal : 2 * P.K01 * X ≤ P.mu / 2000 * Y ^ 2 := by
      refine le_of_mul_le_mul_right ?_ hEpos
      have hXE : X * E = t := hsplit
      have hup : 2 * P.K01 * t ≤ 8 * P.K01 / P.mu * Y ^ 2 := by
        have hh := mul_le_mul_of_nonneg_left htup
          (by positivity : (0 : ℝ) ≤ 2 * P.K01)
        calc 2 * P.K01 * t ≤ 2 * P.K01 * (4 / P.mu * Y ^ 2) := hh
          _ = 8 * P.K01 / P.mu * Y ^ 2 := by ring
      have hlo : 8 * P.K01 / P.mu * Y ^ 2 ≤ P.mu / 2000 * Y ^ 2 * E := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hmu]
        have hh := mul_le_mul_of_nonneg_right hE01 (by positivity : (0 : ℝ) ≤ Y ^ 2)
        linarith [hh]
      calc 2 * P.K01 * X * E = 2 * P.K01 * (X * E) := by ring
        _ = 2 * P.K01 * t := by rw [hXE]
        _ ≤ 8 * P.K01 / P.mu * Y ^ 2 := hup
        _ ≤ P.mu / 2000 * Y ^ 2 * E := hlo
    calc 2 * P.K01 * Y ^ 2 * (t * X) = (2 * P.K01 * X) * (t * Y ^ 2) := by ring
      _ ≤ (P.mu / 2000 * Y ^ 2) * (t * Y ^ 2) := by
          refine mul_le_mul_of_nonneg_right hgoal ?_
          positivity
      _ = P.mu / 2000 * (t * Y ^ 4) := by ring
  -- assemble the five pieces
  have hdecomp : Wfun P (sGuess P n) =
      (McNum P (aI Y) + ((t : ℝ) : ℂ) * M1Num P (aI Y)) +
        (McNum P (sGuess P n) - McNum P (aI Y)) +
        ((t : ℝ) : ℂ) * (M1Num P (sGuess P n) - M1Num P (aI Y)) +
        M0Num P (sGuess P n) * Complex.exp (-(sGuess P n * (P.sig0 : ℂ))) +
        M01Num P (sGuess P n) *
          Complex.exp (-(sGuess P n * ((P.sig0 + P.sig1 : ℝ) : ℂ))) := by
    unfold Wfun
    rw [hPK]
    ring
  rw [hdecomp]
  have t1 := norm_add_le
    ((McNum P (aI Y) + ((t : ℝ) : ℂ) * M1Num P (aI Y)) +
      (McNum P (sGuess P n) - McNum P (aI Y)) +
      ((t : ℝ) : ℂ) * (M1Num P (sGuess P n) - M1Num P (aI Y)) +
      M0Num P (sGuess P n) * Complex.exp (-(sGuess P n * (P.sig0 : ℂ))))
    (M01Num P (sGuess P n) * Complex.exp (-(sGuess P n * ((P.sig0 + P.sig1 : ℝ) : ℂ))))
  have t2 := norm_add_le
    ((McNum P (aI Y) + ((t : ℝ) : ℂ) * M1Num P (aI Y)) +
      (McNum P (sGuess P n) - McNum P (aI Y)) +
      ((t : ℝ) : ℂ) * (M1Num P (sGuess P n) - M1Num P (aI Y)))
    (M0Num P (sGuess P n) * Complex.exp (-(sGuess P n * (P.sig0 : ℂ))))
  have t3 := norm_add_le
    ((McNum P (aI Y) + ((t : ℝ) : ℂ) * M1Num P (aI Y)) +
      (McNum P (sGuess P n) - McNum P (aI Y)))
    (((t : ℝ) : ℂ) * (M1Num P (sGuess P n) - M1Num P (aI Y)))
  have t4 := norm_add_le (McNum P (aI Y) + ((t : ℝ) : ℂ) * M1Num P (aI Y))
    (McNum P (sGuess P n) - McNum P (aI Y))
  have hfinal : (0 : ℝ) ≤ P.mu / 2000 * (t * Y ^ 4) := by positivity
  linarith [t1, t2, t3, t4, hp0, hb0, hp1, hb1a, hb1b, hp2, hb2, hp3, hb3, hp4, hb4,
    hfinal]

/-- Generic budget step (weighted form): `C·Y⁵ ≤ D·t·Y⁴` once `2CA ≤ DY`, via
`t ≥ Y²/(2A)`. -/
theorem budget_gen {A Y t C D : ℝ} (hA : 0 < A) (hY0 : 0 < Y) (hD : 0 ≤ D)
    (htlow : Y ^ 2 / (2 * A) ≤ t) (hC : 2 * C * A ≤ D * Y) :
    C * Y ^ 5 ≤ D * (t * Y ^ 4) := by
  have h2 : D * (Y ^ 2 / (2 * A) * Y ^ 4) ≤ D * (t * Y ^ 4) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right htlow (by positivity)) hD
  refine le_trans ?_ h2
  rw [show D * (Y ^ 2 / (2 * A) * Y ^ 4) = D * Y ^ 6 / (2 * A) by field_simp]
  rw [le_div_iff₀ (by positivity)]
  calc C * Y ^ 5 * (2 * A) = 2 * C * A * Y ^ 5 := by ring
    _ ≤ D * Y * Y ^ 5 := mul_le_mul_of_nonneg_right hC (by positivity)
    _ = D * Y ^ 6 := by ring

/-- `KMcD` is nonnegative for physical parameters. -/
theorem KMcD_nonneg (P : MixParams) (hP : P.Phys) : 0 ≤ P.KMcD := by
  obtain ⟨hsg0, hsg01, hrr, hqp, hqpp⟩ := hP
  have hsg0' : 0 ≤ P.sig0 := hsg0.le
  have hsg1' : 0 ≤ P.sig1 := by linarith
  have h1 := cBD_nonneg (hqp 0 0).le (hqpp 0 0).le hsg0'
  have h2 := cB_nonneg (hqp 1 1).le (hqpp 1 1).le hsg1'
  have h3 := cB_nonneg (hqp 0 0).le (hqpp 0 0).le hsg0'
  have h4 := cBD_nonneg (hqp 1 1).le (hqpp 1 1).le hsg1'
  have h5 := cBD_nonneg (hqp 0 1).le (hqpp 0 1).le hsg0'
  have h6 := cB_nonneg (hqp 1 0).le (hqpp 1 0).le hsg1'
  have h7 := cB_nonneg (hqp 0 1).le (hqpp 0 1).le hsg0'
  have h8 := cBD_nonneg (hqp 1 0).le (hqpp 1 0).le hsg1'
  have e1 := (hrr 0 0).le; have e2 := (hrr 1 1).le
  have e3 := (hrr 0 1).le; have e4 := (hrr 1 0).le
  unfold MixParams.KMcD
  positivity

/-- `K1D` is nonnegative for physical parameters. -/
theorem K1D_nonneg (P : MixParams) (hP : P.Phys) : 0 ≤ P.K1D := by
  obtain ⟨hsg0, hsg01, hrr, hqp, hqpp⟩ := hP
  have hsg0' : 0 ≤ P.sig0 := hsg0.le
  have h1 := cBD_nonneg (hqp 0 0).le (hqpp 0 0).le hsg0'
  have h3 := cB_nonneg (hqp 0 0).le (hqpp 0 0).le hsg0'
  have h5 := cBD_nonneg (hqp 0 1).le (hqpp 0 1).le hsg0'
  have h7 := cB_nonneg (hqp 0 1).le (hqpp 0 1).le hsg0'
  have e1 := (hrr 0 0).le; have e2 := (hrr 1 1).le
  have e3 := (hrr 0 1).le; have e4 := (hrr 1 0).le
  have e5 := (hqp 1 1).le; have e6 := (hqpp 1 1).le
  have e7 := (hqp 1 0).le; have e8 := (hqpp 1 0).le
  unfold MixParams.K1D
  positivity

/-- `K0D` is nonnegative for physical parameters. -/
theorem K0D_nonneg (P : MixParams) (hP : P.Phys) : 0 ≤ P.K0D := by
  obtain ⟨hsg0, hsg01, hrr, hqp, hqpp⟩ := hP
  have hsg1' : 0 ≤ P.sig1 := by linarith [hsg0.le]
  have h2 := cB_nonneg (hqp 1 1).le (hqpp 1 1).le hsg1'
  have h4 := cBD_nonneg (hqp 1 1).le (hqpp 1 1).le hsg1'
  have h6 := cB_nonneg (hqp 1 0).le (hqpp 1 0).le hsg1'
  have h8 := cBD_nonneg (hqp 1 0).le (hqpp 1 0).le hsg1'
  have e1 := (hrr 0 0).le; have e2 := (hrr 1 1).le
  have e3 := (hrr 0 1).le; have e4 := (hrr 1 0).le
  have e5 := (hqp 0 0).le; have e6 := (hqpp 0 0).le
  have e7 := (hqp 0 1).le; have e8 := (hqpp 0 1).le
  unfold MixParams.K0D
  positivity

/-- `K01D` is nonnegative for physical parameters. -/
theorem K01D_nonneg (P : MixParams) (hP : P.Phys) : 0 ≤ P.K01D := by
  obtain ⟨hsg0, hsg01, hrr, hqp, hqpp⟩ := hP
  have e1 := (hrr 0 0).le; have e2 := (hrr 1 1).le
  have e3 := (hrr 0 1).le; have e4 := (hrr 1 0).le
  have e5 := (hqp 0 0).le; have e6 := (hqpp 0 0).le
  have e7 := (hqp 0 1).le; have e8 := (hqpp 0 1).le
  have e9 := (hqp 1 1).le; have e10 := (hqpp 1 1).le
  have e11 := (hqp 1 0).le; have e12 := (hqpp 1 0).le
  unfold MixParams.K01D
  positivity

/-- Reverse triangle inequality in the `a + b` shape: `‖a‖ − ‖b‖ ≤ ‖a + b‖`. -/
theorem norm_add_lower (a b : ℂ) : ‖a‖ - ‖b‖ ≤ ‖a + b‖ := by
  have h : ‖a‖ ≤ ‖a + b‖ + ‖b‖ := by
    calc ‖a‖ = ‖(a + b) - b‖ := by congr 1; ring
      _ ≤ ‖a + b‖ + ‖b‖ := norm_sub_le _ _
  linarith

set_option maxHeartbeats 2000000 in
/-- **Frozen-derivative lower bound at the guess**: the dominant `−σ₁M₁(g)·t` term of
`W′(sGuess n)` beats the polynomial and `e^{-sσ₀}`-type corrections, giving
`‖W′(g)‖ ≥ (7/10)·σ₁μ·t·Y⁴`. -/
theorem WD_at_sGuess_lower (P : MixParams) (hP : P.Phys) (n : ℕ) {Y : ℝ}
    (hYdef : Y = 2 * Real.pi * n / P.sig1)
    (h1 : 1 ≤ Y) (hMc2 : 2 * P.KMc ≤ Y) (hM12 : 2 * P.K1 ≤ P.mu * Y)
    (ht1 : 2 * (P.mu + P.K1) ≤ Y)
    (hLcap : 40 * Real.log (tRat P Y) ≤ P.sig1 * Y)
    (hD1 : 12 * P.K1 ≤ P.mu * Y)
    (hD2 : 54 * P.KMcD * (P.mu + P.K1) ≤ P.sig1 * P.mu * Y)
    (hD3 : 30 * P.K0D + 25 * P.sig0 * P.K0 ≤ P.sig1 * P.mu *
      Real.exp ((P.sig1 - P.sig0) / P.sig1 * Real.log (tRat P Y)))
    (hD4 : 24 * P.K1D ≤ P.sig1 * P.mu * Y)
    (hD5 : 88 * P.K01D + 160 * (P.sig0 + P.sig1) * P.K01 ≤ P.sig1 * P.mu ^ 2 *
      Real.exp ((P.sig1 - P.sig0) / P.sig1 * Real.log (tRat P Y))) :
    7 / 10 * (P.sig1 * P.mu * (tRat P Y * Y ^ 4)) ≤ ‖WD P (sGuess P n)‖ := by
  have hs0 : 0 < P.sig0 := hP.1
  have hs1 : 0 < P.sig1 := lt_trans hP.1 hP.2.1
  have hmu : 0 < P.mu := mul_pos (hP.2.2.1 1 1) (hP.2.2.2.1 1 1)
  have hK10 := K1_nonneg P hP
  have hKMc0 := KMc_nonneg P hP
  have hK00 := K0_nonneg P hP
  have hK010 := K01_nonneg P hP
  have hKMcD0 := KMcD_nonneg P hP
  have hK1D0 := K1D_nonneg P hP
  have hK0D0 := K0D_nonneg P hP
  have hK01D0 := K01D_nonneg P hP
  have hY0 : (0 : ℝ) < Y := lt_of_lt_of_le one_pos h1
  set t : ℝ := tRat P Y with htdef
  set L : ℝ := Real.log t with hLdef
  have hA : 0 < P.mu + P.K1 := by linarith
  have htlow : Y ^ 2 / (2 * (P.mu + P.K1)) ≤ t := tRat_lower P hP h1 hMc2 hM12
  have htup : t ≤ 4 / P.mu * Y ^ 2 :=
    tRat_upper P hP h1 (by linarith [hKMc0]) hM12
  have ht1' : 1 ≤ t := by
    have hYsq : Y ≤ Y ^ 2 := by nlinarith
    have h2A : 2 * (P.mu + P.K1) ≤ Y ^ 2 := by linarith
    have : 1 ≤ Y ^ 2 / (2 * (P.mu + P.K1)) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    linarith [htlow]
  have htpos : 0 < t := lt_of_lt_of_le one_pos ht1'
  have h0L : 0 ≤ L := by rw [hLdef]; exact Real.log_nonneg ht1'
  have hPK : Complex.exp (-(sGuess P n * (P.sig1 : ℂ))) = ((t : ℝ) : ℂ) := by
    have h := exp_at_sGuess P hs1 n (by rw [← hYdef]; exact htpos)
    rw [← hYdef] at h
    exact h
  have hgle : ‖sGuess P n‖ ≤ 21 / 20 * Y := by
    have h := sGuess_norm_le P hs1 n (by rw [← hYdef, ← htdef, ← hLdef]; exact h0L)
      (by rw [← hYdef, ← htdef, ← hLdef]; exact hLcap)
    rw [← hYdef] at h
    nlinarith [h, hY0.le]
  have hgge : Y ≤ ‖sGuess P n‖ := by
    have h := sGuess_norm_ge P hs1 n
    rw [← hYdef] at h
    exact h
  have hM21 : (1 : ℝ) ≤ 21 / 20 * Y := by linarith
  have hpow4 : (21 / 20 * Y) ^ 4 ≤ 5 / 4 * Y ^ 4 := by nlinarith [pow_nonneg hY0.le 4]
  have hpow3 : (21 / 20 * Y) ^ 3 ≤ 7 / 6 * Y ^ 3 := by nlinarith [pow_nonneg hY0.le 3]
  have hpow2 : (21 / 20 * Y) ^ 2 ≤ 2 * Y ^ 2 := by nlinarith [pow_nonneg hY0.le 2]
  have hpow5 : (21 / 20 * Y) ^ 5 ≤ 4 / 3 * Y ^ 5 := by nlinarith [pow_nonneg hY0.le 5]
  have hE0norm : ‖Complex.exp (-(sGuess P n * (P.sig0 : ℂ)))‖ =
      Real.exp (P.sig0 * L / P.sig1) := by
    have h := sGuess_exp_norm P hs1 n P.sig0
    rw [← hYdef, ← htdef, ← hLdef] at h
    exact h
  have hE01norm : ‖Complex.exp (-(sGuess P n * ((P.sig0 + P.sig1 : ℝ) : ℂ)))‖ =
      Real.exp ((P.sig0 + P.sig1) * L / P.sig1) := by
    have h := sGuess_exp_norm P hs1 n (P.sig0 + P.sig1)
    rw [← hYdef, ← htdef, ← hLdef] at h
    exact h
  have hexpL : Real.exp L = t := by rw [hLdef]; exact Real.exp_log htpos
  have hsplit : Real.exp (P.sig0 * L / P.sig1) *
      Real.exp ((P.sig1 - P.sig0) / P.sig1 * L) = t := by
    rw [exp_ratio_split hs1.ne', hexpL]
  have hsplit2 : Real.exp ((P.sig0 + P.sig1) * L / P.sig1) =
      t * Real.exp (P.sig0 * L / P.sig1) := by
    rw [← hexpL, ← Real.exp_add]
    congr 1
    field_simp
    ring
  set X : ℝ := Real.exp (P.sig0 * L / P.sig1) with hXdef
  set E : ℝ := Real.exp ((P.sig1 - P.sig0) / P.sig1 * L) with hEdef
  have hXpos : 0 < X := Real.exp_pos _
  have hEpos : 0 < E := Real.exp_pos _
  -- the dominant term
  have hM1glow : 9 / 10 * (P.mu * Y ^ 4) ≤ ‖M1Num P (sGuess P n)‖ := by
    have hsub := M1Num_sub_norm_le P hP hM21 hgle
    have hlead : P.mu * Y ^ 4 ≤ ‖((P.mu : ℝ) : ℂ) * sGuess P n ^ 4‖ := by
      rw [norm_real_mul hmu.le, norm_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hY0.le hgge 4) hmu.le
    have htri : ‖((P.mu : ℝ) : ℂ) * sGuess P n ^ 4‖ ≤ ‖M1Num P (sGuess P n)‖ +
        ‖M1Num P (sGuess P n) - ((P.mu : ℝ) : ℂ) * sGuess P n ^ 4‖ := by
      calc ‖((P.mu : ℝ) : ℂ) * sGuess P n ^ 4‖
          = ‖M1Num P (sGuess P n) -
            (M1Num P (sGuess P n) - ((P.mu : ℝ) : ℂ) * sGuess P n ^ 4)‖ := by
            congr 1; ring
        _ ≤ _ := norm_sub_le _ _
    have hcorr : P.K1 * (21 / 20 * Y) ^ 3 ≤ 1 / 10 * (P.mu * Y ^ 4) := by
      have e1 : P.K1 * (21 / 20 * Y) ^ 3 ≤ 7 / 6 * P.K1 * Y ^ 3 := by
        linarith [mul_le_mul_of_nonneg_left hpow3 hK10]
      have e2 := mul_le_mul_of_nonneg_right hD1 (pow_nonneg hY0.le 3)
      have e4 : (0 : ℝ) ≤ P.mu * Y ^ 4 := by positivity
      linarith [e1, e2, e4]
    linarith [hsub, hlead, htri, hcorr]
  have hmain : 9 / 10 * (P.sig1 * P.mu * (t * Y ^ 4)) ≤
      ‖-((P.sig1 : ℂ) * M1Num P (sGuess P n) * ((t : ℝ) : ℂ))‖ := by
    rw [norm_neg, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hs1, abs_of_pos htpos]
    calc 9 / 10 * (P.sig1 * P.mu * (t * Y ^ 4))
        = P.sig1 * (9 / 10 * (P.mu * Y ^ 4)) * t := by ring
      _ ≤ P.sig1 * ‖M1Num P (sGuess P n)‖ * t := by
          refine mul_le_mul_of_nonneg_right ?_ htpos.le
          exact mul_le_mul_of_nonneg_left hM1glow hs1.le
  -- the four correction pieces, each `≤ (σ₁μ/20)·t·Y⁴`
  have hr1 : ‖McD P (sGuess P n)‖ ≤ P.sig1 * P.mu / 20 * (t * Y ^ 4) := by
    have h := McD_norm_le P hP hM21 hgle
    have h2 : ‖McD P (sGuess P n)‖ ≤ 4 / 3 * P.KMcD * Y ^ 5 := by
      linarith [h, mul_le_mul_of_nonneg_left hpow5 hKMcD0]
    refine le_trans h2 (budget_gen hA hY0 (by positivity) htlow ?_)
    have hnn : 0 ≤ P.sig1 * P.mu * Y := by positivity
    linarith [hD2]
  have hr3 : ‖M1D P (sGuess P n) * ((t : ℝ) : ℂ)‖ ≤ P.sig1 * P.mu / 20 * (t * Y ^ 4) := by
    have h := M1D_norm_le P hP hM21 hgle
    have hft : ‖((t : ℝ) : ℂ)‖ = t := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos]
    have h2 : ‖M1D P (sGuess P n) * ((t : ℝ) : ℂ)‖ ≤ 7 / 6 * P.K1D * Y ^ 3 * t := by
      rw [norm_mul, hft]
      have e1 : ‖M1D P (sGuess P n)‖ ≤ 7 / 6 * P.K1D * Y ^ 3 := by
        linarith [h, mul_le_mul_of_nonneg_left hpow3 hK1D0]
      exact mul_le_mul_of_nonneg_right e1 htpos.le
    refine le_trans h2 ?_
    have e2 : 7 / 6 * P.K1D * Y ^ 3 ≤ P.sig1 * P.mu / 20 * Y ^ 4 := by
      have e3 := mul_le_mul_of_nonneg_right hD4 (pow_nonneg hY0.le 3)
      have e4 : (0 : ℝ) ≤ P.sig1 * P.mu * Y ^ 4 := by positivity
      linarith [e3, e4]
    calc 7 / 6 * P.K1D * Y ^ 3 * t ≤ P.sig1 * P.mu / 20 * Y ^ 4 * t :=
        mul_le_mul_of_nonneg_right e2 htpos.le
      _ = P.sig1 * P.mu / 20 * (t * Y ^ 4) := by ring
  have hr2 : ‖(M0D P (sGuess P n) - (P.sig0 : ℂ) * M0Num P (sGuess P n)) *
      Complex.exp (-(sGuess P n * (P.sig0 : ℂ)))‖ ≤ P.sig1 * P.mu / 20 * (t * Y ^ 4) := by
    rw [norm_mul, hE0norm]
    have h1 : ‖M0D P (sGuess P n) - (P.sig0 : ℂ) * M0Num P (sGuess P n)‖ ≤
        (7 / 6 * P.K0D + 5 / 4 * P.sig0 * P.K0) * Y ^ 4 := by
      have ha := M0D_norm_le P hP hM21 hgle
      have hb : ‖(P.sig0 : ℂ) * M0Num P (sGuess P n)‖ ≤
          P.sig0 * (P.K0 * (21 / 20 * Y) ^ 4) := by
        rw [norm_real_mul hs0.le]
        exact mul_le_mul_of_nonneg_left (M0Num_norm_le P hP hM21 hgle) hs0.le
      have h34 : Y ^ 3 ≤ Y ^ 4 := pow_le_pow_right₀ h1 (by norm_num)
      refine le_trans (norm_sub_le _ _) ?_
      have e1 : ‖M0D P (sGuess P n)‖ ≤ 7 / 6 * P.K0D * Y ^ 4 := by
        have f1 := mul_le_mul_of_nonneg_left hpow3 hK0D0
        have f2 := mul_le_mul_of_nonneg_left h34 hK0D0
        linarith [ha, f1, f2]
      have e2 : P.sig0 * (P.K0 * (21 / 20 * Y) ^ 4) ≤ 5 / 4 * P.sig0 * P.K0 * Y ^ 4 := by
        linarith [mul_le_mul_of_nonneg_left hpow4 (mul_nonneg hs0.le hK00)]
      linarith [e1, e2]
    calc ‖M0D P (sGuess P n) - (P.sig0 : ℂ) * M0Num P (sGuess P n)‖ * X
        ≤ ((7 / 6 * P.K0D + 5 / 4 * P.sig0 * P.K0) * Y ^ 4) * X :=
          mul_le_mul_of_nonneg_right h1 hXpos.le
      _ ≤ P.sig1 * P.mu / 20 * E * Y ^ 4 * X := by
          have e3 : 7 / 6 * P.K0D + 5 / 4 * P.sig0 * P.K0 ≤ P.sig1 * P.mu / 20 * E := by
            linarith [hD3]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right e3 (pow_nonneg hY0.le 4)) hXpos.le
      _ = P.sig1 * P.mu / 20 * ((X * E) * Y ^ 4) := by ring
      _ = P.sig1 * P.mu / 20 * (t * Y ^ 4) := by rw [hsplit]
  have hr4 : ‖(M01D P (sGuess P n) - ((P.sig0 + P.sig1 : ℝ) : ℂ) * M01Num P (sGuess P n)) *
      Complex.exp (-(sGuess P n * ((P.sig0 + P.sig1 : ℝ) : ℂ)))‖ ≤
      P.sig1 * P.mu / 20 * (t * Y ^ 4) := by
    rw [norm_mul, hE01norm, hsplit2]
    have h1 : ‖M01D P (sGuess P n) - ((P.sig0 + P.sig1 : ℝ) : ℂ) * M01Num P (sGuess P n)‖ ≤
        (11 / 10 * P.K01D + 2 * (P.sig0 + P.sig1) * P.K01) * Y ^ 2 := by
      have ha := M01D_norm_le P hP hM21 hgle
      have hb : ‖((P.sig0 + P.sig1 : ℝ) : ℂ) * M01Num P (sGuess P n)‖ ≤
          (P.sig0 + P.sig1) * (P.K01 * (21 / 20 * Y) ^ 2) := by
        rw [norm_real_mul (by linarith : (0 : ℝ) ≤ P.sig0 + P.sig1)]
        exact mul_le_mul_of_nonneg_left (M01Num_norm_le P hP hM21 hgle) (by linarith)
      have h12 : Y ≤ Y ^ 2 := by nlinarith
      refine le_trans (norm_sub_le _ _) ?_
      have e1 : ‖M01D P (sGuess P n)‖ ≤ 11 / 10 * P.K01D * Y ^ 2 := by
        have f1 := M01D_norm_le P hP hM21 hgle
        have f2 : (0 : ℝ) ≤ P.K01D * Y ^ 2 := by positivity
        linarith [f1, mul_le_mul_of_nonneg_left h12 hK01D0, f2]
      have e2 : (P.sig0 + P.sig1) * (P.K01 * (21 / 20 * Y) ^ 2) ≤
          2 * (P.sig0 + P.sig1) * P.K01 * Y ^ 2 := by
        linarith [mul_le_mul_of_nonneg_left hpow2
          (mul_nonneg (by linarith : (0 : ℝ) ≤ P.sig0 + P.sig1) hK010)]
      linarith [e1, e2]
    have hgoal : (11 / 10 * P.K01D + 2 * (P.sig0 + P.sig1) * P.K01) * X ≤
        P.sig1 * P.mu / 20 * Y ^ 2 := by
      refine le_of_mul_le_mul_right ?_ hEpos
      have hup : (11 / 10 * P.K01D + 2 * (P.sig0 + P.sig1) * P.K01) * X * E =
          (11 / 10 * P.K01D + 2 * (P.sig0 + P.sig1) * P.K01) * t := by
        rw [mul_assoc, hsplit]
      rw [hup]
      have hnn : 0 ≤ 11 / 10 * P.K01D + 2 * (P.sig0 + P.sig1) * P.K01 := by positivity
      have h2 : (11 / 10 * P.K01D + 2 * (P.sig0 + P.sig1) * P.K01) * t ≤
          (11 / 10 * P.K01D + 2 * (P.sig0 + P.sig1) * P.K01) * (4 / P.mu * Y ^ 2) :=
        mul_le_mul_of_nonneg_left htup hnn
      have h3 : (11 / 10 * P.K01D + 2 * (P.sig0 + P.sig1) * P.K01) * (4 / P.mu * Y ^ 2) ≤
          P.sig1 * P.mu / 20 * Y ^ 2 * E := by
        rw [show (11 / 10 * P.K01D + 2 * (P.sig0 + P.sig1) * P.K01) * (4 / P.mu * Y ^ 2) =
          (44 / 10 * P.K01D + 8 * (P.sig0 + P.sig1) * P.K01) * Y ^ 2 / P.mu by ring,
          div_le_iff₀ hmu]
        have h4 := mul_le_mul_of_nonneg_right hD5 (pow_nonneg hY0.le 2)
        linarith [h4]
      linarith [h2, h3]
    calc ‖M01D P (sGuess P n) - ((P.sig0 + P.sig1 : ℝ) : ℂ) * M01Num P (sGuess P n)‖ *
        (t * X)
        ≤ ((11 / 10 * P.K01D + 2 * (P.sig0 + P.sig1) * P.K01) * Y ^ 2) * (t * X) := by
          refine mul_le_mul_of_nonneg_right h1 ?_
          positivity
      _ = ((11 / 10 * P.K01D + 2 * (P.sig0 + P.sig1) * P.K01) * X) * (t * Y ^ 2) := by ring
      _ ≤ (P.sig1 * P.mu / 20 * Y ^ 2) * (t * Y ^ 2) := by
          refine mul_le_mul_of_nonneg_right hgoal ?_
          positivity
      _ = P.sig1 * P.mu / 20 * (t * Y ^ 4) := by ring
  -- assemble via the reverse triangle inequality
  set c0 : ℂ := -((P.sig1 : ℂ) * M1Num P (sGuess P n) * ((t : ℝ) : ℂ)) with hc0
  set c1 : ℂ := McD P (sGuess P n) with hc1
  set c2 : ℂ := (M0D P (sGuess P n) - (P.sig0 : ℂ) * M0Num P (sGuess P n)) *
    Complex.exp (-(sGuess P n * (P.sig0 : ℂ))) with hc2
  set c3 : ℂ := M1D P (sGuess P n) * ((t : ℝ) : ℂ) with hc3
  set c4 : ℂ := (M01D P (sGuess P n) - ((P.sig0 + P.sig1 : ℝ) : ℂ) *
    M01Num P (sGuess P n)) *
    Complex.exp (-(sGuess P n * ((P.sig0 + P.sig1 : ℝ) : ℂ))) with hc4
  have hdecomp : WD P (sGuess P n) = c0 + (c1 + c2 + c3 + c4) := by
    rw [hc0, hc1, hc2, hc3, hc4]
    unfold WD
    rw [hPK]
    ring
  have hRest : ‖c1 + c2 + c3 + c4‖ ≤ 4 * (P.sig1 * P.mu / 20 * (t * Y ^ 4)) := by
    have u1 := norm_add_le (c1 + c2 + c3) c4
    have u2 := norm_add_le (c1 + c2) c3
    have u3 := norm_add_le c1 c2
    linarith [u1, u2, u3, hr1, hr2, hr3, hr4]
  have htri : ‖c0‖ - ‖c1 + c2 + c3 + c4‖ ≤ ‖WD P (sGuess P n)‖ := by
    rw [hdecomp]
    exact norm_add_lower _ _
  linarith [hmain, hRest, htri]

/-! ### The derivative of `detC` off the origin, and disk geometry -/

/-- The explicit derivative of `detC = W/s⁶` off the origin:
`F′(s) = (W′(s) − 6·W(s)/s)/s⁶`. -/
def derivF (P : MixParams) (s : ℂ) : ℂ := (WD P s - 6 * Wfun P s / s) / s ^ 6

/-- **`detC` differentiates to `derivF` at every `s ≠ 0`** — quotient rule on `W/s⁶`
transferred along the local identity `detC = W/s⁶` (the monomial bridge). -/
theorem detF_hasDerivAt (P : MixParams) {s : ℂ} (hs : s ≠ 0) :
    HasDerivAt P.detF (derivF P s) s := by
  have hW := Wfun_hasDerivAt P s
  have hpow : HasDerivAt (fun z : ℂ => z ^ 6) (((6 : ℕ) : ℂ) * s ^ (6 - 1)) s :=
    hasDerivAt_pow 6 s
  have hdiv := hW.div hpow (pow_ne_zero 6 hs)
  have heq : P.detF =ᶠ[nhds s] fun z => Wfun P z / z ^ 6 := by
    filter_upwards [IsOpen.mem_nhds isOpen_compl_singleton hs] with z hz
    have hz' : z ≠ 0 := hz
    rw [eq_div_iff (pow_ne_zero 6 hz'), mul_comm]
    exact detC_monomial_eq P hz'
  refine (hdiv.congr_of_eventuallyEq heq).congr_deriv ?_
  unfold derivF
  push_cast
  field_simp

/-- Envelope constant for `‖W(s)‖` on the chord disks: `‖W(s)‖ ≤ KW·t·Y⁴`. -/
def MixParams.KW (P : MixParams) : ℝ :=
  11 * (P.mu + P.K1) + 5 * P.K0 + 15 * P.K01 / P.mu

/-- Every point of a closed disk has real part at least `Re(centre) − radius`. -/
theorem mem_closedBall_re_ge' {c k : ℂ} {r : ℝ} (hk : k ∈ Metric.closedBall c r) :
    c.re - r ≤ k.re := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hk
  have h1 : |(k - c).re| ≤ ‖k - c‖ := Complex.abs_re_le_norm _
  rw [Complex.sub_re] at h1
  have h2 := abs_le.mp (le_trans h1 hk)
  linarith [h2.1]

/-- Every point of a closed disk has norm at most `‖centre‖ + radius`. -/
theorem mem_closedBall_norm_le' {c k : ℂ} {r : ℝ} (hk : k ∈ Metric.closedBall c r) :
    ‖k‖ ≤ ‖c‖ + r := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hk
  calc ‖k‖ = ‖c + (k - c)‖ := by congr 1; ring
    _ ≤ ‖c‖ + ‖k - c‖ := norm_add_le _ _
    _ ≤ ‖c‖ + r := by linarith

/-- Disk points inherit the norm cap `‖s‖ ≤ (11/10)Y`. -/
theorem disk_norm_le {g s : ℂ} {Y rc : ℝ} (hY0 : 0 ≤ Y) (hg : ‖g‖ ≤ 21 / 20 * Y)
    (hrc : rc ≤ Y / 40) (hs : s ∈ Metric.closedBall g rc) : ‖s‖ ≤ 11 / 10 * Y := by
  have h := mem_closedBall_norm_le' hs
  linarith

/-- Disk points keep a large imaginary part: `s.im ≥ (39/40)Y`. -/
theorem disk_im_ge {g s : ℂ} {Y rc : ℝ} (hgim : g.im = Y) (hrc : rc ≤ Y / 40)
    (hs : s ∈ Metric.closedBall g rc) : 39 / 40 * Y ≤ s.im := by
  have h := mem_closedBall_im_ge hs
  rw [hgim] at h
  linarith

/-- Disk points are nonzero (for `Y ≥ 1`). -/
theorem disk_ne_zero {g s : ℂ} {Y rc : ℝ} (hY : 1 ≤ Y) (hgim : g.im = Y)
    (hrc : rc ≤ Y / 40) (hs : s ∈ Metric.closedBall g rc) : s ≠ 0 := by
  intro h
  have him := disk_im_ge hgim hrc hs
  rw [h] at him
  simp only [Complex.zero_im] at him
  linarith

/-- Disk points keep a large norm: `‖s‖ ≥ (39/40)Y` (for `Y ≥ 0`). -/
theorem disk_norm_ge {g s : ℂ} {Y rc : ℝ} (hY0 : 0 ≤ Y) (hgim : g.im = Y)
    (hrc : rc ≤ Y / 40) (hs : s ∈ Metric.closedBall g rc) : 39 / 40 * Y ≤ ‖s‖ := by
  have him := disk_im_ge hgim hrc hs
  have h2 : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
  have h3 : s.im ≤ |s.im| := le_abs_self _
  linarith

/-- Decaying exponentials on a disk: `‖e^{-sc}‖ ≤ e^{-Re(centre)·c + c·r}` for `c ≥ 0`. -/
theorem disk_exp_norm_le {g s : ℂ} {rc c : ℝ} (hc : 0 ≤ c)
    (hs : s ∈ Metric.closedBall g rc) :
    ‖Complex.exp (-(s * (c : ℂ)))‖ ≤ Real.exp (-(g.re * c) + c * rc) := by
  rw [norm_exp_neg_mul]
  apply Real.exp_le_exp.mpr
  have h := mem_closedBall_re_ge' hs
  nlinarith [h, hc]

/-- Crude numeric bound: `e^x ≤ 3` for `x ≤ 1`. -/
theorem exp_small_le_three {x : ℝ} (hx : x ≤ 1) : Real.exp x ≤ 3 := by
  have h1 := Real.exp_one_lt_d9
  have h2 := Real.exp_le_exp.mpr hx
  linarith

set_option maxHeartbeats 2000000 in
/-- **`W` is `O(t·Y⁴)` on the chord disk**: every monomial piece of `W` is controlled on
the radius-`1/(20σ₁)` disk around the guess, giving `‖W(s)‖ ≤ KW·t·Y⁴`. -/
theorem Wfun_on_disk_le (P : MixParams) (hP : P.Phys) (n : ℕ) {Y : ℝ}
    (hYdef : Y = 2 * Real.pi * n / P.sig1)
    (h1 : 1 ≤ Y) (hMc2 : 2 * P.KMc ≤ Y) (hM12 : 2 * P.K1 ≤ P.mu * Y)
    (ht1 : 2 * (P.mu + P.K1) ≤ Y)
    (hLcap : 40 * Real.log (tRat P Y) ≤ P.sig1 * Y)
    (hrcY : 2 / P.sig1 ≤ Y)
    {s : ℂ} (hs : s ∈ Metric.closedBall (sGuess P n) (1 / (20 * P.sig1))) :
    ‖Wfun P s‖ ≤ P.KW * (tRat P Y * Y ^ 4) := by
  have hs0 : 0 < P.sig0 := hP.1
  have hs01 : P.sig0 < P.sig1 := hP.2.1
  have hs1 : 0 < P.sig1 := lt_trans hs0 hs01
  have hmu : 0 < P.mu := mul_pos (hP.2.2.1 1 1) (hP.2.2.2.1 1 1)
  have hK10 := K1_nonneg P hP
  have hKMc0 := KMc_nonneg P hP
  have hK00 := K0_nonneg P hP
  have hK010 := K01_nonneg P hP
  have hY0 : (0 : ℝ) < Y := lt_of_lt_of_le one_pos h1
  set t : ℝ := tRat P Y with htdef
  set L : ℝ := Real.log t with hLdef
  have hA : 0 < P.mu + P.K1 := by linarith
  have htlow : Y ^ 2 / (2 * (P.mu + P.K1)) ≤ t := tRat_lower P hP h1 hMc2 hM12
  have htup : t ≤ 4 / P.mu * Y ^ 2 :=
    tRat_upper P hP h1 (by linarith [hKMc0]) hM12
  have ht1' : 1 ≤ t := by
    have hYsq : Y ≤ Y ^ 2 := by nlinarith
    have h2A : 2 * (P.mu + P.K1) ≤ Y ^ 2 := by linarith
    have : 1 ≤ Y ^ 2 / (2 * (P.mu + P.K1)) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    linarith [htlow]
  have htpos : 0 < t := lt_of_lt_of_le one_pos ht1'
  have h0L : 0 ≤ L := by rw [hLdef]; exact Real.log_nonneg ht1'
  have hgle : ‖sGuess P n‖ ≤ 21 / 20 * Y := by
    have h := sGuess_norm_le P hs1 n (by rw [← hYdef, ← htdef, ← hLdef]; exact h0L)
      (by rw [← hYdef, ← htdef, ← hLdef]; exact hLcap)
    rw [← hYdef] at h
    nlinarith [h, hY0.le]
  have hgim : (sGuess P n).im = Y := by rw [sGuess_im, ← hYdef]
  have hgre : (sGuess P n).re = -L / P.sig1 := by
    rw [sGuess_re, ← hYdef, ← htdef, ← hLdef]
  have hrcY' : 2 ≤ P.sig1 * Y := by
    rw [div_le_iff₀ hs1] at hrcY
    linarith [hrcY]
  have hrc : 1 / (20 * P.sig1) ≤ Y / 40 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 40)]
    nlinarith [hrcY']
  have hsle : ‖s‖ ≤ 11 / 10 * Y := disk_norm_le hY0.le hgle hrc hs
  have hM11 : (1 : ℝ) ≤ 11 / 10 * Y := by linarith
  have hq6 : (11 / 10 * Y) ^ 6 ≤ 9 / 5 * Y ^ 6 := by nlinarith [pow_nonneg hY0.le 6]
  have hq5 : (11 / 10 * Y) ^ 5 ≤ 5 / 3 * Y ^ 5 := by nlinarith [pow_nonneg hY0.le 5]
  have hq4 : (11 / 10 * Y) ^ 4 ≤ 3 / 2 * Y ^ 4 := by nlinarith [pow_nonneg hY0.le 4]
  have hq2 : (11 / 10 * Y) ^ 2 ≤ 5 / 4 * Y ^ 2 := by nlinarith [pow_nonneg hY0.le 2]
  set X : ℝ := Real.exp (P.sig0 * L / P.sig1) with hXdef
  set E : ℝ := Real.exp ((P.sig1 - P.sig0) / P.sig1 * L) with hEdef
  have hXpos : 0 < X := Real.exp_pos _
  have hexpL : Real.exp L = t := by rw [hLdef]; exact Real.exp_log htpos
  have hsplit : X * E = t := by rw [hXdef, hEdef, exp_ratio_split hs1.ne', hexpL]
  have hE1 : 1 ≤ E := by
    rw [hEdef, show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
    apply Real.exp_le_exp.mpr
    have := mul_nonneg (div_nonneg (by linarith : (0 : ℝ) ≤ P.sig1 - P.sig0) hs1.le) h0L
    linarith
  have hXle : X ≤ t := by
    calc X = X * 1 := by ring
      _ ≤ X * E := mul_le_mul_of_nonneg_left hE1 hXpos.le
      _ = t := hsplit
  have hsrc : P.sig1 * (1 / (20 * P.sig1)) = 1 / 20 := by field_simp
  -- exponential bounds on the disk
  have hE1s : ‖Complex.exp (-(s * (P.sig1 : ℂ)))‖ ≤ 3 * t := by
    have h := disk_exp_norm_le hs1.le hs
    rw [hgre] at h
    have harg : -(-L / P.sig1 * P.sig1) + P.sig1 * (1 / (20 * P.sig1)) = L + 1 / 20 := by
      rw [hsrc]
      field_simp
    rw [harg] at h
    calc ‖Complex.exp (-(s * (P.sig1 : ℂ)))‖ ≤ Real.exp (L + 1 / 20) := h
      _ = Real.exp L * Real.exp (1 / 20) := Real.exp_add _ _
      _ ≤ t * 3 := by
          rw [hexpL]
          exact mul_le_mul_of_nonneg_left (exp_small_le_three (by norm_num)) htpos.le
      _ = 3 * t := by ring
  have hE0s : ‖Complex.exp (-(s * (P.sig0 : ℂ)))‖ ≤ 3 * X := by
    have h := disk_exp_norm_le hs0.le hs
    rw [hgre] at h
    have harg : -(-L / P.sig1 * P.sig0) + P.sig0 * (1 / (20 * P.sig1)) =
        P.sig0 * L / P.sig1 + P.sig0 / (20 * P.sig1) := by
      field_simp
    rw [harg, Real.exp_add] at h
    calc ‖Complex.exp (-(s * (P.sig0 : ℂ)))‖ ≤ X * Real.exp (P.sig0 / (20 * P.sig1)) := h
      _ ≤ X * 3 := by
          refine mul_le_mul_of_nonneg_left (exp_small_le_three ?_) hXpos.le
          rw [div_le_one (by positivity)]
          nlinarith [hs01, hs1]
      _ = 3 * X := by ring
  have hE01s : ‖Complex.exp (-(s * ((P.sig0 + P.sig1 : ℝ) : ℂ)))‖ ≤ 3 * (t * X) := by
    have h := disk_exp_norm_le (by linarith : (0 : ℝ) ≤ P.sig0 + P.sig1) hs
    rw [hgre] at h
    have harg : -(-L / P.sig1 * (P.sig0 + P.sig1)) +
        (P.sig0 + P.sig1) * (1 / (20 * P.sig1)) =
        (P.sig0 * L / P.sig1 + L) + (P.sig0 + P.sig1) / (20 * P.sig1) := by
      field_simp
    rw [harg, Real.exp_add, Real.exp_add] at h
    calc ‖Complex.exp (-(s * ((P.sig0 + P.sig1 : ℝ) : ℂ)))‖ ≤
        X * Real.exp L * Real.exp ((P.sig0 + P.sig1) / (20 * P.sig1)) := h
      _ ≤ X * t * 3 := by
          rw [hexpL]
          refine mul_le_mul_of_nonneg_left (exp_small_le_three ?_) (by positivity)
          rw [div_le_one (by positivity)]
          nlinarith [hs01, hs1]
      _ = 3 * (t * X) := by ring
  -- the four pieces
  have hY26 : Y ^ 6 ≤ 2 * (P.mu + P.K1) * t * Y ^ 4 := by
    have h := htlow
    rw [div_le_iff₀ (by positivity)] at h
    nlinarith [mul_le_mul_of_nonneg_right h (pow_nonneg hY0.le 4)]
  have pMc : ‖McNum P s‖ ≤ 6 * (P.mu + P.K1) * (t * Y ^ 4) := by
    have hsub := McNum_sub_norm_le P hP hM11 hsle
    have h6 : ‖s ^ 6‖ ≤ (11 / 10 * Y) ^ 6 := by
      rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg s) hsle 6
    have htri : ‖McNum P s‖ ≤ ‖McNum P s - s ^ 6‖ + ‖s ^ 6‖ := by
      calc ‖McNum P s‖ = ‖(McNum P s - s ^ 6) + s ^ 6‖ := by congr 1; ring
        _ ≤ _ := norm_add_le _ _
    have hKMcY : P.KMc * (11 / 10 * Y) ^ 5 ≤ 5 / 6 * Y ^ 6 := by
      have e1 : P.KMc * (11 / 10 * Y) ^ 5 ≤ P.KMc * (5 / 3 * Y ^ 5) :=
        mul_le_mul_of_nonneg_left hq5 hKMc0
      nlinarith [mul_le_mul_of_nonneg_right hMc2 (pow_nonneg hY0.le 5)]
    have htot : ‖McNum P s‖ ≤ 3 * Y ^ 6 := by linarith [hsub, h6, htri, hq6, hKMcY]
    nlinarith [htot, hY26]
  have pM1 : ‖M1Num P s * Complex.exp (-(s * (P.sig1 : ℂ)))‖ ≤
      9 / 2 * (P.mu + P.K1) * (t * Y ^ 4) := by
    have h1' := M1Num_norm_le P hP hM11 hsle
    have h2 : ‖M1Num P s‖ ≤ 3 / 2 * (P.mu + P.K1) * Y ^ 4 := by
      have e1 : (P.mu + P.K1) * (11 / 10 * Y) ^ 4 ≤ (P.mu + P.K1) * (3 / 2 * Y ^ 4) :=
        mul_le_mul_of_nonneg_left hq4 (by linarith)
      linarith [h1', e1]
    calc ‖M1Num P s * Complex.exp (-(s * (P.sig1 : ℂ)))‖
        ≤ (3 / 2 * (P.mu + P.K1) * Y ^ 4) * (3 * t) := norm_mul_le_bound h2 hE1s
      _ = 9 / 2 * (P.mu + P.K1) * (t * Y ^ 4) := by ring
  have pM0 : ‖M0Num P s * Complex.exp (-(s * (P.sig0 : ℂ)))‖ ≤
      5 * P.K0 * (t * Y ^ 4) := by
    have h1' := M0Num_norm_le P hP hM11 hsle
    have h2 : ‖M0Num P s‖ ≤ 3 / 2 * P.K0 * Y ^ 4 := by
      have e1 : P.K0 * (11 / 10 * Y) ^ 4 ≤ P.K0 * (3 / 2 * Y ^ 4) :=
        mul_le_mul_of_nonneg_left hq4 hK00
      linarith [h1', e1]
    calc ‖M0Num P s * Complex.exp (-(s * (P.sig0 : ℂ)))‖
        ≤ (3 / 2 * P.K0 * Y ^ 4) * (3 * X) := norm_mul_le_bound h2 hE0s
      _ = 9 / 2 * P.K0 * (X * Y ^ 4) := by ring
      _ ≤ 9 / 2 * P.K0 * (t * Y ^ 4) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_right hXle (by positivity)
      _ ≤ 5 * P.K0 * (t * Y ^ 4) := by nlinarith [hK00, htpos.le, pow_nonneg hY0.le 4]
  have pM01 : ‖M01Num P s * Complex.exp (-(s * ((P.sig0 + P.sig1 : ℝ) : ℂ)))‖ ≤
      15 * P.K01 / P.mu * (t * Y ^ 4) := by
    have h1' := M01Num_norm_le P hP hM11 hsle
    have h2 : ‖M01Num P s‖ ≤ 5 / 4 * P.K01 * Y ^ 2 := by
      have e1 : P.K01 * (11 / 10 * Y) ^ 2 ≤ P.K01 * (5 / 4 * Y ^ 2) :=
        mul_le_mul_of_nonneg_left hq2 hK010
      linarith [h1', e1]
    have hXup : X ≤ 4 / P.mu * Y ^ 2 := le_trans hXle htup
    calc ‖M01Num P s * Complex.exp (-(s * ((P.sig0 + P.sig1 : ℝ) : ℂ)))‖
        ≤ (5 / 4 * P.K01 * Y ^ 2) * (3 * (t * X)) := norm_mul_le_bound h2 hE01s
      _ = 15 / 4 * P.K01 * (X * (t * Y ^ 2)) := by ring
      _ ≤ 15 / 4 * P.K01 * ((4 / P.mu * Y ^ 2) * (t * Y ^ 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_right hXup (by positivity)
      _ = 15 * P.K01 / P.mu * (t * Y ^ 4) := by ring
  -- assemble
  unfold Wfun MixParams.KW
  have u1 := norm_add_le (McNum P s + M0Num P s * Complex.exp (-(s * (P.sig0 : ℂ))) +
    M1Num P s * Complex.exp (-(s * (P.sig1 : ℂ))))
    (M01Num P s * Complex.exp (-(s * ((P.sig0 + P.sig1 : ℝ) : ℂ))))
  have u2 := norm_add_le (McNum P s + M0Num P s * Complex.exp (-(s * (P.sig0 : ℂ))))
    (M1Num P s * Complex.exp (-(s * (P.sig1 : ℂ))))
  have u3 := norm_add_le (McNum P s) (M0Num P s * Complex.exp (-(s * (P.sig0 : ℂ))))
  have hfin : (0 : ℝ) ≤ (P.mu + P.K1) * (t * Y ^ 4) := by positivity
  linarith [u1, u2, u3, pMc, pM0, pM1, pM01, hfin]

set_option maxHeartbeats 8000000 in
/-- **Derivative variation on the chord disk**: `‖W′(g) − W′(s)‖ ≤ (3/8)·σ₁μ·t·Y⁴` for `s`
in the radius-`1/(20σ₁)` disk — the dominant contribution is the oscillatory factor's
`2σ₁r = 1/10` variation against `σ₁·M₁·t`, everything else is threshold-small. -/
theorem WD_var_on_disk_le (P : MixParams) (hP : P.Phys) (n : ℕ) {Y : ℝ}
    (hYdef : Y = 2 * Real.pi * n / P.sig1)
    (h1 : 1 ≤ Y) (hMc2 : 2 * P.KMc ≤ Y) (hM12 : 2 * P.K1 ≤ P.mu * Y)
    (ht1 : 2 * (P.mu + P.K1) ≤ Y)
    (hLcap : 40 * Real.log (tRat P Y) ≤ P.sig1 * Y)
    (hrcY : 2 / P.sig1 ≤ Y)
    (hB1 : 214 * P.KMcD * (P.mu + P.K1) ≤ P.sig1 * P.mu * Y)
    (hB2 : 173 * P.K0D + 192 * P.sig0 * P.K0 ≤ P.sig1 * P.mu *
      Real.exp ((P.sig1 - P.sig0) / P.sig1 * Real.log (tRat P Y)))
    (hB3 : 87 * P.K1D ≤ P.sig1 * P.mu * Y)
    (hB4 : 20 ≤ P.sig1 * Y)
    (hB5 : 87 * P.K1 ≤ P.mu * Y)
    (hB6 : 564 * P.K01D + 640 * (P.sig0 + P.sig1) * P.K01 ≤ P.sig1 * P.mu ^ 2 *
      Real.exp ((P.sig1 - P.sig0) / P.sig1 * Real.log (tRat P Y)))
    {s : ℂ} (hs : s ∈ Metric.closedBall (sGuess P n) (1 / (20 * P.sig1))) :
    ‖WD P (sGuess P n) - WD P s‖ ≤ 3 / 8 * (P.sig1 * P.mu * (tRat P Y * Y ^ 4)) := by
  have hs0 : 0 < P.sig0 := hP.1
  have hs01 : P.sig0 < P.sig1 := hP.2.1
  have hs1 : 0 < P.sig1 := lt_trans hs0 hs01
  have hmu : 0 < P.mu := mul_pos (hP.2.2.1 1 1) (hP.2.2.2.1 1 1)
  have hK10 := K1_nonneg P hP
  have hKMc0 := KMc_nonneg P hP
  have hK00 := K0_nonneg P hP
  have hK010 := K01_nonneg P hP
  have hKMcD0 := KMcD_nonneg P hP
  have hK1D0 := K1D_nonneg P hP
  have hK0D0 := K0D_nonneg P hP
  have hK01D0 := K01D_nonneg P hP
  have hY0 : (0 : ℝ) < Y := lt_of_lt_of_le one_pos h1
  set t : ℝ := tRat P Y with htdef
  set L : ℝ := Real.log t with hLdef
  have hA : 0 < P.mu + P.K1 := by linarith
  have htlow : Y ^ 2 / (2 * (P.mu + P.K1)) ≤ t := tRat_lower P hP h1 hMc2 hM12
  have htup : t ≤ 4 / P.mu * Y ^ 2 :=
    tRat_upper P hP h1 (by linarith [hKMc0]) hM12
  have ht1' : 1 ≤ t := by
    have hYsq : Y ≤ Y ^ 2 := by nlinarith
    have h2A : 2 * (P.mu + P.K1) ≤ Y ^ 2 := by linarith
    have : 1 ≤ Y ^ 2 / (2 * (P.mu + P.K1)) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    linarith [htlow]
  have htpos : 0 < t := lt_of_lt_of_le one_pos ht1'
  have h0L : 0 ≤ L := by rw [hLdef]; exact Real.log_nonneg ht1'
  have hPK : Complex.exp (-(sGuess P n * (P.sig1 : ℂ))) = ((t : ℝ) : ℂ) := by
    have h := exp_at_sGuess P hs1 n (by rw [← hYdef]; exact htpos)
    rw [← hYdef] at h
    exact h
  have hgle : ‖sGuess P n‖ ≤ 21 / 20 * Y := by
    have h := sGuess_norm_le P hs1 n (by rw [← hYdef, ← htdef, ← hLdef]; exact h0L)
      (by rw [← hYdef, ← htdef, ← hLdef]; exact hLcap)
    rw [← hYdef] at h
    nlinarith [h, hY0.le]
  have hgle' : ‖sGuess P n‖ ≤ 11 / 10 * Y := by linarith
  have hgre : (sGuess P n).re = -L / P.sig1 := by
    rw [sGuess_re, ← hYdef, ← htdef, ← hLdef]
  have hrcY' : 2 ≤ P.sig1 * Y := by
    rw [div_le_iff₀ hs1] at hrcY
    linarith [hrcY]
  have hrc : 1 / (20 * P.sig1) ≤ Y / 40 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 40)]
    nlinarith [hrcY']
  have hsle : ‖s‖ ≤ 11 / 10 * Y := disk_norm_le hY0.le hgle hrc hs
  have hM11 : (1 : ℝ) ≤ 11 / 10 * Y := by linarith
  have hq5 : (11 / 10 * Y) ^ 5 ≤ 5 / 3 * Y ^ 5 := by nlinarith [pow_nonneg hY0.le 5]
  have hq4 : (11 / 10 * Y) ^ 4 ≤ 3 / 2 * Y ^ 4 := by nlinarith [pow_nonneg hY0.le 4]
  have hq3 : (11 / 10 * Y) ^ 3 ≤ 27 / 20 * Y ^ 3 := by nlinarith [pow_nonneg hY0.le 3]
  have hq2 : (11 / 10 * Y) ^ 2 ≤ 5 / 4 * Y ^ 2 := by nlinarith [pow_nonneg hY0.le 2]
  set X : ℝ := Real.exp (P.sig0 * L / P.sig1) with hXdef
  set E : ℝ := Real.exp ((P.sig1 - P.sig0) / P.sig1 * L) with hEdef
  have hXpos : 0 < X := Real.exp_pos _
  have hEpos : 0 < E := Real.exp_pos _
  have hexpL : Real.exp L = t := by rw [hLdef]; exact Real.exp_log htpos
  have hsplit : X * E = t := by rw [hXdef, hEdef, exp_ratio_split hs1.ne', hexpL]
  have hE0norm : ‖Complex.exp (-(sGuess P n * (P.sig0 : ℂ)))‖ = X := by
    have h := sGuess_exp_norm P hs1 n P.sig0
    rw [← hYdef, ← htdef, ← hLdef] at h
    exact h
  have hE01g : ‖Complex.exp (-(sGuess P n * ((P.sig0 + P.sig1 : ℝ) : ℂ)))‖ = t * X := by
    have h := sGuess_exp_norm P hs1 n (P.sig0 + P.sig1)
    rw [← hYdef, ← htdef, ← hLdef] at h
    rw [h, ← hexpL, hXdef, ← Real.exp_add]
    congr 1
    field_simp
    ring
  have hsrc : P.sig1 * (1 / (20 * P.sig1)) = 1 / 20 := by field_simp
  have hE0s : ‖Complex.exp (-(s * (P.sig0 : ℂ)))‖ ≤ 3 * X := by
    have h := disk_exp_norm_le hs0.le hs
    rw [hgre] at h
    have harg : -(-L / P.sig1 * P.sig0) + P.sig0 * (1 / (20 * P.sig1)) =
        P.sig0 * L / P.sig1 + P.sig0 / (20 * P.sig1) := by
      field_simp
    rw [harg, Real.exp_add] at h
    calc ‖Complex.exp (-(s * (P.sig0 : ℂ)))‖ ≤ X * Real.exp (P.sig0 / (20 * P.sig1)) := h
      _ ≤ X * 3 := by
          refine mul_le_mul_of_nonneg_left (exp_small_le_three ?_) hXpos.le
          rw [div_le_one (by positivity)]
          nlinarith [hs01, hs1]
      _ = 3 * X := by ring
  have hE01s : ‖Complex.exp (-(s * ((P.sig0 + P.sig1 : ℝ) : ℂ)))‖ ≤ 3 * (t * X) := by
    have h := disk_exp_norm_le (by linarith : (0 : ℝ) ≤ P.sig0 + P.sig1) hs
    rw [hgre] at h
    have harg : -(-L / P.sig1 * (P.sig0 + P.sig1)) +
        (P.sig0 + P.sig1) * (1 / (20 * P.sig1)) =
        (P.sig0 * L / P.sig1 + L) + (P.sig0 + P.sig1) / (20 * P.sig1) := by
      field_simp
    rw [harg, Real.exp_add, Real.exp_add] at h
    calc ‖Complex.exp (-(s * ((P.sig0 + P.sig1 : ℝ) : ℂ)))‖ ≤
        X * Real.exp L * Real.exp ((P.sig0 + P.sig1) / (20 * P.sig1)) := h
      _ ≤ X * t * 3 := by
          rw [hexpL]
          refine mul_le_mul_of_nonneg_left (exp_small_le_three ?_) (by positivity)
          rw [div_le_one (by positivity)]
          nlinarith [hs01, hs1]
      _ = 3 * (t * X) := by ring
  have hgs : ‖s - sGuess P n‖ ≤ 1 / (20 * P.sig1) := by
    rw [← dist_eq_norm]
    exact Metric.mem_closedBall.mp hs
  have hgs' : ‖sGuess P n - s‖ ≤ 1 / (20 * P.sig1) := by
    rw [norm_sub_rev]
    exact hgs
  have hE1split : Complex.exp (-(s * (P.sig1 : ℂ))) =
      ((t : ℝ) : ℂ) * Complex.exp (-((s - sGuess P n) * (P.sig1 : ℂ))) := by
    rw [show -(s * (P.sig1 : ℂ)) = -(sGuess P n * (P.sig1 : ℂ)) +
      -((s - sGuess P n) * (P.sig1 : ℂ)) by ring, Complex.exp_add, hPK]
  have hEfac : ‖Complex.exp (-((s - sGuess P n) * (P.sig1 : ℂ))) - 1‖ ≤ 1 / 10 := by
    have hz : ‖-((s - sGuess P n) * (P.sig1 : ℂ))‖ ≤ 1 / 20 := by
      rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs1]
      calc ‖s - sGuess P n‖ * P.sig1 ≤ 1 / (20 * P.sig1) * P.sig1 :=
          mul_le_mul_of_nonneg_right hgs hs1.le
        _ = 1 / 20 := by field_simp
    calc ‖Complex.exp (-((s - sGuess P n) * (P.sig1 : ℂ))) - 1‖
        ≤ 2 * ‖-((s - sGuess P n) * (P.sig1 : ℂ))‖ :=
          Complex.norm_exp_sub_one_le (le_trans hz (by norm_num))
      _ ≤ 1 / 10 := by linarith [hz]
  -- piece a: `McD`
  have hpa : ‖McD P (sGuess P n) - McD P s‖ ≤
      1 / 32 * (P.sig1 * P.mu * (t * Y ^ 4)) := by
    have h1' := McD_norm_le P hP hM11 hgle'
    have h2' := McD_norm_le P hP hM11 hsle
    have h3 : ‖McD P (sGuess P n) - McD P s‖ ≤ 10 / 3 * P.KMcD * Y ^ 5 := by
      have := norm_sub_le (McD P (sGuess P n)) (McD P s)
      have e1 := mul_le_mul_of_nonneg_left hq5 hKMcD0
      linarith
    refine le_trans h3 ?_
    have hgen := budget_gen (A := P.mu + P.K1) (C := 10 / 3 * P.KMcD)
      (D := P.sig1 * P.mu / 32) hA hY0 (by positivity) htlow ?_
    · calc 10 / 3 * P.KMcD * Y ^ 5 ≤ P.sig1 * P.mu / 32 * (t * Y ^ 4) := hgen
        _ = 1 / 32 * (P.sig1 * P.mu * (t * Y ^ 4)) := by ring
    · have hnn : 0 ≤ P.sig1 * P.mu * Y := by positivity
      linarith [hB1]
  -- piece b: the `e^{-sσ₀}` block
  have hM0Dg : ‖M0D P (sGuess P n) - (P.sig0 : ℂ) * M0Num P (sGuess P n)‖ ≤
      (27 / 20 * P.K0D + 3 / 2 * P.sig0 * P.K0) * Y ^ 4 := by
    refine le_trans (norm_sub_le _ _) ?_
    have ha := M0D_norm_le P hP hM11 hgle'
    have hb : ‖(P.sig0 : ℂ) * M0Num P (sGuess P n)‖ ≤
        P.sig0 * (P.K0 * (11 / 10 * Y) ^ 4) := by
      rw [norm_real_mul hs0.le]
      exact mul_le_mul_of_nonneg_left (M0Num_norm_le P hP hM11 hgle') hs0.le
    have h34 : Y ^ 3 ≤ Y ^ 4 := pow_le_pow_right₀ h1 (by norm_num)
    have e1 := mul_le_mul_of_nonneg_left hq3 hK0D0
    have e2 := mul_le_mul_of_nonneg_left h34 (by positivity : (0 : ℝ) ≤ 27 / 20 * P.K0D)
    have e3 := mul_le_mul_of_nonneg_left hq4 (mul_nonneg hs0.le hK00)
    linarith [ha, hb]
  have hM0Ds : ‖M0D P s - (P.sig0 : ℂ) * M0Num P s‖ ≤
      (27 / 20 * P.K0D + 3 / 2 * P.sig0 * P.K0) * Y ^ 4 := by
    refine le_trans (norm_sub_le _ _) ?_
    have ha := M0D_norm_le P hP hM11 hsle
    have hb : ‖(P.sig0 : ℂ) * M0Num P s‖ ≤ P.sig0 * (P.K0 * (11 / 10 * Y) ^ 4) := by
      rw [norm_real_mul hs0.le]
      exact mul_le_mul_of_nonneg_left (M0Num_norm_le P hP hM11 hsle) hs0.le
    have h34 : Y ^ 3 ≤ Y ^ 4 := pow_le_pow_right₀ h1 (by norm_num)
    have e1 := mul_le_mul_of_nonneg_left hq3 hK0D0
    have e2 := mul_le_mul_of_nonneg_left h34 (by positivity : (0 : ℝ) ≤ 27 / 20 * P.K0D)
    have e3 := mul_le_mul_of_nonneg_left hq4 (mul_nonneg hs0.le hK00)
    linarith [ha, hb]
  have hpb : ‖(M0D P (sGuess P n) - (P.sig0 : ℂ) * M0Num P (sGuess P n)) *
      Complex.exp (-(sGuess P n * (P.sig0 : ℂ))) -
      (M0D P s - (P.sig0 : ℂ) * M0Num P s) * Complex.exp (-(s * (P.sig0 : ℂ)))‖ ≤
      1 / 32 * (P.sig1 * P.mu * (t * Y ^ 4)) := by
    have hg := norm_mul_le_bound hM0Dg (le_of_eq hE0norm)
    have hss := norm_mul_le_bound hM0Ds hE0s
    have htot : ‖(M0D P (sGuess P n) - (P.sig0 : ℂ) * M0Num P (sGuess P n)) *
        Complex.exp (-(sGuess P n * (P.sig0 : ℂ))) -
        (M0D P s - (P.sig0 : ℂ) * M0Num P s) * Complex.exp (-(s * (P.sig0 : ℂ)))‖ ≤
        4 * ((27 / 20 * P.K0D + 3 / 2 * P.sig0 * P.K0) * Y ^ 4) * X := by
      refine le_trans (norm_sub_le _ _) ?_
      linarith [hg, hss]
    refine le_trans htot ?_
    have hE32 : 4 * (27 / 20 * P.K0D + 3 / 2 * P.sig0 * P.K0) ≤ P.sig1 * P.mu / 32 * E := by
      linarith [hB2]
    calc 4 * ((27 / 20 * P.K0D + 3 / 2 * P.sig0 * P.K0) * Y ^ 4) * X
        = (4 * (27 / 20 * P.K0D + 3 / 2 * P.sig0 * P.K0)) * (Y ^ 4 * X) := by ring
      _ ≤ (P.sig1 * P.mu / 32 * E) * (Y ^ 4 * X) := by
          refine mul_le_mul_of_nonneg_right hE32 ?_
          positivity
      _ = 1 / 32 * (P.sig1 * P.mu * ((X * E) * Y ^ 4)) := by ring
      _ = 1 / 32 * (P.sig1 * P.mu * (t * Y ^ 4)) := by rw [hsplit]
  -- pieces c and d: the `e^{-sσ₁}` block, split along the exact phase kill
  have hM1Dvar : ‖M1D P (sGuess P n) - M1D P s‖ ≤ 27 / 10 * P.K1D * Y ^ 3 := by
    have ha := M1D_norm_le P hP hM11 hgle'
    have hb := M1D_norm_le P hP hM11 hsle
    have e1 := mul_le_mul_of_nonneg_left hq3 hK1D0
    have := norm_sub_le (M1D P (sGuess P n)) (M1D P s)
    linarith
  have hM1var : ‖M1Num P (sGuess P n) - M1Num P s‖ ≤
      27 / 100 * P.mu / P.sig1 * Y ^ 3 + 27 / 10 * P.K1 * Y ^ 3 := by
    have h := M1Num_two_point_le P hP hM11 hgle' hsle
    have e1 : P.mu * (4 * (11 / 10 * Y) ^ 3 * ‖sGuess P n - s‖) ≤
        27 / 100 * P.mu / P.sig1 * Y ^ 3 := by
      have e2 : (11 / 10 * Y) ^ 3 * ‖sGuess P n - s‖ ≤
          (27 / 20 * Y ^ 3) * (1 / (20 * P.sig1)) := by
        refine mul_le_mul hq3 hgs' (norm_nonneg _) (by positivity)
      have e3 := mul_le_mul_of_nonneg_left e2 (by positivity : (0 : ℝ) ≤ 4 * P.mu)
      calc P.mu * (4 * (11 / 10 * Y) ^ 3 * ‖sGuess P n - s‖)
          = 4 * P.mu * ((11 / 10 * Y) ^ 3 * ‖sGuess P n - s‖) := by ring
        _ ≤ 4 * P.mu * ((27 / 20 * Y ^ 3) * (1 / (20 * P.sig1))) := e3
        _ = 27 / 100 * P.mu / P.sig1 * Y ^ 3 := by field_simp; ring
    have e4 : 2 * P.K1 * (11 / 10 * Y) ^ 3 ≤ 27 / 10 * P.K1 * Y ^ 3 := by
      have := mul_le_mul_of_nonneg_left hq3 (by positivity : (0 : ℝ) ≤ 2 * P.K1)
      linarith
    linarith [h, e1, e4]
  have hpc : ‖((M1D P (sGuess P n) - (P.sig1 : ℂ) * M1Num P (sGuess P n)) -
      (M1D P s - (P.sig1 : ℂ) * M1Num P s)) * ((t : ℝ) : ℂ)‖ ≤
      3 / 32 * (P.sig1 * P.mu * (t * Y ^ 4)) := by
    have hft : ‖((t : ℝ) : ℂ)‖ = t := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos]
    have hinner : ‖(M1D P (sGuess P n) - (P.sig1 : ℂ) * M1Num P (sGuess P n)) -
        (M1D P s - (P.sig1 : ℂ) * M1Num P s)‖ ≤
        27 / 10 * P.K1D * Y ^ 3 + P.sig1 * (27 / 100 * P.mu / P.sig1 * Y ^ 3 +
          27 / 10 * P.K1 * Y ^ 3) := by
      have hre : (M1D P (sGuess P n) - (P.sig1 : ℂ) * M1Num P (sGuess P n)) -
          (M1D P s - (P.sig1 : ℂ) * M1Num P s) =
          (M1D P (sGuess P n) - M1D P s) -
            (P.sig1 : ℂ) * (M1Num P (sGuess P n) - M1Num P s) := by ring
      rw [hre]
      refine le_trans (norm_sub_le _ _) ?_
      have h2 : ‖(P.sig1 : ℂ) * (M1Num P (sGuess P n) - M1Num P s)‖ ≤
          P.sig1 * (27 / 100 * P.mu / P.sig1 * Y ^ 3 + 27 / 10 * P.K1 * Y ^ 3) := by
        rw [norm_real_mul hs1.le]
        exact mul_le_mul_of_nonneg_left hM1var hs1.le
      linarith [hM1Dvar, h2]
    rw [norm_mul, hft]
    have hbud : (27 / 10 * P.K1D * Y ^ 3 + P.sig1 * (27 / 100 * P.mu / P.sig1 * Y ^ 3 +
        27 / 10 * P.K1 * Y ^ 3)) * t ≤ 3 / 32 * (P.sig1 * P.mu * (t * Y ^ 4)) := by
      have hsig : P.sig1 * (27 / 100 * P.mu / P.sig1 * Y ^ 3) =
          27 / 100 * P.mu * Y ^ 3 := by field_simp
      have b1 : 27 / 10 * P.K1D * Y ^ 3 ≤ 1 / 32 * (P.sig1 * P.mu * Y ^ 4) := by
        have := mul_le_mul_of_nonneg_right hB3 (pow_nonneg hY0.le 3)
        have hnn : (0 : ℝ) ≤ P.sig1 * P.mu * Y ^ 4 := by positivity
        linarith
      have b2 : 27 / 100 * P.mu * Y ^ 3 ≤ 1 / 32 * (P.sig1 * P.mu * Y ^ 4) := by
        have hh := mul_le_mul_of_nonneg_right hB4
          (by positivity : (0 : ℝ) ≤ P.mu * Y ^ 3)
        have hnn : (0 : ℝ) ≤ P.sig1 * P.mu * Y ^ 4 := by positivity
        linarith [hh, hnn]
      have b3 : P.sig1 * (27 / 10 * P.K1 * Y ^ 3) ≤ 1 / 32 * (P.sig1 * P.mu * Y ^ 4) := by
        have hh := mul_le_mul_of_nonneg_right hB5
          (by positivity : (0 : ℝ) ≤ P.sig1 * Y ^ 3)
        have hnn : (0 : ℝ) ≤ P.sig1 * P.mu * Y ^ 4 := by positivity
        linarith [hh, hnn]
      have hsum : 27 / 10 * P.K1D * Y ^ 3 + P.sig1 * (27 / 100 * P.mu / P.sig1 * Y ^ 3 +
          27 / 10 * P.K1 * Y ^ 3) ≤ 3 / 32 * (P.sig1 * P.mu * Y ^ 4) := by
        have hd : P.sig1 * (27 / 100 * P.mu / P.sig1 * Y ^ 3 + 27 / 10 * P.K1 * Y ^ 3) =
            27 / 100 * P.mu * Y ^ 3 + P.sig1 * (27 / 10 * P.K1 * Y ^ 3) := by
          field_simp
        rw [hd]
        linarith [b1, b2, b3]
      calc (27 / 10 * P.K1D * Y ^ 3 + P.sig1 * (27 / 100 * P.mu / P.sig1 * Y ^ 3 +
          27 / 10 * P.K1 * Y ^ 3)) * t ≤ (3 / 32 * (P.sig1 * P.mu * Y ^ 4)) * t :=
          mul_le_mul_of_nonneg_right hsum htpos.le
        _ = 3 / 32 * (P.sig1 * P.mu * (t * Y ^ 4)) := by ring
    calc ‖(M1D P (sGuess P n) - (P.sig1 : ℂ) * M1Num P (sGuess P n)) -
        (M1D P s - (P.sig1 : ℂ) * M1Num P s)‖ * t
        ≤ (27 / 10 * P.K1D * Y ^ 3 + P.sig1 * (27 / 100 * P.mu / P.sig1 * Y ^ 3 +
          27 / 10 * P.K1 * Y ^ 3)) * t := mul_le_mul_of_nonneg_right hinner htpos.le
      _ ≤ 3 / 32 * (P.sig1 * P.mu * (t * Y ^ 4)) := hbud
  have hM1Ds : ‖M1D P s - (P.sig1 : ℂ) * M1Num P s‖ ≤
      27 / 20 * P.K1D * Y ^ 3 + P.sig1 * (3 / 2 * P.mu * Y ^ 4 +
        27 / 20 * P.K1 * Y ^ 3) := by
    refine le_trans (norm_sub_le _ _) ?_
    have ha := M1D_norm_le P hP hM11 hsle
    have hb : ‖(P.sig1 : ℂ) * M1Num P s‖ ≤
        P.sig1 * (3 / 2 * P.mu * Y ^ 4 + 27 / 20 * P.K1 * Y ^ 3) := by
      rw [norm_real_mul hs1.le]
      refine mul_le_mul_of_nonneg_left ?_ hs1.le
      have hsub := M1Num_sub_norm_le P hP hM11 hsle
      have hlead : ‖((P.mu : ℝ) : ℂ) * s ^ 4‖ ≤ 3 / 2 * P.mu * Y ^ 4 := by
        rw [norm_real_mul hmu.le, norm_pow]
        have := pow_le_pow_left₀ (norm_nonneg s) hsle 4
        nlinarith [mul_le_mul_of_nonneg_left hq4 hmu.le,
          mul_le_mul_of_nonneg_left this hmu.le]
      have htri : ‖M1Num P s‖ ≤ ‖((P.mu : ℝ) : ℂ) * s ^ 4‖ +
          ‖M1Num P s - ((P.mu : ℝ) : ℂ) * s ^ 4‖ := by
        calc ‖M1Num P s‖ = ‖((P.mu : ℝ) : ℂ) * s ^ 4 +
            (M1Num P s - ((P.mu : ℝ) : ℂ) * s ^ 4)‖ := by congr 1; ring
          _ ≤ _ := norm_add_le _ _
      have e1 := mul_le_mul_of_nonneg_left hq3 hK10
      linarith [hsub, hlead, htri, e1]
    have e1 := mul_le_mul_of_nonneg_left hq3 hK1D0
    linarith [ha, hb]
  have hpd : ‖M1D P s - (P.sig1 : ℂ) * M1Num P s‖ * t * (1 / 10) ≤
      (3 / 20 + 1 / 32) * (P.sig1 * P.mu * (t * Y ^ 4)) := by
    have hbud : ‖M1D P s - (P.sig1 : ℂ) * M1Num P s‖ ≤
        (3 / 2 + 27 / (20 * 87) + 27 / (20 * 87)) * (P.sig1 * P.mu * Y ^ 4) := by
      have b1 : 27 / 20 * P.K1D * Y ^ 3 ≤ 27 / (20 * 87) * (P.sig1 * P.mu * Y ^ 4) := by
        have hh := mul_le_mul_of_nonneg_right hB3 (pow_nonneg hY0.le 3)
        linarith [hh]
      have b3 : P.sig1 * (27 / 20 * P.K1 * Y ^ 3) ≤
          27 / (20 * 87) * (P.sig1 * P.mu * Y ^ 4) := by
        have hh := mul_le_mul_of_nonneg_right hB5
          (by positivity : (0 : ℝ) ≤ P.sig1 * Y ^ 3)
        linarith [hh]
      have h := hM1Ds
      linarith [h, b1, b3]
    have hcoef : (3 / 2 + 27 / (20 * 87) + 27 / (20 * 87) : ℝ) * (1 / 10) ≤
        3 / 20 + 1 / 32 := by norm_num
    have hnn : (0 : ℝ) ≤ P.sig1 * P.mu * Y ^ 4 := by positivity
    calc ‖M1D P s - (P.sig1 : ℂ) * M1Num P s‖ * t * (1 / 10)
        ≤ ((3 / 2 + 27 / (20 * 87) + 27 / (20 * 87)) * (P.sig1 * P.mu * Y ^ 4)) * t *
          (1 / 10) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hbud htpos.le) ?_
          norm_num
      _ = ((3 / 2 + 27 / (20 * 87) + 27 / (20 * 87)) * (1 / 10)) *
          (P.sig1 * P.mu * (t * Y ^ 4)) := by ring
      _ ≤ (3 / 20 + 1 / 32) * (P.sig1 * P.mu * (t * Y ^ 4)) := by
          refine mul_le_mul_of_nonneg_right hcoef ?_
          positivity
  -- piece e: the `e^{-s(σ₀+σ₁)}` block
  have hM01u : ∀ u : ℂ, ‖u‖ ≤ 11 / 10 * Y →
      ‖M01D P u - ((P.sig0 + P.sig1 : ℝ) : ℂ) * M01Num P u‖ ≤
      (11 / 10 * P.K01D + 5 / 4 * (P.sig0 + P.sig1) * P.K01) * Y ^ 2 := by
    intro u hu
    refine le_trans (norm_sub_le _ _) ?_
    have ha := M01D_norm_le P hP hM11 hu
    have hb : ‖((P.sig0 + P.sig1 : ℝ) : ℂ) * M01Num P u‖ ≤
        (P.sig0 + P.sig1) * (P.K01 * (11 / 10 * Y) ^ 2) := by
      rw [norm_real_mul (by linarith : (0 : ℝ) ≤ P.sig0 + P.sig1)]
      exact mul_le_mul_of_nonneg_left (M01Num_norm_le P hP hM11 hu) (by linarith)
    have h12 : Y ≤ Y ^ 2 := by nlinarith
    have e1 : ‖M01D P u‖ ≤ 11 / 10 * P.K01D * Y ^ 2 := by
      have f2 : (0 : ℝ) ≤ P.K01D * Y ^ 2 := by positivity
      linarith [ha, mul_le_mul_of_nonneg_left h12 hK01D0, f2]
    have e2 : (P.sig0 + P.sig1) * (P.K01 * (11 / 10 * Y) ^ 2) ≤
        5 / 4 * (P.sig0 + P.sig1) * P.K01 * Y ^ 2 := by
      linarith [mul_le_mul_of_nonneg_left hq2
        (mul_nonneg (by linarith : (0 : ℝ) ≤ P.sig0 + P.sig1) hK010)]
    linarith [e1, e2]
  have hpe : ‖(M01D P (sGuess P n) - ((P.sig0 + P.sig1 : ℝ) : ℂ) *
      M01Num P (sGuess P n)) *
      Complex.exp (-(sGuess P n * ((P.sig0 + P.sig1 : ℝ) : ℂ))) -
      (M01D P s - ((P.sig0 + P.sig1 : ℝ) : ℂ) * M01Num P s) *
      Complex.exp (-(s * ((P.sig0 + P.sig1 : ℝ) : ℂ)))‖ ≤
      1 / 32 * (P.sig1 * P.mu * (t * Y ^ 4)) := by
    have hg := norm_mul_le_bound (hM01u (sGuess P n) hgle') (le_of_eq hE01g)
    have hss := norm_mul_le_bound (hM01u s hsle) hE01s
    have htot : ‖(M01D P (sGuess P n) - ((P.sig0 + P.sig1 : ℝ) : ℂ) *
        M01Num P (sGuess P n)) *
        Complex.exp (-(sGuess P n * ((P.sig0 + P.sig1 : ℝ) : ℂ))) -
        (M01D P s - ((P.sig0 + P.sig1 : ℝ) : ℂ) * M01Num P s) *
        Complex.exp (-(s * ((P.sig0 + P.sig1 : ℝ) : ℂ)))‖ ≤
        4 * ((11 / 10 * P.K01D + 5 / 4 * (P.sig0 + P.sig1) * P.K01) * Y ^ 2) * (t * X) := by
      refine le_trans (norm_sub_le _ _) ?_
      linarith [hg, hss]
    refine le_trans htot ?_
    have hgoal : 4 * (11 / 10 * P.K01D + 5 / 4 * (P.sig0 + P.sig1) * P.K01) * X ≤
        P.sig1 * P.mu / 32 * Y ^ 2 := by
      refine le_of_mul_le_mul_right ?_ hEpos
      have hup : 4 * (11 / 10 * P.K01D + 5 / 4 * (P.sig0 + P.sig1) * P.K01) * X * E =
          4 * (11 / 10 * P.K01D + 5 / 4 * (P.sig0 + P.sig1) * P.K01) * t := by
        rw [mul_assoc, hsplit]
      rw [hup]
      have hnn : (0 : ℝ) ≤ 4 * (11 / 10 * P.K01D + 5 / 4 * (P.sig0 + P.sig1) * P.K01) := by
        positivity
      have h2 := mul_le_mul_of_nonneg_left htup hnn
      have h3 : 4 * (11 / 10 * P.K01D + 5 / 4 * (P.sig0 + P.sig1) * P.K01) *
          (4 / P.mu * Y ^ 2) ≤ P.sig1 * P.mu / 32 * Y ^ 2 * E := by
        rw [show 4 * (11 / 10 * P.K01D + 5 / 4 * (P.sig0 + P.sig1) * P.K01) *
          (4 / P.mu * Y ^ 2) = (88 / 5 * P.K01D + 20 * (P.sig0 + P.sig1) * P.K01) *
          Y ^ 2 / P.mu by ring, div_le_iff₀ hmu]
        have h4 := mul_le_mul_of_nonneg_right hB6 (pow_nonneg hY0.le 2)
        nlinarith [h4]
      linarith [h2, h3]
    calc 4 * ((11 / 10 * P.K01D + 5 / 4 * (P.sig0 + P.sig1) * P.K01) * Y ^ 2) * (t * X)
        = (4 * (11 / 10 * P.K01D + 5 / 4 * (P.sig0 + P.sig1) * P.K01) * X) *
          (t * Y ^ 2) := by ring
      _ ≤ (P.sig1 * P.mu / 32 * Y ^ 2) * (t * Y ^ 2) := by
          refine mul_le_mul_of_nonneg_right hgoal ?_
          positivity
      _ = 1 / 32 * (P.sig1 * P.mu * (t * Y ^ 4)) := by ring
  -- assemble the five pieces
  set a1 : ℂ := McD P (sGuess P n) - McD P s with ha1
  set b1 : ℂ := (M0D P (sGuess P n) - (P.sig0 : ℂ) * M0Num P (sGuess P n)) *
    Complex.exp (-(sGuess P n * (P.sig0 : ℂ))) -
    (M0D P s - (P.sig0 : ℂ) * M0Num P s) * Complex.exp (-(s * (P.sig0 : ℂ))) with hb1
  set c1 : ℂ := ((M1D P (sGuess P n) - (P.sig1 : ℂ) * M1Num P (sGuess P n)) -
    (M1D P s - (P.sig1 : ℂ) * M1Num P s)) * ((t : ℝ) : ℂ) with hc1
  set d1 : ℂ := (M1D P s - (P.sig1 : ℂ) * M1Num P s) * ((t : ℝ) : ℂ) *
    (1 - Complex.exp (-((s - sGuess P n) * (P.sig1 : ℂ)))) with hd1
  set e1 : ℂ := (M01D P (sGuess P n) - ((P.sig0 + P.sig1 : ℝ) : ℂ) *
    M01Num P (sGuess P n)) *
    Complex.exp (-(sGuess P n * ((P.sig0 + P.sig1 : ℝ) : ℂ))) -
    (M01D P s - ((P.sig0 + P.sig1 : ℝ) : ℂ) * M01Num P s) *
    Complex.exp (-(s * ((P.sig0 + P.sig1 : ℝ) : ℂ))) with he1
  have hdecomp : WD P (sGuess P n) - WD P s = a1 + b1 + (c1 + d1) + e1 := by
    rw [ha1, hb1, hc1, hd1, he1]
    unfold WD
    rw [hPK, hE1split]
    ring
  have hd1norm : ‖d1‖ ≤ (3 / 20 + 1 / 32) * (P.sig1 * P.mu * (t * Y ^ 4)) := by
    rw [hd1]
    have hft : ‖((t : ℝ) : ℂ)‖ = t := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos]
    have h1m : ‖1 - Complex.exp (-((s - sGuess P n) * (P.sig1 : ℂ)))‖ ≤ 1 / 10 := by
      rw [norm_sub_rev]
      exact hEfac
    calc ‖(M1D P s - (P.sig1 : ℂ) * M1Num P s) * ((t : ℝ) : ℂ) *
        (1 - Complex.exp (-((s - sGuess P n) * (P.sig1 : ℂ))))‖
        = ‖M1D P s - (P.sig1 : ℂ) * M1Num P s‖ * t *
          ‖1 - Complex.exp (-((s - sGuess P n) * (P.sig1 : ℂ)))‖ := by
          rw [norm_mul, norm_mul, hft]
      _ ≤ ‖M1D P s - (P.sig1 : ℂ) * M1Num P s‖ * t * (1 / 10) := by
          refine mul_le_mul_of_nonneg_left h1m ?_
          positivity
      _ ≤ (3 / 20 + 1 / 32) * (P.sig1 * P.mu * (t * Y ^ 4)) := hpd
  rw [hdecomp]
  have u1 := norm_add_le (a1 + b1 + (c1 + d1)) e1
  have u2 := norm_add_le (a1 + b1) (c1 + d1)
  have u3 := norm_add_le a1 b1
  have u4 := norm_add_le c1 d1
  have hfin : (0 : ℝ) ≤ P.sig1 * P.mu * (t * Y ^ 4) := by positivity
  linarith [u1, u2, u3, u4, hpa, hpb, hpc, hd1norm, hpe, hfin]

set_option maxHeartbeats 2000000 in
/-- **`A(g)` lower bound, nonvanishing of the frozen derivative, and the chord step**:
with the residual bound `hWg` and the derivative lower bound `hWDg` as inputs, the
`−6W/s` correction is threshold-small, so `‖A(g)‖ ≥ (2/3)σ₁μtY⁴`, `F′(g) ≠ 0`, and
`‖F(g)/F′(g)‖ ≤ r(1−K)` for `r = 1/(20σ₁)`, `K = 3/4`. -/
theorem Ag_lower_and_step (P : MixParams) (hP : P.Phys) (n : ℕ) {Y : ℝ}
    (hYdef : Y = 2 * Real.pi * n / P.sig1)
    (h1 : 1 ≤ Y) (hMc2 : 2 * P.KMc ≤ Y) (hM12 : 2 * P.K1 ≤ P.mu * Y)
    (ht1 : 2 * (P.mu + P.K1) ≤ Y) (hB4 : 20 ≤ P.sig1 * Y)
    (hWg : ‖Wfun P (sGuess P n)‖ ≤ P.mu / 200 * (tRat P Y * Y ^ 4))
    (hWDg : 7 / 10 * (P.sig1 * P.mu * (tRat P Y * Y ^ 4)) ≤ ‖WD P (sGuess P n)‖) :
    2 / 3 * (P.sig1 * P.mu * (tRat P Y * Y ^ 4)) ≤
      ‖WD P (sGuess P n) - 6 * Wfun P (sGuess P n) / sGuess P n‖ ∧
    derivF P (sGuess P n) ≠ 0 ∧
    ‖P.detF (sGuess P n) / derivF P (sGuess P n)‖ ≤ 1 / (20 * P.sig1) * (1 - 3 / 4) := by
  have hs1 : 0 < P.sig1 := lt_trans hP.1 hP.2.1
  have hmu : 0 < P.mu := mul_pos (hP.2.2.1 1 1) (hP.2.2.2.1 1 1)
  have hK10 := K1_nonneg P hP
  have hKMc0 := KMc_nonneg P hP
  have hY0 : (0 : ℝ) < Y := lt_of_lt_of_le one_pos h1
  set t : ℝ := tRat P Y with htdef
  have hA : 0 < P.mu + P.K1 := by linarith
  have htlow : Y ^ 2 / (2 * (P.mu + P.K1)) ≤ t := tRat_lower P hP h1 hMc2 hM12
  have ht1' : 1 ≤ t := by
    have hYsq : Y ≤ Y ^ 2 := by nlinarith
    have h2A : 2 * (P.mu + P.K1) ≤ Y ^ 2 := by linarith
    have : 1 ≤ Y ^ 2 / (2 * (P.mu + P.K1)) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    linarith [htlow]
  have htpos : 0 < t := lt_of_lt_of_le one_pos ht1'
  have hg_ne : sGuess P n ≠ 0 := by
    intro h
    have him : (sGuess P n).im = Y := by rw [sGuess_im, ← hYdef]
    rw [h] at him
    simp only [Complex.zero_im] at him
    linarith
  have hgY : Y ≤ ‖sGuess P n‖ := by
    have h := sGuess_norm_ge P hs1 n
    rw [← hYdef] at h
    exact h
  -- the −6W/g correction is small
  have h6 : ‖6 * Wfun P (sGuess P n) / sGuess P n‖ ≤
      3 / 2000 * (P.sig1 * P.mu * (t * Y ^ 4)) := by
    rw [norm_div, norm_mul]
    have h6' : ‖(6 : ℂ)‖ = 6 := by norm_num
    rw [h6']
    have hnum : 6 * ‖Wfun P (sGuess P n)‖ ≤ 6 * (P.mu / 200 * (t * Y ^ 4)) := by
      linarith [hWg]
    have hdiv := FMSA.HardSphere.div_le_div_bound hnum (by positivity) hY0 hgY
    refine le_trans hdiv ?_
    rw [div_le_iff₀ hY0]
    have hb4' := mul_le_mul_of_nonneg_right hB4
      (by positivity : (0 : ℝ) ≤ P.mu * (t * Y ^ 4))
    nlinarith [hb4']
  have htri : ‖WD P (sGuess P n)‖ - ‖6 * Wfun P (sGuess P n) / sGuess P n‖ ≤
      ‖WD P (sGuess P n) - 6 * Wfun P (sGuess P n) / sGuess P n‖ :=
    norm_sub_norm_le _ _
  have hAg : 2 / 3 * (P.sig1 * P.mu * (t * Y ^ 4)) ≤
      ‖WD P (sGuess P n) - 6 * Wfun P (sGuess P n) / sGuess P n‖ := by
    have hnn : (0 : ℝ) ≤ P.sig1 * P.mu * (t * Y ^ 4) := by positivity
    linarith [hWDg, h6, htri]
  have hAg_pos : 0 < ‖WD P (sGuess P n) - 6 * Wfun P (sGuess P n) / sGuess P n‖ := by
    have hnn : (0 : ℝ) < P.sig1 * P.mu * (t * Y ^ 4) := by positivity
    linarith [hAg]
  have hAg_ne : WD P (sGuess P n) - 6 * Wfun P (sGuess P n) / sGuess P n ≠ 0 :=
    norm_pos_iff.mp hAg_pos
  have hFp_ne : derivF P (sGuess P n) ≠ 0 := by
    unfold derivF
    exact div_ne_zero hAg_ne (pow_ne_zero 6 hg_ne)
  refine ⟨hAg, hFp_ne, ?_⟩
  -- the chord step
  have hdetFg : P.detF (sGuess P n) = Wfun P (sGuess P n) / sGuess P n ^ 6 := by
    rw [eq_div_iff (pow_ne_zero 6 hg_ne), mul_comm]
    exact detC_monomial_eq P hg_ne
  have hratio : P.detF (sGuess P n) / derivF P (sGuess P n) =
      Wfun P (sGuess P n) / (WD P (sGuess P n) - 6 * Wfun P (sGuess P n) / sGuess P n) := by
    rw [hdetFg]
    unfold derivF
    rw [div_div_div_cancel_right₀]
    exact pow_ne_zero 6 hg_ne
  rw [hratio, norm_div]
  have hdiv := FMSA.HardSphere.div_le_div_bound hWg (by positivity)
    (by positivity : (0 : ℝ) < 2 / 3 * (P.sig1 * P.mu * (t * Y ^ 4))) hAg
  refine le_trans hdiv ?_
  have heq : P.mu / 200 * (t * Y ^ 4) / (2 / 3 * (P.sig1 * P.mu * (t * Y ^ 4))) =
      3 / (400 * P.sig1) := by
    field_simp
    ring
  rw [heq]
  have hs1 : 0 < P.sig1 := lt_trans hP.1 hP.2.1
  have hrw : 1 / (20 * P.sig1) * (1 - 3 / 4) = 5 / (400 * P.sig1) := by
    rw [div_mul_eq_mul_div, div_eq_div_iff (by positivity) (by positivity)]
    ring
  rw [hrw, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hs1.le]

/-- Pure algebraic split of the chord quantity `1 - (B/x⁶)/(A/y⁶)`. -/
private theorem chord_algebra_split (A B x y : ℂ) (hA : A ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0) :
    1 - (B / x ^ 6) / (A / y ^ 6) = (A - B) / A + (B / A) * (1 - y ^ 6 / x ^ 6) := by
  have hx6 : x ^ 6 ≠ 0 := pow_ne_zero _ hx
  have hy6 : y ^ 6 ≠ 0 := pow_ne_zero _ hy
  field_simp
  ring

set_option maxHeartbeats 4000000 in
-- Raised limit: one pass assembles the full disk chord estimate from ~10 sub-bounds.
/-- **The chord contraction bound**: on the radius-`1/(20σ₁)` disk around the guess,
`‖1 − F′(s)/F′(g)‖ ≤ 3/4`, from the `A`-variation and the `g⁶/s⁶` factor. -/
theorem chord_bound_at (P : MixParams) (hP : P.Phys) (n : ℕ) {Y : ℝ}
    (hYdef : Y = 2 * Real.pi * n / P.sig1)
    (h1 : 1 ≤ Y) (hMc2 : 2 * P.KMc ≤ Y) (hM12 : 2 * P.K1 ≤ P.mu * Y)
    (ht1 : 2 * (P.mu + P.K1) ≤ Y)
    (hLcap : 40 * Real.log (tRat P Y) ≤ P.sig1 * Y)
    (hrcY : 2 / P.sig1 ≤ Y) (hB4 : 20 ≤ P.sig1 * Y)
    (hB7 : 224 * P.KW ≤ P.sig1 * P.mu * Y)
    (hWg : ‖Wfun P (sGuess P n)‖ ≤ P.mu / 200 * (tRat P Y * Y ^ 4))
    (hAg : 2 / 3 * (P.sig1 * P.mu * (tRat P Y * Y ^ 4)) ≤
      ‖WD P (sGuess P n) - 6 * Wfun P (sGuess P n) / sGuess P n‖)
    {s : ℂ} (hs : s ∈ Metric.closedBall (sGuess P n) (1 / (20 * P.sig1)))
    (hVar : ‖WD P (sGuess P n) - WD P s‖ ≤ 3 / 8 * (P.sig1 * P.mu * (tRat P Y * Y ^ 4)))
    (hWs : ‖Wfun P s‖ ≤ P.KW * (tRat P Y * Y ^ 4)) :
    ‖1 - derivF P s / derivF P (sGuess P n)‖ ≤ 3 / 4 := by
  have hs1 : 0 < P.sig1 := lt_trans hP.1 hP.2.1
  have hmu : 0 < P.mu := mul_pos (hP.2.2.1 1 1) (hP.2.2.2.1 1 1)
  have hK10 := K1_nonneg P hP
  have hKMc0 := KMc_nonneg P hP
  have hY0 : (0 : ℝ) < Y := lt_of_lt_of_le one_pos h1
  set t : ℝ := tRat P Y with htdef
  set L : ℝ := Real.log t with hLdef
  have hA : 0 < P.mu + P.K1 := by linarith
  have htlow : Y ^ 2 / (2 * (P.mu + P.K1)) ≤ t := tRat_lower P hP h1 hMc2 hM12
  have ht1' : 1 ≤ t := by
    have hYsq : Y ≤ Y ^ 2 := by nlinarith
    have h2A : 2 * (P.mu + P.K1) ≤ Y ^ 2 := by linarith
    have : 1 ≤ Y ^ 2 / (2 * (P.mu + P.K1)) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    linarith [htlow]
  have htpos : 0 < t := lt_of_lt_of_le one_pos ht1'
  have h0L : 0 ≤ L := by rw [hLdef]; exact Real.log_nonneg ht1'
  have hgle : ‖sGuess P n‖ ≤ 21 / 20 * Y := by
    have h := sGuess_norm_le P hs1 n (by rw [← hYdef, ← htdef, ← hLdef]; exact h0L)
      (by rw [← hYdef, ← htdef, ← hLdef]; exact hLcap)
    rw [← hYdef] at h
    nlinarith [h, hY0.le]
  have hgle' : ‖sGuess P n‖ ≤ 11 / 10 * Y := by linarith
  have hgY : Y ≤ ‖sGuess P n‖ := by
    have h := sGuess_norm_ge P hs1 n
    rw [← hYdef] at h
    exact h
  have hgim : (sGuess P n).im = Y := by rw [sGuess_im, ← hYdef]
  have hg_ne : sGuess P n ≠ 0 := by
    intro h
    rw [h] at hgim
    simp only [Complex.zero_im] at hgim
    linarith
  have hrcY' : 2 ≤ P.sig1 * Y := by
    rw [div_le_iff₀ hs1] at hrcY
    linarith [hrcY]
  have hrc : 1 / (20 * P.sig1) ≤ Y / 40 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 40)]
    nlinarith [hrcY']
  have hsle : ‖s‖ ≤ 11 / 10 * Y := disk_norm_le hY0.le hgle hrc hs
  have hsge : 39 / 40 * Y ≤ ‖s‖ := disk_norm_ge hY0.le hgim hrc hs
  have hs_ne : s ≠ 0 := disk_ne_zero h1 hgim hrc hs
  have hgs : ‖s - sGuess P n‖ ≤ 1 / (20 * P.sig1) := by
    rw [← dist_eq_norm]
    exact Metric.mem_closedBall.mp hs
  have hKW0 : 0 ≤ P.KW := by
    have h1' := K0_nonneg P hP
    have h2' := K01_nonneg P hP
    unfold MixParams.KW
    positivity
  have hLam : (0 : ℝ) < P.sig1 * P.mu * (t * Y ^ 4) := by positivity
  -- the two −6W/u corrections
  have h6g : ‖6 * Wfun P (sGuess P n) / sGuess P n‖ ≤
      3 / 2000 * (P.sig1 * P.mu * (t * Y ^ 4)) := by
    rw [norm_div, norm_mul, show ‖(6 : ℂ)‖ = 6 by norm_num]
    have hnum : 6 * ‖Wfun P (sGuess P n)‖ ≤ 6 * (P.mu / 200 * (t * Y ^ 4)) := by
      linarith [hWg]
    refine le_trans (FMSA.HardSphere.div_le_div_bound hnum (by positivity) hY0 hgY) ?_
    rw [div_le_iff₀ hY0]
    have hb4' := mul_le_mul_of_nonneg_right hrcY'
      (by positivity : (0 : ℝ) ≤ P.mu * (t * Y ^ 4))
    nlinarith [hb4']
  have h6s : ‖6 * Wfun P s / s‖ ≤ 1 / 32 * (P.sig1 * P.mu * (t * Y ^ 4)) := by
    rw [norm_div, norm_mul, show ‖(6 : ℂ)‖ = 6 by norm_num]
    have hnum : 6 * ‖Wfun P s‖ ≤ 6 * (P.KW * (t * Y ^ 4)) := by linarith [hWs]
    refine le_trans (FMSA.HardSphere.div_le_div_bound hnum (by positivity)
      (by positivity : (0 : ℝ) < 39 / 40 * Y) hsge) ?_
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 39 / 40 * Y)]
    have hb7' := mul_le_mul_of_nonneg_right hB7
      (by positivity : (0 : ℝ) ≤ t * Y ^ 4)
    have hnn : (0 : ℝ) ≤ P.sig1 * P.mu * Y * (t * Y ^ 4) := by positivity
    nlinarith [hb7']
  -- A-variation
  have hAvar : ‖(WD P (sGuess P n) - 6 * Wfun P (sGuess P n) / sGuess P n) -
      (WD P s - 6 * Wfun P s / s)‖ ≤ 5 / 12 * (P.sig1 * P.mu * (t * Y ^ 4)) := by
    have hre : (WD P (sGuess P n) - 6 * Wfun P (sGuess P n) / sGuess P n) -
        (WD P s - 6 * Wfun P s / s) =
        (WD P (sGuess P n) - WD P s) -
          (6 * Wfun P (sGuess P n) / sGuess P n - 6 * Wfun P s / s) := by ring
    rw [hre]
    refine le_trans (norm_sub_le _ _) ?_
    have h2 := norm_sub_le (6 * Wfun P (sGuess P n) / sGuess P n) (6 * Wfun P s / s)
    linarith [hVar, h6g, h6s, h2]
  have hAg_pos : 0 < ‖WD P (sGuess P n) - 6 * Wfun P (sGuess P n) / sGuess P n‖ := by
    linarith [hAg, hLam]
  have hAg_ne : WD P (sGuess P n) - 6 * Wfun P (sGuess P n) / sGuess P n ≠ 0 :=
    norm_pos_iff.mp hAg_pos
  -- the algebraic split of the chord quantity
  have hID : 1 - derivF P s / derivF P (sGuess P n) =
      ((WD P (sGuess P n) - 6 * Wfun P (sGuess P n) / sGuess P n) -
        (WD P s - 6 * Wfun P s / s)) /
        (WD P (sGuess P n) - 6 * Wfun P (sGuess P n) / sGuess P n) +
      ((WD P s - 6 * Wfun P s / s) /
        (WD P (sGuess P n) - 6 * Wfun P (sGuess P n) / sGuess P n)) *
        (1 - sGuess P n ^ 6 / s ^ 6) := by
    unfold derivF
    exact chord_algebra_split _ _ _ _ hAg_ne hs_ne hg_ne
  -- the three norm ingredients
  have r1 : ‖((WD P (sGuess P n) - 6 * Wfun P (sGuess P n) / sGuess P n) -
      (WD P s - 6 * Wfun P s / s)) /
      (WD P (sGuess P n) - 6 * Wfun P (sGuess P n) / sGuess P n)‖ ≤ 5 / 8 := by
    rw [norm_div, div_le_iff₀ hAg_pos]
    nlinarith [hAvar, hAg]
  have r2 : ‖(WD P s - 6 * Wfun P s / s) /
      (WD P (sGuess P n) - 6 * Wfun P (sGuess P n) / sGuess P n)‖ ≤ 13 / 8 := by
    rw [norm_div, div_le_iff₀ hAg_pos]
    have htri : ‖WD P s - 6 * Wfun P s / s‖ ≤
        ‖WD P (sGuess P n) - 6 * Wfun P (sGuess P n) / sGuess P n‖ +
        ‖(WD P (sGuess P n) - 6 * Wfun P (sGuess P n) / sGuess P n) -
          (WD P s - 6 * Wfun P s / s)‖ := by
      calc ‖WD P s - 6 * Wfun P s / s‖
          = ‖(WD P (sGuess P n) - 6 * Wfun P (sGuess P n) / sGuess P n) -
            ((WD P (sGuess P n) - 6 * Wfun P (sGuess P n) / sGuess P n) -
              (WD P s - 6 * Wfun P s / s))‖ := by congr 1; ring
        _ ≤ _ := norm_sub_le _ _
    nlinarith [htri, hAvar, hAg]
  have r3 : ‖1 - sGuess P n ^ 6 / s ^ 6‖ ≤ 1 / 32 := by
    have hfrac : (1 : ℂ) - sGuess P n ^ 6 / s ^ 6 = (s ^ 6 - sGuess P n ^ 6) / s ^ 6 := by
      field_simp
    rw [hfrac, norm_div, norm_pow]
    have hnum : ‖s ^ 6 - sGuess P n ^ 6‖ ≤ Y ^ 5 / (2 * P.sig1) := by
      have h := pow_six_sub_norm_le s (sGuess P n) hsle hgle'
      have hq5 : (11 / 10 * Y) ^ 5 ≤ 5 / 3 * Y ^ 5 := by nlinarith [pow_nonneg hY0.le 5]
      have e1 : 6 * (11 / 10 * Y) ^ 5 * ‖s - sGuess P n‖ ≤
          (10 * Y ^ 5) * (1 / (20 * P.sig1)) := by
        refine mul_le_mul ?_ hgs (norm_nonneg _) (by positivity)
        linarith [hq5]
      calc ‖s ^ 6 - sGuess P n ^ 6‖ ≤ 6 * (11 / 10 * Y) ^ 5 * ‖s - sGuess P n‖ := h
        _ ≤ (10 * Y ^ 5) * (1 / (20 * P.sig1)) := e1
        _ = Y ^ 5 / (2 * P.sig1) := by field_simp; ring
    have hden : (39 / 40 * Y) ^ 6 ≤ ‖s‖ ^ 6 :=
      pow_le_pow_left₀ (by positivity) hsge 6
    refine le_trans (FMSA.HardSphere.div_le_div_bound hnum (by positivity)
      (by positivity : (0 : ℝ) < (39 / 40 * Y) ^ 6) hden) ?_
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (39 / 40 * Y) ^ 6),
      div_le_iff₀ (by positivity : (0 : ℝ) < 2 * P.sig1)] at *
    have e1 : (4 / 5 : ℝ) ≤ (39 / 40) ^ 6 := by norm_num
    have e2 := mul_le_mul_of_nonneg_right hrcY' (pow_nonneg hY0.le 5)
    nlinarith [mul_le_mul e1 e2 (by positivity) (by positivity),
      pow_nonneg hY0.le 5, hs1.le]
  rw [hID]
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_mul]
  have r23 : ‖(WD P s - 6 * Wfun P s / s) /
      (WD P (sGuess P n) - 6 * Wfun P (sGuess P n) / sGuess P n)‖ *
      ‖1 - sGuess P n ^ 6 / s ^ 6‖ ≤ 13 / 8 * (1 / 32) :=
    mul_le_mul r2 r3 (norm_nonneg _) (by norm_num)
  linarith [r1, r23]


/-! ### The threshold/eventually pass -/

/-- Threshold transfer through a dominating sum: if `c/m ≤ S` and `S ≤ E`, then `c ≤ m·E`. -/
private theorem thresh_of_sum {c m E S : ℝ} (hm : 0 < m) (hS : S ≤ E) (hcS : c / m ≤ S) :
    c ≤ m * E := by
  have h1 : c / m ≤ E := le_trans hcS hS
  rw [div_le_iff₀ hm] at h1
  linarith [mul_comm m E]

set_option maxHeartbeats 4000000 in
-- Raised limit: one pass bundles ~14 eventual thresholds with the five core disk estimates.
/-- **All chord-family conditions hold eventually**: beyond an explicit index threshold `N`,
the frozen derivative at `sGuess P n` is nonzero, the chord bound `‖1 − F′(s)/F′(g)‖ ≤ 3/4`
holds on the disk of radius `1/(20σ₁)`, and the chord step satisfies
`‖F(g)/F′(g)‖ ≤ (1/(20σ₁))·(1 − 3/4)`.  The thresholds come in three flavours: linear ones
`c ≤ m·Y` (bundled via `Filter.eventually_ge_atTop`), sublinear log caps
`c·log t(Y) ≤ m·Y` (via `eventually_log_cap` and `tRat_upper`), and the exponential budgets
`c ≤ m·t(Y)^δ` (via `tRat_lower` ⇒ `t ≥ Y` and `Real.add_one_le_exp`). -/
theorem chord_conditions_eventually (P : MixParams) (hP : P.Phys) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      derivF P (sGuess P n) ≠ 0 ∧
      (∀ s ∈ Metric.closedBall (sGuess P n) (1 / (20 * P.sig1)), s ≠ 0) ∧
      (∀ s ∈ Metric.closedBall (sGuess P n) (1 / (20 * P.sig1)),
        ‖1 - derivF P s / derivF P (sGuess P n)‖ ≤ 3 / 4) ∧
      ‖P.detF (sGuess P n) / derivF P (sGuess P n)‖ ≤
        1 / (20 * P.sig1) * (1 - 3 / 4) ∧
      1 ≤ 2 * Real.pi * n / P.sig1 ∧
      2 * P.KMc ≤ 2 * Real.pi * n / P.sig1 ∧
      2 * P.K1 ≤ P.mu * (2 * Real.pi * n / P.sig1) ∧
      2 * (P.mu + P.K1) ≤ 2 * Real.pi * n / P.sig1 ∧
      40 * Real.log (tRat P (2 * Real.pi * n / P.sig1)) ≤
        P.sig1 * (2 * Real.pi * n / P.sig1) ∧
      2 / 3 * (P.sig1 * P.mu * (tRat P (2 * Real.pi * n / P.sig1) *
          (2 * Real.pi * n / P.sig1) ^ 4)) ≤
        ‖WD P (sGuess P n) - 6 * Wfun P (sGuess P n) / sGuess P n‖ := by
  have hs0 : 0 < P.sig0 := hP.1
  have hs01 : P.sig0 < P.sig1 := hP.2.1
  have hs1 : 0 < P.sig1 := lt_trans hs0 hs01
  have hmu : 0 < P.mu := mul_pos (hP.2.2.1 1 1) (hP.2.2.2.1 1 1)
  have hK10 := K1_nonneg P hP
  have hKMc0 := KMc_nonneg P hP
  have hK00 := K0_nonneg P hP
  have hK010 := K01_nonneg P hP
  have hKMcD0 := KMcD_nonneg P hP
  have hK1D0 := K1D_nonneg P hP
  have hK0D0 := K0D_nonneg P hP
  have hK01D0 := K01D_nonneg P hP
  have hA : 0 < P.mu + P.K1 := by linarith
  have hAne : P.mu + P.K1 ≠ 0 := hA.ne'
  have hKIm0 : 0 ≤ P.KIm := by
    unfold MixParams.KIm
    linarith [mul_nonneg hmu.le hKMc0, mul_nonneg hKMc0 hK10]
  have hKW0 : 0 ≤ P.KW := by
    unfold MixParams.KW
    have h1 : (0 : ℝ) ≤ 15 * P.K01 / P.mu := div_nonneg (by linarith) hmu.le
    linarith
  have hd0 : 0 < (P.sig1 - P.sig0) / P.sig1 := div_pos (by linarith) hs1
  -- the exponential budget: one sum dominating all six `e^{δ·log t}` thresholds
  set Emax : ℝ := 2500 * P.K0 / P.mu + 16000 * P.K01 / P.mu ^ 2 +
    (30 * P.K0D + 25 * P.sig0 * P.K0) / (P.sig1 * P.mu) +
    (88 * P.K01D + 160 * (P.sig0 + P.sig1) * P.K01) / (P.sig1 * P.mu ^ 2) +
    (173 * P.K0D + 192 * P.sig0 * P.K0) / (P.sig1 * P.mu) +
    (564 * P.K01D + 640 * (P.sig0 + P.sig1) * P.K01) / (P.sig1 * P.mu ^ 2) with hEmax
  have hs0K0 : (0 : ℝ) ≤ P.sig0 * P.K0 := mul_nonneg hs0.le hK00
  have hs01K01 : (0 : ℝ) ≤ (P.sig0 + P.sig1) * P.K01 := mul_nonneg (by linarith) hK010
  have hq1 : (0 : ℝ) ≤ 2500 * P.K0 / P.mu := div_nonneg (by linarith) hmu.le
  have hq2 : (0 : ℝ) ≤ 16000 * P.K01 / P.mu ^ 2 := div_nonneg (by linarith) (by positivity)
  have hsm : (0 : ℝ) < P.sig1 * P.mu := mul_pos hs1 hmu
  have hsm2 : (0 : ℝ) < P.sig1 * P.mu ^ 2 := mul_pos hs1 (pow_pos hmu 2)
  have hq3 : (0 : ℝ) ≤ (30 * P.K0D + 25 * P.sig0 * P.K0) / (P.sig1 * P.mu) :=
    div_nonneg (by linarith) hsm.le
  have hq4 : (0 : ℝ) ≤ (88 * P.K01D + 160 * (P.sig0 + P.sig1) * P.K01) / (P.sig1 * P.mu ^ 2) :=
    div_nonneg (by linarith) hsm2.le
  have hq5 : (0 : ℝ) ≤ (173 * P.K0D + 192 * P.sig0 * P.K0) / (P.sig1 * P.mu) :=
    div_nonneg (by linarith) hsm.le
  have hq6 : (0 : ℝ) ≤ (564 * P.K01D + 640 * (P.sig0 + P.sig1) * P.K01) / (P.sig1 * P.mu ^ 2) :=
    div_nonneg (by linarith) hsm2.le
  -- the sublinear log-cap parameter
  set ε : ℝ := min (P.sig1 / 40) (min (P.sig1 * P.mu / (32000 * (P.mu + P.K1)))
    (P.sig1 / 18800)) with hεdef
  have hε0 : 0 < ε := by
    rw [hεdef]
    exact lt_min (by linarith) (lt_min (div_pos hsm (by linarith)) (by linarith))
  have hε40 : ε ≤ P.sig1 / 40 := by rw [hεdef]; exact min_le_left _ _
  have hε32 : ε ≤ P.sig1 * P.mu / (32000 * (P.mu + P.K1)) := by
    rw [hεdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hε18 : ε ≤ P.sig1 / 18800 := by
    rw [hεdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hlogcap := FMSA.HardSphere.eventually_log_cap (Real.log (4 / P.mu)) ε hε0
  -- the eventual thresholds, already in multiplied form
  have hev : ∀ᶠ Y : ℝ in Filter.atTop, (1 ≤ Y) ∧ (2 * P.KMc ≤ Y) ∧
      (2 * (P.mu + P.K1) ≤ Y) ∧ (2 / P.sig1 ≤ Y) ∧ (20 ≤ P.sig1 * Y) ∧
      (P.KIm ≤ P.mu * Y) ∧ (12000 * P.KMc * (P.mu + P.K1) ≤ P.mu * Y) ∧
      (9600 * P.K1 ≤ P.mu * Y) ∧ (16000 * P.KIm * (P.mu + P.K1) ≤ P.mu ^ 2 * Y) ∧
      (214 * P.KMcD * (P.mu + P.K1) ≤ P.sig1 * P.mu * Y) ∧
      (87 * P.K1D ≤ P.sig1 * P.mu * Y) ∧ (224 * P.KW ≤ P.sig1 * P.mu * Y) ∧
      (Real.exp (Emax / ((P.sig1 - P.sig0) / P.sig1)) ≤ Y) ∧
      (Real.log (4 / P.mu) + 2 * Real.log Y ≤ ε * Y) := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ),
      Filter.eventually_ge_atTop (2 * P.KMc),
      Filter.eventually_ge_atTop (2 * (P.mu + P.K1)),
      Filter.eventually_ge_atTop (20 / P.sig1),
      Filter.eventually_ge_atTop (P.KIm / P.mu),
      Filter.eventually_ge_atTop (12000 * P.KMc * (P.mu + P.K1) / P.mu),
      Filter.eventually_ge_atTop (9600 * P.K1 / P.mu),
      Filter.eventually_ge_atTop (16000 * P.KIm * (P.mu + P.K1) / P.mu ^ 2),
      Filter.eventually_ge_atTop (214 * P.KMcD * (P.mu + P.K1) / (P.sig1 * P.mu)),
      Filter.eventually_ge_atTop (87 * P.K1D / (P.sig1 * P.mu)),
      Filter.eventually_ge_atTop (224 * P.KW / (P.sig1 * P.mu)),
      Filter.eventually_ge_atTop (Real.exp (Emax / ((P.sig1 - P.sig0) / P.sig1))),
      hlogcap] with Y g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13
    rw [div_le_iff₀ hs1] at g4
    rw [div_le_iff₀ hmu] at g5 g6 g7
    rw [div_le_iff₀ (pow_pos hmu 2)] at g8
    rw [div_le_iff₀ hsm] at g9 g10 g11
    have hcs : P.sig1 * Y = Y * P.sig1 := mul_comm _ _
    have hcm : P.mu * Y = Y * P.mu := mul_comm _ _
    have hcm2 : P.mu ^ 2 * Y = Y * P.mu ^ 2 := mul_comm _ _
    have hcsm : P.sig1 * P.mu * Y = Y * (P.sig1 * P.mu) := mul_comm _ _
    refine ⟨g1, g2, g3, ?_, by linarith, by linarith, by linarith, by linarith, by linarith,
      by linarith, by linarith, by linarith, g12, g13⟩
    rw [div_le_iff₀ hs1]; linarith
  -- push the thresholds along `n ↦ 2πn/σ₁ → ∞`
  have htends : Filter.Tendsto (fun n : ℕ => 2 * Real.pi * (n : ℝ) / P.sig1)
      Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_div_const hs1
      (Filter.Tendsto.const_mul_atTop (by positivity : (0 : ℝ) < 2 * Real.pi)
        tendsto_natCast_atTop_atTop)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (htends.eventually hev)
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨h1, hMc2, ht1, hrcY, hB4, hre, hT1, hT2, hT0, hB1, hB3, hB7, hEY, hlogY⟩ := hN n hn
  set Y : ℝ := 2 * Real.pi * (n : ℝ) / P.sig1 with hYdef
  have hY0 : (0 : ℝ) < Y := lt_of_lt_of_le one_pos h1
  have hM12 : 2 * P.K1 ≤ P.mu * Y := by linarith
  have hD1 : 12 * P.K1 ≤ P.mu * Y := by linarith
  have hB5 : 87 * P.K1 ≤ P.mu * Y := by linarith
  have hD4 : 24 * P.K1D ≤ P.sig1 * P.mu * Y := by linarith
  have hD2 : 54 * P.KMcD * (P.mu + P.K1) ≤ P.sig1 * P.mu * Y := by
    linarith [mul_nonneg hKMcD0 hA.le]
  have hgim : (sGuess P n).im = Y := by rw [sGuess_im, hYdef]
  have hrc40 : 1 / (20 * P.sig1) ≤ Y / 40 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    rw [div_le_iff₀ hs1] at hrcY
    linarith
  -- the ratio envelope and the sublinear log caps
  have htlow := tRat_lower P hP h1 hMc2 hM12
  have htY : Y ≤ tRat P Y := by
    have hle : Y ≤ Y ^ 2 / (2 * (P.mu + P.K1)) := by
      rw [le_div_iff₀ (by linarith)]
      nlinarith [mul_le_mul_of_nonneg_left ht1 hY0.le]
    linarith
  have htpos : 0 < tRat P Y := lt_of_lt_of_le hY0 htY
  have htup := tRat_upper P hP h1 (by linarith) hM12
  have hlogle : Real.log (tRat P Y) ≤ Real.log (4 / P.mu) + 2 * Real.log Y := by
    have hh := Real.log_le_log htpos htup
    rw [Real.log_mul (div_pos (by norm_num : (0 : ℝ) < 4) hmu).ne' (pow_ne_zero 2 hY0.ne'),
      Real.log_pow] at hh
    push_cast at hh
    linarith
  have hLmax : Real.log (tRat P Y) ≤ ε * Y := by linarith
  have hmul1 := mul_le_mul_of_nonneg_right hε40 hY0.le
  have hmul2 := mul_le_mul_of_nonneg_right hε32 hY0.le
  have hmul3 := mul_le_mul_of_nonneg_right hε18 hY0.le
  have hLcap : 40 * Real.log (tRat P Y) ≤ P.sig1 * Y := by
    have hrw : P.sig1 / 40 * Y = P.sig1 * Y / 40 := by ring
    linarith
  have hL3 : 18800 * Real.log (tRat P Y) ≤ P.sig1 * Y := by
    have hrw : P.sig1 / 18800 * Y = P.sig1 * Y / 18800 := by ring
    linarith
  have hL2 : 32000 * (P.mu + P.K1) * Real.log (tRat P Y) ≤ P.sig1 * P.mu * Y := by
    have hstep2 : Real.log (tRat P Y) ≤ P.sig1 * P.mu / (32000 * (P.mu + P.K1)) * Y := by
      linarith
    have hh := mul_le_mul_of_nonneg_left hstep2 (by linarith : (0 : ℝ) ≤ 32000 * (P.mu + P.K1))
    rwa [show 32000 * (P.mu + P.K1) * (P.sig1 * P.mu / (32000 * (P.mu + P.K1)) * Y)
      = P.sig1 * P.mu * Y by field_simp] at hh
  -- the exponential budgets
  have hEbig : Emax ≤ Real.exp ((P.sig1 - P.sig0) / P.sig1 * Real.log (tRat P Y)) := by
    have hlogYge : Emax / ((P.sig1 - P.sig0) / P.sig1) ≤ Real.log Y := by
      have hh := Real.log_le_log (Real.exp_pos _) hEY
      rwa [Real.log_exp] at hh
    rw [div_le_iff₀ hd0] at hlogYge
    have hmono : (P.sig1 - P.sig0) / P.sig1 * Real.log Y ≤
        (P.sig1 - P.sig0) / P.sig1 * Real.log (tRat P Y) :=
      mul_le_mul_of_nonneg_left (Real.log_le_log hY0 htY) hd0.le
    have hexp := Real.add_one_le_exp ((P.sig1 - P.sig0) / P.sig1 * Real.log (tRat P Y))
    linarith [mul_comm ((P.sig1 - P.sig0) / P.sig1) (Real.log Y)]
  have hE0 : 2500 * P.K0 ≤
      P.mu * Real.exp ((P.sig1 - P.sig0) / P.sig1 * Real.log (tRat P Y)) :=
    thresh_of_sum hmu hEbig (by rw [hEmax]; linarith)
  have hE01 : 16000 * P.K01 ≤
      P.mu ^ 2 * Real.exp ((P.sig1 - P.sig0) / P.sig1 * Real.log (tRat P Y)) :=
    thresh_of_sum (pow_pos hmu 2) hEbig (by rw [hEmax]; linarith)
  have hD3 : 30 * P.K0D + 25 * P.sig0 * P.K0 ≤
      P.sig1 * P.mu * Real.exp ((P.sig1 - P.sig0) / P.sig1 * Real.log (tRat P Y)) :=
    thresh_of_sum hsm hEbig (by rw [hEmax]; linarith)
  have hD5 : 88 * P.K01D + 160 * (P.sig0 + P.sig1) * P.K01 ≤
      P.sig1 * P.mu ^ 2 * Real.exp ((P.sig1 - P.sig0) / P.sig1 * Real.log (tRat P Y)) :=
    thresh_of_sum hsm2 hEbig (by rw [hEmax]; linarith)
  have hB2 : 173 * P.K0D + 192 * P.sig0 * P.K0 ≤
      P.sig1 * P.mu * Real.exp ((P.sig1 - P.sig0) / P.sig1 * Real.log (tRat P Y)) :=
    thresh_of_sum hsm hEbig (by rw [hEmax]; linarith)
  have hB6 : 564 * P.K01D + 640 * (P.sig0 + P.sig1) * P.K01 ≤
      P.sig1 * P.mu ^ 2 * Real.exp ((P.sig1 - P.sig0) / P.sig1 * Real.log (tRat P Y)) :=
    thresh_of_sum hsm2 hEbig (by rw [hEmax]; linarith)
  -- the five core estimates
  have hWg := Wfun_at_sGuess_le P hP n hYdef h1 hMc2 hM12 hre ht1 hLcap hT0 hT1 hT2 hL2 hL3
    hE0 hE01
  have hWDg := WD_at_sGuess_lower P hP n hYdef h1 hMc2 hM12 ht1 hLcap hD1 hD2 hD3 hD4 hD5
  have hAgstep := Ag_lower_and_step P hP n hYdef h1 hMc2 hM12 ht1 hB4 hWg hWDg
  refine ⟨hAgstep.2.1, fun s hs => disk_ne_zero h1 hgim hrc40 hs, fun s hs => ?_,
    hAgstep.2.2, h1, hMc2, hM12, ht1, hLcap, hAgstep.1⟩
  have hWs := Wfun_on_disk_le P hP n hYdef h1 hMc2 hM12 ht1 hLcap hrcY hs
  have hVar := WD_var_on_disk_le P hP n hYdef h1 hMc2 hM12 ht1 hLcap hrcY hB1 hB2 hB3 hB4 hB5
    hB6 hs
  exact chord_bound_at P hP n hYdef h1 hMc2 hM12 ht1 hLcap hrcY hB4 hB7 hWg hAgstep.1 hs hVar hWs


/-! ### Separation of the guesses and the chord pole family -/

/-- **Separation of the guesses**: distinct centres are farther apart than `2r = 1/(10σ₁)` —
their imaginary parts differ by a nonzero multiple of `2π/σ₁`, and `1/10 < 2π`. -/
theorem sGuess_dist_gt (P : MixParams) (hs1 : 0 < P.sig1) {m n : ℕ} (hmn : m ≠ n) :
    2 * (1 / (20 * P.sig1)) < dist (sGuess P m) (sGuess P n) := by
  have hne : P.sig1 ≠ 0 := hs1.ne'
  have hpos : (0 : ℝ) < 2 * Real.pi / P.sig1 := div_pos (by positivity) hs1
  have him : (sGuess P m).im - (sGuess P n).im =
      2 * Real.pi / P.sig1 * ((m : ℝ) - (n : ℝ)) := by
    rw [sGuess_im, sGuess_im]; ring
  have hnat : (1 : ℝ) ≤ |(m : ℝ) - (n : ℝ)| := by
    have hmm : (m : ℤ) - (n : ℤ) ≠ 0 := by
      simpa using sub_ne_zero.mpr (fun h => hmn (by exact_mod_cast h))
    have hz : (1 : ℤ) ≤ |(m : ℤ) - (n : ℤ)| := Int.one_le_abs hmm
    have hcast : ((|(m : ℤ) - (n : ℤ)| : ℤ) : ℝ) = |(m : ℝ) - (n : ℝ)| := by push_cast; ring
    rw [← hcast]
    exact_mod_cast hz
  have him2 : |(sGuess P m).im - (sGuess P n).im| =
      2 * Real.pi / P.sig1 * |(m : ℝ) - (n : ℝ)| := by
    rw [him, abs_mul, abs_of_pos hpos]
  have himabs : 2 * Real.pi / P.sig1 ≤ |(sGuess P m).im - (sGuess P n).im| := by
    rw [him2]
    linarith [mul_le_mul_of_nonneg_left hnat hpos.le]
  have hdistim : |(sGuess P m - sGuess P n).im| ≤ ‖sGuess P m - sGuess P n‖ :=
    Complex.abs_im_le_norm _
  rw [Complex.sub_im] at hdistim
  rw [dist_eq_norm]
  have hgap : 2 * (1 / (20 * P.sig1)) < 2 * Real.pi / P.sig1 := by
    have hpi : (1 : ℝ) / 10 < 2 * Real.pi := by linarith [Real.pi_gt_three]
    have h5 : (0 : ℝ) < (2 * Real.pi - 1 / 10) / P.sig1 := div_pos (by linarith) hs1
    have heq2 : 2 * Real.pi / P.sig1 - 2 * (1 / (20 * P.sig1)) =
        (2 * Real.pi - 1 / 10) / P.sig1 := by
      field_simp
      ring
    linarith
  linarith [himabs, hdistim, hgap]

/-- **The mixture chord pole family** — centres `sGuess P n`, radius `r = 1/(20σ₁)`,
contraction constant `K = 3/4`, index threshold from `chord_conditions_eventually`.
This is the mixture-side instance of the shared Banach obligation of MZERO.5/POLE.3. -/
theorem chordPoleFamily_detF_exists (P : MixParams) (hP : P.Phys) :
    Nonempty (FMSA.BanachPoleFamily.ChordPoleFamily P.detF) := by
  have hs1 : 0 < P.sig1 := lt_trans hP.1 hP.2.1
  obtain ⟨N, hN⟩ := chord_conditions_eventually P hP
  have hKcoe : ((3 / 4 : NNReal) : ℝ) = 3 / 4 := by norm_num
  exact ⟨{
    N := N
    s1 := fun n => sGuess P n
    Fp1 := fun n => derivF P (sGuess P n)
    F' := derivF P
    r := 1 / (20 * P.sig1)
    K := 3 / 4
    hr := div_pos one_pos (by linarith)
    hK1 := by rw [← NNReal.coe_lt_coe, hKcoe, NNReal.coe_one]; norm_num
    hFp1 := fun n hn => (hN n hn).1
    hderiv := fun n hn s hs => detF_hasDerivAt P ((hN n hn).2.1 s hs)
    hbound := fun n hn s hs => by rw [hKcoe]; exact (hN n hn).2.2.1 s hs
    hstep := fun n hn => by rw [hKcoe]; exact (hN n hn).2.2.2.1
    hsep := fun m n _ _ hmn => sGuess_dist_gt P hs1 hmn
  }⟩

/-- **The mixture determinant has infinitely many complex zeros** (parameter-pack form):
`chordPoleFamily_detF_exists` fires the shared `zeros_infinite_of_chordPoleFamily`. -/
theorem detF_zeros_infinite (P : MixParams) (hP : P.Phys) :
    {s : ℂ | P.detF s = 0}.Infinite :=
  (chordPoleFamily_detF_exists P hP).elim fun fam =>
    FMSA.BanachPoleFamily.zeros_infinite_of_chordPoleFamily fam

/-- **Parameter-only form of the family**: a concrete `ChordPoleFamily` for the raw `detC`
of an `N = 2` mixture with physical diameters and entrywise-positive Baxter data. -/
theorem chordPoleFamily_detC_exists {sig0 sig1 : ℝ} (h0 : 0 < sig0) (h01 : sig0 < sig1)
    {rr Qp Qpp : Fin 2 → Fin 2 → ℝ} (hrr : ∀ i j, 0 < rr i j) (hQp : ∀ i j, 0 < Qp i j)
    (hQpp : ∀ i j, 0 < Qpp i j) :
    Nonempty (FMSA.BanachPoleFamily.ChordPoleFamily
      (detC ![sig0, sig1] (fun i j => (rr i j : ℂ)) (fun i j => (Qp i j : ℂ))
        (fun i j => (Qpp i j : ℂ)))) := by
  have hbridge : MixParams.detF ⟨sig0, sig1, rr, Qp, Qpp⟩ =
      detC ![sig0, sig1] (fun i j => (rr i j : ℂ)) (fun i j => (Qp i j : ℂ))
        (fun i j => (Qpp i j : ℂ)) := rfl
  rw [← hbridge]
  exact chordPoleFamily_detF_exists ⟨sig0, sig1, rr, Qp, Qpp⟩ ⟨h0, h01, hrr, hQp, hQpp⟩

/-- **MZERO.5 discharged unconditionally on the mixture side**: for physical `N = 2` mixture
data, `det(Q̂₀_c)` has infinitely many complex zeros — the chord-Newton family
(`chordPoleFamily_detC_exists`) fires `zeros_infinite_of_chordPoleFamily`. -/
theorem detC_zeros_infinite_unconditional {sig0 sig1 : ℝ} (h0 : 0 < sig0) (h01 : sig0 < sig1)
    {rr Qp Qpp : Fin 2 → Fin 2 → ℝ} (hrr : ∀ i j, 0 < rr i j) (hQp : ∀ i j, 0 < Qp i j)
    (hQpp : ∀ i j, 0 < Qpp i j) :
    {s : ℂ | detC ![sig0, sig1] (fun i j => (rr i j : ℂ)) (fun i j => (Qp i j : ℂ))
      (fun i j => (Qpp i j : ℂ)) s = 0}.Infinite := by
  have hbridge : MixParams.detF ⟨sig0, sig1, rr, Qp, Qpp⟩ =
      detC ![sig0, sig1] (fun i j => (rr i j : ℂ)) (fun i j => (Qp i j : ℂ))
        (fun i j => (Qpp i j : ℂ)) := rfl
  rw [← hbridge]
  exact detF_zeros_infinite ⟨sig0, sig1, rr, Qp, Qpp⟩ ⟨h0, h01, hrr, hQp, hQpp⟩

/-! ### MML.5-concrete, Stage B — the zero family with disk membership -/

/-- **Zero family retaining disk membership.**  Given the chord conditions on all indices `≥ N`
(the output of `chord_conditions_eventually`, possibly with an inflated threshold `N`), Banach
chord-Newton produces an injective family of `detF`-zeros whose `n`-th member lies in the
radius-`1/(20σ₁)` disk around `sGuess P (n + N)`.  This mirrors the construction inside
`zeros_infinite_of_chordPoleFamily` / `exists_zero_family_growth_of_chordPoleFamily` but
**retains the disk membership**, which the per-pole magnitude bounds of MML.5 need (the generic
engine's conclusion forgets it). -/
theorem detF_zero_family_in_disks (P : MixParams) (hP : P.Phys) (N : ℕ)
    (hN : ∀ n : ℕ, N ≤ n →
      derivF P (sGuess P n) ≠ 0 ∧
      (∀ s ∈ Metric.closedBall (sGuess P n) (1 / (20 * P.sig1)), s ≠ 0) ∧
      (∀ s ∈ Metric.closedBall (sGuess P n) (1 / (20 * P.sig1)),
        ‖1 - derivF P s / derivF P (sGuess P n)‖ ≤ 3 / 4) ∧
      ‖P.detF (sGuess P n) / derivF P (sGuess P n)‖ ≤ 1 / (20 * P.sig1) * (1 - 3 / 4)) :
    ∃ g : ℕ → ℂ, Function.Injective g ∧ (∀ n, P.detF (g n) = 0) ∧
      (∀ n, g n ∈ Metric.closedBall (sGuess P (n + N)) (1 / (20 * P.sig1))) := by
  have hs1 : 0 < P.sig1 := lt_trans hP.1 hP.2.1
  have hr : (0 : ℝ) < 1 / (20 * P.sig1) := by positivity
  have hKcoe : ((3 / 4 : NNReal) : ℝ) = 3 / 4 := by norm_num
  have hK1 : (3 / 4 : NNReal) < 1 := by
    rw [← NNReal.coe_lt_coe, hKcoe, NNReal.coe_one]; norm_num
  have hwitness : ∀ n : ℕ, ∃ s ∈ Metric.closedBall (sGuess P (n + N)) (1 / (20 * P.sig1)),
      P.detF s = 0 := by
    intro n
    obtain ⟨hne, hnz, hbd, hst⟩ := hN (n + N) (Nat.le_add_left N n)
    have hLip := chordPhi_lipschitzOnWith
      (F := P.detF) (F' := derivF P) (Fp1 := derivF P (sGuess P (n + N)))
      (s1 := sGuess P (n + N)) (r := 1 / (20 * P.sig1)) (3 / 4 : NNReal)
      (fun s hs => detF_hasDerivAt P (hnz s hs)) (fun s hs => by rw [hKcoe]; exact hbd s hs)
    have hstep' : dist (sGuess P (n + N))
        (chordPhi P.detF (derivF P (sGuess P (n + N))) (sGuess P (n + N))) ≤
          1 / (20 * P.sig1) * (1 - ((3 / 4 : NNReal) : ℝ)) := by
      simp only [chordPhi, dist_eq_norm, sub_sub_cancel]
      rw [hKcoe]; exact hst
    have hMapsTo := mapsTo_closedBall_of_lipschitzOnWith_of_dist_le
      (chordPhi P.detF (derivF P (sGuess P (n + N)))) (sGuess P (n + N)) (1 / (20 * P.sig1))
      hr.le (3 / 4 : NNReal) hLip hstep'
    exact chord_zero_exists_of_bounds P.detF (derivF P (sGuess P (n + N)))
      (sGuess P (n + N)) (1 / (20 * P.sig1)) hr hne (3 / 4 : NNReal) hK1 hMapsTo hLip
  choose g hgmem hgzero using hwitness
  refine ⟨g, ?_, hgzero, hgmem⟩
  intro a b hab
  by_contra hne
  have hdist2r : dist (sGuess P (a + N)) (sGuess P (b + N)) ≤ 2 * (1 / (20 * P.sig1)) := by
    calc dist (sGuess P (a + N)) (sGuess P (b + N))
        ≤ dist (sGuess P (a + N)) (g a) + dist (g a) (sGuess P (b + N)) := dist_triangle _ _ _
      _ = dist (g a) (sGuess P (a + N)) + dist (g b) (sGuess P (b + N)) := by
          rw [dist_comm (sGuess P (a + N)) (g a), hab]
      _ ≤ 1 / (20 * P.sig1) + 1 / (20 * P.sig1) :=
          add_le_add (Metric.mem_closedBall.mp (hgmem a)) (Metric.mem_closedBall.mp (hgmem b))
      _ = 2 * (1 / (20 * P.sig1)) := by ring
  have hsep := sGuess_dist_gt P hs1 (m := a + N) (n := b + N) (by omega)
  linarith


theorem detF_zero_family_growth (P : MixParams) (hP : P.Phys) :
    ∃ g : ℕ → ℂ, Function.Injective g ∧ (∀ n, P.detF (g n) = 0) ∧
      ∃ c d : ℝ, 0 < c ∧ 0 < d ∧ ∀ n : ℕ, c * (n : ℝ) + d ≤ ‖g n‖ := by
  have hs1 : 0 < P.sig1 := lt_trans hP.1 hP.2.1
  obtain ⟨N, hN⟩ := chord_conditions_eventually P hP
  obtain ⟨g, hinj, hzero, hmem⟩ := detF_zero_family_in_disks P hP N
    (fun n hn => by
      obtain ⟨a1, a2, a3, a4, _⟩ := hN n hn
      exact ⟨a1, a2, a3, a4⟩)
  refine ⟨fun n => g (n + 1), hinj.comp (fun a b h => by omega), fun n => hzero _,
    2 * Real.pi / P.sig1, (2 * Real.pi - 1 / 20) / P.sig1, by positivity, ?_, ?_⟩
  · apply div_pos (by linarith [Real.pi_gt_three]) hs1
  · intro n
    have hball := Metric.mem_closedBall.mp (hmem (n + 1))
    rw [dist_eq_norm] at hball
    have hrev : ‖sGuess P (n + 1 + N)‖ - ‖g (n + 1)‖ ≤ 1 / (20 * P.sig1) := by
      calc ‖sGuess P (n + 1 + N)‖ - ‖g (n + 1)‖ ≤ ‖sGuess P (n + 1 + N) - g (n + 1)‖ :=
            norm_sub_norm_le _ _
        _ = ‖g (n + 1) - sGuess P (n + 1 + N)‖ := norm_sub_rev _ _
        _ ≤ 1 / (20 * P.sig1) := hball
    have hlow := sGuess_norm_ge P hs1 (n + 1 + N)
    have hcast : 2 * Real.pi * ((n + 1 + N : ℕ) : ℝ) / P.sig1 ≥
        2 * Real.pi * ((n : ℝ) + 1) / P.sig1 := by
      have hc : ((n + 1 + N : ℕ) : ℝ) = (n : ℝ) + 1 + (N : ℝ) := by push_cast; ring
      rw [hc, ge_iff_le, div_le_div_iff_of_pos_right hs1]
      nlinarith [Real.pi_pos, Nat.cast_nonneg N (α := ℝ)]
    have he : 2 * Real.pi / P.sig1 * (n : ℝ) + (2 * Real.pi - 1 / 20) / P.sig1 + 1 / (20 * P.sig1)
        = 2 * Real.pi * ((n : ℝ) + 1) / P.sig1 := by field_simp; ring
    linarith

/-- Constant in the two-sided real-part deviation at the guess. -/
def MixParams.KdevG (P : MixParams) : ℝ :=
  (|Real.log (4 / P.mu)| + |Real.log (2 * (P.mu + P.K1))|) / P.sig1

theorem tRat_ge_one (P : MixParams) (hP : P.Phys) {Y : ℝ} (h1 : 1 ≤ Y)
    (hMc2 : 2 * P.KMc ≤ Y) (hM12 : 2 * P.K1 ≤ P.mu * Y) (ht1 : 2 * (P.mu + P.K1) ≤ Y) :
    1 ≤ tRat P Y := by
  have hmu : 0 < P.mu := mul_pos (hP.2.2.1 1 1) (hP.2.2.2.1 1 1)
  have hK10 := K1_nonneg P hP
  have hY0 : (0 : ℝ) < Y := lt_of_lt_of_le one_pos h1
  have htlow := tRat_lower P hP h1 hMc2 hM12
  have hYsq : Y ≤ Y ^ 2 := by nlinarith
  have h2A : 2 * (P.mu + P.K1) ≤ Y ^ 2 := by linarith
  have hone : 1 ≤ Y ^ 2 / (2 * (P.mu + P.K1)) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  linarith

/-- **Two-sided real-part deviation at the guess**: `Re(sGuess n)` is `−2·log Y/σ₁` up to the
constant `KdevG` — a direct consequence of the two-sided ratio envelope `Y²/(2(μ+K1)) ≤ t ≤ 4Y²/μ`
and `Re(sGuess n) = −log t/σ₁`. -/
theorem sGuess_re_dev (P : MixParams) (hP : P.Phys) (n : ℕ) {Y : ℝ}
    (hYdef : Y = 2 * Real.pi * n / P.sig1) (h1 : 1 ≤ Y)
    (hMc2 : 2 * P.KMc ≤ Y) (hM12 : 2 * P.K1 ≤ P.mu * Y) :
    |(sGuess P n).re + 2 * Real.log Y / P.sig1| ≤ P.KdevG := by
  have hs1 : 0 < P.sig1 := lt_trans hP.1 hP.2.1
  have hmu : 0 < P.mu := mul_pos (hP.2.2.1 1 1) (hP.2.2.2.1 1 1)
  have hK10 := K1_nonneg P hP
  have hY0 : (0 : ℝ) < Y := lt_of_lt_of_le one_pos h1
  have hA : (0 : ℝ) < P.mu + P.K1 := by linarith
  have htlow := tRat_lower P hP h1 hMc2 hM12
  have htup := tRat_upper P hP h1 (by linarith) hM12
  have htpos : 0 < tRat P Y := lt_of_lt_of_le (by positivity) htlow
  set L : ℝ := Real.log (tRat P Y) with hLdef
  -- upper: log t ≤ log(4/μ) + 2 log Y
  have hup : L ≤ Real.log (4 / P.mu) + 2 * Real.log Y := by
    have hh := Real.log_le_log htpos htup
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at hh
    push_cast at hh; linarith
  -- lower: log t ≥ 2 log Y - log(2(μ+K1))
  have hlow : 2 * Real.log Y - Real.log (2 * (P.mu + P.K1)) ≤ L := by
    have hh := Real.log_le_log (by positivity) htlow
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow] at hh
    push_cast at hh; linarith
  have hre : (sGuess P n).re = -L / P.sig1 := by
    rw [sGuess_re, ← hYdef, hLdef]
  have hval : (sGuess P n).re + 2 * Real.log Y / P.sig1 =
      (2 * Real.log Y - L) / P.sig1 := by rw [hre]; ring
  rw [hval, MixParams.KdevG, abs_div, abs_of_pos hs1, div_le_div_iff_of_pos_right hs1]
  rw [abs_le]
  constructor
  · linarith [le_abs_self (Real.log (4 / P.mu)), abs_nonneg (Real.log (2 * (P.mu + P.K1))),
      neg_abs_le (Real.log (4 / P.mu))]
  · linarith [le_abs_self (Real.log (2 * (P.mu + P.K1))), abs_nonneg (Real.log (4 / P.mu))]

/-- **Frozen-derivative lower bound at the guess is `Θ(1)`**: `‖F′(sGuess n)‖ ≥ σ₁μ/(6(μ+K1))`,
uniform in `n`.  From `‖W′ − 6W/g‖ ≥ (2/3)σ₁μ·t·Y⁴` (`Ag_lower_and_step`), `‖g‖ ≤ (41/40)Y` and
`t ≥ Y²/(2(μ+K1))`: the `t·Y⁴/Y⁶ = t/Y²` scaling is bounded below by a constant. -/
theorem derivF_at_sGuess_lower (P : MixParams) (hP : P.Phys) (n : ℕ) {Y : ℝ}
    (hYdef : Y = 2 * Real.pi * n / P.sig1) (h1 : 1 ≤ Y)
    (hMc2 : 2 * P.KMc ≤ Y) (hM12 : 2 * P.K1 ≤ P.mu * Y) (ht1 : 2 * (P.mu + P.K1) ≤ Y)
    (hLcap : 40 * Real.log (tRat P Y) ≤ P.sig1 * Y)
    (hAg : 2 / 3 * (P.sig1 * P.mu * (tRat P Y * Y ^ 4)) ≤
      ‖WD P (sGuess P n) - 6 * Wfun P (sGuess P n) / sGuess P n‖) :
    P.sig1 * P.mu / (6 * (P.mu + P.K1)) ≤ ‖derivF P (sGuess P n)‖ := by
  have hs1 : 0 < P.sig1 := lt_trans hP.1 hP.2.1
  have hmu : 0 < P.mu := mul_pos (hP.2.2.1 1 1) (hP.2.2.2.1 1 1)
  have hK10 := K1_nonneg P hP
  have hY0 : (0 : ℝ) < Y := lt_of_lt_of_le one_pos h1
  have hA : (0 : ℝ) < P.mu + P.K1 := by linarith
  have ht1' := tRat_ge_one P hP h1 hMc2 hM12 ht1
  have htpos : 0 < tRat P Y := lt_of_lt_of_le one_pos ht1'
  have h0L : 0 ≤ Real.log (tRat P Y) := Real.log_nonneg ht1'
  have htlow := tRat_lower P hP h1 hMc2 hM12
  have hgne : sGuess P n ≠ 0 := by
    intro h
    have him : (sGuess P n).im = Y := by rw [sGuess_im, ← hYdef]
    rw [h] at him; simp only [Complex.zero_im] at him; linarith
  have hgup : ‖sGuess P n‖ ≤ 41 / 40 * Y := by
    have := sGuess_norm_le P hs1 n (by rw [← hYdef]; exact h0L)
      (by rw [← hYdef]; linarith [hLcap])
    rw [← hYdef] at this; exact this
  have hgpos : 0 < ‖sGuess P n‖ := norm_pos_iff.mpr hgne
  have hg6 : ‖sGuess P n‖ ^ 6 ≤ 2 * Y ^ 6 := by
    have hp : ‖sGuess P n‖ ^ 6 ≤ (41 / 40 * Y) ^ 6 := pow_le_pow_left₀ (norm_nonneg _) hgup 6
    nlinarith [pow_pos hY0 6, hp]
  have hnorm : ‖derivF P (sGuess P n)‖ =
      ‖WD P (sGuess P n) - 6 * Wfun P (sGuess P n) / sGuess P n‖ / ‖sGuess P n‖ ^ 6 := by
    rw [derivF, norm_div, norm_pow]
  have hdiv := FMSA.HardSphere.div_le_div_bound hAg
    (le_trans (by positivity) hAg) (pow_pos hgpos 6) hg6
  rw [hnorm]
  refine le_trans ?_ hdiv
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have htY2 : Y ^ 2 ≤ 2 * (P.mu + P.K1) * tRat P Y := by
    rw [div_le_iff₀ (by positivity)] at htlow; linarith
  nlinarith [pow_pos hY0 4, mul_pos hs1 hmu, htY2, pow_pos hY0 2,
    mul_le_mul_of_nonneg_left htY2 (by positivity : (0:ℝ) ≤ P.sig1 * P.mu * Y ^ 4)]

/-- Deviation constant on the chord disks. -/
def MixParams.Kdev (P : MixParams) : ℝ := P.KdevG + 1 / (4 * P.sig1)

/-- **The three disk facts** driving the MML.5 magnitude bound: every point `s` of the chord disk
around `sGuess P n` has (i) `‖s‖ ≥ 1`, (ii) real part `−2·log‖s‖/σ₁` up to the fixed constant
`Kdev` (the log-lift, transported from the centre and from `Y` to `‖s‖`), and (iii) a **uniform
`Θ(1)` derivative floor** `‖F′(s)‖ ≥ σ₁μ/(24(μ+K1))` (chord bound `‖1 − F′s/F′g‖ ≤ 3/4` ⇒
`‖F′s‖ ≥ ¼‖F′g‖`, with `derivF_at_sGuess_lower` for `‖F′g‖`). -/
theorem disk_facts (P : MixParams) (hP : P.Phys) (n : ℕ) {Y : ℝ}
    (hYdef : Y = 2 * Real.pi * n / P.sig1) (hn1 : 1 ≤ n) (h2 : 2 ≤ Y)
    (hMc2 : 2 * P.KMc ≤ Y) (hM12 : 2 * P.K1 ≤ P.mu * Y) (ht1 : 2 * (P.mu + P.K1) ≤ Y)
    (hLcap : 40 * Real.log (tRat P Y) ≤ P.sig1 * Y)
    (hAg : 2 / 3 * (P.sig1 * P.mu * (tRat P Y * Y ^ 4)) ≤
      ‖WD P (sGuess P n) - 6 * Wfun P (sGuess P n) / sGuess P n‖)
    (hchord : ∀ s ∈ Metric.closedBall (sGuess P n) (1 / (20 * P.sig1)),
      ‖1 - derivF P s / derivF P (sGuess P n)‖ ≤ 3 / 4)
    {s : ℂ} (hs : s ∈ Metric.closedBall (sGuess P n) (1 / (20 * P.sig1))) :
    1 ≤ ‖s‖ ∧ |(-s.re) - 2 * Real.log ‖s‖ / P.sig1| ≤ P.Kdev ∧
      P.sig1 * P.mu / (24 * (P.mu + P.K1)) ≤ ‖derivF P s‖ := by
  have hs1 : 0 < P.sig1 := lt_trans hP.1 hP.2.1
  have hmu : 0 < P.mu := mul_pos (hP.2.2.1 1 1) (hP.2.2.2.1 1 1)
  have hK10 := K1_nonneg P hP
  have h1 : (1 : ℝ) ≤ Y := by linarith
  have hY0 : (0 : ℝ) < Y := by linarith
  have hA : (0 : ℝ) < P.mu + P.K1 := by linarith
  have h0L : 0 ≤ Real.log (tRat P Y) := Real.log_nonneg (tRat_ge_one P hP h1 hMc2 hM12 ht1)
  have hgup : ‖sGuess P n‖ ≤ 41 / 40 * Y := by
    have := sGuess_norm_le P hs1 n (by rw [← hYdef]; exact h0L) (by rw [← hYdef]; linarith)
    rw [← hYdef] at this; exact this
  have hgim : (sGuess P n).im = Y := by rw [sGuess_im, ← hYdef]
  -- `σ₁·Y = 2πn ≥ 2π > 2` for `n ≥ 1`
  have hsY : (2 : ℝ) ≤ P.sig1 * Y := by
    have he : P.sig1 * Y = 2 * Real.pi * (n : ℝ) := by rw [hYdef]; field_simp
    have hn : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    rw [he]; nlinarith [Real.pi_gt_three]
  have hrc40 : 1 / (20 * P.sig1) ≤ Y / 40 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hslow : 39 / 40 * Y ≤ ‖s‖ := disk_norm_ge hY0.le hgim hrc40 hs
  have hsup : ‖s‖ ≤ 11 / 10 * Y := disk_norm_le hY0.le (by linarith) hrc40 hs
  have hsnorm1 : (1 : ℝ) ≤ ‖s‖ := by linarith
  have hspos : (0 : ℝ) < ‖s‖ := by linarith
  refine ⟨hsnorm1, ?_, ?_⟩
  · -- the deviation chain: centre transport + log-lift + `Y → ‖s‖`
    have hrepart : |(-s.re) - (-(sGuess P n).re)| ≤ 1 / (20 * P.sig1) := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hs
      have h := Complex.abs_re_le_norm (s - sGuess P n)
      rw [Complex.sub_re] at h
      have : |(-s.re) - (-(sGuess P n).re)| = |s.re - (sGuess P n).re| := by
        rw [← abs_neg]; congr 1; ring
      rw [this]; linarith
    have hdevG : |(sGuess P n).re + 2 * Real.log Y / P.sig1| ≤ P.KdevG :=
      sGuess_re_dev P hP n hYdef h1 hMc2 hM12
    have hlogdiff : |Real.log ‖s‖ - Real.log Y| ≤ 1 / 10 := by
      have hd1 : Real.log ‖s‖ - Real.log Y = Real.log (‖s‖ / Y) := (Real.log_div hspos.ne' hY0.ne').symm
      have hd2 : Real.log Y - Real.log ‖s‖ = Real.log (Y / ‖s‖) := (Real.log_div hY0.ne' hspos.ne').symm
      have hu1 : Real.log (‖s‖ / Y) ≤ ‖s‖ / Y - 1 := Real.log_le_sub_one_of_pos (by positivity)
      have hu2 : Real.log (Y / ‖s‖) ≤ Y / ‖s‖ - 1 := Real.log_le_sub_one_of_pos (by positivity)
      have hr1 : ‖s‖ / Y ≤ 11 / 10 := by rw [div_le_iff₀ hY0]; linarith
      have hr2 : Y / ‖s‖ ≤ 40 / 39 := by rw [div_le_iff₀ hspos]; linarith
      rw [abs_le]
      constructor
      · rw [hd1]; linarith [hd2 ▸ hu2, hu2]
      · rw [hd1]; linarith
    have hkey : (-s.re) - 2 * Real.log ‖s‖ / P.sig1 =
        ((-s.re) - (-(sGuess P n).re)) - ((sGuess P n).re + 2 * Real.log Y / P.sig1)
          + 2 * (Real.log Y - Real.log ‖s‖) / P.sig1 := by ring
    have hlast : |2 * (Real.log Y - Real.log ‖s‖) / P.sig1| ≤ 2 * (1 / 10) / P.sig1 := by
      rw [abs_div, abs_of_pos hs1, div_le_div_iff_of_pos_right hs1, abs_mul]
      rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), ← abs_neg (Real.log Y - Real.log ‖s‖)]
      have : -(Real.log Y - Real.log ‖s‖) = Real.log ‖s‖ - Real.log Y := by ring
      rw [this]; linarith [hlogdiff]
    rw [hkey, MixParams.Kdev]
    have hcomb : |((-s.re) - (-(sGuess P n).re)) - ((sGuess P n).re + 2 * Real.log Y / P.sig1)
        + 2 * (Real.log Y - Real.log ‖s‖) / P.sig1| ≤
        (1 / (20 * P.sig1) + P.KdevG) + 2 * (1 / 10) / P.sig1 := by
      refine le_trans (abs_add_le _ _) (add_le_add ?_ hlast)
      exact le_trans (abs_sub _ _) (add_le_add hrepart hdevG)
    refine le_trans hcomb (le_of_eq ?_)
    field_simp
    ring
  · -- the derivative floor
    have hDg : P.sig1 * P.mu / (6 * (P.mu + P.K1)) ≤ ‖derivF P (sGuess P n)‖ :=
      derivF_at_sGuess_lower P hP n hYdef h1 hMc2 hM12 ht1 hLcap hAg
    have hDgpos : 0 < ‖derivF P (sGuess P n)‖ := lt_of_lt_of_le (by positivity) hDg
    have hDgne : derivF P (sGuess P n) ≠ 0 := norm_pos_iff.mp hDgpos
    have hch := hchord s hs
    have hratio : 1 / 4 ≤ ‖derivF P s / derivF P (sGuess P n)‖ := by
      have h := norm_sub_norm_le (1 : ℂ) (1 - derivF P s / derivF P (sGuess P n))
      simp only [sub_sub_cancel, norm_one] at h
      linarith
    have hmul : ‖derivF P s‖ = ‖derivF P s / derivF P (sGuess P n)‖ * ‖derivF P (sGuess P n)‖ := by
      rw [norm_div, div_mul_cancel₀]; exact hDgpos.ne'
    rw [hmul]
    have hstep1 : 1 / 4 * ‖derivF P (sGuess P n)‖ ≤
        ‖derivF P s / derivF P (sGuess P n)‖ * ‖derivF P (sGuess P n)‖ :=
      mul_le_mul_of_nonneg_right hratio (norm_nonneg _)
    have hstep2 : P.sig1 * P.mu / (24 * (P.mu + P.K1)) = 1 / 4 * (P.sig1 * P.mu / (6 * (P.mu + P.K1))) := by
      field_simp; ring
    rw [hstep2]
    linarith [mul_le_mul_of_nonneg_left hDg (by norm_num : (0:ℝ) ≤ 1 / 4)]

/-! ### The `(0,1)` Baxter entry `q01` and its envelope -/

/-- The `(0,1)` entry of the complex Baxter matrix `Q̂₀_c(s)` for the parameter pack `P`
(`FMSA.Q0Complex.q0_entry_c` with `σᵢ = σ₀`, `λ₀₁ = (σ₁−σ₀)/2`, `δ₀₁ = 0`).  This is the numerator
of the MML.5 residue coefficient `B_k = −q01(z_k)/det′(z_k)` (`b_k_residue`). -/
def q01 (P : MixParams) (s : ℂ) : ℂ :=
  FMSA.Q0Complex.q0_entry_c s (P.sig0 : ℂ) (((P.sig1 - P.sig0) / 2 : ℝ) : ℂ)
    ((P.Qp 0 1 : ℝ) : ℂ) ((P.Qpp 0 1 : ℝ) : ℂ) ((P.rr 0 1 : ℝ) : ℂ) 0

/-- **Bridge**: `q01 P` is literally the `(0,1)` entry of the matrix whose determinant is `detC`. -/
theorem q01_eq (P : MixParams) (s : ℂ) :
    q01 P s = FMSA.Q0Complex.Q0_mat_c s (fun i => ((![P.sig0, P.sig1] i : ℝ) : ℂ))
      (fun i j => ((P.rr i j : ℝ) : ℂ)) (fun i j => ((P.Qp i j : ℝ) : ℂ))
      (fun i j => ((P.Qpp i j : ℝ) : ℂ)) 0 1 := by
  unfold q01 FMSA.Q0Complex.Q0_mat_c
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Polynomial-part constant of the `q01` envelope. -/
def MixParams.Cq1 (P : MixParams) : ℝ :=
  (P.Qp 0 1 + P.Qpp 0 1) * (1 + P.sig0 + P.sig0 ^ 2 / 2)

/-- Exponential-part constant of the `q01` envelope. -/
def MixParams.Cq2 (P : MixParams) : ℝ := P.Qp 0 1 + P.Qpp 0 1

/-- **Envelope for `q01`** on `‖s‖ ≥ 1`, with `x := −Re s`:
`‖q01(s)‖ ≤ rr₀₁·e^{λx}·(Cq1/‖s‖ + Cq2·e^{σ₀x}/‖s‖²)`, `λ = (σ₁−σ₀)/2`.
The `e^{λx}` prefactor is `‖e^{−λs}‖`; the bracket collects `‖φ₁‖ ≤ (1+σ₀‖s‖+e^{σ₀x})/‖s‖²` and
`‖φ₂‖ ≤ (1+σ₀‖s‖+σ₀²‖s‖²/2+e^{σ₀x})/‖s‖³`, using `‖s‖ ≥ 1` to merge all purely polynomial
contributions into the single `1/‖s‖` term. -/
theorem q01_norm_le (P : MixParams) (hP : P.Phys) {s : ℂ} (hA : 1 ≤ ‖s‖) :
    ‖q01 P s‖ ≤ P.rr 0 1 * Real.exp ((P.sig1 - P.sig0) / 2 * (-s.re)) *
      (P.Cq1 / ‖s‖ + P.Cq2 * Real.exp (P.sig0 * (-s.re)) / ‖s‖ ^ 2) := by
  have hs0 : 0 < P.sig0 := hP.1
  have hrr : 0 < P.rr 0 1 := hP.2.2.1 0 1
  have hqp : 0 < P.Qp 0 1 := hP.2.2.2.1 0 1
  have hqpp : 0 < P.Qpp 0 1 := hP.2.2.2.2 0 1
  have hApos : (0 : ℝ) < ‖s‖ := by linarith
  have hsne : s ≠ 0 := by
    intro h; rw [h] at hApos; simp only [norm_zero] at hApos; linarith
  set A : ℝ := ‖s‖ with hAdef
  set x : ℝ := -s.re with hxdef
  set E : ℝ := Real.exp (P.sig0 * x) with hEdef
  have hE0 : 0 < E := Real.exp_pos _
  have hsig : ‖s * (P.sig0 : ℂ)‖ = A * P.sig0 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
  have hexpS : ‖Complex.exp (-(s * (P.sig0 : ℂ)))‖ = E := by
    rw [norm_exp_neg_mul, hEdef, hxdef]; congr 1; ring
  have hexpL : ‖Complex.exp (-((((P.sig1 - P.sig0) / 2 : ℝ) : ℂ) * s))‖ =
      Real.exp ((P.sig1 - P.sig0) / 2 * x) := by
    rw [mul_comm, norm_exp_neg_mul, hxdef]; congr 1; ring
  -- the two bracket factors
  have hphi1 : ‖(1 - s * (P.sig0 : ℂ) - Complex.exp (-(s * (P.sig0 : ℂ)))) / s ^ 2‖ ≤
      (1 + P.sig0 * A + E) / A ^ 2 := by
    rw [norm_div, norm_pow, ← hAdef]
    refine (div_le_div_iff_of_pos_right (by positivity)).mpr ?_
    refine le_trans (norm_sub_sub_le _ _ _) ?_
    rw [norm_one, hsig, hexpS]; linarith
  have hphi2 : ‖(1 - s * (P.sig0 : ℂ) + (s * (P.sig0 : ℂ)) ^ 2 / 2 -
      Complex.exp (-(s * (P.sig0 : ℂ)))) / s ^ 3‖ ≤
      (1 + P.sig0 * A + P.sig0 ^ 2 * A ^ 2 / 2 + E) / A ^ 3 := by
    rw [norm_div, norm_pow, ← hAdef]
    refine (div_le_div_iff_of_pos_right (by positivity)).mpr ?_
    have hsq : ‖(s * (P.sig0 : ℂ)) ^ 2 / 2‖ = (A * P.sig0) ^ 2 / 2 := by
      rw [norm_div, norm_pow, hsig]; norm_num
    calc ‖1 - s * (P.sig0 : ℂ) + (s * (P.sig0 : ℂ)) ^ 2 / 2 - Complex.exp (-(s * (P.sig0 : ℂ)))‖
        ≤ ‖1 - s * (P.sig0 : ℂ) + (s * (P.sig0 : ℂ)) ^ 2 / 2‖ + ‖Complex.exp (-(s * (P.sig0 : ℂ)))‖ :=
          norm_sub_le _ _
      _ ≤ (‖(1 : ℂ) - s * (P.sig0 : ℂ)‖ + ‖(s * (P.sig0 : ℂ)) ^ 2 / 2‖) + E := by
          rw [hexpS]; linarith [norm_add_le ((1 : ℂ) - s * (P.sig0 : ℂ)) ((s * (P.sig0 : ℂ)) ^ 2 / 2)]
      _ ≤ ((‖(1 : ℂ)‖ + ‖s * (P.sig0 : ℂ)‖) + ‖(s * (P.sig0 : ℂ)) ^ 2 / 2‖) + E := by
          linarith [norm_sub_le (1 : ℂ) (s * (P.sig0 : ℂ))]
      _ = 1 + P.sig0 * A + P.sig0 ^ 2 * A ^ 2 / 2 + E := by
          rw [norm_one, hsig, hsq]; ring
  -- assemble
  have hq : q01 P s = -(((P.rr 0 1 : ℝ) : ℂ) *
      Complex.exp (-((((P.sig1 - P.sig0) / 2 : ℝ) : ℂ) * s)) *
      (((P.Qp 0 1 : ℝ) : ℂ) * ((1 - s * (P.sig0 : ℂ) - Complex.exp (-(s * (P.sig0 : ℂ)))) / s ^ 2) +
       ((P.Qpp 0 1 : ℝ) : ℂ) * ((1 - s * (P.sig0 : ℂ) + (s * (P.sig0 : ℂ)) ^ 2 / 2 -
         Complex.exp (-(s * (P.sig0 : ℂ)))) / s ^ 3))) := by
    unfold q01 FMSA.Q0Complex.q0_entry_c; ring
  rw [hq, norm_neg, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrr, hexpL]
  have hX : ‖((P.Qp 0 1 : ℝ) : ℂ) * ((1 - s * (P.sig0 : ℂ) - Complex.exp (-(s * (P.sig0 : ℂ)))) / s ^ 2) +
      ((P.Qpp 0 1 : ℝ) : ℂ) * ((1 - s * (P.sig0 : ℂ) + (s * (P.sig0 : ℂ)) ^ 2 / 2 -
        Complex.exp (-(s * (P.sig0 : ℂ)))) / s ^ 3)‖ ≤
      P.Cq1 / A + P.Cq2 * E / A ^ 2 := by
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos hqp, abs_of_pos hqpp]
    have hb1 := mul_le_mul_of_nonneg_left hphi1 hqp.le
    have hb2 := mul_le_mul_of_nonneg_left hphi2 hqpp.le
    refine le_trans (add_le_add hb1 hb2) ?_
    rw [MixParams.Cq1, MixParams.Cq2]
    have e1 : P.Qp 0 1 * ((1 + P.sig0 * A + E) / A ^ 2) =
        (P.Qp 0 1 * (A * (1 + P.sig0 * A + E))) / A ^ 3 := by field_simp
    have e2 : P.Qpp 0 1 * ((1 + P.sig0 * A + P.sig0 ^ 2 * A ^ 2 / 2 + E) / A ^ 3) =
        (P.Qpp 0 1 * (1 + P.sig0 * A + P.sig0 ^ 2 * A ^ 2 / 2 + E)) / A ^ 3 := by ring
    have e3 : (P.Qp 0 1 + P.Qpp 0 1) * (1 + P.sig0 + P.sig0 ^ 2 / 2) / A +
        (P.Qp 0 1 + P.Qpp 0 1) * E / A ^ 2 =
        ((P.Qp 0 1 + P.Qpp 0 1) * (1 + P.sig0 + P.sig0 ^ 2 / 2) * A ^ 2 +
          (P.Qp 0 1 + P.Qpp 0 1) * E * A) / A ^ 3 := by field_simp
    rw [e1, e2, e3, ← add_div,
      div_le_div_iff_of_pos_right (by positivity : (0:ℝ) < A ^ 3)]
    have hA1 : (0:ℝ) ≤ A - 1 := by linarith
    have hA2 : (0:ℝ) ≤ A ^ 2 - 1 := by nlinarith
    have hA3 : (0:ℝ) ≤ A ^ 2 - A := by nlinarith
    have g1 : (0:ℝ) ≤ P.Qp 0 1 * (A * (A - 1)) :=
      mul_nonneg hqp.le (mul_nonneg hApos.le hA1)
    have g2 : (0:ℝ) ≤ P.Qpp 0 1 * (A ^ 2 - 1) := mul_nonneg hqpp.le hA2
    have g3 : (0:ℝ) ≤ P.Qpp 0 1 * (P.sig0 * (A ^ 2 - A)) :=
      mul_nonneg hqpp.le (mul_nonneg hs0.le hA3)
    have g4 : (0:ℝ) ≤ P.Qpp 0 1 * (E * (A - 1)) :=
      mul_nonneg hqpp.le (mul_nonneg hE0.le hA1)
    have g5 : (0:ℝ) ≤ P.Qp 0 1 * (P.sig0 ^ 2 * A ^ 2 / 2) := by positivity
    nlinarith [g1, g2, g3, g4, g5]
  have hpre : (0:ℝ) ≤ P.rr 0 1 * Real.exp ((P.sig1 - P.sig0) / 2 * x) := by positivity
  calc P.rr 0 1 * Real.exp ((P.sig1 - P.sig0) / 2 * x) * ‖_‖
      ≤ P.rr 0 1 * Real.exp ((P.sig1 - P.sig0) / 2 * x) * (P.Cq1 / A + P.Cq2 * E / A ^ 2) :=
        mul_le_mul_of_nonneg_left hX hpre
    _ = _ := by rw [hEdef, hxdef]

/-! ### From the log-lift to a power of `‖s‖` -/

/-- **The log-lift conversion**: if `x` equals `2·log A/σ` up to `K`, then `e^{θx}` is `A^{2θ/σ}`
up to the fixed factor `e^{|θ|K}`, for *any* sign of `θ`.  Kept in `Real.exp (· * Real.log A)`
form (no `rpow`), matching Stage A's style. -/
theorem exp_theta_le {x A K θ σ : ℝ} (hσ : 0 < σ) (hdev : |x - 2 * Real.log A / σ| ≤ K) :
    Real.exp (θ * x) ≤ Real.exp (|θ| * K) * Real.exp (2 * θ / σ * Real.log A) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 : θ * x = θ * (x - 2 * Real.log A / σ) + 2 * θ / σ * Real.log A := by
    field_simp; ring
  have h2 : θ * (x - 2 * Real.log A / σ) ≤ |θ| * K := by
    calc θ * (x - 2 * Real.log A / σ) ≤ |θ * (x - 2 * Real.log A / σ)| := le_abs_self _
      _ = |θ| * |x - 2 * Real.log A / σ| := abs_mul _ _
      _ ≤ |θ| * K := mul_le_mul_of_nonneg_left hdev (abs_nonneg _)
  linarith [h1]

/-- `θ₁ = λ − r`, the exponential rate of the polynomial part of `q01·e^{r·Re s}`. -/
def MixParams.th1 (P : MixParams) (rdist : ℝ) : ℝ := (P.sig1 - P.sig0) / 2 - rdist

/-- `θ₂ = λ + σ₀ − r`, the exponential rate of the `e^{σ₀x}` part of `q01·e^{r·Re s}`. -/
def MixParams.th2 (P : MixParams) (rdist : ℝ) : ℝ := (P.sig1 - P.sig0) / 2 + P.sig0 - rdist

/-- **The MML.5 decay exponent** `p(r) = max((σ₀−σ₁−2r)/σ₁, (−σ₀−2r)/σ₁)`.  The first branch is the
`e^{σ₀x}/‖s‖²` term of `q01` (dominant when `2σ₀ > σ₁`), the second the `σ₀/‖s‖` term.
`p(r) < −1 ⟺ r > max(σ₀/2, (σ₁−σ₀)/2)`. -/
def MixParams.pexp (P : MixParams) (rdist : ℝ) : ℝ :=
  max ((P.sig0 - P.sig1 - 2 * rdist) / P.sig1) ((-P.sig0 - 2 * rdist) / P.sig1)

/-- The MML.5 magnitude constant. -/
def MixParams.Cmag (P : MixParams) (rdist : ℝ) : ℝ :=
  P.rr 0 1 * (24 * (P.mu + P.K1)) / (P.sig1 * P.mu) *
    (P.Cq1 * Real.exp (|P.th1 rdist| * P.Kdev) + P.Cq2 * Real.exp (|P.th2 rdist| * P.Kdev))

theorem Cmag_pos (P : MixParams) (hP : P.Phys) (rdist : ℝ) : 0 < P.Cmag rdist := by
  have hs0 : 0 < P.sig0 := hP.1
  have hs1 : 0 < P.sig1 := lt_trans hP.1 hP.2.1
  have hmu : 0 < P.mu := mul_pos (hP.2.2.1 1 1) (hP.2.2.2.1 1 1)
  have hK10 := K1_nonneg P hP
  have hrr : 0 < P.rr 0 1 := hP.2.2.1 0 1
  have hq1 : 0 < P.Cq1 := by
    unfold MixParams.Cq1
    have := hP.2.2.2.1 0 1; have := hP.2.2.2.2 0 1; positivity
  have hq2 : 0 < P.Cq2 := by
    unfold MixParams.Cq2; linarith [hP.2.2.2.1 0 1, hP.2.2.2.2 0 1]
  unfold MixParams.Cmag
  have hA : (0:ℝ) < P.mu + P.K1 := by linarith
  positivity

/-- **The per-point MML.5 magnitude bound.**  For any `s` carrying the three disk facts
(`‖s‖ ≥ 1`, log-lift deviation `≤ Kdev`, derivative floor), the residue magnitude
`‖q01(s)‖·e^{r·Re s}/‖F′(s)‖` is `≤ Cmag(r)·‖s‖^{p(r)}` — stated in the `rpow` form the
consumer `mixHS_summable_of_growth` wants. -/
theorem magnitude_bound_at (P : MixParams) (hP : P.Phys) (rdist : ℝ)
    {s : ℂ} (hA : 1 ≤ ‖s‖) (hdev : |(-s.re) - 2 * Real.log ‖s‖ / P.sig1| ≤ P.Kdev)
    (hD : P.sig1 * P.mu / (24 * (P.mu + P.K1)) ≤ ‖derivF P s‖) :
    ‖q01 P s‖ * Real.exp (rdist * s.re) / ‖derivF P s‖ ≤
      P.Cmag rdist * ‖s‖ ^ P.pexp rdist := by
  have hs0 : 0 < P.sig0 := hP.1
  have hs1 : 0 < P.sig1 := lt_trans hP.1 hP.2.1
  have hmu : 0 < P.mu := mul_pos (hP.2.2.1 1 1) (hP.2.2.2.1 1 1)
  have hK10 := K1_nonneg P hP
  have hAA : (0:ℝ) < P.mu + P.K1 := by linarith
  have hrr : 0 < P.rr 0 1 := hP.2.2.1 0 1
  have hApos : (0:ℝ) < ‖s‖ := by linarith
  set A : ℝ := ‖s‖ with hAdef
  set x : ℝ := -s.re with hxdef
  set L : ℝ := Real.log A with hLdef
  have hL0 : 0 ≤ L := Real.log_nonneg hA
  set p : ℝ := P.pexp rdist with hpdef
  -- `1/A = e^{-L}`, `1/A² = e^{-2L}`
  have hAexp : A = Real.exp L := (Real.exp_log hApos).symm
  have hinv1 : 1 / A = Real.exp (-L) := by rw [Real.exp_neg, hAexp]; simp
  have hinv2 : 1 / A ^ 2 = Real.exp (-(2 * L)) := by
    rw [Real.exp_neg, hAexp, ← Real.exp_nat_mul]; push_cast; ring_nf
  -- the two exponent branches
  have hb1 : Real.exp (P.th1 rdist * x) / A ≤
      Real.exp (|P.th1 rdist| * P.Kdev) * Real.exp (p * L) := by
    have h1 := exp_theta_le (x := x) (A := A) (K := P.Kdev) (θ := P.th1 rdist) hs1 hdev
    have hstep : Real.exp (P.th1 rdist * x) / A =
        Real.exp (P.th1 rdist * x) * Real.exp (-L) := by rw [← hinv1]; ring
    have hpB : 2 * P.th1 rdist / P.sig1 - 1 = (-P.sig0 - 2 * rdist) / P.sig1 := by
      unfold MixParams.th1; field_simp; ring
    have hple : (-P.sig0 - 2 * rdist) / P.sig1 ≤ p := by
      rw [hpdef, MixParams.pexp]; exact le_max_right _ _
    rw [hstep]
    calc Real.exp (P.th1 rdist * x) * Real.exp (-L)
        ≤ (Real.exp (|P.th1 rdist| * P.Kdev) * Real.exp (2 * P.th1 rdist / P.sig1 * L)) *
            Real.exp (-L) := by
          exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = Real.exp (|P.th1 rdist| * P.Kdev) *
            Real.exp ((2 * P.th1 rdist / P.sig1 - 1) * L) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring
      _ ≤ Real.exp (|P.th1 rdist| * P.Kdev) * Real.exp (p * L) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le
          rw [hpB]
          exact mul_le_mul_of_nonneg_right hple hL0
  have hb2 : Real.exp (P.th2 rdist * x) / A ^ 2 ≤
      Real.exp (|P.th2 rdist| * P.Kdev) * Real.exp (p * L) := by
    have h1 := exp_theta_le (x := x) (A := A) (K := P.Kdev) (θ := P.th2 rdist) hs1 hdev
    have hstep : Real.exp (P.th2 rdist * x) / A ^ 2 =
        Real.exp (P.th2 rdist * x) * Real.exp (-(2 * L)) := by rw [← hinv2]; ring
    have hpA : 2 * P.th2 rdist / P.sig1 - 2 = (P.sig0 - P.sig1 - 2 * rdist) / P.sig1 := by
      unfold MixParams.th2; field_simp; ring
    have hple : (P.sig0 - P.sig1 - 2 * rdist) / P.sig1 ≤ p := by
      rw [hpdef, MixParams.pexp]; exact le_max_left _ _
    rw [hstep]
    calc Real.exp (P.th2 rdist * x) * Real.exp (-(2 * L))
        ≤ (Real.exp (|P.th2 rdist| * P.Kdev) * Real.exp (2 * P.th2 rdist / P.sig1 * L)) *
            Real.exp (-(2 * L)) := mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = Real.exp (|P.th2 rdist| * P.Kdev) *
            Real.exp ((2 * P.th2 rdist / P.sig1 - 2) * L) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring
      _ ≤ Real.exp (|P.th2 rdist| * P.Kdev) * Real.exp (p * L) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le
          rw [hpA]
          exact mul_le_mul_of_nonneg_right hple hL0
  -- numerator envelope
  have hq := q01_norm_le P hP hA
  have hres : Real.exp (rdist * s.re) = Real.exp (-(rdist * x)) := by rw [hxdef]; ring_nf
  have hnum : ‖q01 P s‖ * Real.exp (rdist * s.re) ≤
      P.rr 0 1 * (P.Cq1 * (Real.exp (|P.th1 rdist| * P.Kdev) * Real.exp (p * L)) +
        P.Cq2 * (Real.exp (|P.th2 rdist| * P.Kdev) * Real.exp (p * L))) := by
    rw [hres]
    have hstep1 : ‖q01 P s‖ * Real.exp (-(rdist * x)) ≤
        (P.rr 0 1 * Real.exp ((P.sig1 - P.sig0) / 2 * x) *
          (P.Cq1 / A + P.Cq2 * Real.exp (P.sig0 * x) / A ^ 2)) * Real.exp (-(rdist * x)) :=
      mul_le_mul_of_nonneg_right hq (Real.exp_pos _).le
    refine le_trans hstep1 ?_
    have hE1 : Real.exp ((P.sig1 - P.sig0) / 2 * x) * Real.exp (-(rdist * x)) =
        Real.exp (P.th1 rdist * x) := by
      rw [← Real.exp_add]; unfold MixParams.th1; congr 1; ring
    have hE2 : Real.exp ((P.sig1 - P.sig0) / 2 * x) * Real.exp (P.sig0 * x) *
        Real.exp (-(rdist * x)) = Real.exp (P.th2 rdist * x) := by
      rw [← Real.exp_add, ← Real.exp_add]; unfold MixParams.th2; congr 1; ring
    have hexpand : (P.rr 0 1 * Real.exp ((P.sig1 - P.sig0) / 2 * x) *
        (P.Cq1 / A + P.Cq2 * Real.exp (P.sig0 * x) / A ^ 2)) * Real.exp (-(rdist * x)) =
        P.rr 0 1 * (P.Cq1 * ((Real.exp ((P.sig1 - P.sig0) / 2 * x) *
            Real.exp (-(rdist * x))) / A) +
          P.Cq2 * ((Real.exp ((P.sig1 - P.sig0) / 2 * x) * Real.exp (P.sig0 * x) *
            Real.exp (-(rdist * x))) / A ^ 2)) := by ring
    rw [hexpand, hE1, hE2]
    refine mul_le_mul_of_nonneg_left ?_ hrr.le
    exact add_le_add (mul_le_mul_of_nonneg_left hb1 (by unfold MixParams.Cq1; nlinarith [hP.2.2.2.1 0 1, hP.2.2.2.2 0 1, hs0]))
      (mul_le_mul_of_nonneg_left hb2 (by unfold MixParams.Cq2; linarith [hP.2.2.2.1 0 1, hP.2.2.2.2 0 1]))
  -- divide by the derivative floor
  have hD0 : (0:ℝ) < P.sig1 * P.mu / (24 * (P.mu + P.K1)) := by positivity
  have hDpos : (0:ℝ) < ‖derivF P s‖ := lt_of_lt_of_le hD0 hD
  have hnum0 : (0:ℝ) ≤ ‖q01 P s‖ * Real.exp (rdist * s.re) := by positivity
  have hdiv : ‖q01 P s‖ * Real.exp (rdist * s.re) / ‖derivF P s‖ ≤
      (P.rr 0 1 * (P.Cq1 * (Real.exp (|P.th1 rdist| * P.Kdev) * Real.exp (p * L)) +
        P.Cq2 * (Real.exp (|P.th2 rdist| * P.Kdev) * Real.exp (p * L)))) /
        (P.sig1 * P.mu / (24 * (P.mu + P.K1))) :=
    FMSA.HardSphere.div_le_div_bound hnum (le_trans hnum0 hnum) hD0 hD
  refine le_trans hdiv (le_of_eq ?_)
  have hrpow : A ^ p = Real.exp (p * L) := by
    rw [Real.rpow_def_of_pos hApos, hLdef]; congr 1; ring
  rw [hrpow, MixParams.Cmag]
  field_simp

/-! ### MML.5-concrete — the gate -/

/-- **The threshold**: `p(r) < −1` exactly when `r > max(σ₀/2, (σ₁−σ₀)/2)`. -/
theorem pexp_lt_neg_one (P : MixParams) (hP : P.Phys) {rdist : ℝ}
    (hrd : max (P.sig0 / 2) ((P.sig1 - P.sig0) / 2) < rdist) : P.pexp rdist < -1 := by
  have hs1 : 0 < P.sig1 := lt_trans hP.1 hP.2.1
  obtain ⟨hr0, hr1⟩ := max_lt_iff.mp hrd
  rw [MixParams.pexp, max_lt_iff]
  constructor
  · rw [div_lt_iff₀ hs1]; linarith
  · rw [div_lt_iff₀ hs1]; linarith

/-- **MML.5-concrete (Stage B) — the per-pole magnitude gate.**  For physical `N = 2` mixture data
and a distance `rdist > max(σ₀/2, (σ₁−σ₀)/2)`, there is an injective family `g` of `detC`-zeros with
linear growth `‖g n‖ ≥ c·n + d` on which

`‖q01(g n)‖ · e^{rdist·Re(g n)} / ‖det′(g n)‖ ≤ Cmag · ‖g n‖^{p}`,  `p = max((σ₀−σ₁−2r)/σ₁, (−σ₀−2r)/σ₁) < −1`.

**Reflection convention.**  The constructed zeros have `Re (g n) < 0`.  Writing `s_k := −(g n)`
(so `Re s_k > 0`, the physical HS pole), the bound reads `‖B_k‖·e^{−rdist·Re s_k} ≤ C‖s_k‖^p` with
`p < −1` — exactly MML.5's gate, since `B_k = −q01(z_k)/det′(z_k)` (`b_k_residue`,
`MixtureHSPoles.lean`).  Consequently `mixHSterm` must be fed `−g n`, not `g n`; fixing that
interface is left to the mixture session (`mixHS_summable_of_growth` is stated for `sfam` directly).

**Exponent.**  `p(r) < −1 ⟺ r > max(σ₀/2, (σ₁−σ₀)/2)`.  The `σ₀/2` branch is the numerically
measured one (`p_eff ≈ (σ₀−σ₁−2r)/σ₁`); the extra `(σ₁−σ₀)/2` branch comes from the genuine
`σ₀/s` term of `q01` and binds only when `2σ₀ < σ₁`. -/
theorem detF_family_magnitude_bound (P : MixParams) (hP : P.Phys) {rdist : ℝ}
    (hrd : max (P.sig0 / 2) ((P.sig1 - P.sig0) / 2) < rdist) :
    ∃ (g : ℕ → ℂ) (C p : ℝ), p < -1 ∧ 0 < C ∧ Function.Injective g ∧
      (∀ n, P.detF (g n) = 0) ∧
      (∃ c d : ℝ, 0 < c ∧ 0 < d ∧ ∀ n : ℕ, c * (n : ℝ) + d ≤ ‖g n‖) ∧
      (∀ n : ℕ, ‖q01 P (g n)‖ * Real.exp (rdist * (g n).re) / ‖derivF P (g n)‖ ≤
        C * ‖g n‖ ^ p) := by
  have hs1 : 0 < P.sig1 := lt_trans hP.1 hP.2.1
  obtain ⟨N1, hN1⟩ := chord_conditions_eventually P hP
  have htends : Filter.Tendsto (fun n : ℕ => 2 * Real.pi * (n : ℝ) / P.sig1)
      Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_div_const hs1
      (Filter.Tendsto.const_mul_atTop (by positivity : (0 : ℝ) < 2 * Real.pi)
        tendsto_natCast_atTop_atTop)
  obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.mp (htends.eventually_ge_atTop 2)
  set N : ℕ := max (max N1 N2) 1 with hNdef
  have hNN1 : N1 ≤ N := le_trans (le_max_left _ _) (le_max_left _ _)
  have hNN2 : N2 ≤ N := le_trans (le_max_right _ _) (le_max_left _ _)
  have hN1le : 1 ≤ N := le_max_right _ _
  obtain ⟨g, hinj, hzero, hmem⟩ := detF_zero_family_in_disks P hP N
    (fun n hn => by
      obtain ⟨a1, a2, a3, a4, _⟩ := hN1 n (le_trans hNN1 hn)
      exact ⟨a1, a2, a3, a4⟩)
  refine ⟨g, P.Cmag rdist, P.pexp rdist, pexp_lt_neg_one P hP hrd, Cmag_pos P hP rdist,
    hinj, hzero, ?_, ?_⟩
  · refine ⟨2 * Real.pi / P.sig1, (2 * Real.pi - 1 / 20) / P.sig1, by positivity,
      div_pos (by linarith [Real.pi_gt_three]) hs1, ?_⟩
    intro n
    have hball := Metric.mem_closedBall.mp (hmem n)
    rw [dist_eq_norm] at hball
    have hrev : ‖sGuess P (n + N)‖ - ‖g n‖ ≤ 1 / (20 * P.sig1) :=
      le_trans (le_trans (norm_sub_norm_le _ _) (le_of_eq (norm_sub_rev _ _))) hball
    have hlow := sGuess_norm_ge P hs1 (n + N)
    have hcast : 2 * Real.pi * ((n : ℝ) + 1) / P.sig1 ≤
        2 * Real.pi * ((n + N : ℕ) : ℝ) / P.sig1 := by
      have hc : ((n + N : ℕ) : ℝ) = (n : ℝ) + (N : ℝ) := by push_cast; ring
      have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1le
      rw [hc, div_le_div_iff_of_pos_right hs1]
      nlinarith [Real.pi_pos]
    have he : 2 * Real.pi / P.sig1 * (n : ℝ) + (2 * Real.pi - 1 / 20) / P.sig1 +
        1 / (20 * P.sig1) = 2 * Real.pi * ((n : ℝ) + 1) / P.sig1 := by field_simp; ring
    linarith
  · intro n
    have hm : N1 ≤ n + N := le_trans hNN1 (Nat.le_add_left N n)
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ := hN1 (n + N) hm
    have hm2 : (2 : ℝ) ≤ 2 * Real.pi * ((n + N : ℕ) : ℝ) / P.sig1 :=
      hN2 (n + N) (le_trans hNN2 (Nat.le_add_left N n))
    have hn1 : 1 ≤ n + N := le_trans hN1le (Nat.le_add_left N n)
    obtain ⟨f1, f2, f3⟩ := disk_facts P hP (n + N) rfl hn1 hm2 c6 c7 c8 c9 c10 c3 (hmem n)
    exact magnitude_bound_at P hP rdist f1 f2 f3

end

end FMSA.MixtureHSPoles
