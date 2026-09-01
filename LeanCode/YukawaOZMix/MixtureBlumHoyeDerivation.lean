/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.YukawaOZMix.MSAMixtureBaxterConv
import LeanCode.YukawaOZMix.MSAMixtureBHRootUneq
import LeanCode.YukawaOZMix.MSAMixtureBHRoot
import LeanCode.YukawaOZ.MSAGSideOZ

/-!
# Mixture leg-3 (general `N`, matrix) — the matrix Baxter transform (MPhase 1)

The multi-component / matrix analog of the scalar leg-3
(`YukawaOZ/MSABlumHoyeDerivation.lean`).  The goal of the whole mixture leg-3 is to **derive** the
posited matrix Blum–Høye root `MSAMixture.MixBHRootUneq` (the matrix constraints (29′)/(33′)) from the
real-space OZ/Baxter primitives — see `proof_notes_leg3_mixture.md`.

**This file — MPhase 1: the matrix Baxter transform** `∫₀^∞ Q_ij(r) e^{−sr} dr = qhatMixCuneq`
(the matrix analog of the scalar `bhBaxter_transform`).  The real-space Baxter factor
`FMSA.ExactMSA.Breakpoint.baxterQ` is piecewise — `0` below `edgeLo σ i j = (σ_j−σ_i)/2`, a
quadratic-plus-exponential core on `[edgeLo, edgeHi]` (`edgeHi = (σ_i+σ_j)/2`), and a two-exponential
tail beyond `edgeHi`.  Its Laplace transform regroups into four support-clean pieces:

* the dressed polynomial `qp·(x−λ−σ_i) + (A/2)(x−λ−σ_i)²` on `[edgeLo, edgeHi]`;
* the Yukawa term `Wt·e^{−z(x−edgeLo)}` on **all** of `[edgeLo, ∞)` (it spans core *and* tail);
* the constant `Ct` on `[edgeLo, edgeHi]`;
* the tail Yukawa `Ct·e^{−z(x−edgeHi)}` on `[edgeHi, ∞)`.

The two Yukawa pieces are handled by the foundational half-line moment `yukawa_shift_laplace_Ioi`
below; the polynomial and constant pieces are compact-interval moments (to come).

## Blueprint

Scalar `bhBaxter_transform` = `bhBaxter_transform_split` (core interval `[0,1]` + pure-exp tail) then
`bhCore_moment_gen`.  Here every scalar identity acquires the `edgeLo`/`edgeHi` support shifts and, in
the assembled (29′)/(33′), a `∑_l ρ_l` species contraction.
-/

open Real MeasureTheory

open MSAMixture FMSA.ExactMSA.Breakpoint

namespace FMSA.ExactMSA.MixLeg3

/-- **The Yukawa-shift Laplace moment over a half-line** — the workhorse for the two exponential
pieces of the mixture Baxter factor.  For `s + z > 0`,
`∫_{x > c} e^{−z(x−p)}·e^{−sx} dx = e^{zp}·e^{−(s+z)c}/(s+z)`.  (With `p = c = edgeLo` it gives the
`Wt` term's `e^{−sλ}·Wt/(s+z)`; with `p = c = edgeHi` the tail's `Ct·e^{−s·σij}/(s+z)`.)  Pure
exponential, via `integral_exp_mul_Ioi`. -/
theorem yukawa_shift_laplace_Ioi (z p s c : ℝ) (hsz : 0 < s + z) :
    ∫ x in Set.Ioi c, Real.exp (-z * (x - p)) * Real.exp (-s * x)
      = Real.exp (z * p) * Real.exp (-(s + z) * c) / (s + z) := by
  have hc : (fun x => Real.exp (-z * (x - p)) * Real.exp (-s * x))
      = fun x => Real.exp (z * p) * Real.exp (-(s + z) * x) := by
    funext x
    rw [← Real.exp_add, show -z * (x - p) + -s * x = z * p + -(s + z) * x from by ring,
        Real.exp_add]
  rw [hc, MeasureTheory.integral_const_mul,
      integral_exp_mul_Ioi (show -(s + z) < 0 by linarith) c, neg_div_neg_eq]
  ring

/-! ### Antiderivative helpers for the compact-core polynomial moment

The `baxterQ` core polynomial `qp·(r−λ−σ_i) + (A/2)(r−λ−σ_i)²` has argument `r − λ − σ_i = r − σ_ij`
(it vanishes at the poly/tail junction `σ_ij = edgeHi`), so its Laplace moment is an FTC exercise with
the classical `φ1`/`φ2` antiderivatives (general `σ`, copied from `HardSphere/BaxterRealSpace.lean`
where they are `private`). -/

private lemma bqExp_hasDerivAt {s : ℝ} (r : ℝ) :
    HasDerivAt (fun x => Real.exp (-s * x)) (Real.exp (-s * r) * -s) r := by
  have h : HasDerivAt (fun x => -s * x) (-s) r := by
    simpa using (hasDerivAt_id r).const_mul (-s)
  exact h.exp

private lemma bqPoly1_hasDerivAt {s : ℝ} (hs : s ≠ 0) (sig r : ℝ) :
    HasDerivAt (fun r => -((r - sig) / s + 1 / s ^ 2) * Real.exp (-s * r))
               ((r - sig) * Real.exp (-s * r)) r := by
  have hg : HasDerivAt (fun x : ℝ => x - sig) 1 r := by
    have h := (hasDerivAt_id r).sub (hasDerivAt_const r sig)
    simp only [id_eq, sub_zero] at h; exact h
  have hA : HasDerivAt (fun x => -((x - sig) / s + 1 / s ^ 2)) (-(1 / s)) r := by
    have h := ((hg.div_const s).add (hasDerivAt_const r (1 / s ^ 2))).neg
    exact h.congr_deriv (by ring)
  exact (hA.mul (bqExp_hasDerivAt r)).congr_deriv (by field_simp [hs]; ring)

private lemma bqPoly2_hasDerivAt {s : ℝ} (hs : s ≠ 0) (sig r : ℝ) :
    HasDerivAt (fun r => -((r - sig) ^ 2 / (2 * s) + (r - sig) / s ^ 2 + 1 / s ^ 3) *
                         Real.exp (-s * r))
               ((r - sig) ^ 2 / 2 * Real.exp (-s * r)) r := by
  have hg : HasDerivAt (fun x : ℝ => x - sig) 1 r := by
    have h := (hasDerivAt_id r).sub (hasDerivAt_const r sig)
    simp only [id_eq, sub_zero] at h; exact h
  have hx2 : HasDerivAt (fun x : ℝ => (x - sig) ^ 2) (2 * (r - sig)) r := by
    have hmul := hg.mul hg
    have heq : ((fun x : ℝ => x - sig) * fun x => x - sig) = fun x => (x - sig) ^ 2 :=
      funext fun x => by simp [sq, Pi.mul_apply]
    rw [heq] at hmul
    exact hmul.congr_deriv (by ring)
  have h1 : HasDerivAt (fun x => (x - sig) ^ 2 / (2 * s)) ((r - sig) / s) r :=
    (hx2.div_const _).congr_deriv (by field_simp [hs])
  have h2 : HasDerivAt (fun x => (x - sig) / s ^ 2) (1 / s ^ 2) r := hg.div_const _
  have h3 : HasDerivAt (fun _ : ℝ => (1 : ℝ) / s ^ 3) 0 r := hasDerivAt_const _ _
  have hA : HasDerivAt (fun x => -((x - sig) ^ 2 / (2 * s) + (x - sig) / s ^ 2 + 1 / s ^ 3))
      (-((r - sig) / s + 1 / s ^ 2)) r := by
    have h := ((h1.add h2).add h3).neg
    exact h.congr_deriv (by ring)
  exact (hA.mul (bqExp_hasDerivAt r)).congr_deriv (by field_simp [hs]; ring)

/-- **Elementary interval exponential moment.**  `∫_a^b e^{−sr} dr = (e^{−sa} − e^{−sb})/s`
(`s ≠ 0`).  The `Ct` core piece. -/
theorem expLin_interval (s a b : ℝ) (hs : s ≠ 0) :
    ∫ r in a..b, Real.exp (-s * r) = (Real.exp (-s * a) - Real.exp (-s * b)) / s := by
  have hd : ∀ r : ℝ, HasDerivAt (fun r => -(Real.exp (-s * r) / s)) (Real.exp (-s * r)) r := by
    intro r
    refine (((bqExp_hasDerivAt r).div_const s).neg).congr_deriv ?_
    field_simp
  have hint : IntervalIntegrable (fun r => Real.exp (-s * r)) volume a b :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable a b
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd r) hint]; ring

/-- **Interval Yukawa-shift moment.**  `∫_a^b e^{−z(r−p)}·e^{−sr} dr
= e^{zp}·e^{−(s+z)a}/(s+z) − e^{zp}·e^{−(s+z)b}/(s+z)` (`s+z ≠ 0`).  The `Wt` core piece; its
`e^{−(s+z)b}` term cancels the tail's (see `baxterQ_transform`). -/
theorem yukawa_shift_interval (z p s a b : ℝ) (hsz : s + z ≠ 0) :
    ∫ r in a..b, Real.exp (-z * (r - p)) * Real.exp (-s * r)
      = Real.exp (z * p) * Real.exp (-(s + z) * a) / (s + z)
        - Real.exp (z * p) * Real.exp (-(s + z) * b) / (s + z) := by
  have hcomb : (fun r => Real.exp (-z * (r - p)) * Real.exp (-s * r))
      = fun r => Real.exp (z * p) * Real.exp (-(s + z) * r) := by
    funext r
    rw [← Real.exp_add, show -z * (r - p) + -s * r = z * p + -(s + z) * r from by ring, Real.exp_add]
  rw [hcomb, intervalIntegral.integral_const_mul]
  have hd : ∀ r : ℝ, HasDerivAt (fun r => -(Real.exp (-(s + z) * r) / (s + z)))
      (Real.exp (-(s + z) * r)) r := by
    intro r
    have h1 : HasDerivAt (fun r : ℝ => -(s + z) * r) (-(s + z)) r := by
      simpa using (hasDerivAt_id r).const_mul (-(s + z))
    have h2 : HasDerivAt (fun r => Real.exp (-(s + z) * r))
        (Real.exp (-(s + z) * r) * -(s + z)) r := h1.exp
    refine ((h2.div_const (s + z)).neg).congr_deriv ?_
    rw [mul_div_assoc, neg_div, div_self hsz, mul_neg_one, neg_neg]
  have hint : IntervalIntegrable (fun r => Real.exp (-(s + z) * r)) volume a b :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable a b
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd r) hint]; ring

/-- Integrability of the Yukawa-shift kernel on a half-line (`s+z > 0`). -/
theorem yukawa_shift_integrableOn_Ioi (z p s c : ℝ) (hsz : 0 < s + z) :
    MeasureTheory.IntegrableOn
      (fun r => Real.exp (-z * (r - p)) * Real.exp (-s * r)) (Set.Ioi c) := by
  have hcomb : (fun r => Real.exp (-z * (r - p)) * Real.exp (-s * r))
      = fun r => Real.exp (z * p) * Real.exp (-(s + z) * r) := by
    funext r
    rw [← Real.exp_add, show -z * (r - p) + -s * r = z * p + -(s + z) * r from by ring, Real.exp_add]
  rw [hcomb]
  exact (exp_neg_integrableOn_Ioi c hsz).const_mul _

/-- **The compact-core polynomial moment of `baxterQ`.**  With `λ = edgeLo σ i j`,
`σ_ij = edgeHi σ i j` and `λ + σ_i = σ_ij`, the poly argument `r − λ − σ_i = r − σ_ij`, so this is the
`φ1`/`φ2` FTC moment shifted to `[λ, σ_ij]`.  Matrix analog of `baxter_poly_moment_gen`. -/
theorem baxterQ_poly_moment {N : ℕ} (σ A : Fin N → ℝ) (qp : Fin N → Fin N → ℝ)
    (i j : Fin N) (s : ℝ) (hs : s ≠ 0) :
    ∫ r in (edgeLo σ i j)..(edgeHi σ i j),
        (qp i j * (r - edgeLo σ i j - σ i) + A j / 2 * (r - edgeLo σ i j - σ i) ^ 2)
          * Real.exp (-s * r)
      = Real.exp (-s * edgeLo σ i j)
          * (qp i j * ((1 - s * σ i - Real.exp (-s * σ i)) / s ^ 2)
             + A j * ((1 - s * σ i + (s * σ i) ^ 2 / 2 - Real.exp (-s * σ i)) / s ^ 3)) := by
  have hLH : edgeHi σ i j = edgeLo σ i j + σ i := by unfold edgeLo edgeHi; ring
  have hcongr : (∫ r in (edgeLo σ i j)..(edgeHi σ i j),
        (qp i j * (r - edgeLo σ i j - σ i) + A j / 2 * (r - edgeLo σ i j - σ i) ^ 2) * Real.exp (-s * r))
      = ∫ r in (edgeLo σ i j)..(edgeHi σ i j),
          (qp i j * ((r - edgeHi σ i j) * Real.exp (-s * r))
           + A j * ((r - edgeHi σ i j) ^ 2 / 2 * Real.exp (-s * r))) := by
    apply intervalIntegral.integral_congr; intro r _; rw [hLH]; ring
  rw [hcongr, intervalIntegral.integral_add
        (by apply Continuous.intervalIntegrable; fun_prop)
        (by apply Continuous.intervalIntegrable; fun_prop),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => bqPoly1_hasDerivAt hs (edgeHi σ i j) r)
        (by apply Continuous.intervalIntegrable; fun_prop),
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => bqPoly2_hasDerivAt hs (edgeHi σ i j) r)
        (by apply Continuous.intervalIntegrable; fun_prop)]
  have hEH' : Real.exp (-s * (edgeLo σ i j + σ i))
      = Real.exp (-s * edgeLo σ i j) * Real.exp (-s * σ i) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hLH]; simp only [hEH']; field_simp; ring

/-- ⭐ **MPhase 1 — the matrix Baxter transform.**  The Laplace transform of the real-space Baxter
factor `baxterQ_ij` (supported on `[edgeLo, ∞)`) is the closed form `qhatMixRuneq` (here written out
with `λ = edgeLo σ i j`, `σ_i`, `σ_ij = edgeHi σ i j`).  Assembled from four support-clean pieces —
the dressed polynomial (`baxterQ_poly_moment`), the `Wt`-Yukawa spanning `[λ, ∞)` (core interval
`yukawa_shift_interval` + tail half-line `yukawa_shift_laplace_Ioi`, whose `e^{−(s+z)σ_ij}` terms
cancel), the constant `Ct` on `[λ, σ_ij]` (`expLin_interval`), and the tail `Ct`-Yukawa on
`(σ_ij, ∞)`.  Matrix analog of the scalar `bhBaxter_transform`. -/
theorem baxterQ_transform {N : ℕ} (z : ℝ) (σ A : Fin N → ℝ) (qp Wt Ct : Fin N → Fin N → ℝ)
    (i j : Fin N) (s : ℝ) (hs : s ≠ 0) (hsz : 0 < s + z) (hσi : 0 ≤ σ i) :
    ∫ r, baxterQ z σ A qp Wt Ct i j r * Real.exp (-s * r)
      = Real.exp (-s * edgeLo σ i j)
          * (qp i j * ((1 - s * σ i - Real.exp (-s * σ i)) / s ^ 2)
             + A j * ((1 - s * σ i + (s * σ i) ^ 2 / 2 - Real.exp (-s * σ i)) / s ^ 3)
             + Wt i j / (s + z)
             + Ct i j * ((1 - Real.exp (-s * σ i)) / s))
        + Ct i j * (Real.exp (-s * edgeHi σ i j) / (s + z)) := by
  have hLH : edgeHi σ i j = edgeLo σ i j + σ i := by unfold edgeLo edgeHi; ring
  have hle : edgeLo σ i j ≤ edgeHi σ i j := by rw [hLH]; linarith
  -- pointwise branch identities
  have hzero : ∀ r ∈ Set.Iio (edgeLo σ i j),
      baxterQ z σ A qp Wt Ct i j r * Real.exp (-s * r) = 0 := by
    intro r hr; simp only [baxterQ, if_pos (Set.mem_Iio.mp hr), zero_mul]
  have hcore_eq : ∀ r ∈ Set.Icc (edgeLo σ i j) (edgeHi σ i j),
      baxterQ z σ A qp Wt Ct i j r
        = qp i j * (r - edgeLo σ i j - σ i) + A j / 2 * (r - edgeLo σ i j - σ i) ^ 2
          + Wt i j * Real.exp (-z * (r - edgeLo σ i j)) + Ct i j := by
    intro r hr; simp only [baxterQ, if_neg (not_lt.mpr hr.1), if_pos hr.2]
  have htail_eq : ∀ r ∈ Set.Ioi (edgeHi σ i j),
      baxterQ z σ A qp Wt Ct i j r
        = Wt i j * Real.exp (-z * (r - edgeLo σ i j))
          + Ct i j * Real.exp (-z * (r - edgeHi σ i j)) := by
    intro r hr
    have h1 : ¬ r < edgeLo σ i j := not_lt.mpr (le_trans hle (le_of_lt hr))
    have h2 : ¬ r ≤ edgeHi σ i j := not_le.mpr hr
    simp only [baxterQ, if_neg h1, if_neg h2]
  -- integrabilities
  have hI_lo : MeasureTheory.IntegrableOn
      (fun r => baxterQ z σ A qp Wt Ct i j r * Real.exp (-s * r)) (Set.Iio (edgeLo σ i j)) := by
    rw [MeasureTheory.integrableOn_congr_fun hzero measurableSet_Iio]
    exact MeasureTheory.integrableOn_zero
  have hI_core : MeasureTheory.IntegrableOn
      (fun r => baxterQ z σ A qp Wt Ct i j r * Real.exp (-s * r))
      (Set.Icc (edgeLo σ i j) (edgeHi σ i j)) :=
    (MeasureTheory.integrableOn_congr_fun (fun r hr => by rw [hcore_eq r hr]) measurableSet_Icc).mpr
      ((by fun_prop : Continuous (fun r =>
        (qp i j * (r - edgeLo σ i j - σ i) + A j / 2 * (r - edgeLo σ i j - σ i) ^ 2
          + Wt i j * Real.exp (-z * (r - edgeLo σ i j)) + Ct i j)
          * Real.exp (-s * r))).integrableOn_Icc)
  have hI_tail : MeasureTheory.IntegrableOn
      (fun r => baxterQ z σ A qp Wt Ct i j r * Real.exp (-s * r)) (Set.Ioi (edgeHi σ i j)) := by
    refine (MeasureTheory.integrableOn_congr_fun (fun r hr => by rw [htail_eq r hr])
      measurableSet_Ioi).mpr ?_
    have hW := (yukawa_shift_integrableOn_Ioi z (edgeLo σ i j) s (edgeHi σ i j) hsz).const_mul (Wt i j)
    have hC := (yukawa_shift_integrableOn_Ioi z (edgeHi σ i j) s (edgeHi σ i j) hsz).const_mul (Ct i j)
    exact (MeasureTheory.integrableOn_congr_fun (fun r _ => by simp only [Pi.add_apply]; ring)
      measurableSet_Ioi).mpr (hW.add hC)
  have hI_ici : MeasureTheory.IntegrableOn
      (fun r => baxterQ z σ A qp Wt Ct i j r * Real.exp (-s * r)) (Set.Ici (edgeLo σ i j)) := by
    rw [← Set.Icc_union_Ioi_eq_Ici hle]; exact hI_core.union hI_tail
  have hdisj : Disjoint (Set.Icc (edgeLo σ i j) (edgeHi σ i j)) (Set.Ioi (edgeHi σ i j)) := by
    rw [Set.disjoint_left]; rintro x hx1 hx2; exact absurd hx1.2 (not_le.mpr hx2)
  -- domain split ℝ = Iio ⊔ (Icc ⊔ Ioi)
  have hsplit : (∫ r, baxterQ z σ A qp Wt Ct i j r * Real.exp (-s * r))
      = (∫ r in Set.Iio (edgeLo σ i j), baxterQ z σ A qp Wt Ct i j r * Real.exp (-s * r))
        + ((∫ r in Set.Icc (edgeLo σ i j) (edgeHi σ i j),
              baxterQ z σ A qp Wt Ct i j r * Real.exp (-s * r))
           + (∫ r in Set.Ioi (edgeHi σ i j),
              baxterQ z σ A qp Wt Ct i j r * Real.exp (-s * r))) := by
    rw [← MeasureTheory.setIntegral_univ,
        show (Set.univ : Set ℝ) = Set.Iio (edgeLo σ i j) ∪ Set.Ici (edgeLo σ i j) from
          (Set.Iio_union_Ici).symm,
        MeasureTheory.setIntegral_union (Set.Iio_disjoint_Ici le_rfl) measurableSet_Ici hI_lo hI_ici,
        ← Set.Icc_union_Ioi_eq_Ici hle,
        MeasureTheory.setIntegral_union hdisj measurableSet_Ioi hI_core hI_tail]
  -- the three pieces
  have hI_lo_zero : (∫ r in Set.Iio (edgeLo σ i j),
      baxterQ z σ A qp Wt Ct i j r * Real.exp (-s * r)) = 0 :=
    MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero hzero
  have hcore : (∫ r in Set.Icc (edgeLo σ i j) (edgeHi σ i j),
        baxterQ z σ A qp Wt Ct i j r * Real.exp (-s * r))
      = Real.exp (-s * edgeLo σ i j)
          * (qp i j * ((1 - s * σ i - Real.exp (-s * σ i)) / s ^ 2)
             + A j * ((1 - s * σ i + (s * σ i) ^ 2 / 2 - Real.exp (-s * σ i)) / s ^ 3))
        + Wt i j * (Real.exp (z * edgeLo σ i j) * Real.exp (-(s + z) * edgeLo σ i j) / (s + z)
             - Real.exp (z * edgeLo σ i j) * Real.exp (-(s + z) * edgeHi σ i j) / (s + z))
        + Ct i j * ((Real.exp (-s * edgeLo σ i j) - Real.exp (-s * edgeHi σ i j)) / s) := by
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun r hr => by rw [hcore_eq r hr]),
        MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]
    have hsplit3 : (∫ r in (edgeLo σ i j)..(edgeHi σ i j),
          (qp i j * (r - edgeLo σ i j - σ i) + A j / 2 * (r - edgeLo σ i j - σ i) ^ 2
            + Wt i j * Real.exp (-z * (r - edgeLo σ i j)) + Ct i j) * Real.exp (-s * r))
        = (∫ r in (edgeLo σ i j)..(edgeHi σ i j),
            (qp i j * (r - edgeLo σ i j - σ i) + A j / 2 * (r - edgeLo σ i j - σ i) ^ 2)
              * Real.exp (-s * r))
          + (Wt i j * (∫ r in (edgeLo σ i j)..(edgeHi σ i j),
              Real.exp (-z * (r - edgeLo σ i j)) * Real.exp (-s * r))
             + Ct i j * (∫ r in (edgeLo σ i j)..(edgeHi σ i j), Real.exp (-s * r))) := by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
          ← intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
            (by apply Continuous.intervalIntegrable; fun_prop),
          ← intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
            (by apply Continuous.intervalIntegrable; fun_prop)]
      apply intervalIntegral.integral_congr; intro r _; ring
    rw [hsplit3, baxterQ_poly_moment σ A qp i j s hs,
        yukawa_shift_interval z (edgeLo σ i j) s (edgeLo σ i j) (edgeHi σ i j) hsz.ne',
        expLin_interval s (edgeLo σ i j) (edgeHi σ i j) hs]
    ring
  have htail : (∫ r in Set.Ioi (edgeHi σ i j),
        baxterQ z σ A qp Wt Ct i j r * Real.exp (-s * r))
      = Wt i j * (Real.exp (z * edgeLo σ i j) * Real.exp (-(s + z) * edgeHi σ i j) / (s + z))
        + Ct i j * (Real.exp (z * edgeHi σ i j) * Real.exp (-(s + z) * edgeHi σ i j) / (s + z)) := by
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun r hr => by rw [htail_eq r hr])]
    have hadd : (fun r => (Wt i j * Real.exp (-z * (r - edgeLo σ i j))
          + Ct i j * Real.exp (-z * (r - edgeHi σ i j))) * Real.exp (-s * r))
        = fun r => Wt i j * (Real.exp (-z * (r - edgeLo σ i j)) * Real.exp (-s * r))
            + Ct i j * (Real.exp (-z * (r - edgeHi σ i j)) * Real.exp (-s * r)) := by
      funext r; ring
    rw [hadd, MeasureTheory.integral_add
          ((yukawa_shift_integrableOn_Ioi z (edgeLo σ i j) s (edgeHi σ i j) hsz).const_mul _)
          ((yukawa_shift_integrableOn_Ioi z (edgeHi σ i j) s (edgeHi σ i j) hsz).const_mul _),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
        yukawa_shift_laplace_Ioi z (edgeLo σ i j) s (edgeHi σ i j) hsz,
        yukawa_shift_laplace_Ioi z (edgeHi σ i j) s (edgeHi σ i j) hsz]
  -- assemble + cancel the exponential atoms
  have hR1 : Real.exp (z * edgeLo σ i j) * Real.exp (-(s + z) * edgeLo σ i j)
      = Real.exp (-s * edgeLo σ i j) := by rw [← Real.exp_add]; congr 1; ring
  have hR2 : Real.exp (z * edgeHi σ i j) * Real.exp (-(s + z) * edgeHi σ i j)
      = Real.exp (-s * edgeHi σ i j) := by rw [← Real.exp_add]; congr 1; ring
  have hEH : Real.exp (-s * edgeHi σ i j)
      = Real.exp (-s * edgeLo σ i j) * Real.exp (-s * σ i) := by
    rw [hLH, ← Real.exp_add]; congr 1; ring
  rw [hsplit, hI_lo_zero, hcore, htail]
  simp only [hR1, hR2, hEH]
  field_simp
  ring

/-- **MPhase 1, wired to the posited transform.**  `baxterQ_transform` restated as
`∫₀^∞ Q_ij e^{−sr} = qhatMixRuneq …` — i.e. the posited real-`s` Baxter factor
`MSAMixture.qhatMixRuneq` (consumed by the (29′)/(33′) residual gate `MixBHRootUneq`) **is** the
Laplace transform of the real-space Baxter factor `baxterQ`.  Cosmetic bridge: unfold
`qhatMixRuneq`/`edgeLo`/`edgeHi` and reconcile `−s·x ↔ −(s·x)` and the qp/A multiplication order. -/
theorem baxterQ_transform_eq_qhatMixRuneq {N : ℕ} (z : ℝ) (σ A : Fin N → ℝ)
    (qp Wt Ct : Fin N → Fin N → ℝ) (i j : Fin N) (s : ℝ) (hs : s ≠ 0) (hsz : 0 < s + z)
    (hσi : 0 ≤ σ i) :
    ∫ r, baxterQ z σ A qp Wt Ct i j r * Real.exp (-s * r)
      = qhatMixRuneq z σ qp Wt Ct A s i j := by
  rw [baxterQ_transform z σ A qp Wt Ct i j s hs hsz hσi]
  simp only [qhatMixRuneq, edgeLo, edgeHi, neg_mul]
  ring

/-! ### MPhase 2 — the matrix exterior Baxter relation (c-side)

On the **exterior** `r > σ_ij = edgeHi`, the Baxter convolution `∑_l ρ_l ∫ Q'_il(t+r)·Q_jl(t) dt`
reduces to the MPhase-1 transform `Q̂_jl(z)`: because `edgeLo_jl + edgeHi_ij = edgeHi_il`, whenever
`Q_jl(t) ≠ 0` (i.e. `t ≥ edgeLo_jl`) the shifted argument `t + r` exceeds `edgeHi_il`, so `Q'_il(t+r)`
is in its **tail** `−z(Wt_il e^{−z(·−edgeLo_il)} + Ct_il e^{−z(·−edgeHi_il)})`, which factors as
`e^{−zr}·(coeff)·e^{−zt}` — pulling `e^{−zr}` out and leaving `∫ Q_jl(t) e^{−zt} dt = Q̂_jl(z)`.
This is the matrix analog of the scalar `bh_exterior_baxter_relation`; matching to the MSA closure
`matMSAtail` (Yukawa tail) yields the c-side constraint (29′). -/

/-- **The per-`l` exterior Baxter convolution.**  For `r > edgeHi σ i j`, the shifted convolution of
the Baxter derivative `Q'_il` with `Q_jl` factors through the MPhase-1 transform `Q̂_jl(z) =
qhatMixRuneq … z j l`.  Reuses `baxterQ_transform_eq_qhatMixRuneq`. -/
theorem baxterQ_exterior_conv {N : ℕ} (z : ℝ) (hz : 0 < z) (σ A : Fin N → ℝ)
    (qp Wt Ct : Fin N → Fin N → ℝ) (i j l : Fin N) (r : ℝ)
    (hσ : ∀ k, 0 ≤ σ k) (hr : edgeHi σ i j < r) :
    ∫ t, baxterQ' z σ A qp Wt Ct i l (t + r) * baxterQ z σ A qp Wt Ct j l t
      = -z * Real.exp (-z * r)
        * (Wt i l * Real.exp (z * edgeLo σ i l) + Ct i l * Real.exp (z * edgeHi σ i l))
        * qhatMixRuneq z σ qp Wt Ct A z j l := by
  have hz' : z ≠ 0 := hz.ne'
  have hzz : (0:ℝ) < z + z := by linarith
  have hil : edgeLo σ i l ≤ edgeHi σ i l := by unfold edgeLo edgeHi; linarith [hσ i]
  have hedge : edgeLo σ j l + edgeHi σ i j = edgeHi σ i l := by unfold edgeLo edgeHi; ring
  have hstep : (∫ t, baxterQ' z σ A qp Wt Ct i l (t + r) * baxterQ z σ A qp Wt Ct j l t)
      = ∫ t, (-z * Real.exp (-z * r)
            * (Wt i l * Real.exp (z * edgeLo σ i l) + Ct i l * Real.exp (z * edgeHi σ i l)))
          * (baxterQ z σ A qp Wt Ct j l t * Real.exp (-z * t)) := by
    apply MeasureTheory.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro t
    dsimp only
    by_cases htj : t < edgeLo σ j l
    · rw [show baxterQ z σ A qp Wt Ct j l t = 0 from by simp only [baxterQ, if_pos htj]]; ring
    · push_neg at htj
      have ht1 : edgeHi σ i l < t + r := by linarith [hedge]
      have h1 : ¬ (t + r < edgeLo σ i l) := not_lt.mpr (by linarith)
      have h2 : ¬ (t + r ≤ edgeHi σ i l) := not_le.mpr ht1
      have e1 : Real.exp (-z * (t + r - edgeLo σ i l))
          = Real.exp (-z * r) * Real.exp (z * edgeLo σ i l) * Real.exp (-z * t) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      have e2 : Real.exp (-z * (t + r - edgeHi σ i l))
          = Real.exp (-z * r) * Real.exp (z * edgeHi σ i l) * Real.exp (-z * t) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      simp only [baxterQ', if_neg h1, if_neg h2]
      rw [e1, e2]; ring
  rw [hstep, MeasureTheory.integral_const_mul,
      baxterQ_transform_eq_qhatMixRuneq z σ A qp Wt Ct j l z hz' hzz (hσ j)]

/-- **The matrix exterior Baxter relation (Blum–Høye Eq. 8, mixture).**  For `r > edgeHi σ i j`,
`−Q'_ij(r) + ∑_l ρ_l ∫ Q'_il(t+r) Q_jl(t) dt = z e^{−zr}·(S_ij − ∑_l ρ_l S_il Q̂_jl(z))`, where
`S_ab = Wt_ab e^{z·edgeLo_ab} + Ct_ab e^{z·edgeHi_ab}`.  Matrix analog of the scalar
`bh_exterior_baxter_relation`.  On the exterior the Baxter core `baxterConvCore·(2πr)` equals this;
matching against `2πr·matMSAtail_ij = 2π K_ij e^{z·edgeHi_ij} e^{−zr}` gives the c-side (29′). -/
theorem mat_exterior_baxter_relation {N : ℕ} (z : ℝ) (hz : 0 < z) (ρ σ A : Fin N → ℝ)
    (qp Wt Ct : Fin N → Fin N → ℝ) (i j : Fin N) (r : ℝ)
    (hσ : ∀ k, 0 ≤ σ k) (hr : edgeHi σ i j < r) :
    -baxterQ' z σ A qp Wt Ct i j r
        + ∑ l, ρ l * ∫ t, baxterQ' z σ A qp Wt Ct i l (t + r) * baxterQ z σ A qp Wt Ct j l t
      = z * Real.exp (-z * r)
        * ((Wt i j * Real.exp (z * edgeLo σ i j) + Ct i j * Real.exp (z * edgeHi σ i j))
           - ∑ l, ρ l * (Wt i l * Real.exp (z * edgeLo σ i l) + Ct i l * Real.exp (z * edgeHi σ i l))
               * qhatMixRuneq z σ qp Wt Ct A z j l) := by
  have hij : edgeLo σ i j ≤ edgeHi σ i j := by unfold edgeLo edgeHi; linarith [hσ i]
  have hQ' : baxterQ' z σ A qp Wt Ct i j r
      = -z * Wt i j * Real.exp (-z * (r - edgeLo σ i j))
        - z * Ct i j * Real.exp (-z * (r - edgeHi σ i j)) := by
    have h1 : ¬ (r < edgeLo σ i j) := not_lt.mpr (by linarith)
    have h2 : ¬ (r ≤ edgeHi σ i j) := not_le.mpr hr
    simp only [baxterQ', if_neg h1, if_neg h2]
  have eL : Real.exp (-z * (r - edgeLo σ i j))
      = Real.exp (-z * r) * Real.exp (z * edgeLo σ i j) := by rw [← Real.exp_add]; congr 1; ring
  have eH : Real.exp (-z * (r - edgeHi σ i j))
      = Real.exp (-z * r) * Real.exp (z * edgeHi σ i j) := by rw [← Real.exp_add]; congr 1; ring
  rw [hQ', eL, eH,
      Finset.sum_congr rfl (fun l _ => by
        rw [baxterQ_exterior_conv z hz σ A qp Wt Ct i j l r hσ hr]),
      Finset.sum_congr rfl (fun l _ => show
        ρ l * (-z * Real.exp (-z * r)
              * (Wt i l * Real.exp (z * edgeLo σ i l) + Ct i l * Real.exp (z * edgeHi σ i l))
              * qhatMixRuneq z σ qp Wt Ct A z j l)
          = (-z * Real.exp (-z * r))
            * (ρ l * (Wt i l * Real.exp (z * edgeLo σ i l) + Ct i l * Real.exp (z * edgeHi σ i l))
                * qhatMixRuneq z σ qp Wt Ct A z j l) from by ring),
      ← Finset.mul_sum]
  ring

/-! ### MPhase 2 — the amplitude algebra `S = e^{z·edgeHi}·Dt` and the (29′) reduction

The exterior Baxter relation's amplitude bundle `S_ab = Wt_ab e^{z·edgeLo_ab} + Ct_ab e^{z·edgeHi_ab}`
collapses to `e^{z·edgeHi_ab}·Dt_ab` via the `e^{zσ}` cancellation `MSAMixture.cancellation_star`
(`Dt − Ct = e^{−zσ}·Wt`).  Substituting into `mat_exterior_baxter_relation` puts the exterior Baxter
convolution entirely in terms of `Dt` and the transform `Q̂`.

⚠ **FINDING (σ-edge).** Matching against `matMSAtail` (`2πr·c_ij = 2π K_ij e^{z·σ_ij} e^{−zr}`) then
gives the c-side constraint

    (♦)   Dt_ij − ∑_l ρ_l · e^{z·edgeLo_jl} · Dt_il · Q̂_jl(z) = 2π K_ij / z,

with a **recentering factor `e^{z·edgeLo_jl}`** on the transform (it arises structurally from
`edgeHi_il − edgeHi_ij = edgeLo_jl`, the row-`i` tail edge vs the diagonal `K` edge).  At **equal** σ,
`edgeLo_jl = 0`, so (♦) coincides with the posited `MixBHRootUneq` (29′)
`Dt_ij − ∑_l ρ_l Dt_il Q̂_jl(z) = 2πK_ij/z`; at **unequal** σ they differ.  The `S = e^{z·edgeHi}·Dt`
identity is confirmed to `4.4e-16` numerically (`scratchpad/scheck.py`) and proved below, and
`mat_exterior_baxter_relation` is axiom-clean, so (♦) is the rigorously-derived form.  The posited (29′)
therefore appears to need the recentered transform `e^{z·edgeLo_jl}·qhatMixRuneq_jl` (i.e. the Baxter
`Q̂` centered at the support edge) for the unequal-σ root — a σ-power factor of the exact kind that
`σ=1` masks. Flagged for reconciliation before the wire-in (MPhase 5). -/

/-- **The exterior-amplitude bundle collapses to `Dt`.**  `Wt_il e^{z·edgeLo_il} + Ct_il e^{z·edgeHi_il}
= e^{z·edgeHi_il}·Dt_il`, via `MSAMixture.cancellation_star` (`Dt − Ct = e^{−zσ}·Wt`) and
`e^{−zσ_i}·e^{z·edgeHi_il} = e^{z·edgeLo_il}` (which cancels the two `Wt` terms). -/
theorem baxterS_eq_edgeHi_Dt {N : ℕ} (z : ℝ) (ρ σ : Fin N → ℝ)
    (Gt Dt : Matrix (Fin N) (Fin N) ℝ) (i l : Fin N) :
    Wt z ρ Gt Dt i l * Real.exp (z * edgeLo σ i l)
        + Ct z ρ σ Gt Dt i l * Real.exp (z * edgeHi σ i l)
      = Real.exp (z * edgeHi σ i l) * Dt i l := by
  have hc := cancellation_star z ρ σ Gt Dt i l
  have hkey : Real.exp (-z * σ i) * Real.exp (z * edgeHi σ i l) = Real.exp (z * edgeLo σ i l) := by
    rw [← Real.exp_add]; congr 1; unfold edgeLo edgeHi; ring
  have hCt : Ct z ρ σ Gt Dt i l = Dt i l - Real.exp (-z * σ i) * Wt z ρ Gt Dt i l := by
    linarith [hc]
  rw [hCt,
      show Wt z ρ Gt Dt i l * Real.exp (z * edgeLo σ i l)
            + (Dt i l - Real.exp (-z * σ i) * Wt z ρ Gt Dt i l) * Real.exp (z * edgeHi σ i l)
          = Wt z ρ Gt Dt i l * Real.exp (z * edgeLo σ i l)
            + Dt i l * Real.exp (z * edgeHi σ i l)
            - Wt z ρ Gt Dt i l * (Real.exp (-z * σ i) * Real.exp (z * edgeHi σ i l)) from by ring,
      hkey]
  ring

/-- **The exterior Baxter relation in `Dt` form** (physical MSA amplitudes).  Combining
`mat_exterior_baxter_relation` with `baxterS_eq_edgeHi_Dt`: on `r > edgeHi σ i j`,
`−Q'_ij(r) + ∑_l ρ_l ∫ Q'_il(t+r)Q_jl(t)dt
= z e^{−zr}(e^{z·edgeHi_ij}Dt_ij − ∑_l ρ_l e^{z·edgeHi_il}Dt_il Q̂_jl(z))`.  Matching `matMSAtail`
yields the c-side constraint (♦) (see the `FINDING` note above). -/
theorem mat_exterior_baxter_relation_Dt {N : ℕ} (z : ℝ) (hz : 0 < z) (ρ σ : Fin N → ℝ)
    (Gt Dt : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) (r : ℝ)
    (hσ : ∀ k, 0 ≤ σ k) (hr : edgeHi σ i j < r) :
    -baxterQ' z σ (AVec z ρ σ Gt Dt) (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt) i j r
        + ∑ l, ρ l * ∫ t, baxterQ' z σ (AVec z ρ σ Gt Dt) (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt)
              (Ct z ρ σ Gt Dt) i l (t + r)
              * baxterQ z σ (AVec z ρ σ Gt Dt) (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt)
                  (Ct z ρ σ Gt Dt) j l t
      = z * Real.exp (-z * r)
        * (Real.exp (z * edgeHi σ i j) * Dt i j
           - ∑ l, ρ l * (Real.exp (z * edgeHi σ i l) * Dt i l)
               * qhatMixRuneq z σ (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt)
                   (AVec z ρ σ Gt Dt) z j l) := by
  rw [mat_exterior_baxter_relation z hz ρ σ (AVec z ρ σ Gt Dt) (qpMat z ρ σ Gt Dt)
        (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt) i j r hσ hr,
      baxterS_eq_edgeHi_Dt z ρ σ Gt Dt i j,
      Finset.sum_congr rfl (fun l _ => by rw [baxterS_eq_edgeHi_Dt z ρ σ Gt Dt i l])]

/-- ⭐ **The c-side constraint (♦), derived from the exterior MSA closure.**  Given the physical Baxter
Eq (8) closure `hbax` (`2πr·c_ij = 2πr·matMSAtail_ij` equals the Baxter convolution right-hand side on
the exterior `r > σ_ij`), the c-side constraint is

  `Dt_ij − ∑_l ρ_l · e^{z·edgeLo_jl} · Dt_il · Q̂_jl(z) = 2π K_ij / z`.

This is the rigorously-derived matrix analog of the scalar `h29_of_baxter_exterior` — **with the
recentering factor `e^{z·edgeLo_jl}` on the transform** (`= e^{z(edgeHi_il − edgeHi_ij)}`), which
`MSAMixture.MixBHRootUneq` (29′) **now uses** (the σ-edge FINDING; the recentering fix is applied and
`mixBHRootUneq_cSide_of_exterior` shows the corrected (29′) conjunct is exactly this).  At equal σ
(`edgeLo_jl = 0`) the factor is `1` and reduces to the naive form.  Proof: evaluate `hbax` at
`r = σ_ij + 1`, fold the convolution by `mat_exterior_baxter_relation_Dt`, compute
`2πr·matMSAtail = 2π K_ij e^{−z}`, and cancel the common `z·e^{−z}`. -/
theorem c_side_constraint_of_exterior {N : ℕ} (z : ℝ) (hz : 0 < z) (ρ σ : Fin N → ℝ)
    (Gt Dt K : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) (hσ : ∀ k, 0 ≤ σ k)
    (hbax : ∀ r, edgeHi σ i j < r →
      2 * Real.pi * r * matMSAtail K z σ i j r
        = -baxterQ' z σ (AVec z ρ σ Gt Dt) (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt) i j r
          + ∑ l, ρ l * ∫ t, baxterQ' z σ (AVec z ρ σ Gt Dt) (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt)
                (Ct z ρ σ Gt Dt) i l (t + r)
                * baxterQ z σ (AVec z ρ σ Gt Dt) (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt)
                    (Ct z ρ σ Gt Dt) j l t) :
    Dt i j - ∑ l, ρ l * (Real.exp (z * edgeLo σ j l) * Dt i l)
        * qhatMixRuneq z σ (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt) (AVec z ρ σ Gt Dt) z j l
      = 2 * Real.pi * K i j / z := by
  have hr : edgeHi σ i j < edgeHi σ i j + 1 := by linarith
  have key := hbax (edgeHi σ i j + 1) hr
  rw [mat_exterior_baxter_relation_Dt z hz ρ σ Gt Dt i j (edgeHi σ i j + 1) hσ hr] at key
  -- the exterior LHS `2π(σ_ij+1)·matMSAtail = 2π K_ij e^{−z}`
  have hLHS : 2 * Real.pi * (edgeHi σ i j + 1) * matMSAtail K z σ i j (edgeHi σ i j + 1)
      = 2 * Real.pi * K i j * Real.exp (-z) := by
    unfold matMSAtail cMSAtail
    rw [if_pos (show sigMix σ i j < edgeHi σ i j + 1 from by unfold sigMix edgeHi; linarith),
        show -z * (edgeHi σ i j + 1 - sigMix σ i j) = -z from by unfold sigMix edgeHi; ring]
    have hne : edgeHi σ i j + 1 ≠ 0 :=
      ne_of_gt (show (0:ℝ) < edgeHi σ i j + 1 by unfold edgeHi; have := hσ i; have := hσ j; linarith)
    field_simp
  rw [hLHS] at key
  -- the two exponential regroupings (`e^{−z(σ_ij+1)}·e^{z·edgeHi_i·}`)
  have hDt : Real.exp (-z * (edgeHi σ i j + 1)) * Real.exp (z * edgeHi σ i j) = Real.exp (-z) := by
    rw [← Real.exp_add]; congr 1; ring
  have hsum : ∀ l : Fin N, Real.exp (-z * (edgeHi σ i j + 1)) * Real.exp (z * edgeHi σ i l)
      = Real.exp (-z) * Real.exp (z * edgeLo σ j l) := by
    intro l; rw [← Real.exp_add, ← Real.exp_add]; congr 1; unfold edgeHi edgeLo; ring
  -- fold the `e^{−z(σ_ij+1)}` into the bracket, leaving the recentered `e^{z·edgeLo_jl}`
  have hkey2 : z * Real.exp (-z * (edgeHi σ i j + 1))
        * (Real.exp (z * edgeHi σ i j) * Dt i j
           - ∑ l, ρ l * (Real.exp (z * edgeHi σ i l) * Dt i l)
               * qhatMixRuneq z σ (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt)
                   (AVec z ρ σ Gt Dt) z j l)
      = z * Real.exp (-z)
        * (Dt i j - ∑ l, ρ l * (Real.exp (z * edgeLo σ j l) * Dt i l)
               * qhatMixRuneq z σ (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt)
                   (AVec z ρ σ Gt Dt) z j l) := by
    rw [mul_sub, mul_sub, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · rw [show z * Real.exp (-z * (edgeHi σ i j + 1)) * (Real.exp (z * edgeHi σ i j) * Dt i j)
            = z * (Real.exp (-z * (edgeHi σ i j + 1)) * Real.exp (z * edgeHi σ i j)) * Dt i j
            from by ring, hDt]
    · refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [show z * Real.exp (-z * (edgeHi σ i j + 1))
              * (ρ l * (Real.exp (z * edgeHi σ i l) * Dt i l)
                  * qhatMixRuneq z σ (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt)
                      (AVec z ρ σ Gt Dt) z j l)
            = z * (Real.exp (-z * (edgeHi σ i j + 1)) * Real.exp (z * edgeHi σ i l))
              * (ρ l * Dt i l
                  * qhatMixRuneq z σ (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt)
                      (AVec z ρ σ Gt Dt) z j l) from by ring, hsum l]
      ring
  rw [hkey2] at key
  -- cancel `z·e^{−z}`
  have hze : z * Real.exp (-z) ≠ 0 := mul_ne_zero hz.ne' (Real.exp_ne_zero _)
  apply mul_left_cancel₀ hze
  rw [← key]; field_simp

/-- **The c-side conjunct of the (recentered) `MixBHRootUneq`, derived from the exterior closure.**
Given the c-side exterior MSA closure `hbax` for every `(i,j)`, the **(29′) conjunct of
`MSAMixture.MixBHRootUneq`** (with the recentered transform `e^{z·edgeLo_jl}·Q̂_jl`) holds.  Direct
corollary of `c_side_constraint_of_exterior` + `∑_l Dt_il·δ_lj = Dt_ij`: the recentered (29′) is
**exactly** the OZ/Baxter-derived (♦), confirming the `MixBHRootUneq` recentering fix on the c-side. -/
theorem mixBHRootUneq_cSide_of_exterior {N : ℕ} (z : ℝ) (hz : 0 < z) (ρ σ : Fin N → ℝ)
    (Gt Dt K : Matrix (Fin N) (Fin N) ℝ) (hσ : ∀ k, 0 ≤ σ k)
    (hbax : ∀ i j r, edgeHi σ i j < r →
      2 * Real.pi * r * matMSAtail K z σ i j r
        = -baxterQ' z σ (AVec z ρ σ Gt Dt) (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt) i j r
          + ∑ l, ρ l * ∫ t, baxterQ' z σ (AVec z ρ σ Gt Dt) (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt)
                (Ct z ρ σ Gt Dt) i l (t + r)
                * baxterQ z σ (AVec z ρ σ Gt Dt) (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt)
                    (Ct z ρ σ Gt Dt) j l t) :
    ∀ i j, ∑ l, Dt i l * ((if l = j then (1 : ℝ) else 0)
        - ρ l * (Real.exp (z * edgeLo σ j l)
            * qhatMixRuneq z σ (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt)
                (AVec z ρ σ Gt Dt) z j l))
      = 2 * Real.pi * K i j / z := by
  intro i j
  have hc := c_side_constraint_of_exterior z hz ρ σ Gt Dt K i j hσ (hbax i j)
  have hsum : (∑ l, Dt i l * ((if l = j then (1 : ℝ) else 0)
        - ρ l * (Real.exp (z * edgeLo σ j l)
            * qhatMixRuneq z σ (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt)
                (AVec z ρ σ Gt Dt) z j l)))
      = Dt i j - ∑ l, ρ l * (Real.exp (z * edgeLo σ j l) * Dt i l)
          * qhatMixRuneq z σ (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt)
              (AVec z ρ σ Gt Dt) z j l := by
    rw [Finset.sum_congr rfl (fun l _ => by ring :
          ∀ l ∈ Finset.univ, Dt i l * ((if l = j then (1 : ℝ) else 0)
              - ρ l * (Real.exp (z * edgeLo σ j l)
                  * qhatMixRuneq z σ (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt)
                      (AVec z ρ σ Gt Dt) z j l))
            = Dt i l * (if l = j then (1 : ℝ) else 0)
              - ρ l * (Real.exp (z * edgeLo σ j l) * Dt i l)
                  * qhatMixRuneq z σ (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt)
                      (AVec z ρ σ Gt Dt) z j l),
        Finset.sum_sub_distrib]
    congr 1
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hsum]; exact hc

/-- **`(♦) ⟹ hbax`** — the reverse of `c_side_constraint_of_exterior`, completing the equivalence.  Given
the c-side constraint (♦) `Dt_ij − ∑_l ρ_l e^{z·edgeLo_jl} Dt_il Q̂_jl = 2πK_ij/z`, the exterior Baxter
Eq (8) closure holds at **every** exterior point `r > edgeHi_ij`: fold the Baxter convolution by
`mat_exterior_baxter_relation_Dt` (`= z e^{−zr}(e^{z·edgeHi_ij}Dt_ij − ∑ρ_l e^{z·edgeHi_il}Dt_il Q̂_jl)`),
compute `2πr·matMSAtail = 2πK_ij e^{z·edgeHi_ij} e^{−zr}` (the `r` cancels in `cMSAtail`), and match via
`(♦)` scaled by `z·e^{z·edgeHi_ij}`, using the edge identity `edgeHi_ij + edgeLo_jl = edgeHi_il`. -/
theorem mat_hbax_of_cside {N : ℕ} (z : ℝ) (hz : 0 < z) (ρ σ : Fin N → ℝ)
    (Gt Dt K : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) (hσ : ∀ k, 0 ≤ σ k)
    (hcside : Dt i j - ∑ l, ρ l * (Real.exp (z * edgeLo σ j l) * Dt i l)
        * qhatMixRuneq z σ (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt) (AVec z ρ σ Gt Dt) z j l
      = 2 * Real.pi * K i j / z) :
    ∀ r, edgeHi σ i j < r →
      2 * Real.pi * r * matMSAtail K z σ i j r
        = -baxterQ' z σ (AVec z ρ σ Gt Dt) (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt) i j r
          + ∑ l, ρ l * ∫ t, baxterQ' z σ (AVec z ρ σ Gt Dt) (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt)
                (Ct z ρ σ Gt Dt) i l (t + r)
                * baxterQ z σ (AVec z ρ σ Gt Dt) (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt)
                    (Ct z ρ σ Gt Dt) j l t := by
  intro r hr
  have hrpos : 0 < r := by have := hσ i; have := hσ j; unfold edgeHi at hr; linarith
  rw [mat_exterior_baxter_relation_Dt z hz ρ σ Gt Dt i j r hσ hr]
  have hLHS : 2 * Real.pi * r * matMSAtail K z σ i j r
      = 2 * Real.pi * K i j * Real.exp (z * edgeHi σ i j) * Real.exp (-z * r) := by
    unfold matMSAtail cMSAtail
    rw [if_pos (show sigMix σ i j < r by
          have h := hr; unfold sigMix; unfold edgeHi at h; linarith),
        show -z * (r - sigMix σ i j) = z * edgeHi σ i j + -z * r from by unfold sigMix edgeHi; ring,
        Real.exp_add]
    have hrne : r ≠ 0 := hrpos.ne'
    field_simp
  rw [hLHS]
  have hedge : ∀ l : Fin N, Real.exp (z * edgeHi σ i j) * Real.exp (z * edgeLo σ j l)
      = Real.exp (z * edgeHi σ i l) := by
    intro l; rw [← Real.exp_add]; congr 1; unfold edgeHi edgeLo; ring
  have hsumconv : (∑ l, ρ l * (Real.exp (z * edgeHi σ i l) * Dt i l)
        * qhatMixRuneq z σ (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt)
            (AVec z ρ σ Gt Dt) z j l)
      = Real.exp (z * edgeHi σ i j) * ∑ l, ρ l * (Real.exp (z * edgeLo σ j l) * Dt i l)
          * qhatMixRuneq z σ (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt)
              (AVec z ρ σ Gt Dt) z j l := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [← hedge l]; ring
  -- clear the `/z` in `(♦)` so `linear_combination`'s `ring` needn't cancel `z·z⁻¹`
  have hcside' : z * (Dt i j - ∑ l, ρ l * (Real.exp (z * edgeLo σ j l) * Dt i l)
        * qhatMixRuneq z σ (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt)
            (AVec z ρ σ Gt Dt) z j l)
      = 2 * Real.pi * K i j := by rw [hcside]; field_simp
  rw [hsumconv]
  linear_combination (-(Real.exp (-z * r) * Real.exp (z * edgeHi σ i j))) * hcside'

/-- **`hbax ⟺ (♦)`** — the exterior Baxter Eq (8) closure (`∀ r > edgeHi_ij`) is **exactly** the c-side
Blum–Høye constraint (♦)/(29′).  Forward `c_side_constraint_of_exterior`, reverse `mat_hbax_of_cside` —
the matrix analog of the scalar `FMSA.ExactMSA.GSide.hbax_iff_h29`.  So the c-side OZ primitive `hbax`
consumed by `MixBHRootUneq_of_oz_full` is not a free assumption: it is equivalent to the algebraic root
condition (its full unconditional discharge — that the concrete `baxterQ` really solves OZ — is the
`matExactMSAUnequalDiam_hcore` ring content). -/
theorem mat_hbax_iff_cside {N : ℕ} (z : ℝ) (hz : 0 < z) (ρ σ : Fin N → ℝ)
    (Gt Dt K : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) (hσ : ∀ k, 0 ≤ σ k) :
    (∀ r, edgeHi σ i j < r →
      2 * Real.pi * r * matMSAtail K z σ i j r
        = -baxterQ' z σ (AVec z ρ σ Gt Dt) (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt) i j r
          + ∑ l, ρ l * ∫ t, baxterQ' z σ (AVec z ρ σ Gt Dt) (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt)
                (Ct z ρ σ Gt Dt) i l (t + r)
                * baxterQ z σ (AVec z ρ σ Gt Dt) (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt)
                    (Ct z ρ σ Gt Dt) j l t)
      ↔ Dt i j - ∑ l, ρ l * (Real.exp (z * edgeLo σ j l) * Dt i l)
            * qhatMixRuneq z σ (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt)
                (AVec z ρ σ Gt Dt) z j l
          = 2 * Real.pi * K i j / z :=
  ⟨fun hbax => c_side_constraint_of_exterior z hz ρ σ Gt Dt K i j hσ hbax,
   mat_hbax_of_cside z hz ρ σ Gt Dt K i j hσ⟩

/-! ### MPhase 3 — the g-side matrix Laplace-convolution stack (the CRUX)

The g-side OZ equation (Blum–Høye Eq. 32), Laplace-transformed at `s = z`, folds the species-summed
RDF⋆Baxter convolution `∑_l ρ_l ∫₀^∞ e^{−zr} (∫₀^∞ (r−t) g_il(r−t) Q_lj(t) dt) dr` onto the
transforms `∑_l ρ_l ĝ_il(z)·Q̂_lj(z)`.  The scalar convolution theorem
`FMSA.ExactMSA.GSide.laplace_conv_eq_rdf_mul_qhat_of_integrable` (whose Fubini swap is already
discharged, axiom-clean) is **generic** in the RDF `g` and Baxter factor `Q`, so it lifts **per
species `l`**; the `∑_l ρ_l` contraction the roadmap flagged as the crux is then **just linearity of
the integral** (`Finset.sum_congr`).  The g-side thus reuses the scalar Fubini machinery wholesale.

**Edge structure of the g-side (numerically confirmed).** Both conjuncts of `MSAMixture.MixBHRootUneq`
carry the recentered transform — verified to machine precision (`(29′) 1.7e-16`, `(33′) 3.6e-15`)
against the validated solver `msa_exact_mix.py` (`msaemix_root_recentering_check.py`), whose exact
`_residuals` are `(29′) Σ_l Dt_il·e^{z·edgeLo σ j l}[δ_lj − ρ_l·Q̂_jl] = 2πK_ij/z` and
`(33′) 2π·Σ_l Gt_il·e^{z·edgeLo σ l j}[δ_lj − ρ_l·Q̂_lj] = RHS`.  The two descend from Baxter's Eq (8)
`D(I−PQ̂ᵀ)` and Eq (32) `2πĝ(I−PQ̂)` — hence the **opposite `edgeLo` orientation and transposed `Q̂`
index** (`Q̂_jl` on c-side, `Q̂_lj` on g-side), a distinction invisible at `N=1`.  The `Q̂` is the
full-support `qhatMixRuneq` and the factor may sit on `Q̂` alone or the whole bracket (identical, `=1` at
`l=j`).  (A first analysis wrongly inferred the g-side gets no `Q̂`-recentering; the solver check
refuted it — the recentering is real, and the c/g difference is only in the `edgeLo` index/sign.)
The from-first-principles g-side derivation (via `mat_laplace_conv` + a repo-consistent g-source) is
still open, but the (33′) *form* is now numerically pinned. -/

/-- **MPhase 3 — the matrix Laplace-convolution theorem (the CRUX engine).**  For each species `l` the
scalar `laplace_conv_eq_rdf_mul_qhat_of_integrable` folds the RDF⋆Baxter convolution onto
`ĝ_il(z)·Q̂_lj(z)`; the `∑_l ρ_l` contraction is linearity.  Reuses the scalar Fubini discharge (no new
integration-swap work).  `g_il` = the (abstract) matrix RDF, `Q_lj` = the Baxter factor entry. -/
theorem mat_laplace_conv {N : ℕ} (z : ℝ) (ρ : Fin N → ℝ) (g Q : Fin N → Fin N → ℝ → ℝ) (i j : Fin N)
    (hgsupp : ∀ l u, u < 0 → g i l u = 0)
    (hF1 : ∀ l, Integrable (fun u => Real.exp (-z * u) * (u * g i l u)))
    (hF2 : ∀ l, Integrable (fun t => Real.exp (-z * t) * Q l j t)) :
    ∑ l, ρ l * (∫ r in Set.Ioi (0:ℝ), Real.exp (-z * r)
          * ∫ t in Set.Ioi (0:ℝ), (r - t) * g i l (r - t) * Q l j t)
      = ∑ l, ρ l * (FMSA.ExactMSA.GSide.rdfLaplaceMoment (g i l) z
          * ∫ t in Set.Ioi (0:ℝ), Real.exp (-z * t) * Q l j t) := by
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [FMSA.ExactMSA.GSide.laplace_conv_eq_rdf_mul_qhat_of_integrable (g i l) (Q l j) z
        (hgsupp l) (hF1 l) (hF2 l)]

/-- **MPhase 3/4 — the g-side fold (mixture analog of the scalar `hoz_of_gside`).**  Given the mixture
g-side OZ equation Laplace-transformed at `s = z` (`hgside_mix`, the g-side analog of the c-side `hbax`),
the species-summed RDF⋆Baxter convolution folds via `mat_laplace_conv` onto the transforms, giving the
g-side constraint `2π·∑_l ĝ_il(z)·(δ_lj − ρ_l·Q̂_lj(z)) = source`, where `ĝ_il` / `Q̂_lj` are the matrix
RDF-Laplace moment (`hgmoment`) and Baxter transform (`hQtransform`).  **This discharges the crux** — the
convolution folding + the `∑_l` contraction — exactly as on the c-side.  Matching `source` to
`(A_j + z·qp_ij + z²·Ct_ij/2)/z²·e^{−z·edgeHi_ij}` and identifying `ĝ_il = Gt_il·e^{−z·edgeHi_il}`,
`Q̂_lj = e^{z·edgeLo σ l j}·qhatMixRuneq_lj` (full support) recovers the numerically-confirmed (33′) of
`MSAMixture.MixBHRootUneq` (× `e^{z·edgeHi_ij}`); those identifications are the g-source normalization,
still to be pinned (needs the full-support conv domain `[edgeLo,∞)` in place of the scalar's `Ioi 0`). -/
theorem mat_gside_fold {N : ℕ} (z : ℝ) (ρ : Fin N → ℝ) (g Q : Fin N → Fin N → ℝ → ℝ)
    (ghat Qhat : Fin N → Fin N → ℝ) (i j : Fin N) (source : ℝ)
    (hgsupp : ∀ l u, u < 0 → g i l u = 0)
    (hF1 : ∀ l, Integrable (fun u => Real.exp (-z * u) * (u * g i l u)))
    (hF2 : ∀ l, Integrable (fun t => Real.exp (-z * t) * Q l j t))
    (hgmoment : ∀ l, FMSA.ExactMSA.GSide.rdfLaplaceMoment (g i l) z = ghat i l)
    (hQtransform : ∀ l, (∫ t in Set.Ioi (0:ℝ), Real.exp (-z * t) * Q l j t) = Qhat l j)
    (hgside_mix : 2 * Real.pi * ghat i j
      = source + 2 * Real.pi * ∑ l, ρ l
          * (∫ r in Set.Ioi (0:ℝ), Real.exp (-z * r)
              * ∫ t in Set.Ioi (0:ℝ), (r - t) * g i l (r - t) * Q l j t)) :
    2 * Real.pi * ∑ l, ghat i l * ((if l = j then (1:ℝ) else 0) - ρ l * Qhat l j) = source := by
  rw [mat_laplace_conv z ρ g Q i j hgsupp hF1 hF2,
      Finset.sum_congr rfl (fun l _ => by rw [hgmoment l, hQtransform l])] at hgside_mix
  have hexpand : ∑ l, ghat i l * ((if l = j then (1:ℝ) else 0) - ρ l * Qhat l j)
      = ghat i j - ∑ l, ρ l * (ghat i l * Qhat l j) := by
    rw [Finset.sum_congr rfl (fun l _ => by ring :
          ∀ l ∈ Finset.univ, ghat i l * ((if l = j then (1:ℝ) else 0) - ρ l * Qhat l j)
            = ghat i l * (if l = j then (1:ℝ) else 0) - ρ l * (ghat i l * Qhat l j)),
        Finset.sum_sub_distrib]
    congr 1
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hexpand, mul_sub, hgside_mix]; ring

/-- **MPhase 4 — the g-source bookkeeping: recover (33′) from the fold.**  The g-side fold
`mat_gside_fold` produces `2π·∑_l ĝ_il(z)(δ_lj − ρ_l·Q̂_lj) = source` (here `hgconstraint`, with `source`
in the `×e^{−z·edgeHi_ij}` normalization).  With the physical identifications `ĝ_il = Gt_il·e^{−z·edgeHi_il}`
(`hghat`, the `gam` convention `Gt = ĝ·e^{+z·edgeHi}`) and `Q̂_lj = qhatMixRuneq_lj` (`hQhat`, the
full-support Baxter transform), multiplying by `e^{z·edgeHi_ij}` turns `ĝ_il·e^{z·edgeHi_ij} =
Gt_il·e^{z(edgeHi_ij − edgeHi_il)} = Gt_il·e^{z·edgeLo σ l j}` (the key edge identity), recovering exactly
the **(33′) conjunct of `MSAMixture.MixBHRootUneq`** (numerically confirmed to `3.6e-15`).  This is the
matrix analog of the scalar `h33_of_gside` (it takes the same class of physical hypotheses — moment
identity, transform value, folded OZ relation). -/
theorem gside_33_of_fold {N : ℕ} (z : ℝ) (ρ σ : Fin N → ℝ)
    (Gt Dt : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) (ghat Qhat : Fin N → Fin N → ℝ)
    (hghat : ∀ l, ghat i l = Gt i l * Real.exp (-z * edgeHi σ i l))
    (hQhat : ∀ l, Qhat l j
      = qhatMixRuneq z σ (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt) (AVec z ρ σ Gt Dt) z l j)
    (hgconstraint : 2 * Real.pi * ∑ l, ghat i l * ((if l = j then (1:ℝ) else 0) - ρ l * Qhat l j)
      = (AVec z ρ σ Gt Dt j + z * qpMat z ρ σ Gt Dt i j + z ^ 2 * Ct z ρ σ Gt Dt i j / 2) / z ^ 2
        * Real.exp (-z * edgeHi σ i j)) :
    2 * Real.pi * ∑ l, Gt i l * (Real.exp (z * edgeLo σ l j)
        * ((if l = j then (1:ℝ) else 0)
          - ρ l * qhatMixRuneq z σ (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt)
              (AVec z ρ σ Gt Dt) z l j))
      = (AVec z ρ σ Gt Dt j + z * qpMat z ρ σ Gt Dt i j + z ^ 2 * Ct z ρ σ Gt Dt i j / 2) / z ^ 2 := by
  set R := (AVec z ρ σ Gt Dt j + z * qpMat z ρ σ Gt Dt i j + z ^ 2 * Ct z ρ σ Gt Dt i j / 2) / z ^ 2
    with hR
  have hedge : ∀ l : Fin N, Real.exp (z * edgeHi σ i j) * Real.exp (-z * edgeHi σ i l)
      = Real.exp (z * edgeLo σ l j) := by
    intro l; rw [← Real.exp_add]; congr 1; unfold edgeHi edgeLo; ring
  have keysum : (∑ l, Gt i l * (Real.exp (z * edgeLo σ l j)
        * ((if l = j then (1:ℝ) else 0)
          - ρ l * qhatMixRuneq z σ (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt)
              (AVec z ρ σ Gt Dt) z l j)))
      = Real.exp (z * edgeHi σ i j)
        * ∑ l, ghat i l * ((if l = j then (1:ℝ) else 0) - ρ l * Qhat l j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [hghat l, hQhat l, ← hedge l]; ring
  have hc : Real.exp (z * edgeHi σ i j) * Real.exp (-z * edgeHi σ i j) = 1 := by
    rw [← Real.exp_add, show z * edgeHi σ i j + -z * edgeHi σ i j = 0 from by ring, Real.exp_zero]
  rw [keysum,
      show 2 * Real.pi * (Real.exp (z * edgeHi σ i j)
            * ∑ l, ghat i l * ((if l = j then (1:ℝ) else 0) - ρ l * Qhat l j))
        = Real.exp (z * edgeHi σ i j)
          * (2 * Real.pi * ∑ l, ghat i l * ((if l = j then (1:ℝ) else 0) - ρ l * Qhat l j)) from by ring,
      hgconstraint]
  linear_combination R * hc

/-- ⭐ **MPhase 3/4 — the g-side (33′), derived from the g-side OZ primitive.**  Chains `mat_gside_fold`
(the convolution folding) into `gside_33_of_fold` (the g-source bookkeeping): given the mixture g-side
OZ equation Laplace-transformed at `s = z` (`hgside_mix`) — with its g-source in the `×e^{−z·edgeHi_ij}`
normalization — plus the physical identifications `ĝ_il = Gt_il·e^{−z·edgeHi_il}` (`hghat`) and
`Q̂_lj = qhatMixRuneq_lj` (`hQhat`), the **c… (33′) conjunct of `MSAMixture.MixBHRootUneq`** follows.  The
full matrix analog of the scalar `FMSA.ExactMSA.GSide.h33_of_gside`: the whole g-side leg now stands on
the recognised physical inputs (RDF support/integrability, the RDF-moment and Baxter-transform
identities, and the folded g-side OZ relation), with the convolution-folding crux discharged
axiom-clean.  ⚠ **Range of validity.** `hQtransform` (`∫_{Ioi 0} e^{−zt}Q_lj = qhatMixRuneq_lj`) holds for
the physical `Q_lj = baxterQ_lj` **only when `edgeLo_lj ≥ 0`** (ordered pairs `σ_j ≥ σ_l`): then
`baxterQ_lj = 0` on `(−∞,0)` so `∫_{Ioi 0} = ∫_ℝ = qhatMixRuneq_lj` (MPhase 1).  For `edgeLo_lj < 0`
`baxterQ_lj ≠ 0` on `[edgeLo_lj,0)`, so `∫_{Ioi 0} ≠ qhatMixRuneq_lj` and this hypothesis is
**unsatisfiable**.  ✅ **Superseded by `gside_33_of_hgside_full`** (MPhase 6): running the inner integral
over all of `ℝ` makes `hQtransform` the *unconditional* full-line transform (`baxterQ_fullline_transform`),
and the RDF hard core kills the `t<0` correction — with the overlap `-edgeHi_il < edgeLo_lj` automatic for
positive diameters (`neg_edgeHi_lt_edgeLo`), so the g-side is closed for **every** unequal-σ combination.
(The c-side (♦) has no such limitation — `mat_exterior_baxter_relation` integrates over the full line.) -/
theorem gside_33_of_hgside {N : ℕ} (z : ℝ) (ρ σ : Fin N → ℝ)
    (Gt Dt : Matrix (Fin N) (Fin N) ℝ) (g Q : Fin N → Fin N → ℝ → ℝ)
    (ghat Qhat : Fin N → Fin N → ℝ) (i j : Fin N)
    (hgsupp : ∀ l u, u < 0 → g i l u = 0)
    (hF1 : ∀ l, Integrable (fun u => Real.exp (-z * u) * (u * g i l u)))
    (hF2 : ∀ l, Integrable (fun t => Real.exp (-z * t) * Q l j t))
    (hgmoment : ∀ l, FMSA.ExactMSA.GSide.rdfLaplaceMoment (g i l) z = ghat i l)
    (hQtransform : ∀ l, (∫ t in Set.Ioi (0:ℝ), Real.exp (-z * t) * Q l j t) = Qhat l j)
    (hghat : ∀ l, ghat i l = Gt i l * Real.exp (-z * edgeHi σ i l))
    (hQhat : ∀ l, Qhat l j
      = qhatMixRuneq z σ (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt) (AVec z ρ σ Gt Dt) z l j)
    (hgside_mix : 2 * Real.pi * ghat i j
      = (AVec z ρ σ Gt Dt j + z * qpMat z ρ σ Gt Dt i j + z ^ 2 * Ct z ρ σ Gt Dt i j / 2) / z ^ 2
          * Real.exp (-z * edgeHi σ i j)
        + 2 * Real.pi * ∑ l, ρ l
            * (∫ r in Set.Ioi (0:ℝ), Real.exp (-z * r)
                * ∫ t in Set.Ioi (0:ℝ), (r - t) * g i l (r - t) * Q l j t)) :
    2 * Real.pi * ∑ l, Gt i l * (Real.exp (z * edgeLo σ l j)
        * ((if l = j then (1:ℝ) else 0)
          - ρ l * qhatMixRuneq z σ (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt)
              (AVec z ρ σ Gt Dt) z l j))
      = (AVec z ρ σ Gt Dt j + z * qpMat z ρ σ Gt Dt i j + z ^ 2 * Ct z ρ σ Gt Dt i j / 2) / z ^ 2 :=
  gside_33_of_fold z ρ σ Gt Dt i j ghat Qhat hghat hQhat
    (mat_gside_fold z ρ g Q ghat Qhat i j
      ((AVec z ρ σ Gt Dt j + z * qpMat z ρ σ Gt Dt i j + z ^ 2 * Ct z ρ σ Gt Dt i j / 2) / z ^ 2
        * Real.exp (-z * edgeHi σ i j))
      hgsupp hF1 hF2 hgmoment hQtransform hgside_mix)

/-! ### MPhase 6 — the full-support convolution: close the g-side beyond ordered pairs

The `mat_gside_fold`/`gside_33_of_hgside` stack above folds the RDF⋆Baxter convolution with the inner
`t`-integral over `Ioi 0` and the Baxter transform `∫_{Ioi 0} e^{−zt}Q_lj`, which equals the
full-support `qhatMixRuneq_lj` **only for ordered pairs** `σ_j ≥ σ_l` (`edgeLo_lj ≥ 0`).  The fix here
runs the inner `t`-integral over **all of `ℝ`** — so its transform is the *unconditional* MPhase-1
`baxterQ_transform` (`∫_ℝ e^{−zt}Q_lj = qhatMixRuneq_lj` for every diameter pair) — and rescues the
per-`t` collapse using the **RDF hard core** `g_il(u) = 0` for `u < σ_il = edgeHi_il`.  The naive
`t<0` correction `e^{−zt}∫_{u>−t}e^{−zu}u g(u) du` differs from the clean `e^{−zt}ĝ(z)` only by
`∫_{(0,−t]}e^{−zu}u g(u) du`, which **vanishes** when `−t < σ_il` — i.e. when `Q`'s support floor
`edgeLo_lj > −edgeHi_il`.  For the physical diameters this overlap is **automatic**: `edgeLo_lj + edgeHi_il
= (σ_j−σ_l)/2 + (σ_i+σ_l)/2 = (σ_i+σ_j)/2 > 0` (the `σ_l` cancels; `neg_edgeHi_lt_edgeLo`), so the fold
factors for **every** diameter triple — no ordered-pairs and no size-disparity restriction. -/

/-- **The hard-core shift step** — the full-support generalisation of the scalar
`FMSA.ExactMSA.GSide.rdfLaplaceMoment_shift_from_zero` to `t < 0`.  For an RDF `g` supported on
`[σg, ∞)` (`g u = 0` for `u < σg`, the hard core) and any `t > -σg`,
`∫_{r>0} e^{−zr}·(r−t)·g(r−t) dr = e^{−zt}·ĝ(z)`.  The integrand vanishes on the symmetric difference
between `Ioi 0` and `Ioi t`: for `t ≥ 0` on `(0,t]` (there `r−t ≤ 0 ≤ σg` gives `g(r−t)=0`, or the
`(r−t)` factor vanishes at `r=t`), and for `-σg < t < 0` on `(t,0]` (there `r−t ≤ -t < σg` by the
*strict* bound `-σg < t`).  Hence `∫_{Ioi 0} = ∫_{Ioi t} = e^{−zt}·ĝ(z)`
(`FMSA.ExactMSA.GSide.rdfLaplaceMoment_shift`, itself unconditional). -/
theorem rdfLaplaceMoment_shift_hardcore (g : ℝ → ℝ) (z t σg : ℝ) (hσg : 0 ≤ σg)
    (ht : -σg < t) (hgsupp : ∀ u, u < σg → g u = 0) :
    ∫ r in Set.Ioi (0:ℝ), Real.exp (-z * r) * ((r - t) * g (r - t))
      = Real.exp (-z * t) * FMSA.ExactMSA.GSide.rdfLaplaceMoment g z := by
  rw [← FMSA.ExactMSA.GSide.rdfLaplaceMoment_shift g z t]
  by_cases ht0 : 0 ≤ t
  · apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (Set.Ioi_subset_Ioi ht0)
    intro r hr
    simp only [Set.mem_diff, Set.mem_Ioi, not_lt] at hr
    have hz : (r - t) * g (r - t) = 0 := by
      rcases lt_or_eq_of_le hr.2 with h | h
      · rw [hgsupp (r - t) (by linarith)]; ring
      · rw [h]; ring
    show Real.exp (-z * r) * ((r - t) * g (r - t)) = 0
    rw [hz]; ring
  · push_neg at ht0
    symm
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (Set.Ioi_subset_Ioi (le_of_lt ht0))
    intro r hr
    simp only [Set.mem_diff, Set.mem_Ioi, not_lt] at hr
    have hz : g (r - t) = 0 := hgsupp (r - t) (by linarith)
    show Real.exp (-z * r) * ((r - t) * g (r - t)) = 0
    rw [hz]; ring

/-- **The Fubini swap of the full-support OZ-convolution integrand** — the `Ioi 0 ×ˢ ℝ` analog of the
scalar `FMSA.ExactMSA.GSide.laplace_conv_fubini_swap`.  The 2D integrand factors as the convolution
kernel `e^{−zr}·(r−t)·g(r−t)·Q(t) = F₁(r−t)·F₂(t)` with `F₁(u) = e^{−zu}·u·g(u)`, `F₂(t) = e^{−zt}·Q(t)`,
so `Integrable.convolution_integrand` gives full-plane integrability; restricting **only the `r`
factor** to `Ioi 0` (the physical outer domain) via `Measure.prod_restrict` (with
`Measure.restrict_univ` on the untouched `t` factor) yields the hypothesis `integral_integral_swap`
needs. -/
theorem laplace_conv_full_fubini_swap (g Q : ℝ → ℝ) (z : ℝ)
    (hF1 : Integrable (fun u => Real.exp (-z * u) * (u * g u)))
    (hF2 : Integrable (fun t => Real.exp (-z * t) * Q t)) :
    (∫ r in Set.Ioi (0:ℝ), ∫ t, Real.exp (-z * r) * ((r - t) * g (r - t) * Q t))
      = ∫ t, ∫ r in Set.Ioi (0:ℝ), Real.exp (-z * r) * ((r - t) * g (r - t) * Q t) := by
  have hconv : Integrable
      (fun p : ℝ × ℝ => Real.exp (-z * p.1) * ((p.1 - p.2) * g (p.1 - p.2) * Q p.2))
      (volume.prod volume) := by
    refine (hF2.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hF1).congr
      (Filter.Eventually.of_forall (fun p => ?_))
    simp only [ContinuousLinearMap.mul_apply']
    have hac : Real.exp (-z * p.2) * Real.exp (-z * (p.1 - p.2)) = Real.exp (-z * p.1) := by
      rw [← Real.exp_add]; congr 1; ring
    linear_combination (Q p.2 * ((p.1 - p.2) * g (p.1 - p.2))) * hac
  have hrestr : Integrable
      (fun p : ℝ × ℝ => Real.exp (-z * p.1) * ((p.1 - p.2) * g (p.1 - p.2) * Q p.2))
      ((volume.restrict (Set.Ioi (0:ℝ))).prod volume) := by
    have h1 : (volume.restrict (Set.Ioi (0:ℝ))).prod (volume : Measure ℝ)
        = (volume.restrict (Set.Ioi (0:ℝ))).prod (volume.restrict Set.univ) := by
      rw [Measure.restrict_univ]
    rw [h1, Measure.prod_restrict]
    exact hconv.integrableOn
  exact integral_integral_swap
    (f := fun r t => Real.exp (-z * r) * ((r - t) * g (r - t) * Q t)) hrestr

/-- **The full-support Laplace convolution theorem** — the `[σg,∞)`-`Q`-support analog of the scalar
`FMSA.ExactMSA.GSide.laplace_conv_eq_rdf_mul_qhat`, with the inner `t`-integral over **all of `ℝ`**.
For an RDF `g` supported on `[σg,∞)` (hard core) and a Baxter factor `Q` supported on `[λ,∞)` with the
**overlap condition `-σg < λ`**,
`∫_{r>0} e^{−zr}·(∫_ℝ (r−t)·g(r−t)·Q(t) dt) dr = ĝ(z)·(∫_ℝ e^{−zt}·Q(t) dt)`.  The full-line inner
integral makes the Baxter transform the *unconditional* `qhatMixRuneq` (MPhase 1), while the per-`t`
collapse `Q(t)·∫_{r>0} e^{−zr}(r−t)g(r−t) dr = ĝ·e^{−zt}Q(t)` holds for every `t` — trivially where
`Q(t)=0` (`t<λ`), and via `rdfLaplaceMoment_shift_hardcore` where `t ≥ λ > -σg` (the hard core kills
the `t<0` partial-moment correction). -/
theorem laplace_conv_full (g Q : ℝ → ℝ) (z σg lam : ℝ) (hσg : 0 ≤ σg)
    (hgsupp : ∀ u, u < σg → g u = 0) (hQsupp : ∀ t, t < lam → Q t = 0) (hcond : -σg < lam)
    (hfub : (∫ r in Set.Ioi (0:ℝ), ∫ t, Real.exp (-z * r) * ((r - t) * g (r - t) * Q t))
          = ∫ t, ∫ r in Set.Ioi (0:ℝ), Real.exp (-z * r) * ((r - t) * g (r - t) * Q t)) :
    (∫ r in Set.Ioi (0:ℝ), Real.exp (-z * r) * ∫ t, (r - t) * g (r - t) * Q t)
      = FMSA.ExactMSA.GSide.rdfLaplaceMoment g z * ∫ t, Real.exp (-z * t) * Q t := by
  calc (∫ r in Set.Ioi (0:ℝ), Real.exp (-z * r) * ∫ t, (r - t) * g (r - t) * Q t)
      = ∫ r in Set.Ioi (0:ℝ), ∫ t, Real.exp (-z * r) * ((r - t) * g (r - t) * Q t) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r _
        show Real.exp (-z * r) * (∫ t, (r - t) * g (r - t) * Q t)
            = ∫ t, Real.exp (-z * r) * ((r - t) * g (r - t) * Q t)
        rw [MeasureTheory.integral_const_mul]
    _ = ∫ t, ∫ r in Set.Ioi (0:ℝ), Real.exp (-z * r) * ((r - t) * g (r - t) * Q t) := hfub
    _ = ∫ t, FMSA.ExactMSA.GSide.rdfLaplaceMoment g z * (Real.exp (-z * t) * Q t) := by
        apply MeasureTheory.integral_congr_ae
        refine Filter.Eventually.of_forall (fun t => ?_)
        have hpull : (∫ r in Set.Ioi (0:ℝ), Real.exp (-z * r) * ((r - t) * g (r - t) * Q t))
            = Q t * ∫ r in Set.Ioi (0:ℝ), Real.exp (-z * r) * ((r - t) * g (r - t)) := by
          rw [← MeasureTheory.integral_const_mul]
          apply setIntegral_congr_fun measurableSet_Ioi
          intro r _
          show Real.exp (-z * r) * ((r - t) * g (r - t) * Q t)
              = Q t * (Real.exp (-z * r) * ((r - t) * g (r - t)))
          ring
        show (∫ r in Set.Ioi (0:ℝ), Real.exp (-z * r) * ((r - t) * g (r - t) * Q t))
            = FMSA.ExactMSA.GSide.rdfLaplaceMoment g z * (Real.exp (-z * t) * Q t)
        rw [hpull]
        by_cases htl : t < lam
        · rw [hQsupp t htl]; ring
        · push_neg at htl
          rw [rdfLaplaceMoment_shift_hardcore g z t σg hσg (by linarith) hgsupp]; ring
    _ = FMSA.ExactMSA.GSide.rdfLaplaceMoment g z * ∫ t, Real.exp (-z * t) * Q t := by
        rw [MeasureTheory.integral_const_mul]

/-- **The full-support Laplace convolution theorem, fully discharged** (no Fubini hypothesis) — combines
`laplace_conv_full` with `laplace_conv_full_fubini_swap`.  Only the physical integrability of the RDF
moment `r·g(r)` and Baxter moment `Q(t)` (Laplace-weighted) is assumed. -/
theorem laplace_conv_full_of_integrable (g Q : ℝ → ℝ) (z σg lam : ℝ) (hσg : 0 ≤ σg)
    (hgsupp : ∀ u, u < σg → g u = 0) (hQsupp : ∀ t, t < lam → Q t = 0) (hcond : -σg < lam)
    (hF1 : Integrable (fun u => Real.exp (-z * u) * (u * g u)))
    (hF2 : Integrable (fun t => Real.exp (-z * t) * Q t)) :
    (∫ r in Set.Ioi (0:ℝ), Real.exp (-z * r) * ∫ t, (r - t) * g (r - t) * Q t)
      = FMSA.ExactMSA.GSide.rdfLaplaceMoment g z * ∫ t, Real.exp (-z * t) * Q t :=
  laplace_conv_full g Q z σg lam hσg hgsupp hQsupp hcond
    (laplace_conv_full_fubini_swap g Q z hF1 hF2)

/-- **MPhase 6 — the matrix full-support convolution.**  Per species `l`, `laplace_conv_full_of_integrable`
folds `∫_{r>0}e^{−zr}∫_ℝ(r−t)g_il(r−t)Q_lj(t)dt` onto `ĝ_il(z)·(∫_ℝ e^{−zt}Q_lj(t)dt)`, using the RDF
hard core (`hgsupp`, support `[edgeHi_il,∞)`), the Baxter support (`hQsupp`, `[edgeLo_lj,∞)`) and the
overlap condition `hcond` (`-edgeHi_il < edgeLo_lj`, which is automatic for positive diameters —
`= σ_i+σ_j>0`, `neg_edgeHi_lt_edgeLo`); the `∑_l ρ_l` is linearity.  Unlike `mat_laplace_conv` the inner
integral is over **all of `ℝ`**, so the resulting transform `∫_ℝ e^{−zt}Q_lj` is the unconditional
`qhatMixRuneq_lj`. -/
theorem mat_laplace_conv_full {N : ℕ} (z : ℝ) (ρ σ : Fin N → ℝ) (g Q : Fin N → Fin N → ℝ → ℝ)
    (i j : Fin N) (hσ : ∀ k, 0 ≤ σ k)
    (hgsupp : ∀ l u, u < edgeHi σ i l → g i l u = 0)
    (hQsupp : ∀ l t, t < edgeLo σ l j → Q l j t = 0)
    (hcond : ∀ l, -edgeHi σ i l < edgeLo σ l j)
    (hF1 : ∀ l, Integrable (fun u => Real.exp (-z * u) * (u * g i l u)))
    (hF2 : ∀ l, Integrable (fun t => Real.exp (-z * t) * Q l j t)) :
    ∑ l, ρ l * (∫ r in Set.Ioi (0:ℝ), Real.exp (-z * r)
          * ∫ t, (r - t) * g i l (r - t) * Q l j t)
      = ∑ l, ρ l * (FMSA.ExactMSA.GSide.rdfLaplaceMoment (g i l) z
          * ∫ t, Real.exp (-z * t) * Q l j t) := by
  refine Finset.sum_congr rfl (fun l _ => ?_)
  have hσil : (0:ℝ) ≤ edgeHi σ i l := by unfold edgeHi; have := hσ i; have := hσ l; linarith
  rw [laplace_conv_full_of_integrable (g i l) (Q l j) z (edgeHi σ i l) (edgeLo σ l j)
        hσil (hgsupp l) (hQsupp l) (hcond l) (hF1 l) (hF2 l)]

/-- **MPhase 6 — the full-support g-side fold.**  The full-support analog of `mat_gside_fold`: the
species-summed RDF⋆Baxter convolution (inner `t` over **`ℝ`**) folds via `mat_laplace_conv_full` onto
the transforms, giving `2π·∑_l ĝ_il(z)(δ_lj − ρ_l·Q̂_lj) = source`.  The key upgrade is `hQtransform`,
`∫_ℝ e^{−zt}Q_lj = Q̂_lj` — the **full-line** Baxter transform, discharged unconditionally from MPhase 1
(`baxterQ_transform_eq_qhatMixRuneq`) for every diameter pair, in place of the `Ioi 0` transform of
`mat_gside_fold` (satisfiable only for ordered pairs). -/
theorem mat_gside_fold_full {N : ℕ} (z : ℝ) (ρ σ : Fin N → ℝ) (g Q : Fin N → Fin N → ℝ → ℝ)
    (ghat Qhat : Fin N → Fin N → ℝ) (i j : Fin N) (source : ℝ) (hσ : ∀ k, 0 ≤ σ k)
    (hgsupp : ∀ l u, u < edgeHi σ i l → g i l u = 0)
    (hQsupp : ∀ l t, t < edgeLo σ l j → Q l j t = 0)
    (hcond : ∀ l, -edgeHi σ i l < edgeLo σ l j)
    (hF1 : ∀ l, Integrable (fun u => Real.exp (-z * u) * (u * g i l u)))
    (hF2 : ∀ l, Integrable (fun t => Real.exp (-z * t) * Q l j t))
    (hgmoment : ∀ l, FMSA.ExactMSA.GSide.rdfLaplaceMoment (g i l) z = ghat i l)
    (hQtransform : ∀ l, (∫ t, Real.exp (-z * t) * Q l j t) = Qhat l j)
    (hgside_mix : 2 * Real.pi * ghat i j
      = source + 2 * Real.pi * ∑ l, ρ l
          * (∫ r in Set.Ioi (0:ℝ), Real.exp (-z * r)
              * ∫ t, (r - t) * g i l (r - t) * Q l j t)) :
    2 * Real.pi * ∑ l, ghat i l * ((if l = j then (1:ℝ) else 0) - ρ l * Qhat l j) = source := by
  rw [mat_laplace_conv_full z ρ σ g Q i j hσ hgsupp hQsupp hcond hF1 hF2,
      Finset.sum_congr rfl (fun l _ => by rw [hgmoment l, hQtransform l])] at hgside_mix
  have hexpand : ∑ l, ghat i l * ((if l = j then (1:ℝ) else 0) - ρ l * Qhat l j)
      = ghat i j - ∑ l, ρ l * (ghat i l * Qhat l j) := by
    rw [Finset.sum_congr rfl (fun l _ => by ring :
          ∀ l ∈ Finset.univ, ghat i l * ((if l = j then (1:ℝ) else 0) - ρ l * Qhat l j)
            = ghat i l * (if l = j then (1:ℝ) else 0) - ρ l * (ghat i l * Qhat l j)),
        Finset.sum_sub_distrib]
    congr 1
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hexpand, mul_sub, hgside_mix]; ring

/-- ⭐ **MPhase 6 — the g-side (33′), full-support.**  Chains the full-support fold `mat_gside_fold_full`
into the (unchanged) g-source bookkeeping `gside_33_of_fold`.  Compared to `gside_33_of_hgside` the
`Ioi 0` inner integral is replaced by `∫_ℝ`, so `hQtransform` is the full-line Baxter transform
(`∫_ℝ e^{−zt}Q_lj = qhatMixRuneq_lj`), **unconditionally dischargeable from MPhase 1**.  The only side
condition `hcond : -edgeHi_il < edgeLo_lj` is **automatic** for positive diameters (`= σ_i+σ_j>0`,
`neg_edgeHi_lt_edgeLo`), so — at the mixture wire-in — the g-side (33′) conjunct of
`MSAMixture.MixBHRootUneq` stands on OZ primitives for **every** unequal-σ combination. -/
theorem gside_33_of_hgside_full {N : ℕ} (z : ℝ) (ρ σ : Fin N → ℝ)
    (Gt Dt : Matrix (Fin N) (Fin N) ℝ) (g Q : Fin N → Fin N → ℝ → ℝ)
    (ghat Qhat : Fin N → Fin N → ℝ) (i j : Fin N) (hσ : ∀ k, 0 ≤ σ k)
    (hgsupp : ∀ l u, u < edgeHi σ i l → g i l u = 0)
    (hQsupp : ∀ l t, t < edgeLo σ l j → Q l j t = 0)
    (hcond : ∀ l, -edgeHi σ i l < edgeLo σ l j)
    (hF1 : ∀ l, Integrable (fun u => Real.exp (-z * u) * (u * g i l u)))
    (hF2 : ∀ l, Integrable (fun t => Real.exp (-z * t) * Q l j t))
    (hgmoment : ∀ l, FMSA.ExactMSA.GSide.rdfLaplaceMoment (g i l) z = ghat i l)
    (hQtransform : ∀ l, (∫ t, Real.exp (-z * t) * Q l j t) = Qhat l j)
    (hghat : ∀ l, ghat i l = Gt i l * Real.exp (-z * edgeHi σ i l))
    (hQhat : ∀ l, Qhat l j
      = qhatMixRuneq z σ (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt) (AVec z ρ σ Gt Dt) z l j)
    (hgside_mix : 2 * Real.pi * ghat i j
      = (AVec z ρ σ Gt Dt j + z * qpMat z ρ σ Gt Dt i j + z ^ 2 * Ct z ρ σ Gt Dt i j / 2) / z ^ 2
          * Real.exp (-z * edgeHi σ i j)
        + 2 * Real.pi * ∑ l, ρ l
            * (∫ r in Set.Ioi (0:ℝ), Real.exp (-z * r)
                * ∫ t, (r - t) * g i l (r - t) * Q l j t)) :
    2 * Real.pi * ∑ l, Gt i l * (Real.exp (z * edgeLo σ l j)
        * ((if l = j then (1:ℝ) else 0)
          - ρ l * qhatMixRuneq z σ (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt)
              (AVec z ρ σ Gt Dt) z l j))
      = (AVec z ρ σ Gt Dt j + z * qpMat z ρ σ Gt Dt i j + z ^ 2 * Ct z ρ σ Gt Dt i j / 2) / z ^ 2 :=
  gside_33_of_fold z ρ σ Gt Dt i j ghat Qhat hghat hQhat
    (mat_gside_fold_full z ρ σ g Q ghat Qhat i j
      ((AVec z ρ σ Gt Dt j + z * qpMat z ρ σ Gt Dt i j + z ^ 2 * Ct z ρ σ Gt Dt i j / 2) / z ^ 2
        * Real.exp (-z * edgeHi σ i j))
      hσ hgsupp hQsupp hcond hF1 hF2 hgmoment hQtransform hgside_mix)

/-- **`(33′) ⟹ hgside_mix`** — the reverse of `gside_33_of_hgside_full`, completing the g-side
equivalence.  Given the (33′) conjunct and the RDF-side data, the g-side OZ equation Laplace-transformed
at `s = z` (`hgside_mix`) holds: fold the conv onto the transforms (`mat_laplace_conv_full` +
`hgmoment`/`hQtransform`), then run `gside_33_of_fold`'s `keysum` + `mat_gside_fold_full`'s `hexpand`
**backward** — from `2π·∑_l Gt_il e^{z·edgeLo_lj}(δ_lj − ρ_l Q̂_lj) = R` peel the `e^{z·edgeHi_ij}` (via
`E·E⁻¹ = 1`) to recover `2π·ĝ_ij = R·e^{−z·edgeHi_ij} + 2π·∑_l ρ_l·conv_il`. -/
theorem mat_hgside_of_gside {N : ℕ} (z : ℝ) (ρ σ : Fin N → ℝ)
    (Gt Dt : Matrix (Fin N) (Fin N) ℝ) (g Q : Fin N → Fin N → ℝ → ℝ)
    (ghat Qhat : Fin N → Fin N → ℝ) (i j : Fin N) (hσ : ∀ k, 0 ≤ σ k)
    (hgsupp : ∀ l u, u < edgeHi σ i l → g i l u = 0)
    (hQsupp : ∀ l t, t < edgeLo σ l j → Q l j t = 0)
    (hcond : ∀ l, -edgeHi σ i l < edgeLo σ l j)
    (hF1 : ∀ l, Integrable (fun u => Real.exp (-z * u) * (u * g i l u)))
    (hF2 : ∀ l, Integrable (fun t => Real.exp (-z * t) * Q l j t))
    (hgmoment : ∀ l, FMSA.ExactMSA.GSide.rdfLaplaceMoment (g i l) z = ghat i l)
    (hQtransform : ∀ l, (∫ t, Real.exp (-z * t) * Q l j t) = Qhat l j)
    (hghat : ∀ l, ghat i l = Gt i l * Real.exp (-z * edgeHi σ i l))
    (hQhat : ∀ l, Qhat l j
      = qhatMixRuneq z σ (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt) (AVec z ρ σ Gt Dt) z l j)
    (h33 : 2 * Real.pi * ∑ l, Gt i l * (Real.exp (z * edgeLo σ l j)
        * ((if l = j then (1:ℝ) else 0)
          - ρ l * qhatMixRuneq z σ (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt)
              (AVec z ρ σ Gt Dt) z l j))
      = (AVec z ρ σ Gt Dt j + z * qpMat z ρ σ Gt Dt i j + z ^ 2 * Ct z ρ σ Gt Dt i j / 2) / z ^ 2) :
    2 * Real.pi * ghat i j
      = (AVec z ρ σ Gt Dt j + z * qpMat z ρ σ Gt Dt i j + z ^ 2 * Ct z ρ σ Gt Dt i j / 2) / z ^ 2
          * Real.exp (-z * edgeHi σ i j)
        + 2 * Real.pi * ∑ l, ρ l
            * (∫ r in Set.Ioi (0:ℝ), Real.exp (-z * r)
                * ∫ t, (r - t) * g i l (r - t) * Q l j t) := by
  have hconv : (∑ l, ρ l * (∫ r in Set.Ioi (0:ℝ), Real.exp (-z * r)
        * ∫ t, (r - t) * g i l (r - t) * Q l j t))
      = ∑ l, ρ l * (ghat i l * Qhat l j) := by
    rw [mat_laplace_conv_full z ρ σ g Q i j hσ hgsupp hQsupp hcond hF1 hF2]
    exact Finset.sum_congr rfl (fun l _ => by rw [hgmoment l, hQtransform l])
  rw [hconv]
  have hedge : ∀ l : Fin N, Real.exp (z * edgeHi σ i j) * Real.exp (-z * edgeHi σ i l)
      = Real.exp (z * edgeLo σ l j) := by
    intro l; rw [← Real.exp_add]; congr 1; unfold edgeHi edgeLo; ring
  have keysum : (∑ l, Gt i l * (Real.exp (z * edgeLo σ l j)
        * ((if l = j then (1:ℝ) else 0)
          - ρ l * qhatMixRuneq z σ (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt)
              (AVec z ρ σ Gt Dt) z l j)))
      = Real.exp (z * edgeHi σ i j)
        * ∑ l, ghat i l * ((if l = j then (1:ℝ) else 0) - ρ l * Qhat l j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [hghat l, hQhat l, ← hedge l]; ring
  have hexpand : (∑ l, ghat i l * ((if l = j then (1:ℝ) else 0) - ρ l * Qhat l j))
      = ghat i j - ∑ l, ρ l * (ghat i l * Qhat l j) := by
    rw [Finset.sum_congr rfl (fun l _ => by ring :
          ∀ l ∈ Finset.univ, ghat i l * ((if l = j then (1:ℝ) else 0) - ρ l * Qhat l j)
            = ghat i l * (if l = j then (1:ℝ) else 0) - ρ l * (ghat i l * Qhat l j)),
        Finset.sum_sub_distrib]
    congr 1
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [keysum, hexpand] at h33
  have hc : Real.exp (z * edgeHi σ i j) * Real.exp (-z * edgeHi σ i j) = 1 := by
    rw [← Real.exp_add, show z * edgeHi σ i j + -z * edgeHi σ i j = 0 from by ring, Real.exp_zero]
  linear_combination Real.exp (-z * edgeHi σ i j) * h33
    + (-(2 * Real.pi * (ghat i j - ∑ l, ρ l * (ghat i l * Qhat l j)))) * hc

/-- **`hgside_mix ⟺ (33′)`** (under the RDF-side data) — the g-side OZ Eq (32) Laplace-transformed is
**exactly** the (33′) conjunct of `MSAMixture.MixBHRootUneq`.  Forward `gside_33_of_hgside_full`, reverse
`mat_hgside_of_gside` — the matrix analog of the scalar `FMSA.ExactMSA.GSide.hgside_iff_h33`.  Together
with `mat_hbax_iff_cside`, both OZ primitives consumed by `MixBHRootUneq_of_oz_full` are equivalent to the
algebraic root conditions; their full unconditional discharge is the `matExactMSAUnequalDiam_hcore` ring. -/
theorem mat_hgside_iff_gside {N : ℕ} (z : ℝ) (ρ σ : Fin N → ℝ)
    (Gt Dt : Matrix (Fin N) (Fin N) ℝ) (g Q : Fin N → Fin N → ℝ → ℝ)
    (ghat Qhat : Fin N → Fin N → ℝ) (i j : Fin N) (hσ : ∀ k, 0 ≤ σ k)
    (hgsupp : ∀ l u, u < edgeHi σ i l → g i l u = 0)
    (hQsupp : ∀ l t, t < edgeLo σ l j → Q l j t = 0)
    (hcond : ∀ l, -edgeHi σ i l < edgeLo σ l j)
    (hF1 : ∀ l, Integrable (fun u => Real.exp (-z * u) * (u * g i l u)))
    (hF2 : ∀ l, Integrable (fun t => Real.exp (-z * t) * Q l j t))
    (hgmoment : ∀ l, FMSA.ExactMSA.GSide.rdfLaplaceMoment (g i l) z = ghat i l)
    (hQtransform : ∀ l, (∫ t, Real.exp (-z * t) * Q l j t) = Qhat l j)
    (hghat : ∀ l, ghat i l = Gt i l * Real.exp (-z * edgeHi σ i l))
    (hQhat : ∀ l, Qhat l j
      = qhatMixRuneq z σ (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt) (AVec z ρ σ Gt Dt) z l j) :
    (2 * Real.pi * ghat i j
      = (AVec z ρ σ Gt Dt j + z * qpMat z ρ σ Gt Dt i j + z ^ 2 * Ct z ρ σ Gt Dt i j / 2) / z ^ 2
          * Real.exp (-z * edgeHi σ i j)
        + 2 * Real.pi * ∑ l, ρ l
            * (∫ r in Set.Ioi (0:ℝ), Real.exp (-z * r)
                * ∫ t, (r - t) * g i l (r - t) * Q l j t))
      ↔ 2 * Real.pi * ∑ l, Gt i l * (Real.exp (z * edgeLo σ l j)
            * ((if l = j then (1:ℝ) else 0)
              - ρ l * qhatMixRuneq z σ (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt)
                  (AVec z ρ σ Gt Dt) z l j))
          = (AVec z ρ σ Gt Dt j + z * qpMat z ρ σ Gt Dt i j + z ^ 2 * Ct z ρ σ Gt Dt i j / 2) / z ^ 2 :=
  ⟨fun hgside_mix => gside_33_of_hgside_full z ρ σ Gt Dt g Q ghat Qhat i j hσ hgsupp hQsupp hcond
      hF1 hF2 hgmoment hQtransform hghat hQhat hgside_mix,
   fun h33 => mat_hgside_of_gside z ρ σ Gt Dt g Q ghat Qhat i j hσ hgsupp hQsupp hcond
      hF1 hF2 hgmoment hQtransform hghat hQhat h33⟩

/-! ### MPhase 5 — wire the derived (29′)/(33′) into `MixBHRootUneq` (retire the posited root) -/

/-- The two `∑_l` forms of the g-side (33′) coincide: the recentering factor `e^{z·edgeLo σ l j}` may
sit on the whole bracket `(δ_lj − ρ_l·Q_lj)` (as `gside_33_of_hgside` produces it) or on `Q_lj` alone
(as `MixBHRootUneq` states it) — both equal `Gt_ij − ∑_l ρ_l·Gt_il·e^{z·edgeLo σ l j}·Q_lj`, because the
factor is `1` at `l = j` (`edgeLo σ j j = 0`). -/
theorem gside_bracket_sum_eq {N : ℕ} (z : ℝ) (σ ρ : Fin N → ℝ)
    (Gt : Matrix (Fin N) (Fin N) ℝ) (Q : Fin N → Fin N → ℝ) (i j : Fin N) :
    (∑ l, Gt i l * ((if l = j then (1:ℝ) else 0)
        - ρ l * (Real.exp (z * edgeLo σ l j) * Q l j)))
      = ∑ l, Gt i l * (Real.exp (z * edgeLo σ l j)
          * ((if l = j then (1:ℝ) else 0) - ρ l * Q l j)) := by
  have hjj : Real.exp (z * edgeLo σ j j) = 1 := by
    rw [show edgeLo σ j j = 0 from by unfold edgeLo; ring, mul_zero, Real.exp_zero]
  have h1 : (∑ l, Gt i l * ((if l = j then (1:ℝ) else 0)
        - ρ l * (Real.exp (z * edgeLo σ l j) * Q l j)))
      = Gt i j - ∑ l, ρ l * (Gt i l * (Real.exp (z * edgeLo σ l j) * Q l j)) := by
    rw [Finset.sum_congr rfl (fun l _ => by ring :
          ∀ l ∈ Finset.univ, Gt i l * ((if l = j then (1:ℝ) else 0)
              - ρ l * (Real.exp (z * edgeLo σ l j) * Q l j))
            = Gt i l * (if l = j then (1:ℝ) else 0)
              - ρ l * (Gt i l * (Real.exp (z * edgeLo σ l j) * Q l j))),
        Finset.sum_sub_distrib]
    congr 1
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have h2 : (∑ l, Gt i l * (Real.exp (z * edgeLo σ l j)
        * ((if l = j then (1:ℝ) else 0) - ρ l * Q l j)))
      = Gt i j - ∑ l, ρ l * (Gt i l * (Real.exp (z * edgeLo σ l j) * Q l j)) := by
    rw [Finset.sum_congr rfl (fun l _ => by ring :
          ∀ l ∈ Finset.univ, Gt i l * (Real.exp (z * edgeLo σ l j)
              * ((if l = j then (1:ℝ) else 0) - ρ l * Q l j))
            = Gt i l * Real.exp (z * edgeLo σ l j) * (if l = j then (1:ℝ) else 0)
              - ρ l * (Gt i l * (Real.exp (z * edgeLo σ l j) * Q l j))),
        Finset.sum_sub_distrib]
    congr 1
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [hjj, mul_one]
  rw [h1, h2]

/-- ⭐⭐ **MPhase 5 — the posited root retired: `MixBHRootUneq` from the OZ primitives.**  Assembles the
derived c-side (29′) (`mixBHRootUneq_cSide_of_exterior`, from the exterior Baxter closure `hbax`) and the
derived g-side (33′) (`gside_33_of_hgside`, from the g-side OZ Laplace primitive `hgside_mix`) into the
full physical root `MSAMixture.MixBHRootUneq`.  So the unequal-σ Blum–Høye root — consumed as a
hypothesis by the capstones `matMSAmixture_unequalDiam_of_hcore` etc. — now **stands on the recognised
OZ/Baxter primitives** (the exterior DCF closure + the g-side OZ equation + the RDF-moment/Baxter-
transform identities), exactly as the scalar `exactMSA_factorization_of_oz` retired the scalar `h29`/`h33`.
⚠ **The c-side (29′) is fully general** (`mixBHRootUneq_cSide_of_exterior` / `mat_exterior_baxter_relation`
use the full-line convolution).  This `Ioi 0`-fold version's **g-side hypotheses are satisfiable only for
ordered pairs** (`σ_j ≥ σ_l`): `hQtransform` requires `∫_{Ioi 0}e^{−zt}Q_lj = qhatMixRuneq_lj`, which fails
for `edgeLo_lj < 0`.  ✅ **Superseded by `MixBHRootUneq_of_oz_full`** (MPhase 6): its full-support fold makes
`hQtransform` the unconditional full-line transform (`baxterQ_fullline_transform`) and the RDF hard core
discharges the `t<0` correction, with the overlap automatic (`neg_edgeHi_lt_edgeLo`) — so it retires the
posited root for **every** unequal-σ combination (no size-disparity condition). -/
theorem MixBHRootUneq_of_oz {N : ℕ} (z : ℝ) (hz : 0 < z) (ρ σ : Fin N → ℝ)
    (Gt Dt K : Matrix (Fin N) (Fin N) ℝ) (hσ : ∀ k, 0 ≤ σ k)
    (g Q : Fin N → Fin N → ℝ → ℝ) (ghat Qhat : Fin N → Fin N → ℝ)
    (hbax : ∀ i j r, edgeHi σ i j < r →
      2 * Real.pi * r * matMSAtail K z σ i j r
        = -baxterQ' z σ (AVec z ρ σ Gt Dt) (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt) i j r
          + ∑ l, ρ l * ∫ t, baxterQ' z σ (AVec z ρ σ Gt Dt) (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt)
                (Ct z ρ σ Gt Dt) i l (t + r)
                * baxterQ z σ (AVec z ρ σ Gt Dt) (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt)
                    (Ct z ρ σ Gt Dt) j l t)
    (hgsupp : ∀ i l u, u < 0 → g i l u = 0)
    (hF1 : ∀ i l, Integrable (fun u => Real.exp (-z * u) * (u * g i l u)))
    (hF2 : ∀ j l, Integrable (fun t => Real.exp (-z * t) * Q l j t))
    (hgmoment : ∀ i l, FMSA.ExactMSA.GSide.rdfLaplaceMoment (g i l) z = ghat i l)
    (hQtransform : ∀ j l, (∫ t in Set.Ioi (0:ℝ), Real.exp (-z * t) * Q l j t) = Qhat l j)
    (hghat : ∀ i l, ghat i l = Gt i l * Real.exp (-z * edgeHi σ i l))
    (hQhat : ∀ j l, Qhat l j
      = qhatMixRuneq z σ (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt) (AVec z ρ σ Gt Dt) z l j)
    (hgside_mix : ∀ i j, 2 * Real.pi * ghat i j
      = (AVec z ρ σ Gt Dt j + z * qpMat z ρ σ Gt Dt i j + z ^ 2 * Ct z ρ σ Gt Dt i j / 2) / z ^ 2
          * Real.exp (-z * edgeHi σ i j)
        + 2 * Real.pi * ∑ l, ρ l
            * (∫ r in Set.Ioi (0:ℝ), Real.exp (-z * r)
                * ∫ t in Set.Ioi (0:ℝ), (r - t) * g i l (r - t) * Q l j t)) :
    MixBHRootUneq z ρ σ Gt Dt K := by
  refine ⟨mixBHRootUneq_cSide_of_exterior z hz ρ σ Gt Dt K hσ hbax, fun i j => ?_⟩
  rw [gside_bracket_sum_eq z σ ρ Gt
      (fun a b => qhatMixRuneq z σ (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt)
        (AVec z ρ σ Gt Dt) z a b) i j]
  exact gside_33_of_hgside z ρ σ Gt Dt g Q ghat Qhat i j
    (hgsupp i) (hF1 i) (hF2 j) (hgmoment i) (hQtransform j) (hghat i) (hQhat j) (hgside_mix i j)

/-- **The full-line Baxter transform** — discharges the full-support g-side stack's `hQtransform`
from MPhase 1, **unconditionally** (every diameter pair).  `∫_ℝ e^{−zt}·baxterQ_lj(t) dt =
qhatMixRuneq_lj` is `baxterQ_transform_eq_qhatMixRuneq` at `s = z` modulo `mul_comm`.  This is exactly
the hypothesis that was **unsatisfiable** in the `Ioi 0` stack (`mat_gside_fold`) for `edgeLo_lj < 0`:
integrating over all of `ℝ` removes the ordered-pairs restriction entirely. -/
theorem baxterQ_fullline_transform {N : ℕ} (z : ℝ) (hz : 0 < z) (σ A : Fin N → ℝ)
    (qp Wt Ct : Fin N → Fin N → ℝ) (l j : Fin N) (hσl : 0 ≤ σ l) :
    ∫ t, Real.exp (-z * t) * baxterQ z σ A qp Wt Ct l j t
      = qhatMixRuneq z σ qp Wt Ct A z l j := by
  rw [show (∫ t, Real.exp (-z * t) * baxterQ z σ A qp Wt Ct l j t)
        = ∫ t, baxterQ z σ A qp Wt Ct l j t * Real.exp (-z * t) from
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun t => by ring))]
  exact baxterQ_transform_eq_qhatMixRuneq z σ A qp Wt Ct l j z hz.ne' (by linarith) hσl

/-- **The g-side overlap is automatic** — the MPhase-6 side condition `hcond` is never a restriction.
For positive diameters the RDF hard-core reach `−edgeHi σ i l` lies strictly below the Baxter support
floor `edgeLo σ l j`: the `σ_l` **cancels** and the gap is exactly `(σ_i + σ_j)/2 > 0`.  So the
full-support fold factors for **every** diameter triple (no ordered-pairs, no size-disparity condition). -/
theorem neg_edgeHi_lt_edgeLo {N : ℕ} (σ : Fin N → ℝ) (i j l : Fin N)
    (hi : 0 < σ i) (hj : 0 ≤ σ j) : -edgeHi σ i l < edgeLo σ l j := by
  unfold edgeHi edgeLo; linarith

/-- ⭐⭐⭐ **MPhase 6 — the posited root retired for ALL unequal σ: `MixBHRootUneq` from OZ primitives,
full-support g-side.**  The full-support upgrade of `MixBHRootUneq_of_oz`.  The g-side inner integral now
runs over **all of `ℝ`**, so its Baxter transform `hQtransform` (`∫_ℝ e^{−zt}Q_lj = Qhat_lj`) is the
*unconditional* MPhase-1 transform (satisfiable for every diameter pair — see `baxterQ_fullline_transform`),
in place of the `Ioi 0` transform of `MixBHRootUneq_of_oz` that was **unsatisfiable** for `edgeLo_lj < 0`.
The per-`t` collapse is rescued by the **RDF hard core** `hgsupp` (`g_il = 0` on `[0,edgeHi_il)`), and the
overlap `−edgeHi_il < edgeLo_lj` needed for the collapse is **automatic** (`neg_edgeHi_lt_edgeLo`: the
`σ_l` cancels, the gap `= (σ_i+σ_j)/2 > 0` for positive diameters), so it is discharged internally from
`hσ : 0 < σ` — **no side condition survives**.  So the whole unequal-σ root stands on OZ/Baxter primitives
for **every** diameter combination, exactly like the c-side (29′).  (There is no size-disparity corner —
an earlier `σ_j < σ_i + 2σ_l` claim came from a flipped `edgeLo` orientation; confirmed vacuous over 6.5M
random triples in `msaemix_extreme_disparity_check.py`.) -/
theorem MixBHRootUneq_of_oz_full {N : ℕ} (z : ℝ) (hz : 0 < z) (ρ σ : Fin N → ℝ)
    (Gt Dt K : Matrix (Fin N) (Fin N) ℝ) (hσ : ∀ k, 0 < σ k)
    (g Q : Fin N → Fin N → ℝ → ℝ) (ghat Qhat : Fin N → Fin N → ℝ)
    (hbax : ∀ i j r, edgeHi σ i j < r →
      2 * Real.pi * r * matMSAtail K z σ i j r
        = -baxterQ' z σ (AVec z ρ σ Gt Dt) (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt) i j r
          + ∑ l, ρ l * ∫ t, baxterQ' z σ (AVec z ρ σ Gt Dt) (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt)
                (Ct z ρ σ Gt Dt) i l (t + r)
                * baxterQ z σ (AVec z ρ σ Gt Dt) (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt)
                    (Ct z ρ σ Gt Dt) j l t)
    (hgsupp : ∀ i l u, u < edgeHi σ i l → g i l u = 0)
    (hQsupp : ∀ j l t, t < edgeLo σ l j → Q l j t = 0)
    (hF1 : ∀ i l, Integrable (fun u => Real.exp (-z * u) * (u * g i l u)))
    (hF2 : ∀ j l, Integrable (fun t => Real.exp (-z * t) * Q l j t))
    (hgmoment : ∀ i l, FMSA.ExactMSA.GSide.rdfLaplaceMoment (g i l) z = ghat i l)
    (hQtransform : ∀ j l, (∫ t, Real.exp (-z * t) * Q l j t) = Qhat l j)
    (hghat : ∀ i l, ghat i l = Gt i l * Real.exp (-z * edgeHi σ i l))
    (hQhat : ∀ j l, Qhat l j
      = qhatMixRuneq z σ (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt) (AVec z ρ σ Gt Dt) z l j)
    (hgside_mix : ∀ i j, 2 * Real.pi * ghat i j
      = (AVec z ρ σ Gt Dt j + z * qpMat z ρ σ Gt Dt i j + z ^ 2 * Ct z ρ σ Gt Dt i j / 2) / z ^ 2
          * Real.exp (-z * edgeHi σ i j)
        + 2 * Real.pi * ∑ l, ρ l
            * (∫ r in Set.Ioi (0:ℝ), Real.exp (-z * r)
                * ∫ t, (r - t) * g i l (r - t) * Q l j t)) :
    MixBHRootUneq z ρ σ Gt Dt K := by
  refine ⟨mixBHRootUneq_cSide_of_exterior z hz ρ σ Gt Dt K (fun k => (hσ k).le) hbax, fun i j => ?_⟩
  rw [gside_bracket_sum_eq z σ ρ Gt
      (fun a b => qhatMixRuneq z σ (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt)
        (AVec z ρ σ Gt Dt) z a b) i j]
  exact gside_33_of_hgside_full z ρ σ Gt Dt g Q ghat Qhat i j (fun k => (hσ k).le)
    (hgsupp i) (hQsupp j) (fun l => neg_edgeHi_lt_edgeLo σ i j l (hσ i) (hσ j).le)
    (hF1 i) (hF2 j) (hgmoment i) (hQtransform j)
    (hghat i) (hQhat j) (hgside_mix i j)

/-! ### MPhase 8 — the full MSA factorization from the OZ primitives (analog of scalar `exactMSA_factorization_of_oz`) -/

/-- ⭐⭐ **The full unequal-σ MSA mixture factorization, from the OZ primitives** (Baxter-factor HS form).
The mixture analog of the scalar `FMSA.ExactMSA.GSide.exactMSA_factorization_of_oz`: chains
`MixBHRootUneq_of_oz_full` (the posited root now *derived* from the OZ/Baxter primitives) into the
capstone `MSAMixture.matMSAmixture_unequalDiam_of_hcore`.  So the full MSA factorization
`((F̃_HS+F̃₁)(F̃_HS+F̃₁)ᵀ)_ij = δ_ij − (Ĉ_HS,ij + √(ρ_iρ_j)(𝓕[c_core]_ij + 𝓕[c_tail]_ij))` now stands on
the OZ primitives (`hbax` c-side Eq 8 + `hgside_mix` g-side Eq 32 + the RDF-side data), the HS side by
free `ftilde` algebra (`cHShatUneq`).  Footprint = std-3 + the single physics axiom
`matExactMSAUnequalDiam_hcore` inherited from the capstone — `MixBHRootUneq_of_oz_full` adds **no** axiom,
exactly as the scalar leg-3 adds none to `exactMSA_factorization`. -/
theorem matMSAmixture_unequalDiam_of_oz {N : ℕ} (z : ℝ) (hz : 0 < z) (ρ σ : Fin N → ℝ)
    (hσ : ∀ k, 0 < σ k) (hrho : ∀ l, 0 ≤ ρ l)
    (Gt Dt K : Matrix (Fin N) (Fin N) ℝ) (g Q : Fin N → Fin N → ℝ → ℝ)
    (ghat Qhat : Fin N → Fin N → ℝ) (i j : Fin N) (k : ℝ)
    (hbax : ∀ i j r, edgeHi σ i j < r →
      2 * Real.pi * r * matMSAtail K z σ i j r
        = -baxterQ' z σ (AVec z ρ σ Gt Dt) (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt) i j r
          + ∑ l, ρ l * ∫ t, baxterQ' z σ (AVec z ρ σ Gt Dt) (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt)
                (Ct z ρ σ Gt Dt) i l (t + r)
                * baxterQ z σ (AVec z ρ σ Gt Dt) (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt)
                    (Ct z ρ σ Gt Dt) j l t)
    (hgsupp : ∀ i l u, u < edgeHi σ i l → g i l u = 0)
    (hQsupp : ∀ j l t, t < edgeLo σ l j → Q l j t = 0)
    (hF1 : ∀ i l, Integrable (fun u => Real.exp (-z * u) * (u * g i l u)))
    (hF2 : ∀ j l, Integrable (fun t => Real.exp (-z * t) * Q l j t))
    (hgmoment : ∀ i l, FMSA.ExactMSA.GSide.rdfLaplaceMoment (g i l) z = ghat i l)
    (hQtransform : ∀ j l, (∫ t, Real.exp (-z * t) * Q l j t) = Qhat l j)
    (hghat : ∀ i l, ghat i l = Gt i l * Real.exp (-z * edgeHi σ i l))
    (hQhat : ∀ j l, Qhat l j
      = qhatMixRuneq z σ (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt) (AVec z ρ σ Gt Dt) z l j)
    (hgside_mix : ∀ i j, 2 * Real.pi * ghat i j
      = (AVec z ρ σ Gt Dt j + z * qpMat z ρ σ Gt Dt i j + z ^ 2 * Ct z ρ σ Gt Dt i j / 2) / z ^ 2
          * Real.exp (-z * edgeHi σ i j)
        + 2 * Real.pi * ∑ l, ρ l
            * (∫ r in Set.Ioi (0:ℝ), Real.exp (-z * r)
                * ∫ t, (r - t) * g i l (r - t) * Q l j t)) :
    ((FtHSuneq z ρ σ (Complex.I * k) + Ft1uneq z ρ σ Gt Dt (Complex.I * k))
        * (FtHSuneq z ρ σ (-(Complex.I * k))
            + Ft1uneq z ρ σ Gt Dt (-(Complex.I * k))).transpose) i j
      = (if i = j then (1 : ℂ) else 0)
        - (cHShatUneq z ρ σ k i j + (Real.sqrt (ρ i * ρ j) : ℂ)
            * ((FMSA.HardSphere.radial_fourier (matCoreCorrUneq z ρ σ Gt Dt i j) k : ℂ)
              + (FMSA.HardSphere.radial_fourier (matMSAtail K z σ i j) k : ℂ))) :=
  matMSAmixture_unequalDiam_of_hcore z ρ σ hrho Gt Dt K k
    (MixBHRootUneq_of_oz_full z hz ρ σ Gt Dt K hσ g Q ghat Qhat hbax hgsupp hQsupp hF1 hF2
      hgmoment hQtransform hghat hQhat hgside_mix) i j

/-- ⭐⭐⭐ **The full unequal-σ MSA mixture factorization, from the OZ primitives** (physical
`radial_fourier` form — the exact shape of the scalar `exactMSA_factorization_of_oz` conclusion).  Same
chain as `matMSAmixture_unequalDiam_of_oz` but into `matMSAmixture_unequalDiam_physical`, so the RHS is a
pure radial Fourier transform of real-space DCFs: HS core `Φ_HS` + increment core + Yukawa tail.
Footprint = std-3 + `matExactMSAUnequalDiam_hcore` (increment) + `matHSexactUnequalDiam_kspace` (the HS
Baxter–Fourier anchor — the mixture HS side needs this axiom where the scalar `radial_fourier(c_HS)` is a
proved closed form; this is the one genuinely-mixture-specific extra input). -/
theorem matMSAmixture_unequalDiam_physical_of_oz {N : ℕ} (z : ℝ) (hz : 0 < z) (ρ σ : Fin N → ℝ)
    (hσ : ∀ k, 0 < σ k) (hrho : ∀ l, 0 ≤ ρ l)
    (Gt Dt K : Matrix (Fin N) (Fin N) ℝ) (g Q : Fin N → Fin N → ℝ → ℝ)
    (ghat Qhat : Fin N → Fin N → ℝ) (i j : Fin N) (k : ℝ)
    (hbax : ∀ i j r, edgeHi σ i j < r →
      2 * Real.pi * r * matMSAtail K z σ i j r
        = -baxterQ' z σ (AVec z ρ σ Gt Dt) (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt) i j r
          + ∑ l, ρ l * ∫ t, baxterQ' z σ (AVec z ρ σ Gt Dt) (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt)
                (Ct z ρ σ Gt Dt) i l (t + r)
                * baxterQ z σ (AVec z ρ σ Gt Dt) (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt)
                    (Ct z ρ σ Gt Dt) j l t)
    (hgsupp : ∀ i l u, u < edgeHi σ i l → g i l u = 0)
    (hQsupp : ∀ j l t, t < edgeLo σ l j → Q l j t = 0)
    (hF1 : ∀ i l, Integrable (fun u => Real.exp (-z * u) * (u * g i l u)))
    (hF2 : ∀ j l, Integrable (fun t => Real.exp (-z * t) * Q l j t))
    (hgmoment : ∀ i l, FMSA.ExactMSA.GSide.rdfLaplaceMoment (g i l) z = ghat i l)
    (hQtransform : ∀ j l, (∫ t, Real.exp (-z * t) * Q l j t) = Qhat l j)
    (hghat : ∀ i l, ghat i l = Gt i l * Real.exp (-z * edgeHi σ i l))
    (hQhat : ∀ j l, Qhat l j
      = qhatMixRuneq z σ (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt) (AVec z ρ σ Gt Dt) z l j)
    (hgside_mix : ∀ i j, 2 * Real.pi * ghat i j
      = (AVec z ρ σ Gt Dt j + z * qpMat z ρ σ Gt Dt i j + z ^ 2 * Ct z ρ σ Gt Dt i j / 2) / z ^ 2
          * Real.exp (-z * edgeHi σ i j)
        + 2 * Real.pi * ∑ l, ρ l
            * (∫ r in Set.Ioi (0:ℝ), Real.exp (-z * r)
                * ∫ t, (r - t) * g i l (r - t) * Q l j t)) :
    ((FtHSuneq z ρ σ (Complex.I * k) + Ft1uneq z ρ σ Gt Dt (Complex.I * k))
        * (FtHSuneq z ρ σ (-(Complex.I * k))
            + Ft1uneq z ρ σ Gt Dt (-(Complex.I * k))).transpose) i j
      = (if i = j then (1 : ℂ) else 0)
        - (Real.sqrt (ρ i * ρ j) : ℂ)
            * ((FMSA.HardSphere.radial_fourier (matCoreHSuneq z ρ σ i j) k : ℂ)
              + (FMSA.HardSphere.radial_fourier (matCoreCorrUneq z ρ σ Gt Dt i j) k : ℂ)
              + (FMSA.HardSphere.radial_fourier (matMSAtail K z σ i j) k : ℂ)) :=
  matMSAmixture_unequalDiam_physical z ρ σ hrho Gt Dt K k
    (MixBHRootUneq_of_oz_full z hz ρ σ Gt Dt K hσ g Q ghat Qhat hbax hgsupp hQsupp hF1 hF2
      hgmoment hQtransform hghat hQhat hgside_mix) i j

/-! ### MPhase 9 — the equal-diameter root retired via the unequal-diameter leg-3

The equal-σ root `MSAMixture.MixBHRoot` (bare `qhatMixR`, no recentering) is the equal-σ specialization of
`MixBHRootUneq` (recentered `qhatMixRuneq`).  So it too is retired onto OZ primitives — via the
unequal-diameter leg-3 plus the equal-σ bridge — with no separate equal-diameter derivation needed. -/

/-- **The unequal-σ Baxter transform reduces to the equal-σ one at equal diameters.**  At `σ_i = σ_j = sig`
the recentering exponent `lam = (σ_j−σ_i)/2` is `0` and the per-pair `a = σ_i`, `sij = (σ_i+σ_j)/2` both
become `sig`, so `qhatMixRuneq` collapses to `qhatMixR` term-for-term (the `Ct` split is identical, only
reordered). -/
theorem qhatMixRuneq_eq_qhatMixR_of_equal {N : ℕ} (z sig : ℝ) (σ : Fin N → ℝ)
    (qp Wt Ct : Matrix (Fin N) (Fin N) ℝ) (Av : Fin N → ℝ) (s : ℝ) (i j : Fin N)
    (hi : σ i = sig) (hj : σ j = sig) :
    qhatMixRuneq z σ qp Wt Ct Av s i j = qhatMixR z sig qp Wt Ct Av s i j := by
  simp only [qhatMixRuneq, qhatMixR, hi, hj]
  rw [show (sig - sig) / 2 = (0:ℝ) from by ring, mul_zero, neg_zero, Real.exp_zero, one_mul,
      show (sig + sig) / 2 = sig from by ring]
  ring

/-- **`MixBHRootUneq` at equal σ ⟹ `MixBHRoot`.**  The equal-σ bridge: at `σ ≡ sig` the recentering
`e^{z·edgeLo σ · ·} = 1` (`edgeLo = 0`) and `qhatMixRuneq = qhatMixR` (`qhatMixRuneq_eq_qhatMixR_of_equal`),
so the recentered unequal-σ root is term-for-term the bare equal-σ root. -/
theorem MixBHRoot_of_MixBHRootUneq {N : ℕ} (z sig : ℝ) (ρ σ : Fin N → ℝ)
    (Gt Dt K : Matrix (Fin N) (Fin N) ℝ) (hσ : ∀ k, σ k = sig)
    (h : MixBHRootUneq z ρ σ Gt Dt K) : MixBHRoot z sig ρ σ Gt Dt K := by
  obtain ⟨h29, h33⟩ := h
  have hbridge : ∀ a b : Fin N,
      Real.exp (z * edgeLo σ a b)
          * qhatMixRuneq z σ (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt)
              (AVec z ρ σ Gt Dt) z a b
        = qhatMixR z sig (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt)
            (AVec z ρ σ Gt Dt) z a b := by
    intro a b
    rw [show edgeLo σ a b = 0 from by unfold edgeLo; rw [hσ a, hσ b]; ring, mul_zero,
        Real.exp_zero, one_mul,
        qhatMixRuneq_eq_qhatMixR_of_equal z sig σ (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt)
          (Ct z ρ σ Gt Dt) (AVec z ρ σ Gt Dt) z a b (hσ a) (hσ b)]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [← h29 i j]
    exact (Finset.sum_congr rfl (fun l _ => by rw [hbridge j l])).symm
  · rw [← h33 i j]
    congr 1
    exact (Finset.sum_congr rfl (fun l _ => by rw [hbridge l j])).symm

/-- ⭐⭐ **The equal-diameter root retired onto OZ primitives.**  Chains `MixBHRootUneq_of_oz_full` (the
unequal-σ leg-3) with the equal-σ bridge `MixBHRoot_of_MixBHRootUneq`: so the posited equal-σ
`MSAMixture.MixBHRoot` — consumed by `matExactMSAEqualDiam_hcore`, `matMSAmixture_equalDiam`, and the
IFT-smoothness analysis — now **stands on the same OZ/Baxter primitives** as the unequal-σ root, no separate
equal-diameter leg-3 required.  Axiom-clean (std-3). -/
theorem MixBHRoot_of_oz {N : ℕ} (z sig : ℝ) (hz : 0 < z) (ρ σ : Fin N → ℝ)
    (hσeq : ∀ k, σ k = sig) (hσ : ∀ k, 0 < σ k)
    (Gt Dt K : Matrix (Fin N) (Fin N) ℝ) (g Q : Fin N → Fin N → ℝ → ℝ)
    (ghat Qhat : Fin N → Fin N → ℝ)
    (hbax : ∀ i j r, edgeHi σ i j < r →
      2 * Real.pi * r * matMSAtail K z σ i j r
        = -baxterQ' z σ (AVec z ρ σ Gt Dt) (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt) i j r
          + ∑ l, ρ l * ∫ t, baxterQ' z σ (AVec z ρ σ Gt Dt) (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt)
                (Ct z ρ σ Gt Dt) i l (t + r)
                * baxterQ z σ (AVec z ρ σ Gt Dt) (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt)
                    (Ct z ρ σ Gt Dt) j l t)
    (hgsupp : ∀ i l u, u < edgeHi σ i l → g i l u = 0)
    (hQsupp : ∀ j l t, t < edgeLo σ l j → Q l j t = 0)
    (hF1 : ∀ i l, Integrable (fun u => Real.exp (-z * u) * (u * g i l u)))
    (hF2 : ∀ j l, Integrable (fun t => Real.exp (-z * t) * Q l j t))
    (hgmoment : ∀ i l, FMSA.ExactMSA.GSide.rdfLaplaceMoment (g i l) z = ghat i l)
    (hQtransform : ∀ j l, (∫ t, Real.exp (-z * t) * Q l j t) = Qhat l j)
    (hghat : ∀ i l, ghat i l = Gt i l * Real.exp (-z * edgeHi σ i l))
    (hQhat : ∀ j l, Qhat l j
      = qhatMixRuneq z σ (qpMat z ρ σ Gt Dt) (Wt z ρ Gt Dt) (Ct z ρ σ Gt Dt) (AVec z ρ σ Gt Dt) z l j)
    (hgside_mix : ∀ i j, 2 * Real.pi * ghat i j
      = (AVec z ρ σ Gt Dt j + z * qpMat z ρ σ Gt Dt i j + z ^ 2 * Ct z ρ σ Gt Dt i j / 2) / z ^ 2
          * Real.exp (-z * edgeHi σ i j)
        + 2 * Real.pi * ∑ l, ρ l
            * (∫ r in Set.Ioi (0:ℝ), Real.exp (-z * r)
                * ∫ t, (r - t) * g i l (r - t) * Q l j t)) :
    MixBHRoot z sig ρ σ Gt Dt K :=
  MixBHRoot_of_MixBHRootUneq z sig ρ σ Gt Dt K hσeq
    (MixBHRootUneq_of_oz_full z hz ρ σ Gt Dt K hσ g Q ghat Qhat hbax hgsupp hQsupp hF1 hF2
      hgmoment hQtransform hghat hQhat hgside_mix)

/-- **The recentered unequal-σ transform collapses to the equal-σ transform at the ROW diameter.**
For *any* `σ` (not just equal), `e^{z·edgeLo σ j l} · qhatMixRuneq_jl(z) = qhatMixR z (σ_j)_jl` — the
recentering exactly cancels `qhatMixRuneq`'s prefactor `e^{−z·lam}` (`lam = edgeLo σ j l`), and the tail
term's exponent `lam − sij = −σ_j` erases the `σ_l` dependence, leaving the equal-σ `qhatMixR` at the
row diameter `σ_j`.  (`qhatMixRuneq_eq_qhatMixR_of_equal` is the `σ_j = sig` special case.)  This is the
structural key for an unequal-σ smooth family: the recentered root's amplitude dependence is *identical*
to the equal-σ one (the `e^{z·edgeLo}` factors are `σ`-constants), so the `C^∞`/residual scaffolding of
`MSAMixtureBHRootSmooth` transfers unchanged. -/
theorem qhatMixRuneq_recentered_eq_qhatMixR {N : ℕ} (z : ℝ) (σ : Fin N → ℝ)
    (qp Wt Ct : Matrix (Fin N) (Fin N) ℝ) (Av : Fin N → ℝ) (j l : Fin N) :
    Real.exp (z * edgeLo σ j l) * qhatMixRuneq z σ qp Wt Ct Av z j l
      = qhatMixR z (σ j) qp Wt Ct Av z j l := by
  have hL : Real.exp (z * edgeLo σ j l) * Real.exp (-(z * ((σ l - σ j) / 2))) = 1 := by
    rw [← Real.exp_add, show z * edgeLo σ j l + -(z * ((σ l - σ j) / 2)) = 0 from by
      unfold edgeLo; ring, Real.exp_zero]
  have hLS : Real.exp (z * edgeLo σ j l) * Real.exp (-(z * ((σ j + σ l) / 2)))
      = Real.exp (-(z * σ j)) := by
    rw [← Real.exp_add]; congr 1; unfold edgeLo; ring
  simp only [qhatMixRuneq, qhatMixR]
  rw [mul_add, ← mul_assoc, hL, one_mul,
      show Real.exp (z * edgeLo σ j l)
            * (Ct j l * (Real.exp (-(z * ((σ j + σ l) / 2))) / (z + z)))
          = Ct j l * (Real.exp (z * edgeLo σ j l) * Real.exp (-(z * ((σ j + σ l) / 2)))) / (z + z)
        from by ring, hLS]
  ring

end FMSA.ExactMSA.MixLeg3
