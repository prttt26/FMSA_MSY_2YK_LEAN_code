/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.YukawaOZMix.MSAMixtureBaxterConv
import LeanCode.YukawaOZMix.MSAMixtureBHRootUneq
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

This is the rigorously-derived matrix analog of the scalar `h29_of_baxter_exterior` — **but note the
recentering factor `e^{z·edgeLo_jl}` on the transform** (`= e^{z(edgeHi_il − edgeHi_ij)}`), which the
posited `MSAMixture.MixBHRootUneq` (29′) omits.  At equal σ (`edgeLo_jl = 0`) they coincide; at unequal
σ they differ (a σ-power masked by σ=1 — see the FINDING note above).  Proof: evaluate `hbax` at
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

/-! ### MPhase 3 — the g-side matrix Laplace-convolution stack (the CRUX)

The g-side OZ equation (Blum–Høye Eq. 32), Laplace-transformed at `s = z`, folds the species-summed
RDF⋆Baxter convolution `∑_l ρ_l ∫₀^∞ e^{−zr} (∫₀^∞ (r−t) g_il(r−t) Q_lj(t) dt) dr` onto the
transforms `∑_l ρ_l ĝ_il(z)·Q̂_lj(z)`.  The scalar convolution theorem
`FMSA.ExactMSA.GSide.laplace_conv_eq_rdf_mul_qhat_of_integrable` (whose Fubini swap is already
discharged, axiom-clean) is **generic** in the RDF `g` and Baxter factor `Q`, so it lifts **per
species `l`**; the `∑_l ρ_l` contraction the roadmap flagged as the crux is then **just linearity of
the integral** (`Finset.sum_congr`).  The g-side thus reuses the scalar Fubini machinery wholesale.

⚠ **Edge cross-check (g-side vs the c-side FINDING).** `gam`'s convention is `Gt_ij = ĝ_ij(z)·e^{+zσ_ij}`
(`MSAMixtureCancellation.lean:67`), so `ĝ_il(z) = Gt_il·e^{−zσ_il}` carries a `σ`-edge factor of its
own; and `Q̂_lj(z) = ∫₀^∞ e^{−zt}Q_lj(t) dt = qhatMixRuneq_lj` only when `edgeLo_lj ≥ 0` (else the
`Ioi 0` transform misses `[edgeLo_lj, 0)`).  So the g-side (33′) is expected to carry an analogous
edge/recentering factor at unequal σ — the resolution needs the concrete mixture g-side OZ Eq (32)
(the matrix g-source + the convolution domain), the g-side analog of the c-side `hbax`. -/

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

end FMSA.ExactMSA.MixLeg3
