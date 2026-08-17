/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.YukawaOZMix.MixtureRDFStructureFactor
import LeanCode.YukawaOZMix.MixtureRDFAntideriv
import LeanCode.HSMixture.MixtureMLBound

/-!
# The concrete HS-pole data of the first-order mixture RDF

Task **MML.11**.  MML.9/MML.10 pinned the RDF's pole structure for the OZ pair `Ĥ₁ = S₀·Ĉ₁·S₀`;
this file produces the **concrete** term-(II) data for the *actual* `N=2` mixture, i.e. an explicit
pole family together with the explicit order-2 Laurent coefficient at each of its members.

## Why this file uses the Y1.6 form, not the structure-factor form

`Ĥ₁ = S₀·Ĉ₁·S₀` has denominator `det T₀ = det Q̂₀(k)·det Q̂₀(−k)`
(`det_eq_of_wienerHopf_factorization`).  Concreteness there would need a zero of `det Q̂₀` to stay a
**simple** zero of that *product*, i.e. `det Q̂₀(−s_k) ≠ 0` — a reflection-asymmetry fact nobody has
proved.  Y1.6's `Ĥ₁ = [Q̂₀ᵀ]⁻¹·B₁·[Q̂₀]⁻¹` has denominator `det Q̂₀(k)²` instead, so its poles are
the `det Q̂₀` zeros **directly**, and simplicity there is exactly `det′ ≠ 0`, which MML.5's family
now exports (`detF_family_magnitude_bound`, strengthened 2026-07-24).  The two forms agree
(`oz1_H1_eq` vs `Hhat1_spec`); the Y1.6 one is the one whose concrete instance is available.

## Results

* `hhat1_entry_eq_num_div_det_sq` — Y1.6's `Ĥ₁` entrywise is `N/(det Q̂₀)²` with
  `N = (adj Q̂₀)ᵀ·B₁·adj Q̂₀`.  Transposed sibling of `inv_conj_entry_eq`/`doubly_prop_entry_eq`.
* `num_div_det_sq_eq_transpose_sandwich`, `hhat1_double_pole` — the order-2 coefficient is the
  **residue-matrix sandwich** `β_k = (R̃ᵀ·B₁(s_k)·R̃) i j`, `R̃ = det′(s_k)⁻¹ • adj Q̂₀(s_k)`
  (MML.10's `hsResidueMatrix` at `Q̂₀`).
* `q0Residue_zero_one` — **the loop closes on MML.5**: `R̃ 0 1 = −q01(s_k)/det′(s_k)`, i.e. the
  `(0,1)` entry of the residue matrix is literally the `Bcoef` that `detF_mixHS_summable` sums and
  that `detF_Bcoef_eq_b_k_residue` certified to be MML.2's `B_k`.  So MML.10's matrix-level residue
  and MML.5's scalar-level residue are the same object, not two parallel constructions.
* `detF_rdf_pole_family` — the capstone: for physical data and `rdist > max(σ₀/2,(σ₁−σ₀)/2)` there
  is one injective family `g` that simultaneously (i) consists of simple `det Q̂₀` zeros,
  (ii) carries the concrete order-2 RDF coefficient `rdfBeta` at each, and (iii) makes MML.5's
  HS-pole series `Summable`.

## What is still missing for MML.8

Everything except the real-space step.  This file supplies term (II)'s *data*; the collapse is the
statement that the resulting series reproduces `r·h₁` on `(0,R_ij)`, which is the matrix analog of
`OZFIX.12`/`OZFIX.22` and — by MML.9 — a hard-sphere obligation.

Status: ✓ axiom-clean.
-/

set_option linter.style.longLine false

open Filter Topology
open scoped Matrix

open FMSA.MixtureHSPoles FMSA.PoleSeries

namespace FMSA.MixtureRDF

/-! ### Y1.6's `Ĥ₁` is `N/det²` with a transposed numerator -/

/-- **Y1.6's `Ĥ₁` entrywise.**  `[Q̂₀ᵀ]⁻¹·B₁·[Q̂₀]⁻¹ = (adj Q̂₀)ᵀ·B₁·adj Q̂₀ / (det Q̂₀)²`, since
`(Mᵀ)⁻¹ = (det M)⁻¹ • (adj M)ᵀ` (`Matrix.adjugate_transpose`, `Matrix.det_transpose`) and
`M⁻¹ = (det M)⁻¹ • adj M`.  The transposed sibling of `inv_conj_entry_eq` (MML.9) and of
`doubly_prop_entry_eq` (`MixtureInnerDCF.lean`); unlike those, its denominator is `det Q̂₀` itself,
which is what makes the concrete family below available. -/
theorem hhat1_entry_eq_num_div_det_sq {N : ℕ} (M B : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) :
    FMSA.MixtureYukawaWH.Hhat1 M B i j
      = ((M.adjugate)ᵀ * B * M.adjugate) i j / (M.det) ^ 2 := by
  unfold FMSA.MixtureYukawaWH.Hhat1
  have h1 : (Mᵀ)⁻¹ = (M.det)⁻¹ • (M.adjugate)ᵀ := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.det_transpose, Matrix.adjugate_transpose]
  have h2 : M⁻¹ = (M.det)⁻¹ • M.adjugate := by rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [h1, h2]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul]
  rw [div_eq_mul_inv]
  ring

/-- `Num/det′²` is the transposed residue-matrix sandwich (`smul` algebra; MML.10's
`num_div_det_sq_eq_sandwich` for the `Aᵀ·B·A` arrangement). -/
theorem num_div_det_sq_eq_transpose_sandwich {N : ℕ} (M B : Matrix (Fin N) (Fin N) ℂ) (Dprime : ℂ)
    (i j : Fin N) :
    ((M.adjugate)ᵀ * B * M.adjugate) i j / Dprime ^ 2
      = ((hsResidueMatrix M Dprime)ᵀ * B * hsResidueMatrix M Dprime) i j := by
  unfold hsResidueMatrix
  simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_apply,
    smul_eq_mul]
  rw [div_eq_mul_inv]
  ring

/-- Entry expansion of `(Aᵀ·B·A) i j = ∑_q ∑_p A p i · B p q · A q j`.  The transposed companion of
MML.9's `triple_entry_eq` and MRS.3's `star_entry_eq`. -/
theorem triple_entry_transpose_eq {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) :
    (Aᵀ * B * A) i j = ∑ q, ∑ p, A p i * B p q * A q j := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [Matrix.mul_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun p _ => by rw [Matrix.transpose_apply])

/-- Continuity version of MML.9's `adjugate_entry_differentiableAt`. -/
theorem adjugate_entry_continuousAt (Tf : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (k : ℂ)
    (hT : ∀ p q, ContinuousAt (fun z => Tf z p q) k) :
    ∀ p q : Fin 2, ContinuousAt (fun z => (Tf z).adjugate p q) k := by
  have e00 : (fun z => (Tf z).adjugate 0 0) = fun z => Tf z 1 1 := by
    funext z; rw [Matrix.adjugate_fin_two]; simp
  have e01 : (fun z => (Tf z).adjugate 0 1) = fun z => -(Tf z 0 1) := by
    funext z; rw [Matrix.adjugate_fin_two]; simp
  have e10 : (fun z => (Tf z).adjugate 1 0) = fun z => -(Tf z 1 0) := by
    funext z; rw [Matrix.adjugate_fin_two]; simp
  have e11 : (fun z => (Tf z).adjugate 1 1) = fun z => Tf z 0 0 := by
    funext z; rw [Matrix.adjugate_fin_two]; simp
  refine Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨?_, ?_⟩, Fin.forall_fin_two.2 ⟨?_, ?_⟩⟩
  · rw [e00]; exact hT 1 1
  · rw [e01]; exact (hT 0 1).neg
  · rw [e10]; exact (hT 1 0).neg
  · rw [e11]; exact hT 0 0

/-- **MML.11 — the RDF's order-2 pole, Y1.6 form.**  At a simple zero `s_k` of `z ↦ det Q̂₀(z)`, the
first-order RDF entry `Ĥ₁ i j` has an order-2 pole whose leading Laurent coefficient is the
residue-matrix sandwich `(R̃ᵀ·B₁(s_k)·R̃) i j`, `R̃ = det′(s_k)⁻¹ • adj Q̂₀(s_k)`.  Instantiates
`double_pole_leading_coeff` through `hhat1_entry_eq_num_div_det_sq`. -/
theorem hhat1_double_pole {N : ℕ} (Mf B1f : ℂ → Matrix (Fin N) (Fin N) ℂ) (s_k Dprime : ℂ)
    (i j : Fin N)
    (hD : HasDerivAt (fun z => (Mf z).det) Dprime s_k)
    (hD0 : (Mf s_k).det = 0) (hDp : Dprime ≠ 0)
    (hNum : ContinuousAt (fun z => (((Mf z).adjugate)ᵀ * B1f z * (Mf z).adjugate) i j) s_k) :
    Tendsto (fun z => (z - s_k) ^ 2 * (FMSA.MixtureYukawaWH.Hhat1 (Mf z) (B1f z) i j)) (𝓝[≠] s_k)
      (𝓝 (((hsResidueMatrix (Mf s_k) Dprime)ᵀ * B1f s_k
            * hsResidueMatrix (Mf s_k) Dprime) i j)) := by
  have hbase := FMSA.MixtureMLSeries.double_pole_leading_coeff
    (fun z => (((Mf z).adjugate)ᵀ * B1f z * (Mf z).adjugate) i j)
    (fun z => (Mf z).det) Dprime s_k hD hD0 hDp hNum
  rw [num_div_det_sq_eq_transpose_sandwich (Mf s_k) (B1f s_k) Dprime i j] at hbase
  refine hbase.congr (fun z => ?_)
  rw [hhat1_entry_eq_num_div_det_sq (Mf z) (B1f z) i j]

/-! ### The concrete `N=2` mixture instance -/

/-- The physical `N=2` Baxter matrix of a `MixParams` pack (the matrix whose determinant is
`P.detF`, `detF_eq_det_Q0`). -/
noncomputable def q0Mat (P : MixParams) (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  FMSA.Q0Complex.Q0_mat_c s (fun i => ((![P.sig0, P.sig1] i : ℝ) : ℂ))
    (fun i j => ((P.rr i j : ℝ) : ℂ)) (fun i j => ((P.Qp i j : ℝ) : ℂ))
    (fun i j => ((P.Qpp i j : ℝ) : ℂ))

@[simp] theorem q0Mat_det (P : MixParams) (s : ℂ) : (q0Mat P s).det = P.detF s := rfl

/-- The **residue matrix of `Q̂₀⁻¹`** at a simple zero `s_k` — MML.10's `hsResidueMatrix` at the
physical Baxter matrix. -/
noncomputable def q0Residue (P : MixParams) (s_k : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  hsResidueMatrix (q0Mat P s_k) (derivF P s_k)

/-- **The loop closes on MML.5.**  The `(0,1)` entry of the residue matrix is exactly the
coefficient `−q01(s_k)/det′(s_k)` that `detF_mixHS_summable` sums and that
`detF_Bcoef_eq_b_k_residue` certified to be MML.2's `B_k`.  So the matrix-level residue of MML.10
and the scalar-level residue of MML.2/MML.5 are one object, not two parallel constructions.
Proof: `adj M 0 1 = −M 0 1` (`adjugate_fin_two_zero_one`, MML.1) plus `q01_eq`. -/
theorem q0Residue_zero_one (P : MixParams) (s_k : ℂ) :
    q0Residue P s_k 0 1 = -(q01 P s_k) / derivF P s_k := by
  unfold q0Residue hsResidueMatrix
  rw [Matrix.smul_apply, smul_eq_mul, adjugate_fin_two_zero_one, q0Mat, ← q01_eq P s_k,
    div_eq_mul_inv]
  ring

/-- **MML.11 — the concrete term-(II) coefficient** `β_k = (R̃ᵀ·B₁(s_k)·R̃) i j` of the first-order
mixture RDF at the HS pole `s_k`. -/
noncomputable def rdfBeta (P : MixParams) (B1f : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (s_k : ℂ)
    (i j : Fin 2) : ℂ :=
  ((q0Residue P s_k)ᵀ * B1f s_k * q0Residue P s_k) i j

/-- Entries of the physical Baxter matrix are continuous off `s = 0` (`q0_entry_c_differentiableAt`). -/
theorem q0Mat_entry_continuousAt (P : MixParams) {s_k : ℂ} (hs : s_k ≠ 0) (p q : Fin 2) :
    ContinuousAt (fun z => q0Mat P z p q) s_k :=
  (q0_entry_c_differentiableAt _ _ _ _ _ _ hs).continuousAt

/-- **MML.11 capstone — one pole family carrying all of term (II)'s concrete data.**  For physical
`N = 2` data and `rdist > max(σ₀/2, (σ₁−σ₀)/2)`, there is a single injective family `g` such that

1. every `g n` is a **simple** zero of `det Q̂₀` (`detF (g n) = 0`, `g n ≠ 0`, `det′(g n) ≠ 0`) —
   the strengthened `detF_family_magnitude_bound` (MML.5, 2026-07-24);
2. the first-order RDF entry has an **order-2 pole** at each `g n` with leading coefficient
   `rdfBeta P B1f (g n) i j` — the explicit residue-matrix sandwich;
3. the reflected HS-pole series `Σ B_k e^{−s_k r}` with `s_k = −(g n)` is **`Summable`** — MML.5,
   whose coefficient is `q0Residue P (g n) 0 1` by `q0Residue_zero_one`.

The only hypothesis on the Yukawa side is entrywise continuity of `B₁` at the poles, which the
finite (★) closed form (MRS.3/MRS.5) supplies. -/
theorem detF_rdf_pole_family (P : MixParams) (hP : P.Phys) {rdist : ℝ}
    (hrd : max (P.sig0 / 2) ((P.sig1 - P.sig0) / 2) < rdist)
    (B1f : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2)
    (hB1 : ∀ (s : ℂ) (p q : Fin 2), ContinuousAt (fun z => B1f z p q) s) :
    ∃ g : ℕ → ℂ, Function.Injective g ∧
      (∀ n, P.detF (g n) = 0 ∧ g n ≠ 0 ∧ derivF P (g n) ≠ 0) ∧
      (∀ n, Tendsto (fun z => (z - g n) ^ 2 * (FMSA.MixtureYukawaWH.Hhat1 (q0Mat P z) (B1f z) i j))
        (𝓝[≠] (g n)) (𝓝 (rdfBeta P B1f (g n) i j))) ∧
      Summable (poleExpTerm (fun n => q0Residue P (g n) 0 1) (fun n => -(g n)) rdist) := by
  obtain ⟨g, hinj, hpoledata, _hres, hsum⟩ := detF_mixHS_summable P hP hrd
  refine ⟨g, hinj, hpoledata, ?_, ?_⟩
  · intro n
    obtain ⟨hz, hg0, hDp⟩ := hpoledata n
    have hD : HasDerivAt (fun z => (q0Mat P z).det) (derivF P (g n)) (g n) :=
      detF_hasDerivAt P hg0
    have hD0 : (q0Mat P (g n)).det = 0 := hz
    have hcontM : ∀ p q : Fin 2, ContinuousAt (fun z => q0Mat P z p q) (g n) :=
      fun p q => q0Mat_entry_continuousAt P hg0 p q
    have hadj := adjugate_entry_continuousAt (fun z => q0Mat P z) (g n) hcontM
    have hNum : ContinuousAt
        (fun z => (((q0Mat P z).adjugate)ᵀ * B1f z * (q0Mat P z).adjugate) i j) (g n) := by
      have hrw : (fun z => (((q0Mat P z).adjugate)ᵀ * B1f z * (q0Mat P z).adjugate) i j)
          = fun z => ∑ q, ∑ p, (q0Mat P z).adjugate p i * B1f z p q
              * (q0Mat P z).adjugate q j := by
        funext z
        exact triple_entry_transpose_eq ((q0Mat P z).adjugate) (B1f z) i j
      rw [hrw]
      apply tendsto_finsetSum
      intro q _
      apply tendsto_finsetSum
      intro p _
      exact ((hadj p i).mul (hB1 (g n) p q)).mul (hadj q j)
    exact hhat1_double_pole (fun z => q0Mat P z) B1f (g n) (derivF P (g n)) i j hD hD0 hDp hNum
  · refine hsum.congr (fun n => ?_)
    simp only [poleExpTerm, q0Residue_zero_one]

/-! ### MML.12 — the collapse region, and what the ML series can *never* reach

`MixRDFInnerCollapse` (`MixtureInnerDCF.lean`) quantifies over the whole inner core,
`∀ r, 0 < r → r < R_ij`. But term (II)'s convergence is established only for
`r > max(σ₀/2, (σ₁−σ₀)/2)` — MML.5's gate exponent `p(r) = max((σ₀−σ₁−2r)/σ₁, (−σ₀−2r)/σ₁)` is
`< −1` exactly there. Two consequences, one a scoping correction and one structural.

**(1) Scoping correction — state the collapse on the annulus.** Below the threshold there is no
summability result at all, and the evidence points the wrong way: the scalar precedent (`Kterm`,
`OZFIX.12`) is genuinely **divergent** for `u ≤ σ/2`, and MML.5's own numerics measured
`p(0.45) = −0.867 > −1` at `σ = [0.8, 2.3]`. Since Lean's `tsum` of a non-summable family is the junk
value `0`, `mixHS_series2` collapses to `0` there and the predicate silently degenerates into
`base r + p0 = r·h₁(r)` — a *different* claim from the intended one, and one that has no reason to
hold. This is the `Kterm` vacuity trap the MML.8 notes warned about (Crux #2, item 4), reaching
MML.8 through the quantifier range rather than through the summand. `MixRDFInnerCollapseAnnulus`
below is the safe statement; `threshold_lt_contact` shows its region is **never empty**, so the
restriction costs nothing.

⚠ This does **not** prove the `(0, R_ij)` form false — only that its content below the threshold is
unsupported and junk-valued. The honest disposition is "state it where term (II) converges".

**(2) Structural — the ML series only ever reaches the OUTER inner-core piece.** The threshold's
second branch is *exactly* the inner-core knot: `(σ₁−σ₀)/2 = Mix.lam 0 1 = λ₀₁`. Hence
`λ₀₁ ≤ max(σ₀/2, λ₀₁) = threshold`, and the whole collapse region sits inside `(λ₀₁, R₀₁)` — the
**outer** of the two pieces into which the unlike-pair inner core splits (IB.4 / MPOLY.5: `(0,λ)`
degree 1, `(λ,R)` degree 4). So the HS-pole Mittag-Leffler series can never certify the inner piece
`(0, λ₀₁)`, whatever happens to MML.8's real-space step; that piece has to come from Group MRS's
finite closed form. (The other branch binds when `2σ₀ ≥ σ₁`, matching MML.5's "the `(σ₁−σ₀)/2`
branch binds only when `2σ₀ < σ₁`".) -/

/-- MML.5's summability threshold for the HS-pole series, `max(σ₀/2, (σ₁−σ₀)/2)`. -/
noncomputable def rdfCollapseThreshold (P : MixParams) : ℝ :=
  max (P.sig0 / 2) ((P.sig1 - P.sig0) / 2)

/-- The unlike-pair contact distance `R₀₁ = (σ₀+σ₁)/2` (`Mix.R 0 1`) — the outer end of the inner
core. -/
noncomputable def contactR01 (P : MixParams) : ℝ := (P.sig0 + P.sig1) / 2

/-- The inner-core knot `λ₀₁ = (σ₁−σ₀)/2` (`Mix.lam 0 1`), where the unlike-pair inner core splits
(IB.4 / MPOLY.5). -/
noncomputable def lam01 (P : MixParams) : ℝ := (P.sig1 - P.sig0) / 2

/-- **The threshold is at or beyond the inner-core knot.**  Definitional (`le_max_right`), but it is
the whole content of MML.12(2): the collapse region lies inside `(λ₀₁, R₀₁)`, so the HS-pole series
can never reach the inner piece `(0, λ₀₁)`. -/
theorem lam01_le_threshold (P : MixParams) : lam01 P ≤ rdfCollapseThreshold P :=
  le_max_right _ _

/-- Any point of the collapse region is beyond the inner-core knot. -/
theorem lam01_lt_of_threshold_lt (P : MixParams) {r : ℝ} (hr : rdfCollapseThreshold P < r) :
    lam01 P < r :=
  lt_of_le_of_lt (lam01_le_threshold P) hr

/-- **The collapse region is never empty**: `max(σ₀/2, (σ₁−σ₀)/2) < (σ₀+σ₁)/2` for any physical
pair.  Both branches are strict for elementary reasons (`0 < σ₁` and `0 < σ₀` respectively), so
restricting `MixRDFInnerCollapse` to the annulus costs no generality. -/
theorem threshold_lt_contact (P : MixParams) (hP : P.Phys) :
    rdfCollapseThreshold P < contactR01 P := by
  have h0 : 0 < P.sig0 := hP.1
  have h1 : 0 < P.sig1 := lt_trans hP.1 hP.2.1
  unfold rdfCollapseThreshold contactR01
  exact max_lt (by linarith) (by linarith)

/-- The threshold is positive, so the annulus really is a proper sub-interval of `(0, R₀₁)`. -/
theorem threshold_pos (P : MixParams) (hP : P.Phys) : 0 < rdfCollapseThreshold P :=
  lt_of_lt_of_le (by linarith [hP.1] : (0:ℝ) < P.sig0 / 2) (le_max_left _ _)

/-- An explicit witness in the collapse region — the predicate below is not vacuous for want of
points. -/
theorem exists_mem_collapse_region (P : MixParams) (hP : P.Phys) :
    ∃ r : ℝ, 0 < r ∧ rdfCollapseThreshold P < r ∧ r < contactR01 P := by
  refine ⟨(rdfCollapseThreshold P + contactR01 P) / 2, ?_, ?_, ?_⟩ <;>
    linarith [threshold_pos P hP, threshold_lt_contact P hP]

/-- **MML.12 — the collapse predicate on the annulus** where term (II) is known to converge.  Same
assembly as `MixRDFInnerCollapse`, with the lower endpoint moved from `0` to MML.5's summability
threshold.  `threshold_lt_contact` / `exists_mem_collapse_region` show the region is nonempty, and
`lam01_lt_of_threshold_lt` locates it inside the outer inner-core piece `(λ₀₁, R₀₁)`. -/
def MixRDFInnerCollapseAnnulus (P : MixParams) (base : ℝ → ℝ) (alpha beta sfam : ℕ → ℂ)
    (p0 : ℝ) (h1true : ℝ → ℝ) : Prop :=
  ∀ r, rdfCollapseThreshold P < r → r < contactR01 P →
    FMSA.MixtureMLSeries.mixRDFInnerAssembly base alpha beta sfam p0 r = r * h1true r

/-- The original `(0, R_ij)` predicate implies the annulus one (the annulus is a sub-interval).  The
converse fails, and the difference is exactly the junk-valued region flagged above — which is why
the annulus form is the one to aim at. -/
theorem mixRDFInnerCollapseAnnulus_of_collapse (P : MixParams) (base : ℝ → ℝ)
    (alpha beta sfam : ℕ → ℂ) (p0 : ℝ) (h1true : ℝ → ℝ) (hP : P.Phys)
    (h : FMSA.MixtureMLSeries.MixRDFInnerCollapse base alpha beta sfam p0 (contactR01 P) h1true) :
    MixRDFInnerCollapseAnnulus P base alpha beta sfam p0 h1true := by
  intro r hlo hhi
  exact h r (lt_trans (threshold_pos P hP) hlo) hhi

/-! ### MML.13 — the `n = 1` soundness bridge

MML.8's collapse is not proved, and its ingredients (MML.9–MML.12) are matrix statements with no
consumer yet. The one mechanical test such a body of statements admits is the **degenerate case**:
instantiate everything at a single component and check that it reproduces the *known* scalar theory
rather than something new. This is the same test MRS.0b ran on the consumer-less physics axiom
`pyhs_mixture_no_spinodal` (`MixtureNoSpinodalN1.lean`), and the project's history says it earns its
keep — statement bugs in MA.5 (junk-valued zero set), MA.2 (partial-sum grouping) and
`baxter_exterior_regularity` clause 6a (a jump at `σ`) were all caught by exactly this kind of
confrontation with a case whose answer is independently known.

Three checks, all passing:

1. **The collapse factor.** MML.10's `R_k = R_k·Ĉ₀(s_k)` at one component yields `Ĉ₀(s_k) = 1` —
   the scalar `ρĈ(kₙ) = 1` behind `OZFIX.11` (`cmix_eq_one_fin_one`). ⚠ **Read this correctly:** at
   `Fin 1` that conclusion is already forced by `det T₀(s_k) = 0` alone
   (`cmix_eq_one_fin_one_of_det`), so the two are *not* independent confirmations. The content is
   **consistency**: specializing the matrix identity must land on exactly the scalar fact, and a
   sign slip, a transposition error, or a wrong `det′` power in `hsResidue_eq_mul_cmix` would land
   somewhere else and contradict the second route. That is what a degenerate-case test can check,
   and all it can check.
2. **The pole order.** Y1.6's `Ĥ₁` at one component is the scalar `B₁/(det Q̂₀)²`
   (`hhat1_fin_one_entry`) — a genuine **double** pole, matching the `Q̂₀⁻¹`-count reading (two
   inverse factors ⇒ order 2) that MML.8's Crux #1 rests on.
3. **The term-(II) coefficient.** MML.11's residue-matrix sandwich
   `β_k = (R̃ᵀ·B₁(s_k)·R̃) i j` degenerates to the elementary `β_k = B₁(s_k)/det′(s_k)²`
   (`hhat1_double_pole_fin_one`) — no matrix artifacts survive, which is the outcome the formula
   had to produce and did not have to. -/

/-- At one component the residue matrix is the scalar `1/det′` times the identity
(`Matrix.adjugate_fin_one`). -/
theorem hsResidueMatrix_fin_one (T0 : Matrix (Fin 1) (Fin 1) ℂ) (Dprime : ℂ) :
    hsResidueMatrix T0 Dprime = Dprime⁻¹ • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  unfold hsResidueMatrix
  rw [Matrix.adjugate_fin_one]

/-- **Check 1a — the collapse factor at one component, via the matrix identity.**  MML.10's
`R_k = R_k·Ĉ₀(s_k)` at `Fin 1` forces `Ĉ₀(s_k) = 1`: the scalar collapse factor `ρĈ(kₙ) = 1` that
powers `OZFIX.11`.  The derivation deliberately routes through `hsResidue_eq_mul_cmix` (cancelling the
nonzero `det′`), *not* through `det T₀(s_k) = 0`.  ⚠ The conclusion is also forced by `hdet` alone
(`cmix_eq_one_fin_one_of_det`), so this is a **consistency** check on the matrix identity, not
independent evidence: what it rules out is a sign/transposition/`det′`-power error, which would make
the two routes disagree. -/
theorem cmix_eq_one_fin_one (C0 T0 : Matrix (Fin 1) (Fin 1) ℂ) (Dprime : ℂ)
    (hT : T0 = 1 - C0) (hdet : T0.det = 0) (hDp : Dprime ≠ 0) :
    C0 = 1 := by
  obtain ⟨hL, _⟩ := hsResidue_eq_mul_cmix C0 T0 Dprime hT hdet
  rw [hsResidueMatrix_fin_one] at hL
  have hL' : Dprime⁻¹ • (1 : Matrix (Fin 1) (Fin 1) ℂ) = Dprime⁻¹ • C0 := by
    rw [hL, Matrix.smul_mul, Matrix.one_mul]
  have := congrArg (fun M : Matrix (Fin 1) (Fin 1) ℂ => (Dprime : ℂ) • M) hL'
  simpa [smul_smul, mul_inv_cancel₀ hDp] using this.symm

/-- **Check 1b — the same, independently.**  Straight from `det T₀(s_k) = 0` at `Fin 1`
(`Matrix.det_fin_one`), with no residue matrix involved.  Agreement with `cmix_eq_one_fin_one` is
the soundness test passing: the matrix machinery adds nothing spurious at one component. -/
theorem cmix_eq_one_fin_one_of_det (C0 T0 : Matrix (Fin 1) (Fin 1) ℂ)
    (hT : T0 = 1 - C0) (hdet : T0.det = 0) : C0 = 1 := by
  -- no residue matrix, no `det′`: the `Fin 1` determinant is the entry itself
  rw [Matrix.det_fin_one, hT] at hdet
  ext i j
  have hij : i = j := Subsingleton.elim i j
  subst hij
  have h00 : C0 i i = 1 := by
    have : (1 : Matrix (Fin 1) (Fin 1) ℂ) 0 0 - C0 0 0 = 0 := hdet
    have hone : (1 : Matrix (Fin 1) (Fin 1) ℂ) 0 0 = 1 := Matrix.one_apply_eq 0
    have hi0 : i = 0 := Subsingleton.elim i 0
    rw [hi0]
    rw [hone] at this
    linear_combination -this
  rw [h00, Matrix.one_apply_eq]

/-- **Check 2 — the pole order.**  Y1.6's RDF at one component is the scalar `B₁/(det Q̂₀)²`: a
genuine **double** pole at a simple zero of `det Q̂₀`, exactly as the `Q̂₀⁻¹`-count reading of
MML.8's Crux #1 predicts (two inverse factors ⇒ order 2). -/
theorem hhat1_fin_one_entry (M B : Matrix (Fin 1) (Fin 1) ℂ) :
    FMSA.MixtureYukawaWH.Hhat1 M B 0 0 = B 0 0 / (M 0 0) ^ 2 := by
  rw [hhat1_entry_eq_num_div_det_sq, Matrix.adjugate_fin_one, Matrix.det_fin_one]
  simp

/-- **Check 3 — the term-(II) coefficient.**  MML.11's residue-matrix sandwich
`β_k = (R̃ᵀ·B₁(s_k)·R̃) i j` degenerates at one component to the elementary scalar double-pole
coefficient `β_k = B₁(s_k)/det′(s_k)²`.  Nothing matrix-shaped survives — the outcome the general
formula had to produce, and the only one consistent with the scalar theory. -/
theorem hhat1_double_pole_fin_one (Mf B1f : ℂ → Matrix (Fin 1) (Fin 1) ℂ) (s_k Dprime : ℂ)
    (hD : HasDerivAt (fun z => (Mf z).det) Dprime s_k)
    (hD0 : (Mf s_k).det = 0) (hDp : Dprime ≠ 0)
    (hNum : ContinuousAt (fun z => B1f z 0 0) s_k) :
    Tendsto (fun z => (z - s_k) ^ 2 * (B1f z 0 0 / ((Mf z) 0 0) ^ 2)) (𝓝[≠] s_k)
      (𝓝 (B1f s_k 0 0 / Dprime ^ 2)) := by
  have hnumeq : (fun z => (((Mf z).adjugate)ᵀ * B1f z * (Mf z).adjugate) 0 0)
      = fun z => B1f z 0 0 := by
    funext z; rw [Matrix.adjugate_fin_one]; simp
  have hNum' : ContinuousAt
      (fun z => (((Mf z).adjugate)ᵀ * B1f z * (Mf z).adjugate) 0 0) s_k := by
    rw [hnumeq]; exact hNum
  have hbase := hhat1_double_pole Mf B1f s_k Dprime 0 0 hD hD0 hDp hNum'
  have hlim : ((hsResidueMatrix (Mf s_k) Dprime)ᵀ * B1f s_k
      * hsResidueMatrix (Mf s_k) Dprime) 0 0 = B1f s_k 0 0 / Dprime ^ 2 := by
    rw [hsResidueMatrix_fin_one]
    simp only [Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, Matrix.smul_apply, smul_eq_mul]
    rw [div_eq_mul_inv]
    ring
  rw [hlim] at hbase
  refine hbase.congr (fun z => ?_)
  rw [hhat1_fin_one_entry]

/-- **Non-vacuity certificate for the `n = 1` checks.**  The hypotheses of
`hhat1_double_pole_fin_one` (and hence of `hhat1_double_pole`, which it specialises) are
simultaneously satisfiable: `Q̂₀(z) = !![z − 1]` has a simple zero of its determinant at `s_k = 1`
with `det′ = 1 ≠ 0`, and a constant `B₁` is continuous.  A degenerate-case test proves nothing if
its own case is empty, and this repo has produced true-but-vacuous statements before
(`b4_origin_bc_abstract`, `b9_d_ij_nonzero_example`), so the witness is recorded rather than
assumed. -/
example : ∃ (Mf B1f : ℂ → Matrix (Fin 1) (Fin 1) ℂ) (s_k Dprime : ℂ),
    HasDerivAt (fun z => (Mf z).det) Dprime s_k ∧ (Mf s_k).det = 0 ∧ Dprime ≠ 0 ∧
      ContinuousAt (fun z => B1f z 0 0) s_k := by
  refine ⟨fun z => !![z - 1], fun _ => 1, 1, 1, ?_, ?_, one_ne_zero, continuousAt_const⟩
  · simpa [Matrix.det_fin_one] using (hasDerivAt_id (1 : ℂ)).sub_const 1
  · simp

/-! ### MML.14 Rung 1 — completing the assembly: `N = adjᵀ·B₁·adj` bounds from matrix primitives

The last mechanical step of Rung 1: assemble the RDF numerator `N = ((adj Q̂₀)ᵀ·B₁·adj Q̂₀)ᵢⱼ` bound
`‖N(s_n)‖ ≤ C·‖s_n‖^q` (`q < 1`) from **entry-level primitive bounds** — the adjugate entries bounded
by `Ca`, the Yukawa numerator entries bounded by `Cb·‖s_n‖^q` (which `bMulti_norm_le` supplies with
`q = −1`) — and combine with the `det′` lower / `det″` upper bounds to conclude tower summability.
This turns MML.14's abstract `mixHSAntideriv2_summable_of_component_bounds` into a statement whose
only inputs are the standard per-entry magnitudes of the *explicit* Baxter matrix and its determinant
derivatives (the mixture `residue_term_norm_bound` primitives). -/

/-- **Matrix triple-product entry bound.**  `‖(Aᵀ·B·A) i j‖ ≤ N²·Ca²·Cb` from entrywise bounds
`‖A p q‖ ≤ Ca`, `‖B p q‖ ≤ Cb`.  Via `triple_entry_transpose_eq` (`(Aᵀ B A)ᵢⱼ = Σ_q Σ_p A_pi B_pq
A_qj`) and the finite triangle inequality.  This is what carries the RDF numerator `N = adjᵀ·B₁·adj`
from the (bounded) adjugate and (decaying) `B₁`. -/
theorem triple_transpose_entry_norm_le {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N)
    {Ca Cb : ℝ} (hCa0 : 0 ≤ Ca) (hCb0 : 0 ≤ Cb)
    (hCa : ∀ p q, ‖A p q‖ ≤ Ca) (hCb : ∀ p q, ‖B p q‖ ≤ Cb) :
    ‖(Aᵀ * B * A) i j‖ ≤ (N : ℝ) ^ 2 * (Ca * Cb * Ca) := by
  rw [triple_entry_transpose_eq]
  calc ‖∑ q, ∑ p, A p i * B p q * A q j‖
      ≤ ∑ q : Fin N, ‖∑ p, A p i * B p q * A q j‖ := norm_sum_le _ _
    _ ≤ ∑ q : Fin N, ∑ p : Fin N, ‖A p i * B p q * A q j‖ := by
        apply Finset.sum_le_sum; intro q _; exact norm_sum_le _ _
    _ ≤ ∑ q : Fin N, ∑ p : Fin N, (Ca * Cb * Ca) := by
        apply Finset.sum_le_sum; intro q _
        apply Finset.sum_le_sum; intro p _
        rw [norm_mul, norm_mul]; gcongr; exacts [hCa p i, hCb p q, hCa q j]
    _ = (N : ℝ) ^ 2 * (Ca * Cb * Ca) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- **Rung 1 — tower summability from the matrix primitives.**  For the RDF with numerator
`N = ((adj Q̂₀)ᵀ·B₁·adj Q̂₀)ᵢⱼ`, coefficients `β = N/det′²`, `α = N′/det′² − N·det″/det′³`, given
entrywise bounds — adjugate `≤ Ca`, Yukawa numerator `≤ Cb·‖s_n‖^q`, `det″ ≤ CDpp`, `N′ ≤ CN′·‖s_n‖^q`
— a constant `det′` lower bound `c₀`, and `q < 1`, the `Kterm`-rung series is `Summable` at every
`r ≥ 0`.  The numerator bounds `‖N‖, ‖N·det″‖ ≤ C·‖s_n‖^q` are *assembled here* from the entry bounds
(`triple_transpose_entry_norm_le`); only `N′` is taken as an input (its own assembly needs the
adjugate/`B₁` derivatives).  Feeds `mixHSAntideriv2_summable_of_component_bounds`.

Instantiating with `B₁ = bMulti` (whose entries obey `‖·‖ ≤ C·‖s‖^{−1}`, `bMulti_norm_le`) and the
bounded adjugate/`det Q̂₀ → 1` derivatives gives `q = −1 < 1` — the concrete threshold-free
summability of the mixture RDF's `Kterm` tower, modulo the standard per-entry magnitude estimates. -/
theorem tower_summable_of_matrix_bounds {NN : ℕ}
    {alpha beta Ndval Dpp Dprime sfam : ℕ → ℂ}
    {adjfun bfun : ℕ → Matrix (Fin NN) (Fin NN) ℂ} {i j : Fin NN}
    {r q Ca Cb CDpp CN' c0 c d : ℝ}
    (hq : q < 1) (hc : 0 < c) (hd : 0 < d) (hr : 0 ≤ r) (hc0 : 0 < c0)
    (hCa0 : 0 ≤ Ca) (hCb0 : 0 ≤ Cb) (hCDpp0 : 0 ≤ CDpp) (hCN'0 : 0 ≤ CN')
    (hs1 : ∀ n, 1 ≤ ‖sfam n‖) (hre : ∀ n, 0 ≤ (sfam n).re)
    (hgrowth : ∀ n : ℕ, c * (n : ℝ) + d ≤ ‖sfam n‖)
    (hbeta : ∀ n, beta n = ((adjfun n)ᵀ * bfun n * adjfun n) i j / (Dprime n) ^ 2)
    (halpha : ∀ n, alpha n = Ndval n / (Dprime n) ^ 2
        - ((adjfun n)ᵀ * bfun n * adjfun n) i j * Dpp n / (Dprime n) ^ 3)
    (hDlo : ∀ n, c0 ≤ ‖Dprime n‖)
    (hadj : ∀ n p qq, ‖adjfun n p qq‖ ≤ Ca) (hb : ∀ n p qq, ‖bfun n p qq‖ ≤ Cb * ‖sfam n‖ ^ q)
    (hDpp : ∀ n, ‖Dpp n‖ ≤ CDpp) (hNd : ∀ n, ‖Ndval n‖ ≤ CN' * ‖sfam n‖ ^ q) :
    Summable (fun n => mixHSAntideriv2 alpha beta sfam n r) := by
  set K : ℝ := (NN : ℝ) ^ 2 * (Ca * Ca * Cb) with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hNbd : ∀ n, ‖((adjfun n)ᵀ * bfun n * adjfun n) i j‖ ≤ K * ‖sfam n‖ ^ q := by
    intro n
    have h := triple_transpose_entry_norm_le (adjfun n) (bfun n) i j hCa0
      (by positivity : (0 : ℝ) ≤ Cb * ‖sfam n‖ ^ q) (hadj n) (hb n)
    calc ‖((adjfun n)ᵀ * bfun n * adjfun n) i j‖
        ≤ (NN : ℝ) ^ 2 * (Ca * (Cb * ‖sfam n‖ ^ q) * Ca) := h
      _ = K * ‖sfam n‖ ^ q := by rw [hK]; ring
  refine mixHSAntideriv2_summable_of_component_bounds (q := q) (CN := K + CN' + K * CDpp)
    (Nval := fun n => ((adjfun n)ᵀ * bfun n * adjfun n) i j) (Ndval := Ndval) (Dpp := Dpp)
    (Dprime := Dprime) hq (by positivity) hc hd hr hc0 hs1 hre hgrowth hbeta halpha hDlo
    (fun n => ?_) (fun n => ?_) (fun n => ?_)
  · have hsq : 0 ≤ ‖sfam n‖ ^ q := Real.rpow_nonneg (le_trans zero_le_one (hs1 n)) q
    have hle : K ≤ K + CN' + K * CDpp := by nlinarith [hK0, hCN'0, hCDpp0]
    calc ‖((adjfun n)ᵀ * bfun n * adjfun n) i j‖ ≤ K * ‖sfam n‖ ^ q := hNbd n
      _ ≤ (K + CN' + K * CDpp) * ‖sfam n‖ ^ q := mul_le_mul_of_nonneg_right hle hsq
  · have hsq : 0 ≤ ‖sfam n‖ ^ q := Real.rpow_nonneg (le_trans zero_le_one (hs1 n)) q
    have hle : CN' ≤ K + CN' + K * CDpp := by nlinarith [hK0, hCDpp0]
    calc ‖Ndval n‖ ≤ CN' * ‖sfam n‖ ^ q := hNd n
      _ ≤ (K + CN' + K * CDpp) * ‖sfam n‖ ^ q := mul_le_mul_of_nonneg_right hle hsq
  · have hsq : 0 ≤ ‖sfam n‖ ^ q := Real.rpow_nonneg (le_trans zero_le_one (hs1 n)) q
    have h1 : ‖((adjfun n)ᵀ * bfun n * adjfun n) i j‖ * ‖Dpp n‖ ≤ (K * ‖sfam n‖ ^ q) * CDpp :=
      mul_le_mul (hNbd n) (hDpp n) (norm_nonneg _) (by positivity)
    have hle : K * CDpp ≤ K + CN' + K * CDpp := by nlinarith [hK0, hCN'0]
    calc ‖((adjfun n)ᵀ * bfun n * adjfun n) i j‖ * ‖Dpp n‖
        ≤ (K * ‖sfam n‖ ^ q) * CDpp := h1
      _ = (K * CDpp) * ‖sfam n‖ ^ q := by ring
      _ ≤ (K + CN' + K * CDpp) * ‖sfam n‖ ^ q := mul_le_mul_of_nonneg_right hle hsq

end FMSA.MixtureRDF
