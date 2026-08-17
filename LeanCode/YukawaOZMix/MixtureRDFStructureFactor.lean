/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.Analysis.MatrixIdentity
import LeanCode.YukawaOZMix.MixtureRealSpace
import LeanCode.YukawaOZMix.MixtureInnerDCF

/-!
# The first-order mixture RDF as `Ĥ₁ = S₀·Ĉ₁·S₀` — localizing every HS pole in the structure factor

Task **MML.8** (RDF-only), the structural half of Crux #2.  Group MRS's `oz1_C1_eq`
(`MixtureRealSpace.lean`) solves the first-order OZ equation `Ĥ₁·T₀ = S₀·Ĉ₁` for the **DCF**,
`Ĉ₁ = T₀·Ĥ₁·T₀`.  This file records its **dual**, which solves the same equation for the **RDF**:

    Ĥ₁ = S₀ · Ĉ₁ · S₀ ,        `S₀ = I + Ĥ₀ = T₀⁻¹`,  `T₀ = I − Ĉ₀`.   (`oz1_H1_eq`)

`S₀` is the hard-sphere structure factor.  Read together with the two established facts

* **(★)** `Ĉ₁ = Q̂₀(−k)·B₁(k)·Q̂₀ᵀ(−k)` carries **no** `Q̂₀⁻¹`, so the first-order **DCF has no HS
  poles** and is a finite closed form (MRS.3 `star_of_oz1_baxter`, `star_entry_differentiableAt`;
  the finite form is MRS.5), and
* `T₀ = Q̂₀(k)·Q̂₀ᵀ(−k)` (MRS.6 `Cmix0_factorization`), whence
  `det T₀ = det Q̂₀(k)·det Q̂₀(−k)` (`det_eq_of_wienerHopf_factorization`),

the dual identity says something sharper than "the RDF has double HS poles": it says **every HS pole
of the first-order RDF is contributed by the two `S₀` factors, and by nothing else.**  The Yukawa
half of the problem is finite and already closed by Group MRS; what remains in MML.8's collapse is
purely the pole content of `S₀`, i.e. of the **hard-sphere mixture RDF** `Ĥ₀`.

## Results

* `oz1_H1_eq` — the dual of `oz1_C1_eq`: `Ĥ₁ = S₀·Ĉ₁·S₀` from `hoz`, `hTS` alone (pure algebra;
  strictly weaker hypotheses than `star_of_first_order_oz`, which additionally needs MRS.1/MRS.7).
* `structureFactor_eq_inv` — `S₀ = T₀⁻¹` (from `hTS`, no invertibility hypothesis needed:
  `Matrix.inv_eq_right_inv`).
* `inv_conj_entry_eq` — the `N/det²` shape: `(M⁻¹·K·M⁻¹) i j = (adj M·K·adj M) i j / (det M)²`.
  The **transpose-free sibling** of `doubly_prop_entry_eq` (`MixtureInnerDCF.lean`), which proves
  the same shape for the Y1.6 form `[Q̂₀⁻¹·K·Q̂₀⁻ᵀ]`.
* `rdf_entry_eq_num_div_det_sq` — the two combined: the RDF entry is `Num/(det T₀)²` with
  `Num = (adj T₀·Ĉ₁·adj T₀) i j`.  **This is a second, independent proof of Crux #1**
  (`doubly_prop_entry_eq` argued from `Ĥ₁ = [Q̂₀ᵀ]⁻¹B₁[Q̂₀]⁻¹`; this one argues from the OZ equation
  and never mentions `B₁`), and it is the form `double_pole_leading_coeff` consumes.
* `det_eq_of_wienerHopf_factorization` — `det T₀ = det Q̂₀(k) · det Q̂₀(−k)`, pinning the pole
  locations to Group MZERO's zero family (at `k` **and** its reflection).  Its generic core is
  `Analysis.MatrixIdentity.det_mul_transpose`, homed there because `HSMixture/MixtureRDFUniqueness.lean`
  needs it too and may not import this file (`CONVENTIONS.md` layering).
* `rdf_entry_differentiableAt` — the sharp localization (`Fin 2`): off the zeros of `det T₀`, the
  RDF entries are differentiable wherever `T₀` and `Ĉ₁` are.  The exact counterpart of MRS.3's
  `star_entry_differentiableAt`, with the `det T₀ ≠ 0` hypothesis that the DCF statement pointedly
  does **not** have — that single hypothesis *is* the DCF/RDF dividing line.
* `rdf_entry_double_pole` — at a **simple** zero `s_k` of `det T₀`, the RDF entry has a genuine
  order-2 pole with leading Laurent coefficient `Num(s_k)/(det T₀)′(s_k)²`, i.e. term (II)'s
  `β_k` (`mixHSterm2`, `MixtureInnerDCF.lean`) for the physical OZ pair.

## What this does *not* do

It does not discharge `MixRDFInnerCollapse`.  The collapse is the real-space statement that the
Mittag-Leffler sum over these poles reproduces the inner-core value; this file only shows that the
poles being summed are exactly `S₀`'s, and that their order is 2.  Per the `OZFIX.22` template the
remaining input is a matrix real-space/uniqueness bridge — now visibly a statement about the
**hard-sphere** mixture alone, since the Yukawa factor `Ĉ₁` sitting between the two `S₀`'s is
pole-free.

Status: ✓ axiom-clean.
-/

set_option linter.style.longLine false

open Filter Topology
open scoped Matrix

namespace FMSA.MixtureRDF

/-! ### The dual of `oz1_C1_eq` — solving the first-order OZ equation for the RDF -/

/-- **MML.8 — the RDF dual of MRS.2's `oz1_C1_eq`.**  The first-order OZ equation
`Ĥ₁·T₀ = S₀·Ĉ₁` together with the zeroth-order OZ `T₀·S₀ = I` (`S₀ = (I−Ĉ₀)⁻¹`) gives

    Ĥ₁ = Ĥ₁·(T₀·S₀) = (Ĥ₁·T₀)·S₀ = (S₀·Ĉ₁)·S₀ = S₀·Ĉ₁·S₀ .

Pure algebra, and with *strictly fewer* hypotheses than `star_of_first_order_oz` (no factorization,
no symmetry).  Physically: the first-order RDF is the first-order DCF **dressed on both sides by the
hard-sphere structure factor** `S₀ = I + Ĥ₀`. -/
theorem oz1_H1_eq {N : ℕ} (T0 S0 H1 C1 : Matrix (Fin N) (Fin N) ℂ)
    (hoz : H1 * T0 = S0 * C1) (hTS : T0 * S0 = 1) :
    H1 = S0 * C1 * S0 := by
  calc H1 = H1 * (T0 * S0) := by rw [hTS, Matrix.mul_one]
    _ = (H1 * T0) * S0 := by rw [Matrix.mul_assoc]
    _ = (S0 * C1) * S0 := by rw [hoz]
    _ = S0 * C1 * S0 := rfl

/-- The zeroth-order OZ relation identifies the structure factor with `T₀⁻¹`.  No invertibility
hypothesis is needed: a right inverse of a square matrix over a commutative ring *is* the inverse
(`Matrix.inv_eq_right_inv`). -/
theorem structureFactor_eq_inv {N : ℕ} (T0 S0 : Matrix (Fin N) (Fin N) ℂ)
    (hTS : T0 * S0 = 1) : T0⁻¹ = S0 :=
  Matrix.inv_eq_right_inv hTS

/-- The first-order RDF written with the inverse made explicit: `Ĥ₁ = T₀⁻¹·Ĉ₁·T₀⁻¹`. -/
theorem rdf_eq_inv_conj {N : ℕ} (T0 S0 H1 C1 : Matrix (Fin N) (Fin N) ℂ)
    (hoz : H1 * T0 = S0 * C1) (hTS : T0 * S0 = 1) :
    H1 = T0⁻¹ * C1 * T0⁻¹ := by
  rw [oz1_H1_eq T0 S0 H1 C1 hoz hTS, structureFactor_eq_inv T0 S0 hTS]

/-! ### The four-term structure-factor dressing — where the HS poles enter

`S₀ = I + Ĥ₀` (structure factor = identity + hard-sphere RDF).  Substituting into `Ĥ₁ = S₀·Ĉ₁·S₀`
and expanding names the RDF as the DCF plus exactly three `Ĥ₀`-dressed terms.  Since `Ĉ₁` is finite
and HS-pole-free (MRS.3/MRS.5), **every HS pole of the first-order RDF sits in one of the three terms
carrying an `Ĥ₀` factor** — the undressed `Ĉ₁` term contributes none.  This is the algebraic core of
MML.9's "the residual collapse content is hard-sphere": in real space (`⋆` = convolution) it reads

    h₁ = c₁ + h₀⋆c₁ + c₁⋆h₀ + h₀⋆c₁⋆h₀ ,

so the RDF's Mittag-Leffler series is the sum of the ML series of the three `h₀`-dressed terms alone
(the collapse target `assembly = r·h₁`, MML.8, is then term-by-term over these three).  The Fourier
identity here is the mechanical half; the real-space convolution reading is the (still-missing)
transform step. -/
theorem structureFactorDressing {N : ℕ} (H0 C1 : Matrix (Fin N) (Fin N) ℂ) :
    (1 + H0) * C1 * (1 + H0) = C1 + H0 * C1 + C1 * H0 + H0 * C1 * H0 := by
  noncomm_ring

/-- **The RDF's four-term dressing.**  With `S₀ = I + Ĥ₀`, the first-order RDF is the DCF plus three
`Ĥ₀`-dressed terms (`structureFactorDressing` applied to `oz1_H1_eq`). -/
theorem rdf_four_term_dressing {N : ℕ} (T0 S0 H0 H1 C1 : Matrix (Fin N) (Fin N) ℂ)
    (hoz : H1 * T0 = S0 * C1) (hTS : T0 * S0 = 1) (hS0 : S0 = 1 + H0) :
    H1 = C1 + H0 * C1 + C1 * H0 + H0 * C1 * H0 := by
  rw [oz1_H1_eq T0 S0 H1 C1 hoz hTS, hS0, structureFactorDressing]

/-- **The DCF term carries no HS poles; the three dressed terms carry them all.**  Restatement of
the dressing as `Ĥ₁ − Ĉ₁ = (the three Ĥ₀ terms)`: the difference between the first-order RDF and the
first-order DCF is entirely `Ĥ₀`-dressed.  Since `Ĉ₁` is HS-pole-free (MRS.3), this locates every HS
pole of `Ĥ₁` in the right-hand side — the precise sense in which MML.8's collapse is a hard-sphere
(`Ĥ₀`) statement, not a Yukawa one. -/
theorem rdf_sub_dcf_is_dressed {N : ℕ} (T0 S0 H0 H1 C1 : Matrix (Fin N) (Fin N) ℂ)
    (hoz : H1 * T0 = S0 * C1) (hTS : T0 * S0 = 1) (hS0 : S0 = 1 + H0) :
    H1 - C1 = H0 * C1 + C1 * H0 + H0 * C1 * H0 := by
  rw [rdf_four_term_dressing T0 S0 H0 H1 C1 hoz hTS hS0]
  abel

/-! ### The `N/det²` shape -/

/-- **The two-sided inverse conjugation is `N/det²`.**  `(M⁻¹·K·M⁻¹) i j = (adj M·K·adj M) i j /
(det M)²`, since `M⁻¹ = (det M)⁻¹ • adj M` contributes two `det⁻¹` factors.  This is the
transpose-free sibling of `doubly_prop_entry_eq` (`MixtureInnerDCF.lean`), which establishes the
same shape for the Y1.6 form `[Q̂₀⁻¹·K·Q̂₀⁻ᵀ]₀₁`; the OZ route below produces this one. -/
theorem inv_conj_entry_eq {N : ℕ} (M K : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) :
    (M⁻¹ * K * M⁻¹) i j = (M.adjugate * K * M.adjugate) i j / (M.det) ^ 2 := by
  have hinv : M⁻¹ = (M.det)⁻¹ • M.adjugate := by rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [hinv]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul]
  rw [div_eq_mul_inv]
  ring

/-- **MML.8 Crux #1, second (OZ-route) proof.**  From the first-order OZ equation alone, every entry
of the first-order RDF is `Num/(det T₀)²` with the *entire-where-`T₀`-and-`Ĉ₁`-are* numerator
`Num = (adj T₀·Ĉ₁·adj T₀) i j`.  So at a simple zero of `det T₀` the RDF has an order-2 pole — the
`(α_k + β_k·r)·e^{−s_k r}` term (II) of `mixHSterm2`.  Independent of `doubly_prop_entry_eq`: that
argument runs through `Ĥ₁ = [Q̂₀ᵀ]⁻¹·B₁·[Q̂₀]⁻¹` (Y1.6), this one never mentions `B₁`. -/
theorem rdf_entry_eq_num_div_det_sq {N : ℕ} (T0 S0 H1 C1 : Matrix (Fin N) (Fin N) ℂ)
    (hoz : H1 * T0 = S0 * C1) (hTS : T0 * S0 = 1) (i j : Fin N) :
    H1 i j = (T0.adjugate * C1 * T0.adjugate) i j / (T0.det) ^ 2 := by
  rw [rdf_eq_inv_conj T0 S0 H1 C1 hoz hTS, inv_conj_entry_eq T0 C1 i j]

/-- **The RDF's poles sit at the Group MZERO zeros, at `k` and at its reflection.**  Under MRS.1's
Wiener–Hopf factorization `T₀ = Q̂₀(k)·Q̂₀ᵀ(−k)` (MRS.6 `Cmix0_factorization`),
`det T₀ = det Q̂₀(k) · det Q̂₀(−k)`.  Combined with `rdf_entry_eq_num_div_det_sq`, the first-order
RDF's HS poles are exactly the zeros of `det Q̂₀` **and their reflections** — the reflected family
being precisely the one `detF_mixHS_summable` (`MixtureMLBound.lean`) enumerates. -/
theorem det_eq_of_wienerHopf_factorization {N : ℕ} (Qp Qm T0 : Matrix (Fin N) (Fin N) ℂ)
    (hfact : T0 = Qp * Qmᵀ) : T0.det = Qp.det * Qm.det := by
  rw [hfact, FMSA.MatrixIdentity.det_mul_transpose]

/-- **The whole first-order RDF in one line.**  Combining the OZ dual with MRS.1 and (★): the
numerator is built from the *finite*, HS-pole-free (★) DCF `Ĉ₁ = Q̂₀(−k)·B₁·Q̂₀ᵀ(−k)`, and the entire
HS-pole content is the square of `det Q̂₀(k)·det Q̂₀(−k)`. -/
theorem rdf_entry_star_eq {N : ℕ} (Qp Qm T0 S0 H1 C1 B1 : Matrix (Fin N) (Fin N) ℂ)
    (hoz : H1 * T0 = S0 * C1) (hTS : T0 * S0 = 1) (hfact : T0 = Qp * Qmᵀ)
    (hstar : C1 = Qm * B1 * Qmᵀ) (i j : Fin N) :
    H1 i j
      = (T0.adjugate * (Qm * B1 * Qmᵀ) * T0.adjugate) i j / (Qp.det * Qm.det) ^ 2 := by
  rw [rdf_entry_eq_num_div_det_sq T0 S0 H1 C1 hoz hTS i j, hstar,
    det_eq_of_wienerHopf_factorization Qp Qm T0 hfact]

/-! ### Sharp localization: off `det T₀ = 0` the RDF is regular -/

/-- Entry expansion of a two-sided (transpose-free) triple product:
`(A·B·A) i j = ∑_q ∑_p A i p · B p q · A q j`.  Companion to MRS.3's `star_entry_eq`, which does the
transposed shape `(A·B·Aᵀ)`. -/
theorem triple_entry_eq {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) :
    (A * B * A) i j = ∑ q, ∑ p, A i p * B p q * A q j := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [Matrix.mul_apply, Finset.sum_mul]

/-- Entries of the `2×2` adjugate are (up to sign) entries of the matrix, hence differentiable
wherever the entries are (`Matrix.adjugate_fin_two`). -/
theorem adjugate_entry_differentiableAt (Tf : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (k : ℂ)
    (hT : ∀ p q, DifferentiableAt ℂ (fun z => Tf z p q) k) :
    ∀ p q : Fin 2, DifferentiableAt ℂ (fun z => (Tf z).adjugate p q) k := by
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

/-- **The DCF/RDF dividing line, made into a hypothesis.**  Every entry of the first-order RDF
`Ĥ₁(z) = T₀(z)⁻¹·Ĉ₁(z)·T₀(z)⁻¹` is differentiable at `k` as soon as the entries of `T₀` and `Ĉ₁`
are **and** `det T₀(k) ≠ 0`.  Compare MRS.3's `star_entry_differentiableAt` for the DCF, which has
**no** determinant hypothesis at all: that missing hypothesis is exactly what makes the DCF
HS-pole-free and the RDF not.  (Stated at `Fin 2`, the mixture case, since it discharges the
adjugate's differentiability explicitly.) -/
theorem rdf_entry_differentiableAt (T0f C1f : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (k : ℂ)
    (hT : ∀ p q, DifferentiableAt ℂ (fun z => T0f z p q) k)
    (hC : ∀ p q, DifferentiableAt ℂ (fun z => C1f z p q) k)
    (hdet : (T0f k).det ≠ 0) (i j : Fin 2) :
    DifferentiableAt ℂ (fun z => ((T0f z)⁻¹ * C1f z * (T0f z)⁻¹) i j) k := by
  have hrw : (fun z => ((T0f z)⁻¹ * C1f z * (T0f z)⁻¹) i j)
      = fun z => (∑ q, ∑ p, (T0f z).adjugate i p * C1f z p q * (T0f z).adjugate q j)
          / ((T0f z).det) ^ 2 := by
    funext z
    rw [inv_conj_entry_eq (T0f z) (C1f z) i j, triple_entry_eq]
  rw [hrw]
  have hadj := adjugate_entry_differentiableAt T0f k hT
  have hnum : DifferentiableAt ℂ
      (fun z => ∑ q, ∑ p, (T0f z).adjugate i p * C1f z p q * (T0f z).adjugate q j) k := by
    apply DifferentiableAt.fun_sum
    intro q _
    apply DifferentiableAt.fun_sum
    intro p _
    exact ((hadj i p).mul (hC p q)).mul (hadj q j)
  have hdetdiff : DifferentiableAt ℂ (fun z => (T0f z).det) k := by
    have hd : (fun z => (T0f z).det)
        = fun z => T0f z 0 0 * T0f z 1 1 - T0f z 0 1 * T0f z 1 0 := by
      funext z; rw [Matrix.det_fin_two]
    rw [hd]
    exact ((hT 0 0).mul (hT 1 1)).sub ((hT 0 1).mul (hT 1 0))
  exact hnum.div (hdetdiff.pow 2) (pow_ne_zero 2 hdet)

/-! ### The order-2 pole at a simple zero of `det T₀` -/

/-- **MML.8 term (II) for the physical OZ pair.**  At a **simple** zero `s_k` of `z ↦ det T₀(z)`,
the first-order RDF entry `Ĥ₁ i j = Num/(det T₀)²` has a genuine order-2 pole, with leading Laurent
coefficient `Num(s_k)/(det T₀)′(s_k)²` — the `β_k` (`r`-prefactor coefficient) of `mixHSterm2`.
Direct instantiation of `double_pole_leading_coeff` (`MixtureInnerDCF.lean`) at
`N := (adj T₀·Ĉ₁·adj T₀) i j`, `D := det T₀`, routed through `inv_conj_entry_eq`.

Nonvanishing of the coefficient — i.e. that the pole really is order 2 and not lower — is
`double_pole_leading_coeff_ne_zero` at `Num(s_k) ≠ 0`. -/
theorem rdf_entry_double_pole (T0f C1f : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (s_k Dprime : ℂ)
    (i j : Fin 2)
    (hD : HasDerivAt (fun z => (T0f z).det) Dprime s_k)
    (hD0 : (T0f s_k).det = 0) (hDp : Dprime ≠ 0)
    (hNum : ContinuousAt
      (fun z => ((T0f z).adjugate * C1f z * (T0f z).adjugate) i j) s_k) :
    Tendsto (fun z => (z - s_k) ^ 2 * (((T0f z)⁻¹ * C1f z * (T0f z)⁻¹) i j)) (𝓝[≠] s_k)
      (𝓝 (((T0f s_k).adjugate * C1f s_k * (T0f s_k).adjugate) i j / Dprime ^ 2)) := by
  have hbase := FMSA.MixtureHSPoles.double_pole_leading_coeff
    (fun z => ((T0f z).adjugate * C1f z * (T0f z).adjugate) i j)
    (fun z => (T0f z).det) Dprime s_k hD hD0 hDp hNum
  refine hbase.congr (fun z => ?_)
  rw [inv_conj_entry_eq (T0f z) (C1f z) i j]

/-! ### Both term-(II) coefficients in terms of `D′` and `D″` alone

`double_pole_second_coeff` (`MixtureInnerDCF.lean`) states the order-1 Laurent coefficient as
`α_k = N′/E(s_k)² − 2·N(s_k)·E′/E(s_k)³`, where `E` is the analytic cofactor of the simple-zero
factorization `D = (·−s_k)·E`.  `E` is an auxiliary object — a *consumer* (the concrete `detF` pole
family of `MixtureChordFamily.lean`, or a numerical evaluation) has `D = det Q̂₀` and its derivatives,
not `E`.  Eliminating it via

    D′(s_k) = E(s_k),        D″(s_k) = 2·E′(s_k)

turns the pair of coefficients into

    β_k = N(s_k) / D′(s_k)²,        α_k = N′(s_k)/D′(s_k)² − N(s_k)·D″(s_k)/D′(s_k)³ ,

both computable from `D` alone.  The `D″` identity is where the linear factor pays off: the product
rule gives `D′ = E + (·−s_k)·E′`, and differentiating *that* at `s_k` needs no second derivative of
`E` — only its continuity, because the extra `(·−s_k)` factor kills the unwanted term
(`hasDerivAt_sub_mul_of_continuousAt`). -/

/-- A linear factor differentiates for free: `(·−s_k)·g` has derivative `g(s_k)` at `s_k` whenever
`g` is merely **continuous** there (no differentiability of `g` needed).  Immediate from the slope
characterization, since the difference quotient at `s_k` *is* `g`. -/
theorem hasDerivAt_sub_mul_of_continuousAt (g : ℂ → ℂ) (s_k : ℂ) (hg : ContinuousAt g s_k) :
    HasDerivAt (fun z => (z - s_k) * g z) (g s_k) s_k := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hg' : Tendsto g (𝓝[≠] s_k) (𝓝 (g s_k)) := hg.tendsto.mono_left nhdsWithin_le_nhds
  refine Tendsto.congr' ?_ hg'
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hzsk : z - s_k ≠ 0 := sub_ne_zero.mpr hz
  rw [slope_def_field]
  field_simp
  ring

/-- Product rule for the simple-zero factorization `D = (·−s_k)·E`: `D′(z) = E(z) + (z−s_k)·E′(z)`. -/
theorem factor_hasDerivAt (D E E' : ℂ → ℂ) (s_k : ℂ)
    (hfact : ∀ z, D z = (z - s_k) * E z) (hE : ∀ z, HasDerivAt E (E' z) z) (z : ℂ) :
    HasDerivAt D (E z + (z - s_k) * E' z) z := by
  have hbase : HasDerivAt (fun w => (w - s_k) * E w) (1 * E z + (z - s_k) * E' z) z :=
    ((hasDerivAt_id z).sub_const s_k).mul (hE z)
  rw [one_mul] at hbase
  exact hbase.congr_of_eventuallyEq (Filter.Eventually.of_forall hfact)

/-- `D′(s_k) = E(s_k)` — the value of the cofactor at the zero is the derivative of `D` there. -/
theorem factor_hasDerivAt_at_zero (D E E' : ℂ → ℂ) (s_k : ℂ)
    (hfact : ∀ z, D z = (z - s_k) * E z) (hE : ∀ z, HasDerivAt E (E' z) z) :
    HasDerivAt D (E s_k) s_k := by
  have h := factor_hasDerivAt D E E' s_k hfact hE s_k
  simpa using h

/-- `D″(s_k) = 2·E′(s_k)` — the second derivative of `D` at the simple zero.  Needs only
`ContinuousAt E'`, not a second derivative of `E`: the `(·−s_k)` factor in `D′ = E + (·−s_k)·E′`
supplies the missing differentiability (`hasDerivAt_sub_mul_of_continuousAt`). -/
theorem factor_second_hasDerivAt (D E E' : ℂ → ℂ) (s_k : ℂ)
    (hfact : ∀ z, D z = (z - s_k) * E z) (hE : ∀ z, HasDerivAt E (E' z) z)
    (hE'c : ContinuousAt E' s_k) :
    HasDerivAt (deriv D) (2 * E' s_k) s_k := by
  have hderiv : deriv D = fun z => E z + (z - s_k) * E' z := by
    funext z
    exact (factor_hasDerivAt D E E' s_k hfact hE z).deriv
  rw [hderiv, two_mul]
  exact (hE s_k).add (hasDerivAt_sub_mul_of_continuousAt E' s_k hE'c)

/-- **MML.8 term (II) — the order-1 coefficient `α_k`, cofactor-free.**  For a double pole `N/D²` at
a simple zero `s_k` of `D` (factorization `D = (·−s_k)·E` with `E` differentiable and `E′` continuous
at `s_k`), the two Laurent coefficients are

    β_k = N(s_k)/D′(s_k)²        (`double_pole_leading_coeff`)
    α_k = N′(s_k)/D′(s_k)² − N(s_k)·D″(s_k)/D′(s_k)³   (here),

with `D′ := Dprime` and `D″ := Dpp` the actual derivatives of `D` at `s_k`.  Restates
`double_pole_second_coeff` with the auxiliary cofactor `E` eliminated, which is what a concrete
consumer needs: for the mixture RDF, `D = det T₀ = det Q̂₀(k)·det Q̂₀(−k)`
(`det_eq_of_wienerHopf_factorization`) and only *its* derivatives are available. -/
theorem double_pole_second_coeff_deriv_form (N D E E' : ℂ → ℂ) (Nprime Dprime Dpp s_k : ℂ)
    (hfact : ∀ z, D z = (z - s_k) * E z)
    (hN : HasDerivAt N Nprime s_k)
    (hE : ∀ z, HasDerivAt E (E' z) z) (hE'c : ContinuousAt E' s_k)
    (hD : HasDerivAt D Dprime s_k) (hD2 : HasDerivAt (deriv D) Dpp s_k)
    (hDprime : Dprime ≠ 0) :
    Tendsto (fun z => (z - s_k) * (N z / (D z) ^ 2) - (N s_k / Dprime ^ 2) / (z - s_k))
      (𝓝[≠] s_k)
      (𝓝 (Nprime / Dprime ^ 2 - N s_k * Dpp / Dprime ^ 3)) := by
  -- identify the cofactor data with `D`'s own derivatives
  have hEval : E s_k = Dprime :=
    (factor_hasDerivAt_at_zero D E E' s_k hfact hE).unique hD
  have hEderiv : 2 * E' s_k = Dpp :=
    (factor_second_hasDerivAt D E E' s_k hfact hE hE'c).unique hD2
  have hEs : E s_k ≠ 0 := by rw [hEval]; exact hDprime
  have hbase := FMSA.MixtureHSPoles.double_pole_second_coeff N D E Nprime (E' s_k) s_k
    (Filter.Eventually.of_forall hfact) hN (hE s_k) hEs
  rw [hEval] at hbase
  have hlim : Nprime / Dprime ^ 2 - 2 * N s_k * E' s_k / Dprime ^ 3
      = Nprime / Dprime ^ 2 - N s_k * Dpp / Dprime ^ 3 := by
    rw [← hEderiv]; ring
  rwa [hlim] at hbase

/-! ### Term (II)'s coefficient factorizes as `HS residue × (finite Yukawa DCF) × HS residue`

`oz1_H1_eq` says the RDF's HS poles all come from the two `S₀` factors. This section turns that
into an identity between *numbers*: the order-2 Laurent coefficient `β_k` of the RDF is the
**structure factor's own residue matrix**, sandwiching the DCF evaluated at the pole,

    β_k = (R_k · Ĉ₁(s_k) · R_k) i j ,        R_k := det′T₀(s_k)⁻¹ • adj T₀(s_k) = Res_{s_k} S₀ .

`R_k` is built from `T₀ = I − Ĉ₀` alone — **no Yukawa data whatsoever** — while `Ĉ₁(s_k)` is a
plain evaluation of the finite, HS-pole-free (★) closed form (MRS.3/MRS.5). So term (II)'s
coefficients are *already* factored into "hard-sphere spectral data" × "closed-form Yukawa data",
which is what makes MML.8's residual collapse content a hard-sphere statement. -/

/-- The **residue matrix of the hard-sphere structure factor** at a simple zero `s_k` of `det T₀`:
`R_k = det′(s_k)⁻¹ • adj T₀(s_k)`.  Certified to be the actual residue of `S₀ = T₀⁻¹` by
`structureFactor_entry_residue`. -/
noncomputable def hsResidueMatrix {N : ℕ} (T0 : Matrix (Fin N) (Fin N) ℂ) (Dprime : ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  Dprime⁻¹ • T0.adjugate

/-- `Num/det′²` **is** the residue-matrix sandwich: `(adj·C·adj) i j / D′² = (R·C·R) i j` for
`R = D′⁻¹ • adj`.  Pure `smul` algebra. -/
theorem num_div_det_sq_eq_sandwich {N : ℕ} (T0 C1 : Matrix (Fin N) (Fin N) ℂ) (Dprime : ℂ)
    (i j : Fin N) :
    (T0.adjugate * C1 * T0.adjugate) i j / Dprime ^ 2
      = (hsResidueMatrix T0 Dprime * C1 * hsResidueMatrix T0 Dprime) i j := by
  unfold hsResidueMatrix
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul]
  rw [div_eq_mul_inv]
  ring

/-- **`R_k` is the structure factor's residue.**  At a simple zero `s_k` of `det T₀`, every entry of
`S₀(z) = T₀(z)⁻¹` has a *simple* pole with residue `hsResidueMatrix (T₀ s_k) D′ i j`.  (One `S₀`
factor ⇒ one pole; the RDF's two factors ⇒ the order-2 pole of `rdf_entry_double_pole`.)  Uses
`inv_apply_eq_adj_div_det` (Y1.1) + `residue_of_simple_pole`. -/
theorem structureFactor_entry_residue {N : ℕ} (T0f : ℂ → Matrix (Fin N) (Fin N) ℂ)
    (s_k Dprime : ℂ) (i j : Fin N)
    (hD : HasDerivAt (fun z => (T0f z).det) Dprime s_k)
    (hD0 : (T0f s_k).det = 0) (hDp : Dprime ≠ 0)
    (hadj : ContinuousAt (fun z => (T0f z).adjugate i j) s_k) :
    Tendsto (fun z => (z - s_k) * ((T0f z)⁻¹ i j)) (𝓝[≠] s_k)
      (𝓝 (hsResidueMatrix (T0f s_k) Dprime i j)) := by
  have hbase := FMSA.Analysis.residue_of_simple_pole
    (fun z => (T0f z).adjugate i j) (fun z => (T0f z).det) Dprime s_k hD hD0 hDp hadj
  have hval : (T0f s_k).adjugate i j / Dprime = hsResidueMatrix (T0f s_k) Dprime i j := by
    unfold hsResidueMatrix
    rw [Matrix.smul_apply, smul_eq_mul, div_eq_mul_inv]
    ring
  rw [hval] at hbase
  refine hbase.congr (fun z => ?_)
  rw [FMSA.Q0Complex.inv_apply_eq_adj_div_det]

/-- **MML.8 term (II), fully factored.**  The RDF's order-2 Laurent coefficient at a simple zero
`s_k` of `det T₀` is `β_k = (R_k · Ĉ₁(s_k) · R_k) i j` with `R_k = Res_{s_k} S₀` the hard-sphere
structure factor's residue matrix.  Combines `rdf_entry_double_pole` with
`num_div_det_sq_eq_sandwich`. -/
theorem rdf_double_pole_coeff_sandwich (T0f C1f : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (s_k Dprime : ℂ) (i j : Fin 2)
    (hD : HasDerivAt (fun z => (T0f z).det) Dprime s_k)
    (hD0 : (T0f s_k).det = 0) (hDp : Dprime ≠ 0)
    (hNum : ContinuousAt
      (fun z => ((T0f z).adjugate * C1f z * (T0f z).adjugate) i j) s_k) :
    Tendsto (fun z => (z - s_k) ^ 2 * (((T0f z)⁻¹ * C1f z * (T0f z)⁻¹) i j)) (𝓝[≠] s_k)
      (𝓝 ((hsResidueMatrix (T0f s_k) Dprime * C1f s_k
            * hsResidueMatrix (T0f s_k) Dprime) i j)) := by
  have h := rdf_entry_double_pole T0f C1f s_k Dprime i j hD hD0 hDp hNum
  rwa [num_div_det_sq_eq_sandwich (T0f s_k) (C1f s_k) Dprime i j] at h

/-- **The same, with the Yukawa side written out by (★).**  Substituting the finite, HS-pole-free
(★) form `Ĉ₁(s_k) = Q̂₀(−s_k)·B₁(s_k)·Q̂₀ᵀ(−s_k)` (MRS.3) exhibits term (II)'s coefficient as

    β_k = (R_k · Q̂₀(−s_k) · B₁(s_k) · Q̂₀ᵀ(−s_k) · R_k) i j ,

hard-sphere spectral data (`R_k`) on the outside, closed-form Yukawa data (`B₁`, `Q̂₀`) on the
inside — the separation `oz1_H1_eq` predicts, now as an equation between numbers. -/
theorem rdf_double_pole_coeff_star (T0f C1f : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (Qm B1 : Matrix (Fin 2) (Fin 2) ℂ) (s_k Dprime : ℂ) (i j : Fin 2)
    (hD : HasDerivAt (fun z => (T0f z).det) Dprime s_k)
    (hD0 : (T0f s_k).det = 0) (hDp : Dprime ≠ 0)
    (hNum : ContinuousAt
      (fun z => ((T0f z).adjugate * C1f z * (T0f z).adjugate) i j) s_k)
    (hstar : C1f s_k = Qm * B1 * Qmᵀ) :
    Tendsto (fun z => (z - s_k) ^ 2 * (((T0f z)⁻¹ * C1f z * (T0f z)⁻¹) i j)) (𝓝[≠] s_k)
      (𝓝 ((hsResidueMatrix (T0f s_k) Dprime * (Qm * B1 * Qmᵀ)
            * hsResidueMatrix (T0f s_k) Dprime) i j)) := by
  have h := rdf_double_pole_coeff_sandwich T0f C1f s_k Dprime i j hD hD0 hDp hNum
  rwa [hstar] at h

/-! ### The mixture collapse factor — matrix analog of the scalar `ρĈ(kₙ) = 1`

The scalar `hcollapse` (`OZFIX.11`) turns on one identity: at a Baxter pole `kₙ` the symbol satisfies
`ρĈ(kₙ) = 1`, i.e. `1 − ρĈ` vanishes there, which makes the forcing term drop out per pole. MML.8's
own scoping (Crux #2, item 1) names the mixture counterpart as its "first concrete sub-piece": the
`det(I − Ĉ_mix)(s_k) = 0` corollary of the matrix Wiener–Hopf factorization, **and the adjugate-level
version** that an entry-wise collapse needs. Both now land in two lines, because
`hsResidueMatrix` is built from the adjugate:

* `det T₀(s_k) = 0` at a `det Q̂₀` zero is `det_eq_of_wienerHopf_factorization` (MRS.6 supplies
  `T₀ = Q̂₀(k)·Q̂₀ᵀ(−k)`, and `T₀ = I − Ĉ₀` is that file's `Cmix0` definition);
* the adjugate-level statement is `hsResidue_annihilates` / `hsResidue_eq_mul_cmix` below.

`hsResidue_eq_mul_cmix` is the literal matrix transcription of `ρĈ(kₙ) = 1`: the residue matrix is a
**fixed point of multiplication by the hard-sphere DCF at the pole**, `R_k = R_k·Ĉ₀(s_k) = Ĉ₀(s_k)·R_k`.
Scalar case `N = 1`: `R_k` is a nonzero number, so it cancels and leaves `Ĉ₀(s_k) = 1`. -/

/-- **The collapse factor, adjugate level.**  At a zero of `det T₀` the structure factor's residue
matrix annihilates `T₀ = I − Ĉ₀` on both sides.  Immediate from `Matrix.adjugate_mul` /
`Matrix.mul_adjugate` (`adj A · A = A · adj A = det A • I`) at `det A = 0`. -/
theorem hsResidue_annihilates {N : ℕ} (T0 : Matrix (Fin N) (Fin N) ℂ) (Dprime : ℂ)
    (hdet : T0.det = 0) :
    hsResidueMatrix T0 Dprime * T0 = 0 ∧ T0 * hsResidueMatrix T0 Dprime = 0 := by
  unfold hsResidueMatrix
  constructor
  · rw [Matrix.smul_mul, Matrix.adjugate_mul, hdet, zero_smul, smul_zero]
  · rw [Matrix.mul_smul, Matrix.mul_adjugate, hdet, zero_smul, smul_zero]

/-- **The mixture collapse factor.**  With `T₀ = I − Ĉ₀`, the annihilation above reads
`R_k = R_k·Ĉ₀(s_k)` and `R_k = Ĉ₀(s_k)·R_k` — the residue matrix is a fixed point of multiplication
by the hard-sphere DCF at the pole.  This is the matrix transcription of the scalar collapse factor
`ρĈ(kₙ) = 1` that powers `OZFIX.11`, and the form an entry-wise mixture collapse consumes. -/
theorem hsResidue_eq_mul_cmix {N : ℕ} (C0 T0 : Matrix (Fin N) (Fin N) ℂ) (Dprime : ℂ)
    (hT : T0 = 1 - C0) (hdet : T0.det = 0) :
    hsResidueMatrix T0 Dprime = hsResidueMatrix T0 Dprime * C0 ∧
      hsResidueMatrix T0 Dprime = C0 * hsResidueMatrix T0 Dprime := by
  obtain ⟨hL, hR⟩ := hsResidue_annihilates T0 Dprime hdet
  constructor
  · have h1 : hsResidueMatrix T0 Dprime * T0
        = hsResidueMatrix T0 Dprime - hsResidueMatrix T0 Dprime * C0 := by
      rw [hT, Matrix.mul_sub, Matrix.mul_one]
    rw [hL] at h1
    exact sub_eq_zero.mp h1.symm
  · have h2 : T0 * hsResidueMatrix T0 Dprime
        = hsResidueMatrix T0 Dprime - C0 * hsResidueMatrix T0 Dprime := by
      rw [hT, Matrix.sub_mul, Matrix.one_mul]
    rw [hR] at h2
    exact sub_eq_zero.mp h2.symm

end FMSA.MixtureRDF
