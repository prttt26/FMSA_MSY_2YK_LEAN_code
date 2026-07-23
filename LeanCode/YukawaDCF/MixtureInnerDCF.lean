/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.YukawaDCF.MixtureMLSeries
import LeanCode.YukawaDCF.SpectralAmplitude
import LeanCode.FMSAPoly.EijStructure
import LeanCode.FMSAPoly.OriginConstraint

/-!
# Tasks MML.6 / MML.7 — Yukawa base term + origin constant (N=2 mixture)

Group MML (split of the retired MML.3). This file supplies two of the three ingredients of the
`(I)+(II)+(III)` assembly (the third, the HS-pole series, is MML.4/MML.5 in `MixtureMLSeries.lean`;
the assembly itself is MML.8).

## ⚠ Scope correction (2026-07-16): this is the **RDF** (`h₁`) assembly, not the DCF

The numerical session's **(★)** result (certified to 4.4×10⁻¹³) is
`Ĉ₁(k) = Q̂₀(−k)·B₁(k)·Q̂₀ᵀ(−k)` — obtained by equating [LN] eq:OZ1_Baxter with
`Hhat1_spec` (Y1.6) and solving for `Ĉ₁`.
**(★) contains no `Q̂₀⁻¹`**, and `Q̂₀` is entire, so the **DCF** `Ĉ₁` has **only
Yukawa poles**: the `det Q̂₀` zeros (Group MZERO) never enter it, and the inner DCF is a **finite
closed form**, piecewise at the `λ_ij` knots. The DCF route is **Group MRS**; the infinite HS-pole
sum premise is **refuted for the DCF**.

What survives here is the **RDF**: `Ĥ₁ = [Q̂₀ᵀ]⁻¹·B₁·[Q̂₀]⁻¹` *does* carry the inverses ⇒ genuine
(double) HS poles ⇒ a genuine Mittag-Leffler series. **The inverse factors are the DCF/RDF dividing
line.** Read MML.4–MML.8 (and MZERO, MML.5-concrete) as RDF-scoped.

## MML.6 — Yukawa doubly-propagated base term

Term (I) of the inner DCF, `Σ_t [Q̂₀(z_t)⁻¹·K_t·Q̂₀(z_t)⁻ᵀ]₀₁ · exp(z_t(R₀₁−r))`.

* `yukawaBaseAmp` — the doubly-propagated amplitude `[Ĝ·K·Ĝᵀ]₀₁` (`Ĝ = Q̂₀⁻¹`), index `(0,1)`.
* `yukawaBaseTerm` — the real-space base, `Σ_t amp_t · exp(z_t(R−r))`.
* `yukawaBaseAmp_eq_spectralAmp_residue` — **MML.6**: `yukawaBaseAmp` *is* the residue of the
  Y1.5 spectral amplitude `spectralAmp` at the Yukawa pole `s = −z` (`spectralAmp_residue`,
  `SpectralAmplitude.lean`), certifying it as the exact doubly-propagated leading residue. (The
  real-space `exp(z_t(R−r))` envelope — the inverse-Laplace step relating this residue to
  `yukawaBaseTerm` — is the assembly, MML.8.)

## MML.7 — origin constant `p₀`

The singularity-cancellation constant `p₀ = −(Yukawa base + HS-pole sum)|_{r→0}` that keeps
`c(r) = rc₁(r)/(…·r)` finite as `r→0` (`fmsa_hs_pole_residue.py` `_precompute_p0`).

* `origin_constant_mix` — **MML.7 (abstract)**: for any `base`, `hsum`, inner-polynomial `P`
  continuous at `0` with the `1/r` limit existing, `P 0 = −(base 0 + hsum 0)`. Instantiates the
  fully-generic `origin_necessity` (P.2, `OriginConstraint.lean`) with `E := base + hsum`.
* `origin_constant_eij_mix` — the Yukawa specialization with `base := eij` (its continuity via
  `fun_prop`, as in Y1.7): `P 0 = −(Σ_k A_k·exp(−z_k R) + hsum 0)` — exactly `_precompute_p0`'s
  `−(E_ij(0) + Σ_k 2·Re[B_k])` form (with `hsum := mixHS_series` at `r=0`, whose continuity-at-0 is
  the one deferred ingredient).

## MML.8 — term (II) in the doubly-propagated RDF form + the collapse reduction target

The surviving RDF term (II) is the **double-pole** envelope `(α_k + β_k·r)·e^{−s_k r}`, not the
*singly* simple-exponential `mixHS_series` that `(★)`/Group MRS refuted for the DCF. **Both Laurent
coefficients are now certified:** `double_pole_leading_coeff` gives the order-2
`β_k = N(s_k)/D′(s_k)²` (the `r`-prefactor), and `double_pole_reg_hasDerivAt` /
`double_pole_second_coeff` give the order-1
`α_k = N′/E(s_k)² − 2·N(s_k)·E′/E(s_k)³` (via the simple-zero factorization `D = (·−s_k)·E`,
`E(s_k)=D′(s_k)`), so the real-space term (II) is fully pinned by the pole data.

* `double_pole_reg_hasDerivAt` / `double_pole_reg_eventuallyEq` / `double_pole_second_coeff` — the
  order-1 coefficient `α_k` as the derivative of the regularization `N/E²` (which `= (·−s_k)²·N/D²`
  near `s_k`), i.e. `α_k` as the simple-pole residue coefficient.
* `mixHSterm2` / `mixHS_series2` — term (II) in doubly form; `mixHSterm2_eq` / `mixHS_series2_eq`
  identify them (definitionally) with the singly `mixHSterm`/`mixHS_series` at the `r`-absorbed
  coefficient `α_k + β_k·r`, so all summability API transfers.
* `mixHS_series2_summable` — convergence from the MML.5-concrete growth bounds (non-vacuity).
* `mixRDFInnerAssembly`, `MixRDFInnerCollapse` — the `(I)+(II)+(III)` assembly and the collapse
  `Prop` (the reduction target; matrix analog of `CoreSeriesClosure`, OZFIX.12). Deliberately not an
  axiom (sub-family trap); the bridge `assembly = r·h₁` awaits matrix `oz_fixed_pt_unique` + matrix
  OZ★ (Group MRS), per the OZFIX.22 template.

Status: ✓ DONE (MML.6, MML.7), axiom-clean. MML.8: term-(II) doubly form + collapse reduction target
done axiom-clean; the collapse itself (the bridge) awaits the matrix real-space infrastructure.
-/

set_option linter.style.longLine false

open Filter Topology
open scoped Matrix

open FMSA.PoleSeries

namespace FMSA.MixtureHSPoles

/-! ### MML.6 — the Yukawa doubly-propagated base term -/

/-- **MML.6 — the doubly-propagated Yukawa amplitude** `[Ĝ·K·Ĝᵀ]₀₁` with `Ĝ = Q̂₀(z)⁻¹`.
This is the exact leading Yukawa-pole residue ([LN] Eq. 73; Y1.5).

**NB — this is the RDF (`h₁`) amplitude, NOT the DCF base** (2026-07-16, `(★)`). `Ĥ₁ =
[Q̂₀ᵀ]⁻¹·B₁·[Q̂₀]⁻¹` genuinely carries the inverses, so at an HS pole this gives a *double* pole
(`doubly_prop_entry_eq` + `double_pole_leading_coeff`), hence `r·e^{−s_k r}` terms. The **DCF**
`Ĉ₁(k) = Q̂₀(−k)·B₁(k)·Q̂₀ᵀ(−k)` **(★)** contains **no `Q̂₀⁻¹` at all** ⇒ only Yukawa poles, no HS
poles, and a *finite* closed form — see Group MRS. So this amplitude is load-bearing for the RDF
only. (An earlier version of this docstring claimed the DCF base was the *singly*-propagated
`K·[Q̂₀⁻¹]₀₁`; that is **refuted** by (★) — the DCF has no inverse factor whatsoever.) -/
noncomputable def yukawaBaseAmp (Kmat Gmat : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  ((Gmat * Kmat * Gmatᵀ : Matrix (Fin 2) (Fin 2) ℂ) 0 1)

/-- **MML.6 — the real-space Yukawa base** `Σ_{t<nt} amp_t · exp(z_t(R−r))` (term (I)). -/
noncomputable def yukawaBaseTerm (amp : ℕ → ℂ) (z : ℕ → ℝ) (R r : ℝ) (nt : ℕ) : ℂ :=
  ∑ t ∈ Finset.range nt, amp t * Complex.exp ((z t : ℂ) * ((R : ℂ) - (r : ℂ)))

/-- **MML.6 — the base amplitude is the doubly-propagated residue.**  `yukawaBaseAmp Kmat Gmat`
is exactly the residue at the Yukawa pole `s = −z` of the Y1.5 spectral amplitude
`spectralAmp Kmat Gmat z · 0 1`.  Direct reuse of `spectralAmp_residue`. -/
theorem yukawaBaseAmp_eq_spectralAmp_residue (Kmat Gmat : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ) :
    Tendsto (fun s => (s - (-z)) * FMSA.SpectralAmplitude.spectralAmp Kmat Gmat z s 0 1)
      (𝓝[≠] (-z)) (𝓝 (yukawaBaseAmp Kmat Gmat)) := by
  unfold yukawaBaseAmp
  exact FMSA.SpectralAmplitude.spectralAmp_residue Kmat Gmat z 0 1

/-! ### MML.7 — the origin (singularity-cancellation) constant `p₀` -/

/-- **MML.7 (abstract) — origin constant.**  For a base `base`, HS-pole sum `hsum`, and inner
polynomial `P`, all continuous at `0`, if `(base + hsum + P)/r` has a finite limit as `r→0` (i.e.
the `1/r` singularity of `c` cancels) then the inner-polynomial constant is forced:
`P 0 = −(base 0 + hsum 0)`.  Instantiates P.2's fully-generic `origin_necessity` with the bundled
`E := base + hsum`. -/
theorem origin_constant_mix (base hsum P : ℝ → ℝ)
    (hcBase : ContinuousAt base 0) (hcSum : ContinuousAt hsum 0) (hcP : ContinuousAt P 0)
    {L : ℝ}
    (hL : Tendsto (fun r => (base r + hsum r + P r) / r) (𝓝[≠] (0 : ℝ)) (𝓝 L)) :
    P 0 = -(base 0 + hsum 0) := by
  have hE : ContinuousAt (fun r => base r + hsum r) 0 := hcBase.add hcSum
  have h : base 0 + hsum 0 + P 0 = 0 :=
    FMSA.OriginConstraint.origin_necessity (fun r => base r + hsum r) P hE hcP hL
  linarith [h]

/-- **MML.7 — Yukawa specialization.**  With `base := eij Amp z R` (the Yukawa base, whose
continuity at `0` is automatic), the origin constant is
`P 0 = −(Σ_k A_k·exp(−z_k R) + hsum 0)` — exactly `fmsa_hs_pole_residue.py` `_precompute_p0`'s
`−(E_ij(0) + Σ_k 2·Re[B_k])` (with `hsum` the HS-pole sum at `r=0`). Mirrors Y1.7's
`origin_constraint_eq76`, adding the HS-pole sum term. -/
theorem origin_constant_eij_mix {n : ℕ} (Amp z : Fin n → ℝ) (R : ℝ) (hsum P : ℝ → ℝ)
    (hcSum : ContinuousAt hsum 0) (hcP : ContinuousAt P 0) {L : ℝ}
    (hL : Tendsto (fun r => (FMSA.EijStructure.eij Amp z R r + hsum r + P r) / r)
      (𝓝[≠] (0 : ℝ)) (𝓝 L)) :
    P 0 = -((∑ k : Fin n, Amp k * Real.exp (-(z k) * R)) + hsum 0) := by
  have hcBase : ContinuousAt (FMSA.EijStructure.eij Amp z R) 0 := by
    unfold FMSA.EijStructure.eij
    fun_prop
  have h := origin_constant_mix (FMSA.EijStructure.eij Amp z R) hsum P hcBase hcSum hcP hL
  rwa [FMSA.EijStructure.eij_at_origin] at h

/-! ### MML.8 (Crux #1) — pole order: how many `Q̂₀⁻¹` factors, and hence what the HS terms look like

**Scope (2026-07-16): this is about the RDF `h₁`, not the DCF.** The DCF premise was refuted by
**(★)** `Ĉ₁(k) = Q̂₀(−k)·B₁(k)·Q̂₀ᵀ(−k)` (numerically certified to 4.4×10⁻¹³): (★) carries **no
`Q̂₀⁻¹`**, and `Q̂₀` is entire, so `Ĉ₁` has **only Yukawa poles** — the `det Q̂₀` zeros never enter the
DCF, and the inner DCF is a *finite* closed form, piecewise at the `λ_ij` knots (Group MRS). Any
HS-pole term-(II) sum is therefore an **RDF-only** object. The lemmas below stay valid for `h₁`.

**The content.** A term-(II) form `Σ_k 2·Re[B_k·e^{−s_k r}]` (clean exponentials) presupposes
*simple* HS poles, i.e. **one** `Q̂₀⁻¹` factor (`[Q̂₀⁻¹]₀₁ = −Q̂₀₀₁/det`, MML.2 `b_k_residue`). But the
RDF's **doubly**-propagated `[Q̂₀⁻¹·K·Q̂₀⁻ᵀ]₀₁ = (adj·K·adjᵀ)₀₁/det²` (since `Q̂₀⁻¹ = adj/det`) has a
**double** pole, whose inverse-Laplace weight carries an `r`-prefactor: `(α_k + β_k r)·e^{−s_k r}`.
The lemmas make this rigorous: any `N/D²` with `D` a simple zero is a genuine order-2 pole with
leading Laurent coefficient `N(s_k)/det′(s_k)²` (= `to_python.md` option (a)'s `B_k^{new}`).

**Upshot — the number of inverse factors is the DCF/RDF dividing line:** none ⇒ DCF (★, finite closed
form, Group MRS); two ⇒ RDF `h₁` (double HS poles, `(α+βr)e^{−s_k r}`). The "singly-propagated"
reading has **no** object: an earlier note here recommended it for the DCF, which (★) refutes. -/

/-- **The doubly-propagated entry is `N/det²`.**  `[M⁻¹·K·(M⁻¹)ᵀ]₀₁ = (adj·K·adjᵀ)₀₁ / det²`,
since `M⁻¹ = det⁻¹ • adj` (`Matrix.inv_def`) contributes two `det⁻¹` factors. So the doubly-propagated
amplitude `[Q̂₀⁻¹·K·Q̂₀⁻ᵀ]₀₁` (`yukawaBaseAmp` at `Gmat = Q̂₀⁻¹`) is literally of the `N/det²` form
`double_pole_leading_coeff` analyses — a **double** pole at each HS zero `s_k` of `det`. -/
theorem doubly_prop_entry_eq (M K : Matrix (Fin 2) (Fin 2) ℂ) :
    (M⁻¹ * K * (M⁻¹)ᵀ) 0 1 = (M.adjugate * K * (M.adjugate)ᵀ) 0 1 / (M.det) ^ 2 := by
  have hinv : M⁻¹ = (M.det)⁻¹ • M.adjugate := by rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [hinv, Matrix.transpose_smul]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.smul_apply, smul_eq_mul]
  rw [div_eq_mul_inv]
  ring

/-- **General double-pole leading coefficient.**  If `D` has a simple zero at `s_k`
(`HasDerivAt D Dprime s_k`, `D s_k = 0`, `Dprime ≠ 0`) and `N` is continuous at `s_k`, then `N/D²`
has an order-2 pole with leading Laurent coefficient `N(s_k)/Dprime²`:
`(z − s_k)²·(N z/(D z)²) → N(s_k)/Dprime²`.  Reuses `residue_of_simple_pole` (with `N ≡ 1`) for
`(z−s_k)/D → 1/Dprime`, squared (`Tendsto.pow`) and scaled by the continuous `N`. -/
theorem double_pole_leading_coeff (N D : ℂ → ℂ) (Dprime s_k : ℂ)
    (hD : HasDerivAt D Dprime s_k) (hDz0 : D s_k = 0) (hDprime : Dprime ≠ 0)
    (hNcont : ContinuousAt N s_k) :
    Tendsto (fun z => (z - s_k) ^ 2 * (N z / (D z) ^ 2)) (𝓝[≠] s_k)
      (𝓝 (N s_k / Dprime ^ 2)) := by
  have h1 : Tendsto (fun z => (z - s_k) * (1 / D z)) (𝓝[≠] s_k) (𝓝 (1 / Dprime)) := by
    have := FMSA.HardSphere.residue_of_simple_pole (fun _ => (1 : ℂ)) D Dprime s_k hD hDz0 hDprime
      continuousAt_const
    simpa using this
  have h2 : Tendsto (fun z => ((z - s_k) * (1 / D z)) ^ 2) (𝓝[≠] s_k) (𝓝 ((1 / Dprime) ^ 2)) :=
    h1.pow 2
  have hN : Tendsto N (𝓝[≠] s_k) (𝓝 (N s_k)) := hNcont.tendsto.mono_left nhdsWithin_le_nhds
  have hprod := hN.mul h2
  have heq : ∀ z, N z * ((z - s_k) * (1 / D z)) ^ 2 = (z - s_k) ^ 2 * (N z / (D z) ^ 2) :=
    fun z => by ring
  rw [show N s_k / Dprime ^ 2 = N s_k * (1 / Dprime) ^ 2 from by ring]
  exact hprod.congr heq

/-- **The doubly-propagated pole is genuinely order 2** (nonzero leading coefficient) whenever the
numerator does not vanish at the pole — so its inverse-Laplace weight carries the `r`-prefactor
(`r·e^{−s_k r}`) that the stated simple-exponential term (II) lacks. -/
theorem double_pole_leading_coeff_ne_zero (N Dprime s_k : ℂ) (hDprime : Dprime ≠ 0)
    (hN : N ≠ 0) : N / Dprime ^ 2 ≠ 0 :=
  div_ne_zero hN (pow_ne_zero 2 hDprime)

/-! ### MML.8 — the order-1 (simple-pole) Laurent coefficient `α_k` of the double pole

`double_pole_leading_coeff` gives the order-2 coefficient `A = N(s_k)/D′(s_k)²` (the `β_k`
`r`-prefactor). A double pole's principal part is `A/(z−s_k)² + B/(z−s_k)`, so the real-space term
(II) `(β_k + α_k/…)` needs the **order-1** coefficient `B = α_k` too. Working from the analytic
factorization `D = (·−s_k)·E` of the simple zero (`E` differentiable, `E(s_k) ≠ 0` — exactly the
shape Mathlib's `AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff` gives for an analytic `D` such
as `det Q̂₀`, with `E(s_k) = D′(s_k)`), the regularization `(z−s_k)²·(N/D²)` extends to `reg := N/E²`,
which is genuinely differentiable at `s_k`; its value is `A` and its derivative is `α_k`. This avoids
the (unavailable over `ℂ`) L'Hôpital / 2nd-order-Taylor machinery. -/

/-- **`reg := N/E²` has derivative `α_k = N′/E(s_k)² − 2·N(s_k)·E′/E(s_k)³` at `s_k`** — the order-1
Laurent coefficient of the double pole `N/D²` (via the factorization `D = (·−s_k)·E`, so
`reg = (·−s_k)²·(N/D²)` extended). Pure quotient-rule calculus. -/
theorem double_pole_reg_hasDerivAt (N E : ℂ → ℂ) (Nprime Eprime s_k : ℂ)
    (hN : HasDerivAt N Nprime s_k) (hE : HasDerivAt E Eprime s_k) (hEs : E s_k ≠ 0) :
    HasDerivAt (fun z => N z / (E z) ^ 2)
      (Nprime / (E s_k) ^ 2 - 2 * N s_k * Eprime / (E s_k) ^ 3) s_k := by
  have hE2 : HasDerivAt (fun z => E z ^ 2) (2 * E s_k * Eprime) s_k := by
    have h := hE.mul hE
    rw [show (2 * E s_k * Eprime) = Eprime * E s_k + E s_k * Eprime from by ring,
        show (fun z => E z ^ 2) = (fun z => E z * E z) from by ext z; rw [pow_two]]
    exact h
  have hden : (E s_k) ^ 2 ≠ 0 := pow_ne_zero 2 hEs
  have hdiv : HasDerivAt (fun z => N z / (E z) ^ 2)
      ((Nprime * (E s_k) ^ 2 - N s_k * (2 * E s_k * Eprime)) / ((E s_k) ^ 2) ^ 2) s_k :=
    hN.div hE2 hden
  rw [show (Nprime * (E s_k) ^ 2 - N s_k * (2 * E s_k * Eprime)) / ((E s_k) ^ 2) ^ 2
      = Nprime / (E s_k) ^ 2 - 2 * N s_k * Eprime / (E s_k) ^ 3 from by field_simp] at hdiv
  exact hdiv

/-- The regularization `(z−s_k)²·(N/D²)` equals `reg = N/E²` on a punctured neighbourhood of `s_k`,
via the factorization `D = (·−s_k)·E` (and `E ≠ 0` near `s_k`). So `reg` is the analytic extension
whose value/derivative at `s_k` are the double pole's two Laurent coefficients. -/
theorem double_pole_reg_eventuallyEq (N D E : ℂ → ℂ) (s_k : ℂ)
    (hfact : ∀ᶠ z in nhds s_k, D z = (z - s_k) * E z)
    (hE : ContinuousAt E s_k) (hEs : E s_k ≠ 0) :
    (fun z => (z - s_k) ^ 2 * (N z / (D z) ^ 2))
      =ᶠ[nhdsWithin s_k {s_k}ᶜ] (fun z => N z / (E z) ^ 2) := by
  have hEne : ∀ᶠ z in nhds s_k, E z ≠ 0 := hE.eventually_ne hEs
  have hfact' : ∀ᶠ z in nhdsWithin s_k {s_k}ᶜ, D z = (z - s_k) * E z :=
    hfact.filter_mono nhdsWithin_le_nhds
  have hEne' : ∀ᶠ z in nhdsWithin s_k {s_k}ᶜ, E z ≠ 0 := hEne.filter_mono nhdsWithin_le_nhds
  have hne : ∀ᶠ z in nhdsWithin s_k {s_k}ᶜ, z ≠ s_k := by
    filter_upwards [self_mem_nhdsWithin] with z hz using hz
  filter_upwards [hfact', hEne', hne] with z hz hEz hzne
  have hzsk : z - s_k ≠ 0 := sub_ne_zero.mpr hzne
  rw [hz]; field_simp

/-- **MML.8 — `α_k` as the order-1 residue coefficient** (companion to `double_pole_leading_coeff`).
`(z−s_k)·(N/D²) − A/(z−s_k) → α_k` as `z → s_k`, with `A = N(s_k)/E(s_k)²` the order-2 coefficient and
`α_k = N′/E(s_k)² − 2·N(s_k)·E′/E(s_k)³`.  Content: the double pole's simple-pole part.  Proof:
`α_k = reg′(s_k)` (`double_pole_reg_hasDerivAt`) read through the slope characterization, with the
slope rewritten to `(z−s_k)·f − A/(z−s_k)` via `double_pole_reg_eventuallyEq`. -/
theorem double_pole_second_coeff (N D E : ℂ → ℂ) (Nprime Eprime s_k : ℂ)
    (hfact : ∀ᶠ z in nhds s_k, D z = (z - s_k) * E z)
    (hN : HasDerivAt N Nprime s_k) (hE : HasDerivAt E Eprime s_k) (hEs : E s_k ≠ 0) :
    Tendsto (fun z => (z - s_k) * (N z / (D z) ^ 2) - (N s_k / (E s_k) ^ 2) / (z - s_k))
      (nhdsWithin s_k {s_k}ᶜ)
      (nhds (Nprime / (E s_k) ^ 2 - 2 * N s_k * Eprime / (E s_k) ^ 3)) := by
  have hreg := double_pole_reg_hasDerivAt N E Nprime Eprime s_k hN hE hEs
  have hslope := hasDerivAt_iff_tendsto_slope.mp hreg
  have heq := double_pole_reg_eventuallyEq N D E s_k hfact hE.continuousAt hEs
  refine Tendsto.congr' ?_ hslope
  have hne : ∀ᶠ z in nhdsWithin s_k {s_k}ᶜ, z ≠ s_k := by
    filter_upwards [self_mem_nhdsWithin] with z hz using hz
  filter_upwards [heq, hne] with z hzeq hzne
  have hzsk : z - s_k ≠ 0 := sub_ne_zero.mpr hzne
  rw [slope_def_field, ← hzeq]
  field_simp

/-! ### MML.8 — term (II) in the doubly-propagated RDF form, and the collapse reduction target

Crux #1 (`double_pole_leading_coeff`) proved the RDF `h₁ = [Q̂₀ᵀ]⁻¹·B₁·[Q̂₀]⁻¹` has **double** HS
poles (the two inverse factors give an `N/det²` entry, `doubly_prop_entry_eq`). So — unlike the
*singly*-propagated DCF reading, whose term (II) is the simple-exponential `mixHS_series`
(`MixtureMLSeries.lean`) and which `(★)`/Group MRS refuted for the DCF — the surviving **RDF** term
(II) is the **double-pole envelope** `(α_k + β_k·r)·e^{−s_k r}`, with the `r`-prefactor `β_k` the
order-2 leading Laurent coefficient `N(s_k)/det′(s_k)²` that `double_pole_leading_coeff` computes and
`α_k` the simple-pole part.

This section makes that RDF term (II) precise, wires its convergence to the (now DONE)
MML.5-concrete growth machinery, and records the full collapse as a `Prop` reduction target — the
N=2 matrix analog of the scalar `CoreSeriesClosure` (`OzCollapseInner.lean`, OZFIX.12) and, per the
OZFIX.22 template, the single clean input MML.8 reduces to once the matrix real-space infrastructure
(matrix `oz_fixed_pt_unique` + matrix OZ★, Group MRS) supplies the bridge `assembly = r·h₁`. -/

/-- **MML.8 — term (II), doubly-propagated (RDF) form.** The double-pole real-space HS term
`(α_k + β_k·r)·exp(−s_k·r)`. The `r`-prefactor `β_k` is the order-2 leading Laurent coefficient
(`double_pole_leading_coeff`); `α_k` is the simple-pole part. It is definitionally the *singly*
`mixHSterm` with the `r`-absorbed coefficient `α_k + β_k·r` (`mixHSterm2_eq`), so it inherits all of
`mixHSterm`'s summability API. -/
noncomputable def mixHSterm2 (alpha beta sfam : ℕ → ℂ) (r : ℝ) (n : ℕ) : ℂ :=
  (alpha n + beta n * (r : ℂ)) * Complex.exp (-(sfam n) * (r : ℂ))

/-- The doubly-propagated term is the singly `mixHSterm` with the `r`-absorbed coefficient
`α_k + β_k·r` (definitional). -/
theorem mixHSterm2_eq (alpha beta sfam : ℕ → ℂ) (r : ℝ) (n : ℕ) :
    mixHSterm2 alpha beta sfam r n
      = mixHSterm (fun m => alpha m + beta m * (r : ℂ)) sfam r n := rfl

/-- **MML.8 — term (II) series, doubly-propagated (RDF) form** `Σ_k 2·Re[(α_k + β_k·r)·e^{−s_k r}]`.
This is the surviving RDF term (II); the singly `mixHS_series` was the refuted DCF reading. -/
noncomputable def mixHS_series2 (alpha beta sfam : ℕ → ℂ) (r : ℝ) : ℝ :=
  2 * (∑' n : ℕ, mixHSterm2 alpha beta sfam r n).re

/-- The doubly series is the singly `mixHS_series` at the `r`-absorbed coefficient (definitional). -/
theorem mixHS_series2_eq (alpha beta sfam : ℕ → ℂ) (r : ℝ) :
    mixHS_series2 alpha beta sfam r
      = mixHS_series (fun m => alpha m + beta m * (r : ℂ)) sfam r := rfl

/-- **MML.8 — summability of the doubly-propagated term (II).** Same growth-bound hypotheses as
`mixHS_summable_of_growth` (the shape MML.5-concrete's `detF_family_magnitude_bound` produces): the
exponential `e^{−r·Re s_k}` dominates the polynomial growth of the coefficient `α_k + β_k·r`, so the
`r`-prefactor costs nothing. Establishes that `mixHS_series2` is a genuine convergent sum, i.e. the
collapse predicate below is non-vacuous (cf. `coreSeriesClosure_summand_summable`, OZFIX.12). -/
theorem mixHS_series2_summable {alpha beta sfam : ℕ → ℂ} {r : ℝ} {C p c d : ℝ}
    (hp : p < -1) (hC : 0 ≤ C) (hc : 0 < c) (hd : 0 < d)
    (hgrowth : ∀ n : ℕ, c * (n : ℝ) + d ≤ ‖sfam n‖)
    (hbound : ∀ n : ℕ, ‖mixHSterm2 alpha beta sfam r n‖ ≤ C * ‖sfam n‖ ^ p) :
    Summable (mixHSterm2 alpha beta sfam r) := by
  have hb' : ∀ n : ℕ,
      ‖mixHSterm (fun m => alpha m + beta m * (r : ℂ)) sfam r n‖ ≤ C * ‖sfam n‖ ^ p := by
    intro n; rw [← mixHSterm2_eq]; exact hbound n
  have hsum := mixHS_summable_of_growth (Bcoef := fun m => alpha m + beta m * (r : ℂ))
    (sfam := sfam) (r := r) hp hC hc hd hgrowth hb'
  exact hsum.congr (fun n => (mixHSterm2_eq alpha beta sfam r n).symm)

/-- **MML.8 — the doubly-propagated (RDF) inner assembly** `(I) base + (II) doubly HS series + (III)
p₀`.  `base` is the Yukawa doubly-propagated base (`yukawaBaseTerm`, MML.6, summed over tails, real
part); `p0` is the origin constant (`origin_constant_mix`, MML.7). This is the candidate for
`r·h₁_{01}(r)`. -/
noncomputable def mixRDFInnerAssembly
    (base : ℝ → ℝ) (alpha beta sfam : ℕ → ℂ) (p0 : ℝ) (r : ℝ) : ℝ :=
  base r + mixHS_series2 alpha beta sfam r + p0

/-- **MML.8 — the collapse predicate (the reduction target).** `MixRDFInnerCollapse` says the
doubly-propagated assembly `(I)+(II)+(III)` reproduces the true RDF `r·h₁_{01}(r)` on `(0, Rij)`. It
is the N=2 matrix analog of the scalar `CoreSeriesClosure` (`OzCollapseInner.lean`, OZFIX.12), and —
per the OZFIX.22 template — the single clean input MML.8 reduces to once the matrix real-space
infrastructure (matrix `oz_fixed_pt_unique` + matrix OZ★, Group MRS) supplies the bridge
`assembly = r·h₁`.

**⚠ Deliberately a `Prop`, NOT an axiom** (same discipline as `CoreSeriesClosure`): the residue
family `(α, β, sfam)` is constrained only to be *some* growth-family of HS poles, and sub-families
would satisfy any naive series-value axiom while summing to the wrong value (the verified
sub-family trap of OZFIX.12/MA.5/MA.2). An axiom form would need a completeness bundle — exhaustion
of the `det Q̂₀` zeros up to mirror pairing — which `MZERO.1` (infinitude) does **not** supply. Held
as a *hypothesis*, it is discharged only by a family that genuinely enumerates the poles;
`mixHS_series2_summable` shows its term (II) is a convergent (non-vacuous) sum. -/
def MixRDFInnerCollapse
    (base : ℝ → ℝ) (alpha beta sfam : ℕ → ℂ) (p0 Rij : ℝ) (h1true : ℝ → ℝ) : Prop :=
  ∀ r, 0 < r → r < Rij → mixRDFInnerAssembly base alpha beta sfam p0 r = r * h1true r

end FMSA.MixtureHSPoles
