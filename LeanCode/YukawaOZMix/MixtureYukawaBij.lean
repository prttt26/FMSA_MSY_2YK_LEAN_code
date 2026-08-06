/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import LeanCode.YukawaOZ.MixtureYukawaResidue

/-!
# The eq (23) residue coefficients `bᵢⱼ(s)` of `B₁` (Tang & Lu)

`B₁(k)` — the numerator of the first-order mixture RDF `Ĥ₁ = [Q̂₀ᵀ]⁻¹B₁[Q̂₀]⁻¹` (eq 15) — is the
residue, at the Yukawa poles of `U₁`, of the eq (20) integrand.  `MixtureYukawaResidue` computes the
per-pole residue mechanism `Res_{y=iz}[g(y)/((y−k)(iy+z))] = −g(iz)/(ik+z)`; assembling it over the
four term-types of the expanded integrand `E(I+A)U₁(I+Aᵀ)E` gives Tang & Lu's closed form (eq 23)

`bᵢⱼ(s) = Kᵢⱼ/(s+zᵢⱼ) + ∑ₙ Kᵢₙ Aⱼₙ(zᵢₙ)/(s+zᵢₙ) + ∑ₘ Kₘⱼ Aᵢₘ(zₘⱼ)/(s+zₘⱼ)
           + ∑ₘₙ Kₘₙ Aᵢₘ(zₘₙ)Aⱼₙ(zₘₙ)/(s+zₘₙ)`,

`{B₁(k)}ᵢⱼ = bᵢⱼ(ik)·e^{−ikRᵢⱼ}`, with `K` the Yukawa amplitudes and `A(z)` the propagators.

* **`bij_eq23`** — the general eq (23) coefficient (pair-specific decays `z_{αβ}`);
* **`bij_eqz`** — its equal-decay specialization (a single `z`, the Tables 1–2 regime), with
  **`bij_eq23_const`** identifying it with `bij_eq23` at a constant `zmat`/propagator;
* **`bij_eqz_matrix`** — the four equal-`z` sums collapse to `bᵢⱼ(s) = {(I+A)K(I+A)ᵀ}ᵢⱼ/(s+z)`,
  whose numerator is exactly the propagator-dressed amplitude `(I+A)K(I+A)ᵀ` (`N` of the contact
  benchmark `benchmark_tanglu_contact.py`);
* **`bij_eqz_residue`** — the **residue value** at the simple pole `s = −z`:
  `(s+z)·bᵢⱼ(s) = {(I+A)K(I+A)ᵀ}ᵢⱼ`;
* **`bij_eq23_contact`** / **`bij_eqz_contact`** — Tang & Lu eq (24), the **contact value**
  `lim_{s→∞} s·bᵢⱼ(s) = 2π√(ρᵢρⱼ)Rᵢⱼ·g¹ᵢⱼ(Rᵢⱼ)`: each Yukawa factor `s/(s+z_{αβ}) → 1`, so the limit
  is the sum of the four eq (23) residue amplitudes (equal-`z`: `{(I+A)K(I+A)ᵀ}ᵢⱼ`, benchmark `N`);
* **`g1Contact`** / **`g1Contact_eqz`** — the **first-order contact RDF `g¹ᵢⱼ(Rᵢⱼ)`** itself,
  eq (24) solved through: the contact value divided by the prefactor `contactPre = 2π√(ρᵢρⱼ)Rᵢⱼ`.
  **`g1Contact_limit`** / **`g1Contact_eqz_limit`** exhibit it as the limit of
  `s·bᵢⱼ(s)/(2π√(ρᵢρⱼ)Rᵢⱼ)`, and **`g1Contact_eqz_spec`** is eq (24) as written
  (`2π√(ρᵢρⱼ)Rᵢⱼ·g¹ᵢⱼ = {(I+A)K(I+A)ᵀ}ᵢⱼ`).

`K` and `A` are the data inputs: `K` = the Yukawa residue amplitudes (`YukawaPoleResidue`), and the
propagator entries `A(z)` are the explicit Appendix amplitudes `2π√(ρᵢρⱼ)Wtl/(Δ detTL)` supplied by
`Q0ComplexH1Assembly.AmatC_entry`.  This makes `Ĥ₁`'s numerator `B₁` explicit, completing the
momentum-side data alongside the eq (15)/(21) assembly.  All axiom-clean (`propext`,
`Classical.choice`, `Quot.sound`).
-/

open Filter Topology Matrix

namespace FMSA.MixtureRDF

/-- **Tang & Lu eq (23), general form.**  The residue coefficient `bᵢⱼ(s)` of `{B₁(s)}ᵢⱼ`, one
term per residue-programme pole type: the diagonal Yukawa amplitude `Kᵢⱼ`, the two single
propagator-dressings `∑ Kᵢₙ Aⱼₙ(zᵢₙ)` / `∑ Kₘⱼ Aᵢₘ(zₘⱼ)`, and the double dressing
`∑ₘₙ Kₘₙ Aᵢₘ(zₘₙ) Aⱼₙ(zₘₙ)`, each over its own Yukawa denominator `s + z_{αβ}`.  `K` = the Yukawa
amplitudes, `Aprop z` = the propagator amplitudes `A(z)` evaluated at the pair's decay, `zmat` = the
pair-specific decays `z_{αβ}`. -/
noncomputable def bij_eq23 {N : ℕ} (K : Matrix (Fin N) (Fin N) ℂ)
    (Aprop : ℂ → Matrix (Fin N) (Fin N) ℂ) (zmat : Fin N → Fin N → ℂ) (i j : Fin N) (s : ℂ) : ℂ :=
  K i j / (s + zmat i j)
  + (∑ n, K i n * Aprop (zmat i n) j n / (s + zmat i n))
  + (∑ m, K m j * Aprop (zmat m j) i m / (s + zmat m j))
  + ∑ m, ∑ n, K m n * Aprop (zmat m n) i m * Aprop (zmat m n) j n / (s + zmat m n)

/-- **Tang & Lu eq (23), equal Yukawa decay `z`.**  The residue coefficient `bᵢⱼ(s)`: with a single
`z` for all pairs, the four eq (23) sums (Kᵢⱼ, `∑ₙ Kᵢₙ Ajn`, `∑ₘ Kₘⱼ Aᵢₘ`, `∑ₘₙ Kₘₙ Aᵢₘ Ajn`)
share the denominator `s + z`.  `K` = the Yukawa amplitudes, `A` = the propagator matrix `A(z)`. -/
noncomputable def bij_eqz {N : ℕ} (K A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (i j : Fin N)
    (s : ℂ) : ℂ :=
  K i j / (s + z)
  + (∑ n, K i n * A j n / (s + z))
  + (∑ m, K m j * A i m / (s + z))
  + ∑ m, ∑ n, K m n * A i m * A j n / (s + z)

/-- **The equal-`z` `bᵢⱼ` is the general eq (23) specialized to a constant decay and a fixed
propagator matrix `A = A(z)`.** -/
theorem bij_eq23_const {N : ℕ} (K A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (i j : Fin N) (s : ℂ) :
    bij_eq23 K (fun _ => A) (fun _ _ => z) i j s = bij_eqz K A z i j s := rfl

/-- **eq (23) collapses to the matrix numerator over `s+z`.**  With one `z`, `bᵢⱼ(s) =
{(I+A)·K·(I+A)ᵀ}ᵢⱼ / (s + z)` — the numerator is exactly the propagator-dressed amplitude
`(I+A)K(I+A)ᵀ` (the `N` of the contact-value benchmark). -/
theorem bij_eqz_matrix {N : ℕ} (K A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (i j : Fin N) (s : ℂ) :
    bij_eqz K A z i j s = ((1 + A) * K * (1 + A)ᵀ : Matrix (Fin N) (Fin N) ℂ) i j / (s + z) := by
  have hd : ((1 : Matrix (Fin N) (Fin N) ℂ) + A) * K * (1 + A)ᵀ
      = K + K * Aᵀ + A * K + A * K * Aᵀ := by
    rw [Matrix.transpose_add, Matrix.transpose_one]; noncomm_ring
  have e1 : (K * Aᵀ : Matrix (Fin N) (Fin N) ℂ) i j = ∑ n, K i n * A j n := by
    simp [Matrix.mul_apply, Matrix.transpose_apply]
  have e2 : (A * K : Matrix (Fin N) (Fin N) ℂ) i j = ∑ m, K m j * A i m := by
    simp only [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun m _ => mul_comm _ _
  have e3 : (A * K * Aᵀ : Matrix (Fin N) (Fin N) ℂ) i j
      = ∑ m, ∑ n, K m n * A i m * A j n := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun n _ => by ring
  simp only [bij_eqz]
  simp_rw [← Finset.sum_div]
  rw [← add_div, ← add_div, ← add_div, hd]
  congr 1
  simp only [Matrix.add_apply, e1, e2, e3]

/-- **The eq (23) residue value.**  The residue of `bᵢⱼ(s)` at the simple pole `s = −z` is the
dressed amplitude `{(I+A)·K·(I+A)ᵀ}ᵢⱼ`: `(s+z)·bᵢⱼ(s) = {(I+A)K(I+A)ᵀ}ᵢⱼ` for `s ≠ −z`. -/
theorem bij_eqz_residue {N : ℕ} (K A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (i j : Fin N) (s : ℂ)
    (hsz : s + z ≠ 0) :
    (s + z) * bij_eqz K A z i j s = ((1 + A) * K * (1 + A)ᵀ : Matrix (Fin N) (Fin N) ℂ) i j := by
  rw [bij_eqz_matrix]; field_simp

/-- Core large-`s` limit `s/(s+z) → 1` (real Laplace variable `s → ∞`). -/
theorem tendsto_s_div_s_add (z : ℂ) :
    Tendsto (fun s : ℝ => (s : ℂ) / ((s : ℂ) + z)) atTop (𝓝 1) := by
  have hi : Tendsto (fun s : ℝ => (s : ℂ)⁻¹) atTop (𝓝 0) := by
    have : Tendsto (fun s : ℝ => ((s⁻¹ : ℝ) : ℂ)) atTop (𝓝 ((0 : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero
    simpa [Complex.ofReal_inv] using this
  have h2 : Tendsto (fun s : ℝ => 1 + z * (s : ℂ)⁻¹) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℂ))).add (hi.const_mul z)
  have h1 : Tendsto (fun s : ℝ => (1 + z * (s : ℂ)⁻¹)⁻¹) atTop (𝓝 1) := by
    simpa using h2.inv₀ one_ne_zero
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have heq2 : (1 : ℂ) + z * (s : ℂ)⁻¹ = ((s : ℂ) + z) * (s : ℂ)⁻¹ := by
    rw [add_mul, mul_inv_cancel₀ hs0]
  rw [heq2, mul_inv, inv_inv, mul_comm, ← div_eq_mul_inv]

/-- **Tang & Lu eq (24), equal decay `z`.**  The contact value is the residue-at-`−z` amplitude:
`lim_{s→∞} s·bᵢⱼ(s) = {(I+A)K(I+A)ᵀ}ᵢⱼ` (`= 2π√(ρᵢρⱼ)Rᵢⱼ·g¹ᵢⱼ(Rᵢⱼ)`, the `N` of the benchmark). -/
theorem bij_eqz_contact {N : ℕ} (K A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (i j : Fin N) :
    Tendsto (fun s : ℝ => (s : ℂ) * bij_eqz K A z i j (s : ℂ)) atTop
      (𝓝 (((1 + A) * K * (1 + A)ᵀ : Matrix (Fin N) (Fin N) ℂ) i j)) := by
  have hfun : (fun s : ℝ => (s : ℂ) * bij_eqz K A z i j (s : ℂ))
      = fun s : ℝ =>
        (((1 + A) * K * (1 + A)ᵀ : Matrix (Fin N) (Fin N) ℂ) i j) * ((s : ℂ) / ((s : ℂ) + z)) := by
    funext s; rw [bij_eqz_matrix]; ring
  rw [hfun]
  have h := (tendsto_s_div_s_add z).const_mul
    (((1 + A) * K * (1 + A)ᵀ : Matrix (Fin N) (Fin N) ℂ) i j)
  rwa [mul_one] at h

/-- **Tang & Lu eq (24), general form.**  The contact value `lim_{s→∞} s·bᵢⱼ(s)` — each Yukawa
factor `s/(s+z_{αβ}) → 1` — is the sum of the four eq (23) residue amplitudes
`Kᵢⱼ + ∑ₙ Kᵢₙ Aⱼₙ(zᵢₙ) + ∑ₘ Kₘⱼ Aᵢₘ(zₘⱼ) + ∑ₘₙ Kₘₙ Aᵢₘ(zₘₙ)Aⱼₙ(zₘₙ)`. -/
theorem bij_eq23_contact {N : ℕ} (K : Matrix (Fin N) (Fin N) ℂ)
    (Aprop : ℂ → Matrix (Fin N) (Fin N) ℂ) (zmat : Fin N → Fin N → ℂ) (i j : Fin N) :
    Tendsto (fun s : ℝ => (s : ℂ) * bij_eq23 K Aprop zmat i j (s : ℂ)) atTop
      (𝓝 (K i j + (∑ n, K i n * Aprop (zmat i n) j n) + (∑ m, K m j * Aprop (zmat m j) i m)
          + ∑ m, ∑ n, K m n * Aprop (zmat m n) i m * Aprop (zmat m n) j n)) := by
  have hterm : ∀ c w : ℂ, Tendsto (fun s : ℝ => (s : ℂ) * (c / ((s : ℂ) + w))) atTop (𝓝 c) := by
    intro c w
    have h : Tendsto (fun s : ℝ => c * ((s : ℂ) / ((s : ℂ) + w))) atTop (𝓝 (c * 1)) :=
      (tendsto_s_div_s_add w).const_mul c
    rw [mul_one] at h
    have heq : (fun s : ℝ => c * ((s : ℂ) / ((s : ℂ) + w)))
        = fun s : ℝ => (s : ℂ) * (c / ((s : ℂ) + w)) := by funext s; ring
    rwa [heq] at h
  simp only [bij_eq23, mul_add, Finset.mul_sum]
  refine Tendsto.add (Tendsto.add (Tendsto.add ?_ ?_) ?_) ?_
  · exact hterm (K i j) (zmat i j)
  · exact tendsto_finsetSum _ fun n _ => hterm (K i n * Aprop (zmat i n) j n) (zmat i n)
  · exact tendsto_finsetSum _ fun m _ => hterm (K m j * Aprop (zmat m j) i m) (zmat m j)
  · exact tendsto_finsetSum _ fun m _ =>
      tendsto_finsetSum _ fun n _ =>
        hterm (K m n * Aprop (zmat m n) i m * Aprop (zmat m n) j n) (zmat m n)

/-- The Tang & Lu eq (24) contact prefactor `2π√(ρᵢρⱼ)Rᵢⱼ`. -/
noncomputable def contactPre {N : ℕ} (rho : Fin N → ℝ) (R : Fin N → Fin N → ℝ) (i j : Fin N) : ℝ :=
  2 * Real.pi * Real.sqrt (rho i * rho j) * R i j

/-- **First-order contact RDF `g¹ᵢⱼ(Rᵢⱼ)` (general).**  Tang & Lu eq (24) solved for the contact
value: the residue sum divided by the prefactor `2π√(ρᵢρⱼ)Rᵢⱼ`. -/
noncomputable def g1Contact {N : ℕ} (K : Matrix (Fin N) (Fin N) ℂ)
    (Aprop : ℂ → Matrix (Fin N) (Fin N) ℂ) (zmat : Fin N → Fin N → ℂ)
    (rho : Fin N → ℝ) (R : Fin N → Fin N → ℝ) (i j : Fin N) : ℂ :=
  (K i j + (∑ n, K i n * Aprop (zmat i n) j n) + (∑ m, K m j * Aprop (zmat m j) i m)
    + ∑ m, ∑ n, K m n * Aprop (zmat m n) i m * Aprop (zmat m n) j n)
  / (contactPre rho R i j : ℂ)

/-- **`g¹ᵢⱼ(Rᵢⱼ)` is the `s → ∞` limit of `s·bᵢⱼ(s)/(2π√(ρᵢρⱼ)Rᵢⱼ)`** (eq 24 divided through). -/
theorem g1Contact_limit {N : ℕ} (K : Matrix (Fin N) (Fin N) ℂ)
    (Aprop : ℂ → Matrix (Fin N) (Fin N) ℂ) (zmat : Fin N → Fin N → ℂ)
    (rho : Fin N → ℝ) (R : Fin N → Fin N → ℝ) (i j : Fin N) :
    Tendsto (fun s : ℝ => (s : ℂ) * bij_eq23 K Aprop zmat i j (s : ℂ) / (contactPre rho R i j : ℂ))
      atTop (𝓝 (g1Contact K Aprop zmat rho R i j)) :=
  (bij_eq23_contact K Aprop zmat i j).div_const _

/-- **First-order contact RDF `g¹ᵢⱼ(Rᵢⱼ)` (equal decay `z`).**  `{(I+A)K(I+A)ᵀ}ᵢⱼ / (2π√(ρᵢρⱼ)Rᵢⱼ)`
— the equal-`z` residue value `N = (I+A)K(I+A)ᵀ` is `z`-independent (`A = A(z)` carries `z`). -/
noncomputable def g1Contact_eqz {N : ℕ} (K A : Matrix (Fin N) (Fin N) ℂ)
    (rho : Fin N → ℝ) (R : Fin N → Fin N → ℝ) (i j : Fin N) : ℂ :=
  ((1 + A) * K * (1 + A)ᵀ : Matrix (Fin N) (Fin N) ℂ) i j / (contactPre rho R i j : ℂ)

/-- **`g¹ᵢⱼ(Rᵢⱼ)` (equal `z`) is the `s → ∞` limit of `s·bᵢⱼ(s)/(2π√(ρᵢρⱼ)Rᵢⱼ)`.** -/
theorem g1Contact_eqz_limit {N : ℕ} (K A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ)
    (rho : Fin N → ℝ) (R : Fin N → Fin N → ℝ) (i j : Fin N) :
    Tendsto (fun s : ℝ => (s : ℂ) * bij_eqz K A z i j (s : ℂ) / (contactPre rho R i j : ℂ))
      atTop (𝓝 (g1Contact_eqz K A rho R i j)) :=
  (bij_eqz_contact K A z i j).div_const _

/-- **eq (24) as written** — `2π√(ρᵢρⱼ)Rᵢⱼ·g¹ᵢⱼ(Rᵢⱼ) = {(I+A)K(I+A)ᵀ}ᵢⱼ` (`= lim s·bᵢⱼ`),
for a non-degenerate prefactor `2π√(ρᵢρⱼ)Rᵢⱼ ≠ 0`. -/
theorem g1Contact_eqz_spec {N : ℕ} (K A : Matrix (Fin N) (Fin N) ℂ)
    (rho : Fin N → ℝ) (R : Fin N → Fin N → ℝ) (i j : Fin N) (hc : contactPre rho R i j ≠ 0) :
    (contactPre rho R i j : ℂ) * g1Contact_eqz K A rho R i j
    = ((1 + A) * K * (1 + A)ᵀ : Matrix (Fin N) (Fin N) ℂ) i j := by
  have hcC : (contactPre rho R i j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
  rw [g1Contact_eqz]; field_simp

end FMSA.MixtureRDF
