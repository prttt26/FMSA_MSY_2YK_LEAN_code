/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import LeanCode.HSMixture.MixtureOzStar

/-!
# Matrix Baxter seed — the first convolution `u := Ψ ⋆ Q₊` and its outer vanishing (`OZFIX.15`)

The scalar seed identity `baxter_psi_conv_eq_phi` (`Ψ ⋆ Q₊ ⋆ Q₋ = r·c_HS`, `BaxterRenewal.lean`) is
what the OZ★ assembly's `hclaimA` is built from.  Its first brick is `baxter_u_outer`: the renewal
equation `Ψ(r) = F(r) + ∫_σ^r q0(r−t)·Ψ(t) dt` (`r ≥ σ`) is equivalent to the **convolution**
statement `u := Ψ ⋆ Q₊ ≡ 0` on `[σ,∞)`, i.e. `Ψ(r) = ∫_0^σ q0(t)·Ψ(r−t) dt`.

This file builds the matrix analog.  The reusable analytic heart is `intervalConv_sub_open` — a
general "substitute `s = r−t`, then open the support" reduction valid for **any** continuous kernel
`q` supported in `[0,σ]` — and the matrix `baxter_u_outer` is that reduction summed over the
intermediate species `k` and matched against the coupled matrix renewal (`MatRenewalEq`) with the
forcing taken as the core convolution.

* `intervalConv_sub_open` — `∫_0^σ q(t)·ψ(r−t) dt = ∫_0^r q(r−s)·ψ(s) ds` for `q` supported in
  `[0,σ]` (scalar, reusable — no core/forcing content).
* `matBaxterU` — the matrix first Baxter convolution `uᵢⱼ(r) = Ψᵢⱼ(r) − ∑ₖ ∫_0^σ Qᵢₖ(t)·Ψₖⱼ(r−t) dt`.
* `matBaxterU_outer` — `uᵢⱼ ≡ 0` on `[σ,∞)`: the coupled renewal in convolution form, matrix `(A)`.

Status: ✓ axiom-clean.  The remaining seed pieces (the matrix `baxter_core_seed` affine algebra and
the second convolution `⋆ Q₋`) need the concrete real-space matrix Baxter data and are left open.
-/

open MeasureTheory Set
namespace FMSA.MixtureOzStar
noncomputable section

/-- **Substitute `s = r − t`, then open the support** — for a continuous kernel `q` supported in
`[0,σ]` (`q v = 0` once `v ≥ σ`) and `r ≥ σ`,

  `∫_0^σ q(t)·ψ(r−t) dt = ∫_0^r q(r−s)·ψ(s) ds`.

The substitution turns the `[0,σ]` integral into `∫_{r−σ}^r q(r−s)ψ(s)`, and the `[0,r−σ]` tail is
identically `0` (there `r−s ≥ σ`, so `q(r−s) = 0`), so the lower limit opens to `0`.  Reusable: it
carries no core-value or forcing content — those enter only when matching `∫_0^σ q(r−s)ψ(s)` to a
forcing term.  This is the general form of the scalar `baxter_u_outer` reduction. -/
theorem intervalConv_sub_open {q psi : ℝ → ℝ} {sigma r : ℝ} (hsigma : 0 < sigma) (hr : sigma ≤ r)
    (hqsupp : ∀ v, sigma ≤ v → q v = 0)
    (hInt : IntervalIntegrable (fun s => q (r - s) * psi s) volume 0 r) :
    (∫ t in (0:ℝ)..sigma, q t * psi (r - t)) = ∫ s in (0:ℝ)..r, q (r - s) * psi s := by
  have hrs : (0:ℝ) ≤ r - sigma := by linarith
  -- Step 1: substitute `s = r − t`.
  have hstep1 : (∫ t in (0:ℝ)..sigma, q t * psi (r - t))
      = ∫ s in (r - sigma)..r, q (r - s) * psi s := by
    have h := intervalIntegral.integral_comp_sub_left (a := (0:ℝ)) (b := sigma)
      (f := fun s => q (r - s) * psi s) r
    simpa only [sub_sub_cancel, sub_zero] using h
  rw [hstep1]
  -- Step 2: the `[0, r−σ]` tail vanishes, so the lower limit opens to `0`.
  have hInt1 : IntervalIntegrable (fun s => q (r - s) * psi s) volume 0 (r - sigma) :=
    hInt.mono_set (Set.uIcc_subset_uIcc
      (by rw [Set.mem_uIcc]; exact Or.inl ⟨le_refl 0, by linarith⟩)
      (by rw [Set.mem_uIcc]; exact Or.inl ⟨hrs, by linarith⟩))
  have hInt2 : IntervalIntegrable (fun s => q (r - s) * psi s) volume (r - sigma) r :=
    hInt.mono_set (Set.uIcc_subset_uIcc
      (by rw [Set.mem_uIcc]; exact Or.inl ⟨hrs, by linarith⟩)
      (by rw [Set.mem_uIcc]; exact Or.inl ⟨by linarith, le_refl r⟩))
  have hvanish : (∫ s in (0:ℝ)..(r - sigma), q (r - s) * psi s) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) ?_, intervalIntegral.integral_zero]
    intro s hs
    rw [Set.uIcc_of_le hrs] at hs
    dsimp only []
    rw [hqsupp (r - s) (by linarith [hs.2]), zero_mul]
  conv_rhs => rw [← intervalIntegral.integral_add_adjacent_intervals hInt1 hInt2]
  rw [hvanish, zero_add]

/-! ### The matrix first Baxter convolution and its outer vanishing -/

/-- **Matrix first Baxter convolution `u := Ψ ⋆ Q₊`.**
`uᵢⱼ(r) = Ψᵢⱼ(r) − ∑ₖ ∫_0^σ Qᵢₖ(t)·Ψₖⱼ(r−t) dt` — the matrix analog of the scalar `baxterU`, with the
species-coupling sum over `k`. -/
def matBaxterU {N : ℕ} (Psi Q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma : ℝ) (i j : Fin N) (r : ℝ) :
    ℝ :=
  Psi i j r - ∑ k, ∫ t in (0:ℝ)..sigma, Q i k t * Psi k j (r - t)

/-- **Matrix `(A)` — `u := Ψ ⋆ Q₊ ≡ 0` on `[σ,∞)`.**  The coupled matrix renewal equation
(`MatRenewalEq`, with the `∫_σ^r` forcing form) is equivalent, on `[σ,∞)`, to the convolution
statement `Ψᵢⱼ(r) = ∑ₖ ∫_0^σ Qᵢₖ(t)·Ψₖⱼ(r−t) dt`, provided the forcing `F` is the **core convolution**
`Fᵢⱼ(r) = ∑ₖ ∫_0^σ Qᵢₖ(r−s)·Ψcoreₖⱼ(s) ds` and the kernels are supported in `[0,σ]`.  The matrix
analog of the scalar `baxter_u_outer`: the reusable `intervalConv_sub_open` reduction summed over the
species `k`, with the `[0,σ]` piece matched to the forcing via the core values.  Hypotheses: `Q`
continuous + supported in `[0,σ]`; `Ψcore` continuous; `Ψ = Ψcore` on the open core and continuous on
each `[σ,b]` (the glued-solution regularity); `F` = the core convolution; `MatRenewalEq`. -/
theorem matBaxterU_outer {N : ℕ} (sigma : ℝ) (hsigma : 0 < sigma)
    (Psi Psicore Q Fmat : Matrix (Fin N) (Fin N) (ℝ → ℝ))
    (hQcont : ∀ i k, Continuous (Q i k))
    (hQsupp : ∀ i k v, sigma ≤ v → Q i k v = 0)
    (hcore_cont : ∀ k j, Continuous (Psicore k j))
    (hcore : ∀ k j s, s ∈ Set.Ioo (0:ℝ) sigma → Psi k j s = Psicore k j s)
    (houter_cont : ∀ k j b, ContinuousOn (Psi k j) (Set.Icc sigma b))
    (hforcing : ∀ i j r, sigma ≤ r →
      Fmat i j r = ∑ k, ∫ s in (0:ℝ)..sigma, Q i k (r - s) * Psicore k j s)
    (hrenewal : ∀ i j r, sigma ≤ r →
      Psi i j r = Fmat i j r + ∑ k, ∫ t in sigma..r, Q i k (r - t) * Psi k j t)
    {r : ℝ} (hr : sigma ≤ r) (i j : Fin N) :
    matBaxterU Psi Q sigma i j r = 0 := by
  rw [matBaxterU, sub_eq_zero, hrenewal i j r hr, hforcing i j r hr, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  -- integrability of `Qᵢₖ(r−·)·Ψₖⱼ` on `[0,r]`, split at `σ` (core a.e. + outer continuous)
  have hcontA : Continuous (fun s => Q i k (r - s) * Psicore k j s) :=
    ((hQcont i k).comp (continuous_const.sub continuous_id)).mul (hcore_cont k j)
  have haeA : (fun s => Q i k (r - s) * Psi k j s)
      =ᵐ[volume.restrict (Set.Ioc (0:ℝ) sigma)] (fun s => Q i k (r - s) * Psicore k j s) := by
    rw [← MeasureTheory.Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with s hs
    rw [hcore k j s ⟨hs.1, hs.2⟩]
  have hIa : IntervalIntegrable (fun s => Q i k (r - s) * Psi k j s) volume 0 sigma := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hsigma.le]
    exact ((hcontA.integrableOn_Icc (a := 0) (b := sigma)).mono_set
      Set.Ioc_subset_Icc_self).congr_fun_ae haeA.symm
  have hIb : IntervalIntegrable (fun s => Q i k (r - s) * Psi k j s) volume sigma r := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hr]
    exact (((hQcont i k).comp (continuous_const.sub continuous_id)).continuousOn).mul
      (houter_cont k j r)
  -- the reduction and the split
  have hgen := intervalConv_sub_open (q := Q i k) (psi := Psi k j) hsigma hr (hQsupp i k)
    (hIa.trans hIb)
  have hsplit : (∫ s in (0:ℝ)..r, Q i k (r - s) * Psi k j s)
      = (∫ s in (0:ℝ)..sigma, Q i k (r - s) * Psi k j s)
        + ∫ s in sigma..r, Q i k (r - s) * Psi k j s :=
    (intervalIntegral.integral_add_adjacent_intervals hIa hIb).symm
  have hcore_int : (∫ s in (0:ℝ)..sigma, Q i k (r - s) * Psi k j s)
      = ∫ s in (0:ℝ)..sigma, Q i k (r - s) * Psicore k j s := by
    refine intervalIntegral.integral_congr_ae ?_
    rw [Set.uIoc_of_le hsigma.le]
    have hne : ∀ᵐ x : ℝ, x ≠ sigma := by
      rw [MeasureTheory.ae_iff]; simp
    filter_upwards [hne] with s hs hmem
    rw [hcore k j s ⟨hmem.1, lt_of_le_of_ne hmem.2 hs⟩]
  rw [hgen, hsplit, hcore_int]

/-! ### The second Baxter convolution `⋆ Q₋` and the outer half of the seed -/

/-- **Matrix second Baxter convolution `Ψ ⋆ Q₊ ⋆ Q₋`.**  Applying the reflected Baxter factor `Q₋`
to `u := matBaxterU`: `(u ⋆ Q₋)ᵢⱼ(r) = uᵢⱼ(r) − ∑ₖ ∫_0^σ Qᵢₖ(t)·uₖⱼ(r+t) dt` (the `r+t` sample is
`Q₋(v) = Q₊(−v)`).  The matrix analog of the scalar `baxterUQm`. -/
def matBaxterUQm {N : ℕ} (Psi Q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma : ℝ) (i j : Fin N) (r : ℝ) :
    ℝ :=
  matBaxterU Psi Q sigma i j r - ∑ k, ∫ t in (0:ℝ)..sigma, Q i k t * matBaxterU Psi Q sigma k j (r + t)

/-- **The outer half of the seed — `Ψ ⋆ Q₊ ⋆ Q₋ ≡ 0` on `[σ,∞)`.**  Once `u := Ψ ⋆ Q₊` vanishes on
`[σ,∞)` (matrix claim `(A)`, `matBaxterU_outer`), the second convolution vanishes there too: `uᵢⱼ(r)=0`
and, for `t ∈ [0,σ]`, `uₖⱼ(r+t)=0` (as `r+t ≥ σ`), so every term of the coupling sum is `0`.  This is
the `r ≥ σ` branch of the scalar `baxter_psi_conv_eq_phi` (there `r·c_HS(r)` also vanishes, `c_HS`
being supported in `[0,σ]`).  Stated abstractly in the vanishing hypothesis `hUouter` so the caller
supplies it from `matBaxterU_outer`; the nontrivial **core** branch `(0,σ)` needs the matrix
`baxter_core_seed` affine algebra (the concrete moments), left open. -/
theorem matBaxterUQm_zero_of_uOuter {N : ℕ} (Psi Q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma : ℝ)
    (hsigma : 0 < sigma)
    (hUouter : ∀ i j r, sigma ≤ r → matBaxterU Psi Q sigma i j r = 0)
    {r : ℝ} (hr : sigma ≤ r) (i j : Fin N) :
    matBaxterUQm Psi Q sigma i j r = 0 := by
  rw [matBaxterUQm, hUouter i j r hr, zero_sub, neg_eq_zero]
  refine Finset.sum_eq_zero (fun k _ => ?_)
  rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) ?_, intervalIntegral.integral_zero]
  intro t ht
  rw [Set.uIcc_of_le hsigma.le] at ht
  dsimp only []
  rw [hUouter k j (r + t) (by linarith [ht.1]), mul_zero]

/-! ### Claim (B) — `u := Ψ ⋆ Q₊` is affine on the core -/

/-- **Matrix `(B)` — `u := Ψ ⋆ Q₊` is the explicit affine row-moment form on the core.**  For any `Ψ`
carrying the definitional core value `Ψₖⱼ(v) = −v` on `(−σ,σ)` (the multicomponent `h = −1` hard-core
value), on `0 < r < σ` the whole sampling range `r − t` (`t ∈ [0,σ]`) stays in the core, so

  `uᵢⱼ(r) = Ψᵢⱼ(r) − ∑ₖ ∫_0^σ Qᵢₖ(t)·Ψₖⱼ(r−t) dt = r·(∑ₖ M₀ᵢₖ − 1) − ∑ₖ M₁ᵢₖ`,

with `M₀ᵢₖ = ∫_0^σ Qᵢₖ`, `M₁ᵢₖ = ∫_0^σ t·Qᵢₖ` the `[0,σ]` moments of the Baxter factor row.  The matrix
analog of the scalar `baxter_u_core`: the scalar computation summed over the intermediate species `k`.
Stated with **integrability** (not continuity) of the factor rows so it accepts the physical
`WHSupports.q0MixEntry` (which jumps at `λᵢₖ`).  The `−1` is the single `Ψᵢⱼ(r) = −r` term (the Baxter
identity part), NOT summed over `k`. -/
theorem matBaxterU_core {N : ℕ} (sigma : ℝ) (hsigma : 0 < sigma)
    (Psi Q : Matrix (Fin N) (Fin N) (ℝ → ℝ))
    (hQ0 : ∀ i k, IntervalIntegrable (Q i k) volume 0 sigma)
    (hQ1 : ∀ i k, IntervalIntegrable (fun t => t * Q i k t) volume 0 sigma)
    (hcore : ∀ (k j : Fin N) (v : ℝ), v ∈ Set.Ioo (-sigma) sigma → Psi k j v = -v)
    {r : ℝ} (hr : r ∈ Set.Ioo (0:ℝ) sigma) (i j : Fin N) :
    matBaxterU Psi Q sigma i j r
      = r * ((∑ k, ∫ t in (0:ℝ)..sigma, Q i k t) - 1)
        - ∑ k, ∫ t in (0:ℝ)..sigma, t * Q i k t := by
  obtain ⟨hr0, hrlt⟩ := hr
  have hpr : Psi i j r = -r := hcore i j r ⟨by linarith, hrlt⟩
  have hcongr : (∑ k, ∫ t in (0:ℝ)..sigma, Q i k t * Psi k j (r - t))
      = ∑ k, ∫ t in (0:ℝ)..sigma, (t * Q i k t - r * Q i k t) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [Set.uIcc_of_le hsigma.le] at ht
    rw [hcore k j (r - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩]
    ring
  unfold matBaxterU
  rw [hpr, hcongr]
  have hsplit : ∀ k : Fin N, (∫ t in (0:ℝ)..sigma, (t * Q i k t - r * Q i k t))
      = (∫ t in (0:ℝ)..sigma, t * Q i k t) - r * ∫ t in (0:ℝ)..sigma, Q i k t := by
    intro k
    rw [intervalIntegral.integral_sub (hQ1 i k) ((hQ0 i k).const_mul r),
        intervalIntegral.integral_const_mul]
  simp_rw [hsplit]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

end
end FMSA.MixtureOzStar
