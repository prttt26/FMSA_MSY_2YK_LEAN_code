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

/-! ### The second Baxter convolution on the core — reduction to the Wertheim–Thiele seed -/

/-- **Matrix `(u ⋆ Q₋)` core truncation** — on `0 < r < σ` the second Baxter convolution's `[0,σ]`
integral collapses to `[0,σ−r]`:

  `matBaxterUQmᵢⱼ(r) = uᵢⱼ(r) − ∑ₖ ∫₀^{σ−r} Qᵢₖ(t)·uₖⱼ(r+t) dt`   (`u := matBaxterU`).

The `[σ−r,σ]` tail vanishes **exactly** (not merely a.e.): for `t ≥ σ−r` the sample `r+t ≥ σ`, where
`uₖⱼ` has switched to the outer branch and is `0` (matrix claim `(A)`, `matBaxterU_outer`), so every
integrand is `Qᵢₖ(t)·0 = 0`.  This is the matrix analog of the `htail`/`hsplit` step inside the scalar
`baxter_psi_conv_eq_phi`; it carries no moment content — only claim `(A)` + interval integrability. -/
theorem matBaxterUQm_core_reduce {N : ℕ} (Psi Q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma : ℝ)
    (hUouter : ∀ i j r, sigma ≤ r → matBaxterU Psi Q sigma i j r = 0)
    (hint : ∀ (i j k : Fin N) (r : ℝ), IntervalIntegrable
      (fun t => Q i k t * matBaxterU Psi Q sigma k j (r + t)) volume 0 sigma)
    {r : ℝ} (hr : r ∈ Set.Ioo (0 : ℝ) sigma) (i j : Fin N) :
    matBaxterUQm Psi Q sigma i j r
      = matBaxterU Psi Q sigma i j r
        - ∑ k, ∫ t in (0:ℝ)..(sigma - r), Q i k t * matBaxterU Psi Q sigma k j (r + t) := by
  obtain ⟨hr0, hrlt⟩ := hr
  have hsr : (0:ℝ) ≤ sigma - r := by linarith
  unfold matBaxterUQm
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hIa : IntervalIntegrable (fun t => Q i k t * matBaxterU Psi Q sigma k j (r + t))
      volume 0 (sigma - r) :=
    (hint i j k r).mono_set (Set.uIcc_subset_uIcc
      (by rw [Set.mem_uIcc]; exact Or.inl ⟨le_refl 0, by linarith⟩)
      (by rw [Set.mem_uIcc]; exact Or.inl ⟨hsr, by linarith⟩))
  have hIb : IntervalIntegrable (fun t => Q i k t * matBaxterU Psi Q sigma k j (r + t))
      volume (sigma - r) sigma :=
    (hint i j k r).mono_set (Set.uIcc_subset_uIcc
      (by rw [Set.mem_uIcc]; exact Or.inl ⟨hsr, by linarith⟩)
      (by rw [Set.mem_uIcc]; exact Or.inl ⟨by linarith, le_refl sigma⟩))
  have htail : (∫ t in (sigma - r)..sigma, Q i k t * matBaxterU Psi Q sigma k j (r + t)) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) ?_, intervalIntegral.integral_zero]
    intro t ht
    rw [Set.uIcc_of_le (by linarith : sigma - r ≤ sigma)] at ht
    dsimp only []
    rw [hUouter k j (r + t) (by linarith [ht.1]), mul_zero]
  rw [← intervalIntegral.integral_add_adjacent_intervals hIa hIb, htail, add_zero]

/-- **Matrix `OZFIX.15` seed, assembled from an abstract core seed — `Ψ ⋆ Q₊ ⋆ Q₋ = r·Φ` on `(0,∞)`.**
With `u := matBaxterU` (`= Ψ ⋆ Q₊`) and the second convolution `matBaxterUQm` (`= (Ψ ⋆ Q₊) ⋆ Q₋`,
parenthesised — no Fubini/associativity), the full seed holds on **all** `r > 0` given the single
concrete **core-seed hypothesis** `hseed` (the matrix Wertheim–Thiele identity, the analog of the
scalar `baxter_core_seed`) plus the already-proved plumbing:

* `0 < r < σ`: `matBaxterUQm_core_reduce` collapses the `[0,σ]` integral to `[0,σ−r]`, then `hseed`.
* `r ≥ σ`: `matBaxterUQm_zero_of_uOuter` gives `0`, and `Φ` (`= c_HS`, supported in `[0,σ]`) is `0` too.

This mirrors the scalar `baxter_psi_conv_eq_phi`, isolating the **only** remaining seed gap to `hseed`:
the pure moment/`Φ` identity on the core, with all support/integrability discharged here. -/
theorem matBaxterUQm_eq_rPhi_of_seed {N : ℕ} (Psi Q Phi : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma : ℝ)
    (hsigma : 0 < sigma)
    (hUouter : ∀ i j r, sigma ≤ r → matBaxterU Psi Q sigma i j r = 0)
    (hPhiOuter : ∀ i j r, sigma ≤ r → Phi i j r = 0)
    (hint : ∀ (i j k : Fin N) (r : ℝ), IntervalIntegrable
      (fun t => Q i k t * matBaxterU Psi Q sigma k j (r + t)) volume 0 sigma)
    (hseed : ∀ (i j : Fin N), ∀ r ∈ Set.Ioo (0 : ℝ) sigma,
      matBaxterU Psi Q sigma i j r
        - ∑ k, ∫ t in (0:ℝ)..(sigma - r), Q i k t * matBaxterU Psi Q sigma k j (r + t)
      = r * Phi i j r)
    {r : ℝ} (hr : 0 < r) (i j : Fin N) :
    matBaxterUQm Psi Q sigma i j r = r * Phi i j r := by
  rcases lt_or_ge r sigma with hrs | hrs
  · rw [matBaxterUQm_core_reduce Psi Q sigma hUouter hint ⟨hr, hrs⟩ i j]
    exact hseed i j r ⟨hr, hrs⟩
  · rw [matBaxterUQm_zero_of_uOuter Psi Q sigma hsigma hUouter hrs i j,
      hPhiOuter i j r hrs, mul_zero]

/-! ### The core seed in explicit row-moment form (claim (B) substituted) -/

/-- **The truncated second convolution, in explicit row-moment form.**  On `0 < r < σ`, substituting
the affine core form of `u` (matrix claim `(B)`, `matBaxterU_core`) both for the leading `uᵢⱼ(r)` and
for `uₖⱼ(r+t)` under the `[0,σ−r]` integral (a.e. — the endpoint `t = σ−r` samples `r+t = σ`, outside
the open core), the seed's left-hand side becomes the fully explicit **row-moment** expression

  `(r·(∑ₖM₀ᵢₖ − 1) − ∑ₖM₁ᵢₖ) − ∑ₖ ∫₀^{σ−r} Qᵢₖ(t)·((r+t)·(∑ₗM₀ₖₗ − 1) − ∑ₗM₁ₖₗ) dt`,

with `M₀ᵢₖ = ∫₀^σ Qᵢₖ`, `M₁ᵢₖ = ∫₀^σ t·Qᵢₖ` the `[0,σ]` moments of the Baxter-factor row.  This is the
matrix analog of the algebra inside the scalar `baxter_seed_at_psi`, and reduces the seed to a pure
moment/`Φ` identity (the matrix `baxter_core_seed`).  The core value enters only through `hcore`
(`Ψ = −v` on `(−σ,σ)`, the `h = −1` hard-core value). -/
theorem matBaxterUQm_coreSeed_moment {N : ℕ} (Psi Q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma : ℝ)
    (hsigma : 0 < sigma)
    (hQ0 : ∀ i k, IntervalIntegrable (Q i k) volume 0 sigma)
    (hQ1 : ∀ i k, IntervalIntegrable (fun t => t * Q i k t) volume 0 sigma)
    (hcore : ∀ (k j : Fin N) (v : ℝ), v ∈ Set.Ioo (-sigma) sigma → Psi k j v = -v)
    {r : ℝ} (hr : r ∈ Set.Ioo (0 : ℝ) sigma) (i j : Fin N) :
    matBaxterU Psi Q sigma i j r
        - ∑ k, ∫ t in (0:ℝ)..(sigma - r), Q i k t * matBaxterU Psi Q sigma k j (r + t)
      = (r * ((∑ k, ∫ t in (0:ℝ)..sigma, Q i k t) - 1) - ∑ k, ∫ t in (0:ℝ)..sigma, t * Q i k t)
        - ∑ k, ∫ t in (0:ℝ)..(sigma - r), Q i k t
            * ((r + t) * ((∑ l, ∫ s in (0:ℝ)..sigma, Q k l s) - 1)
               - ∑ l, ∫ s in (0:ℝ)..sigma, s * Q k l s) := by
  obtain ⟨hr0, hrlt⟩ := hr
  have hsr : (0:ℝ) ≤ sigma - r := by linarith
  rw [matBaxterU_core sigma hsigma Psi Q hQ0 hQ1 hcore ⟨hr0, hrlt⟩ i j]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine intervalIntegral.integral_congr_ae ?_
  rw [Set.uIoc_of_le hsr]
  have hne : ∀ᵐ x : ℝ, x ≠ sigma - r := by rw [MeasureTheory.ae_iff]; simp
  filter_upwards [hne] with t ht hmem
  have hlt : t < sigma - r := lt_of_le_of_ne hmem.2 ht
  rw [matBaxterU_core sigma hsigma Psi Q hQ0 hQ1 hcore
    (r := r + t) ⟨by linarith [hmem.1], by linarith⟩ k j]

/-- **Matrix `OZFIX.15` seed from the pure moment identity — the MML.8-ready form.**  The full second
convolution `matBaxterUQm = Ψ ⋆ Q₊ ⋆ Q₋` equals `r·Φ` on all `r > 0`, given the plumbing (claim `(A)`
outer vanishing, `Φ` outer vanishing, integrability) **and the concrete core value** `Ψ = −v` +
moment-integrability (claim `(B)`), with the **only** genuine remaining input the pure moment identity
`hMomentSeed` — the matrix Wertheim–Thiele `baxter_core_seed` (row moments of the concrete
`WHSupports.q0MixEntry` matched against `Φ = c_HS`).  Everything else — supports, integrability, the
`(A)`/`(B)` substitutions, the two-regime split — is discharged.  This is the exact shape MML.8 needs:
supply `hMomentSeed` (equal-diameter, delta-free) and `matBaxterUQm ≡ r·c_HS` follows. -/
theorem matBaxterUQm_eq_rPhi_of_momentSeed {N : ℕ}
    (Psi Q Phi : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma : ℝ) (hsigma : 0 < sigma)
    (hUouter : ∀ i j r, sigma ≤ r → matBaxterU Psi Q sigma i j r = 0)
    (hPhiOuter : ∀ i j r, sigma ≤ r → Phi i j r = 0)
    (hint : ∀ (i j k : Fin N) (r : ℝ), IntervalIntegrable
      (fun t => Q i k t * matBaxterU Psi Q sigma k j (r + t)) volume 0 sigma)
    (hQ0 : ∀ i k, IntervalIntegrable (Q i k) volume 0 sigma)
    (hQ1 : ∀ i k, IntervalIntegrable (fun t => t * Q i k t) volume 0 sigma)
    (hcore : ∀ (k j : Fin N) (v : ℝ), v ∈ Set.Ioo (-sigma) sigma → Psi k j v = -v)
    (hMomentSeed : ∀ (i j : Fin N), ∀ r ∈ Set.Ioo (0 : ℝ) sigma,
      (r * ((∑ k, ∫ t in (0:ℝ)..sigma, Q i k t) - 1) - ∑ k, ∫ t in (0:ℝ)..sigma, t * Q i k t)
        - ∑ k, ∫ t in (0:ℝ)..(sigma - r), Q i k t
            * ((r + t) * ((∑ l, ∫ s in (0:ℝ)..sigma, Q k l s) - 1)
               - ∑ l, ∫ s in (0:ℝ)..sigma, s * Q k l s)
      = r * Phi i j r)
    {r : ℝ} (hr : 0 < r) (i j : Fin N) :
    matBaxterUQm Psi Q sigma i j r = r * Phi i j r := by
  refine matBaxterUQm_eq_rPhi_of_seed Psi Q Phi sigma hsigma hUouter hPhiOuter hint ?_ hr i j
  intro i' j' r' hr'
  rw [matBaxterUQm_coreSeed_moment Psi Q sigma hsigma hQ0 hQ1 hcore hr' i' j']
  exact hMomentSeed i' j' r' hr'

/-- **The general-`N` mixture DCF — the moment expression divided by `r`.**  The explicit-in-moments
inner DCF `c_ij(r)`: `matBaxterUQm = r · cMixMomentDCF` (the grand assembly below).  On the core
`(0,σ)` it is the Wertheim–Thiele moment expression over `r`; `0` outside.  Every `∫₀^σ` /
`∫₀^{σ−r}` in it is a closed form (`baxterQuad`/moment lemmas) — at unequal diameters the assembled
polynomial is piecewise (breakpoints `r = σ − Rᵢₖ`); at equal diameters the row-sum collapses it to
the scalar
`c_HS`.  (This is the WINDOWED-seed DCF; the loss-free object is the extended
`matBaxterUQmSymFullExt`.) -/
noncomputable def cMixMomentDCF (Q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma : ℝ)
    (i j : Fin N) (r : ℝ) : ℝ :=
  if r ∈ Set.Ioo (0:ℝ) sigma then
    ((r * ((∑ k, ∫ t in (0:ℝ)..sigma, Q i k t) - 1) - ∑ k, ∫ t in (0:ℝ)..sigma, t * Q i k t)
      - ∑ k, ∫ t in (0:ℝ)..(sigma - r), Q i k t
          * ((r + t) * ((∑ l, ∫ s in (0:ℝ)..sigma, Q k l s) - 1)
             - ∑ l, ∫ s in (0:ℝ)..sigma, s * Q k l s)) / r
  else 0

/-- **⭐⭐ General-`N` grand assembly — `matBaxterUQm = r · c_ij`, no equal-diameter row-collapse.**
For ANY renewal `Ψ` (core value `−v`, outer-vanishing `matBaxterU = 0` on `[σ,∞)`) and Baxter factor
`Q`, the second Baxter convolution equals `r` times the explicit mixture DCF `cMixMomentDCF Q σ`.
This is the general-`N` analog of the equal-diameter `matBaxterUQm_eq_rcHS_of_rowSum` (where `hrow`
collapses `c_ij` to the scalar `c_HS`) — here `c_ij` stays the explicit-in-moments expression, valid
at unequal diameters.  Composes `matBaxterUQm_eq_rPhi_of_momentSeed` with the tautological moment
seed `moment_expr = r · (moment_expr / r)` (`r > 0`). -/
theorem matBaxterUQm_eq_rcMixMomentDCF (Psi Q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma : ℝ)
    (hsigma : 0 < sigma)
    (hUouter : ∀ i j r, sigma ≤ r → matBaxterU Psi Q sigma i j r = 0)
    (hint : ∀ (i j k : Fin N) (r : ℝ), IntervalIntegrable
      (fun t => Q i k t * matBaxterU Psi Q sigma k j (r + t)) volume 0 sigma)
    (hQ0 : ∀ i k, IntervalIntegrable (Q i k) volume 0 sigma)
    (hQ1 : ∀ i k, IntervalIntegrable (fun t => t * Q i k t) volume 0 sigma)
    (hcore : ∀ (k j : Fin N) (v : ℝ), v ∈ Set.Ioo (-sigma) sigma → Psi k j v = -v)
    {r : ℝ} (hr : 0 < r) (i j : Fin N) :
    matBaxterUQm Psi Q sigma i j r = r * cMixMomentDCF Q sigma i j r := by
  refine matBaxterUQm_eq_rPhi_of_momentSeed Psi Q (cMixMomentDCF Q sigma) sigma hsigma hUouter
    ?_ hint hQ0 hQ1 hcore ?_ hr i j
  · intro i' j' r' hr'
    simp only [cMixMomentDCF, if_neg (fun hm => absurd (Set.mem_Ioo.mp hm).2 (not_lt.mpr hr'))]
  · intro i' j' r' hr'
    have hrne : r' ≠ 0 := ne_of_gt (Set.mem_Ioo.mp hr').1
    simp only [cMixMomentDCF, if_pos hr']
    field_simp

open FMSA.HardSphere in
/-- **N=1 non-vacuity — the moment seed `hMomentSeed` reduces to the proved scalar `baxter_core_seed`.**
At one component (`Q = q0_poly`, `Φ = c_HS`), the matrix Wertheim–Thiele moment identity required by
`matBaxterUQm_eq_rPhi_of_momentSeed` **is** the scalar `FMSA.HardSphere.baxter_core_seed` (`OZFIX.15`):
the `Fin 1` sums collapse (`Fin.sum_univ_one`) and `baxterM0_eq`/`baxterM1_eq` fold the row integrals
into the moments `M₀`, `M₁`.  This witnesses that the one genuinely-concrete seed hypothesis is
**dischargeable** (not a vacuous `Prop`) — the seed-side analog of `matOZStar_fin_one_of_scalar`. -/
theorem matBaxterUQm_momentSeed_fin_one_of_scalar {eta sigma rho : ℝ}
    (hsigma : 0 < sigma) (heta : eta < 1) (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) :
    ∀ (i j : Fin 1), ∀ r ∈ Set.Ioo (0 : ℝ) sigma,
      (r * ((∑ k : Fin 1, ∫ t in (0:ℝ)..sigma, (fun _ _ => q0_poly eta sigma rho) i k t) - 1)
          - ∑ k : Fin 1, ∫ t in (0:ℝ)..sigma, t * (fun _ _ => q0_poly eta sigma rho) i k t)
        - ∑ k : Fin 1, ∫ t in (0:ℝ)..(sigma - r), (fun _ _ => q0_poly eta sigma rho) i k t
            * ((r + t) * ((∑ l : Fin 1, ∫ s in (0:ℝ)..sigma,
                    (fun _ _ => q0_poly eta sigma rho) k l s) - 1)
               - ∑ l : Fin 1, ∫ s in (0:ℝ)..sigma, s * (fun _ _ => q0_poly eta sigma rho) k l s)
      = r * (fun _ _ => c_HS eta sigma) i j r := by
  intro i j r hr
  fin_cases i; fin_cases j
  simp only [Fin.sum_univ_one, baxterM0_eq hsigma, baxterM1_eq hsigma]
  exact baxter_core_seed hsigma heta heta_def r hr

open FMSA.HardSphere in
/-- **General-N EQUAL-DIAMETER matrix `baxter_core_seed` — the moment seed via row-sum collapse.**

For a **common-diameter** mixture the physical Lebowitz PY coefficients `Q0phys`/`Qppphys` are
constant across species (`Q0phys i j`, `Qppphys j` depend on `σᵢ = σⱼ = σ` only), so the Baxter-factor
rows collapse: `∑ₖ Qᵢₖ(u) = q0_poly η σ ρ(u)`, the **one-component** scalar factor at the total density
`ρ = ∑ₖρₖ` (with `η = πρσ³/6`, the total packing).  Under this row-sum hypothesis `hrow`, every matrix
moment reduces to the scalar one — `∑ₖ M₀ᵢₖ = M₀`, `∑ₖ M₁ᵢₖ = M₁` (so the affine factor becomes
`k`-independent), and the coupling `∑ₖ Qᵢₖ(t)·(…)` pulls the row-sum inside the integral to `q0_poly` —
and the matrix moment identity **is** the proved scalar `baxter_core_seed` (`OZFIX.15`).  The `Φ = c_HS`
is the single one-component PY DCF (equal-diameter species are colour labels), matching the classical
result that same-size additive mixtures have a species-independent `c(r)`.  This **discharges**
`matBaxterUQm_eq_rPhi_of_momentSeed`'s `hMomentSeed` for general `N` in the delta-free equal-diameter
regime — the matrix Wertheim–Thiele seed. -/
theorem matBaxterUQm_momentSeed_of_rowSum {N : ℕ} (Q : Matrix (Fin N) (Fin N) (ℝ → ℝ))
    {eta sigma rho : ℝ} (hsigma : 0 < sigma) (heta : eta < 1)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6)
    (hrow : ∀ (i : Fin N) (u : ℝ), u ∈ Set.Icc (0:ℝ) sigma → ∑ k, Q i k u = q0_poly eta sigma rho u)
    (hQ0 : ∀ i k, IntervalIntegrable (Q i k) volume 0 sigma)
    (hQ1 : ∀ i k, IntervalIntegrable (fun t => t * Q i k t) volume 0 sigma) :
    ∀ (i _j : Fin N), ∀ r ∈ Set.Ioo (0 : ℝ) sigma,
      (r * ((∑ k, ∫ t in (0:ℝ)..sigma, Q i k t) - 1) - ∑ k, ∫ t in (0:ℝ)..sigma, t * Q i k t)
        - ∑ k, ∫ t in (0:ℝ)..(sigma - r), Q i k t
            * ((r + t) * ((∑ l, ∫ s in (0:ℝ)..sigma, Q k l s) - 1)
               - ∑ l, ∫ s in (0:ℝ)..sigma, s * Q k l s)
      = r * c_HS eta sigma r := by
  have hIcc : Set.uIcc (0:ℝ) sigma = Set.Icc 0 sigma := Set.uIcc_of_le hsigma.le
  -- row moments collapse to the scalar moments `M₀`, `M₁`
  have hM0 : ∀ i : Fin N, (∑ k, ∫ t in (0:ℝ)..sigma, Q i k t) = baxterM0 eta sigma rho := by
    intro i
    rw [← intervalIntegral.integral_finsetSum (fun k _ => hQ0 i k),
      intervalIntegral.integral_congr (g := q0_poly eta sigma rho)
        (fun t ht => hrow i t (hIcc ▸ ht)), baxterM0_eq hsigma]
  have hM1 : ∀ i : Fin N, (∑ k, ∫ t in (0:ℝ)..sigma, t * Q i k t) = baxterM1 eta sigma rho := by
    intro i
    rw [← intervalIntegral.integral_finsetSum (fun k _ => hQ1 i k),
      intervalIntegral.integral_congr (g := fun t => t * q0_poly eta sigma rho t)
        (fun t ht => (Finset.mul_sum Finset.univ (fun k => Q i k t) t).symm.trans
          (congrArg (fun x => t * x) (hrow i t (hIcc ▸ ht)))), baxterM1_eq hsigma]
  intro i _j r hr
  obtain ⟨hr0, hrlt⟩ := hr
  have hsr : (0:ℝ) ≤ sigma - r := by linarith
  simp only [hM0, hM1]
  -- the coupling term: pull the row-sum inside the truncated integral, giving the scalar integrand
  have hAcont : Continuous
      (fun t => (r + t) * (baxterM0 eta sigma rho - 1) - baxterM1 eta sigma rho) := by fun_prop
  have hDbl : (∑ k, ∫ t in (0:ℝ)..(sigma - r), Q i k t
        * ((r + t) * (baxterM0 eta sigma rho - 1) - baxterM1 eta sigma rho))
      = ∫ t in (0:ℝ)..(sigma - r), q0_poly eta sigma rho t
          * ((r + t) * (baxterM0 eta sigma rho - 1) - baxterM1 eta sigma rho) := by
    have hintk : ∀ k ∈ (Finset.univ : Finset (Fin N)),
        IntervalIntegrable (fun t => Q i k t
          * ((r + t) * (baxterM0 eta sigma rho - 1) - baxterM1 eta sigma rho)) volume 0 (sigma - r) :=
      fun k _ => ((hQ0 i k).mono_set (Set.uIcc_subset_uIcc
        (by rw [Set.mem_uIcc]; exact Or.inl ⟨le_refl 0, hsigma.le⟩)
        (by rw [Set.mem_uIcc]; exact Or.inl ⟨hsr, by linarith⟩))).mul_continuousOn hAcont.continuousOn
    rw [← intervalIntegral.integral_finsetSum hintk]
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [Set.uIcc_of_le hsr] at ht
    have hmem : t ∈ Set.Icc (0:ℝ) sigma := ⟨ht.1, by linarith [ht.2]⟩
    exact (Finset.sum_mul Finset.univ (fun k => Q i k t)
      ((r + t) * (baxterM0 eta sigma rho - 1) - baxterM1 eta sigma rho)).symm.trans
      (congrArg (fun x => x * ((r + t) * (baxterM0 eta sigma rho - 1) - baxterM1 eta sigma rho))
        (hrow i t hmem))
  rw [hDbl]
  exact baxter_core_seed hsigma heta heta_def r ⟨hr0, hrlt⟩

open FMSA.HardSphere in
/-- **General-N equal-diameter seed COMPLETE — `Ψ ⋆ Q₊ ⋆ Q₋ ≡ r·c_HS`.**  Combining the seed chain
(`matBaxterUQm_eq_rPhi_of_momentSeed`) with the equal-diameter core seed
(`matBaxterUQm_momentSeed_of_rowSum`), the second Baxter convolution equals `r·c_HS` on **all** `r > 0`
for a general-`N` common-diameter mixture: `Φ = c_HS` (the single one-component PY DCF) is fixed, and
its outer-vanishing is `c_HS_outer`.  This is the matrix `OZFIX.15` (`baxter_psi_conv_eq_phi`) at
general `N`, delta-free — the load-bearing MML.8 seed input, now with **no remaining hypothesis beyond
the equal-diameter row-sum collapse** `hrow` (and the standard claim-(A)/core-value regularity). -/
theorem matBaxterUQm_eq_rcHS_of_rowSum {N : ℕ} (Psi Q : Matrix (Fin N) (Fin N) (ℝ → ℝ))
    {eta sigma rho : ℝ} (hsigma : 0 < sigma) (heta : eta < 1)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6)
    (hUouter : ∀ i j r, sigma ≤ r → matBaxterU Psi Q sigma i j r = 0)
    (hint : ∀ (i j k : Fin N) (r : ℝ), IntervalIntegrable
      (fun t => Q i k t * matBaxterU Psi Q sigma k j (r + t)) volume 0 sigma)
    (hrow : ∀ (i : Fin N) (u : ℝ), u ∈ Set.Icc (0:ℝ) sigma → ∑ k, Q i k u = q0_poly eta sigma rho u)
    (hQ0 : ∀ i k, IntervalIntegrable (Q i k) volume 0 sigma)
    (hQ1 : ∀ i k, IntervalIntegrable (fun t => t * Q i k t) volume 0 sigma)
    (hcore : ∀ (k j : Fin N) (v : ℝ), v ∈ Set.Ioo (-sigma) sigma → Psi k j v = -v)
    {r : ℝ} (hr : 0 < r) (i j : Fin N) :
    matBaxterUQm Psi Q sigma i j r = r * c_HS eta sigma r :=
  matBaxterUQm_eq_rPhi_of_momentSeed Psi Q (fun _ _ => c_HS eta sigma) sigma hsigma
    hUouter (fun _ _ _ hr' => c_HS_outer hr') hint hQ0 hQ1 hcore
    (matBaxterUQm_momentSeed_of_rowSum Q hsigma heta heta_def hrow hQ0 hQ1) hr i j

end
end FMSA.MixtureOzStar
