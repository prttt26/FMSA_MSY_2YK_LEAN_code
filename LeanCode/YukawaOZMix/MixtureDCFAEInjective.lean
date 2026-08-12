/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import LeanCode.YukawaOZMix.MixtureRowSum
import LeanCode.YukawaOZMix.MixtureRealSpace
import LeanCode.Analysis.FourierAEInjective
import LeanCode.YukawaOZMix.MixtureCorrectedSeed
import LeanCode.HSMixture.MixtureOzStar
import LeanCode.YukawaOZMix.MixtureHSDCF
import LeanCode.HSMixture.PhysHSMix

/-!
# a.e.-injectivity of the DCF `zOfW` transform (obstruction (b), the continuity upgrade)

The MML.15 unequal-diameter obstruction (b) needs the real-space matrix DCF to be symmetric a.e.
(`matDCF i k = matDCF k i` a.e.) from the momentum symmetry `Qphys_Cmix0_symm`.  The real-space DCF
is **discontinuous** (its `q0MixEntry` linear terms jump at `v = λᵢₖ`), so the file's
`eq_of_fourier_eq` — which needs FULL continuity and concludes everywhere-equality — cannot apply.

The fix is `Analysis/FourierAEInjective.ae_eq_of_fourier_eq`, which needs only **a.e.-continuity**
and concludes **a.e.-equality** (its `𝓕 diff = 0` route needs no `Integrable (𝓕 ·)`, so it works on
the DCF whose transform is not `L¹`).  Composed with `MixtureRowSum.fourier_eq_zOfW` (the
`𝓕 ↔ ∫·e^{−zv}` convention bridge), it gives:

* **`ae_eq_of_zOfW_transform_eq`** — integrable, a.e.-continuous `f, g` with equal `zOfW`-transforms
  (`∫ f(v)e^{−(2πi w)v} dv = ∫ g(v)e^{−(2πi w)v} dv` for all `w`) agree a.e.

This is the tool obstruction (b) needs; what remains is the object-level bookkeeping — building
the correctly `ρ_geo`-weighted full-line DCF whose `zOfW` transform is the (symmetric) `Cmix0`, then
feeding `Qphys_Cmix0_symm`.  Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/

open MeasureTheory Complex
open scoped FourierTransform

namespace FMSA.MixtureOzStar

/-- **a.e.-injectivity of the `zOfW` (1-D real-space) transform.**  Two integrable, a.e.-continuous
functions with equal `∫ ·(v)·e^{−(2πi w)v} dv` transforms for every `w` agree a.e.  The a.e.-cont.
upgrade of the file's `eq_of_fourier_eq` (which needs full continuity, failing on the DCF's jumps at
`v = λ`), via `ae_eq_of_fourier_eq` + `fourier_eq_zOfW`. -/
theorem ae_eq_of_zOfW_transform_eq {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g)
    (hcf : ∀ᵐ v, ContinuousAt f v) (hcg : ∀ᵐ v, ContinuousAt g v)
    (heq : ∀ w : ℝ, (∫ v, f v * Complex.exp (-(zOfW w * v)))
      = ∫ v, g v * Complex.exp (-(zOfW w * v))) :
    f =ᵐ[volume] g := by
  refine ae_eq_of_fourier_eq hf hg ?_ hcf hcg
  funext w
  rw [fourier_eq_zOfW f w, fourier_eq_zOfW g w, heq w]

open FMSA.MRS Matrix in
/-- **`Cmix0` entry expansion — the identity/`δ` cancels, leaving a pure function.**  If the Baxter
matrix has the `q0_entry_c` shape `Q(s)ᵢⱼ = δᵢⱼ − ρ_geoᵢⱼ·B(s)ᵢⱼ` (which `Qphys` has by definition,
`B = e^{−λs}(Q0·p₁ + Qpp·p₂)`), then
`Cmix0(Q)(k)ᵢⱼ = ρ_geoᵢⱼ·B(k)ᵢⱼ + ρ_geoⱼᵢ·B(−k)ⱼᵢ − ∑ₗ ρ_geoᵢₗρ_geoⱼₗ·B(k)ᵢₗ·B(−k)ⱼₗ` — two linear
`B` terms + the `ρ_geo`-weighted double-product, with **no `δ`** (identity contributions cancel).
This is the momentum-side closed form the weighted real-space full-line DCF must transform to; with
`B(s)ᵢⱼ = ∫ q0MixEntry(i,j)·e^{−st}` (`q0MixEntry_laplace_c`) its `zOfW` inverse is
`ρ_geoᵢⱼ·q0MixEntry(i,j) + ρ_geoⱼᵢ·q0MixEntry(j,i)(−·) − (weighted matCorr)`, and `Qphys_Cmix0_symm`
+ `ae_eq_of_zOfW_transform_eq` then give the DCF a.e.-symmetry `hCsym`. -/
theorem Cmix0_entry_of_id_sub {N : ℕ} (Q : ℂ → Matrix (Fin N) (Fin N) ℂ)
    (B : ℂ → Fin N → Fin N → ℂ) (ρg : Fin N → Fin N → ℂ) (k : ℂ) (i j : Fin N)
    (hQ : ∀ s a b, Q s a b = (if a = b then (1 : ℂ) else 0) - ρg a b * B s a b) :
    Cmix0 Q k i j
      = ρg i j * B k i j + ρg j i * B (-k) j i
        - ∑ l, ρg i l * ρg j l * B k i l * B (-k) j l := by
  simp only [Cmix0, Matrix.sub_apply, Matrix.one_apply, Matrix.mul_apply, Matrix.transpose_apply,
    hQ]
  have hexp : ∀ l : Fin N,
      ((if i = l then (1 : ℂ) else 0) - ρg i l * B k i l)
        * ((if j = l then (1 : ℂ) else 0) - ρg j l * B (-k) j l)
      = (if i = l then (1 : ℂ) else 0) * (if j = l then (1 : ℂ) else 0)
        - (if i = l then (1 : ℂ) else 0) * (ρg j l * B (-k) j l)
        - (if j = l then (1 : ℂ) else 0) * (ρg i l * B k i l)
        + ρg i l * ρg j l * B k i l * B (-k) j l := fun l => by ring
  simp only [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rcases eq_or_ne i j with hij | hij
  · subst hij; ring
  · rw [if_neg hij, if_neg (Ne.symm hij)]; ring

/-! ### MRS.7 — the GENERAL-`N` physical swap `Cmix0ᵢⱼ = Cmix0ⱼᵢ`, assembled.  Chaining
`Cmix0_entry_of_id_sub` (general `N`) with the sum→moment reduction (`phys_sum`) and the bracket
core (`swap_pair_core`'s `field_simp;ring`, inlined via the `Ei = exp(kσᵢ/2)` exp bridge): the
physical zeroth-order mixture DCF is symmetric for ANY number of components — the general-`N`
`Qphys_Cmix0_entry_symm`, coefficient-free given the two `KEY` relations (`Q0phys`/`Qppphys`) + the
`ρ_geo` symmetry & product relations. -/

open FMSA.MRS in
/-- **Reduction of a physical `Cmix0` entry.**  `Cmix0ᵢⱼ = ρgᵢⱼ·e^{−λᵢⱼk}·(Tᵢⱼ(k) + Tⱼᵢ(−k) − Sᵢⱼ)`
with `Tᵢⱼ(k) = pP(σᵢ,k)·Qpp1 j + pQ(σᵢ,k)·c·σⱼ` (rank-2, KEY 1) and `Sᵢⱼ` the moment form — via
`Cmix0_entry_of_id_sub` + `phys_sum` + the two linear terms (`Bbra_sep`). -/
theorem Cmix0_phys_reduce {N : ℕ} (sigma rho Qpp1 : Fin N → ℂ) (Q0 Qpp rho_geo : Fin N → Fin N → ℂ)
    (c k : ℂ) (i j : Fin N)
    (hK1 : ∀ a b, Q0 a b = sigma a / 2 * Qpp a b + c * sigma b)
    (hQI : ∀ a b, Qpp a b = Qpp1 b)
    (hrgsymm : ∀ a b, rho_geo a b = rho_geo b a)
    (hrgprod : ∀ a b l, rho_geo a l * rho_geo b l = rho l * rho_geo a b) :
    Cmix0 (fun s => FMSA.Q0Complex.Q0_mat_c s sigma rho_geo Q0 Qpp) k i j
      = rho_geo i j * Complex.exp (-(((sigma j - sigma i) / 2) * k))
        * ((pP (sigma i) k * Qpp1 j + pQ (sigma i) k * c * sigma j)
           + (pP (sigma j) (-k) * Qpp1 i + pQ (sigma j) (-k) * c * sigma i)
           - (pP (sigma i) k * pP (sigma j) (-k) * (∑ l, rho l * Qpp1 l ^ 2)
             + c * (∑ l, rho l * (sigma l * Qpp1 l))
                 * (pP (sigma i) k * pQ (sigma j) (-k) + pQ (sigma i) k * pP (sigma j) (-k))
             + c ^ 2 * (∑ l, rho l * sigma l ^ 2) * (pQ (sigma i) k * pQ (sigma j) (-k)))) := by
  rw [Cmix0_entry_of_id_sub _ (fun s => Bbra sigma Q0 Qpp s) rho_geo k i j
        (fun s a b => Q0_mat_c_eq_id_sub sigma rho_geo Q0 Qpp s a b)]
  have hsum : ∑ l, rho_geo i l * rho_geo j l * Bbra sigma Q0 Qpp k i l * Bbra sigma Q0 Qpp (-k) j l
      = ∑ l, (rho_geo i l * rho_geo j l) * (Bbra sigma Q0 Qpp k i l * Bbra sigma Q0 Qpp (-k) j l) :=
    Finset.sum_congr rfl (fun l _ => by ring)
  rw [hsum, phys_sum sigma rho Qpp1 Q0 Qpp rho_geo c k i j hK1 hQI hrgprod,
      Bbra_sep sigma Q0 Qpp c k i j (hK1 i j),
      Bbra_sep sigma Q0 Qpp c (-k) j i (hK1 j i), hQI i j, hQI j i, hrgsymm j i]
  rw [show Complex.exp (-(((sigma i - sigma j) / 2) * (-k)))
        = Complex.exp (-(((sigma j - sigma i) / 2) * k)) from by ring_nf]
  ring

open FMSA.MRS in
/-- **The general-`N` physical swap** `Cmix0ᵢⱼ = Cmix0ⱼᵢ` (momentum-space DCF symmetry, any `N`).
`Cmix0_phys_reduce` (twice) + `ρ_geo` symmetry factor out `ρgᵢⱼ`, leaving the per-pair bracket
identity — closed by the `swap_pair_core` `field_simp;ring` inlined via `Ei = exp(kσᵢ/2)` (so
`exp(−kσᵢ) = 1/Ei²`, `exp(−λᵢⱼk) = Ei/Ej`) + KEY 2 (`Qpp1 = 2c + c²ξ₂σ`, `ξ₂ = ∑ρσ²`).
Coefficient-free given the `KEY`/`ρ_geo` relations — the general-`N` `Qphys_Cmix0_entry_symm`. -/
theorem Cmix0_phys_swap {N : ℕ} (sigma rho Qpp1 : Fin N → ℂ) (Q0 Qpp rho_geo : Fin N → Fin N → ℂ)
    (c xi2 k : ℂ) (hk : k ≠ 0)
    (hK1 : ∀ a b, Q0 a b = sigma a / 2 * Qpp a b + c * sigma b)
    (hQI : ∀ a b, Qpp a b = Qpp1 b)
    (hQpp2 : ∀ b, Qpp1 b = 2 * c + c ^ 2 * xi2 * sigma b)
    (hxi2 : xi2 = ∑ l, rho l * sigma l ^ 2)
    (hrgsymm : ∀ a b, rho_geo a b = rho_geo b a)
    (hrgprod : ∀ a b l, rho_geo a l * rho_geo b l = rho l * rho_geo a b)
    (i j : Fin N) :
    Cmix0 (fun s => FMSA.Q0Complex.Q0_mat_c s sigma rho_geo Q0 Qpp) k i j
      = Cmix0 (fun s => FMSA.Q0Complex.Q0_mat_c s sigma rho_geo Q0 Qpp) k j i := by
  rw [Cmix0_phys_reduce sigma rho Qpp1 Q0 Qpp rho_geo c k i j hK1 hQI hrgsymm hrgprod,
      Cmix0_phys_reduce sigma rho Qpp1 Q0 Qpp rho_geo c k j i hK1 hQI hrgsymm hrgprod, hrgsymm j i]
  simp only [pP, pQ, hQpp2 i, hQpp2 j, ← hxi2]
  set Ei := Complex.exp (k * sigma i / 2) with hEi
  set Ej := Complex.exp (k * sigma j / 2) with hEj
  have hEi0 : Ei ≠ 0 := Complex.exp_ne_zero _
  have hEj0 : Ej ≠ 0 := Complex.exp_ne_zero _
  have e1 : Complex.exp (-(k * sigma i)) = (Ei ^ 2)⁻¹ := by
    rw [hEi, sq, ← Complex.exp_add, ← Complex.exp_neg]; ring_nf
  have e2 : Complex.exp (k * sigma i) = Ei ^ 2 := by rw [hEi, sq, ← Complex.exp_add]; ring_nf
  have e3 : Complex.exp (-(k * sigma j)) = (Ej ^ 2)⁻¹ := by
    rw [hEj, sq, ← Complex.exp_add, ← Complex.exp_neg]; ring_nf
  have e4 : Complex.exp (k * sigma j) = Ej ^ 2 := by rw [hEj, sq, ← Complex.exp_add]; ring_nf
  have e5 : Complex.exp (-((sigma j - sigma i) / 2 * k)) = Ei * Ej⁻¹ := by
    rw [hEi, hEj, ← Complex.exp_neg, ← Complex.exp_add]; ring_nf
  have e6 : Complex.exp (-((sigma i - sigma j) / 2 * k)) = Ej * Ei⁻¹ := by
    rw [hEi, hEj, ← Complex.exp_neg, ← Complex.exp_add]; ring_nf
  simp only [neg_mul, neg_neg]
  rw [e1, e2, e3, e4, e5, e6]
  field_simp
  ring

open FMSA.MRS FMSA.Q0Complex FMSA.MatrixQ0 in
/-- The bare (unweighted) Baxter bracket `B(s)ᵢⱼ = e^{−λᵢⱼs}(Q0phys·p₁(σᵢ) + Qppphys·p₂(σᵢ))` — the
function part of `q0_entry_c`, i.e. `(δᵢⱼ − Qphys(s)ᵢⱼ)/ρ_geoᵢⱼ`. -/
noncomputable def BbarePhys (rho sigma : Fin 2 → ℝ) (s : ℂ) (i j : Fin 2) : ℂ :=
  Complex.exp (-(((sigma j : ℂ) - (sigma i : ℂ)) / 2 * s))
    * ((Q0phys rho sigma i j : ℂ)
        * ((1 - s * (sigma i : ℂ) - Complex.exp (-(s * (sigma i : ℂ)))) / s ^ 2)
      + (Qppphys rho sigma i j : ℂ)
        * ((1 - s * (sigma i : ℂ) + (s * (sigma i : ℂ)) ^ 2 / 2
              - Complex.exp (-(s * (sigma i : ℂ)))) / s ^ 3))

open FMSA.MRS FMSA.Q0Complex FMSA.MatrixQ0 in
/-- **`Qphys` has the `q0_entry_c` id-sub shape** `Qphys(s)ᵢⱼ = δᵢⱼ − ρ_geoᵢⱼ·B(s)ᵢⱼ` — by the
definition of `q0_entry_c`.  Discharges `Cmix0_entry_of_id_sub`'s `hQ` for the physical matrix. -/
theorem Qphys_id_sub (rho sigma : Fin 2 → ℝ) (s : ℂ) (a b : Fin 2) :
    Qphys sigma rho s a b
      = (if a = b then (1 : ℂ) else 0)
        - ((rhoGeoPhys rho a b : ℝ) : ℂ) * BbarePhys rho sigma s a b := by
  simp only [Qphys, Q0_mat_c, q0_entry_c, BbarePhys]; ring

open FMSA.MRS FMSA.MatrixQ0 in
/-- **Physical `Cmix0` closed form.**  `Cmix0(Qphys)(k)ᵢⱼ = ρ_geoᵢⱼ·B(k)ᵢⱼ + ρ_geoⱼᵢ·B(−k)ⱼᵢ −
∑ₗ ρ_geoᵢₗρ_geoⱼₗ·B(k)ᵢₗ·B(−k)ⱼₗ` — the momentum-side target for the weighted real-space DCF
(`Cmix0_entry_of_id_sub` at `Qphys_id_sub`). -/
theorem Cmix0_Qphys_eq (rho sigma : Fin 2 → ℝ) (k : ℂ) (i j : Fin 2) :
    Cmix0 (Qphys sigma rho) k i j
      = ((rhoGeoPhys rho i j : ℝ) : ℂ) * BbarePhys rho sigma k i j
        + ((rhoGeoPhys rho j i : ℝ) : ℂ) * BbarePhys rho sigma (-k) j i
        - ∑ l, ((rhoGeoPhys rho i l : ℝ) : ℂ) * ((rhoGeoPhys rho j l : ℝ) : ℂ)
            * BbarePhys rho sigma k i l * BbarePhys rho sigma (-k) j l :=
  Cmix0_entry_of_id_sub (Qphys sigma rho) (BbarePhys rho sigma)
    (fun a b => ((rhoGeoPhys rho a b : ℝ) : ℂ)) k i j (Qphys_id_sub rho sigma)

open FMSA.InnerDecomp FMSA.MatrixQ0 in
/-- Physical `Mix 2 0` — the HS Baxter data (`σ`/`ρ`/`Q0phys`/`Qppphys`) as a `Mix`, no Yukawa tails
(`M = 0`).  `q0MixEntry (physMix …)` is the physical real-space Baxter kernel whose transform is
`BbarePhys`. -/
noncomputable def physMix (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k) : Mix 2 0 where
  σ := sigma
  ρ := rho
  zp := fun _ _ => Fin.elim0
  cb := fun _ _ => Fin.elim0
  Q0 := Q0phys rho sigma
  Qpp := fun j => Qppphys rho sigma 0 j
  hσ := hsig

open FMSA.InnerDecomp FMSA.WHSupports FMSA.MatrixQ0 in
/-- **Step (ii) — the window Laplace transform of the physical kernel equals `BbarePhys`.**
`∫_{[λᵢⱼ,Rᵢⱼ]} e^{−st}·q0MixEntry(physMix)ᵢⱼ(t) dt = BbarePhys(s)ᵢⱼ` (`q0MixEntry_laplace_c` + the
physical field values; `Qpp` row-independence via `fin_cases`).  Since `q0MixEntry` is supported on
`[λᵢⱼ,Rᵢⱼ]`, the full-line `𝓕`/`zOfW`-transform of the kernel is this, connecting the DCF's linear
terms to the momentum closed form `Cmix0_Qphys_eq`. -/
theorem q0MixEntry_physMix_laplace (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k)
    (s : ℂ) (hs : s ≠ 0) (i j : Fin 2) :
    (∫ t in ((physMix rho sigma hsig).lam i j)..((physMix rho sigma hsig).R i j),
        Complex.exp (-(s * (t : ℂ))) * ((q0MixEntry (physMix rho sigma hsig) i j t : ℝ) : ℂ))
      = BbarePhys rho sigma s i j := by
  have hexparg : -(s * ((physMix rho sigma hsig).lam i j : ℂ))
      = -(((sigma j : ℂ) - (sigma i : ℂ)) / 2 * s) := by
    simp only [physMix, Mix.lam]; push_cast; ring
  rw [q0MixEntry_laplace_c (physMix rho sigma hsig) i j s hs, hexparg]
  simp only [physMix, BbarePhys]
  rw [show (Qppphys rho sigma 0 j : ℝ) = Qppphys rho sigma i j from by fin_cases i <;> rfl]

open FMSA.InnerDecomp FMSA.WHSupports in
/-- **Step (ii-full) — the full-line Laplace transform of the physical kernel is `BbarePhys`.**
`∫_ℝ e^{−st}·q0MixEntry(physMix)ᵢⱼ = BbarePhys(s)ᵢⱼ`, from the window form + compact support
(`setIntegral_eq_integral_of_forall_compl_eq_zero` + `integral_Icc_eq_integral_Ioc`). -/
theorem q0MixEntry_physMix_fullline (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k)
    (s : ℂ) (hs : s ≠ 0) (i j : Fin 2) :
    (∫ t, (q0MixEntry (physMix rho sigma hsig) i j t : ℂ) * Complex.exp (-(s * t)))
      = BbarePhys rho sigma s i j := by
  set X := physMix rho sigma hsig with hX
  have hle : X.lam i j ≤ X.R i j := by
    have := hsig i
    simp only [hX, physMix, Mix.lam, Mix.R]; linarith
  have hg0 : ∀ t, t ∉ Set.Icc (X.lam i j) (X.R i j) →
      (q0MixEntry X i j t : ℂ) * Complex.exp (-(s * t)) = 0 := by
    intro t ht
    have hq : q0MixEntry X i j t = 0 := by
      by_contra h
      exact ht (q0MixEntry_support_subset X i j (Function.mem_support.mpr h))
    rw [hq]; push_cast; ring
  rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hg0,
    MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]
  rw [intervalIntegral.integral_congr (g := fun t => Complex.exp (-(s * t))
      * ((q0MixEntry X i j t : ℝ) : ℂ)) (fun t _ => by ring)]
  exact q0MixEntry_physMix_laplace rho sigma hsig s hs i j

open FMSA.InnerDecomp FMSA.WHSupports in
/-- The `ρ_geo`-weighted full-line matrix correlation
`∑ₗ ∫ (ρᵢₗ·q0(i,l)(t))·(ρⱼₗ·q0(j,l)(t−v)) dt` — the double-product part of the real-space DCF. -/
noncomputable def matCorrW {M : ℕ} (X : Mix 2 M) (ρg : Fin 2 → Fin 2 → ℝ) (i j : Fin 2) (v : ℝ) :
    ℂ :=
  ∑ l, ∫ t, ((ρg i l : ℂ) * (q0MixEntry X i l t : ℂ))
              * ((ρg j l : ℂ) * (q0MixEntry X j l (t - v) : ℂ))

open FMSA.InnerDecomp FMSA.WHSupports in
/-- **Step (iii) — weighted correlation Laplace transform.**  `∫ matCorrW·e^{−zv} =
∑ₗ ρᵢₗρⱼₗ·(∫ q0(i,l)e^{−zt})·(∫ q0(j,l)e^{zs})` — `laplace_sum_eq_corr_c` with the `ρ_geo` weights
absorbed into `F l = ρᵢₗ·q0(i,l)`, `G l = ρⱼₗ·q0(j,l)`, integrability from the unweighted lemmas ×
constants, then the constants factored out.  Its RHS is the `Cmix0_Qphys_eq` double-product term
(each `∫ q0·e^{−st} = BbarePhys(s)`). -/
theorem matCorrW_laplace {M : ℕ} (X : Mix 2 M) (ρg : Fin 2 → Fin 2 → ℝ) (i j : Fin 2) (z : ℂ) :
    (∫ v, matCorrW X ρg i j v * Complex.exp (-(z * v)))
      = ∑ l, (ρg i l : ℂ) * (ρg j l : ℂ)
          * (∫ t, (q0MixEntry X i l t : ℂ) * Complex.exp (-(z * t)))
          * (∫ s, (q0MixEntry X j l s : ℂ) * Complex.exp (z * s)) := by
  set F : Fin 2 → ℝ → ℂ := fun l t => (ρg i l : ℂ) * (q0MixEntry X i l t : ℂ) with hF
  set G : Fin 2 → ℝ → ℂ := fun l t => (ρg j l : ℂ) * (q0MixEntry X j l t : ℂ) with hG
  have h3 : ∀ l : Fin 2, Integrable
      (fun v => (∫ t, F l t * G l (t - v)) * Complex.exp (-(z * v))) := by
    intro l
    have hUnw : Integrable
        (fun v => (∫ t, (q0MixEntry X i l t : ℂ) * (q0MixEntry X j l (t - v) : ℂ))
          * Complex.exp (-(z * v))) := by
      refine (q0MixEntry_corr_exp_prod_integrable X i j l z).integral_prod_right.congr
        (Filter.Eventually.of_forall (fun v => ?_))
      simp only [Function.uncurry]
      exact MeasureTheory.integral_mul_const (Complex.exp (-(z * (v : ℂ)))) _
    refine (hUnw.const_mul ((ρg i l : ℂ) * (ρg j l : ℂ))).congr
      (Filter.Eventually.of_forall (fun v => ?_))
    simp only [hF, hG]
    rw [show (fun t => (ρg i l : ℂ) * (q0MixEntry X i l t : ℂ)
            * ((ρg j l : ℂ) * (q0MixEntry X j l (t - v) : ℂ)))
          = (fun t => ((ρg i l : ℂ) * (ρg j l : ℂ))
              * ((q0MixEntry X i l t : ℂ) * (q0MixEntry X j l (t - v) : ℂ))) from by
        funext t; ring, MeasureTheory.integral_const_mul]
    ring
  have key := laplace_sum_eq_corr_c (ι := Fin 2) Finset.univ F G z
    (fun l _ => by
      have h := ((q0MixEntry_mul_exp_integrable X i l (-z)).const_mul (ρg i l : ℂ)).mul_prod
        ((q0MixEntry_mul_exp_integrable X j l z).const_mul (ρg j l : ℂ))
      refine h.congr (Filter.Eventually.of_forall (fun p => ?_))
      simp only [hF, hG, neg_mul]; ring)
    (fun l _ => by
      refine ((q0MixEntry_corr_exp_prod_integrable X i j l z).const_mul
        ((ρg i l : ℂ) * (ρg j l : ℂ))).congr (Filter.Eventually.of_forall (fun p => ?_))
      simp only [hF, hG, Function.uncurry]; ring)
    (fun l _ => h3 l)
  have hmc : (∫ v, matCorrW X ρg i j v * Complex.exp (-(z * v)))
      = ∫ v, (∑ l, ∫ t, F l t * G l (t - v)) * Complex.exp (-(z * v)) := by
    simp only [matCorrW, hF, hG]
  rw [hmc, ← key]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [show (∫ t, F l t * Complex.exp (-(z * t)))
        = (ρg i l : ℂ) * ∫ t, (q0MixEntry X i l t : ℂ) * Complex.exp (-(z * t)) from by
      rw [← MeasureTheory.integral_const_mul]; refine integral_congr_ae
        (Filter.Eventually.of_forall (fun t => ?_)); simp only [hF]; ring,
    show (∫ s, G l s * Complex.exp (z * s))
        = (ρg j l : ℂ) * ∫ s, (q0MixEntry X j l s : ℂ) * Complex.exp (z * s) from by
      rw [← MeasureTheory.integral_const_mul]; refine integral_congr_ae
        (Filter.Eventually.of_forall (fun s => ?_)); simp only [hG]; ring]
  ring

open FMSA.InnerDecomp FMSA.WHSupports FMSA.MatrixQ0 in
/-- **The correctly `ρ_geo`-weighted full-line real-space DCF** `Ĉ₀ᵢⱼ(v) = ρ_geoᵢⱼ·q0(i,j)(v) +
ρ_geoⱼᵢ·q0(j,i)(−v) − matCorrW(v)` — the function whose transform is `Cmix0(Qphys)ᵢⱼ`.  (The `q0`
linear terms jump at `v=λ`, so it is a.e.-continuous but not continuous.) -/
noncomputable def matDCFfull (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k) (i j : Fin 2)
    (v : ℝ) : ℂ :=
  (rhoGeoPhys rho i j : ℂ) * (q0MixEntry (physMix rho sigma hsig) i j v : ℂ)
    + (rhoGeoPhys rho j i : ℂ) * (q0MixEntry (physMix rho sigma hsig) j i (-v) : ℂ)
    - matCorrW (physMix rho sigma hsig) (rhoGeoPhys rho) i j v

open FMSA.InnerDecomp FMSA.WHSupports FMSA.MatrixQ0 FMSA.MRS in
/-- **Step (iv) — `𝓕(matDCFfull) = Cmix0(Qphys)`.**  `∫_ℝ matDCFfull·e^{−zv} = Cmix0(Qphys)(z)ᵢⱼ`
for `z ≠ 0` — assembles ii-full (`q0MixEntry_physMix_fullline`, the two linear terms, the reflected
one via `integral_neg_eq_self`) + `matCorrW_laplace` (double product) + `Cmix0_Qphys_eq`.  So the
real-space DCF is exactly the inverse transform of the momentum `Cmix0`. -/
theorem matDCFfull_laplace (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k)
    (z : ℂ) (hz : z ≠ 0) (i j : Fin 2) :
    (∫ v, matDCFfull rho sigma hsig i j v * Complex.exp (-(z * v)))
      = Cmix0 (Qphys sigma rho) z i j := by
  set X := physMix rho sigma hsig with hX
  have hnz : -z ≠ 0 := neg_ne_zero.mpr hz
  have iA : Integrable (fun v => (rhoGeoPhys rho i j : ℂ) * (q0MixEntry X i j v : ℂ)
      * Complex.exp (-(z * v))) :=
    ((q0MixEntry_mul_exp_integrable X i j (-z)).const_mul (rhoGeoPhys rho i j : ℂ)).congr
      (Filter.Eventually.of_forall (fun v => by simp only [neg_mul]; ring))
  have iB : Integrable (fun v => (rhoGeoPhys rho j i : ℂ) * (q0MixEntry X j i (-v) : ℂ)
      * Complex.exp (-(z * v))) :=
    (((q0MixEntry_mul_exp_integrable X j i z).comp_neg).const_mul (rhoGeoPhys rho j i : ℂ)).congr
      (Filter.Eventually.of_forall (fun v => by
        dsimp only
        rw [show z * ((-v : ℝ) : ℂ) = -(z * (v : ℂ)) from by push_cast; ring]; ring))
  have iC : Integrable (fun v => matCorrW X (rhoGeoPhys rho) i j v * Complex.exp (-(z * v))) := by
    simp only [matCorrW, Finset.sum_mul]
    refine integrable_finsetSum _ (fun l _ => ?_)
    have hUnw : Integrable (fun v => (∫ t, (q0MixEntry X i l t : ℂ)
        * (q0MixEntry X j l (t - v) : ℂ)) * Complex.exp (-(z * v))) := by
      refine (q0MixEntry_corr_exp_prod_integrable X i j l z).integral_prod_right.congr
        (Filter.Eventually.of_forall (fun v => ?_))
      simp only [Function.uncurry]
      exact MeasureTheory.integral_mul_const (Complex.exp (-(z * (v : ℂ)))) _
    refine (hUnw.const_mul ((rhoGeoPhys rho i l : ℂ) * (rhoGeoPhys rho j l : ℂ))).congr
      (Filter.Eventually.of_forall (fun v => ?_))
    dsimp only
    have hfac : (∫ t, (rhoGeoPhys rho i l : ℂ) * (q0MixEntry X i l t : ℂ)
          * ((rhoGeoPhys rho j l : ℂ) * (q0MixEntry X j l (t - v) : ℂ)))
        = (rhoGeoPhys rho i l : ℂ) * (rhoGeoPhys rho j l : ℂ)
          * ∫ t, (q0MixEntry X i l t : ℂ) * (q0MixEntry X j l (t - v) : ℂ) := by
      rw [← MeasureTheory.integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall (fun t => by ring))
    rw [hfac]; ring
  have hdist : ∀ v, matDCFfull rho sigma hsig i j v * Complex.exp (-(z * v))
      = (rhoGeoPhys rho i j : ℂ) * (q0MixEntry X i j v : ℂ) * Complex.exp (-(z * v))
        + (rhoGeoPhys rho j i : ℂ) * (q0MixEntry X j i (-v) : ℂ) * Complex.exp (-(z * v))
        - matCorrW X (rhoGeoPhys rho) i j v * Complex.exp (-(z * v)) := fun v => by
    simp only [matDCFfull, hX]; ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hdist)]
  rw [integral_sub (μ := volume)
      (f := fun a => (rhoGeoPhys rho i j : ℂ) * (q0MixEntry X i j a : ℂ) * Complex.exp (-(z * a))
          + (rhoGeoPhys rho j i : ℂ) * (q0MixEntry X j i (-a) : ℂ) * Complex.exp (-(z * a)))
      (g := fun a => matCorrW X (rhoGeoPhys rho) i j a * Complex.exp (-(z * a)))
      (iA.add iB) iC,
    integral_add iA iB]
  have t1 : (∫ v, (rhoGeoPhys rho i j : ℂ) * (q0MixEntry X i j v : ℂ) * Complex.exp (-(z * v)))
      = (rhoGeoPhys rho i j : ℂ) * BbarePhys rho sigma z i j := by
    rw [← q0MixEntry_physMix_fullline rho sigma hsig z hz i j, ← MeasureTheory.integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun v => by ring))
  have hstep : ∀ b : Fin 2, (∫ v, (q0MixEntry X j b (-v) : ℂ) * Complex.exp (-(z * v)))
      = BbarePhys rho sigma (-z) j b := by
    intro b
    rw [← q0MixEntry_physMix_fullline rho sigma hsig (-z) hnz j b]
    rw [← integral_neg_eq_self
      (fun t => (q0MixEntry X j b t : ℂ) * Complex.exp (-((-z) * t))) volume]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
    dsimp only
    rw [show -((-z) * ((-v : ℝ) : ℂ)) = -(z * (v : ℂ)) from by push_cast; ring]
  have t2 : (∫ v, (rhoGeoPhys rho j i : ℂ) * (q0MixEntry X j i (-v) : ℂ) * Complex.exp (-(z * v)))
      = (rhoGeoPhys rho j i : ℂ) * BbarePhys rho sigma (-z) j i := by
    rw [← hstep i, ← MeasureTheory.integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun v => by ring))
  have hrefl : ∀ b : Fin 2, (∫ s, (q0MixEntry X j b s : ℂ) * Complex.exp (z * s))
      = BbarePhys rho sigma (-z) j b := by
    intro b
    rw [← q0MixEntry_physMix_fullline rho sigma hsig (-z) hnz j b]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun s => ?_))
    dsimp only
    rw [show -((-z) * (s : ℂ)) = z * (s : ℂ) from by ring]
  have t3 : (∫ v, matCorrW X (rhoGeoPhys rho) i j v * Complex.exp (-(z * v)))
      = ∑ l, (rhoGeoPhys rho i l : ℂ) * (rhoGeoPhys rho j l : ℂ)
          * BbarePhys rho sigma z i l * BbarePhys rho sigma (-z) j l := by
    rw [matCorrW_laplace]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [q0MixEntry_physMix_fullline rho sigma hsig z hz i l, hrefl l]
  rw [t1, t2, t3, Cmix0_Qphys_eq]

/-! ### Step (v) — regularity + the DCF a.e.-symmetry `matDCF_ae_symm` (discharges `hCsym`).
Pointwise regularity of `matDCFfull` (integrable, a.e.-continuous), continuity of its `zOfW`
transform, and the momentum-space symmetry `Qphys_Cmix0_entry_symm` combine (via
`ae_eq_of_zOfW_transform_eq`, with the `w = 0` edge closed by density) to give `Ĉ₀ᵢⱼ = Ĉ₀ⱼᵢ`
a.e. — MML.15 obstruction (b). -/

variable {M : ℕ}

open Set FMSA.InnerDecomp FMSA.WHSupports

/-- `q0MixEntry` (cast to ℂ) is continuous away from the two support endpoints `λᵢⱼ`, `Rᵢⱼ`. -/
theorem q0MixEntry_continuousAt (X : Mix 2 M) (i j : Fin 2) {v : ℝ}
    (hlam : v ≠ X.lam i j) (hR : v ≠ X.R i j) :
    ContinuousAt (fun t => (q0MixEntry X i j t : ℂ)) v := by
  have hreal : ContinuousAt (fun t => q0MixEntry X i j t) v := by
    have hpc : ContinuousAt
        (fun r => X.Q0 i j * (r - X.R i j) + X.Qpp j * (r - X.R i j) ^ 2 / 2) v := by fun_prop
    have hzero : ContinuousAt (fun _ : ℝ => (0 : ℝ)) v := continuousAt_const
    rcases lt_trichotomy v (X.lam i j) with hlt | heq | hgt
    · refine hzero.congr ?_
      filter_upwards [Iio_mem_nhds hlt] with t ht
      have hnm : t ∉ Set.Icc (X.lam i j) (X.R i j) :=
        fun h => absurd (Set.mem_Iio.mp ht) (not_lt.mpr h.1)
      rw [q0MixEntry, Set.indicator_of_notMem hnm]
    · exact absurd heq hlam
    · rcases lt_trichotomy v (X.R i j) with h2 | h2 | h2
      · refine hpc.congr ?_
        filter_upwards [Ioo_mem_nhds hgt h2] with t ht
        rw [q0MixEntry, Set.indicator_of_mem (Set.mem_Icc.mpr ⟨le_of_lt ht.1, le_of_lt ht.2⟩)]
      · exact absurd h2 hR
      · refine hzero.congr ?_
        filter_upwards [Ioi_mem_nhds h2] with t ht
        have hnm : t ∉ Set.Icc (X.lam i j) (X.R i j) :=
          fun h => absurd (Set.mem_Ioi.mp ht) (not_lt.mpr h.2)
        rw [q0MixEntry, Set.indicator_of_notMem hnm]
  exact Complex.continuous_ofReal.continuousAt.comp hreal

open FMSA.MatrixQ0 in
/-- `matCorrW` is continuous (finite sum of `const · (continuous correlation)`). -/
theorem matCorrW_continuous (X : Mix 2 M) (ρg : Fin 2 → Fin 2 → ℝ) (i j : Fin 2) :
    Continuous (fun v => matCorrW X ρg i j v) := by
  simp only [matCorrW]
  refine continuous_finsetSum _ (fun l _ => ?_)
  have heq : (fun v => ∫ t, ((ρg i l : ℂ) * (q0MixEntry X i l t : ℂ))
        * ((ρg j l : ℂ) * (q0MixEntry X j l (t - v) : ℂ)))
      = (fun v => (ρg i l : ℂ) * (ρg j l : ℂ)
          * ∫ t, (q0MixEntry X i l t : ℂ) * (q0MixEntry X j l (t - v) : ℂ)) := by
    funext v; rw [← MeasureTheory.integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun t => by ring))
  rw [heq]
  exact continuous_const.mul (q0MixEntry_corr_continuous X i j l)

open FMSA.MatrixQ0 in
/-- `matDCFfull` is integrable (each term compactly supported/bounded). -/
theorem matDCFfull_integrable (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k) (i j : Fin 2) :
    Integrable (fun v => matDCFfull rho sigma hsig i j v) := by
  set X := physMix rho sigma hsig with hX
  have h1 : Integrable (fun v => (rhoGeoPhys rho i j : ℂ) * (q0MixEntry X i j v : ℂ)) :=
    ((memLp_one_iff_integrable.mp (q0MixEntry_memLp X i j 1))).const_mul _
  have h2 : Integrable (fun v => (rhoGeoPhys rho j i : ℂ) * (q0MixEntry X j i (-v) : ℂ)) :=
    (((memLp_one_iff_integrable.mp (q0MixEntry_memLp X j i 1)).comp_neg)).const_mul _
  have h3 : Integrable (fun v => matCorrW X (rhoGeoPhys rho) i j v) := by
    simp only [matCorrW]
    refine integrable_finsetSum _ (fun l _ => ?_)
    have := (q0MixEntry_corr_exp_prod_integrable X i j l 0).integral_prod_right
    refine (this.const_mul ((rhoGeoPhys rho i l : ℂ) * (rhoGeoPhys rho j l : ℂ))).congr
      (Filter.Eventually.of_forall (fun v => ?_))
    simp only [Function.uncurry, zero_mul, neg_zero, Complex.exp_zero, mul_one]
    rw [← MeasureTheory.integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun t => by ring))
  refine ((h1.add h2).sub h3).congr (Filter.Eventually.of_forall (fun v => ?_))
  simp only [matDCFfull, hX, Pi.add_apply, Pi.sub_apply]

open FMSA.MatrixQ0 in
/-- `matDCFfull` is a.e.-continuous — discontinuity ⊆ the finite endpoint set. -/
theorem matDCFfull_ae_continuous (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k) (i j : Fin 2) :
    ∀ᵐ v, ContinuousAt (fun v => matDCFfull rho sigma hsig i j v) v := by
  set X := physMix rho sigma hsig with hX
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null
    (t := {X.lam i j, X.R i j, -(X.lam j i), -(X.R j i)}) (fun v hv => ?_) ?_
  · by_contra hnotin
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hnotin
    obtain ⟨hne1, hne2, hne3, hne4⟩ := hnotin
    apply hv
    show ContinuousAt (fun v => matDCFfull rho sigma hsig i j v) v
    simp only [matDCFfull]
    have c1 : ContinuousAt (fun v => (rhoGeoPhys rho i j : ℂ) * (q0MixEntry X i j v : ℂ)) v :=
      continuousAt_const.mul (q0MixEntry_continuousAt X i j hne1 hne2)
    have c2 : ContinuousAt (fun v => (rhoGeoPhys rho j i : ℂ) * (q0MixEntry X j i (-v) : ℂ)) v := by
      refine continuousAt_const.mul ?_
      have hnv1 : -v ≠ X.lam j i := fun h => hne3 (by linarith)
      have hnv2 : -v ≠ X.R j i := fun h => hne4 (by linarith)
      exact (q0MixEntry_continuousAt X j i hnv1 hnv2).comp continuous_neg.continuousAt
    exact (c1.add c2).sub (matCorrW_continuous X (rhoGeoPhys rho) i j).continuousAt
  · exact (Set.toFinite _).measure_zero volume

open FMSA.MRS in
/-- The `zOfW` transform `w ↦ ∫ f·e^{−(2πi w)v}` of an integrable `f` is continuous in `w`
(dominated convergence; the kernel has unit modulus). -/
theorem zOfW_transform_continuous {f : ℝ → ℂ} (hf : Integrable f) :
    Continuous (fun w : ℝ => ∫ v, f v * Complex.exp (-(zOfW w * (v : ℂ)))) := by
  apply continuous_of_dominated (bound := fun v => ‖f v‖)
  · intro w
    refine hf.aestronglyMeasurable.mul ?_
    exact (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal).neg).aestronglyMeasurable
  · intro w
    filter_upwards with v
    rw [norm_mul, show -(zOfW w * (v : ℂ)) = ((-(2 * Real.pi * w * v) : ℝ) : ℂ) * Complex.I from by
      simp only [zOfW]; push_cast; ring, Complex.norm_exp_ofReal_mul_I, mul_one]
  · exact hf.norm
  · filter_upwards with v
    refine continuous_const.mul (Complex.continuous_exp.comp ?_)
    simp only [zOfW]; fun_prop

/-- `zOfW w = 2πiw ≠ 0` for `w ≠ 0`. -/
theorem zOfW_ne_zero {w : ℝ} (hw : w ≠ 0) : zOfW w ≠ 0 := by
  simp only [zOfW]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hw' : (w : ℂ) ≠ 0 := by exact_mod_cast hw
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hpi) hw') Complex.I_ne_zero

/-- **a.e.-symmetry from off-`0` transform equality (`N`-independent).**  If two integrable,
a.e.-continuous functions have equal `zOfW` transforms for every `w ≠ 0`, they agree a.e. — the
`w = 0` edge follows because both transforms are continuous (`zOfW_transform_continuous`) and agree
on the dense set `{0}ᶜ`.  Packages the `w=0`-edge/continuity half of `matDCF_ae_symm` as a reusable
lemma independent of `Fin 2`: for general `N`, feed it the momentum-symmetry transform equality
(off `0`) per species pair to get the full-line DCF a.e.-symmetry `Dᵢⱼ =ᵐ Dⱼᵢ`. -/
theorem ae_eq_of_zOfW_transform_offdiag {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g)
    (hcf : ∀ᵐ v, ContinuousAt f v) (hcg : ∀ᵐ v, ContinuousAt g v)
    (hoff : ∀ w : ℝ, w ≠ 0 → (∫ v, f v * Complex.exp (-(zOfW w * v)))
      = ∫ v, g v * Complex.exp (-(zOfW w * v))) :
    f =ᵐ[volume] g := by
  refine ae_eq_of_zOfW_transform_eq hf hg hcf hcg (fun w => ?_)
  have hall : (fun w : ℝ => ∫ v, f v * Complex.exp (-(zOfW w * v)))
      = (fun w : ℝ => ∫ v, g v * Complex.exp (-(zOfW w * v))) := by
    refine Continuous.ext_on (dense_compl_singleton (0 : ℝ))
      (zOfW_transform_continuous hf) (zOfW_transform_continuous hg) (fun x hx => ?_)
    exact hoff x (Set.mem_compl_singleton_iff.mp hx)
  exact congrFun hall w

open FMSA.MatrixQ0 FMSA.MRS in
/-- **Off-diagonal (`w ≠ 0`) transform symmetry.**  The `zOfW` transforms of `matDCFfull i j`
and `matDCFfull j i` coincide away from `w = 0`, straight from `matDCFfull_laplace`
+ the momentum-space DCF entry symmetry `Qphys_Cmix0_entry_symm`. -/
theorem matDCFfull_transform_offdiag (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k)
    (hρ0 : 0 ≤ rho 0) (hρ1 : 0 ≤ rho 1) (hvac : vacMix rho sigma ≠ 0) (i j : Fin 2)
    {w : ℝ} (hw : w ≠ 0) :
    (∫ v, matDCFfull rho sigma hsig i j v * Complex.exp (-(zOfW w * v)))
      = ∫ v, matDCFfull rho sigma hsig j i v * Complex.exp (-(zOfW w * v)) := by
  have hzw : zOfW w ≠ 0 := zOfW_ne_zero hw
  rw [matDCFfull_laplace rho sigma hsig (zOfW w) hzw i j,
    matDCFfull_laplace rho sigma hsig (zOfW w) hzw j i]
  exact Qphys_Cmix0_entry_symm sigma rho (zOfW w) hρ0 hρ1 hzw hvac i j

open FMSA.MatrixQ0 FMSA.MRS in
/-- **Obstruction (b), discharged: the real-space zeroth-order mixture DCF is a.e.-symmetric.**
`Ĉ₀ᵢⱼ(v) = Ĉ₀ⱼᵢ(v)` for a.e. `v` — the `hCsym` input for MML.8's collapse at unequal diameters.
Route: `ae_eq_of_zOfW_transform_eq` needs the transform equality at **every** `w`; off `w = 0` it
is `matDCFfull_transform_offdiag`, and the `w = 0` edge follows because both transforms are
continuous (`zOfW_transform_continuous`) and agree on the dense set `{0}ᶜ`. -/
theorem matDCF_ae_symm (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k)
    (hρ0 : 0 ≤ rho 0) (hρ1 : 0 ≤ rho 1) (hvac : vacMix rho sigma ≠ 0) (i j : Fin 2) :
    (fun v => matDCFfull rho sigma hsig i j v)
      =ᵐ[volume] (fun v => matDCFfull rho sigma hsig j i v) :=
  ae_eq_of_zOfW_transform_offdiag
    (matDCFfull_integrable rho sigma hsig i j) (matDCFfull_integrable rho sigma hsig j i)
    (matDCFfull_ae_continuous rho sigma hsig i j) (matDCFfull_ae_continuous rho sigma hsig j i)
    (fun _ hw => matDCFfull_transform_offdiag rho sigma hsig hρ0 hρ1 hvac i j hw)

/-! ### The a.e.-consuming shell assembly + the corrected `hfact` (MML.8 unequal-diameter).
`matShellConvAsym_symm_of_K_ae`/`matOzStar_of_asymK_ae` are the a.e. variants of the shell-symmetry
assembly (symmetry used inside `intervalIntegral.integral_congr_ae`); `matDCFreCore` is the
corrected DCF core (`Ĉ₀`, real part of `matDCFfull`, the two-linear-term object) whose a.e. symmetry
comes free from `matDCF_ae_symm`.  Capstone `matOzStar_of_matDCF_ae(_canonical)`: `MatOZStar` from
the corrected `hfact` (`ρK = Ĉ₀`) + seed + bridge, symmetry discharged internally. -/

/-- **a.e.-consuming shell-symmetry.**  The a.e. variant of `matShellConvAsym_symm_of_K`: when the
Baxter kernel `K` is symmetric only **a.e.** on the shell `(0,σ]` (`hKsym_ae`), the asymmetric shell
convolution `matShellConvAsym K Kᵀ` still collapses to the symmetric `matShellConv K` — the symmetry
is used inside `intervalIntegral.integral_congr_ae`, so a null set of exceptions (the DCF's jump at
`v = λ`) is harmless. -/
theorem matShellConvAsym_symm_of_K_ae (K G : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma r : ℝ)
    (hsigma : 0 ≤ sigma)
    (hKsym_ae : ∀ i k, ∀ᵐ u ∂volume, u ∈ Set.Ioc (0 : ℝ) sigma → K i k u = K k i u) (i j : Fin N) :
    matShellConvAsym K (fun a b => fun u => K b a u) G sigma r i j
      = matShellConv K G sigma r i j := by
  unfold matShellConvAsym matShellConv
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hKsym_ae k i] with u hu hmem
  rw [Set.uIoc_of_le hsigma] at hmem
  show K i k u * FMSA.HardSphere.oddExt (G k j) (r + u)
        + K k i u * FMSA.HardSphere.oddExt (G k j) (r - u)
      = K i k u * (FMSA.HardSphere.oddExt (G k j) (r - u) + FMSA.HardSphere.oddExt (G k j) (r + u))
  rw [hu hmem]; ring

/-- **a.e.-consuming K-shell OZ★ assembly.**  The a.e. variant of `matOzStar_of_asymK`: `MatOZStar`
from the seed's asymmetric-`K` renewal (`hclaimA`), the shell bridge (`hbridge`), and only an
**a.e.** kernel symmetry (`hKsym_ae`) — the form `matDCF_ae_symm` supplies (the full-line DCF
is symmetric only a.e., discontinuous at `v = λ`). -/
theorem matOzStar_of_asymK_ae (Psi Phi Kmat : Matrix (Fin N) (Fin N) (ℝ → ℝ)) {rho sigma : ℝ}
    (hsigma : 0 ≤ sigma)
    (hKsym_ae : ∀ i k, ∀ᵐ u ∂volume, u ∈ Set.Ioc (0 : ℝ) sigma → Kmat i k u = Kmat k i u)
    (hbridge : ∀ (i j : Fin N) (r : ℝ), 0 < r →
      r * matRadialConv Phi (fun k l => fun x => Psi k l x / x) r i j
        = matShellConv Kmat (fun k l => fun x => Psi k l x / x) sigma r i j)
    (hclaimA : ∀ (i j : Fin N) (r : ℝ), 0 < r →
      Psi i j r = r * Phi i j r
        + rho * matShellConvAsym Kmat (fun a b => fun u => Kmat b a u)
            (fun k l => fun x => Psi k l x / x) sigma r i j) :
    MatOZStar Psi Phi rho := by
  refine matOzStar_of_shellClaims_K Psi Phi Kmat hbridge (fun i j r hr => ?_)
  rw [hclaimA i j r hr,
    matShellConvAsym_symm_of_K_ae Kmat (fun k l => fun x => Psi k l x / x) sigma r hsigma
      hKsym_ae i j]

/-- **The corrected DCF core kernel** — the real part of the full-line `matDCFfull`, the object that
is genuinely (a.e.) symmetric.  This is the `Ĉ₀` the "corrected `hfact`" refers to (`seed-output =
Ĉ₀` with the two linear `q̂` terms **included**), replacing the false windowed `matSelfConv`. -/
noncomputable def matDCFreCore (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k) (i j : Fin 2)
    (v : ℝ) : ℝ :=
  (matDCFfull rho sigma hsig i j v).re

open FMSA.MatrixQ0 in
/-- **The corrected DCF core is a.e.-symmetric** — `Ĉ₀ᵢⱼ(v) = Ĉ₀ⱼᵢ(v)` a.e., inherited directly from
`matDCF_ae_symm` by taking real parts.  This is the correct symmetric object (the false windowed
`matSelfConv`/single-linear `K` is not symmetric even a.e.; only this full-line two-linear-term
object is). -/
theorem matDCFreCore_ae_symm (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k)
    (hρ0 : 0 ≤ rho 0) (hρ1 : 0 ≤ rho 1) (hvac : vacMix rho sigma ≠ 0) (i j : Fin 2) :
    (fun v => matDCFreCore rho sigma hsig i j v)
      =ᵐ[volume] (fun v => matDCFreCore rho sigma hsig j i v) := by
  filter_upwards [matDCF_ae_symm rho sigma hsig hρ0 hρ1 hvac i j] with v hv
  simp only [matDCFreCore, hv]

open FMSA.MatrixQ0 in
/-- **CAPSTONE — MML.8 unequal-diameter collapse from the corrected `hfact` + `matDCF_ae_symm`, with
NO symmetry hypothesis.**  Given the corrected factorization `hKdcf` (`ρ·Kᵢₖ = Ĉ₀ᵢₖ` =
`matDCFreCore`, the DCF core with the linear terms) plus the seed's asymmetric-`K` renewal
(`hclaimA`) and the shell bridge (`hbridge`), `MatOZStar` holds — the required kernel symmetry is
discharged **internally** from `matDCF_ae_symm` (a.e. symmetry of the full-line DCF).  The last
inputs are exactly `hbridge` (provable, `matRadialConv_eq_matShellConv`) and `hclaimA` (the
corrected seed); the symmetry obstruction is gone. -/
theorem matOzStar_of_matDCF_ae (Psi Phi Kmat : Matrix (Fin 2) (Fin 2) (ℝ → ℝ))
    (rhoV sigmaV : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigmaV k)
    (hρ0 : 0 ≤ rhoV 0) (hρ1 : 0 ≤ rhoV 1) (hvac : vacMix rhoV sigmaV ≠ 0)
    {rho sigmaS : ℝ} (hrho : rho ≠ 0) (hsigmaS : 0 ≤ sigmaS)
    (hKdcf : ∀ i k, ∀ᵐ u ∂volume, u ∈ Set.Ioc (0 : ℝ) sigmaS →
      rho * Kmat i k u = matDCFreCore rhoV sigmaV hsig i k u)
    (hbridge : ∀ (i j : Fin 2) (r : ℝ), 0 < r →
      r * matRadialConv Phi (fun k l => fun x => Psi k l x / x) r i j
        = matShellConv Kmat (fun k l => fun x => Psi k l x / x) sigmaS r i j)
    (hclaimA : ∀ (i j : Fin 2) (r : ℝ), 0 < r →
      Psi i j r = r * Phi i j r
        + rho * matShellConvAsym Kmat (fun a b => fun u => Kmat b a u)
            (fun k l => fun x => Psi k l x / x) sigmaS r i j) :
    MatOZStar Psi Phi rho := by
  refine matOzStar_of_asymK_ae Psi Phi Kmat hsigmaS (fun i k => ?_) hbridge hclaimA
  filter_upwards [hKdcf i k, hKdcf k i, matDCFreCore_ae_symm rhoV sigmaV hsig hρ0 hρ1 hvac i k]
    with u h1 h2 h3
  intro hmem
  have hmul : rho * Kmat i k u = rho * Kmat k i u := by rw [h1 hmem, h3, ← h2 hmem]
  exact mul_left_cancel₀ hrho hmul

open FMSA.MatrixQ0 in
/-- **CANONICAL form — the corrected `hfact` is DISCHARGED for the natural kernel `Kmat = Ĉ₀/ρ`.**
With the Baxter kernel taken to be the corrected DCF core itself (`matDCFreCore/ρ`), the `hKdcf`
identity is `ρ·(Ĉ₀/ρ) = Ĉ₀`, trivially true, so it drops out.  The ONLY remaining inputs to the
unequal-diameter `MatOZStar` are the shell bridge `hbridge` (provable) and the corrected seed
`hclaimA` — the symmetry obstruction (b) is fully gone. -/
theorem matOzStar_of_matDCF_ae_canonical (Psi Phi : Matrix (Fin 2) (Fin 2) (ℝ → ℝ))
    (rhoV sigmaV : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigmaV k)
    (hρ0 : 0 ≤ rhoV 0) (hρ1 : 0 ≤ rhoV 1) (hvac : vacMix rhoV sigmaV ≠ 0)
    {rho sigmaS : ℝ} (hrho : rho ≠ 0) (hsigmaS : 0 ≤ sigmaS)
    (hbridge : ∀ (i j : Fin 2) (r : ℝ), 0 < r →
      r * matRadialConv Phi (fun k l => fun x => Psi k l x / x) r i j
        = matShellConv (fun i k u => matDCFreCore rhoV sigmaV hsig i k u / rho)
            (fun k l => fun x => Psi k l x / x) sigmaS r i j)
    (hclaimA : ∀ (i j : Fin 2) (r : ℝ), 0 < r →
      Psi i j r = r * Phi i j r
        + rho * matShellConvAsym (fun i k u => matDCFreCore rhoV sigmaV hsig i k u / rho)
            (fun a b => fun u => matDCFreCore rhoV sigmaV hsig b a u / rho)
            (fun k l => fun x => Psi k l x / x) sigmaS r i j) :
    MatOZStar Psi Phi rho := by
  refine matOzStar_of_matDCF_ae Psi Phi
    (fun i k u => matDCFreCore rhoV sigmaV hsig i k u / rho) rhoV sigmaV hsig hρ0 hρ1 hvac
    hrho hsigmaS (fun i k => ?_) hbridge hclaimA
  filter_upwards with u _
  rw [mul_div_cancel₀ _ hrho]

/-! ### Convolution theorem for the shell operators (the transport machinery).
`laplace_shift` (translation: `∫ g(r+u)e^{−zr} = e^{zu}∫ g e^{−zr}`) turns each `r±u` sample in a
shell operator into an `e^{±zu}` symbol factor; `foldShell_laplace` assembles this (Fubini + shift)
into `𝓕[∑ₖ∫ Dₖ(v)Ψₖ(r+v)] = ∑ₖ(∫ Dₖ e^{zv})·Ψ̂ₖ` — a multiplication operator on `Ψ̂` whose symbol is
the full-line DCF (by the linchpin below). -/

/-- **Translation theorem for the bilateral-Laplace / `zOfW` transform.**  Shifting the argument by
`u` multiplies the transform by `e^{zu}`:  `∫ g(r+u)·e^{−zr} = e^{zu}·∫ g(r)·e^{−zr}`.  The core
of the convolution theorem for the shell operators (`matShellConv`/`matShellConvAsym` sample `Ψ` at
`r±u`, so their transform picks up `e^{±zu}` factors — turning the shell integral into a momentum
symbol acting on `Ψ̂`).  Pure change of variables (`integral_add_right_eq_self`); no integrability
needed (translation invariance of Lebesgue measure). -/
theorem laplace_shift (g : ℝ → ℂ) (u : ℝ) (z : ℂ) :
    (∫ r, g (r + u) * Complex.exp (-(z * (r : ℂ))))
      = Complex.exp (z * (u : ℂ)) * ∫ r, g r * Complex.exp (-(z * (r : ℂ))) := by
  have hsubst : (∫ r, g (r + u) * Complex.exp (-(z * (r : ℂ))))
      = ∫ r, (fun s => g s * Complex.exp (-(z * ((s : ℂ) - (u : ℂ))))) (r + u) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun r => ?_))
    simp only
    rw [show ((r + u : ℝ) : ℂ) - (u : ℂ) = (r : ℂ) from by push_cast; ring]
  rw [hsubst, integral_add_right_eq_self (fun s => g s * Complex.exp (-(z * ((s : ℂ) - (u : ℂ))))),
    ← MeasureTheory.integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun r => ?_))
  dsimp only
  rw [show -(z * ((r : ℂ) - (u : ℂ))) = z * (u : ℂ) + -(z * (r : ℂ)) from by ring, Complex.exp_add]
  ring

/-- **Reflected translation** — `∫ g(r−u)·e^{−zr} = e^{−zu}·∫ g(r)·e^{−zr}` (the `r−u` arm),
`laplace_shift` at `−u`. -/
theorem laplace_shift_neg (g : ℝ → ℂ) (u : ℝ) (z : ℂ) :
    (∫ r, g (r - u) * Complex.exp (-(z * (r : ℂ))))
      = Complex.exp (-(z * (u : ℂ))) * ∫ r, g r * Complex.exp (-(z * (r : ℂ))) := by
  have h := laplace_shift g (-u) z
  simp only [sub_eq_add_neg, Complex.ofReal_neg, mul_neg] at h ⊢
  rw [h]

/-- **Shell-operator transform — the convolution theorem for the folded shell.**  The
`zOfW`-transform (in `r`) of the folded shell `∑ₖ ∫ Dₖ(v)·Ψₖ(r+v) dv` is the momentum **symbol**
`∑ₖ (∫ Dₖ·e^{zv})` times `Ψ̂ₖ`: the shell integral becomes a multiplication operator on `Ψ̂` (via
Fubini + `laplace_shift`).  This turns the seed's real-space shell (windowed, asymmetric) into the
momentum product `(I − Ĉ₀)·Ψ̂` — dissolving the windowed↔full-line gap: only the **symbol** `∫
Dₖ·e^{zv}` matters, and by `Qphys_prod_eq_one_sub_dcf_transform` it is the full-line DCF symbol. -/
theorem foldShell_laplace {N : ℕ} (D Psi : Fin N → ℝ → ℂ) (z : ℂ)
    (hjoint : ∀ k, Integrable
      (Function.uncurry fun v r => D k v * Psi k (r + v) * Complex.exp (-(z * (r : ℂ))))
      (volume.prod volume))
    (hsum : ∀ k, Integrable
      (fun r => (∫ v, D k v * Psi k (r + v)) * Complex.exp (-(z * (r : ℂ))))) :
    (∫ r, (∑ k, ∫ v, D k v * Psi k (r + v)) * Complex.exp (-(z * (r : ℂ))))
      = ∑ k, (∫ v, D k v * Complex.exp (z * (v : ℂ)))
          * ∫ r, Psi k r * Complex.exp (-(z * (r : ℂ))) := by
  have hstep : ∀ r : ℝ, (∑ k, ∫ v, D k v * Psi k (r + v)) * Complex.exp (-(z * (r : ℂ)))
      = ∑ k, (∫ v, D k v * Psi k (r + v)) * Complex.exp (-(z * (r : ℂ))) := by
    intro r; rw [Finset.sum_mul]
  rw [integral_congr_ae (Filter.Eventually.of_forall hstep),
    integral_finsetSum _ (fun k _ => hsum k)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  -- push e^{-zr} into the inner ∫v, then Fubini swap, then laplace_shift
  have h1 : (∫ r, (∫ v, D k v * Psi k (r + v)) * Complex.exp (-(z * (r : ℂ))))
      = ∫ r, ∫ v, D k v * Psi k (r + v) * Complex.exp (-(z * (r : ℂ))) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun r => ?_))
    dsimp only
    rw [← MeasureTheory.integral_mul_const]
  rw [h1, ← MeasureTheory.integral_integral_swap (hjoint k)]
  -- inner: ∫r, D k v * Psi k (r+v) * e^{-zr} = D k v * e^{zv} * Ψ̂
  have h2 : ∀ v : ℝ, (∫ r, D k v * Psi k (r + v) * Complex.exp (-(z * (r : ℂ))))
      = (D k v * Complex.exp (z * (v : ℂ))) * ∫ r, Psi k r * Complex.exp (-(z * (r : ℂ))) := by
    intro v
    have := laplace_shift (Psi k) v z
    calc (∫ r, D k v * Psi k (r + v) * Complex.exp (-(z * (r : ℂ))))
        = D k v * ∫ r, Psi k (r + v) * Complex.exp (-(z * (r : ℂ))) := by
          rw [← MeasureTheory.integral_const_mul]
          refine integral_congr_ae (Filter.Eventually.of_forall (fun r => ?_)); ring
      _ = D k v * (Complex.exp (z * (v : ℂ)) * ∫ r, Psi k r * Complex.exp (-(z * (r : ℂ)))) := by
          rw [this]
      _ = (D k v * Complex.exp (z * (v : ℂ))) * ∫ r, Psi k r * Complex.exp (-(z * (r : ℂ))) := by
          ring
  rw [integral_congr_ae (Filter.Eventually.of_forall h2), MeasureTheory.integral_mul_const]

/-! ### Fourier/factorization route — the momentum linchpin dissolving windowed↔full-line.
The seed's operator `Ψ ⋆ Q₊ ⋆ Q₋` has momentum symbol `Q̂₀(z)·Q̂₀ᵀ(−z) = I − Ĉ₀` (factorization);
since `matDCFfull`'s transform IS `Ĉ₀ = Cmix0` (`matDCFfull_laplace`), the seed equals `Ψ − Ψ ⋆
matDCFfull` — OZ★ with the full-line a.e.-symmetric DCF, dissolving the windowed↔full-line gap.
-/

open FMSA.MRS Matrix in
/-- **Momentum factorization via the full-line DCF transform — the Fourier-route linchpin.**  The
Baxter-factor product `T₀ = Q̂₀(z)·Q̂₀ᵀ(−z)` equals `I` minus the (bilateral-Laplace) transform of
the full-line real-space DCF `matDCFfull` (`(Q̂₀·Q̂₀ᵀ(−z))ᵢⱼ = δᵢⱼ − ∫_ℝ matDCFfullᵢⱼ(v)e^{−zv}`).
Combines `Cmix0_factorization` (`Q̂₀(z)·Q̂₀ᵀ(−z) = I − Ĉ₀(z)`) with `matDCFfull_laplace`
(`∫ matDCFfull·e^{−zv} = Ĉ₀(z) = Cmix0`, step (iv)).  This is the momentum content of the real-space
operator identity `Q₊ ⋆ Q₋ = δ·I − matDCFfull`: the seed's `Ψ ⋆ Q₊ ⋆ Q₋` therefore equals
`Ψ − Ψ ⋆ matDCFfull`, i.e. OZ★ with the **full-line, a.e.-symmetric** DCF `matDCFfull`
(`matDCF_ae_symm`) — dissolving the windowed↔full-line gap at the transform level. -/
theorem Qphys_prod_eq_one_sub_dcf_transform (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k)
    (z : ℂ) (hz : z ≠ 0) (i j : Fin 2) :
    (Qphys sigma rho z * (Qphys sigma rho (-z))ᵀ) i j
      = (1 : Matrix (Fin 2) (Fin 2) ℂ) i j
        - (∫ v, (matDCFfull rho sigma hsig i j v) * Complex.exp (-(z * v))) := by
  have h := congrFun (congrFun (Cmix0_factorization (Qphys sigma rho) z) i) j
  rw [Matrix.sub_apply, ← matDCFfull_laplace rho sigma hsig z hz i j] at h
  exact h

open FMSA.MRS in
open scoped Matrix in
/-- **Extended (full-line) DCF shell operator = multiplication by the DCF symbol.**  With the
FULL-LINE kernel `matDCFfull` (the fix for the `[0,σ]`-windowing loss: it integrates the Baxter
factor over its true support via `matCorrW`, dropping no sub-zero tail), the shell operator
`∑ₖ ∫_ℝ matDCFfullᵢₖ(v)·Ψₖ(r+v) dv` transforms in `r` to `∑ₖ Cmix0(Qphys)(−z)ᵢₖ · Ψ̂ₖ(z)`.
Route: `foldShell_laplace` gives `∑ₖ (∫ matDCFfullᵢₖ·e^{zv})·Ψ̂ₖ`, then `matDCFfull_laplace`
identifies each symbol `= Cmix0(−z)ᵢₖ`.  So the extended seed operator IS the OZ★ DCF convolution,
symbol `Cmix0` (a.e.-symmetric by `matDCF_ae_symm`) — closing the symbol identity the windowed seed
could not. -/
theorem matDCFfull_shell_laplace (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k) (z : ℂ)
    (hz : z ≠ 0) (Psi : Fin 2 → ℝ → ℂ) (i : Fin 2)
    (hjoint : ∀ k, Integrable
      (Function.uncurry fun v r =>
        (matDCFfull rho sigma hsig i k v) * Psi k (r + v) * Complex.exp (-(z * (r : ℂ))))
      (volume.prod volume))
    (hsum : ∀ k, Integrable
      (fun r => (∫ v, (matDCFfull rho sigma hsig i k v) * Psi k (r + v))
        * Complex.exp (-(z * (r : ℂ))))) :
    (∫ r, (∑ k, ∫ v, (matDCFfull rho sigma hsig i k v) * Psi k (r + v))
        * Complex.exp (-(z * (r : ℂ))))
      = ∑ k, Cmix0 (Qphys sigma rho) (-z) i k * ∫ r, Psi k r * Complex.exp (-(z * (r : ℂ))) := by
  rw [foldShell_laplace (fun k => matDCFfull rho sigma hsig i k) Psi z hjoint hsum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  congr 1
  have hlap := matDCFfull_laplace rho sigma hsig (-z) (neg_ne_zero.mpr hz) i k
  rw [← hlap]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
  dsimp only
  rw [show z * (v : ℂ) = -((-z) * (v : ℂ)) from by ring]


/-! ### General-`N` port of the full-line DCF a.e.-symmetry infrastructure.
The `Fin 2` `matDCFfull` machinery (`physMix`/`matCorrW`/`matDCFfull` + Laplace transform +
regularity + `matDCF_ae_symm`) lifted to arbitrary component count `N`.  The momentum-space
symmetry is discharged by the general-`N` `Cmix0_phys_swap` (rank-2 KEY relations), and the
windowed↔full-line bridge by `Cmix0_entry_of_id_sub` + `Q0_mat_c_eq_id_sub` (both general `N`),
bypassing the `Fin 2`-only `Cmix0_Qphys_eq`. -/

section GeneralNDCF

open FMSA.InnerDecomp FMSA.WHSupports FMSA.MatrixQ0 FMSA.MRS

variable {N : ℕ}

/-- General-N physical Mix (M=0, no Yukawa tails). -/
noncomputable def physMixN (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k) : Mix N 0 where
  σ := sigma
  ρ := rho
  zp := fun _ _ => Fin.elim0
  cb := fun _ _ => Fin.elim0
  Q0 := Q0phys rho sigma
  Qpp := fun j => Qppphys rho sigma j j
  hσ := hsig

/-- **`M=0` bridge — the physical `Mix N 0` forgets to the HS-layer `physHSMixN`.**  `physMixN` is the
`M=0` lift of the pure hard-sphere `FMSA.HSMix.physHSMixN` (`HSMixture/PhysHSMix.lean`); dropping the
trivial Yukawa tail via `toHSMix` recovers it, definitionally. -/
theorem physMixN_toHSMix (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k) :
    (physMixN rho sigma hsig).toHSMix = FMSA.HSMix.physHSMixN rho sigma hsig := rfl

/-- **`M=0` bridge for the binary mixture** — `physMix.toHSMix = physHSMix`, definitionally. -/
theorem physMix_toHSMix (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k) :
    (physMix rho sigma hsig).toHSMix = FMSA.HSMix.physHSMix rho sigma hsig := rfl

/-- General-N kernel window Laplace transform = the Bbra bracket. -/
theorem q0MixEntry_physMixN_laplace (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k)
    (s : ℂ) (hs : s ≠ 0) (i j : Fin N) :
    (∫ t in ((physMixN rho sigma hsig).lam i j)..((physMixN rho sigma hsig).R i j),
        Complex.exp (-(s * (t : ℂ))) * ((q0MixEntry (physMixN rho sigma hsig) i j t : ℝ) : ℂ))
      = Bbra (fun a => (sigma a : ℂ)) (fun a b => (Q0phys rho sigma a b : ℂ))
          (fun a b => (Qppphys rho sigma a b : ℂ)) s i j := by
  rw [q0MixEntry_laplace_c (physMixN rho sigma hsig) i j s hs]
  simp only [physMixN, Mix.lam, Bbra]
  rw [show (Qppphys rho sigma j j : ℝ) = Qppphys rho sigma i j from rfl]
  congr 1
  congr 1
  push_cast; ring

/-- General-N kernel full-line Laplace transform = Bbra. -/
theorem q0MixEntry_physMixN_fullline (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k)
    (s : ℂ) (hs : s ≠ 0) (i j : Fin N) :
    (∫ t, (q0MixEntry (physMixN rho sigma hsig) i j t : ℂ) * Complex.exp (-(s * t)))
      = Bbra (fun a => (sigma a : ℂ)) (fun a b => (Q0phys rho sigma a b : ℂ))
          (fun a b => (Qppphys rho sigma a b : ℂ)) s i j := by
  set X := physMixN rho sigma hsig with hX
  have hle : X.lam i j ≤ X.R i j := by
    have := hsig i; simp only [hX, physMixN, Mix.lam, Mix.R]; linarith
  have hg0 : ∀ t, t ∉ Set.Icc (X.lam i j) (X.R i j) →
      (q0MixEntry X i j t : ℂ) * Complex.exp (-(s * t)) = 0 := by
    intro t ht
    have hq : q0MixEntry X i j t = 0 := by
      by_contra h; exact ht (q0MixEntry_support_subset X i j (Function.mem_support.mpr h))
    rw [hq]; push_cast; ring
  rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hg0,
    MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]
  rw [intervalIntegral.integral_congr (g := fun t => Complex.exp (-(s * t))
      * ((q0MixEntry X i j t : ℝ) : ℂ)) (fun t _ => by ring)]
  exact q0MixEntry_physMixN_laplace rho sigma hsig s hs i j


noncomputable def matCorrWN {M : ℕ} (X : Mix N M) (ρg : Fin N → Fin N → ℝ) (i j : Fin N)
    (v : ℝ) : ℂ :=
  ∑ l, ∫ t, ((ρg i l : ℂ) * (q0MixEntry X i l t : ℂ))
              * ((ρg j l : ℂ) * (q0MixEntry X j l (t - v) : ℂ))

theorem matCorrWN_laplace {M : ℕ} (X : Mix N M) (ρg : Fin N → Fin N → ℝ) (i j : Fin N) (z : ℂ) :
    (∫ v, matCorrWN X ρg i j v * Complex.exp (-(z * v)))
      = ∑ l, (ρg i l : ℂ) * (ρg j l : ℂ)
          * (∫ t, (q0MixEntry X i l t : ℂ) * Complex.exp (-(z * t)))
          * (∫ s, (q0MixEntry X j l s : ℂ) * Complex.exp (z * s)) := by
  set F : Fin N → ℝ → ℂ := fun l t => (ρg i l : ℂ) * (q0MixEntry X i l t : ℂ) with hF
  set G : Fin N → ℝ → ℂ := fun l t => (ρg j l : ℂ) * (q0MixEntry X j l t : ℂ) with hG
  have h3 : ∀ l : Fin N, Integrable
      (fun v => (∫ t, F l t * G l (t - v)) * Complex.exp (-(z * v))) := by
    intro l
    have hUnw : Integrable
        (fun v => (∫ t, (q0MixEntry X i l t : ℂ) * (q0MixEntry X j l (t - v) : ℂ))
          * Complex.exp (-(z * v))) := by
      refine (q0MixEntry_corr_exp_prod_integrable X i j l z).integral_prod_right.congr
        (Filter.Eventually.of_forall (fun v => ?_))
      simp only [Function.uncurry]
      exact MeasureTheory.integral_mul_const (Complex.exp (-(z * (v : ℂ)))) _
    refine (hUnw.const_mul ((ρg i l : ℂ) * (ρg j l : ℂ))).congr
      (Filter.Eventually.of_forall (fun v => ?_))
    simp only [hF, hG]
    rw [show (fun t => (ρg i l : ℂ) * (q0MixEntry X i l t : ℂ)
            * ((ρg j l : ℂ) * (q0MixEntry X j l (t - v) : ℂ)))
          = (fun t => ((ρg i l : ℂ) * (ρg j l : ℂ))
              * ((q0MixEntry X i l t : ℂ) * (q0MixEntry X j l (t - v) : ℂ))) from by
        funext t; ring, MeasureTheory.integral_const_mul]
    ring
  have key := laplace_sum_eq_corr_c (ι := Fin N) Finset.univ F G z
    (fun l _ => by
      have h := ((q0MixEntry_mul_exp_integrable X i l (-z)).const_mul (ρg i l : ℂ)).mul_prod
        ((q0MixEntry_mul_exp_integrable X j l z).const_mul (ρg j l : ℂ))
      refine h.congr (Filter.Eventually.of_forall (fun p => ?_))
      simp only [hF, hG, neg_mul]; ring)
    (fun l _ => by
      refine ((q0MixEntry_corr_exp_prod_integrable X i j l z).const_mul
        ((ρg i l : ℂ) * (ρg j l : ℂ))).congr (Filter.Eventually.of_forall (fun p => ?_))
      simp only [hF, hG, Function.uncurry]; ring)
    (fun l _ => h3 l)
  have hmc : (∫ v, matCorrWN X ρg i j v * Complex.exp (-(z * v)))
      = ∫ v, (∑ l, ∫ t, F l t * G l (t - v)) * Complex.exp (-(z * v)) := by
    simp only [matCorrWN, hF, hG]
  rw [hmc, ← key]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [show (∫ t, F l t * Complex.exp (-(z * t)))
        = (ρg i l : ℂ) * ∫ t, (q0MixEntry X i l t : ℂ) * Complex.exp (-(z * t)) from by
      rw [← MeasureTheory.integral_const_mul]; refine integral_congr_ae
        (Filter.Eventually.of_forall (fun t => ?_)); simp only [hF]; ring,
    show (∫ s, G l s * Complex.exp (z * s))
        = (ρg j l : ℂ) * ∫ s, (q0MixEntry X j l s : ℂ) * Complex.exp (z * s) from by
      rw [← MeasureTheory.integral_const_mul]; refine integral_congr_ae
        (Filter.Eventually.of_forall (fun s => ?_)); simp only [hG]; ring]
  ring


/-- General-N physical Q̂₀ (Q0_mat_c with physical coeffs, cast). -/
noncomputable def QphysN (rho sigma : Fin N → ℝ) (s : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  FMSA.Q0Complex.Q0_mat_c s (fun a => (sigma a : ℂ))
    (fun a b => (rhoGeoPhys rho a b : ℂ)) (fun a b => (Q0phys rho sigma a b : ℂ))
    (fun a b => (Qppphys rho sigma a b : ℂ))

/-- General-N real-space full-line DCF. -/
noncomputable def matDCFfullN (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k) (i j : Fin N)
    (v : ℝ) : ℂ :=
  (rhoGeoPhys rho i j : ℂ) * (q0MixEntry (physMixN rho sigma hsig) i j v : ℂ)
    + (rhoGeoPhys rho j i : ℂ) * (q0MixEntry (physMixN rho sigma hsig) j i (-v) : ℂ)
    - matCorrWN (physMixN rho sigma hsig) (rhoGeoPhys rho) i j v

theorem matDCFfullN_laplace (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k)
    (z : ℂ) (hz : z ≠ 0) (i j : Fin N) :
    (∫ v, matDCFfullN rho sigma hsig i j v * Complex.exp (-(z * v)))
      = Cmix0 (QphysN rho sigma) z i j := by
  set X := physMixN rho sigma hsig with hX
  have hnz : -z ≠ 0 := neg_ne_zero.mpr hz
  have iA : Integrable (fun v => (rhoGeoPhys rho i j : ℂ) * (q0MixEntry X i j v : ℂ)
      * Complex.exp (-(z * v))) :=
    ((q0MixEntry_mul_exp_integrable X i j (-z)).const_mul (rhoGeoPhys rho i j : ℂ)).congr
      (Filter.Eventually.of_forall (fun v => by simp only [neg_mul]; ring))
  have iB : Integrable (fun v => (rhoGeoPhys rho j i : ℂ) * (q0MixEntry X j i (-v) : ℂ)
      * Complex.exp (-(z * v))) :=
    (((q0MixEntry_mul_exp_integrable X j i z).comp_neg).const_mul (rhoGeoPhys rho j i : ℂ)).congr
      (Filter.Eventually.of_forall (fun v => by
        dsimp only
        rw [show z * ((-v : ℝ) : ℂ) = -(z * (v : ℂ)) from by push_cast; ring]; ring))
  have iC : Integrable (fun v => matCorrWN X (rhoGeoPhys rho) i j v * Complex.exp (-(z * v))) := by
    simp only [matCorrWN, Finset.sum_mul]
    refine integrable_finsetSum _ (fun l _ => ?_)
    have hUnw : Integrable (fun v => (∫ t, (q0MixEntry X i l t : ℂ)
        * (q0MixEntry X j l (t - v) : ℂ)) * Complex.exp (-(z * v))) := by
      refine (q0MixEntry_corr_exp_prod_integrable X i j l z).integral_prod_right.congr
        (Filter.Eventually.of_forall (fun v => ?_))
      simp only [Function.uncurry]
      exact MeasureTheory.integral_mul_const (Complex.exp (-(z * (v : ℂ)))) _
    refine (hUnw.const_mul ((rhoGeoPhys rho i l : ℂ) * (rhoGeoPhys rho j l : ℂ))).congr
      (Filter.Eventually.of_forall (fun v => ?_))
    dsimp only
    have hfac : (∫ t, (rhoGeoPhys rho i l : ℂ) * (q0MixEntry X i l t : ℂ)
          * ((rhoGeoPhys rho j l : ℂ) * (q0MixEntry X j l (t - v) : ℂ)))
        = (rhoGeoPhys rho i l : ℂ) * (rhoGeoPhys rho j l : ℂ)
          * ∫ t, (q0MixEntry X i l t : ℂ) * (q0MixEntry X j l (t - v) : ℂ) := by
      rw [← MeasureTheory.integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall (fun t => by ring))
    rw [hfac]; ring
  have hdist : ∀ v, matDCFfullN rho sigma hsig i j v * Complex.exp (-(z * v))
      = (rhoGeoPhys rho i j : ℂ) * (q0MixEntry X i j v : ℂ) * Complex.exp (-(z * v))
        + (rhoGeoPhys rho j i : ℂ) * (q0MixEntry X j i (-v) : ℂ) * Complex.exp (-(z * v))
        - matCorrWN X (rhoGeoPhys rho) i j v * Complex.exp (-(z * v)) := fun v => by
    simp only [matDCFfullN, hX]; ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hdist)]
  rw [integral_sub (μ := volume)
      (f := fun a => (rhoGeoPhys rho i j : ℂ) * (q0MixEntry X i j a : ℂ) * Complex.exp (-(z * a))
          + (rhoGeoPhys rho j i : ℂ) * (q0MixEntry X j i (-a) : ℂ) * Complex.exp (-(z * a)))
      (g := fun a => matCorrWN X (rhoGeoPhys rho) i j a * Complex.exp (-(z * a)))
      (iA.add iB) iC,
    integral_add iA iB]
  have t1 : (∫ v, (rhoGeoPhys rho i j : ℂ) * (q0MixEntry X i j v : ℂ) * Complex.exp (-(z * v)))
      = (rhoGeoPhys rho i j : ℂ) * Bbra (fun a => (sigma a : ℂ))
          (fun a b => (Q0phys rho sigma a b : ℂ)) (fun a b => (Qppphys rho sigma a b : ℂ))
          z i j := by
    rw [← q0MixEntry_physMixN_fullline rho sigma hsig z hz i j, ← MeasureTheory.integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun v => by ring))
  have hstep : ∀ b : Fin N, (∫ v, (q0MixEntry X j b (-v) : ℂ) * Complex.exp (-(z * v)))
      = Bbra (fun a => (sigma a : ℂ)) (fun a b => (Q0phys rho sigma a b : ℂ))
          (fun a b => (Qppphys rho sigma a b : ℂ)) (-z) j b := by
    intro b
    rw [← q0MixEntry_physMixN_fullline rho sigma hsig (-z) hnz j b]
    rw [← integral_neg_eq_self
      (fun t => (q0MixEntry X j b t : ℂ) * Complex.exp (-((-z) * t))) volume]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
    dsimp only
    rw [show -((-z) * ((-v : ℝ) : ℂ)) = -(z * (v : ℂ)) from by push_cast; ring]
  have t2 : (∫ v, (rhoGeoPhys rho j i : ℂ) * (q0MixEntry X j i (-v) : ℂ) * Complex.exp (-(z * v)))
      = (rhoGeoPhys rho j i : ℂ) * Bbra (fun a => (sigma a : ℂ))
          (fun a b => (Q0phys rho sigma a b : ℂ)) (fun a b => (Qppphys rho sigma a b : ℂ))
          (-z) j i := by
    rw [← hstep i, ← MeasureTheory.integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun v => by ring))
  have hrefl : ∀ b : Fin N, (∫ s, (q0MixEntry X j b s : ℂ) * Complex.exp (z * s))
      = Bbra (fun a => (sigma a : ℂ)) (fun a b => (Q0phys rho sigma a b : ℂ))
          (fun a b => (Qppphys rho sigma a b : ℂ)) (-z) j b := by
    intro b
    rw [← q0MixEntry_physMixN_fullline rho sigma hsig (-z) hnz j b]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun s => ?_))
    dsimp only
    rw [show -((-z) * (s : ℂ)) = z * (s : ℂ) from by ring]
  have t3 : (∫ v, matCorrWN X (rhoGeoPhys rho) i j v * Complex.exp (-(z * v)))
      = ∑ l, (rhoGeoPhys rho i l : ℂ) * (rhoGeoPhys rho j l : ℂ)
          * Bbra (fun a => (sigma a : ℂ)) (fun a b => (Q0phys rho sigma a b : ℂ))
              (fun a b => (Qppphys rho sigma a b : ℂ)) z i l
          * Bbra (fun a => (sigma a : ℂ)) (fun a b => (Q0phys rho sigma a b : ℂ))
              (fun a b => (Qppphys rho sigma a b : ℂ)) (-z) j l := by
    rw [matCorrWN_laplace]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [q0MixEntry_physMixN_fullline rho sigma hsig z hz i l, hrefl l]
  rw [t1, t2, t3]
  rw [Cmix0_entry_of_id_sub (QphysN rho sigma)
      (fun s => Bbra (fun a => (sigma a : ℂ)) (fun a b => (Q0phys rho sigma a b : ℂ))
        (fun a b => (Qppphys rho sigma a b : ℂ)) s)
      (fun a b => (rhoGeoPhys rho a b : ℂ)) z i j
      (fun s a b => Q0_mat_c_eq_id_sub (fun a => (sigma a : ℂ))
        (fun a b => (rhoGeoPhys rho a b : ℂ))
        (fun a b => (Q0phys rho sigma a b : ℂ)) (fun a b => (Qppphys rho sigma a b : ℂ)) s a b)]


theorem q0MixEntry_continuousAt_N {M : ℕ} (X : Mix N M) (i j : Fin N) {v : ℝ}
    (hlam : v ≠ X.lam i j) (hR : v ≠ X.R i j) :
    ContinuousAt (fun t => (q0MixEntry X i j t : ℂ)) v := by
  have hreal : ContinuousAt (fun t => q0MixEntry X i j t) v := by
    have hpc : ContinuousAt
        (fun r => X.Q0 i j * (r - X.R i j) + X.Qpp j * (r - X.R i j) ^ 2 / 2) v := by fun_prop
    have hzero : ContinuousAt (fun _ : ℝ => (0 : ℝ)) v := continuousAt_const
    rcases lt_trichotomy v (X.lam i j) with hlt | heq | hgt
    · refine hzero.congr ?_
      filter_upwards [Iio_mem_nhds hlt] with t ht
      have hnm : t ∉ Set.Icc (X.lam i j) (X.R i j) :=
        fun h => absurd (Set.mem_Iio.mp ht) (not_lt.mpr h.1)
      rw [q0MixEntry, Set.indicator_of_notMem hnm]
    · exact absurd heq hlam
    · rcases lt_trichotomy v (X.R i j) with h2 | h2 | h2
      · refine hpc.congr ?_
        filter_upwards [Ioo_mem_nhds hgt h2] with t ht
        rw [q0MixEntry, Set.indicator_of_mem (Set.mem_Icc.mpr ⟨le_of_lt ht.1, le_of_lt ht.2⟩)]
      · exact absurd h2 hR
      · refine hzero.congr ?_
        filter_upwards [Ioi_mem_nhds h2] with t ht
        have hnm : t ∉ Set.Icc (X.lam i j) (X.R i j) :=
          fun h => absurd (Set.mem_Ioi.mp ht) (not_lt.mpr h.2)
        rw [q0MixEntry, Set.indicator_of_notMem hnm]
  exact Complex.continuous_ofReal.continuousAt.comp hreal

theorem matCorrWN_continuous {M : ℕ} (X : Mix N M) (ρg : Fin N → Fin N → ℝ) (i j : Fin N) :
    Continuous (fun v => matCorrWN X ρg i j v) := by
  simp only [matCorrWN]
  refine continuous_finsetSum _ (fun l _ => ?_)
  have heq : (fun v => ∫ t, ((ρg i l : ℂ) * (q0MixEntry X i l t : ℂ))
        * ((ρg j l : ℂ) * (q0MixEntry X j l (t - v) : ℂ)))
      = (fun v => (ρg i l : ℂ) * (ρg j l : ℂ)
          * ∫ t, (q0MixEntry X i l t : ℂ) * (q0MixEntry X j l (t - v) : ℂ)) := by
    funext v; rw [← MeasureTheory.integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun t => by ring))
  rw [heq]
  exact continuous_const.mul (q0MixEntry_corr_continuous X i j l)

theorem matDCFfullN_integrable (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k) (i j : Fin N) :
    Integrable (fun v => matDCFfullN rho sigma hsig i j v) := by
  set X := physMixN rho sigma hsig with hX
  have h1 : Integrable (fun v => (rhoGeoPhys rho i j : ℂ) * (q0MixEntry X i j v : ℂ)) :=
    ((memLp_one_iff_integrable.mp (q0MixEntry_memLp X i j 1))).const_mul _
  have h2 : Integrable (fun v => (rhoGeoPhys rho j i : ℂ) * (q0MixEntry X j i (-v) : ℂ)) :=
    (((memLp_one_iff_integrable.mp (q0MixEntry_memLp X j i 1)).comp_neg)).const_mul _
  have h3 : Integrable (fun v => matCorrWN X (rhoGeoPhys rho) i j v) := by
    simp only [matCorrWN]
    refine integrable_finsetSum _ (fun l _ => ?_)
    have := (q0MixEntry_corr_exp_prod_integrable X i j l 0).integral_prod_right
    refine (this.const_mul ((rhoGeoPhys rho i l : ℂ) * (rhoGeoPhys rho j l : ℂ))).congr
      (Filter.Eventually.of_forall (fun v => ?_))
    simp only [Function.uncurry, zero_mul, neg_zero, Complex.exp_zero, mul_one]
    rw [← MeasureTheory.integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun t => by ring))
  refine ((h1.add h2).sub h3).congr (Filter.Eventually.of_forall (fun v => ?_))
  simp only [matDCFfullN, hX, Pi.add_apply, Pi.sub_apply]

theorem matDCFfullN_ae_continuous (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k) (i j : Fin N) :
    ∀ᵐ v, ContinuousAt (fun v => matDCFfullN rho sigma hsig i j v) v := by
  set X := physMixN rho sigma hsig with hX
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null
    (t := {X.lam i j, X.R i j, -(X.lam j i), -(X.R j i)}) (fun v hv => ?_) ?_
  · by_contra hnotin
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hnotin
    obtain ⟨hne1, hne2, hne3, hne4⟩ := hnotin
    apply hv
    show ContinuousAt (fun v => matDCFfullN rho sigma hsig i j v) v
    simp only [matDCFfullN]
    have c1 : ContinuousAt (fun v => (rhoGeoPhys rho i j : ℂ) * (q0MixEntry X i j v : ℂ)) v :=
      continuousAt_const.mul (q0MixEntry_continuousAt_N X i j hne1 hne2)
    have c2 : ContinuousAt (fun v => (rhoGeoPhys rho j i : ℂ) * (q0MixEntry X j i (-v) : ℂ)) v := by
      refine continuousAt_const.mul ?_
      have hnv1 : -v ≠ X.lam j i := fun h => hne3 (by linarith)
      have hnv2 : -v ≠ X.R j i := fun h => hne4 (by linarith)
      exact (q0MixEntry_continuousAt_N X j i hnv1 hnv2).comp continuous_neg.continuousAt
    exact (c1.add c2).sub (matCorrWN_continuous X (rhoGeoPhys rho) i j).continuousAt
  · exact (Set.toFinite _).measure_zero volume

theorem matDCFfullN_transform_offdiag (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k)
    (hrho : ∀ i, 0 ≤ rho i) (hvac : vacMix rho sigma ≠ 0) (i j : Fin N) {w : ℝ} (hw : w ≠ 0) :
    (∫ v, matDCFfullN rho sigma hsig i j v * Complex.exp (-(zOfW w * v)))
      = ∫ v, matDCFfullN rho sigma hsig j i v * Complex.exp (-(zOfW w * v)) := by
  have hzw : zOfW w ≠ 0 := zOfW_ne_zero hw
  rw [matDCFfullN_laplace rho sigma hsig (zOfW w) hzw i j,
      matDCFfullN_laplace rho sigma hsig (zOfW w) hzw j i]
  refine Cmix0_phys_swap (fun a => (sigma a : ℂ)) (fun a => (rho a : ℂ))
    (fun b => (Qppphys rho sigma b b : ℂ)) (fun a b => (Q0phys rho sigma a b : ℂ))
    (fun a b => (Qppphys rho sigma a b : ℂ)) (fun a b => (rhoGeoPhys rho a b : ℂ))
    (Real.pi / vacMix rho sigma : ℂ) (xi2 rho sigma : ℂ) (zOfW w) hzw ?_ ?_ ?_ ?_ ?_ ?_ i j
  · intro a b
    have h := Q0phys_key_relation rho sigma a b hvac
    have : ((Q0phys rho sigma a b : ℝ) : ℂ)
        = ((sigma a / 2 * Qppphys rho sigma a b + Real.pi / vacMix rho sigma * sigma b : ℝ) : ℂ) :=
      congrArg _ h
    push_cast at this ⊢; linear_combination this
  · intro a b; rfl
  · intro b
    have h := Qppphys_key_relation rho sigma b b hvac
    have : ((Qppphys rho sigma b b : ℝ) : ℂ)
        = ((2 * (Real.pi / vacMix rho sigma)
            + (Real.pi / vacMix rho sigma) ^ 2 * xi2 rho sigma * sigma b : ℝ) : ℂ) := congrArg _ h
    push_cast at this ⊢; linear_combination this
  · simp only [xi2]; push_cast; ring
  · intro a b
    simp only [rhoGeoPhys]; rw [mul_comm (rho a) (rho b)]
  · intro a b l
    have h := rhoGeoPhys_mul_eq rho hrho a b l
    have : ((rhoGeoPhys rho a l * rhoGeoPhys rho b l : ℝ) : ℂ)
        = ((rho l * rhoGeoPhys rho a b : ℝ) : ℂ) := congrArg _ h
    push_cast at this ⊢; rw [this]

theorem matDCF_ae_symmN (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k)
    (hrho : ∀ i, 0 ≤ rho i) (hvac : vacMix rho sigma ≠ 0) (i j : Fin N) :
    (fun v => matDCFfullN rho sigma hsig i j v)
      =ᵐ[volume] (fun v => matDCFfullN rho sigma hsig j i v) :=
  ae_eq_of_zOfW_transform_offdiag (matDCFfullN_integrable rho sigma hsig i j)
    (matDCFfullN_integrable rho sigma hsig j i) (matDCFfullN_ae_continuous rho sigma hsig i j)
    (matDCFfullN_ae_continuous rho sigma hsig j i)
    (fun _ hw => matDCFfullN_transform_offdiag rho sigma hsig hrho hvac i j hw)

end GeneralNDCF

/-! ### Physical identification — the abstract fold kernel IS the physical DCF core.
The seed-route `hclaimA` (`correctedSeedExt_hclaimA_matShellConvAsym`) is stated in the ABSTRACT
fold kernel `matDCFfoldKernel Q`.  Here `Q = qWeighted` (the `ρ_geo`-weighted physical Baxter
factor) is pinned so `matDCFfoldKernel (qWeighted) = matDCFreCore` (`= Re(matDCFfull)`), turning the
abstract `hclaimA` into the exact `matDCFreCore`-kernel input of
`matOzStar_of_matDCF_ae_canonical`. -/

section PhysicalIdentification

open FMSA.WHSupports FMSA.InnerDecomp FMSA.MatrixQ0

/-- The `ρ_geo`-weighted physical Baxter factor `Qwᵢₖ(v) = ρ_geoᵢₖ·q0MixEntry(physMix)ᵢₖ(v)` — the
concrete `Q` for which the abstract fold kernel `matDCFfoldKernel Qw` is the physical DCF core. -/
noncomputable def qWeighted (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k) :
    Matrix (Fin 2) (Fin 2) (ℝ → ℝ) :=
  fun i k => fun v => rhoGeoPhys rho i k * q0MixEntry (physMix rho sigma hsig) i k v

/-- **Physical identification** — the abstract full-line DCF fold kernel at the weighted Baxter
factor `qWeighted` IS the physical DCF core `matDCFreCore` (= `Re(matDCFfull)`). -/
theorem matDCFfoldKernel_qWeighted_eq_matDCFreCore (rho sigma : Fin 2 → ℝ)
    (hsig : ∀ k, 0 < sigma k) (i k : Fin 2) (v : ℝ) :
    matDCFfoldKernel (qWeighted rho sigma hsig) i k v = matDCFreCore rho sigma hsig i k v := by
  have hcorr : matCorrW (physMix rho sigma hsig) (rhoGeoPhys rho) i k v
      = ((matCorrFull (qWeighted rho sigma hsig) i k v : ℝ) : ℂ) := by
    simp only [matCorrFull, matCorrW, Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
    simp only [qWeighted]; push_cast; ring
  rw [matDCFreCore, matDCFfull, hcorr]
  rw [show ((rhoGeoPhys rho i k : ℂ) * (q0MixEntry (physMix rho sigma hsig) i k v : ℂ)
        + (rhoGeoPhys rho k i : ℂ) * (q0MixEntry (physMix rho sigma hsig) k i (-v) : ℂ)
        - ((matCorrFull (qWeighted rho sigma hsig) i k v : ℝ) : ℂ))
      = (((rhoGeoPhys rho i k * q0MixEntry (physMix rho sigma hsig) i k v
          + rhoGeoPhys rho k i * q0MixEntry (physMix rho sigma hsig) k i (-v)
          - matCorrFull (qWeighted rho sigma hsig) i k v : ℝ)) : ℂ) from by push_cast; ring,
    Complex.ofReal_re]
  simp only [matDCFfoldKernel, qWeighted]

/-- The `ρ`-scaled kernel functions agree: `matDCFfoldKernel(qWeighted)/ρ = matDCFreCore/ρ`
(funext of the identification) — lets one swap the abstract fold kernel for the physical DCF core
inside `matShellConvAsym`. -/
theorem qWeighted_dcfKernel_div_eq (rhoV sigmaV : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigmaV k) (rho : ℝ) :
    (fun a b => fun u => matDCFfoldKernel (qWeighted rhoV sigmaV hsig) a b u / rho)
      = (fun a b => fun u => matDCFreCore rhoV sigmaV hsig a b u / rho) := by
  funext a b u; rw [matDCFfoldKernel_qWeighted_eq_matDCFreCore]

/-- **Kernel swap for the `hclaimA`.**  The `matShellConvAsym`-form `hclaimA` of
`correctedSeedExt_hclaimA_matShellConvAsym` (at `Q = qWeighted`) rewrites into the physical
`matDCFreCore`-kernel `hclaimA` — EXACTLY the input `matOzStar_of_matDCF_ae_canonical` consumes. -/
theorem hclaimA_qWeighted_to_matDCFreCore (rhoV sigmaV : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigmaV k)
    (Psi Phi : Matrix (Fin 2) (Fin 2) (ℝ → ℝ)) (rho sigma r : ℝ) (i j : Fin 2)
    (h : Psi i j r = r * Phi i j r
      + rho * matShellConvAsym
          (fun a b u => matDCFfoldKernel (qWeighted rhoV sigmaV hsig) a b u / rho)
          (fun a b u => matDCFfoldKernel (qWeighted rhoV sigmaV hsig) b a u / rho)
          (fun k l => fun x => Psi k l x / x) sigma r i j) :
    Psi i j r = r * Phi i j r
      + rho * matShellConvAsym (fun a b u => matDCFreCore rhoV sigmaV hsig a b u / rho)
          (fun a b u => matDCFreCore rhoV sigmaV hsig b a u / rho)
          (fun k l => fun x => Psi k l x / x) sigma r i j := by
  rw [h, qWeighted_dcfKernel_div_eq,
    show (fun a b => fun u => matDCFfoldKernel (qWeighted rhoV sigmaV hsig) b a u / rho)
      = (fun a b => fun u => matDCFreCore rhoV sigmaV hsig b a u / rho) from by
        funext a b u; rw [matDCFfoldKernel_qWeighted_eq_matDCFreCore]]

/-! #### Discharging the `qWeighted` geometric side-conditions (`hsupp`, `hQlam`) of the
`hclaimA` capstone.  `q0MixEntry`'s support `[λᵢₖ,Rᵢₖ]` (`λ=(σₖ−σᵢ)/2`, `R=(σᵢ+σₖ)/2`) pins the
physical fold kernel's compact support: with any shell radius `sigmaS ≥` every diameter,
`matDCFfoldKernel (qWeighted)ᵢₖ` vanishes for `|v| > sigmaS` (both Baxter terms + the correlation)
and `qWeighted` vanishes below `−sigmaS` — the `hsupp`/`hQlam` inputs.  (Integrability conditions
still need `Ψ`-regularity and are left to the wiring.) -/

/-- `q0MixEntry(physMix)` vanishes off its support `[(σⱼ−σᵢ)/2, (σᵢ+σⱼ)/2]`. -/
theorem q0_physMix_eq_zero_of_notMem (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k)
    (i j : Fin 2) {t : ℝ} (ht : t ∉ Set.Icc ((sigma j - sigma i) / 2) ((sigma i + sigma j) / 2)) :
    q0MixEntry (physMix rho sigma hsig) i j t = 0 := by
  by_contra h
  have hmem := q0MixEntry_support_subset (physMix rho sigma hsig) i j (Function.mem_support.mpr h)
  simp only [Mix.lam, Mix.R, physMix] at hmem
  exact ht hmem

/-- The full-line correlation `matCorrFull(qWeighted)ᵢₖ` vanishes for `|v| > Rᵢₖ = (σᵢ+σₖ)/2` — the
two Baxter factors' supports (`[λᵢₘ,Rᵢₘ]`, `[λₖₘ,Rₖₘ]` shifted by `v`) cannot overlap. -/
theorem matCorrFull_qWeighted_eq_zero_of_R_lt_abs (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k)
    (i k : Fin 2) {v : ℝ} (hv : (sigma i + sigma k) / 2 < |v|) :
    matCorrFull (qWeighted rho sigma hsig) i k v = 0 := by
  simp only [matCorrFull]
  refine Finset.sum_eq_zero (fun m _ => ?_)
  have hz : (fun t => qWeighted rho sigma hsig i m t * qWeighted rho sigma hsig k m (t - v))
      = fun _ => (0 : ℝ) := by
    funext t
    by_contra hne
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp hne
    have ht1 : t ∈ Set.Icc ((sigma m - sigma i) / 2) ((sigma i + sigma m) / 2) := by
      by_contra hc
      apply h1
      simp only [qWeighted]
      rw [q0_physMix_eq_zero_of_notMem rho sigma hsig i m hc, mul_zero]
    have ht2 : t - v ∈ Set.Icc ((sigma m - sigma k) / 2) ((sigma k + sigma m) / 2) := by
      by_contra hc
      apply h2
      simp only [qWeighted]
      rw [q0_physMix_eq_zero_of_notMem rho sigma hsig k m hc, mul_zero]
    rw [Set.mem_Icc] at ht1 ht2
    have hvle : |v| ≤ (sigma i + sigma k) / 2 := by
      rw [abs_le]; constructor <;> linarith [ht1.1, ht1.2, ht2.1, ht2.2]
    linarith [hv, hvle]
  rw [hz, integral_zero]

/-- `qWeighted i k` vanishes off `[(σₖ−σᵢ)/2, (σᵢ+σₖ)/2]`. -/
theorem qWeighted_eq_zero_of_notMem (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k) (i k : Fin 2)
    {t : ℝ} (ht : t ∉ Set.Icc ((sigma k - sigma i) / 2) ((sigma i + sigma k) / 2)) :
    qWeighted rho sigma hsig i k t = 0 := by
  simp only [qWeighted]
  rw [q0_physMix_eq_zero_of_notMem rho sigma hsig i k ht, mul_zero]

/-- With a shell radius `sigmaS ≥` every diameter, `qWeighted i k` vanishes for `|t| > sigmaS`
(its support `[(σₖ−σᵢ)/2,(σᵢ+σₖ)/2] ⊆ [−sigmaS, sigmaS]`). -/
theorem qWeighted_eq_zero_of_sigmaS_lt_abs (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k)
    {sigmaS : ℝ} (hσσ : ∀ l, sigma l ≤ sigmaS) (i k : Fin 2) {t : ℝ} (ht : sigmaS < |t|) :
    qWeighted rho sigma hsig i k t = 0 := by
  apply qWeighted_eq_zero_of_notMem
  rw [Set.mem_Icc, not_and_or]
  rcases lt_abs.mp ht with h | h
  · right; rw [not_le]; linarith [hσσ i, hσσ k]
  · left; rw [not_le]; linarith [hσσ i, hsig k, hsig i]

/-- **`hsupp` discharge** — the physical DCF fold kernel is compactly supported in `[−σ,σ]`
for any shell radius `sigmaS ≥` every diameter: `matDCFfoldKernel (qWeighted) i k v = 0` for
`sigmaS < |v|` (both linear Baxter terms and the correlation `matCorrFull` vanish). -/
theorem matDCFfoldKernel_qWeighted_eq_zero_of_lt_abs (rho sigma : Fin 2 → ℝ)
    (hsig : ∀ k, 0 < sigma k) {sigmaS : ℝ} (hσσ : ∀ l, sigma l ≤ sigmaS) (i k : Fin 2) {v : ℝ}
    (hv : sigmaS < |v|) :
    matDCFfoldKernel (qWeighted rho sigma hsig) i k v = 0 := by
  simp only [matDCFfoldKernel]
  rw [qWeighted_eq_zero_of_sigmaS_lt_abs rho sigma hsig hσσ i k hv,
      qWeighted_eq_zero_of_sigmaS_lt_abs rho sigma hsig hσσ k i (by rwa [abs_neg]),
      matCorrFull_qWeighted_eq_zero_of_R_lt_abs rho sigma hsig i k (by linarith [hσσ i, hσσ k])]
  ring

/-- **`hQlam` discharge** — `qWeighted i k` vanishes below `−sigmaS` (the global support lower bound
`lam = −sigmaS ≤ 0` works for every pair). -/
theorem qWeighted_eq_zero_of_lt_neg_sigmaS (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k)
    {sigmaS : ℝ} (hσσ : ∀ l, sigma l ≤ sigmaS) (i k : Fin 2) {t : ℝ} (ht : t < -sigmaS) :
    qWeighted rho sigma hsig i k t = 0 := by
  refine qWeighted_eq_zero_of_sigmaS_lt_abs rho sigma hsig hσσ i k ?_
  rw [lt_abs]; right; linarith
/-! #### Discharging the `qWeighted` integrability side-conditions (`hB`/`hA`/`hC`/`hint`/`hIfwd`/
`hIbwd`) of the `hclaimA` capstone, from continuity of the OZ solution `Ψ`.  Each pairs the
compactly-supported bounded `qWeighted` (or the continuous, compact-support correlation
`matCorrFull`) with `Ψ(r±·)`; `integrable_of_bddSupp_mul_continuous` gives integrability.
`matCorrFull` is continuous (`q0MixEntry_corr_continuous` real part); `hint` splits the fold kernel
into its two linear Baxter terms + the correlation.  (The three NESTED/2D inputs `hI1`/`hI2`/`hfub`
— inner convolutions and the product-measure Fubini integrand — still need convolution-continuity
/ 2D integrability infrastructure.) -/

/-- **Bounded-compact-support × continuous ⟹ integrable.**  A measurable `f` bounded by `C` and
supported in `[a,b]`, times a continuous `g`, is integrable (product supported in `[a,b]`, bdd by
`C·(sup_{[a,b]}‖g‖)`). -/
theorem integrable_of_bddSupp_mul_continuous {f g : ℝ → ℝ} {a b C : ℝ}
    (hfm : Measurable f) (hfC : ∀ t, |f t| ≤ C)
    (hfs : ∀ t, t ∉ Set.Icc a b → f t = 0) (hg : Continuous g) :
    Integrable (fun t => f t * g t) := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn hg.continuousOn
  have hind : (fun t => f t * g t) = (Set.Icc a b).indicator (fun t => f t * g t) := by
    funext t
    by_cases h : t ∈ Set.Icc a b
    · rw [Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem h, hfs t h, zero_mul]
  rw [hind, integrable_indicator_iff measurableSet_Icc]
  refine Measure.integrableOn_of_bounded (M := C * M) measure_Icc_lt_top.ne
    (hfm.mul hg.measurable).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [Real.norm_eq_abs, abs_mul]
  have hgt := hM t ht
  rw [Real.norm_eq_abs] at hgt
  exact mul_le_mul (hfC t) hgt (abs_nonneg _) (le_trans (abs_nonneg _) (hfC t))

theorem qWeighted_abs_le (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k) (i k : Fin 2) :
    ∃ C, ∀ t, |qWeighted rho sigma hsig i k t| ≤ C := by
  obtain ⟨C, _, hC⟩ := q0MixEntry_abs_le (physMix rho sigma hsig) i k
  refine ⟨|rhoGeoPhys rho i k| * C, fun t => ?_⟩
  show |rhoGeoPhys rho i k * q0MixEntry (physMix rho sigma hsig) i k t| ≤ |rhoGeoPhys rho i k| * C
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hC t) (abs_nonneg _)

theorem qWeighted_measurable (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k) (i k : Fin 2) :
    Measurable (qWeighted rho sigma hsig i k) := by
  show Measurable (fun v => rhoGeoPhys rho i k * q0MixEntry (physMix rho sigma hsig) i k v)
  exact (q0MixEntry_measurable (physMix rho sigma hsig) i k).const_mul _

/-- The real cross-correlation `v ↦ ∫ q0ᵢₗ(t)·q0ⱼₗ(t−v)` is continuous (real part of the proven
`ℂ`-valued `q0MixEntry_corr_continuous`). -/
theorem q0_corr_real_continuous {N M : ℕ} (X : Mix N M) (i j l : Fin N) :
    Continuous (fun v => ∫ t, q0MixEntry X i l t * q0MixEntry X j l (t - v)) := by
  have heq : (fun v => ∫ t, q0MixEntry X i l t * q0MixEntry X j l (t - v))
      = fun v => (∫ t, (q0MixEntry X i l t : ℂ) * (q0MixEntry X j l (t - v) : ℂ)).re := by
    funext v
    rw [show (fun t => (q0MixEntry X i l t : ℂ) * (q0MixEntry X j l (t - v) : ℂ))
        = fun t => ((q0MixEntry X i l t * q0MixEntry X j l (t - v) : ℝ) : ℂ) from by
          funext t; push_cast; ring, integral_complex_ofReal, Complex.ofReal_re]
  rw [heq]
  exact Complex.continuous_re.comp (q0MixEntry_corr_continuous X i j l)

/-- `matCorrFull (qWeighted)ᵢₖ` is continuous (finite sum of `const · (continuous correlation)`). -/
theorem matCorrFull_qWeighted_continuous (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k)
    (i k : Fin 2) : Continuous (fun v => matCorrFull (qWeighted rho sigma hsig) i k v) := by
  simp only [matCorrFull]
  refine continuous_finset_sum _ (fun m _ => ?_)
  have heq : (fun v => ∫ t, qWeighted rho sigma hsig i m t * qWeighted rho sigma hsig k m (t - v))
      = fun v => (rhoGeoPhys rho i m * rhoGeoPhys rho k m)
          * ∫ t, q0MixEntry (physMix rho sigma hsig) i m t
              * q0MixEntry (physMix rho sigma hsig) k m (t - v) := by
    funext v
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
    show rhoGeoPhys rho i m * q0MixEntry (physMix rho sigma hsig) i m t
        * (rhoGeoPhys rho k m * q0MixEntry (physMix rho sigma hsig) k m (t - v))
      = rhoGeoPhys rho i m * rhoGeoPhys rho k m
          * (q0MixEntry (physMix rho sigma hsig) i m t
              * q0MixEntry (physMix rho sigma hsig) k m (t - v))
    ring
  rw [heq]
  exact continuous_const.mul (q0_corr_real_continuous (physMix rho sigma hsig) i k m)

/-- `matCorrFull (qWeighted)ᵢₖ` is globally bounded (continuous + compact support `[−Rᵢₖ,Rᵢₖ]`). -/
theorem matCorrFull_qWeighted_abs_le (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k)
    (i k : Fin 2) :
    ∃ C, ∀ v, |matCorrFull (qWeighted rho sigma hsig) i k v| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -((sigma i + sigma k) / 2)) (b := (sigma i + sigma k) / 2)
    ).exists_bound_of_continuousOn
    (matCorrFull_qWeighted_continuous rho sigma hsig i k).continuousOn
  refine ⟨max C 0, fun v => ?_⟩
  by_cases hv : v ∈ Set.Icc (-((sigma i + sigma k) / 2)) ((sigma i + sigma k) / 2)
  · have hb := hC v hv; rw [Real.norm_eq_abs] at hb; exact le_trans hb (le_max_left _ _)
  · rw [Set.mem_Icc, not_and_or, not_le, not_le] at hv
    rw [matCorrFull_qWeighted_eq_zero_of_R_lt_abs rho sigma hsig i k ?_, abs_zero]
    · exact le_max_right _ _
    · rcases hv with h | h
      · exact lt_of_lt_of_le (by linarith) (neg_le_abs v)
      · exact lt_of_lt_of_le h (le_abs_self v)

/-- General `g`: `qWeightedᵢₖ · g` integrable for continuous `g`. -/
theorem qWeighted_mul_cont_integrable (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k)
    (i k : Fin 2)
    {g : ℝ → ℝ} (hg : Continuous g) :
    Integrable (fun t => qWeighted rho sigma hsig i k t * g t) :=
  integrable_of_bddSupp_mul_continuous (a := (sigma k - sigma i) / 2) (b := (sigma i + sigma k) / 2)
    (qWeighted_measurable rho sigma hsig i k) (qWeighted_abs_le rho sigma hsig i k).choose_spec
    (fun t ht => qWeighted_eq_zero_of_notMem rho sigma hsig i k ht) hg

/-- General `g`: reflected `qWeightedₖᵢ(−·) · g` integrable for continuous `g`. -/
theorem qWeightedRefl_mul_cont_integrable (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k)
    (i k : Fin 2) {g : ℝ → ℝ} (hg : Continuous g) :
    Integrable (fun v => qWeighted rho sigma hsig k i (-v) * g v) :=
  integrable_of_bddSupp_mul_continuous
    (a := -((sigma k + sigma i) / 2)) (b := (sigma k - sigma i) / 2)
    ((qWeighted_measurable rho sigma hsig k i).comp continuous_neg.measurable)
    (fun v => (qWeighted_abs_le rho sigma hsig k i).choose_spec (-v))
    (fun v hv => qWeighted_eq_zero_of_notMem rho sigma hsig k i (fun hmem => hv (by
      rw [Set.mem_Icc] at hmem ⊢; constructor <;> linarith [hmem.1, hmem.2]))) hg

/-- General `g`: `matCorrFull (qWeighted)ᵢₖ · g` integrable for continuous `g`. -/
theorem matCorrFull_mul_cont_integrable (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k)
    (i k : Fin 2)
    {g : ℝ → ℝ} (hg : Continuous g) :
    Integrable (fun v => matCorrFull (qWeighted rho sigma hsig) i k v * g v) := by
  refine integrable_of_bddSupp_mul_continuous (a := -((sigma i + sigma k) / 2))
    (b := (sigma i + sigma k) / 2) (matCorrFull_qWeighted_continuous rho sigma hsig i k).measurable
    (matCorrFull_qWeighted_abs_le rho sigma hsig i k).choose_spec (fun v hv => ?_) hg
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hv
  refine matCorrFull_qWeighted_eq_zero_of_R_lt_abs rho sigma hsig i k ?_
  rcases hv with h | h
  · exact lt_of_lt_of_le (by linarith) (neg_le_abs v)
  · exact lt_of_lt_of_le h (le_abs_self v)

/-- General `g`: the DCF fold kernel `matDCFfoldKernel (qWeighted)ᵢₖ · g` integrable (split into the
two linear Baxter terms + the correlation, each integrable). -/
theorem matDCFfoldKernel_mul_cont_integrable (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k)
    (i k : Fin 2) {g : ℝ → ℝ} (hg : Continuous g) :
    Integrable (fun v => matDCFfoldKernel (qWeighted rho sigma hsig) i k v * g v) := by
  refine (((qWeighted_mul_cont_integrable rho sigma hsig i k hg).add
    (qWeightedRefl_mul_cont_integrable rho sigma hsig i k hg)).sub
    (matCorrFull_mul_cont_integrable rho sigma hsig i k hg)).congr
    (Filter.Eventually.of_forall (fun v => ?_))
  simp only [matDCFfoldKernel, Pi.add_apply, Pi.sub_apply]; ring

/-! The six capstone integrability inputs discharged from `Ψ`-continuity
(`hΨ : ∀ k, Continuous (Ψ k j)`). -/

theorem hB_qWeighted (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k)
    (Psi : Matrix (Fin 2) (Fin 2) (ℝ → ℝ)) (r : ℝ) (i j : Fin 2)
    (hΨ : ∀ k, Continuous (Psi k j)) :
    ∀ k, Integrable (fun t => qWeighted rho sigma hsig i k t * Psi k j (r + t)) :=
  fun k => qWeighted_mul_cont_integrable rho sigma hsig i k
    ((hΨ k).comp (continuous_const.add continuous_id))

theorem hA_qWeighted (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k)
    (Psi : Matrix (Fin 2) (Fin 2) (ℝ → ℝ)) (r : ℝ) (i j : Fin 2)
    (hΨ : ∀ k, Continuous (Psi k j)) :
    ∀ k, Integrable (fun v => qWeighted rho sigma hsig k i (-v) * Psi k j (r + v)) :=
  fun k => qWeightedRefl_mul_cont_integrable rho sigma hsig i k
    ((hΨ k).comp (continuous_const.add continuous_id))

theorem hC_qWeighted (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k)
    (Psi : Matrix (Fin 2) (Fin 2) (ℝ → ℝ)) (r : ℝ) (i j : Fin 2)
    (hΨ : ∀ k, Continuous (Psi k j)) :
    ∀ k, Integrable (fun v => matCorrFull (qWeighted rho sigma hsig) i k v * Psi k j (r + v)) :=
  fun k => matCorrFull_mul_cont_integrable rho sigma hsig i k
    ((hΨ k).comp (continuous_const.add continuous_id))

theorem hint_qWeighted (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k)
    (Psi : Matrix (Fin 2) (Fin 2) (ℝ → ℝ)) (r : ℝ) (i j : Fin 2)
    (hΨ : ∀ k, Continuous (Psi k j)) :
    ∀ k, Integrable
      (fun v => matDCFfoldKernel (qWeighted rho sigma hsig) i k v * Psi k j (r + v)) :=
  fun k => matDCFfoldKernel_mul_cont_integrable rho sigma hsig i k
    ((hΨ k).comp (continuous_const.add continuous_id))

theorem hIfwd_qWeighted (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k)
    (Psi : Matrix (Fin 2) (Fin 2) (ℝ → ℝ)) (r sigmaS : ℝ) (i j : Fin 2)
    (hΨ : ∀ k, Continuous (Psi k j)) :
    ∀ k, IntervalIntegrable
      (fun u => matDCFfoldKernel (qWeighted rho sigma hsig) i k u * Psi k j (r + u))
      volume 0 sigmaS :=
  fun k => (matDCFfoldKernel_mul_cont_integrable rho sigma hsig i k
    ((hΨ k).comp (continuous_const.add continuous_id))).intervalIntegrable

theorem hIbwd_qWeighted (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k)
    (Psi : Matrix (Fin 2) (Fin 2) (ℝ → ℝ)) (r sigmaS : ℝ) (i j : Fin 2)
    (hΨ : ∀ k, Continuous (Psi k j)) :
    ∀ k, IntervalIntegrable
      (fun u => matDCFfoldKernel (qWeighted rho sigma hsig) k i u * Psi k j (r - u))
      volume 0 sigmaS :=
  fun k => (matDCFfoldKernel_mul_cont_integrable rho sigma hsig k i
    ((hΨ k).comp (continuous_const.sub continuous_id))).intervalIntegrable
/-! #### `hI2` discharge — the single-correlation `∫ Qᵢₖ(t)·Qₘₖ(t−v)` (one summand shape) is
continuous in `v` (`q0_corr_real_continuous`), compactly supported in `[−(σᵢ+σₘ)/2,(σᵢ+σₘ)/2]`, and
bounded — so its product with `Ψₘⱼ(r+·)` is integrable via `integrable_of_bddSupp_mul_continuous`.-/

/-- Single cross-correlation `∫ qWeightedₐₗ(t)·qWeightedᵦₗ(t−v)` vanishes for `|v| > (σₐ+σᵦ)/2`
(the two factors' `v`-shifted supports cannot overlap). -/
theorem qWeighted_corr_eq_zero_of_R_lt_abs (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k)
    (a b l : Fin 2) {v : ℝ} (hv : (sigma a + sigma b) / 2 < |v|) :
    (∫ t, qWeighted rho sigma hsig a l t * qWeighted rho sigma hsig b l (t - v)) = 0 := by
  have hz : (fun t => qWeighted rho sigma hsig a l t * qWeighted rho sigma hsig b l (t - v))
      = fun _ => (0 : ℝ) := by
    funext t
    by_contra hne
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp hne
    have ht1 : t ∈ Set.Icc ((sigma l - sigma a) / 2) ((sigma a + sigma l) / 2) := by
      by_contra hc
      apply h1
      simp only [qWeighted]
      rw [q0_physMix_eq_zero_of_notMem rho sigma hsig a l hc, mul_zero]
    have ht2 : t - v ∈ Set.Icc ((sigma l - sigma b) / 2) ((sigma b + sigma l) / 2) := by
      by_contra hc
      apply h2
      simp only [qWeighted]
      rw [q0_physMix_eq_zero_of_notMem rho sigma hsig b l hc, mul_zero]
    rw [Set.mem_Icc] at ht1 ht2
    have hvle : |v| ≤ (sigma a + sigma b) / 2 := by
      rw [abs_le]; constructor <;> linarith [ht1.1, ht1.2, ht2.1, ht2.2]
    linarith [hv, hvle]
  rw [hz, integral_zero]

/-- The single correlation `v ↦ ∫ qWeightedₐₗ(t)·qWeightedᵦₗ(t−v)` is continuous. -/
theorem qWeighted_corr_continuous (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k)
    (a b l : Fin 2) :
    Continuous
      (fun v => ∫ t, qWeighted rho sigma hsig a l t * qWeighted rho sigma hsig b l (t - v)) := by
  have heq : (fun v => ∫ t, qWeighted rho sigma hsig a l t * qWeighted rho sigma hsig b l (t - v))
      = fun v => (rhoGeoPhys rho a l * rhoGeoPhys rho b l)
          * ∫ t, q0MixEntry (physMix rho sigma hsig) a l t
              * q0MixEntry (physMix rho sigma hsig) b l (t - v) := by
    funext v
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
    show rhoGeoPhys rho a l * q0MixEntry (physMix rho sigma hsig) a l t
        * (rhoGeoPhys rho b l * q0MixEntry (physMix rho sigma hsig) b l (t - v))
      = rhoGeoPhys rho a l * rhoGeoPhys rho b l
          * (q0MixEntry (physMix rho sigma hsig) a l t
              * q0MixEntry (physMix rho sigma hsig) b l (t - v))
    ring
  rw [heq]
  exact continuous_const.mul (q0_corr_real_continuous (physMix rho sigma hsig) a b l)

/-- The single correlation is globally bounded (continuous + compact support `[−Rₐᵦ,Rₐᵦ]`). -/
theorem qWeighted_corr_abs_le (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k) (a b l : Fin 2) :
    ∃ C, ∀ v,
      |∫ t, qWeighted rho sigma hsig a l t * qWeighted rho sigma hsig b l (t - v)| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -((sigma a + sigma b) / 2)) (b := (sigma a + sigma b) / 2)
    ).exists_bound_of_continuousOn (qWeighted_corr_continuous rho sigma hsig a b l).continuousOn
  refine ⟨max C 0, fun v => ?_⟩
  by_cases hv : v ∈ Set.Icc (-((sigma a + sigma b) / 2)) ((sigma a + sigma b) / 2)
  · have hb := hC v hv; rw [Real.norm_eq_abs] at hb; exact le_trans hb (le_max_left _ _)
  · rw [Set.mem_Icc, not_and_or, not_le, not_le] at hv
    rw [qWeighted_corr_eq_zero_of_R_lt_abs rho sigma hsig a b l ?_, abs_zero]
    · exact le_max_right _ _
    · rcases hv with h | h
      · exact lt_of_lt_of_le (by linarith) (neg_le_abs v)
      · exact lt_of_lt_of_le h (le_abs_self v)

/-- **`hI2` discharge** — `(∫ Qᵢₖ(t)·Qₘₖ(t−v))·Ψₘⱼ(r+v)` integrable (single-correlation continuity
+ compact support × continuous `Ψ`). -/
theorem hI2_qWeighted (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k)
    (Psi : Matrix (Fin 2) (Fin 2) (ℝ → ℝ)) (r : ℝ) (i j : Fin 2)
    (hΨ : ∀ k, Continuous (Psi k j)) :
    ∀ k m, Integrable (fun v => (∫ t, qWeighted rho sigma hsig i k t
        * qWeighted rho sigma hsig m k (t - v)) * Psi m j (r + v)) := by
  intro k m
  refine integrable_of_bddSupp_mul_continuous (a := -((sigma i + sigma m) / 2))
    (b := (sigma i + sigma m) / 2) (qWeighted_corr_continuous rho sigma hsig i m k).measurable
    (qWeighted_corr_abs_le rho sigma hsig i m k).choose_spec (fun v hv => ?_)
    ((hΨ m).comp (continuous_const.add continuous_id))
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hv
  refine qWeighted_corr_eq_zero_of_R_lt_abs rho sigma hsig i m k ?_
  rcases hv with h | h
  · exact lt_of_lt_of_le (by linarith) (neg_le_abs v)
  · exact lt_of_lt_of_le h (le_abs_self v)
/-! #### `hI1` discharge — the inner convolution `t ↦ ∫ Qₘₖ(s)·Ψₘⱼ(r+t−s)` is continuous (a
dominated-convergence argument at each `t₀`, since `Q = qWeighted` jumps in `s` but the integral is
continuous in `t`), so `Qᵢₖ·(that convolution)` is integrable by the compact-support helper. -/

/-- `qWeighted i k` is integrable (bounded × compact support, `g := 1`). -/
theorem qWeighted_integrable (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k) (i k : Fin 2) :
    Integrable (qWeighted rho sigma hsig i k) := by
  have h := integrable_of_bddSupp_mul_continuous (a := (sigma k - sigma i) / 2)
    (b := (sigma i + sigma k) / 2) (qWeighted_measurable rho sigma hsig i k)
    (qWeighted_abs_le rho sigma hsig i k).choose_spec
    (fun t ht => qWeighted_eq_zero_of_notMem rho sigma hsig i k ht)
    (continuous_const (y := (1 : ℝ)))
  simpa using h

/-- **Inner-convolution continuity** — `t ↦ ∫ qWeightedₘₖ(s)·Ψₘⱼ(r+t−s) ds` is continuous.  Proved
by dominated convergence at each `t₀`: the integrand is continuous in `t` pointwise (Ψ continuous,
`qWeighted` constant in `t`) and, for `t` in a unit ball around `t₀`, dominated by
`M·|qWeightedₘₖ|` (`M` bounds `Ψ` on the compact `[r+t₀−1−R, r+t₀+1−λ]`). -/
theorem qWeighted_conv_continuous (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k)
    (Psi : Matrix (Fin 2) (Fin 2) (ℝ → ℝ)) (r : ℝ) (m k j : Fin 2) (hΨ : Continuous (Psi m j)) :
    Continuous (fun t => ∫ s, qWeighted rho sigma hsig m k s * Psi m j (r + t - s)) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := r + t₀ - 1 - (sigma m + sigma k) / 2)
    (b := r + t₀ + 1 - (sigma k - sigma m) / 2)).exists_bound_of_continuousOn hΨ.continuousOn
  refine continuousAt_of_dominated (bound := fun s => M * |qWeighted rho sigma hsig m k s|)
    (Filter.Eventually.of_forall (fun t => ?_)) ?_
    ((qWeighted_integrable rho sigma hsig m k).abs.const_mul M)
    (Filter.Eventually.of_forall (fun s =>
      (continuous_const.mul (hΨ.comp (by fun_prop))).continuousAt))
  · exact ((qWeighted_measurable rho sigma hsig m k).mul
      (hΨ.measurable.comp (by fun_prop))).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds t₀ one_pos] with t ht
    filter_upwards with s
    rw [Real.norm_eq_abs, abs_mul]
    by_cases hs : s ∈ Set.Icc ((sigma k - sigma m) / 2) ((sigma m + sigma k) / 2)
    · have harg : r + t - s ∈ Set.Icc (r + t₀ - 1 - (sigma m + sigma k) / 2)
          (r + t₀ + 1 - (sigma k - sigma m) / 2) := by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt] at ht
        rw [Set.mem_Icc] at hs ⊢
        constructor <;> [linarith [hs.2, ht.1]; linarith [hs.1, ht.2]]
      have hΨb := hM (r + t - s) harg
      rw [Real.norm_eq_abs] at hΨb
      calc |qWeighted rho sigma hsig m k s| * |Psi m j (r + t - s)|
          ≤ |qWeighted rho sigma hsig m k s| * M :=
            mul_le_mul_of_nonneg_left hΨb (abs_nonneg _)
        _ = M * |qWeighted rho sigma hsig m k s| := by ring
    · rw [qWeighted_eq_zero_of_notMem rho sigma hsig m k hs]; simp

/-- **`hI1` discharge** — `Qᵢₖ(t)·(∫ Qₘₖ(s)·Ψₘⱼ(r+t−s))` integrable (the inner convolution is
continuous, times the compact-support `Qᵢₖ`). -/
theorem hI1_qWeighted (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k)
    (Psi : Matrix (Fin 2) (Fin 2) (ℝ → ℝ)) (r : ℝ) (i j : Fin 2)
    (hΨ : ∀ k, Continuous (Psi k j)) :
    ∀ k m, Integrable (fun t => qWeighted rho sigma hsig i k t
        * ∫ s, qWeighted rho sigma hsig m k s * Psi m j (r + t - s)) :=
  fun k m => qWeighted_mul_cont_integrable rho sigma hsig i k
    (qWeighted_conv_continuous rho sigma hsig Psi r m k j (hΨ m))
/-! #### `hfub` discharge — the 2D product-measure Fubini integrand.  The integrand
`Qᵢₖ(t)·Qₘₖ(t−v)·Ψₘⱼ(r+v)` is bounded, measurable, and compactly supported in the rectangle
`[λᵢₖ,Rᵢₖ] × [λᵢₖ−Rₘₖ, Rᵢₖ−λₘₖ]`, so it is integrable on `volume ×ˢ volume` (general helper
`integrable_of_bddOn_support`: bounded on a finite-measure support ⟹ integrable).  This completes
all 9 integrability inputs of the seed-route `hclaimA` capstone. -/

/-- **Bounded-on-support ⟹ integrable** (any measure).  A measurable `F` supported in a
finite-measure set `s` and bounded by `C` on `s` is integrable. -/
theorem integrable_of_bddOn_support {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}
    {F : α → ℝ} {s : Set α} {C : ℝ} (hs : MeasurableSet s) (hμs : μ s ≠ ⊤) (hFm : Measurable F)
    (hFC : ∀ p ∈ s, |F p| ≤ C) (hFsupp : ∀ p, p ∉ s → F p = 0) :
    Integrable F μ := by
  have hind : F = s.indicator F := by
    funext p; by_cases h : p ∈ s
    · rw [Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem h, hFsupp p h]
  rw [hind, integrable_indicator_iff hs]
  refine Measure.integrableOn_of_bounded (M := C) hμs hFm.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem hs] with p hp
  rw [Real.norm_eq_abs]; exact hFC p hp

/-- **`hfub` discharge** — the 2D Fubini integrand `Qᵢₖ(t)·Qₘₖ(t−v)·Ψₘⱼ(r+v)` is integrable on
`volume ×ˢ volume` (bounded, measurable, compactly supported in the rectangle
`[λᵢₖ,Rᵢₖ] × [λᵢₖ−Rₘₖ, Rᵢₖ−λₘₖ]`). -/
theorem hfub_qWeighted (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k)
    (Psi : Matrix (Fin 2) (Fin 2) (ℝ → ℝ)) (r : ℝ) (i j : Fin 2)
    (hΨ : ∀ k, Continuous (Psi k j)) :
    ∀ k m, Integrable (Function.uncurry fun t v =>
        qWeighted rho sigma hsig i k t * qWeighted rho sigma hsig m k (t - v) * Psi m j (r + v))
      (volume.prod volume) := by
  intro k m
  obtain ⟨C1, hC1⟩ := qWeighted_abs_le rho sigma hsig i k
  obtain ⟨C2, hC2⟩ := qWeighted_abs_le rho sigma hsig m k
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (sigma k - sigma i) / 2 - (sigma m + sigma k) / 2)
      (b := (sigma i + sigma k) / 2 - (sigma k - sigma m) / 2)).exists_bound_of_continuousOn
    ((hΨ m).comp (continuous_const.add continuous_id)).continuousOn
  have hFm : Measurable (Function.uncurry fun t v => qWeighted rho sigma hsig i k t
      * qWeighted rho sigma hsig m k (t - v) * Psi m j (r + v)) := by
    apply Measurable.mul
    · exact ((qWeighted_measurable rho sigma hsig i k).comp measurable_fst).mul
        ((qWeighted_measurable rho sigma hsig m k).comp (measurable_fst.sub measurable_snd))
    · exact ((hΨ m).comp (continuous_const.add continuous_id)).measurable.comp measurable_snd
  refine integrable_of_bddOn_support (C := C1 * C2 * M)
    (s := Set.Icc ((sigma k - sigma i) / 2) ((sigma i + sigma k) / 2) ×ˢ
      Set.Icc ((sigma k - sigma i) / 2 - (sigma m + sigma k) / 2)
        ((sigma i + sigma k) / 2 - (sigma k - sigma m) / 2))
    (measurableSet_Icc.prod measurableSet_Icc) ?_ hFm ?_ ?_
  · rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top measure_Icc_lt_top.ne measure_Icc_lt_top.ne
  · rintro ⟨t, v⟩ ⟨ht, hv⟩
    simp only [Function.uncurry]
    have h3 : |Psi m j (r + v)| ≤ M := by have := hM v hv; rwa [Real.norm_eq_abs] at this
    have hc1 : (0 : ℝ) ≤ C1 := le_trans (abs_nonneg _) (hC1 t)
    have hc2 : (0 : ℝ) ≤ C2 := le_trans (abs_nonneg _) (hC2 (t - v))
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul (hC1 t) (hC2 (t - v)) (abs_nonneg _) hc1) h3
      (abs_nonneg _) (mul_nonneg hc1 hc2)
  · rintro ⟨t, v⟩ hp
    simp only [Function.uncurry]
    by_contra hne
    obtain ⟨h12, _⟩ := mul_ne_zero_iff.mp hne
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp h12
    have ht : t ∈ Set.Icc ((sigma k - sigma i) / 2) ((sigma i + sigma k) / 2) := by
      by_contra hc
      exact h1 (qWeighted_eq_zero_of_notMem rho sigma hsig i k hc)
    have hv : t - v ∈ Set.Icc ((sigma k - sigma m) / 2) ((sigma m + sigma k) / 2) := by
      by_contra hc
      exact h2 (qWeighted_eq_zero_of_notMem rho sigma hsig m k hc)
    rw [Set.mem_Icc] at ht hv
    exact hp (Set.mem_prod.mpr ⟨Set.mem_Icc.mpr ht,
      Set.mem_Icc.mpr ⟨by linarith [ht.1, hv.2], by linarith [ht.2, hv.1]⟩⟩)
/-! #### `hbridge` discharge — `r·matRadialConv Φ (Ψ/·) = matShellConv (shellKernel Φ) (Ψ/·)`.
Via `matRadialConv_eq_matShellConv_of_shellKernel`, with its two side-conditions discharged from `Ψ`
odd+continuous and `Φ` bounded+measurable+compactly-supported: `hshell` uses `oddExt(Ψ/·)=Ψ` +
continuity; `hjoint` is the 2D integrability (bounded, compactly-supported integrand on the finite
restricted product measure).  This gives `hbridge` in `shellKernel Φ` form; matching the capstone's
`matDCFreCore/ρ` kernel needs the separate shell-kernel↔DCF identity (the open Wertheim step). -/

open FMSA.HardSphere in
theorem matBridge_of_regular (Phi Psi : Matrix (Fin 2) (Fin 2) (ℝ → ℝ)) {sigma : ℝ}
    (hsigma : 0 < sigma) {r : ℝ} (hr : 0 < r) (i j : Fin 2)
    (hΦsupp : ∀ k s, sigma ≤ s → Phi i k s = 0)
    (hΦmeas : ∀ k, Measurable (Phi i k))
    (hΦbd : ∀ k, ∃ C, ∀ s, |Phi i k s| ≤ C)
    (hΨcont : ∀ k, Continuous (Psi k j))
    (hΨodd : ∀ k, (∀ x, Psi k j (-x) = -Psi k j x) ∧ Psi k j 0 = 0) :
    r * matRadialConv Phi (fun k l => fun x => Psi k l x / x) r i j
      = matShellConv (fun i k => shellKernel (Phi i k) sigma)
          (fun k l => fun x => Psi k l x / x) sigma r i j := by
  refine matRadialConv_eq_matShellConv_of_shellKernel Phi _ hsigma hr i j hΦsupp (fun k t _ => ?_)
    (fun k => ?_)
  · rw [oddExt_div_self_eq_of_odd (hΨodd k).1 (hΨodd k).2]
    exact (hΨcont k).intervalIntegrable _ _
  · -- hjoint
    have hoe : ∀ x, oddExt ((fun k' l => fun x => Psi k' l x / x
          : Matrix (Fin 2) (Fin 2) (ℝ → ℝ)) k j) x = Psi k j x :=
      fun x => congrFun (oddExt_div_self_eq_of_odd (hΨodd k).1 (hΨodd k).2) x
    obtain ⟨Cφ, hCφ⟩ := hΦbd k
    obtain ⟨M, hM⟩ := (isCompact_Icc (a := r - sigma) (b := r + sigma)).exists_bound_of_continuousOn
      (hΨcont k).continuousOn
    have hCφ0 : 0 ≤ Cφ := le_trans (abs_nonneg _) (hCφ 0)
    have hσ0 : 0 ≤ sigma := hsigma.le
    have hInd : Measurable
        (fun p : ℝ × ℝ => (Set.Ioi p.1).indicator (fun s => s * Phi i k s) p.2) := by
      have he : (fun p : ℝ × ℝ => (Set.Ioi p.1).indicator (fun s => s * Phi i k s) p.2)
          = {p : ℝ × ℝ | p.1 < p.2}.indicator (fun p => p.2 * Phi i k p.2) := by
        funext p
        rw [Set.indicator_apply, Set.indicator_apply]
        simp only [Set.mem_Ioi, Set.mem_setOf_eq]
      rw [he]
      exact (measurable_snd.mul ((hΦmeas k).comp measurable_snd)).indicator
        (measurableSet_lt measurable_fst measurable_snd)
    have hFmΨ : Measurable (Function.uncurry fun u s =>
        (Set.Ioi u).indicator (fun s => s * Phi i k s) s
          * (Psi k j (r - u) + Psi k j (r + u))) := by
      exact hInd.mul (((hΨcont k).measurable.comp (measurable_const.sub measurable_fst)).add
        ((hΨcont k).measurable.comp (measurable_const.add measurable_fst)))
    have hint : Integrable (Function.uncurry fun u s =>
        (Set.Ioi u).indicator (fun s => s * Phi i k s) s * (Psi k j (r - u) + Psi k j (r + u)))
        ((volume.restrict (Set.Ioc (0:ℝ) sigma)).prod (volume.restrict (Set.Ioc (0:ℝ) sigma))) := by
      rw [show (volume.restrict (Set.Ioc (0:ℝ) sigma)).prod (volume.restrict (Set.Ioc (0:ℝ) sigma))
          = (volume.prod volume).restrict (Set.Ioc (0:ℝ) sigma ×ˢ Set.Ioc (0:ℝ) sigma) from
        Measure.prod_restrict _ _]
      refine Measure.integrableOn_of_bounded (M := sigma * Cφ * (M + M)) ?_
        hFmΨ.aestronglyMeasurable ?_
      · rw [Measure.prod_prod]
        exact ENNReal.mul_ne_top measure_Ioc_lt_top.ne measure_Ioc_lt_top.ne
      · filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with p hp
        obtain ⟨hu, hs⟩ := Set.mem_prod.mp hp
        rw [Set.mem_Ioc] at hu hs
        rw [Real.norm_eq_abs]
        simp only [Function.uncurry]
        rw [abs_mul]
        have hb1 : |(Set.Ioi p.1).indicator (fun s => s * Phi i k s) p.2| ≤ sigma * Cφ := by
          rw [Set.indicator_apply]
          split
          · rw [abs_mul]
            exact mul_le_mul (by rw [abs_of_pos hs.1]; exact hs.2) (hCφ p.2) (abs_nonneg _) hσ0
          · rw [abs_zero]; exact mul_nonneg hσ0 hCφ0
        have hb2 : |Psi k j (r - p.1) + Psi k j (r + p.1)| ≤ M + M := by
          refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
          · have := hM (r - p.1) ⟨by linarith [hu.2], by linarith [hu.1]⟩
            rwa [Real.norm_eq_abs] at this
          · have := hM (r + p.1) ⟨by linarith [hu.1], by linarith [hu.2]⟩
            rwa [Real.norm_eq_abs] at this
        exact mul_le_mul hb1 hb2 (abs_nonneg _) (mul_nonneg hσ0 hCφ0)
    exact hint.congr (Filter.Eventually.of_forall (fun p => by
      simp only [Function.uncurry, hoe]))
open FMSA.HardSphere in
/-- **`hbridge` in the capstone's `matDCFreCore/ρ` kernel form, reduced to the shell-kernel↔DCF
identity.**  Combining `matBridge_of_regular` (`hbridge` with kernel `shellKernel Φ`) with the
single real-space identity `hShellDCF` (`shellKernel(Φᵢₖ)(v) = matDCFreCore(i,k)(v)/ρ` on `(0,σ)`)
gives the exact `hbridge` `matOzStar_of_matDCF_ae_canonical` consumes.  `hShellDCF` is the **open
Baxter–Wiener–Hopf factorization** step (the 3D-radial shell-kernel transform of `Φ` = the
1D DCF core), NOT a mechanical discharge — this lemma isolates it as the sole remaining input. -/
theorem matBridge_matDCFreCore (Phi Psi : Matrix (Fin 2) (Fin 2) (ℝ → ℝ)) (rhoV sigmaV : Fin 2 → ℝ)
    (hsigV : ∀ k, 0 < sigmaV k) {sigma rho : ℝ} (hsigma : 0 < sigma) {r : ℝ} (hr : 0 < r)
    (i j : Fin 2)
    (hΦsupp : ∀ k s, sigma ≤ s → Phi i k s = 0)
    (hΦmeas : ∀ k, Measurable (Phi i k))
    (hΦbd : ∀ k, ∃ C, ∀ s, |Phi i k s| ≤ C)
    (hΨcont : ∀ k, Continuous (Psi k j))
    (hΨodd : ∀ k, (∀ x, Psi k j (-x) = -Psi k j x) ∧ Psi k j 0 = 0)
    (hShellDCF : ∀ k v, v ∈ Set.Ioo (0 : ℝ) sigma →
      shellKernel (Phi i k) sigma v = matDCFreCore rhoV sigmaV hsigV i k v / rho) :
    r * matRadialConv Phi (fun k l => fun x => Psi k l x / x) r i j
      = matShellConv (fun i k u => matDCFreCore rhoV sigmaV hsigV i k u / rho)
          (fun k l => fun x => Psi k l x / x) sigma r i j := by
  rw [matBridge_of_regular Phi Psi hsigma hr i j hΦsupp hΦmeas hΦbd hΨcont hΨodd]
  unfold matShellConv
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine intervalIntegral.integral_congr_ae ?_
  rw [Set.uIoc_of_le hsigma.le]
  have hne : ∀ᵐ u : ℝ, u ≠ sigma := by rw [MeasureTheory.ae_iff]; simp
  filter_upwards [hne] with u hune hmem
  rw [hShellDCF k u ⟨hmem.1, lt_of_le_of_ne hmem.2 hune⟩]
/-! #### The shell-kernel↔DCF identity `hShellDCF` is an FTC/ODE relation.  `shellKernel c σ` is
the antiderivative-type object (`shellKernel_eq_of_hasDerivAt` / `_of_continuousOn`), so `hShellDCF`
reduces to `matDCFreCore/ρ` vanishing at `σ` + the first-order relation `(matDCFreCore/ρ)'=−2π·s·Φ`
(`hShellDCF_of_deriv`).  Even at equal diameters this differential Baxter–WH relation between
the DCF core and the forcing `Φ` is the residual open content — isolated here to an ODE. -/

open FMSA.HardSphere

/-- **FTC characterization of `shellKernel`.**  `shellKernel c σ` is the antiderivative-type object:
if `F σ = 0` and `F' = −2π·s·c(s)` on `[v,σ]`, then `shellKernel c σ v = F v` (for `0 < v < σ`).
This turns `hShellDCF` (`shellKernel(Φᵢₖ) = matDCFreCore/ρ`) into the DIFFERENTIAL relation
`(matDCFreCore/ρ)'(s) = −2π·s·Φᵢₖ(s)` + boundary `matDCFreCore(σ)/ρ = 0`. -/
theorem shellKernel_eq_of_hasDerivAt {c F : ℝ → ℝ} {sigma : ℝ} (hFσ : F sigma = 0)
    {v : ℝ} (hv : v ∈ Set.Ioo (0 : ℝ) sigma)
    (hderiv : ∀ s ∈ Set.uIcc v sigma, HasDerivAt F (-(2 * Real.pi * s * c s)) s)
    (hint : IntervalIntegrable (fun s => -(2 * Real.pi * s * c s)) volume v sigma) :
    shellKernel c sigma v = F v := by
  unfold shellKernel
  rw [abs_of_pos hv.1]
  have hftc : ∫ s in v..sigma, -(2 * Real.pi * s * c s) = F sigma - F v :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [hFσ, zero_sub] at hftc
  have h2 : (∫ s in v..sigma, -(2 * Real.pi * s * c s))
      = -(2 * Real.pi) * ∫ s in v..sigma, s * c s := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun s _ => ?_)
    ring
  rw [h2] at hftc
  linear_combination -hftc

/-- **FTC characterization (continuity variant)** — for the piecewise-polynomial DCF: `F`
differentiable only on the OPEN `(v,σ)` but continuous on closed `[v,σ]` (matching `matDCFreCore`,
which may have a kink at `σ`). -/
theorem shellKernel_eq_of_hasDeriv_of_continuousOn {c F : ℝ → ℝ} {sigma v : ℝ}
    (hv : v ∈ Set.Ioo (0 : ℝ) sigma) (hFσ : F sigma = 0)
    (hFc : ContinuousOn F (Set.Icc v sigma))
    (hderiv : ∀ s ∈ Set.Ioo v sigma, HasDerivAt F (-(2 * Real.pi * s * c s)) s)
    (hint : IntervalIntegrable (fun s => -(2 * Real.pi * s * c s)) volume v sigma) :
    shellKernel c sigma v = F v := by
  unfold shellKernel
  rw [abs_of_pos hv.1]
  have hftc : ∫ s in v..sigma, -(2 * Real.pi * s * c s) = F sigma - F v :=
    intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hv.2.le hFc
      (fun s hs => (hderiv s hs).hasDerivWithinAt) hint
  rw [hFσ, zero_sub] at hftc
  have h2 : (∫ s in v..sigma, -(2 * Real.pi * s * c s))
      = -(2 * Real.pi) * ∫ s in v..sigma, s * c s := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun s _ => ?_)
    ring
  rw [h2] at hftc
  linear_combination -hftc

/-- **`hShellDCF` reduced to its differential form.**  The shell-kernel↔DCF identity
`shellKernel(Φᵢₖ)(v) = matDCFreCore(i,k)(v)/ρ` on `(0,σ)` holds iff `matDCFreCore/ρ` vanishes at `σ`
(boundary — provable for equal diameters, `q0` and the correlation both vanish at `σ`) and satisfies
the DIFFERENTIAL relation `(matDCFreCore/ρ)'(s) = −2π·s·Φᵢₖ(s)`.  So even at equal diameters the
identity is the differential Baxter–WH relation between the DCF core and the forcing `Φ` — the
residual open content, isolated here to a first-order ODE. -/
theorem hShellDCF_of_deriv (Phi : Matrix (Fin 2) (Fin 2) (ℝ → ℝ)) (rhoV sigmaV : Fin 2 → ℝ)
    (hsigV : ∀ k, 0 < sigmaV k) {sigma rho : ℝ} (i k : Fin 2)
    (hbdry : matDCFreCore rhoV sigmaV hsigV i k sigma / rho = 0)
    (hFc : ∀ v ∈ Set.Ioo (0 : ℝ) sigma,
      ContinuousOn (fun w => matDCFreCore rhoV sigmaV hsigV i k w / rho) (Set.Icc v sigma))
    (hderiv : ∀ s ∈ Set.Ioo (0 : ℝ) sigma,
      HasDerivAt (fun w => matDCFreCore rhoV sigmaV hsigV i k w / rho)
        (-(2 * Real.pi * s * Phi i k s)) s)
    (hint : ∀ v ∈ Set.Ioo (0 : ℝ) sigma,
      IntervalIntegrable (fun s => -(2 * Real.pi * s * Phi i k s)) volume v sigma)
    (v : ℝ) (hv : v ∈ Set.Ioo (0 : ℝ) sigma) :
    shellKernel (Phi i k) sigma v = matDCFreCore rhoV sigmaV hsigV i k v / rho :=
  shellKernel_eq_of_hasDeriv_of_continuousOn hv hbdry (hFc v hv)
    (fun s hs => hderiv s ⟨lt_trans hv.1 hs.1, hs.2⟩) (hint v hv)
/-! #### Constructive discharge of the ODE `(matDCFreCore/ρ)' = −2π·s·Φ`.  The ODE DEFINES the
forcing `Φᶜ = shellForcing = −matDCFreCore'/(ρ·2π·s)` (the shellKernel-inverse); with it the ODE
holds by construction, so `hShellDCF` reduces to `matDCFreCore`'s C¹ regularity alone
(`hShellDCF_construct`).  The residue is then (a) DCF-core regularity — mechanical for the
piecewise-polynomial DCF — and (b) identifying `shellForcing` with the physical `c_HS` (the open
Baxter–WH content). -/

/-- **The constructed shell-forcing** `Φᶜᵢₖ(s) = −matDCFreCore'(i,k)(s) / (ρ·2π·s)` — the unique
forcing whose shell kernel is `matDCFreCore/ρ` (the shellKernel-inverse, from the FTC/ODE). -/
noncomputable def shellForcing (rhoV sigmaV : Fin 2 → ℝ) (hsigV : ∀ k, 0 < sigmaV k) (rho : ℝ) :
    Matrix (Fin 2) (Fin 2) (ℝ → ℝ) :=
  fun i k => fun s =>
    -(deriv (fun w => matDCFreCore rhoV sigmaV hsigV i k w) s) / (rho * (2 * Real.pi * s))

/-- The ODE `(matDCFreCore/ρ)'(s) = −2π·s·Φᶜᵢₖ(s)` holds BY CONSTRUCTION for `Φᶜ = shellForcing`,
given `matDCFreCore(i,k)` differentiable at `s ≠ 0`. -/
theorem hasDerivAt_matDCFreCore_div {rhoV sigmaV : Fin 2 → ℝ} {hsigV : ∀ k, 0 < sigmaV k}
    {rho : ℝ} {i k : Fin 2} {s : ℝ} (hs : s ≠ 0) (hρ : rho ≠ 0)
    (hd : DifferentiableAt ℝ (fun w => matDCFreCore rhoV sigmaV hsigV i k w) s) :
    HasDerivAt (fun w => matDCFreCore rhoV sigmaV hsigV i k w / rho)
      (-(2 * Real.pi * s * shellForcing rhoV sigmaV hsigV rho i k s)) s := by
  have he : -(2 * Real.pi * s * shellForcing rhoV sigmaV hsigV rho i k s)
      = deriv (fun w => matDCFreCore rhoV sigmaV hsigV i k w) s / rho := by
    simp only [shellForcing]
    field_simp
  rw [he]
  exact hd.hasDerivAt.div_const rho

/-- **Constructive discharge of `hShellDCF`** — with the forcing taken to be `shellForcing` (the
shellKernel-inverse of `matDCFreCore/ρ`), `shellKernel(Φᶜᵢₖ)(v) = matDCFreCore(i,k)(v)/ρ` on `(0,σ)`
holds given ONLY `matDCFreCore`'s C¹ regularity (differentiable + continuous), vanishing at `σ`, and
integrability of its derivative.  So the ODE is discharged; the residue is the DCF-core regularity
(mechanical for the piecewise-polynomial DCF) plus identifying `shellForcing` with the physical DCF
`c_HS` (the open Baxter–WH content). -/
theorem hShellDCF_construct (rhoV sigmaV : Fin 2 → ℝ) (hsigV : ∀ k, 0 < sigmaV k)
    {sigma rho : ℝ} (hρ : rho ≠ 0) (i k : Fin 2)
    (hbdry : matDCFreCore rhoV sigmaV hsigV i k sigma / rho = 0)
    (hFc : ∀ v ∈ Set.Ioo (0 : ℝ) sigma,
      ContinuousOn (fun w => matDCFreCore rhoV sigmaV hsigV i k w / rho) (Set.Icc v sigma))
    (hdiff : ∀ s ∈ Set.Ioo (0 : ℝ) sigma,
      DifferentiableAt ℝ (fun w => matDCFreCore rhoV sigmaV hsigV i k w) s)
    (hint : ∀ v ∈ Set.Ioo (0 : ℝ) sigma, IntervalIntegrable
      (fun s => -(2 * Real.pi * s * shellForcing rhoV sigmaV hsigV rho i k s)) volume v sigma)
    (v : ℝ) (hv : v ∈ Set.Ioo (0 : ℝ) sigma) :
    shellKernel (shellForcing rhoV sigmaV hsigV rho i k) sigma v
      = matDCFreCore rhoV sigmaV hsigV i k v / rho :=
  hShellDCF_of_deriv (shellForcing rhoV sigmaV hsigV rho) rhoV sigmaV hsigV i k hbdry hFc
    (fun s hs => hasDerivAt_matDCFreCore_div (ne_of_gt hs.1) hρ (hdiff s hs)) hint v hv
/-! #### `matDCFreCore` C¹ regularity (item (a) of the `hShellDCF_construct` reduction).  The
linear Baxter term is `C^∞` on the open support (`qWeighted_contDiffOn`, a quadratic — same idea
as `cHSmixRaw_contDiffOn`'s `hqFwd`); `matDCFreCore_contDiffOn_of_corr` then reduces the DCF core's
`ContDiffOn` to the correlation term `matCorrFull`, whose smoothness follows from the proven
`qpConv_contDiffOn` (`matCorrFull = ∑ₗ qpConv/(2π)²`). -/

/-- The linear Baxter term `qWeightedᵢₖ = ρ_geoᵢₖ·q0MixEntry` is `C^∞` on the open support
`(λᵢₖ, Rᵢₖ) = ((σₖ−σᵢ)/2, (σᵢ+σₖ)/2)` — a quadratic there.  Mirrors `hqFwd` in `cHSmixRaw`. -/
theorem qWeighted_contDiffOn (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k) (i k : Fin 2) :
    ContDiffOn ℝ (⊤ : ℕ∞) (qWeighted rho sigma hsig i k)
      (Set.Ioo ((sigma k - sigma i) / 2) ((sigma i + sigma k) / 2)) := by
  refine (ContDiff.contDiffOn (f := fun r => rhoGeoPhys rho i k
      * ((physMix rho sigma hsig).Q0 i k * (r - (physMix rho sigma hsig).R i k)
         + (physMix rho sigma hsig).Qpp k * (r - (physMix rho sigma hsig).R i k) ^ 2 / 2))
      (by fun_prop)).congr ?_
  intro x hx
  show rhoGeoPhys rho i k * q0MixEntry (physMix rho sigma hsig) i k x = _
  rw [q0MixEntry, Set.indicator_of_mem (show x ∈ Set.Icc ((physMix rho sigma hsig).lam i k)
    ((physMix rho sigma hsig).R i k) from Set.mem_Icc.mpr ⟨hx.1.le, hx.2.le⟩)]

/-- **`matDCFreCore` C¹ regularity reduced to the correlation.**  Via the physical identification
`matDCFfoldKernel(qWeighted) = matDCFreCore`, `matDCFreCore` is `ContDiffOn` on `s ⊆ (λᵢₖ,Rᵢₖ)`
whenever the reflected linear term `qWeightedₖᵢ(−·)` and the correlation `matCorrFull(qWeighted)ᵢₖ`
are — the forward term is `qWeighted_contDiffOn`.  (For equal diameters on `(0,σ)` the reflected
term is `0`; the correlation's `ContDiffOn` follows from the proven `qpConv_contDiffOn` via
`matCorrFull = ∑ₗ qpConv/(2π)²` — the sole remaining regularity input.) -/
theorem matDCFreCore_contDiffOn_of_corr (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k)
    (i k : Fin 2)
    {s : Set ℝ} (hs : s ⊆ Set.Ioo ((sigma k - sigma i) / 2) ((sigma i + sigma k) / 2))
    (hrefl : ContDiffOn ℝ (⊤ : ℕ∞) (fun v => qWeighted rho sigma hsig k i (-v)) s)
    (hcorr : ContDiffOn ℝ (⊤ : ℕ∞) (fun v => matCorrFull (qWeighted rho sigma hsig) i k v) s) :
    ContDiffOn ℝ (⊤ : ℕ∞) (matDCFreCore rho sigma hsig i k) s := by
  have hlin : ContDiffOn ℝ (⊤ : ℕ∞) (qWeighted rho sigma hsig i k) s :=
    (qWeighted_contDiffOn rho sigma hsig i k).mono hs
  refine ((hlin.add hrefl).sub hcorr).congr (fun x _ => ?_)
  rw [← matDCFfoldKernel_qWeighted_eq_matDCFreCore]
  simp only [matDCFfoldKernel]
/-! #### The normalization bridge `matCorrFull = ∑ₗ qpConv/(2π)²`, completing item (a).  Since
`qFwd = 2π·qWeighted` and `pMixEntry = 2π·qWeighted(−·)`, the correlation is the proven-smooth
convolution `qpConv` over `(2π)²` — so `matCorrFull` (hence `matDCFreCore`) is `C^∞` on the upper
piece `(λᵢₖ,Rᵢₖ)` (= `(0,σ)` at equal diam).  `matDCFreCore_contDiffOn_upper` closes item (a). -/

open FMSA.MixtureHSDCF FMSA.MixtureConvolution
open scoped Convolution

/-- **Normalization bridge** — the full-line correlation is the proven-smooth convolution `qpConv`
divided by `(2π)²`: `matCorrFull(qWeighted)ᵢₖ(v) = ∑ₗ qpConv(physMix)ᵢₗₖ(v)/(2π)²`.  Since
`qFwd = 2π·qWeighted` and `pMixEntry = 2π·qWeighted(−·)`, the convolution integrand is `(2π)²·` the
correlation integrand.  This carries `matCorrFull`'s `ContDiffOn` from `qpConv_contDiffOn`. -/
theorem matCorrFull_eq_qpConv (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k) (i k : Fin 2)
    (v : ℝ) :
    matCorrFull (qWeighted rho sigma hsig) i k v
      = ∑ l, qpConv (physMix rho sigma hsig) i l k v / (2 * Real.pi) ^ 2 := by
  simp only [matCorrFull]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  have hqFwd : ∀ t, qFwd (physMix rho sigma hsig) i l t
      = 2 * Real.pi * qWeighted rho sigma hsig i l t := by
    intro t; simp only [qFwd, qWeighted, rhoGeoPhys, physMix]; ring
  have hpMix : ∀ u, pMixEntry (physMix rho sigma hsig) k l u
      = 2 * Real.pi * qWeighted rho sigma hsig k l (-u) := by
    intro u; simp only [pMixEntry, qWeighted, rhoGeoPhys, physMix]; ring
  rw [show qpConv (physMix rho sigma hsig) i l k v
      = ∫ t, qFwd (physMix rho sigma hsig) i l t
          * pMixEntry (physMix rho sigma hsig) k l (v - t) from rfl,
    ← integral_div]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
  dsimp only
  rw [hqFwd, hpMix, show -(v - t) = t - v from by ring]
  have h2π : (2 * Real.pi) ^ 2 ≠ 0 := by positivity
  field_simp

/-- `matCorrFull(qWeighted)ᵢₖ` is `C^∞` on the upper piece `(λᵢₖ,Rᵢₖ)` — from the proven
`qpConv_contDiffOn_upper` via the normalization bridge `matCorrFull = ∑ₗ qpConv/(2π)²`. -/
theorem matCorrFull_contDiffOn_upper (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k) (i k : Fin 2)
    (hlam : 0 ≤ (sigma k - sigma i) / 2) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun v => matCorrFull (qWeighted rho sigma hsig) i k v)
      (Set.Ioo ((sigma k - sigma i) / 2) ((sigma i + sigma k) / 2)) := by
  have heq : (fun v => matCorrFull (qWeighted rho sigma hsig) i k v)
      = fun v => ∑ l, qpConv (physMix rho sigma hsig) i l k v / (2 * Real.pi) ^ 2 := by
    funext v; exact matCorrFull_eq_qpConv rho sigma hsig i k v
  rw [heq]
  refine ContDiffOn.sum (fun l _ => ?_)
  exact (qpConv_contDiffOn_upper (physMix rho sigma hsig) i l k hlam).div_const _

/-- On the upper piece `(λᵢₖ,Rᵢₖ)` the reflected linear term `qWeightedₖᵢ(−·)` vanishes (its support
lies below), so it is `C^∞` (constant `0`). -/
theorem qWeightedRefl_contDiffOn_upper (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k)
    (i k : Fin 2) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun v => qWeighted rho sigma hsig k i (-v))
      (Set.Ioo ((sigma k - sigma i) / 2) ((sigma i + sigma k) / 2)) := by
  refine (contDiff_const (c := (0 : ℝ))).contDiffOn.congr (fun x hx => ?_)
  refine qWeighted_eq_zero_of_notMem rho sigma hsig k i (fun hmem => ?_)
  rw [Set.mem_Icc] at hmem
  linarith [hmem.1, hx.1]

/-- **`matDCFreCore` is `C^∞` on the upper piece `(λᵢₖ,Rᵢₖ)`** (equal diameters: this is `(0,σ)` —
item (a) of the `hShellDCF_construct` reduction, now fully discharged there). -/
theorem matDCFreCore_contDiffOn_upper (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k)
    (i k : Fin 2)
    (hlam : 0 ≤ (sigma k - sigma i) / 2) :
    ContDiffOn ℝ (⊤ : ℕ∞) (matDCFreCore rho sigma hsig i k)
      (Set.Ioo ((sigma k - sigma i) / 2) ((sigma i + sigma k) / 2)) :=
  matDCFreCore_contDiffOn_of_corr rho sigma hsig i k (le_refl _)
    (qWeightedRefl_contDiffOn_upper rho sigma hsig i k)
    (matCorrFull_contDiffOn_upper rho sigma hsig i k hlam)
/-! #### Item (b) — `shellForcing = c_HS` IS the open Baxter–WH gap, characterized by uniqueness.
`shellKernel` has derivative `−2π·v·c(v)` (`shellKernel_hasDerivAt`, FTC lower-limit), so any
continuous forcing `Φ` satisfying `hShellDCF` is FORCED to equal `shellForcing`
(`forcing_eq_shellForcing_of_hShellDCF`, differentiate the identity).  Hence identifying
`c_HS` with `shellForcing` = the claim `c_HS` satisfies `hShellDCF` — no independent content; the
residue is the Baxter–WH factorization (and `c_HS`, the mixture real-space PY DCF, is not even
defined in-project — the deferred Wertheim closed form). -/

open FMSA.HardSphere

/-- **Derivative of `shellKernel`** — `(shellKernel c σ)'(v) = −2π·v·c(v)` on `(0,σ)` (`c` cont.),
by the FTC lower-limit rule (`|v| = v` locally). -/
theorem shellKernel_hasDerivAt {c : ℝ → ℝ} {sigma : ℝ} (hc : Continuous c) {v : ℝ}
    (hv : v ∈ Set.Ioo (0 : ℝ) sigma) :
    HasDerivAt (fun w => shellKernel c sigma w) (-(2 * Real.pi * v * c v)) v := by
  have hcf : Continuous (fun s => s * c s) := by fun_prop
  have hd : HasDerivAt (fun w => ∫ s in w..sigma, s * c s) (-(v * c v)) v :=
    intervalIntegral.integral_hasDerivAt_left (hcf.intervalIntegrable _ _)
      hcf.aestronglyMeasurable.stronglyMeasurableAtFilter hcf.continuousAt
  have h2 : HasDerivAt (fun w => 2 * Real.pi * ∫ s in w..sigma, s * c s)
      (-(2 * Real.pi * v * c v)) v := by
    rw [show (-(2 * Real.pi * v * c v)) = 2 * Real.pi * (-(v * c v)) from by ring]
    exact hd.const_mul (2 * Real.pi)
  have hloc : (fun w => shellKernel c sigma w)
      =ᶠ[nhds v] (fun w => 2 * Real.pi * ∫ s in w..sigma, s * c s) := by
    filter_upwards [Ioi_mem_nhds hv.1] with w hw
    rw [Set.mem_Ioi] at hw
    simp only [shellKernel, abs_of_pos hw]
  exact h2.congr_of_eventuallyEq hloc

/-- **Uniqueness of the forcing (item (b) characterization).**  ANY continuous `Φ` satisfying
the shell-kernel↔DCF identity `hShellDCF` (`shellKernel Φ = matDCFreCore/ρ` on `(0,σ)`) is FORCED to
equal `shellForcing` there — differentiate the identity: `−2π·v·Φ(v) = (matDCFreCore/ρ)'(v)`.  So
identifying the physical `c_HS` with `shellForcing` is EXACTLY the claim that `c_HS` satisfies
`hShellDCF` — the open Baxter–WH gap; there is no independent content. -/
theorem forcing_eq_shellForcing_of_hShellDCF (rhoV sigmaV : Fin 2 → ℝ) (hsigV : ∀ k, 0 < sigmaV k)
    {sigma rho : ℝ} (hρ : rho ≠ 0) (i k : Fin 2) (Phi : ℝ → ℝ) (hΦ : Continuous Phi)
    (hSK : ∀ v ∈ Set.Ioo (0 : ℝ) sigma,
      shellKernel Phi sigma v = matDCFreCore rhoV sigmaV hsigV i k v / rho)
    (v : ℝ) (hv : v ∈ Set.Ioo (0 : ℝ) sigma) :
    Phi v = shellForcing rhoV sigmaV hsigV rho i k v := by
  have hL : HasDerivAt (fun w => shellKernel Phi sigma w) (-(2 * Real.pi * v * Phi v)) v :=
    shellKernel_hasDerivAt hΦ hv
  have heq : (fun w => shellKernel Phi sigma w)
      =ᶠ[nhds v] (fun w => matDCFreCore rhoV sigmaV hsigV i k w / rho) := by
    filter_upwards [isOpen_Ioo.mem_nhds hv] with w hw
    exact hSK w hw
  have hderivval : deriv (fun w => matDCFreCore rhoV sigmaV hsigV i k w / rho) v
      = -(2 * Real.pi * v * Phi v) := (hL.congr_of_eventuallyEq heq.symm).deriv
  rw [deriv_div_const] at hderivval
  have hdv : deriv (fun w => matDCFreCore rhoV sigmaV hsigV i k w) v
      = -(2 * Real.pi * v * Phi v) * rho := (div_eq_iff hρ).mp hderivval
  have hv0 : v ≠ 0 := ne_of_gt hv.1
  have hπ : (2 : ℝ) * Real.pi ≠ 0 := by positivity
  simp only [shellForcing, hdv]
  field_simp

/-! #### C¹ regularity of `matDCFreCore` — discharging the `hdiff`/`hFc`/`hbdry` inputs of
`hShellDCF_construct` / `matShellConvAsym_matDCFreCore_eq_shellForcing`.  `matDCFreCore` is `C^∞` on
the OPEN upper piece (`matDCFreCore_contDiffOn_upper`), continuous up to the boundary `σ` (the
correlation is globally continuous, `matCorrFull_continuous`), and vanishes at `σ`. -/

/-- **`matDCFreCore` is differentiable on the open upper piece** `(λᵢₖ, Rᵢₖ)` — from
`matDCFreCore_contDiffOn_upper` (`C^∞` there).  Discharges the `hdiff` hypothesis. -/
theorem matDCFreCore_differentiableAt (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k)
    (i k : Fin 2) (hlam : 0 ≤ (sigma k - sigma i) / 2)
    {s : ℝ} (hs : s ∈ Set.Ioo ((sigma k - sigma i) / 2) ((sigma i + sigma k) / 2)) :
    DifferentiableAt ℝ (fun w => matDCFreCore rho sigma hsig i k w) s := by
  have hcd := matDCFreCore_contDiffOn_upper rho sigma hsig i k hlam
  have hdon : DifferentiableOn ℝ (matDCFreCore rho sigma hsig i k)
      (Set.Ioo ((sigma k - sigma i) / 2) ((sigma i + sigma k) / 2)) :=
    hcd.differentiableOn (by simp)
  exact (hdon s hs).differentiableAt (isOpen_Ioo.mem_nhds hs)

open FMSA.MatrixQ0 in
/-- **`matCorrFull(qWeighted)` is globally continuous** — each species term is `√(ρᵢρₘ)√(ρₖρₘ)`
times the `q0MixEntry` autocorrelation, whose continuity is `q0MixEntry_corr_continuous` (via the
real part of the complex integral).  Needed for `matDCFreCore`'s continuity up to the boundary. -/
theorem matCorrFull_continuous (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k) (i k : Fin 2) :
    Continuous (fun v => matCorrFull (qWeighted rho sigma hsig) i k v) := by
  unfold matCorrFull
  refine continuous_finsetSum Finset.univ (fun m _ => ?_)
  have hcong : (fun v => ∫ t, qWeighted rho sigma hsig i m t * qWeighted rho sigma hsig k m (t - v))
      = fun v => rhoGeoPhys rho i m * rhoGeoPhys rho k m
          * (∫ t, (q0MixEntry (physMix rho sigma hsig) i m t : ℂ)
                * (q0MixEntry (physMix rho sigma hsig) k m (t - v) : ℂ)).re := by
    funext v
    have hre : (∫ t, (q0MixEntry (physMix rho sigma hsig) i m t : ℂ)
            * (q0MixEntry (physMix rho sigma hsig) k m (t - v) : ℂ)).re
          = ∫ t, q0MixEntry (physMix rho sigma hsig) i m t
                * q0MixEntry (physMix rho sigma hsig) k m (t - v) := by
      simp_rw [← Complex.ofReal_mul]
      rw [integral_complex_ofReal, Complex.ofReal_re]
    rw [hre, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
    simp only [qWeighted]; ring
  rw [hcong]
  exact continuous_const.mul (Complex.continuous_re.comp (q0MixEntry_corr_continuous _ i k m))

open FMSA.MatrixQ0 in
/-- **`matDCFreCore` is continuous up to the boundary** — `ContinuousOn [v,σ]` (equal diameters,
`0 < v < σ`).  On `[v,σ] ⊆ [0,σ]` the forward linear term is `= √(ρᵢρₖ)·(quadratic)` (indicator
`= 1`), the reflected term vanishes (support below `0`), and the correlation is globally continuous
(`matCorrFull_continuous`).  Discharges `hFc`. -/
theorem matDCFreCore_continuousOn_Icc (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k)
    {σ : ℝ} (hED : ∀ n, sigma n = σ) (i k : Fin 2) {v : ℝ} (hv : v ∈ Set.Ioo (0 : ℝ) σ) :
    ContinuousOn (fun w => matDCFreCore rho sigma hsig i k w) (Set.Icc v σ) := by
  have hlam : (physMix rho sigma hsig).lam i k = 0 := by simp only [physMix, Mix.lam, hED]; ring
  have hR : (physMix rho sigma hsig).R i k = σ := by simp only [physMix, Mix.R, hED]; ring
  have hfold : (fun w => matDCFreCore rho sigma hsig i k w)
      = fun w => qWeighted rho sigma hsig i k w + qWeighted rho sigma hsig k i (-w)
          - matCorrFull (qWeighted rho sigma hsig) i k w := by
    funext w; rw [← matDCFfoldKernel_qWeighted_eq_matDCFreCore]; simp only [matDCFfoldKernel]
  rw [hfold]
  refine ContinuousOn.sub (ContinuousOn.add ?_ ?_) ?_
  · refine (Continuous.continuousOn (by fun_prop :
        Continuous (fun w => rhoGeoPhys rho i k
          * ((physMix rho sigma hsig).Q0 i k * (w - (physMix rho sigma hsig).R i k)
            + (physMix rho sigma hsig).Qpp k
              * (w - (physMix rho sigma hsig).R i k) ^ 2 / 2)))).congr (fun w hw => ?_)
    simp only [qWeighted]
    rw [Set.mem_Icc] at hw
    congr 1
    unfold q0MixEntry
    rw [Set.indicator_of_mem (by rw [Set.mem_Icc, hlam, hR]; exact ⟨le_trans hv.1.le hw.1, hw.2⟩)]
  · refine (continuousOn_const (c := (0 : ℝ))).congr (fun w hw => ?_)
    rw [Set.mem_Icc] at hw
    simp only [qWeighted]
    rw [q0_physMix_eq_zero_of_notMem rho sigma hsig k i
      (fun hmem => by rw [Set.mem_Icc] at hmem; linarith [hv.1, hw.1, hED i, hED k, hmem.1]),
      mul_zero]
  · exact (matCorrFull_continuous rho sigma hsig i k).continuousOn

open FMSA.MatrixQ0 in
/-- **`matDCFreCore` vanishes at the boundary `σ`** (equal diameters).  The forward Baxter quadratic
vanishes at `R = σ`, the reflected term's support is below `0`, and the correlation integrand is `0`
(the supports `[0,σ]` and `[σ,2σ]` touch only at `t = σ`, where the forward factor is already `0`).
Discharges `hbdry`. -/
theorem matDCFreCore_boundary (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k)
    {σ : ℝ} (hED : ∀ n, sigma n = σ) (i k : Fin 2) :
    matDCFreCore rho sigma hsig i k σ = 0 := by
  have hσ0 : 0 < σ := by rw [← hED 0]; exact hsig 0
  have hlam : ∀ a b : Fin 2, (physMix rho sigma hsig).lam a b = 0 := by
    intro a b; simp only [physMix, Mix.lam, hED]; ring
  have hR : ∀ a b : Fin 2, (physMix rho sigma hsig).R a b = σ := by
    intro a b; simp only [physMix, Mix.R, hED]; ring
  have hq0σ : ∀ a b : Fin 2, q0MixEntry (physMix rho sigma hsig) a b σ = 0 := by
    intro a b
    unfold q0MixEntry
    rw [Set.indicator_of_mem (by rw [Set.mem_Icc, hlam, hR]; exact ⟨hσ0.le, le_refl _⟩), hR]
    ring
  rw [← matDCFfoldKernel_qWeighted_eq_matDCFreCore]
  simp only [matDCFfoldKernel]
  have h1 : qWeighted rho sigma hsig i k σ = 0 := by simp only [qWeighted, hq0σ, mul_zero]
  have h2 : qWeighted rho sigma hsig k i (-σ) = 0 := by
    simp only [qWeighted]
    rw [q0_physMix_eq_zero_of_notMem rho sigma hsig k i
      (fun hmem => by rw [Set.mem_Icc] at hmem; linarith [hσ0, hED i, hED k, hmem.1]), mul_zero]
  have h3 : matCorrFull (qWeighted rho sigma hsig) i k σ = 0 := by
    simp only [matCorrFull]
    refine Finset.sum_eq_zero (fun m _ => ?_)
    have hz : (fun t => qWeighted rho sigma hsig i m t * qWeighted rho sigma hsig k m (t - σ))
        = fun _ => (0 : ℝ) := by
      funext t
      rcases lt_trichotomy t σ with ht | ht | ht
      · have : qWeighted rho sigma hsig k m (t - σ) = 0 := by
          simp only [qWeighted]
          rw [q0_physMix_eq_zero_of_notMem rho sigma hsig k m
            (fun hmem => by rw [Set.mem_Icc] at hmem; linarith [hED k, hED m, hmem.1]), mul_zero]
        rw [this, mul_zero]
      · have hzσ : qWeighted rho sigma hsig i m σ = 0 := by simp only [qWeighted, hq0σ, mul_zero]
        rw [ht, hzσ, zero_mul]
      · have : qWeighted rho sigma hsig i m t = 0 := by
          simp only [qWeighted]
          rw [q0_physMix_eq_zero_of_notMem rho sigma hsig i m
            (fun hmem => by rw [Set.mem_Icc] at hmem; linarith [hED i, hED m, hmem.2]), mul_zero]
        rw [this, zero_mul]
    rw [hz, integral_zero]
  rw [h1, h2, h3]; ring

/-! #### `matCorrFull`'s derivative bound at `σ`, via Lipschitz.  The kink at `σ` blocks the naive
`ContDiffOn`-on-a-neighborhood route, but `matDCFreCore` is LIPSCHITZ on `Ici 0` (so its `deriv` is
bounded on the interior), because on `[0,∞)` the Baxter kernel's only jump (at the left edge `0`) is
never crossed and the quadratic vanishes at the right edge `σ`.  This is the analytic input that
bounds `matCorrFull'` up to `σ` — the last `hint` residual. -/

open FMSA.MatrixQ0 in
/-- **`qWeighted i m` is Lipschitz on `Ici 0`** (equal diameters).  On `[0,∞)` the left-edge jump at
`0` is never crossed, and the quadratic vanishes at the right edge `σ`, so
`q0MixEntry i m x = quad(min x σ)` there — a Lipschitz composition (`quad` Lipschitz on the compact
`[0,σ]`, `min · σ` is `1`-Lipschitz).  This is the ingredient that makes `matCorrFull` Lipschitz. -/
theorem qWeighted_lipschitzOnWith (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k)
    {σ : ℝ} (hED : ∀ n, sigma n = σ) (i m : Fin 2) :
    ∃ K : NNReal, LipschitzOnWith K (fun x => qWeighted rho sigma hsig i m x) (Set.Ici 0) := by
  set X := physMix rho sigma hsig with hX
  have hR : X.R i m = σ := by simp only [hX, physMix, Mix.R, hED]; ring
  have hlam : X.lam i m = 0 := by simp only [hX, physMix, Mix.lam, hED]; ring
  have hσ0 : 0 < σ := by rw [← hED 0]; exact hsig 0
  set a := X.Q0 i m with ha
  set b := X.Qpp m with hb
  have hq0 : ∀ x : ℝ, 0 ≤ x → q0MixEntry X i m x
      = a * (min x σ - σ) + b * (min x σ - σ) ^ 2 / 2 := by
    intro x hx
    simp only [q0MixEntry, hlam, hR, ← ha, ← hb]
    by_cases hxσ : x ≤ σ
    · rw [Set.indicator_of_mem (by rw [Set.mem_Icc]; exact ⟨hx, hxσ⟩), min_eq_left hxσ]
    · rw [Set.indicator_of_notMem (by rw [Set.mem_Icc, not_and_or]; exact Or.inr (by
          push_neg; exact lt_of_not_ge hxσ)), min_eq_right (le_of_not_ge hxσ), sub_self]
      ring
  refine ⟨Real.toNNReal (|rhoGeoPhys rho i m| * (|a| + |b| * σ)), ?_⟩
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  rw [Set.mem_Ici] at hx hy
  simp only [Real.dist_eq]
  have hqW : ∀ z : ℝ, qWeighted rho sigma hsig i m z = rhoGeoPhys rho i m * q0MixEntry X i m z :=
    fun z => by simp only [qWeighted, hX]
  rw [hqW x, hqW y, hq0 x hx, hq0 y hy]
  set u := min x σ with hu
  set v := min y σ with hv
  have hu0 : 0 ≤ u := le_min hx hσ0.le
  have huσ : u ≤ σ := min_le_right _ _
  have hv0 : 0 ≤ v := le_min hy hσ0.le
  have hvσ : v ≤ σ := min_le_right _ _
  have huv : |u - v| ≤ |x - y| := by
    have h := (LipschitzWith.min_const LipschitzWith.id σ).dist_le_mul x y
    simp only [Real.dist_eq, NNReal.coe_one, one_mul] at h
    exact h
  have hfac : rhoGeoPhys rho i m * (a * (u - σ) + b * (u - σ) ^ 2 / 2)
      - rhoGeoPhys rho i m * (a * (v - σ) + b * (v - σ) ^ 2 / 2)
      = rhoGeoPhys rho i m * (u - v) * (a + b * (u + v - 2 * σ) / 2) := by ring
  rw [hfac, abs_mul, abs_mul]
  have hbnd : |a + b * (u + v - 2 * σ) / 2| ≤ |a| + |b| * σ := by
    calc |a + b * (u + v - 2 * σ) / 2| ≤ |a| + |b * (u + v - 2 * σ) / 2| := abs_add_le _ _
      _ = |a| + |b| * (|u + v - 2 * σ| / 2) := by rw [abs_div, abs_mul]; simp; ring
      _ ≤ |a| + |b| * σ := by
          have : |u + v - 2 * σ| ≤ 2 * σ := by rw [abs_le]; constructor <;> linarith
          nlinarith [this, abs_nonneg b]
  have hK : (Real.toNNReal (|rhoGeoPhys rho i m| * (|a| + |b| * σ)) : ℝ)
      = |rhoGeoPhys rho i m| * (|a| + |b| * σ) :=
    Real.coe_toNNReal _ (mul_nonneg (abs_nonneg _) (by positivity))
  rw [hK]
  calc |rhoGeoPhys rho i m| * |u - v| * |a + b * (u + v - 2 * σ) / 2|
      ≤ |rhoGeoPhys rho i m| * |x - y| * (|a| + |b| * σ) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left huv (abs_nonneg _)) hbnd (abs_nonneg _)
        exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
    _ = |rhoGeoPhys rho i m| * (|a| + |b| * σ) * |x - y| := by ring

/-- **`matCorrFull` is Lipschitz on `Ici 0`** (equal diameters) — hence its derivative is bounded on
the interior, the `matCorrFull'`-at-`σ` fact.  In the SUBSTITUTED form `∑ₘ ∫ qim(u+v)·qkm(u) du` the
moving kernel `qim` has argument `u+v ≥ 0` (its left-edge jump at `0` is never reached), so
`qWeighted_lipschitzOnWith` bounds the integrand difference pointwise — NO region-split.  Lipschitz
constant `∑ₘ Lip(qim)·‖qkm‖₁`. -/
theorem matCorrFull_lipschitzOnWith (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k)
    {σ : ℝ} (hED : ∀ n, sigma n = σ) (i k : Fin 2) :
    ∃ C : NNReal, LipschitzOnWith C
      (fun v => matCorrFull (qWeighted rho sigma hsig) i k v) (Set.Ici 0) := by
  choose Kq hKq using fun m => qWeighted_lipschitzOnWith rho sigma hsig hED i m
  set L1 : Fin 2 → ℝ := fun m => ∫ u, |qWeighted rho sigma hsig k m u| with hL1
  refine ⟨∑ m, Kq m * Real.toNNReal (L1 m), ?_⟩
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro v hv w hw
  rw [Set.mem_Ici] at hv hw
  simp only [Real.dist_eq]
  have hterm : ∀ m : Fin 2,
      |(∫ t, qWeighted rho sigma hsig i m t * qWeighted rho sigma hsig k m (t - v))
        - (∫ t, qWeighted rho sigma hsig i m t * qWeighted rho sigma hsig k m (t - w))|
      ≤ (Kq m : ℝ) * L1 m * |v - w| := by
    intro m
    set qim := qWeighted rho sigma hsig i m with hqim
    set qkm := qWeighted rho sigma hsig k m with hqkm
    have hsub : ∀ s : ℝ, (∫ t, qim t * qkm (t - s)) = ∫ u, qim (u + s) * qkm u := by
      intro s
      have h := integral_sub_right_eq_self (μ := volume) (fun t => qim t * qkm (t - s)) (-s)
      simpa using h.symm
    rw [hsub v, hsub w]
    have hbd : ∀ s : ℝ, ∀ᵐ u : ℝ,
        ‖qim (u + s)‖ ≤ (qWeighted_abs_le rho sigma hsig i m).choose := by
      intro s; filter_upwards with u
      rw [Real.norm_eq_abs]; exact (qWeighted_abs_le rho sigma hsig i m).choose_spec (u + s)
    have hint : ∀ s : ℝ, Integrable (fun u => qim (u + s) * qkm u) := by
      intro s
      exact (qWeighted_integrable rho sigma hsig k m).bdd_mul
        ((qWeighted_measurable rho sigma hsig i m).comp (by fun_prop)).aestronglyMeasurable (hbd s)
    rw [← integral_sub (hint v) (hint w)]
    calc |∫ u, (qim (u + v) * qkm u - qim (u + w) * qkm u)|
        ≤ ∫ u, |qim (u + v) * qkm u - qim (u + w) * qkm u| := abs_integral_le_integral_abs
      _ ≤ ∫ u, (Kq m : ℝ) * |v - w| * |qkm u| := by
          refine integral_mono ((hint v).sub (hint w)).abs
            ((qWeighted_integrable rho sigma hsig k m).abs.const_mul ((Kq m : ℝ) * |v - w|))
            (fun u => ?_)
          rw [show qim (u + v) * qkm u - qim (u + w) * qkm u
              = (qim (u + v) - qim (u + w)) * qkm u from by ring, abs_mul]
          by_cases hqk : qkm u = 0
          · rw [hqk, abs_zero, mul_zero]; positivity
          · have humem : u ∈ Set.Icc ((sigma m - sigma k) / 2) ((sigma k + sigma m) / 2) := by
              by_contra hc
              exact hqk (qWeighted_eq_zero_of_notMem rho sigma hsig k m hc)
            have hu0 : (0 : ℝ) ≤ u := by
              rw [Set.mem_Icc] at humem
              have hz : (sigma m - sigma k) / 2 = 0 := by rw [hED, hED]; ring
              linarith [humem.1, hz.ge]
            have hlip := (hKq m).dist_le_mul (u + v) (Set.mem_Ici.mpr (by linarith))
              (u + w) (Set.mem_Ici.mpr (by linarith))
            simp only [Real.dist_eq] at hlip
            have hqd : |qim (u + v) - qim (u + w)| ≤ (Kq m : ℝ) * |v - w| := by
              refine hlip.trans (le_of_eq ?_)
              congr 1; rw [show u + v - (u + w) = v - w from by ring]
            exact mul_le_mul_of_nonneg_right hqd (abs_nonneg _)
      _ = (Kq m : ℝ) * L1 m * |v - w| := by
          rw [integral_const_mul]; simp only [hL1, hqkm]; ring
  simp only [matCorrFull]
  rw [← Finset.sum_sub_distrib]
  calc |∑ m, ((∫ t, qWeighted rho sigma hsig i m t * qWeighted rho sigma hsig k m (t - v))
          - ∫ t, qWeighted rho sigma hsig i m t * qWeighted rho sigma hsig k m (t - w))|
      ≤ ∑ m, |(∫ t, qWeighted rho sigma hsig i m t * qWeighted rho sigma hsig k m (t - v))
          - ∫ t, qWeighted rho sigma hsig i m t * qWeighted rho sigma hsig k m (t - w)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m, (Kq m : ℝ) * L1 m * |v - w| := Finset.sum_le_sum (fun m _ => hterm m)
    _ = (↑(∑ m, Kq m * Real.toNNReal (L1 m)) : ℝ) * |v - w| := by
        rw [NNReal.coe_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun m _ => ?_)
        rw [NNReal.coe_mul, Real.coe_toNNReal _ (integral_nonneg (fun u => abs_nonneg _))]

/-- **`matDCFreCore` is Lipschitz on `Ioi 0`** (equal diameters) — combine
`qWeighted_lipschitzOnWith` and `matCorrFull_lipschitzOnWith`: on `Ioi 0` the reflected term
vanishes so `matDCFreCore = qWeighted i k − matCorrFull`.  Its `deriv` is then bounded. -/
theorem matDCFreCore_lipschitzOnWith (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k)
    {σ : ℝ} (hED : ∀ n, sigma n = σ) (i k : Fin 2) :
    ∃ C : NNReal, LipschitzOnWith C
      (fun v => matDCFreCore rho sigma hsig i k v) (Set.Ioi 0) := by
  obtain ⟨Kik, hKik⟩ := qWeighted_lipschitzOnWith rho sigma hsig hED i k
  obtain ⟨Cc, hCc⟩ := matCorrFull_lipschitzOnWith rho sigma hsig hED i k
  refine ⟨Kik + Cc, ?_⟩
  have heq : ∀ z : ℝ, 0 < z → matDCFreCore rho sigma hsig i k z
      = qWeighted rho sigma hsig i k z - matCorrFull (qWeighted rho sigma hsig) i k z := by
    intro z hz
    rw [← matDCFfoldKernel_qWeighted_eq_matDCFreCore]
    simp only [matDCFfoldKernel]
    have hrefl : qWeighted rho sigma hsig k i (-z) = 0 := by
      simp only [qWeighted]
      rw [q0_physMix_eq_zero_of_notMem rho sigma hsig k i (fun hmem => by
        rw [Set.mem_Icc] at hmem
        have hz0 : (sigma i - sigma k) / 2 = 0 := by rw [hED, hED]; ring
        linarith [hmem.1, hz0.ge, hz]), mul_zero]
    rw [hrefl]; ring
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  rw [Set.mem_Ioi] at hx hy
  simp only [Real.dist_eq]
  rw [heq x hx, heq y hy]
  have h1 := (hKik.dist_le_mul x (Set.mem_Ici.mpr hx.le) y (Set.mem_Ici.mpr hy.le))
  have h2 := (hCc.dist_le_mul x (Set.mem_Ici.mpr hx.le) y (Set.mem_Ici.mpr hy.le))
  simp only [Real.dist_eq] at h1 h2
  rw [NNReal.coe_add]
  calc |qWeighted rho sigma hsig i k x - matCorrFull (qWeighted rho sigma hsig) i k x
        - (qWeighted rho sigma hsig i k y - matCorrFull (qWeighted rho sigma hsig) i k y)|
      = |(qWeighted rho sigma hsig i k x - qWeighted rho sigma hsig i k y)
        - (matCorrFull (qWeighted rho sigma hsig) i k x
            - matCorrFull (qWeighted rho sigma hsig) i k y)| := by ring_nf
    _ ≤ |qWeighted rho sigma hsig i k x - qWeighted rho sigma hsig i k y|
        + |matCorrFull (qWeighted rho sigma hsig) i k x
            - matCorrFull (qWeighted rho sigma hsig) i k y| := abs_sub _ _
    _ ≤ (Kik : ℝ) * |x - y| + (Cc : ℝ) * |x - y| := add_le_add h1 h2
    _ = ((Kik : ℝ) + (Cc : ℝ)) * |x - y| := by ring

/-! #### `hint` — integrability of the shell forcing.  On `[v,σ]` (`0 < v ≤ σ`) the integrand
`−2π·s·shellForcing = deriv(matDCFreCore)/ρ` (the `2π·s` cancels), so `hint` reduces to
`deriv(matDCFreCore)` being interval-integrable.  Its derivative is CONTINUOUS on the open interior
(`matDCFreCore_deriv_continuousOn`), so the interior is integrable; the only residual is the
single-point behavior at the boundary `σ` (the convolution's derivative there), left to the
caller. -/

/-- **`matDCFreCore`'s derivative is continuous on the open upper piece** — from
`matDCFreCore_contDiffOn_upper` (`C^∞`).  So `deriv(matDCFreCore)` is interval-integrable on every
compact SUBinterval of the interior; only the boundary point `σ` is left for `hint`. -/
theorem matDCFreCore_deriv_continuousOn (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k)
    (i k : Fin 2) (hlam : 0 ≤ (sigma k - sigma i) / 2) :
    ContinuousOn (deriv (fun w => matDCFreCore rho sigma hsig i k w))
      (Set.Ioo ((sigma k - sigma i) / 2) ((sigma i + sigma k) / 2)) := by
  have hcd := matDCFreCore_contDiffOn_upper rho sigma hsig i k hlam
  exact hcd.continuousOn_deriv_of_isOpen isOpen_Ioo (by simp)

/-- **`hint` reduces to `matDCFreCore`'s derivative being interval-integrable.**  On `[v,σ]` with
`0 < v ≤ σ` the shell-forcing integrand `−2π·s·shellForcing = deriv(matDCFreCore)/ρ` (the `2π·s`
cancels, `s ≠ 0`), so its interval-integrability is exactly that of `deriv(matDCFreCore)/ρ`.  This
strips the `shellForcing`/`ρ`/`s` bookkeeping off `hint`, leaving the pure analytic residual. -/
theorem hint_of_deriv_intervalIntegrable (rhoV sigmaV : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigmaV k)
    {rho v sigma : ℝ} (hρ : rho ≠ 0) (a b : Fin 2) (hv : 0 < v) (hvσ : v ≤ sigma)
    (hD : IntervalIntegrable (fun s => deriv (fun w => matDCFreCore rhoV sigmaV hsig a b w) s)
      volume v sigma) :
    IntervalIntegrable (fun s => -(2 * Real.pi * s * shellForcing rhoV sigmaV hsig rho a b s))
      volume v sigma := by
  refine (hD.div_const rho).congr (fun s hs => ?_)
  rw [Set.uIoc_of_le hvσ, Set.mem_Ioc] at hs
  have hs0 : s ≠ 0 := ne_of_gt (lt_of_lt_of_le hv hs.1.le)
  simp only [shellForcing]
  field_simp

/-- **⭐ `hint` DISCHARGED (equal diameters).**  The shell-forcing integrand is interval-integrable
on `[v,σ]` (`0 < v ≤ σ`): via `hint_of_deriv_intervalIntegrable` it reduces to
`deriv(matDCFreCore)`, bounded on the interior `Ioi 0` by `matDCFreCore_lipschitzOnWith`'s constant
(`norm_deriv_le_of_lipschitzOn`) and measurable (`measurable_deriv`) — so
`Measure.integrableOn_of_bounded` closes it.  This is the LAST mechanical residual of the
shell-inverse reduction; only the open Baxter–WH identification `shellForcing = c_HS` remains. -/
theorem hint_discharged (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k)
    {σ : ℝ} (hED : ∀ n, sigma n = σ) {ρ v : ℝ} (hρ : ρ ≠ 0) (a b : Fin 2)
    (hv : 0 < v) (hvσ : v ≤ σ) :
    IntervalIntegrable (fun s => -(2 * Real.pi * s * shellForcing rho sigma hsig ρ a b s))
      volume v σ := by
  refine hint_of_deriv_intervalIntegrable rho sigma hsig hρ a b hv hvσ ?_
  obtain ⟨C, hC⟩ := matDCFreCore_lipschitzOnWith rho sigma hsig hED a b
  rw [intervalIntegrable_iff, Set.uIoc_of_le hvσ]
  refine Measure.integrableOn_of_bounded (M := (C : ℝ)) measure_Ioc_lt_top.ne
    (measurable_deriv _).aestronglyMeasurable ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with u hu
  rw [Set.mem_Ioc] at hu
  have huioi : Set.Ioi (0 : ℝ) ∈ nhds u :=
    isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr (lt_of_lt_of_le hv hu.1.le))
  exact norm_deriv_le_of_lipschitzOn huioi hC

/-! #### The Baxter–WH identification `shellForcing = c_HS`, reduced to the Baxter ODE.  With every
regularity/boundary input discharged, `shellForcing = c_HS` on `(0,σ)` is now equivalent to the
single pointwise relation `(matDCFreCore/ρ)'(s) = −2π·s·c_HS(s)` — the classical real-space
Baxter–Wertheim factorization, the irreducible open analytic core (the OZ★ value route
`matOzStar_unique` still discharges MML.8 without evaluating it). -/

/-- **⭐ `shellForcing = c_HS` REDUCED to the Baxter ODE.**  Given the pointwise Baxter–Wertheim
differential relation `(matDCFreCore/ρ)'(s) = −2π·s·c_HS(s)` on `(0,σ)`, the physical identification
`shellForcing i k v = c_HS v` holds — every other input (boundary `matDCFreCore(σ)=0`, continuity up
to `σ`, integrability, the shell-kernel inversion `forcing_eq_shellForcing_of_hShellDCF`) is
discharged.  So the whole open Baxter–WH content is EXACTLY this one ODE (a genuine identity in `η`;
the classical real-space factorization, which the route deliberately never evaluates). -/
theorem shellForcing_eq_cHS_of_baxterODE (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k)
    {σ : ℝ} (hED : ∀ n, sigma n = σ) {ρ : ℝ} (hρ : ρ ≠ 0) {eta : ℝ} (i k : Fin 2)
    (hODE : ∀ s ∈ Set.Ioo (0 : ℝ) σ,
      HasDerivAt (fun w => matDCFreCore rho sigma hsig i k w / ρ)
        (-(2 * Real.pi * s
            * -(py_a0 eta + py_a1 eta * (s / σ) + py_a3 eta * (s / σ) ^ 3))) s)
    {v : ℝ} (hv : v ∈ Set.Ioo (0 : ℝ) σ) :
    shellForcing rho sigma hsig ρ i k v = c_HS eta σ v := by
  set Phi : ℝ → ℝ := fun r => -(py_a0 eta + py_a1 eta * (r / σ) + py_a3 eta * (r / σ) ^ 3) with hPhi
  have hcont : Continuous Phi := by simp only [hPhi]; fun_prop
  have hbdry : matDCFreCore rho sigma hsig i k σ / ρ = 0 := by
    rw [matDCFreCore_boundary rho sigma hsig hED i k]; simp
  have hFc : ∀ w ∈ Set.Ioo (0 : ℝ) σ,
      ContinuousOn (fun z => matDCFreCore rho sigma hsig i k z / ρ) (Set.Icc w σ) :=
    fun w hw => (matDCFreCore_continuousOn_Icc rho sigma hsig hED i k hw).div_const ρ
  have hint : ∀ w ∈ Set.Ioo (0 : ℝ) σ,
      IntervalIntegrable (fun s => -(2 * Real.pi * s * Phi s)) volume w σ :=
    fun w _ => (by simp only [hPhi]; fun_prop :
      Continuous fun s => -(2 * Real.pi * s * Phi s)).intervalIntegrable _ _
  have hSK : ∀ w ∈ Set.Ioo (0 : ℝ) σ,
      shellKernel Phi σ w = matDCFreCore rho sigma hsig i k w / ρ :=
    fun w hw => hShellDCF_of_deriv (fun _ _ => Phi) rho sigma hsig i k hbdry hFc hODE hint w hw
  have hforcing := forcing_eq_shellForcing_of_hShellDCF rho sigma hsig hρ i k Phi hcont hSK v hv
  rw [← hforcing, c_HS_inner hv.2]

/-! #### Shell-inverse form of the corrected seed.  With `matDCFreCore/ρ =
shellKernel(shellForcing)` (the constructed forcing, `hShellDCF_construct`), the seed's
DCF-core-kernel `matShellConvAsym`
rewrites into the `shellKernel(shellForcing)`-kernel form — the shell kernel of the shell-inverse
forcing.  This closes the loop: the renewal seed `matBaxterUQmSymFullExt` (via its `qWeighted` fold)
has forcing exactly `shellForcing`; identifying `shellForcing` with `c_HS` is the open Baxter–WH
gap. -/

/-- **Shell-inverse reduction of the seed's DCF-core kernel.**  The `matDCFreCore/ρ`-kernel
`matShellConvAsym` (the physical form of the corrected seed / `matBaxterUQmSymFullExt`) equals the
`matShellConvAsym` whose kernel is `shellKernel(shellForcing)` — the shell kernel of the
shell-inverse forcing.  Since `matDCFreCore/ρ = shellKernel(shellForcing)` on `(0,σ)` by
construction (`hShellDCF_construct`), and the shell convolution only samples its kernel there, the
two agree. -/
theorem matShellConvAsym_matDCFreCore_eq_shellForcing (rhoV sigmaV : Fin 2 → ℝ)
    (hsig : ∀ k, 0 < sigmaV k) {rho sigma : ℝ} (hσ : 0 < sigma) (hρ : rho ≠ 0)
    (G : Matrix (Fin 2) (Fin 2) (ℝ → ℝ)) (r : ℝ) (i j : Fin 2)
    (hbdry : ∀ a b : Fin 2, matDCFreCore rhoV sigmaV hsig a b sigma / rho = 0)
    (hFc : ∀ (a b : Fin 2), ∀ v ∈ Set.Ioo (0 : ℝ) sigma,
      ContinuousOn (fun w => matDCFreCore rhoV sigmaV hsig a b w / rho) (Set.Icc v sigma))
    (hdiff : ∀ (a b : Fin 2), ∀ s ∈ Set.Ioo (0 : ℝ) sigma,
      DifferentiableAt ℝ (fun w => matDCFreCore rhoV sigmaV hsig a b w) s)
    (hint : ∀ (a b : Fin 2), ∀ v ∈ Set.Ioo (0 : ℝ) sigma, IntervalIntegrable
      (fun s => -(2 * Real.pi * s * shellForcing rhoV sigmaV hsig rho a b s)) volume v sigma) :
    matShellConvAsym (fun a b u => matDCFreCore rhoV sigmaV hsig a b u / rho)
        (fun a b u => matDCFreCore rhoV sigmaV hsig b a u / rho) G sigma r i j
      = matShellConvAsym
          (fun a b u => shellKernel (shellForcing rhoV sigmaV hsig rho a b) sigma u)
          (fun a b u => shellKernel (shellForcing rhoV sigmaV hsig rho b a) sigma u)
          G sigma r i j := by
  unfold matShellConvAsym
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine intervalIntegral.integral_congr_ae ?_
  rw [Set.uIoc_of_le hσ.le]
  have hne : ∀ᵐ u : ℝ, u ≠ sigma := by rw [MeasureTheory.ae_iff]; simp
  filter_upwards [hne] with u hune hmem
  have huoo : u ∈ Set.Ioo (0 : ℝ) sigma := ⟨hmem.1, lt_of_le_of_ne hmem.2 hune⟩
  rw [hShellDCF_construct rhoV sigmaV hsig hρ i k (hbdry i k) (hFc i k) (hdiff i k) (hint i k)
      u huoo,
    hShellDCF_construct rhoV sigmaV hsig hρ k i (hbdry k i) (hFc k i) (hdiff k i) (hint k i) u huoo]

/-- **⭐ Shell-inverse form of the corrected seed (`matBaxterUQmSymFullExt` via `qWeighted`).**  The
seed's `hclaimA` — stated with the physical fold kernel `matDCFfoldKernel(qWeighted)/ρ` (which IS
`matBaxterUQmSymFullExt`'s fold, `matDCFfoldKernel_qWeighted_eq_matDCFreCore`) — is rewritten so its
DCF kernel is `shellKernel(shellForcing)`, the shell kernel of the shell-inverse forcing.  So the
renewal seed's forcing is exactly `shellForcing = −matDCFreCore'/(ρ·2π·s)`; under the (open)
Baxter–WH gap `hShellDCF` that forcing is `c_HS` (`forcing_eq_shellForcing_of_hShellDCF`). -/
theorem hclaimA_qWeighted_to_shellForcing (rhoV sigmaV : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigmaV k)
    (Psi Phi : Matrix (Fin 2) (Fin 2) (ℝ → ℝ)) {rho sigma r : ℝ} (hσ : 0 < sigma) (hρ : rho ≠ 0)
    (i j : Fin 2)
    (hbdry : ∀ a b : Fin 2, matDCFreCore rhoV sigmaV hsig a b sigma / rho = 0)
    (hFc : ∀ (a b : Fin 2), ∀ v ∈ Set.Ioo (0 : ℝ) sigma,
      ContinuousOn (fun w => matDCFreCore rhoV sigmaV hsig a b w / rho) (Set.Icc v sigma))
    (hdiff : ∀ (a b : Fin 2), ∀ s ∈ Set.Ioo (0 : ℝ) sigma,
      DifferentiableAt ℝ (fun w => matDCFreCore rhoV sigmaV hsig a b w) s)
    (hint : ∀ (a b : Fin 2), ∀ v ∈ Set.Ioo (0 : ℝ) sigma, IntervalIntegrable
      (fun s => -(2 * Real.pi * s * shellForcing rhoV sigmaV hsig rho a b s)) volume v sigma)
    (h : Psi i j r = r * Phi i j r
      + rho * matShellConvAsym
          (fun a b u => matDCFfoldKernel (qWeighted rhoV sigmaV hsig) a b u / rho)
          (fun a b u => matDCFfoldKernel (qWeighted rhoV sigmaV hsig) b a u / rho)
          (fun k l => fun x => Psi k l x / x) sigma r i j) :
    Psi i j r = r * Phi i j r
      + rho * matShellConvAsym
          (fun a b u => shellKernel (shellForcing rhoV sigmaV hsig rho a b) sigma u)
          (fun a b u => shellKernel (shellForcing rhoV sigmaV hsig rho b a) sigma u)
          (fun k l => fun x => Psi k l x / x) sigma r i j := by
  rw [hclaimA_qWeighted_to_matDCFreCore rhoV sigmaV hsig Psi Phi rho sigma r i j h,
    matShellConvAsym_matDCFreCore_eq_shellForcing rhoV sigmaV hsig hσ hρ
      (fun k l => fun x => Psi k l x / x) r i j hbdry hFc hdiff hint]

end PhysicalIdentification

end FMSA.MixtureOzStar
