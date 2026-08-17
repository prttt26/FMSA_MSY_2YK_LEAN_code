/-
Copyright (c) 2026 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import LeanCode.HSMixture.MixtureWienerHopfN1
import LeanCode.HardSphere.BaxterRenewal
import LeanCode.HardSphere.ShellKernel

/-!
# General-N: reducing the structure-factor identity `hSF` to a pure-`q` 1D Fourier identity

The value-route Gram input `hfack` was reduced (`MatrixGramWienerHopf`) to the single matrix
structure-factor identity `hSF`: `(Q̂₀·Q̂₀(−·)ᵀ)ᵢⱼ = δᵢⱼ − ρ·radial_fourier(Φᵢⱼ)`.  That identity
still mentions the physical DCF `Φ` and its shell kernel — objects whose real-space closed form is
the (open) mixture Wertheim theorem.  This file removes them from the frontier.

The scalar `baxter_wiener_hopf_factorization` was proved by brute-force closed forms because BOTH
the Baxter factor `q̃₀(k)` AND `radial_fourier(c_HS)` have them.  For general `N` the DCF `Φᵢⱼ`
has no closed form, so the RHS is not directly computable.  But two already-proved facts express
`ρ·radial_fourier(Φᵢⱼ)` through the Baxter factor `q` alone:

* the **shell-cosine bridge** `matShellKernel_cos_eq_radial_fourier`:
  `radial_fourier(Φᵢⱼ)(k) = 2∫₀^σ Kᵢⱼ(v)·cos(kv) dv`, `K = shellKernel(Φ)`; and
* the **real-space KDEF** `MatBaxterFactorization`: `ρKᵢⱼ(v) = qᵢⱼ(v) − (matSelfConv q)ᵢⱼ(v)` on
  `(0,σ)`.

`matBaxterFactor_cos_eq_rho_radial_fourier` collapses these to `ρ·radial_fourier(Φᵢⱼ) = 2∫₀^σ (qᵢⱼ −
(matSelfConv q)ᵢⱼ)·cos` — a real identity in the Baxter factor `q` only (which DOES have closed
forms, `q0MixEntry`).  Hence:

* `MatBaxterFourierWH` — the remaining **frontier**, stated purely in `q`: `(Q̂₀·Q̂₀(−·)ᵀ)ᵢⱼ = δᵢⱼ −
  2∫₀^σ (qᵢⱼ − (matSelfConv q)ᵢⱼ)·cos` — the matrix 1D Baxter Wiener–Hopf convolution identity, the
  matrix analog of `baxter_wiener_hopf_factorization`.  `Φ` and `shellKernel` no longer appear.
* `matSF_of_baxterFourierWH` — `hSF` from `MatBaxterFourierWH` + KDEF + bridge.
* `matWH_hfack_of_baxterFourierWH` — chaining with `matWH_hfack_of_structureFactor`: the value-route
  Gram input `hfack` from `MatBaxterFourierWH` (+ Hermitian reality + KDEF + bridge), general `N`.
* `matBaxterFourierWH_fin_one` — non-vacuity: at `N = 1` the frontier IS the proven scalar
  `baxter_wiener_hopf_factorization` (via `hSF_fin_one_of_baxterWH` + the KDEF/bridge collapse).

So the sole open input to the general-`N` value route is now `MatBaxterFourierWH`, a self-contained
1D Fourier identity in the Baxter factor `q` — the DCF and shell kernel are eliminated.

**Decomposition of `MatBaxterFourierWH` (see the section below).**  `MatBaxterFourierWH` is NOT an
identity for arbitrary `q` — with the concrete `1D` Fourier Baxter factor `matFourierFactor`, the
pure algebra `matFourierFactor_mul_conj_expand` shows the LHS is generally complex/asymmetric while
the target is real/symmetric.  `matBaxterFourierWH_of_wk_sym` proves it from two ingredients: the
matrix **Wiener–Khinchin identity** `hWK` (`∑ₗ q̃ᵢₗ·conj q̃ⱼₗ = ∫mSCᵢⱼe^{ikv} + ∫mSCⱼᵢe^{-ikv}`,
true for any compactly-supported `q` — the standard-Fourier-analysis crux) and the **physical
D-symmetry** (`∫Dᵢⱼ = ∫Dⱼᵢ`, `Dᵢⱼ = qᵢⱼ − mSCᵢⱼ`, from the physical DCF symmetry).  So the crux is
now cleanly
separated: `hWK` (Fourier analysis) vs. D-symmetry (physics); `matFourierFactor_fin_one` checks the
concrete factor is `Q0fourier_fin_one` at `N = 1`.  `hWK` (a Fubini/triangle fact) is the remaining
analytic atom.
-/

open MeasureTheory
namespace FMSA.MixtureOzStar
open FMSA.HardSphere
variable {N : ℕ}

/-- **Core 1D Baxter Fourier–Wiener–Hopf identity** (in terms of the real-space Baxter factor `q`
only).  `(Q̂₀·Q̂₀(−·)ᵀ)ᵢⱼ = δᵢⱼ − 2∫₀^σ (qᵢⱼ − (matSelfConv q)ᵢⱼ)·cos(kv) dv` — the matrix analog
of the scalar `baxter_wiener_hopf_factorization` content, with the DCF `Φ` and shell kernel
ELIMINATED (they enter only via the done shell-cosine bridge + KDEF). -/
def MatBaxterFourierWH (Q Qneg : Matrix (Fin N) (Fin N) ℂ)
    (q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma k : ℝ) : Prop :=
  ∀ i j, (Q * Qneg.transpose) i j
    = (if i = j then (1 : ℂ) else 0)
      - 2 * ((∫ v in (0:ℝ)..sigma, (q i j v - matSelfConv q sigma v i j)
          * Real.cos (k * v) : ℝ) : ℂ)

/-- **The KDEF + shell-cosine bridge collapse to a `q`-only real identity.**  From the matrix Baxter
factorization `ρKᵢⱼ = qᵢⱼ − (matSelfConv q)ᵢⱼ` on `(0,σ)` and the shell bridge
`2∫₀^σ Kᵢⱼ·cos = radial_fourier(Φᵢⱼ)`, the DCF's `ρ·radial_fourier` equals the cosine transform of
`qᵢⱼ − (matSelfConv q)ᵢⱼ`.  The KDEF holds only on the open core `(0,σ)`; the two endpoints are a
null set, handled by `integral_congr_ae`. -/
theorem matBaxterFactor_cos_eq_rho_radial_fourier
    (K q Phi : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (rho sigma k : ℝ) (hsigma : 0 < sigma)
    (hKDEF : MatBaxterFactorization K q rho sigma)
    (hbridge : ∀ i j,
      2 * ∫ v in (0:ℝ)..sigma, K i j v * Real.cos (k * v) = radial_fourier (Phi i j) k)
    (i j : Fin N) :
    2 * ∫ v in (0:ℝ)..sigma, (q i j v - matSelfConv q sigma v i j) * Real.cos (k * v)
      = rho * radial_fourier (Phi i j) k := by
  have hpull : ∫ v in (0:ℝ)..sigma, (q i j v - matSelfConv q sigma v i j) * Real.cos (k * v)
             = ∫ v in (0:ℝ)..sigma, (rho * K i j v) * Real.cos (k * v) := by
    apply intervalIntegral.integral_congr_ae
    have hsigmanull : ∀ᵐ v ∂(volume : Measure ℝ), v ≠ sigma := by
      rw [ae_iff]
      have hset : {a : ℝ | ¬ a ≠ sigma} = {sigma} := by ext a; simp
      rw [hset]; exact Real.volume_singleton
    filter_upwards [hsigmanull] with v hv hmem
    rw [Set.uIoc_of_le hsigma.le, Set.mem_Ioc] at hmem
    have hvIoo : v ∈ Set.Ioo (0:ℝ) sigma := ⟨hmem.1, lt_of_le_of_ne hmem.2 hv⟩
    rw [hKDEF i j v hvIoo]
  rw [hpull]
  have hconst : ∫ v in (0:ℝ)..sigma, (rho * K i j v) * Real.cos (k * v)
             = rho * ∫ v in (0:ℝ)..sigma, K i j v * Real.cos (k * v) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro v _; ring
  rw [hconst, ← hbridge i j]; ring

/-- **`hSF` from the core `q`-only Fourier identity.**  Given the matrix Baxter factorization (KDEF)
and the shell-cosine bridge, the structure-factor identity `hSF`
`(Q·Qnegᵀ)ᵢⱼ = δᵢⱼ − ρ·radial_fourier(Φᵢⱼ)` reduces to the pure-`q` `MatBaxterFourierWH`.  Removes
the DCF `Φ` and shell kernel from the value-route frontier. -/
theorem matSF_of_baxterFourierWH (Q Qneg : Matrix (Fin N) (Fin N) ℂ)
    (K q Phi : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (rho sigma k : ℝ) (hsigma : 0 < sigma)
    (hKDEF : MatBaxterFactorization K q rho sigma)
    (hbridge : ∀ i j,
      2 * ∫ v in (0:ℝ)..sigma, K i j v * Real.cos (k * v) = radial_fourier (Phi i j) k)
    (hcore : MatBaxterFourierWH Q Qneg q sigma k) (i j : Fin N) :
    (Q * Qneg.transpose) i j
      = (if i = j then (1 : ℂ) else 0) - (rho : ℂ) * (radial_fourier (Phi i j) k : ℂ) := by
  rw [hcore i j]
  congr 1
  have hR := matBaxterFactor_cos_eq_rho_radial_fourier K q Phi rho sigma k hsigma hKDEF hbridge i j
  exact_mod_cast hR

/-- **Capstone — the value-route Gram input from the pure-`q` core identity.**  Chaining
`matSF_of_baxterFourierWH` with `matWH_hfack_of_structureFactor`: given the Hermitian reality
`Qneg = conj Q`, the KDEF, the shell-cosine bridge, and the core `MatBaxterFourierWH`, the
`matSymbolCoercive_of_gramFactors` Gram input `hfack` holds for general `N`.  So the entire
general-`N` value route now rests on the single self-contained 1D Fourier identity
`MatBaxterFourierWH`. -/
theorem matWH_hfack_of_baxterFourierWH (Q Qneg : Matrix (Fin N) (Fin N) ℂ)
    (K q Phi : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (rho sigma k : ℝ) (hsigma : 0 < sigma)
    (hherm : Qneg = Q.map (starRingEnd ℂ))
    (hKDEF : MatBaxterFactorization K q rho sigma)
    (hbridge : ∀ i j,
      2 * ∫ v in (0:ℝ)..sigma, K i j v * Real.cos (k * v) = radial_fourier (Phi i j) k)
    (hcore : MatBaxterFourierWH Q Qneg q sigma k) (v : Fin N → ℝ) :
    (∑ i, v i ^ 2) - rho * ∑ i, ∑ j, radial_fourier (Phi i j) k * v i * v j
      = ∑ l, Complex.normSq (Q.transpose.mulVec (fun i => (v i : ℂ)) l) :=
  matWH_hfack_of_structureFactor Q Qneg rho (fun i j => radial_fourier (Phi i j) k) hherm
    (fun i j =>
      matSF_of_baxterFourierWH Q Qneg K q Phi rho sigma k hsigma hKDEF hbridge hcore i j) v

/-- **N=1 non-vacuity — the core `q`-only identity IS the scalar Baxter WH factorization.**  At one
component `MatBaxterFourierWH` holds for the `1×1` Fourier Baxter factor `Q0fourier_fin_one`, its
Hermitian companion, and `q = q0_poly`, proved from `hSF_fin_one_of_baxterWH` + the KDEF/bridge
collapse.  Confirms the general-`N` frontier `MatBaxterFourierWH` is satisfiable and specializes to
the proven scalar theorem. -/
theorem matBaxterFourierWH_fin_one (eta sigma rho : ℝ) (hsigma : 0 < sigma) (heta : eta < 1)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) {k : ℝ} (hk : k ≠ 0) :
    MatBaxterFourierWH (Q0fourier_fin_one eta sigma rho k)
      ((Q0fourier_fin_one eta sigma rho k).map (starRingEnd ℂ))
      (fun _ _ => q0_poly eta sigma rho) sigma k := by
  intro i j
  have hSF := hSF_fin_one_of_baxterWH eta sigma rho hsigma heta heta_def hk i j
  rw [hSF]
  congr 1
  have hR := matBaxterFactor_cos_eq_rho_radial_fourier
    (fun _ _ => baxterK eta sigma) (fun _ _ => q0_poly eta sigma rho)
    (fun _ _ => c_HS eta sigma) rho sigma k hsigma
    (matBaxterFactorization_fin_one_of_scalar hsigma heta heta_def)
    (fun _ _ => baxterK_cos_eq_radial_fourier hsigma hk) i j
  exact_mod_cast hR.symm


/-! ### Decomposing the general-`N` frontier `MatBaxterFourierWH`

`MatBaxterFourierWH` is NOT an identity for arbitrary `q`.  With the concrete `1D` Fourier Baxter
factor `Q̂₀ᵢⱼ = δᵢⱼ − q̃ᵢⱼ` (`q̃ᵢⱼ = ∫₀^σ qᵢⱼ e^{ikv}`, real/imag parts `qCos`/`qSin`), the pure
algebra `matFourierFactor_mul_conj_expand` gives
`(Q̂₀·Q̂₀(−·)ᵀ)ᵢⱼ = δᵢⱼ − q̃ᵢⱼ − conj(q̃ⱼᵢ) + ∑ₗ q̃ᵢₗ·conj(q̃ⱼₗ)`, which is generally complex and
asymmetric — while the target `δᵢⱼ − 2∫₀^σ(qᵢⱼ − (matSelfConv q)ᵢⱼ)·cos` is real and symmetric.  So
`MatBaxterFourierWH` for the concrete factor decomposes into exactly two ingredients:

* the **matrix Wiener–Khinchin identity** `hWK`
  `∑ₗ q̃ᵢₗ·conj(q̃ⱼₗ) = (∫mSCᵢⱼcos + ∫mSCⱼᵢcos) + i(∫mSCᵢⱼsin − ∫mSCⱼᵢsin)` — true for ANY
  compactly-supported `q` (`f̃·conj g̃ = ∫Corr(f,g)e^{ikv} + ∫Corr(g,f)e^{-ikv}`, a Fubini/triangle
  fact); the standard-Fourier-analysis crux; and
* the **physical D-symmetry** `∫Dᵢⱼcos = ∫Dⱼᵢcos`, `∫Dᵢⱼsin = ∫Dⱼᵢsin` where `Dᵢⱼ = qᵢⱼ − mSCᵢⱼ`
  (holds because the physical DCF is symmetric — the KDEF forces `Dᵢⱼ = ρ·shellKernel(Φᵢⱼ)`,
  symmetric via `Cmix0` symmetry / `matBaxterK_symm_of_dcf`).

`matBaxterFourierWH_of_wk_sym` assembles `MatBaxterFourierWH` from these (+ the cosine linearity
split `hsplitc`).  So the crux is now cleanly separated: `hWK` (Fourier analysis) vs. D-symmetry
(physics). -/

/-- Real part of the `1D` FT of the Baxter factor: `Cᵢⱼ = ∫₀^σ qᵢⱼ·cos(kv)`. -/
noncomputable def qCos (q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma k : ℝ) (i j : Fin N) : ℝ :=
  ∫ v in (0:ℝ)..sigma, q i j v * Real.cos (k * v)
/-- (Negated) imaginary part of the `1D` FT of the Baxter factor: `Sᵢⱼ = ∫₀^σ qᵢⱼ·sin(kv)`. -/
noncomputable def qSin (q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma k : ℝ) (i j : Fin N) : ℝ :=
  ∫ v in (0:ℝ)..sigma, q i j v * Real.sin (k * v)
/-- The `1D` Fourier transform of the Baxter factor: `q̃ᵢⱼ(k) = Cᵢⱼ + i·Sᵢⱼ`. -/
noncomputable def qtil (q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma k : ℝ) (i j : Fin N) : ℂ :=
  (qCos q sigma k i j : ℂ) + (qSin q sigma k i j : ℂ) * Complex.I
/-- Cosine transform of the self-convolution: `∫₀^σ (matSelfConv q)ᵢⱼ·cos(kv)`. -/
noncomputable def mscCos (q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma k : ℝ) (i j : Fin N) : ℝ :=
  ∫ v in (0:ℝ)..sigma, matSelfConv q sigma v i j * Real.cos (k * v)
/-- Sine transform of the self-convolution: `∫₀^σ (matSelfConv q)ᵢⱼ·sin(kv)`. -/
noncomputable def mscSin (q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma k : ℝ) (i j : Fin N) : ℝ :=
  ∫ v in (0:ℝ)..sigma, matSelfConv q sigma v i j * Real.sin (k * v)

/-- **The `1D` Fourier Baxter factor** built from `q`: `Q̂₀ᵢⱼ = δᵢⱼ − q̃ᵢⱼ(k)`.  At `N = 1` with
`q = q0_poly` it equals `Q0fourier_fin_one` (`matFourierFactor_fin_one`). -/
noncomputable def matFourierFactor (q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma k : ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j => (if i = j then (1:ℂ) else 0) - qtil q sigma k i j

/-- **Pure algebra: the structure-factor product in terms of the FT `q̃`.**
`(Q̂₀·Q̂₀(−·)ᵀ)ᵢⱼ = δᵢⱼ − q̃ᵢⱼ − conj(q̃ⱼᵢ) + ∑ₗ q̃ᵢₗ·conj(q̃ⱼₗ)`, with `Q̂₀(−·) = conj Q̂₀`. -/
theorem matFourierFactor_mul_conj_expand (q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma k : ℝ)
    (i j : Fin N) :
    (matFourierFactor q sigma k * ((matFourierFactor q sigma k).map (starRingEnd ℂ)).transpose) i j
      = (if i = j then (1:ℂ) else 0) - qtil q sigma k i j - (starRingEnd ℂ) (qtil q sigma k j i)
        + ∑ l, qtil q sigma k i l * (starRingEnd ℂ) (qtil q sigma k j l) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, matFourierFactor]
  have hterm : ∀ l, ((if i = l then (1:ℂ) else 0) - qtil q sigma k i l)
        * (starRingEnd ℂ) ((if j = l then (1:ℂ) else 0) - qtil q sigma k j l)
      = (if i = l then (1:ℂ) else 0) * (if j = l then (1:ℂ) else 0)
        - (if i = l then (1:ℂ) else 0) * (starRingEnd ℂ) (qtil q sigma k j l)
        - qtil q sigma k i l * (if j = l then (1:ℂ) else 0)
        + qtil q sigma k i l * (starRingEnd ℂ) (qtil q sigma k j l) := by
    intro l
    rw [map_sub]
    have hc : (starRingEnd ℂ) (if j = l then (1:ℂ) else 0) = (if j = l then (1:ℂ) else 0) := by
      rw [apply_ite (starRingEnd ℂ)]; simp
    rw [hc]; ring
  simp only [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hs1 : (∑ l, (if i = l then (1:ℂ) else 0) * (if j = l then (1:ℂ) else 0))
      = (if i = j then (1:ℂ) else 0) := by
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq Finset.univ i (fun l => if j = l then (1:ℂ) else 0)]
    simp only [Finset.mem_univ, if_true]
    by_cases h : i = j
    · subst h; simp
    · have h' : j ≠ i := fun hh => h hh.symm
      simp [h, h']
  have hs2 : (∑ l, (if i = l then (1:ℂ) else 0) * (starRingEnd ℂ) (qtil q sigma k j l))
      = (starRingEnd ℂ) (qtil q sigma k j i) := by
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq Finset.univ i (fun l => (starRingEnd ℂ) (qtil q sigma k j l))]
    simp
  have hs3 : (∑ l, qtil q sigma k i l * (if j = l then (1:ℂ) else 0))
      = qtil q sigma k i j := by
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq Finset.univ j (fun l => qtil q sigma k i l)]
    simp
  rw [hs1, hs2, hs3]; ring

/-- **`MatBaxterFourierWH` from the Wiener–Khinchin identity `hWK` + physical D-symmetry.**  For the
concrete `1D` Fourier Baxter factor, `MatBaxterFourierWH` follows from: `hWK` (the matrix
Wiener–Khinchin identity, the standard-Fourier-analysis crux), the cosine linearity split `hsplitc`,
and the D-symmetries `hDc`/`hDs` (`∫Dᵢⱼ·cos/sin = ∫Dⱼᵢ·cos/sin`, `Dᵢⱼ = qᵢⱼ − mSCᵢⱼ`, physical DCF
symmetry).  The proof: expand (`matFourierFactor_mul_conj_expand`), substitute `hWK`, then match
real part (`hDc`) and imaginary part (`= 0`, `hDs`). -/
theorem matBaxterFourierWH_of_wk_sym (q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma k : ℝ)
    (hWK : ∀ i j, ∑ l, qtil q sigma k i l * (starRingEnd ℂ) (qtil q sigma k j l)
       = ((mscCos q sigma k i j + mscCos q sigma k j i : ℝ) : ℂ)
         + ((mscSin q sigma k i j - mscSin q sigma k j i : ℝ) : ℂ) * Complex.I)
    (hsplitc : ∀ i j,
        (∫ v in (0:ℝ)..sigma, (q i j v - matSelfConv q sigma v i j) * Real.cos (k * v))
       = qCos q sigma k i j - mscCos q sigma k i j)
    (hDc : ∀ i j, qCos q sigma k i j - mscCos q sigma k i j
       = qCos q sigma k j i - mscCos q sigma k j i)
    (hDs : ∀ i j, qSin q sigma k i j - mscSin q sigma k i j
       = qSin q sigma k j i - mscSin q sigma k j i) :
    MatBaxterFourierWH (matFourierFactor q sigma k)
      ((matFourierFactor q sigma k).map (starRingEnd ℂ)) q sigma k := by
  intro i j
  rw [matFourierFactor_mul_conj_expand q sigma k i j, hWK i j, hsplitc i j]
  simp only [qtil, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  have hc := hDc i j
  have hs := hDs i j
  apply Complex.ext
  · simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, apply_ite Complex.re,
      Complex.one_re, Complex.zero_re, Complex.re_ofNat, Complex.im_ofNat]
    ring_nf; ring_nf at hc; linarith [hc]
  · simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, apply_ite Complex.im,
      Complex.one_im, Complex.zero_im, Complex.re_ofNat, Complex.im_ofNat]
    ring_nf; ring_nf at hs; linarith [hs]

/-- **Consistency at `N = 1`.**  The concrete `1D` Fourier Baxter factor for `q = q0_poly` is
exactly the `Q0fourier_fin_one` of the proven `N = 1` case. -/
theorem matFourierFactor_fin_one (eta sigma rho k : ℝ) :
    matFourierFactor (fun _ _ => q0_poly eta sigma rho) sigma k
      = Q0fourier_fin_one eta sigma rho k := by
  ext i j
  fin_cases i; fin_cases j
  simp only [matFourierFactor, qtil, qCos, qSin, Q0fourier_fin_one, Matrix.cons_val_fin_one,
    Matrix.of_apply, if_true]
  push_cast; ring


end FMSA.MixtureOzStar
