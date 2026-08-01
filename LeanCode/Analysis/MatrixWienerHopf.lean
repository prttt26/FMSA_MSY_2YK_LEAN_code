/-
Copyright (c) 2026 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/
import Mathlib
import LeanCode.Analysis.WienerHopf

/-!
# Matrix Krein / Wiener–Hopf half-line injectivity, positive symbol — PROVED via matrix Plancherel

The **multicomponent** analog of `wienerHopf_positive_symbol_injective` (`MA.12`,
`Analysis/WienerHopf.lean`), proved the same way — **coercivity via Plancherel** — but for a matrix
(vector-valued) symbol, so it is a THEOREM, not an axiom.

For `u ∈ (L²)^N` supported on `[0,∞)` and a bounded measurable matrix symbol `A(x)` that is coercive
on `ℝ^N` (`vᵀA(x)v ≥ ε‖v‖²`), the Fourier multiplier `T_A u = 𝓕⁻¹(A·𝓕u)` satisfies
`∑ᵢ Re⟪(T_A u)ᵢ, uᵢ⟫ = ∑ᵢⱼ ∫ Aᵢⱼ Re(𝓕uⱼ · conj 𝓕uᵢ) ≥ ε ∑ᵢ‖𝓕uᵢ‖² = ε‖u‖²` (componentwise
Plancherel).  If `T_A u` also vanishes on `[0,∞)`, the pairing is `0`, forcing `u = 0`.

The one new ingredient over the scalar proof is `matrix_quadratic_coercive`: a real quadratic form
coercive on `ℝ^N` is coercive on `ℂ^N` (split `w = Re w + i·Im w`; `Re⟨Aw,w⟩ = (Re w)ᵀA(Re w) +
(Im w)ᵀA(Im w) ≥ ε(‖Re w‖² + ‖Im w‖²) = ε‖w‖²`).  Everything else reuses the scalar `mulLp`, `𝓕`,
`Lp.inner_fourier_eq`, `Lp.norm_fourier_eq`.

**All results axiom-clean** (`propext`, `Classical.choice`, `Quot.sound`).

## Relation to the `L∞` axiom

This is the `L²` half of the `L²`/`L∞` pair, exactly as in the scalar case: the `L∞`/bounded matrix
Wiener–Hopf injectivity (`FMSA.matRadialShell_bounded_injective`, `Analysis/MatrixRadialWienerHopf.lean`,
the consumer of `MML.8`'s `matOzStar_unique`) stays an axiom — bounded functions are not `L²`, and the
Plancherel pairing does not apply; it needs Wiener-algebra resolvent inversion (`MA.13`-class gap).
This file discharges the `L²` specialization, mirroring `MA.12`.
-/

open MeasureTheory Complex RCLike FourierTransform
open scoped ComplexInnerProductSpace

namespace FMSA

noncomputable section


/-- **Real → complex coercivity.**  A real quadratic form coercive on `ℝ^N` is coercive on `ℂ^N`
(split into real and imaginary parts): `ε‖w‖² ≤ ∑ᵢⱼ Aᵢⱼ(Re wᵢ Re wⱼ + Im wᵢ Im wⱼ)`. -/
lemma matrix_quadratic_coercive {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} {ε : ℝ}
    (hA : ∀ v : Fin N → ℝ, ε * (∑ i, v i ^ 2) ≤ ∑ i, ∑ j, A i j * v i * v j)
    (w : Fin N → ℂ) :
    ε * (∑ i, ‖w i‖ ^ 2)
      ≤ ∑ i, ∑ j, A i j * ((w i).re * (w j).re + (w i).im * (w j).im) := by
  have hre := hA (fun i => (w i).re)
  have him := hA (fun i => (w i).im)
  have hnorm : (∑ i, ‖w i‖ ^ 2) = (∑ i, (w i).re ^ 2) + (∑ i, (w i).im ^ 2) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring)
  calc ε * (∑ i, ‖w i‖ ^ 2)
      = ε * (∑ i, (w i).re ^ 2) + ε * (∑ i, (w i).im ^ 2) := by rw [hnorm]; ring
    _ ≤ (∑ i, ∑ j, A i j * (w i).re * (w j).re)
        + (∑ i, ∑ j, A i j * (w i).im * (w j).im) := add_le_add hre him
    _ = ∑ i, ∑ j, A i j * ((w i).re * (w j).re + (w i).im * (w j).im) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun j _ => by ring)

lemma mulLp_inner_re {a : ℝ → ℝ} (ha : Measurable a) (M : ℝ) (haM : ∀ x, |a x| ≤ M)
    (wj wi : Lp ℂ 2 (volume : Measure ℝ)) :
    (inner ℂ (mulLp a ha M haM wj) wi).re
      = ∫ x, a x * (((wj : ℝ → ℂ) x).re * ((wi : ℝ → ℂ) x).re
          + ((wj : ℝ → ℂ) x).im * ((wi : ℝ → ℂ) x).im) := by
  have hrep : (mulLp a ha M haM wj : ℝ → ℂ) =ᵐ[volume] fun x => (a x : ℂ) * wj x :=
    MemLp.coeFn_toLp _
  change RCLike.re (inner ℂ (mulLp a ha M haM wj) wi) = _
  rw [MeasureTheory.L2.inner_def,
    ← integral_re (MeasureTheory.L2.integrable_inner (mulLp a ha M haM wj) wi)]
  apply integral_congr_ae
  filter_upwards [hrep] with x hx
  rw [hx, RCLike.inner_apply', RCLike.re_to_complex]
  simp only [map_mul, Complex.conj_ofReal, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
  ring

/-- The `mulLp` cross-integrand is integrable (`L²·L² ∈ L¹`, times bounded symbol). -/
lemma mulLp_integrand_integrable {a : ℝ → ℝ} (ha : Measurable a) (M : ℝ) (haM : ∀ x, |a x| ≤ M)
    (wj wi : Lp ℂ 2 (volume : Measure ℝ)) :
    Integrable (fun x => a x * (((wj : ℝ → ℂ) x).re * ((wi : ℝ → ℂ) x).re
        + ((wj : ℝ → ℂ) x).im * ((wi : ℝ → ℂ) x).im)) volume := by
  have hII := (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) (mulLp a ha M haM wj) wi).re
  have hrep : (mulLp a ha M haM wj : ℝ → ℂ) =ᵐ[volume] fun x => (a x : ℂ) * wj x :=
    MemLp.coeFn_toLp _
  refine hII.congr ?_
  filter_upwards [hrep] with x hx
  rw [hx, RCLike.inner_apply']
  simp only [map_mul, Complex.conj_ofReal, RCLike.re_to_complex, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
  ring

/-- **Matrix multiplier coercivity (integral half).**  For a bounded measurable matrix symbol `A`
coercive on `ℝ^N`, `ε ∑ᵢ‖wᵢ‖² ≤ ∑ᵢⱼ Re⟪Aᵢⱼ·wⱼ, wᵢ⟫`.  Matrix analog of `mulLp_coercive`. -/
lemma matMulLp_coercive {N : ℕ} {A : ℝ → Matrix (Fin N) (Fin N) ℝ}
    (hA : ∀ i j, Measurable (fun x => A x i j)) (M : ℝ) (hM : ∀ i j x, |A x i j| ≤ M)
    (ε : ℝ) (hcoer : ∀ x, ∀ v : Fin N → ℝ, ε * (∑ i, v i ^ 2) ≤ ∑ i, ∑ j, A x i j * v i * v j)
    (w : Fin N → Lp ℂ 2 (volume : Measure ℝ)) :
    ε * (∑ i, ‖w i‖ ^ 2)
      ≤ ∑ i, ∑ j, (inner ℂ (mulLp (fun x => A x i j) (hA i j) M (fun x => hM i j x) (w j)) (w i)).re := by
  set g : Fin N → Fin N → ℝ → ℝ := fun i j x =>
    A x i j * (((w j : ℝ → ℂ) x).re * ((w i : ℝ → ℂ) x).re
      + ((w j : ℝ → ℂ) x).im * ((w i : ℝ → ℂ) x).im) with hg
  have hgint : ∀ i j, Integrable (g i j) volume := fun i j =>
    mulLp_integrand_integrable (hA i j) M (fun x => hM i j x) (w j) (w i)
  have hrhs : (∑ i, ∑ j, (inner ℂ (mulLp (fun x => A x i j) (hA i j) M (fun x => hM i j x) (w j)) (w i)).re)
      = ∫ x, ∑ i, ∑ j, g i j x := by
    rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hgint i j))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [integral_finset_sum _ (fun j _ => hgint i j)]
    exact Finset.sum_congr rfl (fun j _ => mulLp_inner_re (hA i j) M (fun x => hM i j x) (w j) (w i))
  rw [hrhs]
  have hlhs : ε * (∑ i, ‖w i‖ ^ 2) = ∫ x, ε * ∑ i, ‖(w i : ℝ → ℂ) x‖ ^ 2 := by
    rw [integral_const_mul]
    congr 1
    rw [integral_finset_sum _ (fun i _ => integrable_norm_sq (w i))]
    exact Finset.sum_congr rfl (fun i _ => (integral_norm_sq_eq (w i)).symm)
  rw [hlhs]
  refine integral_mono (by
      exact (integrable_finset_sum _ (fun i _ => integrable_norm_sq (w i))).const_mul ε)
    (integrable_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hgint i j)))
    (fun x => ?_)
  simp only [hg]
  exact (matrix_quadratic_coercive (A := A x) (ε := ε) (hcoer x) (fun i => (w i : ℝ → ℂ) x)).trans_eq
    (Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring)))

/-- The **matrix Fourier multiplier** `(T_A u)ᵢ = 𝓕⁻¹(∑ⱼ Aᵢⱼ·𝓕uⱼ)` (componentwise `L²`). -/
def matFourierMul {N : ℕ} (A : ℝ → Matrix (Fin N) (Fin N) ℝ)
    (hA : ∀ i j, Measurable (fun x => A x i j)) (M : ℝ) (hM : ∀ i j x, |A x i j| ≤ M)
    (u : Fin N → Lp ℂ 2 (volume : Measure ℝ)) (i : Fin N) : Lp ℂ 2 (volume : Measure ℝ) :=
  𝓕⁻ (∑ j, mulLp (fun x => A x i j) (hA i j) M (fun x => hM i j x) (𝓕 (u j)))

/-- **Matrix Fourier-multiplier coercivity** (matrix Plancherel): `ε ∑ᵢ‖uᵢ‖² ≤ ∑ᵢ Re⟪(T_A u)ᵢ, uᵢ⟫`. -/
lemma matFourierMul_coercive {N : ℕ} {A : ℝ → Matrix (Fin N) (Fin N) ℝ}
    (hA : ∀ i j, Measurable (fun x => A x i j)) (M : ℝ) (hM : ∀ i j x, |A x i j| ≤ M)
    (ε : ℝ) (hcoer : ∀ x, ∀ v : Fin N → ℝ, ε * (∑ i, v i ^ 2) ≤ ∑ i, ∑ j, A x i j * v i * v j)
    (u : Fin N → Lp ℂ 2 (volume : Measure ℝ)) :
    ε * (∑ i, ‖u i‖ ^ 2) ≤ ∑ i, (inner ℂ (matFourierMul A hA M hM u i) (u i)).re := by
  have hstep : ∀ i, (inner ℂ (matFourierMul A hA M hM u i) (u i))
      = ∑ j, inner ℂ (mulLp (fun x => A x i j) (hA i j) M (fun x => hM i j x) (𝓕 (u j))) (𝓕 (u i)) := by
    intro i
    rw [matFourierMul, ← Lp.inner_fourier_eq
      (𝓕⁻ (∑ j, mulLp (fun x => A x i j) (hA i j) M (fun x => hM i j x) (𝓕 (u j)))) (u i),
      fourier_fourierInv_eq, sum_inner]
  calc ε * (∑ i, ‖u i‖ ^ 2)
      = ε * (∑ i, ‖𝓕 (u i)‖ ^ 2) := by
        refine congrArg (ε * ·) (Finset.sum_congr rfl (fun i _ => ?_))
        rw [Lp.norm_fourier_eq]
    _ ≤ ∑ i, ∑ j, (inner ℂ (mulLp (fun x => A x i j) (hA i j) M (fun x => hM i j x)
          (𝓕 (u j))) (𝓕 (u i))).re :=
        matMulLp_coercive hA M hM ε hcoer (fun i => 𝓕 (u i))
    _ = ∑ i, (inner ℂ (matFourierMul A hA M hM u i) (u i)).re := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [hstep i, Complex.re_sum]

/-- **Matrix Krein / Wiener–Hopf half-line injectivity, positive symbol — PROVED via matrix
Plancherel.**  The multicomponent analog of `wienerHopf_positive_symbol_injective`: for a bounded
measurable matrix symbol `A` coercive on `ℝ^N` (`vᵀA(x)v ≥ ε‖v‖²`), the matrix half-line Wiener–Hopf
operator `T_A` is injective — any `u` supported on `[0,∞)` with `T_A u` vanishing on `[0,∞)` is `0`. -/
theorem matWienerHopf_positive_symbol_injective {N : ℕ} {A : ℝ → Matrix (Fin N) (Fin N) ℝ}
    (hA : ∀ i j, Measurable (fun x => A x i j)) (M : ℝ) (hM : ∀ i j x, |A x i j| ≤ M)
    (ε : ℝ) (hε : 0 < ε)
    (hcoer : ∀ x, ∀ v : Fin N → ℝ, ε * (∑ i, v i ^ 2) ≤ ∑ i, ∑ j, A x i j * v i * v j)
    (u : Fin N → Lp ℂ 2 (volume : Measure ℝ))
    (hu : ∀ i, ∀ᵐ x ∂(volume : Measure ℝ), x ≤ 0 → (u i : ℝ → ℂ) x = 0)
    (hTu : ∀ i, ∀ᵐ x ∂(volume : Measure ℝ), 0 ≤ x → (matFourierMul A hA M hM u i : ℝ → ℂ) x = 0) :
    ∀ i, u i = 0 := by
  have hzero : ∀ i, (inner ℂ (matFourierMul A hA M hM u i) (u i)) = 0 := by
    intro i
    rw [MeasureTheory.L2.inner_def,
      show (0 : ℂ) = ∫ _ : ℝ, (0 : ℂ) from (integral_zero _ _).symm]
    apply integral_congr_ae
    filter_upwards [hu i, hTu i] with x hx hTx
    rcases le_total x 0 with h | h
    · rw [hx h, inner_zero_right]
    · rw [hTx h, inner_zero_left]
  have hcoerc := matFourierMul_coercive hA M hM ε hcoer u
  have hsum0 : (∑ i, (inner ℂ (matFourierMul A hA M hM u i) (u i)).re) = 0 := by
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [hzero i, Complex.zero_re]
  rw [hsum0] at hcoerc
  have hnn : ∀ i, (0:ℝ) ≤ ‖u i‖ ^ 2 := fun i => sq_nonneg _
  have hall : ∀ i ∈ Finset.univ, ‖u i‖ ^ 2 = 0 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨i, _, hi⟩ := hcon
    have hpos : 0 < ∑ i, ‖u i‖ ^ 2 :=
      Finset.sum_pos' (fun i _ => hnn i) ⟨i, Finset.mem_univ i, lt_of_le_of_ne (hnn i) (Ne.symm hi)⟩
    nlinarith [hcoerc, hpos, hε]
  intro i
  have := hall i (Finset.mem_univ i)
  rw [sq_eq_zero_iff, norm_eq_zero] at this
  exact this

end
end FMSA
