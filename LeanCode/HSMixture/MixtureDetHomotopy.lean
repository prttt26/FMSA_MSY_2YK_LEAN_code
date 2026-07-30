/-
Copyright (c) 2026. All rights reserved.
-/
import LeanCode.HSMixture.MixtureDetEscape
import LeanCode.Analysis.ZeroCountHomotopy

/-!
# Density homotopy scaffold for `det Q̂₀` pole-freeness (`OZFIX.17` matrix)

Assembling the ingredients for the `η`-homotopy that proves `det Q̂₀ ≠ 0` in the open lower half
`k`-plane, via the *scalar* `zeroFree_lowerHalfPlane_of_homotopy` applied to the **entire** monomial
form `W(s) = s⁶·detF(s)` (`detC_monomial_eq`) — `detF` itself is meromorphic (pole at `s=0`), but `W`
is entire, and `W(s) = 0 ⇔ detF(s) = 0` for `s ≠ 0`.

Convention: `s = I·z` with `z` the frequency (`k`), so `Re s = −Im z` — the open lower half
`z`-plane (`Im z < 0`) is the right half `s`-plane (`Re s > 0`), the pole-free region.

Ingredients built here (all axiom-clean):
* `Pscale` — the coupling homotopy `rr ↦ t·rr`; `Pscale 1 P = P`, `Pscale 0 P` = zero coupling;
  `Pscale_Phys` (positivity preserved for `t > 0`).
* `Wfun_Pscale_zero` — dilute base `W(P₀, s) = s⁶`; `Wfun_dilute_ne_zero` = **`hbase`**
  (`W(P₀, I·z) = −z⁶ ≠ 0` for `Im z < 0`).
* `Wfun_ne_zero_of_norm_ge` — **`hbound`** in `z`-form, from `exists_escape_radius` through `s = I·z`.
* `Wfun_comp_I_differentiable` — **`hholo`** (`W(P, I·z)` entire).
* `Wfun_Pscale_comp_I_continuous` — **`hcont`** (jointly continuous in `(t, z)`).

Remaining for the full assembly: **`hreal`** (`W(Pscale t P, I·z) ≠ 0` for real `z`, from
`pyhs_mixture_no_spinodal` along the density path + the `z=0` value), a uniform-in-`t` escape radius
(the `K`-constants are continuous, hence bounded on `[0,1]`), then the `zeroFree_lowerHalfPlane_of_homotopy`
call.
-/

open Complex
namespace FMSA.MixtureHSPoles
noncomputable section

/-- **Density homotopy on the coupling matrix.**  Scale the geometric density weights `rr` by `t`
(keeping diameters and contact data fixed).  `Pscale 1 P = P`; `Pscale 0 P` has zero coupling, i.e.
the ideal-gas / dilute base where `Q̂₀ = I`. -/
def Pscale (t : ℝ) (P : MixParams) : MixParams :=
  { P with rr := fun i j => t * P.rr i j }

@[simp] theorem Pscale_rr (t : ℝ) (P : MixParams) (i j : Fin 2) :
    (Pscale t P).rr i j = t * P.rr i j := rfl
@[simp] theorem Pscale_sig0 (t : ℝ) (P : MixParams) : (Pscale t P).sig0 = P.sig0 := rfl
@[simp] theorem Pscale_sig1 (t : ℝ) (P : MixParams) : (Pscale t P).sig1 = P.sig1 := rfl
@[simp] theorem Pscale_Qp (t : ℝ) (P : MixParams) (i j : Fin 2) :
    (Pscale t P).Qp i j = P.Qp i j := rfl
@[simp] theorem Pscale_Qpp (t : ℝ) (P : MixParams) (i j : Fin 2) :
    (Pscale t P).Qpp i j = P.Qpp i j := rfl

/-- `Pscale 1 = id` (up to the structure). -/
@[simp] theorem Pscale_one (P : MixParams) : Pscale 1 P = P := by
  cases P; simp only [Pscale]; congr 1; funext i j; ring

/-- Physicality is preserved for a positive scale factor (coupling stays positive). -/
theorem Pscale_Phys {t : ℝ} (ht : 0 < t) {P : MixParams} (hP : P.Phys) : (Pscale t P).Phys := by
  obtain ⟨hs0, hs01, hrr, hqp, hqpp⟩ := hP
  exact ⟨by simpa using hs0, by simpa using hs01,
    fun i j => by simpa using mul_pos ht (hrr i j),
    fun i j => by simpa using hqp i j, fun i j => by simpa using hqpp i j⟩

/-- **Dilute base — `W = s⁶`.**  With zero coupling every off-diagonal monomial coefficient vanishes
and `Mc → s⁶`, so the entire monomial form of the determinant is exactly `s⁶`; its only zero is
`s = 0`.  This is the zero-free base point of the density homotopy. -/
theorem Wfun_Pscale_zero (P : MixParams) (s : ℂ) : Wfun (Pscale 0 P) s = s ^ 6 := by
  simp only [Wfun, McNum, M0Num, M1Num, M01Num, dNum, Pscale_rr, Pscale_sig0, Pscale_sig1,
    Pscale_Qp, Pscale_Qpp, zero_mul, Complex.ofReal_zero]
  ring

/-- `I^6 = −1`. -/
theorem I_pow_six : Complex.I ^ 6 = -1 := by
  rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, Complex.I_sq]; ring

/-- **Homotopy base point (`hbase`).**  At zero coupling `W(P₀, I·z) = (I·z)⁶ = −z⁶`, whose only zero
is `z = 0`; so it is nonzero throughout the open lower half `z`-plane. -/
theorem Wfun_dilute_ne_zero (P : MixParams) {z : ℂ} (hz : z.im < 0) :
    Wfun (Pscale 0 P) (Complex.I * z) ≠ 0 := by
  rw [Wfun_Pscale_zero, mul_pow, I_pow_six]
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  simpa using neg_ne_zero.mpr (pow_ne_zero 6 hz0)

/-- **Escape in the `z`-plane (`hbound` core, `z`-form).**  Converting `exists_escape_radius` through
`s = I·z` (`Re s = −Im z`, `‖I·z‖ = ‖z‖`): the entire form `W(P, I·z)` is nonzero for `Im z ≤ 0`,
`‖z‖ ≥ R`, provided `‖z‖ ≥ 1` (so `I·z ≠ 0`). -/
theorem Wfun_ne_zero_of_norm_ge (P : MixParams) {R : ℝ}
    (hR : ∀ s : ℂ, 0 ≤ s.re → R ≤ ‖s‖ → P.detF s ≠ 0)
    {z : ℂ} (hz : z.im ≤ 0) (hzR : R ≤ ‖z‖) (hz1 : 1 ≤ ‖z‖) :
    Wfun P (Complex.I * z) ≠ 0 := by
  have hnormIz : ‖Complex.I * z‖ = ‖z‖ := by rw [norm_mul, Complex.norm_I, one_mul]
  have hIz : Complex.I * z ≠ 0 := by
    intro h; rw [h, norm_zero] at hnormIz; linarith
  have hre : (0 : ℝ) ≤ (Complex.I * z).re := by
    rw [Complex.mul_re, Complex.I_re, Complex.I_im]; simp; linarith
  have hdet : P.detF (Complex.I * z) ≠ 0 := hR _ hre (by rw [hnormIz]; exact hzR)
  intro hW
  rw [← detC_monomial_eq P hIz] at hW
  exact hdet ((mul_eq_zero.mp hW).resolve_left (pow_ne_zero 6 hIz))

/-- **`hholo` — `W(P, I·z)` is entire in `z`.**  `Wfun` is a polynomial-exponential (`Wfun_hasDerivAt`),
so it is entire; composing with the entire `z ↦ I·z` keeps it entire. -/
theorem Wfun_comp_I_differentiable (P : MixParams) :
    Differentiable ℂ (fun z => Wfun P (Complex.I * z)) := by
  have h1 : Differentiable ℂ (Wfun P) := fun s => (Wfun_hasDerivAt P s).differentiableAt
  exact h1.comp (differentiable_id.const_mul Complex.I)

/-- **`hcont` — joint continuity of the density homotopy.**  `(t, z) ↦ W(Pscale t P, I·z)` is
continuous: `Wfun` is a polynomial-exponential in `s` with coefficients polynomial in the coupling
`t` (via `Pscale`). -/
theorem Wfun_Pscale_comp_I_continuous (P : MixParams) :
    Continuous (fun q : ℝ × ℂ => Wfun (Pscale q.1 P) (Complex.I * q.2)) := by
  unfold Wfun McNum M0Num M1Num M01Num dNum polyB polyF Pscale
  fun_prop


/-! ### Homotopy assembly (conditional on `hreal` + a uniform escape radius) -/

/-- **Homotopy assembly (conditional on `hreal` + a uniform escape radius).**  Wiring the four
geometric ingredients (`hcont`, `hholo`, `hbound`, `hbase`) into the scalar
`zeroFree_lowerHalfPlane_of_homotopy` at `H t z = W(Pscale t P, I·z)` (a=0 dilute, b=1 physical):
`W(P, I·z) ≠ 0` throughout the open lower half `z`-plane. -/
theorem Wfun_zeroFree_of_hreal (P : MixParams) {R : ℝ} (hR1 : 1 ≤ R)
    (hRunif : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s : ℂ, 0 ≤ s.re → R ≤ ‖s‖ → (Pscale t P).detF s ≠ 0)
    (hreal : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ z : ℂ, z.im = 0 →
      Wfun (Pscale t P) (Complex.I * z) ≠ 0)
    {z : ℂ} (hz : z.im < 0) :
    Wfun P (Complex.I * z) ≠ 0 := by
  have hkey := FMSA.Analysis.zeroFree_lowerHalfPlane_of_homotopy
    (H := fun t z => Wfun (Pscale t P) (Complex.I * z)) (a := 0) (b := 1) (R := R)
    (by norm_num) (by linarith)
    ((Wfun_Pscale_comp_I_continuous P).continuousOn)
    (fun t _ => Wfun_comp_I_differentiable (Pscale t P))
    (fun t ht w hw hW => by
      by_contra hnot
      rw [not_lt] at hnot
      exact Wfun_ne_zero_of_norm_ge (Pscale t P) (hRunif t ht) hw hnot (le_trans hR1 hnot) hW)
    hreal
    (fun w hw => Wfun_dilute_ne_zero P hw) z hz
  rwa [Pscale_one] at hkey

/-- **LHP pole-freeness of `detF` (conditional).**  From the assembled `W(P, I·z) ≠ 0` and `s = I·z ≠ 0`
(`z.im < 0 ⇒ z ≠ 0`), the determinant `detF(I·z) ≠ 0` in the open lower half `z`-plane. -/
theorem detF_zeroFree_of_hreal (P : MixParams) {R : ℝ} (hR1 : 1 ≤ R)
    (hRunif : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s : ℂ, 0 ≤ s.re → R ≤ ‖s‖ → (Pscale t P).detF s ≠ 0)
    (hreal : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ z : ℂ, z.im = 0 →
      Wfun (Pscale t P) (Complex.I * z) ≠ 0)
    {z : ℂ} (hz : z.im < 0) :
    P.detF (Complex.I * z) ≠ 0 := by
  have hW := Wfun_zeroFree_of_hreal P hR1 hRunif hreal hz
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  have hIz : Complex.I * z ≠ 0 := mul_ne_zero Complex.I_ne_zero hz0
  intro hdet
  exact hW (by rw [← detC_monomial_eq P hIz, hdet, mul_zero])
end
end FMSA.MixtureHSPoles
