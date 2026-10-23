import LeanCode.YukawaOZMix.MSAMultiTailMixtureBasis

/-! First variation of the actual ordered Baxter convolution at the PY seed.
The finite basis keeps the improper integrals independent of the coupling.
Identification with the independent double-propagator FMSA construction is
a separate obligation. -/
noncomputable section
open Real Filter Topology Set MSAMixture FMSA.MatrixQ0 FMSA.ExactMSA.Breakpoint
open scoped BigOperators ContDiff
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

theorem family_Dt_entry_hasDerivAt
    (ψ : ℝ → TailMatrix ι N × TailMatrix ι N) (d : TailMatrix ι N × TailMatrix ι N)
    (hd : HasDerivAt ψ d 0) (u : ι) (i j : Fin N) :
    HasDerivAt (fun τ => (ψ τ).1 u i j) (d.1 u i j) 0 :=
  ((entry u i j).comp (ContinuousLinearMap.fst ℝ (TailMatrix ι N) (TailMatrix ι N))).hasFDerivAt.comp_hasDerivAt 0 hd

theorem family_G_entry_hasDerivAt
    (ψ : ℝ → TailMatrix ι N × TailMatrix ι N) (d : TailMatrix ι N × TailMatrix ι N)
    (hd : HasDerivAt ψ d 0) (u : ι) (i j : Fin N) :
    HasDerivAt (fun τ => (ψ τ).2 u i j) (d.2 u i j) 0 :=
  ((entry u i j).comp (ContinuousLinearMap.snd ℝ (TailMatrix ι N) (TailMatrix ι N))).hasFDerivAt.comp_hasDerivAt 0 hd

theorem W_hasDerivAt_seed (z : ι → ℝ) (ρ : Fin N → ℝ) (G0 : TailMatrix ι N)
    (ψ : ℝ → TailMatrix ι N × TailMatrix ι N) (d : TailMatrix ι N × TailMatrix ι N)
    (h0 : ψ 0 = (0, G0)) (hd : HasDerivAt ψ d 0) (u : ι) (i j : Fin N) :
    HasDerivAt (fun τ => W z ρ (ψ τ).1 (ψ τ).2 u i j) (W z ρ d.1 G0 u i j) 0 := by
  have h := (HasDerivAt.fun_sum (u := Finset.univ) (fun l _ =>
    ((family_G_entry_hasDerivAt ψ d hd u i l).const_mul (ρ l)).mul
      (family_Dt_entry_hasDerivAt ψ d hd u l j))).const_mul (2 * π / z u)
  simpa [W, Wt, h0] using h

theorem C_hasDerivAt_seed (z : ι → ℝ) (ρ σ : Fin N → ℝ) (G0 : TailMatrix ι N)
    (ψ : ℝ → TailMatrix ι N × TailMatrix ι N) (d : TailMatrix ι N × TailMatrix ι N)
    (h0 : ψ 0 = (0, G0)) (hd : HasDerivAt ψ d 0) (u : ι) (i j : Fin N) :
    HasDerivAt (fun τ => C z ρ σ (ψ τ).1 (ψ τ).2 u i j) (C z ρ σ d.1 G0 u i j) 0 := by
  have hg : ∀ l, HasDerivAt (fun τ => MSAMixture.gam (z u) ρ σ ((ψ τ).2 u) i l)
      (-(2 * π * ρ l * d.2 u i l * exp (-z u * sigMix σ i l) / z u)) 0 := by
    intro l
    convert! (hasDerivAt_const (0 : ℝ) (if i = l then (1 : ℝ) else 0)).sub
      (((family_G_entry_hasDerivAt ψ d hd u i l).const_mul (2 * π * ρ l)).mul_const
        (exp (-z u * sigMix σ i l)) |>.div_const (z u)) using 1 <;>
      simp only [MSAMixture.gam, Pi.sub_apply, zero_sub]
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun l _ =>
    ((hg l).mul (family_Dt_entry_hasDerivAt ψ d hd u l j)).mul_const
      (exp (z u * (σ l - σ i) / 2)))
  simpa [C, Ct, h0] using h

theorem mixM_hasDerivAt_seed (z : ι → ℝ) (ρ σ : Fin N → ℝ) (G0 : TailMatrix ι N)
    (ψ : ℝ → TailMatrix ι N × TailMatrix ι N) (d : TailMatrix ι N × TailMatrix ι N)
    (h0 : ψ 0 = (0, G0)) (hd : HasDerivAt ψ d 0) (u : ι) (j : Fin N) :
    HasDerivAt (fun τ => mixM (z u) ρ σ ((ψ τ).2 u) ((ψ τ).1 u) j)
      (mixM (z u) ρ σ (G0 u) (d.1 u) j) 0 := by
  exact (HasDerivAt.fun_sum (u := Finset.univ) (fun l _ =>
    ((W_hasDerivAt_seed z ρ G0 ψ d h0 hd u l j).add
      ((C_hasDerivAt_seed z ρ σ G0 ψ d h0 hd u l j).const_mul (1 + z u * σ l))).const_mul
        (ρ l))).const_mul (-(1 / z u))

theorem mixN_hasDerivAt_seed (z : ι → ℝ) (ρ σ : Fin N → ℝ) (G0 : TailMatrix ι N)
    (ψ : ℝ → TailMatrix ι N × TailMatrix ι N) (d : TailMatrix ι N × TailMatrix ι N)
    (h0 : ψ 0 = (0, G0)) (hd : HasDerivAt ψ d 0) (u : ι) (j : Fin N) :
    HasDerivAt (fun τ => mixN (z u) ρ σ ((ψ τ).2 u) ((ψ τ).1 u) j)
      (mixN (z u) ρ σ (G0 u) (d.1 u) j) 0 := by
  exact HasDerivAt.fun_sum (u := Finset.univ) (fun l _ =>
    (((W_hasDerivAt_seed z ρ G0 ψ d h0 hd u l j).const_mul
      ((1 + z u * ((σ j - σ l) / 2)) / (z u)^2)).add
        ((C_hasDerivAt_seed z ρ σ G0 ψ d h0 hd u l j).const_mul
          ((1 + z u * σ l + (z u * σ l)^2/2)/(z u)^2 +
            ((σ j - σ l)/2)*(1 + z u * σ l)/z u))).const_mul (ρ l))

def coefficientSlope (z : ι → ℝ) (ρ σ : Fin N → ℝ) (D G0 : TailMatrix ι N)
    (i j : Fin N) (b : BasisIndex ι) : ℝ :=
  bhCoefficient z ρ σ (D, G0) i j b - bhCoefficient z ρ σ (0, G0) i j b

theorem bhCoefficient_hasDerivAt_seed (z : ι → ℝ) (ρ σ : Fin N → ℝ) (G0 : TailMatrix ι N)
    (ψ : ℝ → TailMatrix ι N × TailMatrix ι N) (d : TailMatrix ι N × TailMatrix ι N)
    (h0 : ψ 0 = (0, G0)) (hd : HasDerivAt ψ d 0) (i j : Fin N) (b : BasisIndex ι) :
    HasDerivAt (fun τ => bhCoefficient z ρ σ (ψ τ) i j b)
      (coefficientSlope z ρ σ d.1 G0 i j b) 0 := by
  have hm := mixM_hasDerivAt_seed z ρ σ G0 ψ d h0 hd
  have hn := mixN_hasDerivAt_seed z ρ σ G0 ψ d h0 hd
  rcases b with b | (u | u)
  · fin_cases b
    · have h := (hasDerivAt_const (0 : ℝ) (Q0phys ρ σ i j)).add
        (HasDerivAt.fun_sum (u := Finset.univ) (fun u _ =>
          ((hm u j).const_mul (Q0phys ρ σ i j)).add
            ((hn u j).const_mul (Qppphys ρ σ i i))))
      convert! h using 1 <;>
        simp [coefficientSlope, bhCoefficient, coefficient, amplitudeQp, mixDqp,
          mixM, mixN, Wt, Ct, Pi.add_apply]
    · have h := (hasDerivAt_const (0 : ℝ) (Qppphys ρ σ j j)).add
        (HasDerivAt.fun_sum (u := Finset.univ) (fun u _ =>
          ((hm u j).const_mul (Qppphys ρ σ j j)).add
            ((hn u j).const_mul (2 * π^2 * xi2 ρ σ / vacMix ρ σ^2))))
      convert! h using 1 <;>
        simp [coefficientSlope, bhCoefficient, coefficient, amplitudeA, mixDA,
          mixM, mixN, Wt, Ct, Pi.add_apply]
  · simpa [coefficientSlope, bhCoefficient, coefficient, W, Wt] using
      W_hasDerivAt_seed z ρ G0 ψ d h0 hd u i j
  · simpa [coefficientSlope, bhCoefficient, coefficient, C, Ct] using
      C_hasDerivAt_seed z ρ σ G0 ψ d h0 hd u i j

/-- Explicit first variation: only fixed basis integrals and dressed HS
amplitudes occur. This is not defined as a derivative. -/
def linearizedCorrelation (z : ι → ℝ) (ρ σ : Fin N → ℝ) (D G0 : TailMatrix ι N)
    (i j : Fin N) (r : ℝ) : ℝ :=
  (-(∑ b : BasisIndex ι, coefficientSlope z ρ σ D G0 i j b * basisPrime z σ b i j r) +
    ∑ l, ρ l * ∑ b : BasisIndex ι, ∑ c : BasisIndex ι,
      (coefficientSlope z ρ σ D G0 i l b * bhCoefficient z ρ σ (0, G0) j l c +
        bhCoefficient z ρ σ (0, G0) i l b * coefficientSlope z ρ σ D G0 j l c) *
          basisConvolution z σ b c i j l r) / (2*π*r)

/-- Actual first derivative at any fixed position, including the inner-core
knots. At zero coupling the G-direction drops out internally. -/
theorem correlation_hasDerivAt_seed (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (G0 : TailMatrix ι N)
    (ψ : ℝ → TailMatrix ι N × TailMatrix ι N) (d : TailMatrix ι N × TailMatrix ι N)
    (h0 : ψ 0 = (0, G0)) (hd : HasDerivAt ψ d 0) (i j : Fin N) (r : ℝ) :
    HasDerivAt (fun τ => correlation z ρ σ
      (amplitudeA z ρ σ (ψ τ).1 (ψ τ).2) (amplitudeQp z ρ σ (ψ τ).1 (ψ τ).2)
      (W z ρ (ψ τ).1 (ψ τ).2) (C z ρ σ (ψ τ).1 (ψ τ).2) i j r)
      (linearizedCorrelation z ρ σ d.1 G0 i j r) 0 := by
  have hb := bhCoefficient_hasDerivAt_seed z ρ σ G0 ψ d h0 hd
  have hp : ∀ l (b c : BasisIndex ι), HasDerivAt (fun τ =>
      (bhCoefficient z ρ σ (ψ τ) i l b * bhCoefficient z ρ σ (ψ τ) j l c) *
        basisConvolution z σ b c i j l r)
      ((coefficientSlope z ρ σ d.1 G0 i l b * bhCoefficient z ρ σ (0, G0) j l c +
        bhCoefficient z ρ σ (0, G0) i l b * coefficientSlope z ρ σ d.1 G0 j l c) *
          basisConvolution z σ b c i j l r) 0 := by
    intro l b c
    convert! ((hb i l b).mul (hb j l c)).mul_const
      (basisConvolution z σ b c i j l r) using 1 <;> simp only [h0, Pi.mul_apply]
  have h := ((HasDerivAt.fun_sum (u := Finset.univ) (fun b _ =>
      (hb i j b).mul_const (basisPrime z σ b i j r))).neg.add
    (HasDerivAt.fun_sum (u := Finset.univ) (fun l _ =>
      (HasDerivAt.fun_sum (u := Finset.univ) (fun b _ =>
        HasDerivAt.fun_sum (u := Finset.univ) (fun c _ => hp l b c))).const_mul (ρ l)))).div_const
          (2*π*r)
  simp_rw [correlation_eq_basis z hz ρ σ hσ]
  exact h

/-- A genuine local BH family with its explicit actual ordered DCF slope,
throughout the positive core as well as outside contact. The whole-family
radial/OZ bridge and independent FMSA construction identity remain open. -/
theorem exists_contDiffAt_root_with_linearizedCorrelation (z : ι → ℝ)
    (ρ σ : Fin N → ℝ) (K : TailMatrix ι N) (hz : ∀ u, 0 < z u)
    (hvac : 0 < vacMix ρ σ) (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i) :
    ∃ ψ : ℝ → TailMatrix ι N × TailMatrix ι N,
      ψ 0 = (0, baseSeed z ρ σ) ∧
      (∀ᶠ τ in 𝓝 (0 : ℝ), IsRoot z ρ σ (τ • K) (ψ τ).1 (ψ τ).2) ∧
      ContDiffAt ℝ ∞ ψ 0 ∧
      HasDerivAt (fun τ => (ψ τ).1) (firstOrderDt z ρ σ K) 0 ∧
      ∀ i j r, σ j ≤ σ i → 0 < r →
        HasDerivAt (fun τ => correlation z ρ σ
          (amplitudeA z ρ σ (ψ τ).1 (ψ τ).2) (amplitudeQp z ρ σ (ψ τ).1 (ψ τ).2)
          (W z ρ (ψ τ).1 (ψ τ).2) (C z ρ σ (ψ τ).1 (ψ τ).2) i j r)
          (linearizedCorrelation z ρ σ (firstOrderDt z ρ σ K) (baseSeed z ρ σ) i j r) 0 := by
  obtain ⟨ψ, h0, hr, hc, hD⟩ := exists_contDiffAt_root_with_firstOrderDt z ρ σ K hz hvac hρ hσ
  have hd := (hc.differentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)).hasDerivAt
  have hs := firstOrderDt_eq_of_family z ρ σ K hz hvac hρ hσ ψ _ h0 hr hd
  refine ⟨ψ, h0, hr, hc, hD, ?_⟩
  intro i j r _ _
  have h := correlation_hasDerivAt_seed z hz ρ σ (fun i => (hσ i).le)
    (baseSeed z ρ σ) ψ _ h0 hd i j r
  rwa [hs] at h

/-- Connect the explicit finite-integral formula to the actual linear
Frechet derivative. This proves superposition without defining the formula
by a derivative or assuming an interchange with the improper integral. -/
theorem linearizedCorrelation_eq_fderiv (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (D G0 : TailMatrix ι N)
    (i j : Fin N) (r : ℝ) :
    linearizedCorrelation z ρ σ D G0 i j r =
      fderiv ℝ (fun p : TailMatrix ι N × TailMatrix ι N => correlation z ρ σ
        (amplitudeA z ρ σ p.1 p.2) (amplitudeQp z ρ σ p.1 p.2)
        (W z ρ p.1 p.2) (C z ρ σ p.1 p.2) i j r) (0, G0) (D, 0) := by
  let ψ : ℝ → TailMatrix ι N × TailMatrix ι N := fun τ => (τ • D, G0)
  have h0 : ψ 0 = (0, G0) := by simp [ψ]
  have hd : HasDerivAt ψ (D, 0) 0 := by
    simpa [ψ] using ((hasDerivAt_id (0 : ℝ)).smul_const D).prodMk
      (hasDerivAt_const (0 : ℝ) G0)
  have hc := (correlation_contDiff_amplitudes z hz ρ σ hσ i j r).differentiable
    (by simp : (∞ : ℕ∞ω) ≠ 0) |>.differentiableAt.hasFDerivAt (x := (0, G0))
  rw [← h0] at hc
  have ht := hc.comp_hasDerivAt 0 hd
  rw [h0] at ht
  exact (correlation_hasDerivAt_seed z hz ρ σ hσ G0 ψ (D, 0) h0 hd i j r).unique
    ht

theorem linearizedCorrelation_add (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (D E G0 : TailMatrix ι N)
    (i j : Fin N) (r : ℝ) :
    linearizedCorrelation z ρ σ (D + E) G0 i j r =
      linearizedCorrelation z ρ σ D G0 i j r + linearizedCorrelation z ρ σ E G0 i j r := by
  simp_rw [linearizedCorrelation_eq_fderiv z hz ρ σ hσ]
  have he : (D + E, (0 : TailMatrix ι N)) = (D, 0) + (E, 0) := by simp
  rw [he, map_add]

theorem firstOrderDt_add (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K L : TailMatrix ι N) :
    firstOrderDt z ρ σ (K + L) = firstOrderDt z ρ σ K + firstOrderDt z ρ σ L := by
  have he : firstOrderSource z (K + L) = firstOrderSource z K + firstOrderSource z L := by
    funext u i j
    simp only [firstOrderSource, Pi.add_apply]
    ring
  unfold firstOrderDt
  rw [he, map_add]

/-- First-order superposition of arbitrary matrix-valued tail strengths,
including mixed signs and zero strengths. -/
theorem linearizedCorrelation_tail_superposition (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (K L : TailMatrix ι N)
    (i j : Fin N) (r : ℝ) :
    linearizedCorrelation z ρ σ (firstOrderDt z ρ σ (K + L)) (baseSeed z ρ σ) i j r =
      linearizedCorrelation z ρ σ (firstOrderDt z ρ σ K) (baseSeed z ρ σ) i j r +
        linearizedCorrelation z ρ σ (firstOrderDt z ρ σ L) (baseSeed z ρ σ) i j r := by
  rw [firstOrderDt_add, linearizedCorrelation_add z hz ρ σ hσ]

/-- The explicit linearized convolution has the prescribed Yukawa exterior.
The identity follows from uniqueness of the actual family derivative. -/
theorem linearizedCorrelation_exterior (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hvac : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i)
    (i j : Fin N) (r : ℝ) (hr : edgeHi σ i j < r) :
    linearizedCorrelation z ρ σ (firstOrderDt z ρ σ K) (baseSeed z ρ σ) i j r =
      ∑ u, K u i j * exp (-z u * (r - edgeHi σ i j)) / r := by
  obtain ⟨ψ, h0, hroot, hc, _⟩ := exists_contDiffAt_root_with_firstOrderDt z ρ σ K hz hvac hρ hσ
  have hd := (hc.differentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)).hasDerivAt
  have hs := firstOrderDt_eq_of_family z ρ σ K hz hvac hρ hσ ψ _ h0 hroot hd
  have hi := correlation_hasDerivAt_seed z hz ρ σ (fun i => (hσ i).le)
    (baseSeed z ρ σ) ψ _ h0 hd i j r
  rw [hs] at hi
  exact hi.unique (correlation_exterior_hasDerivAt_of_family z hz ρ σ K
    (fun i => (hσ i).le) ψ hroot i j r hr)

end FMSA.ExactMSA.MultiTailMixture
