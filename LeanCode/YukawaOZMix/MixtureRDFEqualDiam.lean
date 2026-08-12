import LeanCode.YukawaOZMix.MixtureRowSum
import LeanCode.HSMixture.MixtureRDFUniqueness
import LeanCode.HardSphere.OzSymbolCoercive

/-!
# Equal-diameter mixture RDF — existence + uniqueness assembled

The equal-diameter matrix OZ★ solution `Ψᵢⱼ = √(ρᵢρⱼ)/ρ · baxterPsi`, `Φᵢⱼ = √(ρᵢρⱼ)/ρ · c_HS` is
BOTH constructed (`matOzStar_equalDiam_phys`, existence, axiom-clean) and — via the symbol coercivity
proved here from the scalar `one_sub_rho_radial_fourier_c_HS_coercive` (rank-1 reduction) — the UNIQUE
such solution (`matOzStar_unique`, resting on the bounded WH axiom `matRadialShell_bounded_injective` =
MA.15).  This closes the equal-diameter RDF: the mixture radial distribution function is exactly the
density-weighted single-component `baxterPsi`.
-/

open MeasureTheory Set
namespace FMSA.MixtureOzStar
open FMSA.HardSphere

/-- **Equal-diameter matrix symbol coercivity, from the scalar coercivity.**  For `Φᵢⱼ = wᵢⱼ·c_HS` with
the rank-1 idempotent weight `wᵢⱼ = √(ρᵢρⱼ)/ρ = uᵢuⱼ` (`uᵢ = √ρᵢ/√ρ`, `∑uᵢ² = 1`), the matrix symbol
`I − ρĈ` has eigenvalue `1−ρĉ_HS` on the `u`-direction and `1` on `u⊥`, so its coercivity reduces to the
scalar `one_sub_rho_radial_fourier_c_HS_coercive`.  Discharges `MatSymbolCoercive` for the equal-diameter
mixture — the missing analytic input of `matOzStar_unique`. -/
theorem matSymbolCoercive_equalDiam {N : ℕ} (rhof : Fin N → ℝ) (hnonneg : ∀ k, 0 ≤ rhof k)
    {sigma eta rho : ℝ} (heta0 : 0 < eta) (heta : eta < 1) (hsigma : 0 < sigma)
    (hrho : rho = ∑ k, rhof k) (hpos : 0 < rho)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) :
    MatSymbolCoercive
      (fun i j r => (Real.sqrt (rhof i * rhof j) / rho) * c_HS eta sigma r) rho := by
  obtain ⟨ε, hε, hscal⟩ := one_sub_rho_radial_fourier_c_HS_coercive heta0 heta hsigma hpos heta_def
  refine ⟨min ε 1, lt_min hε one_pos, fun k v => ?_⟩
  set c := radial_fourier (c_HS eta sigma) k with hc
  set u : Fin N → ℝ := fun i => Real.sqrt (rhof i) / Real.sqrt rho with hu
  have hsym : ∀ i j, matRadialSymbol
      (fun i j r => (Real.sqrt (rhof i * rhof j) / rho) * c_HS eta sigma r) k i j
      = (Real.sqrt (rhof i * rhof j) / rho) * c := by
    intro i j
    show (4 * Real.pi / k) * ∫ r in Ioi (0:ℝ),
        r * ((Real.sqrt (rhof i * rhof j) / rho) * c_HS eta sigma r) * Real.sin (k * r)
      = (Real.sqrt (rhof i * rhof j) / rho) * c
    rw [show (fun r => r * ((Real.sqrt (rhof i * rhof j) / rho) * c_HS eta sigma r) * Real.sin (k * r))
        = (fun r => (Real.sqrt (rhof i * rhof j) / rho) * (r * c_HS eta sigma r * Real.sin (k * r)))
      from by funext r; ring, integral_const_mul, hc, radial_fourier]
    ring
  have hw : ∀ i j, Real.sqrt (rhof i * rhof j) / rho = u i * u j := by
    intro i j
    rw [hu, Real.sqrt_mul (hnonneg i), div_mul_div_comm, Real.mul_self_sqrt hpos.le]
  have husum : ∑ i, u i ^ 2 = 1 := by
    have hui : ∀ i, u i ^ 2 = rhof i / rho := fun i => by
      rw [hu, div_pow, Real.sq_sqrt (hnonneg i), Real.sq_sqrt hpos.le]
    simp_rw [hui, ← Finset.sum_div, ← hrho, div_self hpos.ne']
  have hquad : (∑ i, ∑ j, matRadialSymbol
      (fun i j r => (Real.sqrt (rhof i * rhof j) / rho) * c_HS eta sigma r) k i j * v i * v j)
      = c * (∑ i, u i * v i) ^ 2 := by
    rw [show (∑ i, ∑ j, matRadialSymbol
          (fun i j r => (Real.sqrt (rhof i * rhof j) / rho) * c_HS eta sigma r) k i j * v i * v j)
        = ∑ i, ∑ j, c * ((u i * v i) * (u j * v j)) from
      Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by
        rw [hsym i j, hw i j]; ring))]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul, pow_two]
  have hCS : (∑ i, u i * v i) ^ 2 ≤ ∑ i, v i ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u v
    rwa [husum, one_mul] at h
  rw [hquad]
  have hs := hscal k
  nlinarith [mul_nonneg (by linarith [min_le_right ε 1] : (0:ℝ) ≤ 1 - min ε 1)
      (by linarith [hCS] : (0:ℝ) ≤ (∑ i, v i ^ 2) - (∑ i, u i * v i) ^ 2),
    mul_nonneg (by linarith [hs, min_le_left ε 1] : (0:ℝ) ≤ 1 - rho * c - min ε 1)
      (sq_nonneg (∑ i, u i * v i))]

/-- **Equal-diameter mixture RDF — UNIQUE (the coercivity discharged).**  Any `MatOZStar` solution `Ψ'`
with the equal-diameter forcing `Φᵢⱼ = √(ρᵢρⱼ)/ρ·c_HS` equals the constructed `√(ρᵢρⱼ)/ρ·baxterPsi` on
`r > 0`.  Instantiates `matOzStar_unique` at the constructed existence witness `matOzStar_equalDiam_phys`,
with `hPhisupp` from `c_HS_outer` and `hcoercive` from `matSymbolCoercive_equalDiam`; only the arbitrary
solution's routine regularity (`hlin`/`hbdd`/`hcont`/`hcore` of the difference) is a hypothesis.  So the
equal-diameter mixture RDF is exactly the density-weighted single-component `baxterPsi`, resting only on
the bounded WH axiom `matRadialShell_bounded_injective` (= MA.15 = the unformalized Wiener tauberian). -/
theorem matOzStar_equalDiam_unique {N : ℕ} (rhof : Fin N → ℝ) (hnonneg : ∀ k, 0 ≤ rhof k)
    {sigma eta rho : ℝ} (heta0 : 0 < eta) (heta : eta < 1) (hsigma : 0 < sigma)
    (hrho : rho = ∑ k, rhof k) (hpos : 0 < rho)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6)
    {Psi' : Matrix (Fin N) (Fin N) (ℝ → ℝ)}
    (hPsi' : MatOZStar Psi'
      (fun i j r => (Real.sqrt (rhof i * rhof j) / rho) * c_HS eta sigma r) rho)
    (hlin : ∀ (i j : Fin N) (r : ℝ), 0 < r →
      matRadialConv (fun i j r => (Real.sqrt (rhof i * rhof j) / rho) * c_HS eta sigma r)
          (fun k l => fun x => Psi' k l x / x) r i j
        - matRadialConv (fun i j r => (Real.sqrt (rhof i * rhof j) / rho) * c_HS eta sigma r)
          (fun k l => fun x => ((Real.sqrt (rhof k * rhof l) / rho) * baxterPsi eta sigma rho x) / x) r i j
        = matRadialConv (fun i j r => (Real.sqrt (rhof i * rhof j) / rho) * c_HS eta sigma r)
          (fun k l => fun x =>
            (Psi' k l x - (Real.sqrt (rhof k * rhof l) / rho) * baxterPsi eta sigma rho x) / x)
          r i j)
    (hbdd : ∀ i j, ∃ M : ℝ, ∀ r : ℝ,
      |Psi' i j r - (Real.sqrt (rhof i * rhof j) / rho) * baxterPsi eta sigma rho r| ≤ M)
    (hcont : ∀ i j, ContinuousOn
      (fun r => Psi' i j r - (Real.sqrt (rhof i * rhof j) / rho) * baxterPsi eta sigma rho r)
      (Set.Ici sigma))
    (hcore : ∀ (i j : Fin N) (r : ℝ), r < sigma →
      Psi' i j r - (Real.sqrt (rhof i * rhof j) / rho) * baxterPsi eta sigma rho r = 0) :
    ∀ (i j : Fin N) (r : ℝ), 0 < r →
      Psi' i j r = (Real.sqrt (rhof i * rhof j) / rho) * baxterPsi eta sigma rho r :=
  matOzStar_unique hsigma
    (fun i j t ht => by simp [c_HS_outer ht])
    (matSymbolCoercive_equalDiam rhof hnonneg heta0 heta hsigma hrho hpos heta_def)
    hPsi'
    (matOzStar_equalDiam_phys rhof hnonneg hsigma heta hrho hpos heta_def)
    hlin hbdd hcont hcore

end FMSA.MixtureOzStar
