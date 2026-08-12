/-
Copyright (c) 2026 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import LeanCode.HSMixture.MixtureRDFUniqueness

/-!
# General-N uniform coercivity — the compactness reduction (`MatSymbolCoercive`)

The non-circular value route to MML.8 (`MixtureRDFUniqueness.lean`) needs `MatSymbolCoercive Φ ρ`:
the UNIFORM positive-definiteness of the OZ structure factor `I − ρĈ(k) ⪰ εI`.  For EQUAL diameters
this is `matSymbolCoercive_equalDiam` (rank-1 reduction to the scalar).  This file supplies the
GENERAL-N reduction, closing the "gluing" of the uniform `ε` — the abstract compactness argument the
scalar `one_sub_rho_radial_fourier_c_HS_coercive` performs by hand:

* `matSymbolCoercive_of_sphere` — HOMOGENEITY: a uniform lower bound of the symbol quadratic form
  `F(k,u) = ∑ᵢuᵢ² − ρ·∑ᵢⱼ Ĉ(k)ᵢⱼuᵢuⱼ` on the L²-unit sphere `∑ᵢuᵢ² = 1` upgrades to
  `MatSymbolCoercive` (`ε∑vᵢ² ≤ F(k,v)` for all `v`), since `F` is degree-2 homogeneous in `v`.
* `sphere_isCompact` — the L²-unit sphere in `Fin N → ℝ` is compact (closed + bounded, finite dim).
* `matSymbolCoercive_of_regions` — THREE-REGION COMPACTNESS: from uniform sphere lower bounds in the
  near-`0` (`|k| ≤ a`) and tail (`b ≤ |k|`) regions, plus symbol continuity and POINTWISE positivity
  on the compact middle `a ≤ |k| ≤ b`, the middle gives a positive min (`IsCompact.exists_isMinOn`)
  and the sphere bound follows; `matSymbolCoercive_of_sphere` then gives `MatSymbolCoercive`.

So the general-N coercivity is reduced to exactly the three CONCRETE analytic facts about the
mixture symbol — the matrix analogs of the scalar proof's three regions (near-`0` sign, middle
continuity + `det Q̂₀ ≠ 0` positivity, tail `Ĉ(k) → 0` decay).  The `k`-compactness gluing is done.

The MIDDLE positivity input is also supplied here from `det Q̂₀ ≠ 0`:
* `matSymbol_pos_of_factor` — the OZ symbol quadratic form, factored through an invertible complex
  matrix `B` as `∑ₗ|(B·u)ₗ|²`, is `> 0` on the sphere (`B·u ≠ 0` by invertibility).
* `matSymbol_middle_pos` — packaged as the `hpos` hypothesis of `matSymbolCoercive_of_regions`: a
  per-`k` factorization with `det B(k) ≠ 0` (`= det Q̂₀(−k)`, from `pyhs_mixture_no_spinodal` +
  `mixtureDet_pole_free_N`) gives the middle pointwise positivity.

The TAIL input is supplied here from the `Ĉ(k) → 0` decay:
* `matSymbol_tail_bound` — a uniform entry bound `|Ĉ(k)ᵢⱼ| ≤ M` on `b ≤ |k|` with `ρMN < 1` gives
  `htail` with `δ = 1 − ρMN` (Cauchy–Schwarz: `∑ᵢⱼĈᵢⱼuᵢuⱼ ≤ M(∑|uᵢ|)² ≤ MN` on the sphere).  The
  matrix analog of the scalar `radial_fourier_c_HS_le` (`|Ĉ(k)| ≤ cHS_bound/k²`).

The NEAR-`0` input is supplied here from the sign argument:
* `matRadialSymbol_neg` — the symbol is even in `k`.
* `matSymbol_near_bound` — if the real-space DCF quadratic form `∑ᵢⱼΦᵢⱼ(r)uᵢuⱼ` is `≤ 0` on the core
  `(0,σ)` (matrix analog of `c_HS < 0`) and `0` outside, then `∑ᵢⱼĈ(k)ᵢⱼuᵢuⱼ ≤ 0` for `|k| ≤ π/σ`
  (`(4π/k)∫r·g·sin(kr) ≤ 0`, `sin(kr) ≥ 0` since `kr ≤ π`; `k=0` is the junk value `0`; `k<0` even),
  so `hnear` holds with `ε₀ = 1`.  Matrix analog of the scalar near-`0` sign region.

So ALL THREE concrete inputs are now reduced to isolated symbol facts: near-`0` ← core-NSD
real-space DCF; middle ← `Cmix0_factorization` + `det Q̂₀ ≠ 0`; tail ← `Ĉ → 0` decay.  With the
compactness gluing and the equal-diameter closure, the general-N value route rests only on these
three concrete DCF-symbol facts (plus the committed axioms MA.15 and the physics no-spinodal).

The core-NSD input itself is PROVED for equal diameters:
* `matDCF_coreNSD_equalDiam` — for `Φᵢⱼ = √(ρᵢρⱼ)/ρ·c_HS` the core quadratic form is rank-1,
  `∑ᵢⱼΦᵢⱼ(r)uᵢuⱼ = (c_HS(r)/ρ)(∑ᵢ√ρᵢuᵢ)² ≤ 0` on `(0,σ)` (from `c_HS_neg`), so `hNSD` holds.  For
  unequal diameters the mixture DCF's pointwise core sign is the one open per-region symbol fact.
-/

open MeasureTheory Set
namespace FMSA.MixtureOzStar
variable {N : ℕ}

theorem matSymbolCoercive_of_sphere (Phi : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (rho : ℝ)
    (h : ∃ ε : ℝ, 0 < ε ∧ ∀ (k : ℝ) (u : Fin N → ℝ), (∑ i, u i ^ 2) = 1 →
      ε ≤ (∑ i, u i ^ 2) - rho * ∑ i, ∑ j, matRadialSymbol Phi k i j * u i * u j) :
    MatSymbolCoercive Phi rho := by
  obtain ⟨ε, hε, hsph⟩ := h
  refine ⟨ε, hε, fun k v => ?_⟩
  rcases eq_or_ne (∑ i, v i ^ 2) 0 with h0 | h0
  · have hvi : ∀ i, v i = 0 := by
      intro i
      have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (v i))).mp h0 i
        (Finset.mem_univ i)
      exact pow_eq_zero_iff (by norm_num) |>.mp hz
    have hdz : (∑ i, ∑ j, matRadialSymbol Phi k i j * v i * v j) = 0 :=
      Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j _ => by rw [hvi i, hvi j]; ring))
    rw [h0, hdz]; simp
  · have hspos : 0 < ∑ i, v i ^ 2 :=
      lt_of_le_of_ne (Finset.sum_nonneg (fun i _ => sq_nonneg _)) (Ne.symm h0)
    set s := Real.sqrt (∑ i, v i ^ 2) with hs
    have hsp : 0 < s := Real.sqrt_pos.mpr hspos
    have hs2 : s ^ 2 = ∑ i, v i ^ 2 := Real.sq_sqrt hspos.le
    set u : Fin N → ℝ := fun i => v i / s with hu
    have hvu : ∀ i, v i = s * u i := fun i => by rw [hu]; field_simp
    have husum : (∑ i, u i ^ 2) = 1 := by
      simp only [hu, div_pow]; rw [← Finset.sum_div, hs2, div_self hspos.ne']
    have hsum1 : (∑ i, v i ^ 2) = s ^ 2 * ∑ i, u i ^ 2 := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by rw [hvu i]; ring)
    have hsum2 : (∑ i, ∑ j, matRadialSymbol Phi k i j * v i * v j)
        = s ^ 2 * ∑ i, ∑ j, matRadialSymbol Phi k i j * u i * u j := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by rw [hvu i, hvu j]; ring)
    have hb := hsph k u husum
    rw [husum] at hb
    rw [hsum1, hsum2, husum]; nlinarith [hb, sq_nonneg s, hε]

/-- L²-unit sphere in `Fin N → ℝ` is compact. -/
theorem sphere_isCompact : IsCompact {u : Fin N → ℝ | (∑ i, u i ^ 2) = 1} := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_eq (by fun_prop) continuous_const
  · rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨1, fun u hu => ?_⟩
    simp only [Set.mem_setOf_eq] at hu
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    have h1 : u i ^ 2 ≤ ∑ j, u j ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (u j)) (Finset.mem_univ i)
    rw [hu] at h1; rw [Real.norm_eq_abs]; nlinarith [h1, abs_nonneg (u i), sq_abs (u i)]

/-- **Three-region compactness reduction ⟹ `MatSymbolCoercive`.**  From uniform lower bounds on the
L²-unit sphere in the near-`0` (`|k| ≤ a`) and tail (`b ≤ |k|`) regions, plus symbol continuity and
POINTWISE positivity of `F(k,u)` on the compact middle `a ≤ |k| ≤ b`, the OZ symbol is coercive: the
middle gives a positive min via `IsCompact.exists_isMinOn`, and `matSymbolCoercive_of_sphere` lifts
the sphere bound to all `v`.  The three concrete inputs are the matrix analogs of the scalar
`one_sub_rho_radial_fourier_c_HS_coercive`'s three regions. -/
theorem matSymbolCoercive_of_regions (Phi : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (rho : ℝ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hnear : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ (k : ℝ) (u : Fin N → ℝ), |k| ≤ a → (∑ i, u i ^ 2) = 1 →
      ε₀ ≤ (∑ i, u i ^ 2) - rho * ∑ i, ∑ j, matRadialSymbol Phi k i j * u i * u j)
    (htail : ∃ δ : ℝ, 0 < δ ∧ ∀ (k : ℝ) (u : Fin N → ℝ), b ≤ |k| → (∑ i, u i ^ 2) = 1 →
      δ ≤ (∑ i, u i ^ 2) - rho * ∑ i, ∑ j, matRadialSymbol Phi k i j * u i * u j)
    (hcont : ∀ i j, ContinuousOn (fun k => matRadialSymbol Phi k i j)
      (Set.Icc a b ∪ Set.Icc (-b) (-a)))
    (hpos : ∀ (k : ℝ) (u : Fin N → ℝ), a ≤ |k| → |k| ≤ b → (∑ i, u i ^ 2) = 1 →
      0 < (∑ i, u i ^ 2) - rho * ∑ i, ∑ j, matRadialSymbol Phi k i j * u i * u j) :
    MatSymbolCoercive Phi rho := by
  obtain ⟨ε₀, hε₀, hnear'⟩ := hnear
  obtain ⟨δ, hδ, htail'⟩ := htail
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; exact ⟨1, one_pos, fun k v => by simp⟩
  set F : ℝ × (Fin N → ℝ) → ℝ :=
    fun p => (∑ i, p.2 i ^ 2) - rho * ∑ i, ∑ j, matRadialSymbol Phi p.1 i j * p.2 i * p.2 j with hF
  set K : Set ℝ := Set.Icc a b ∪ Set.Icc (-b) (-a) with hK
  set S : Set (Fin N → ℝ) := {u | (∑ i, u i ^ 2) = 1} with hSdef
  have hKmem : ∀ k : ℝ, a ≤ |k| → |k| ≤ b → k ∈ K := by
    intro k hka hkb
    by_cases hk0 : (0:ℝ) ≤ k
    · exact Or.inl ⟨by rwa [abs_of_nonneg hk0] at hka, by rwa [abs_of_nonneg hk0] at hkb⟩
    · replace hk0 := not_le.mp hk0
      rw [abs_of_neg hk0] at hka hkb
      exact Or.inr ⟨by linarith, by linarith⟩
  have hKmem' : ∀ k ∈ K, a ≤ |k| ∧ |k| ≤ b := by
    intro k hk
    rcases hk with hk | hk
    · rw [abs_of_nonneg (by linarith [hk.1, ha] : (0:ℝ) ≤ k)]; exact ⟨hk.1, hk.2⟩
    · rw [abs_of_neg (by linarith [hk.2, ha] : k < 0)]
      exact ⟨by linarith [hk.2], by linarith [hk.1]⟩
  have hKcomp : IsCompact K := (isCompact_Icc).union isCompact_Icc
  have hScomp : IsCompact S := sphere_isCompact
  have hprod : IsCompact (K ×ˢ S) := hKcomp.prod hScomp
  have hax : |a| = a := abs_of_nonneg ha.le
  have hane : a ∈ K := hKmem a hax.ge (hax.le.trans hab)
  have hu0 : (Pi.single (⟨0, hN⟩ : Fin N) (1:ℝ)) ∈ S := by
    simp only [hSdef, Set.mem_setOf_eq]
    rw [Finset.sum_eq_single (⟨0, hN⟩ : Fin N)]
    · simp
    · intro j _ hj; rw [Pi.single_eq_of_ne hj]; ring
    · intro h; exact absurd (Finset.mem_univ _) h
  have hne : (K ×ˢ S).Nonempty :=
    ⟨(a, Pi.single (⟨0, hN⟩ : Fin N) (1:ℝ)), Set.mk_mem_prod hane hu0⟩
  have hFcont : ContinuousOn F (K ×ˢ S) := by
    apply ContinuousOn.sub
    · exact (by fun_prop : Continuous fun p : ℝ × (Fin N → ℝ) => ∑ i, p.2 i ^ 2).continuousOn
    · apply ContinuousOn.const_mul
      apply continuousOn_finset_sum; intro i _
      apply continuousOn_finset_sum; intro j _
      refine ((hcont i j).comp continuousOn_fst (fun p hp => hp.1)).mul ?_ |>.mul ?_
      · exact (by fun_prop : Continuous fun p : ℝ × (Fin N → ℝ) => p.2 i).continuousOn
      · exact (by fun_prop : Continuous fun p : ℝ × (Fin N → ℝ) => p.2 j).continuousOn
  obtain ⟨p₀, hp₀mem, hp₀min⟩ := hprod.exists_isMinOn hne hFcont
  have hm : 0 < F p₀ := by
    obtain ⟨hk₀, hu₀⟩ := Set.mem_prod.mp hp₀mem
    obtain ⟨hka, hkb⟩ := hKmem' p₀.1 hk₀
    exact hpos p₀.1 p₀.2 hka hkb hu₀
  apply matSymbolCoercive_of_sphere
  refine ⟨min (min ε₀ δ) (F p₀), lt_min (lt_min hε₀ hδ) hm, fun k u husum => ?_⟩
  by_cases hk : |k| ≤ a
  · exact le_trans ((min_le_left _ _).trans (min_le_left _ _)) (hnear' k u hk husum)
  · replace hk := not_le.mp hk
    by_cases hk2 : |k| ≤ b
    · have hmem : (k, u) ∈ K ×ˢ S := Set.mk_mem_prod (hKmem k (le_of_lt hk) hk2) husum
      exact le_trans (min_le_right _ _) (hp₀min hmem)
    · replace hk2 := not_le.mp hk2
      exact le_trans ((min_le_left _ _).trans (min_le_right _ _)) (htail' k u (le_of_lt hk2) husum)



/-- **Middle pointwise positivity from `det Q̂₀ ≠ 0`.**  If the OZ symbol quadratic form factors as
a squared norm `∑ᵢuᵢ² − ρ∑ᵢⱼĈ(k)ᵢⱼuᵢuⱼ = ∑ₗ |(B·u)ₗ|²` through an invertible complex matrix `B`
(`B = Q̂₀(−k)ᵀ` on the real axis, via `Cmix0_factorization`; `det B ≠ 0` from
`pyhs_mixture_no_spinodal` + `mixtureDet_pole_free_N`), then it is `> 0` on the L²-unit sphere:
`B·u ≠ 0` (invertibility) forces a strictly-positive term.  Discharges `hpos` of
`matSymbolCoercive_of_regions`. -/
theorem matSymbol_pos_of_factor (Phi : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (rho k : ℝ)
    (B : Matrix (Fin N) (Fin N) ℂ) (hB : B.det ≠ 0)
    (hfac : ∀ (v : Fin N → ℝ),
      (∑ i, v i ^ 2) - rho * ∑ i, ∑ j, matRadialSymbol Phi k i j * v i * v j
        = ∑ l, Complex.normSq (B.mulVec (fun i => (v i : ℂ)) l))
    (u : Fin N → ℝ) (hu : (∑ i, u i ^ 2) = 1) :
    0 < (∑ i, u i ^ 2) - rho * ∑ i, ∑ j, matRadialSymbol Phi k i j * u i * u j := by
  rw [hfac u]
  have hune : (fun i => (u i : ℂ)) ≠ 0 := by
    intro h
    have hz : ∀ i, u i = 0 := fun i => by
      have hc : (u i : ℂ) = 0 := by simpa using congrFun h i
      exact_mod_cast hc
    rw [Finset.sum_eq_zero (fun i _ => by rw [hz i]; ring)] at hu
    exact one_ne_zero hu.symm
  have hBune : B.mulVec (fun i => (u i : ℂ)) ≠ 0 := by
    intro h
    apply hune
    have hd : IsUnit B.det := isUnit_iff_ne_zero.mpr hB
    have hinv : B⁻¹.mulVec (B.mulVec (fun i => (u i : ℂ))) = (fun i => (u i : ℂ)) := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul B hd, Matrix.one_mulVec]
    rw [h, Matrix.mulVec_zero] at hinv
    exact hinv.symm
  obtain ⟨l, hl⟩ := Function.ne_iff.mp hBune
  refine Finset.sum_pos' (fun l _ => Complex.normSq_nonneg _) ⟨l, Finset.mem_univ l, ?_⟩
  exact Complex.normSq_pos.mpr hl

/-- **Packaged middle positivity — discharges `hpos` of `matSymbolCoercive_of_regions`.**  A
per-`k` factorization `hfac` (`= ∑ₗ|(B(k)·u)ₗ|²`) with `det B(k) ≠ 0` (`= det Q̂₀(−k)`) on the
middle `a ≤ |k| ≤ b` yields the pointwise positivity of the symbol on the L²-unit sphere — the
`hpos` input of `matSymbolCoercive_of_regions`, from `det Q̂₀ ≠ 0` alone. -/
theorem matSymbol_middle_pos (Phi : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (rho : ℝ) {a b : ℝ}
    (Bfun : ℝ → Matrix (Fin N) (Fin N) ℂ)
    (hBdet : ∀ k : ℝ, a ≤ |k| → |k| ≤ b → (Bfun k).det ≠ 0)
    (hfac : ∀ k : ℝ, a ≤ |k| → |k| ≤ b → ∀ (v : Fin N → ℝ),
      (∑ i, v i ^ 2) - rho * ∑ i, ∑ j, matRadialSymbol Phi k i j * v i * v j
        = ∑ l, Complex.normSq ((Bfun k).mulVec (fun i => (v i : ℂ)) l)) :
    ∀ (k : ℝ) (u : Fin N → ℝ), a ≤ |k| → |k| ≤ b → (∑ i, u i ^ 2) = 1 →
      0 < (∑ i, u i ^ 2) - rho * ∑ i, ∑ j, matRadialSymbol Phi k i j * u i * u j :=
  fun k u hka hkb hu =>
    matSymbol_pos_of_factor Phi rho k (Bfun k) (hBdet k hka hkb) (hfac k hka hkb) u hu

/-- **Tail decay bound — `Ĉ(k) → 0` ⟹ `htail`.**  If every symbol entry is uniformly small in the
tail, `|Ĉ(k)ᵢⱼ| ≤ M` for `b ≤ |k|`, with `ρ·M·N < 1`, then the OZ symbol quadratic form is bounded
below by `δ = 1 − ρMN > 0` on the L²-unit sphere: `∑ᵢⱼĈᵢⱼuᵢuⱼ ≤ M(∑ᵢ|uᵢ|)² ≤ MN∑ᵢuᵢ² = MN`
(Cauchy–Schwarz), so `∑ᵢuᵢ² − ρ∑ᵢⱼĈᵢⱼuᵢuⱼ ≥ 1 − ρMN`.  This discharges `htail` of
`matSymbolCoercive_of_regions` from the mixture DCF's `Ĉ(k) → 0` decay (matrix analog of the scalar
`radial_fourier_c_HS_le`). -/
theorem matSymbol_tail_bound (Phi : Matrix (Fin N) (Fin N) (ℝ → ℝ)) {rho : ℝ} (hrho : 0 ≤ rho)
    {b M : ℝ} (hM : ∀ (i j : Fin N) (k : ℝ), b ≤ |k| → |matRadialSymbol Phi k i j| ≤ M)
    (hMbound : rho * M * (N : ℝ) < 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (k : ℝ) (u : Fin N → ℝ), b ≤ |k| → (∑ i, u i ^ 2) = 1 →
      δ ≤ (∑ i, u i ^ 2) - rho * ∑ i, ∑ j, matRadialSymbol Phi k i j * u i * u j := by
  refine ⟨1 - rho * M * (N : ℝ), by linarith, fun k u hkb hu => ?_⟩
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp only [Finset.univ_eq_empty, Finset.sum_empty] at hu
    exact (zero_ne_one hu).elim
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM ⟨0, hN⟩ ⟨0, hN⟩ k hkb)
  have hcs : (∑ i, |u i|) ^ 2 ≤ (N : ℝ) * ∑ i, u i ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1:ℝ)) (fun i => |u i|)
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, sq_abs] at h
    exact h
  have hprod : (∑ i, ∑ j, M * (|u i| * |u j|)) = M * (∑ i, |u i|) ^ 2 := by
    rw [pow_two, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
  have hqf : (∑ i, ∑ j, matRadialSymbol Phi k i j * u i * u j) ≤ M * (N : ℝ) := by
    calc (∑ i, ∑ j, matRadialSymbol Phi k i j * u i * u j)
        ≤ ∑ i, ∑ j, |matRadialSymbol Phi k i j * u i * u j| :=
          Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => le_abs_self _))
      _ = ∑ i, ∑ j, |matRadialSymbol Phi k i j| * (|u i| * |u j|) := by
          simp_rw [abs_mul]; exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl
            (fun j _ => by ring))
      _ ≤ ∑ i, ∑ j, M * (|u i| * |u j|) :=
          Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ =>
            mul_le_mul_of_nonneg_right (hM i j k hkb) (mul_nonneg (abs_nonneg _) (abs_nonneg _))))
      _ = M * (∑ i, |u i|) ^ 2 := hprod
      _ ≤ M * ((N : ℝ) * ∑ i, u i ^ 2) := mul_le_mul_of_nonneg_left hcs hM0
      _ = M * (N : ℝ) := by rw [hu]; ring
  rw [hu]
  nlinarith [mul_le_mul_of_nonneg_left hqf hrho]


/-- `matRadialSymbol` is even in `k` (`sin` odd, `1/k` odd). -/
theorem matRadialSymbol_neg (Phi : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (k : ℝ) (i j : Fin N) :
    matRadialSymbol Phi (-k) i j = matRadialSymbol Phi k i j := by
  unfold matRadialSymbol
  have hint : (∫ r in Set.Ioi (0:ℝ), r * Phi i j r * Real.sin (-k * r))
      = -∫ r in Set.Ioi (0:ℝ), r * Phi i j r * Real.sin (k * r) := by
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi (fun r _ => ?_)
    rw [show -k * r = -(k * r) by ring, Real.sin_neg]; ring
  rw [hint, div_neg]; ring

/-- **Near-`0` sign bound ⟹ `hnear`.**  When the real-space DCF quadratic form
`g(r) = ∑ᵢⱼΦᵢⱼ(r)uᵢuⱼ` is `≤ 0` on the core `(0,σ)` (matrix analog of `c_HS < 0`) and `0` outside,
the OZ symbol quadratic form is `≤ 0` for `|k| ≤ π/σ`: for `0 < k ≤ π/σ`,
`∑ᵢⱼ Ĉ(k)ᵢⱼuᵢuⱼ = (4π/k)∫₀^∞ r·g(r)·sin(kr) ≤ 0` (integrand `≤ 0`: `r>0`, `g≤0`, `sin(kr)≥0` since
`kr ≤ π`); `k=0` gives `0` (the `4π/k` junk value); `k<0` by evenness.  So
`∑ᵢuᵢ² − ρ∑ᵢⱼĈᵢⱼuᵢuⱼ ≥ 1`, giving `hnear` of `matSymbolCoercive_of_regions` with `ε₀ = 1`.  (`hqf`
is the ∑/∫-swap identity of the symbol quadratic form; a definitional/Fubini step for the concrete
symbol.) -/
theorem matSymbol_near_bound (Phi : Matrix (Fin N) (Fin N) (ℝ → ℝ)) {rho sigma : ℝ}
    (hrho : 0 ≤ rho) (hsigma : 0 < sigma)
    (hqf : ∀ (k : ℝ) (u : Fin N → ℝ), 0 < k →
      (∑ i, ∑ j, matRadialSymbol Phi k i j * u i * u j)
        = (4 * Real.pi / k) * ∫ r in Set.Ioi (0:ℝ),
            r * (∑ i, ∑ j, Phi i j r * u i * u j) * Real.sin (k * r))
    (hsupp : ∀ (u : Fin N → ℝ) (r : ℝ), sigma ≤ r → (∑ i, ∑ j, Phi i j r * u i * u j) = 0)
    (hNSD : ∀ (u : Fin N → ℝ) (r : ℝ), 0 < r → r < sigma → (∑ i, ∑ j, Phi i j r * u i * u j) ≤ 0) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ (k : ℝ) (u : Fin N → ℝ), |k| ≤ Real.pi / sigma → (∑ i, u i ^ 2) = 1 →
      ε₀ ≤ (∑ i, u i ^ 2) - rho * ∑ i, ∑ j, matRadialSymbol Phi k i j * u i * u j := by
  refine ⟨1, one_pos, fun k u hk hu => ?_⟩
  have key : ∀ (m : ℝ), 0 < m → m ≤ Real.pi / sigma →
      (∑ i, ∑ j, matRadialSymbol Phi m i j * u i * u j) ≤ 0 := by
    intro m hm hmb
    rw [hqf m u hm]
    apply mul_nonpos_of_nonneg_of_nonpos (by positivity)
    apply setIntegral_nonpos measurableSet_Ioi
    intro r hr
    rw [Set.mem_Ioi] at hr
    rcases lt_or_ge r sigma with hrs | hrs
    · have hmr : m * r ≤ Real.pi := by
        have h1 : m * r ≤ (Real.pi / sigma) * r := by
          apply mul_le_mul_of_nonneg_right hmb hr.le
        have h2 : (Real.pi / sigma) * r ≤ (Real.pi / sigma) * sigma :=
          mul_le_mul_of_nonneg_left hrs.le (by positivity)
        rw [div_mul_cancel₀ _ hsigma.ne'] at h2
        linarith
      have hsin : 0 ≤ Real.sin (m * r) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) hmr
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos hr.le (hNSD u r hr hrs)) hsin
    · rw [hsupp u r hrs]; simp
  have hsign : (∑ i, ∑ j, matRadialSymbol Phi k i j * u i * u j) ≤ 0 := by
    rcases lt_trichotomy k 0 with hkn | hkz | hkp
    · have hrw : (∑ i, ∑ j, matRadialSymbol Phi k i j * u i * u j)
          = ∑ i, ∑ j, matRadialSymbol Phi (-k) i j * u i * u j :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl
          (fun j _ => by rw [matRadialSymbol_neg]))
      rw [hrw]
      exact key (-k) (by linarith) (by rwa [abs_of_neg hkn] at hk)
    · subst hkz
      have h0 : ∀ i j, matRadialSymbol Phi 0 i j = 0 := fun i j => by simp [matRadialSymbol]
      simp only [h0, zero_mul, Finset.sum_const_zero, le_refl]
    · exact key k hkp (by rwa [abs_of_pos hkp] at hk)
  rw [hu]; nlinarith [hsign, hrho]


open FMSA.HardSphere in
/-- **Equal-diameter real-space DCF is NSD in the core.**  For the equal-diameter forcing
`Φᵢⱼ = √(ρᵢρⱼ)/ρ · c_HS`, the quadratic form is rank-1: `∑ᵢⱼΦᵢⱼ(r)uᵢuⱼ = (c_HS(r)/ρ)(∑ᵢ√ρᵢ uᵢ)²`,
so `c_HS(r) < 0` on the core `(0,σ)` (`c_HS_neg`) makes it `≤ 0`.  Discharges the `hNSD` core-sign
hypothesis of `matSymbol_near_bound` for the equal-diameter mixture. -/
theorem matDCF_coreNSD_equalDiam (rhof : Fin N → ℝ) (hnonneg : ∀ k, 0 ≤ rhof k)
    {sigma eta rho : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1) (hsigma : 0 < sigma) (hpos : 0 < rho)
    (u : Fin N → ℝ) (r : ℝ) (hr0 : 0 < r) (hrs : r < sigma) :
    (∑ i, ∑ j, (Real.sqrt (rhof i * rhof j) / rho * c_HS eta sigma r) * u i * u j) ≤ 0 := by
  have hc : c_HS eta sigma r < 0 := c_HS_neg heta0 heta1 hsigma hr0 hrs
  have hquad : (∑ i, ∑ j, (Real.sqrt (rhof i * rhof j) / rho * c_HS eta sigma r) * u i * u j)
      = (c_HS eta sigma r / rho) * (∑ i, Real.sqrt (rhof i) * u i) ^ 2 := by
    have step1 : (∑ i, ∑ j, (Real.sqrt (rhof i * rhof j) / rho * c_HS eta sigma r) * u i * u j)
        = (c_HS eta sigma r / rho) * ∑ i, ∑ j,
            (Real.sqrt (rhof i) * u i) * (Real.sqrt (rhof j) * u j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Real.sqrt_mul (hnonneg i)]; ring
    rw [step1, ← Finset.sum_mul_sum]; ring
  rw [hquad]
  exact mul_nonpos_of_nonpos_of_nonneg (div_neg_of_neg_of_pos hc hpos).le (sq_nonneg _)


/-- **2×2 NSD from the determinant condition.**  A symmetric `2×2` matrix with nonpositive diagonal
and nonnegative determinant is negative-semidefinite: `∑ᵢⱼMᵢⱼuᵢuⱼ ≤ 0`.  The unequal-diameter mixed
DCF matrix is NSD in the core but is *not* diagonally dominant in general (numerically: `N=2` at
`σ`-ratio `0.6`, and every `N=3`, fail diagonal dominance), so the Gershgorin/AM-GM criterion cannot
close it — the determinant condition is the correct one (`M` NSD `⟺ Mᵢᵢ ≤ 0` and `det M ≥ 0`).  For
`M 0 0 < 0` the form squares as `M₀₀·F = (M₀₀u₀+M₀₁u₁)² + (det)u₁² ≥ 0`; for `M 0 0 = 0` the
determinant forces `M 0 1 = 0` and only the `M₁₁u₁² ≤ 0` term survives. -/
theorem matNSD_2x2_of_det (M : Matrix (Fin 2) (Fin 2) ℝ) (hsym : M 0 1 = M 1 0)
    (h00 : M 0 0 ≤ 0) (h11 : M 1 1 ≤ 0)
    (hdet : 0 ≤ M 0 0 * M 1 1 - M 0 1 * M 1 0)
    (u : Fin 2 → ℝ) :
    (∑ i, ∑ j, M i j * u i * u j) ≤ 0 := by
  simp only [Fin.sum_univ_two]
  rw [← hsym] at *
  rcases lt_or_eq_of_le h00 with ha | ha
  · nlinarith [sq_nonneg (M 0 0 * u 0 + M 0 1 * u 1), mul_nonneg hdet (sq_nonneg (u 1)), ha,
      mul_pos (neg_pos.mpr ha) (neg_pos.mpr ha)]
  · have hb : M 0 1 = 0 := by nlinarith [sq_nonneg (M 0 1), hdet, ha]
    rw [ha, hb]
    simp only [zero_mul, zero_add, add_zero]
    nlinarith [h11, sq_nonneg (u 1)]

/-- **`N=2` DCF core-NSD from the per-`r` determinant condition** — a valid CONDITIONAL reduction.
Packages `matNSD_2x2_of_det` into the `hNSD` core-sign shape consumed by `matSymbol_near_bound`:
IF on the whole core `(0,σ)` the diagonal DCFs are nonpositive (`Φ₀₀,Φ₁₁ ≤ 0`) and the `2×2` DCF
determinant is nonnegative (`Φ₀₀Φ₁₁ ≥ Φ₀₁²`), THEN the real-space DCF matrix `(Φᵢⱼ(r))` is NSD on
the core.  **⚠ CAUTION (2026-08-09): for UNEQUAL diameters the hypotheses are UNMEETABLE, so this
does NOT discharge the unequal near-`0` route.**  On the band `σ_min < r < R₀₁ = (σ₀+σ₁)/2` the
like-pair DCF `Φ₀₀` has already vanished (PY range `= σ₀`) while `Φ₀₁ ≠ 0` (range `R₀₁ > σ₀`),
so the determinant is `−Φ₀₁² < 0` and the matrix is INDEFINITE there — see
`matSym_2x2_pos_of_zero_diag`.  (My earlier "numerically confirmed a.e." claim was an artifact of a
scan restricted to `r < σ_min`.)  The DCF matrix is NSD only on `(0,σ_min)`; equal diameters have no
band (`R₀₁ = σ`) so `matDCF_coreNSD_equalDiam` is unaffected.  For unequal diameters the near-`0`
region must instead be covered by continuity of the regular `1 − ρĈ(k)` at `k = 0` plus stability
(`det Q̂₀ ≠ 0` at the origin), NOT by pointwise DCF-NSD. -/
theorem matDCF_coreNSD_N2_of_conditions (Phi : Matrix (Fin 2) (Fin 2) (ℝ → ℝ)) {sigma : ℝ}
    (hsym : ∀ r, Phi 0 1 r = Phi 1 0 r)
    (h00 : ∀ r, 0 < r → r < sigma → Phi 0 0 r ≤ 0)
    (h11 : ∀ r, 0 < r → r < sigma → Phi 1 1 r ≤ 0)
    (hdet : ∀ r, 0 < r → r < sigma → 0 ≤ Phi 0 0 r * Phi 1 1 r - Phi 0 1 r * Phi 1 0 r)
    (u : Fin 2 → ℝ) (r : ℝ) (hr0 : 0 < r) (hrs : r < sigma) :
    (∑ i, ∑ j, Phi i j r * u i * u j) ≤ 0 :=
  matNSD_2x2_of_det (fun i j => Phi i j r) (hsym r) (h00 r hr0 hrs) (h11 r hr0 hrs)
    (hdet r hr0 hrs) u

/-- **The unequal-diameter DCF matrix is NOT NSD on the band `σ_min < r < R₀₁` — refutation.**  A
symmetric `2×2` matrix with a ZERO diagonal entry and a NONZERO off-diagonal entry admits a vector
making the quadratic form strictly positive (`u = ((1−M₁₁)/(2M₀₁), 1)` gives form `= 1 > 0`).  This
is exactly the mixture DCF on the band: the PY like-pair `Φ₀₀` vanishes beyond contact `σ₀` while
the unlike-pair `Φ₀₁` remains nonzero out to `R₀₁ = (σ₀+σ₁)/2 > σ₀`, so `[[0, Φ₀₁],[Φ₀₁, Φ₁₁]]` has
determinant `−Φ₀₁² < 0` and a strictly positive eigenvalue.  ⇒ the `hNSD` hypothesis of
`matSymbol_near_bound` CANNOT hold on the full core for unequal diameters, and the near-`0`
pointwise-DCF-NSD route is EQUAL-DIAMETER-SPECIFIC (the equal case has an empty band). -/
theorem matSym_2x2_pos_of_zero_diag (M : Matrix (Fin 2) (Fin 2) ℝ) (hsym : M 0 1 = M 1 0)
    (h00 : M 0 0 = 0) (h01 : M 0 1 ≠ 0) :
    ∃ u : Fin 2 → ℝ, 0 < ∑ i, ∑ j, M i j * u i * u j := by
  refine ⟨![(1 - M 1 1) / (2 * M 0 1), 1], ?_⟩
  have hval : (∑ i, ∑ j, M i j * (![(1 - M 1 1) / (2 * M 0 1), 1]) i
      * (![(1 - M 1 1) / (2 * M 0 1), 1]) j) = 1 := by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [h00, ← hsym]
    field_simp
    ring
  rw [hval]; exact one_pos


/-- **Corrected near-`0` coercivity — from continuity + PD at `k = 0`.**  Replaces the RETRACTED
pointwise-DCF-NSD near-`0` bound (`matSymbol_near_bound`), equal-diameter-only.  The symbol
`matRadialSymbol Φ k` jumps at `k = 0` (the `4π/k` junk value is `0`), but the true DCF transform
extends continuously through `0` with a PD value there (stability).  Given a continuous regularizer
`Csym` agreeing with the symbol off `0` (`hagree`), continuous near `0` (`hcont`), and PD at `0`
(`hpd0`: `∑uᵢ² − ρ∑Csym(0)ᵢⱼuᵢuⱼ ≥ ε₀` on the sphere), a compactness argument yields a
neighborhood `|k| ≤ a` and `ε > 0` realizing the `hnear` bound of `matSymbolCoercive_of_regions`.
Mechanism: the sphere is compact, so the sublevel set `Bad = {(k,u) : form ≤ ε₀/2}` is compact; its
`k`-projection is compact and misses `0` (PD gives `form(0,u) ≥ ε₀ > ε₀/2`), so bounded off `0` by
a ball — that radius is `a`.  At `k = 0` the junk value gives form `= 1 ≥ ε`; off `0`, `hagree` +
continuity + PD.  Valid for UNEQUAL diameters. -/
theorem matSymbol_near_of_continuous_pd (Phi : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (rho : ℝ)
    (Csym : ℝ → Matrix (Fin N) (Fin N) ℝ) {a₀ : ℝ} (ha₀ : 0 < a₀)
    (hagree : ∀ k, k ≠ 0 → ∀ i j, Csym k i j = matRadialSymbol Phi k i j)
    (hcont : ∀ i j, ContinuousOn (fun k => Csym k i j) (Set.Icc (-a₀) a₀))
    (hpd0 : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ (u : Fin N → ℝ), (∑ i, u i ^ 2) = 1 →
        ε₀ ≤ (∑ i, u i ^ 2) - rho * ∑ i, ∑ j, Csym 0 i j * u i * u j) :
    ∃ a : ℝ, 0 < a ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ (k : ℝ) (u : Fin N → ℝ), |k| ≤ a →
      (∑ i, u i ^ 2) = 1 →
        ε ≤ (∑ i, u i ^ 2) - rho * ∑ i, ∑ j, matRadialSymbol Phi k i j * u i * u j := by
  obtain ⟨ε₀, hε₀, hpd⟩ := hpd0
  have hzero : ∀ i j, matRadialSymbol Phi 0 i j = 0 := fun i j => by
    simp [matRadialSymbol]
  set S : Set (Fin N → ℝ) := {u | (∑ i, u i ^ 2) = 1} with hSdef
  set K₀ : Set ℝ := Set.Icc (-a₀) a₀ with hK₀
  set g : ℝ × (Fin N → ℝ) → ℝ :=
    fun p => (∑ i, p.2 i ^ 2) - rho * ∑ i, ∑ j, Csym p.1 i j * p.2 i * p.2 j with hg
  have hSclosed : IsClosed S := isClosed_eq (by fun_prop) continuous_const
  have hKSclosed : IsClosed (K₀ ×ˢ S) := isClosed_Icc.prod hSclosed
  have hcomp : IsCompact (K₀ ×ˢ S) := (isCompact_Icc).prod sphere_isCompact
  have hgcont : ContinuousOn g (K₀ ×ˢ S) := by
    apply ContinuousOn.sub
    · exact (by fun_prop : Continuous fun p : ℝ × (Fin N → ℝ) => ∑ i, p.2 i ^ 2).continuousOn
    · apply ContinuousOn.const_mul
      apply continuousOn_finset_sum; intro i _
      apply continuousOn_finset_sum; intro j _
      refine ((hcont i j).comp continuousOn_fst (fun p hp => hp.1)).mul ?_ |>.mul ?_
      · exact (by fun_prop : Continuous fun p : ℝ × (Fin N → ℝ) => p.2 i).continuousOn
      · exact (by fun_prop : Continuous fun p : ℝ × (Fin N → ℝ) => p.2 j).continuousOn
  set Bad : Set (ℝ × (Fin N → ℝ)) := (K₀ ×ˢ S) ∩ g ⁻¹' (Set.Iic (ε₀ / 2)) with hBad
  have hBadclosed : IsClosed Bad :=
    hgcont.preimage_isClosed_of_isClosed hKSclosed isClosed_Iic
  have hBadcomp : IsCompact Bad := hcomp.of_isClosed_subset hBadclosed Set.inter_subset_left
  have hπcomp : IsCompact (Prod.fst '' Bad) := hBadcomp.image continuous_fst
  have h0notin : (0 : ℝ) ∉ Prod.fst '' Bad := by
    rintro ⟨⟨k, u⟩, hmem, hk⟩
    simp only at hk; subst hk
    have hu : u ∈ S := hmem.1.2
    have hle : g (0, u) ≤ ε₀ / 2 := hmem.2
    have hge : ε₀ ≤ g (0, u) := hpd u hu
    linarith
  have hopen : IsOpen (Prod.fst '' Bad)ᶜ := hπcomp.isClosed.isOpen_compl
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds h0notin)
  refine ⟨min a₀ (r / 2), lt_min ha₀ (by linarith), min 1 (ε₀ / 2),
    lt_min one_pos (by linarith), fun k u hk hu => ?_⟩
  have hka₀ : |k| ≤ a₀ := le_trans hk (min_le_left _ _)
  have hkr : |k| < r := lt_of_le_of_lt (le_trans hk (min_le_right _ _)) (by linarith)
  have hkK₀ : k ∈ K₀ := by
    rw [hK₀, Set.mem_Icc]
    constructor <;> [linarith [abs_le.mp hka₀]; linarith [abs_le.mp hka₀]]
  have huS : u ∈ S := hu
  have hknot : k ∉ Prod.fst '' Bad := by
    apply hrsub
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]; exact hkr
  have hgt : ε₀ / 2 < g (k, u) := by
    by_contra h
    exact hknot ⟨(k, u), ⟨Set.mk_mem_prod hkK₀ huS, not_lt.mp h⟩, rfl⟩
  rcases eq_or_ne k 0 with hk0 | hk0
  · subst hk0
    have hz0 : (∑ i, ∑ j, matRadialSymbol Phi (0 : ℝ) i j * u i * u j) = 0 :=
      Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j _ => by rw [hzero i j]; ring))
    rw [hz0, hu]; simp only [mul_zero, sub_zero]; exact min_le_left _ _
  · have hEq : (∑ i, u i ^ 2) - rho * ∑ i, ∑ j, matRadialSymbol Phi k i j * u i * u j
        = g (k, u) := by
      simp only [hg]
      congr 2
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      rw [hagree k hk0 i j]
    rw [hEq]; exact le_trans (min_le_right _ _) hgt.le

/-- **Full symbol coercivity via the corrected near-`0` route.**  Assembles `MatSymbolCoercive` from
the corrected near-`0` reduction (`matSymbol_near_of_continuous_pd`: `Csym` continuity + PD-at-`0`)
around `0`, plus the UNCHANGED middle (`hpos_all`: pointwise positivity for every `k ≠ 0`, the
`matSymbol_pos_of_factor` / `det Q̂₀ ≠ 0` fact) and tail (`htail`: `Ĉ → 0` decay).  The near lemma
supplies a radius `a`; the middle runs on `[min a b, b]`, the tail on `|k| ≥ b`, covering the line
via `matSymbolCoercive_of_regions`.  Unlike the retracted DCF-NSD route, every input is valid for
UNEQUAL diameters: `hpd0` is stability at `k = 0`, not pointwise real-space DCF-NSD. -/
theorem matSymbolCoercive_of_regularNear (Phi : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (rho : ℝ)
    (Csym : ℝ → Matrix (Fin N) (Fin N) ℝ) {a₀ b : ℝ} (ha₀ : 0 < a₀) (hb : 0 < b)
    (hagree : ∀ k, k ≠ 0 → ∀ i j, Csym k i j = matRadialSymbol Phi k i j)
    (hcont_near : ∀ i j, ContinuousOn (fun k => Csym k i j) (Set.Icc (-a₀) a₀))
    (hpd0 : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ (u : Fin N → ℝ), (∑ i, u i ^ 2) = 1 →
        ε₀ ≤ (∑ i, u i ^ 2) - rho * ∑ i, ∑ j, Csym 0 i j * u i * u j)
    (hcont_sym : ∀ i j, ContinuousOn (fun k => matRadialSymbol Phi k i j) {k : ℝ | k ≠ 0})
    (hpos_all : ∀ (k : ℝ) (u : Fin N → ℝ), k ≠ 0 → (∑ i, u i ^ 2) = 1 →
      0 < (∑ i, u i ^ 2) - rho * ∑ i, ∑ j, matRadialSymbol Phi k i j * u i * u j)
    (htail : ∃ δ : ℝ, 0 < δ ∧ ∀ (k : ℝ) (u : Fin N → ℝ), b ≤ |k| → (∑ i, u i ^ 2) = 1 →
      δ ≤ (∑ i, u i ^ 2) - rho * ∑ i, ∑ j, matRadialSymbol Phi k i j * u i * u j) :
    MatSymbolCoercive Phi rho := by
  obtain ⟨a, ha, ε, hε, hnear⟩ :=
    matSymbol_near_of_continuous_pd Phi rho Csym ha₀ hagree hcont_near hpd0
  have ha' : 0 < min a b := lt_min ha hb
  have hsub : (Set.Icc (min a b) b ∪ Set.Icc (-b) (-(min a b))) ⊆ {k : ℝ | k ≠ 0} := by
    intro k hk
    rcases hk with hk | hk
    · exact ne_of_gt (by linarith [hk.1, ha'])
    · exact ne_of_lt (by linarith [hk.2, ha'])
  refine matSymbolCoercive_of_regions Phi rho ha' (min_le_right a b)
    ⟨ε, hε, fun k u hk hu => hnear k u (le_trans hk (min_le_left a b)) hu⟩
    htail (fun i j => (hcont_sym i j).mono hsub) (fun k u hka _ hu => ?_)
  exact hpos_all k u (abs_pos.mp (lt_of_lt_of_le ha' hka)) hu


/-- **Generic pointwise positivity from a Gram factorization.**  The symbol-agnostic core of
`matSymbol_pos_of_factor`: for ANY real symbol matrix `C`, if `∑uᵢ² − ρ∑ᵢⱼCᵢⱼuᵢuⱼ` factors as a
squared norm `∑ₗ |(B·u)ₗ|²` through an invertible complex `B` (`det B ≠ 0`), it is `> 0` on the
L²-unit sphere (`B·u ≠ 0` by invertibility).  Used at both `k ≠ 0` (`C = matRadialSymbol Φ k`, the
middle) and the regularized `k = 0` (`C = Csym 0`, near-`0`). -/
theorem quadForm_pos_of_gram_factor (rho : ℝ) (C : Matrix (Fin N) (Fin N) ℝ)
    (B : Matrix (Fin N) (Fin N) ℂ) (hB : B.det ≠ 0)
    (hfac : ∀ (v : Fin N → ℝ),
      (∑ i, v i ^ 2) - rho * ∑ i, ∑ j, C i j * v i * v j
        = ∑ l, Complex.normSq (B.mulVec (fun i => (v i : ℂ)) l))
    (u : Fin N → ℝ) (hu : (∑ i, u i ^ 2) = 1) :
    0 < (∑ i, u i ^ 2) - rho * ∑ i, ∑ j, C i j * u i * u j := by
  rw [hfac u]
  have hune : (fun i => (u i : ℂ)) ≠ 0 := by
    intro h
    have hz : ∀ i, u i = 0 := fun i => by
      have hc : (u i : ℂ) = 0 := by simpa using congrFun h i
      exact_mod_cast hc
    rw [Finset.sum_eq_zero (fun i _ => by rw [hz i]; ring)] at hu
    exact one_ne_zero hu.symm
  have hBune : B.mulVec (fun i => (u i : ℂ)) ≠ 0 := by
    intro h
    apply hune
    have hd : IsUnit B.det := isUnit_iff_ne_zero.mpr hB
    have hinv : B⁻¹.mulVec (B.mulVec (fun i => (u i : ℂ))) = (fun i => (u i : ℂ)) := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul B hd, Matrix.one_mulVec]
    rw [h, Matrix.mulVec_zero] at hinv
    exact hinv.symm
  obtain ⟨l, hl⟩ := Function.ne_iff.mp hBune
  refine Finset.sum_pos' (fun l _ => Complex.normSq_nonneg _) ⟨l, Finset.mem_univ l, ?_⟩
  exact Complex.normSq_pos.mpr hl

/-- **PD at `k = 0` (`hpd0`) from the regularized Gram factorization + `det ≠ 0`.**  Discharges the
`hpd0` hypothesis of `matSymbol_near_of_continuous_pd` (`matSymbolCoercive_of_regularNear`) with no
eigenvalue-path / connectedness argument.  The Baxter factorization at the regularized `k = 0` is a
real Gram form `1 − ρĈ(0) = B₀B₀ᵀ` (every `AAᵀ` is PSD), and `det B₀ ≠ 0`
(`det_Q0_contour_origin_ne_zero`, the origin compressibility point, no physics axiom) upgrades PSD
to PD.  Concretely: pointwise positivity (`quadForm_pos_of_gram_factor`) + a min over the compact
L²-sphere (`sphere_isCompact.exists_isMinOn`) gives the uniform `ε₀ > 0`.  The near-`0` analog of
`matSymbol_middle_pos` — the SAME `det Q̂₀ ≠ 0` machinery, at the origin. -/
theorem matSymbol_pd_at_zero_of_gram (rho : ℝ) (C : Matrix (Fin N) (Fin N) ℝ)
    (B : Matrix (Fin N) (Fin N) ℂ) (hB : B.det ≠ 0)
    (hfac : ∀ (v : Fin N → ℝ),
      (∑ i, v i ^ 2) - rho * ∑ i, ∑ j, C i j * v i * v j
        = ∑ l, Complex.normSq (B.mulVec (fun i => (v i : ℂ)) l)) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ (u : Fin N → ℝ), (∑ i, u i ^ 2) = 1 →
      ε₀ ≤ (∑ i, u i ^ 2) - rho * ∑ i, ∑ j, C i j * u i * u j := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · refine ⟨1, one_pos, fun u hu => ?_⟩
    subst hN; simp only [Finset.univ_eq_empty, Finset.sum_empty] at hu
    exact (zero_ne_one hu).elim
  set S : Set (Fin N → ℝ) := {u | (∑ i, u i ^ 2) = 1} with hSdef
  set g : (Fin N → ℝ) → ℝ := fun u => (∑ i, u i ^ 2) - rho * ∑ i, ∑ j, C i j * u i * u j with hg
  have hgcont : Continuous g := by fun_prop
  have hSne : S.Nonempty := by
    refine ⟨Pi.single (⟨0, hN⟩ : Fin N) (1 : ℝ), ?_⟩
    simp only [hSdef, Set.mem_setOf_eq]
    rw [Finset.sum_eq_single (⟨0, hN⟩ : Fin N)]
    · simp
    · intro j _ hj; rw [Pi.single_eq_of_ne hj]; ring
    · intro h; exact absurd (Finset.mem_univ _) h
  obtain ⟨u₀, hu₀mem, hu₀min⟩ := sphere_isCompact.exists_isMinOn hSne hgcont.continuousOn
  have hpos : 0 < g u₀ := quadForm_pos_of_gram_factor rho C B hB hfac u₀ hu₀mem
  exact ⟨g u₀, hpos, fun u hu => isMinOn_iff.mp hu₀min u hu⟩

/-- **Full symbol coercivity from Baxter factorization + `det Q̂₀ ≠ 0` alone.**  The complete
corrected value-route assembly: `MatSymbolCoercive` from the Baxter Gram factorizations and their
determinants being nonzero, plus symbol continuity and tail decay — every region reduced to
`det Q̂₀ ≠ 0`.  Near-`0` (`k = 0`): the regularized Gram `B₀` with `det B₀ ≠ 0`
(`det_Q0_contour_origin_ne_zero`) gives `hpd0` via `matSymbol_pd_at_zero_of_gram`.  Middle
(`k ≠ 0`): `Bfun k` with `det ≠ 0` (`mixtureDet_pole_free_N` / no-spinodal) gives positivity via
`quadForm_pos_of_gram_factor`.  Tail: `Ĉ → 0` decay (`htail`).  No pointwise DCF-NSD, no
connectedness — the whole coercivity is one `det Q̂₀ ≠ 0` statement (origin + off-origin) plus
continuity and decay. -/
theorem matSymbolCoercive_of_gramFactors (Phi : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (rho : ℝ)
    (Csym : ℝ → Matrix (Fin N) (Fin N) ℝ) {a₀ b : ℝ} (ha₀ : 0 < a₀) (hb : 0 < b)
    (hagree : ∀ k, k ≠ 0 → ∀ i j, Csym k i j = matRadialSymbol Phi k i j)
    (hcont_near : ∀ i j, ContinuousOn (fun k => Csym k i j) (Set.Icc (-a₀) a₀))
    (hcont_sym : ∀ i j, ContinuousOn (fun k => matRadialSymbol Phi k i j) {k : ℝ | k ≠ 0})
    (B₀ : Matrix (Fin N) (Fin N) ℂ) (hB₀ : B₀.det ≠ 0)
    (hfac0 : ∀ (v : Fin N → ℝ),
      (∑ i, v i ^ 2) - rho * ∑ i, ∑ j, Csym 0 i j * v i * v j
        = ∑ l, Complex.normSq (B₀.mulVec (fun i => (v i : ℂ)) l))
    (Bfun : ℝ → Matrix (Fin N) (Fin N) ℂ) (hBfun : ∀ k, k ≠ 0 → (Bfun k).det ≠ 0)
    (hfack : ∀ k, k ≠ 0 → ∀ (v : Fin N → ℝ),
      (∑ i, v i ^ 2) - rho * ∑ i, ∑ j, matRadialSymbol Phi k i j * v i * v j
        = ∑ l, Complex.normSq ((Bfun k).mulVec (fun i => (v i : ℂ)) l))
    (htail : ∃ δ : ℝ, 0 < δ ∧ ∀ (k : ℝ) (u : Fin N → ℝ), b ≤ |k| → (∑ i, u i ^ 2) = 1 →
      δ ≤ (∑ i, u i ^ 2) - rho * ∑ i, ∑ j, matRadialSymbol Phi k i j * u i * u j) :
    MatSymbolCoercive Phi rho :=
  matSymbolCoercive_of_regularNear Phi rho Csym ha₀ hb hagree hcont_near
    (matSymbol_pd_at_zero_of_gram rho (Csym 0) B₀ hB₀ hfac0) hcont_sym
    (fun k u hk hu =>
      quadForm_pos_of_gram_factor rho (matRadialSymbol Phi k) (Bfun k) (hBfun k hk)
        (hfack k hk) u hu)
    htail

end FMSA.MixtureOzStar
