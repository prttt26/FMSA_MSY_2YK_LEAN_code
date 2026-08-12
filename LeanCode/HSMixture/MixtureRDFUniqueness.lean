/-
Copyright (c) 2026. All rights reserved.
-/
import LeanCode.HSMixture.MixtureOzStar
import LeanCode.Analysis.MatrixIdentity
import LeanCode.Analysis.MatrixRadialWienerHopf

/-!
# Matrix `oz_fixed_pt_unique` — conditional skeleton + the pole-freeness → coercivity bridge (`MML.8`)

Re-evaluation of `MML.8` (mixture inner-core RDF) after the matrix OZ★ (`MixtureOzStar.lean`) and the
all-`N` pole-freeness (`MixtureDetGeneralN.lean`) were completed.  The literal pole-series collapse
`MixRDFInnerCollapse` remains the matrix analog of the still-open, provably-Fourier-**circular**
scalar `CoreSeriesClosure` (`OZFIX.12/14`).  The **non-circular** route — the matrix analog of the
scalar `OZFIX.22` retirement of `oz_core_closure` via OZ★ + `oz_fixed_pt_unique` — is assembled here
up to a single, clearly-scoped Mathlib gap:

* `MatOZHom` — the homogeneous matrix radial OZ★ equation `D = ρ·r·(matRadialConv Φ (D/·))`.
* `matOzStar_sub_hom` — the difference of two `MatOZStar` solutions with the same forcing satisfies
  `MatOZHom` (the `r·Φ` cancels; matrix analog of the scalar `oz_linear_op_sub`).  Axiom-clean, given
  the convolution's additivity on the two solutions (`hlin`, a routine integrability fact).
* `matOzStar_unique_of_injective` — **conditional matrix `oz_fixed_pt_unique`**: two `MatOZStar`
  solutions coincide, given the matrix Wiener–Hopf **injectivity** `hinj` (only the zero function
  solves `MatOZHom`).
* `matStructureFactor_isUnit_of_det_ne_zero` — the **coercivity input** for `hinj`: `det Q̂₀ ≠ 0` (at
  both Wiener–Hopf factors of `T₀ = Q̂₀(k)·Q̂₀(−k)ᵀ`) makes the zeroth-order structure-factor inverse
  `T₀` a unit (`Analysis.MatrixIdentity.det_mul_transpose` + `isUnit_iff_ne_zero`).  The
  nonvanishing is
  exactly what `mixtureDet_pole_free_N` + `pyhs_mixture_no_spinodal` supply.

The gap `hinj` is the matrix analog of the scalar kept axiom `radialShell_bounded_injective`
(`Analysis/RadialWienerHopf.lean`): bounded/`L∞` Wiener–Hopf injectivity given a coercive symbol.
**Committed and abstracted to `Analysis/MatrixRadialWienerHopf.lean`** as the project-independent,
raw-integral `FMSA.matRadialShell_bounded_injective` (one new **math** axiom, ledger `7 → 8` = 7 math
+ 1 physics, homed in `Analysis/` alongside the scalar).  Here it is re-exposed as the THEOREM
`matRadialShell_bounded_injective` (via the definitional bridges `matOZHom_raw`, `matRadialSymbol`),
and `matOzStar_unique` — the **unconditional matrix `oz_fixed_pt_unique`** (value route) — discharges
`hinj` from it, resting only on the coercive symbol (`MatSymbolCoercive`, the multicomponent
no-spinodal, a hypothesis exactly as in the scalar axiom, whose invertibility `det Q̂₀ ≠ 0` is
`matStructureFactor_isUnit_of_det_ne_zero` from `mixtureDet_pole_free_N`) and the solutions'
regularity.  The `L∞` route needs Wiener-algebra resolvent inversion (the `MA.13`-class gap); the
`L²` Plancherel `MA.12` does not reach it.
-/

open scoped Matrix
open MeasureTheory
namespace FMSA.MixtureOzStar
noncomputable section


/-- The **homogeneous** matrix radial OZ★ equation: `D = ρ·r·(matRadialConv Φ (D/·))`.  The
difference of two `MatOZStar` solutions with the same forcing `Φ` satisfies it (the `r·Φ` cancels). -/
def MatOZHom {N : ℕ} (D Phi : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (rho : ℝ) : Prop :=
  ∀ (i j : Fin N) (r : ℝ), 0 < r →
    D i j r = rho * (r * matRadialConv Phi (fun k l => fun x => D k l x / x) r i j)

/-- **Homogeneous difference.**  Two `MatOZStar` solutions `Ψ¹, Ψ²` with the same forcing `Φ` have a
difference `D = Ψ¹ − Ψ²` satisfying the homogeneous equation `MatOZHom D Φ ρ`, given the convolution
is additive on them (`hlin` — a genuine integrability fact for physical solutions).  Matrix analog of
the scalar `oz_linear_op_sub`. -/
theorem matOzStar_sub_hom {N : ℕ} {Psi1 Psi2 Phi : Matrix (Fin N) (Fin N) (ℝ → ℝ)} {rho : ℝ}
    (h1 : MatOZStar Psi1 Phi rho) (h2 : MatOZStar Psi2 Phi rho)
    (hlin : ∀ (i j : Fin N) (r : ℝ), 0 < r →
      matRadialConv Phi (fun k l => fun x => Psi1 k l x / x) r i j
        - matRadialConv Phi (fun k l => fun x => Psi2 k l x / x) r i j
        = matRadialConv Phi (fun k l => fun x => (Psi1 k l x - Psi2 k l x) / x) r i j) :
    MatOZHom (fun i j => fun r => Psi1 i j r - Psi2 i j r) Phi rho := by
  intro i j r hr
  dsimp only
  rw [h1 i j r hr, h2 i j r hr, ← hlin i j r hr]; ring

/-- **Conditional matrix `oz_fixed_pt_unique`.**  Given the matrix Wiener–Hopf **injectivity** on the
relevant function class (`hinj`: the only homogeneous solution is `0` — the matrix analog of the
scalar kept axiom `radialShell_bounded_injective`, whose coercivity is supplied by the structure-factor
invertibility `matStructureFactor_isUnit_of_det_ne_zero`, i.e. `det Q̂₀ ≠ 0` from `mixtureDet_pole_free_N`),
two `MatOZStar` solutions with the same forcing coincide. -/
theorem matOzStar_unique_of_injective {N : ℕ} {Psi1 Psi2 Phi : Matrix (Fin N) (Fin N) (ℝ → ℝ)}
    {rho : ℝ} (h1 : MatOZStar Psi1 Phi rho) (h2 : MatOZStar Psi2 Phi rho)
    (hlin : ∀ (i j : Fin N) (r : ℝ), 0 < r →
      matRadialConv Phi (fun k l => fun x => Psi1 k l x / x) r i j
        - matRadialConv Phi (fun k l => fun x => Psi2 k l x / x) r i j
        = matRadialConv Phi (fun k l => fun x => (Psi1 k l x - Psi2 k l x) / x) r i j)
    (hinj : ∀ D : Matrix (Fin N) (Fin N) (ℝ → ℝ), MatOZHom D Phi rho →
      ∀ (i j : Fin N) (r : ℝ), 0 < r → D i j r = 0) :
    ∀ (i j : Fin N) (r : ℝ), 0 < r → Psi1 i j r = Psi2 i j r := by
  intro i j r hr
  have hD := hinj _ (matOzStar_sub_hom h1 h2 hlin) i j r hr
  linarith [hD]

/-- **Structure-factor invertibility from pole-freeness.**  If `det Q̂₀ ≠ 0` at both `k` and its
reflection (the Wiener–Hopf factors `Qp, Qm` of `T₀ = Qp·Qmᵀ`), then the zeroth-order structure-factor
inverse `T₀` is a unit — the invertibility (coercivity) input the matrix Wiener–Hopf uniqueness needs.
Supplied by `mixtureDet_pole_free_N` (LHP) + `pyhs_mixture_no_spinodal` (real axis). -/
theorem matStructureFactor_isUnit_of_det_ne_zero {N : ℕ} (Qp Qm T0 : Matrix (Fin N) (Fin N) ℂ)
    (hfact : T0 = Qp * Qmᵀ) (hQp : Qp.det ≠ 0) (hQm : Qm.det ≠ 0) : IsUnit T0 := by
  rw [Matrix.isUnit_iff_isUnit_det, hfact, FMSA.MatrixIdentity.det_mul_transpose]
  exact isUnit_iff_ne_zero.mpr (mul_ne_zero hQp hQm)


/-! ## The matrix WH axiom — the value route made unconditional (ledger `7 → 8`) -/


/-- The **matrix radial (sine) symbol** of the forcing `Φ`: `Ĉ(k)ᵢⱼ = (4π/k)∫₀^∞ r·Φᵢⱼ(r)·sin(kr) dr`.
The Fourier symbol of the homogeneous matrix radial OZ operator is `I − ρ·Ĉ(k)` (the structure-factor
inverse `T₀(k)` for the hard-sphere forcing). -/
def matRadialSymbol {N : ℕ} (Phi : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (k : ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun i j => (4 * Real.pi / k) * ∫ r in Set.Ioi (0 : ℝ), r * Phi i j r * Real.sin (k * r)

/-- **Matrix symbol coercivity** — the multicomponent analog of the scalar `1 − ρĈ(k) ≥ ε > 0`: the
Hermitian symbol `I − ρ·Ĉ(k)` is uniformly positive-definite, `vᵀ(I − ρĈ(k))v ≥ ε‖v‖²` for all `k, v`.
For the hard-sphere forcing this is the no-spinodal / positive-definite structure factor `T₀ ⪰ εI`,
whose invertibility is `det Q̂₀ ≠ 0` (`matStructureFactor_isUnit_of_det_ne_zero`, supplied by
`mixtureDet_pole_free_N` + `pyhs_mixture_no_spinodal`). -/
def MatSymbolCoercive {N : ℕ} (Phi : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (rho : ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ (k : ℝ) (v : Fin N → ℝ),
    ε * (∑ i, v i ^ 2) ≤ (∑ i, v i ^ 2)
      - rho * ∑ i, ∑ j, matRadialSymbol Phi k i j * v i * v j

/-- **Bridge — `MatOZHom` unfolds to the raw-integral operator** of the abstract Analysis axiom.
Definitional: `matRadialConv`/`radial3d_conv` are exactly the raw `∑ₖ (2π/r)∫∫`; the `if r ≤ 0` branch
is killed by `r > 0`. -/
theorem matOZHom_raw {N : ℕ} {D Phi : Matrix (Fin N) (Fin N) (ℝ → ℝ)} {rho : ℝ}
    (h : MatOZHom D Phi rho) :
    ∀ (i j : Fin N) (r : ℝ), 0 < r → D i j r =
      rho * (r * ∑ k, (2 * Real.pi / r)
        * ∫ t in Set.Ioi (0 : ℝ), t * Phi i k t
            * ∫ s in Set.Icc |r - t| (r + t), s * (D k j s / s)) := by
  intro i j r hr
  rw [h i j r hr]
  simp only [matRadialConv, FMSA.HardSphere.radial3d_conv, if_neg (not_le.mpr hr)]

/-- **Matrix bounded (`L∞`) Wiener–Hopf injectivity — now a THEOREM.**  Discharged from the abstract,
project-independent, raw-integral axiom `FMSA.matRadialShell_bounded_injective`
(`Analysis/MatrixRadialWienerHopf.lean`, the matrix analog of the scalar kept `MA.15`) via the
definitional bridges `matOZHom_raw` (operator) and `matRadialSymbol` (symbol).  For a coercive matrix
symbol the homogeneous matrix radial OZ★ operator is injective — `MatOZHom D Φ ρ` forces `D ≡ 0`. -/
theorem matRadialShell_bounded_injective {N : ℕ} {Phi : Matrix (Fin N) (Fin N) (ℝ → ℝ)}
    {rho sigma : ℝ} (hsigma : 0 < sigma)
    (hPhisupp : ∀ (i j : Fin N) (t : ℝ), sigma ≤ t → Phi i j t = 0)
    (hcoercive : MatSymbolCoercive Phi rho)
    {D : Matrix (Fin N) (Fin N) (ℝ → ℝ)}
    (hbdd : ∀ i j, ∃ M : ℝ, ∀ r : ℝ, |D i j r| ≤ M)
    (hcont : ∀ i j, ContinuousOn (D i j) (Set.Ici sigma))
    (hcore : ∀ (i j : Fin N) (r : ℝ), r < sigma → D i j r = 0)
    (hhom : MatOZHom D Phi rho) :
    ∀ (i j : Fin N) (r : ℝ), 0 < r → D i j r = 0 := by
  have hco : ∃ ε : ℝ, 0 < ε ∧ ∀ (k : ℝ) (v : Fin N → ℝ),
      ε * (∑ i, v i ^ 2) ≤ (∑ i, v i ^ 2)
        - rho * ∑ i, ∑ j,
            ((4 * Real.pi / k) * ∫ r in Set.Ioi (0 : ℝ), r * Phi i j r * Real.sin (k * r))
              * v i * v j := by
    obtain ⟨ε, hε, h⟩ := hcoercive
    exact ⟨ε, hε, fun k v => by simpa only [matRadialSymbol] using h k v⟩
  have hz := FMSA.matRadialShell_bounded_injective hsigma hPhisupp hco hbdd hcont hcore
    (matOZHom_raw hhom)
  intro i j r _hr
  exact hz i j r

/-- **Matrix `oz_fixed_pt_unique` — UNCONDITIONAL (value route).**  Two `MatOZStar` solutions with the
same forcing `Φ` coincide, given the coercive symbol and the solutions' regularity.  The abstract
injectivity hypothesis of `matOzStar_unique_of_injective` is now discharged by the committed axiom
`matRadialShell_bounded_injective` — the matrix analog of how the scalar `oz_fixed_pt_unique` rests on
`radialShell_bounded_injective`. -/
theorem matOzStar_unique {N : ℕ} {Psi1 Psi2 Phi : Matrix (Fin N) (Fin N) (ℝ → ℝ)} {rho sigma : ℝ}
    (hsigma : 0 < sigma)
    (hPhisupp : ∀ (i j : Fin N) (t : ℝ), sigma ≤ t → Phi i j t = 0)
    (hcoercive : MatSymbolCoercive Phi rho)
    (h1 : MatOZStar Psi1 Phi rho) (h2 : MatOZStar Psi2 Phi rho)
    (hlin : ∀ (i j : Fin N) (r : ℝ), 0 < r →
      matRadialConv Phi (fun k l => fun x => Psi1 k l x / x) r i j
        - matRadialConv Phi (fun k l => fun x => Psi2 k l x / x) r i j
        = matRadialConv Phi (fun k l => fun x => (Psi1 k l x - Psi2 k l x) / x) r i j)
    (hbdd : ∀ i j, ∃ M : ℝ, ∀ r : ℝ, |Psi1 i j r - Psi2 i j r| ≤ M)
    (hcont : ∀ i j, ContinuousOn (fun r => Psi1 i j r - Psi2 i j r) (Set.Ici sigma))
    (hcore : ∀ (i j : Fin N) (r : ℝ), r < sigma → Psi1 i j r - Psi2 i j r = 0) :
    ∀ (i j : Fin N) (r : ℝ), 0 < r → Psi1 i j r = Psi2 i j r := by
  have hD := matRadialShell_bounded_injective hsigma hPhisupp hcoercive
    (D := fun i j => fun r => Psi1 i j r - Psi2 i j r) hbdd hcont hcore
    (matOzStar_sub_hom h1 h2 hlin)
  intro i j r hr
  have hz := hD i j r hr
  linarith [hz]
/-! ## The non-circular value route to MML.8 — end-to-end status

This route discharges the mixture RDF identity (MML.8) WITHOUT the seed and WITHOUT any pole
enumeration, via **uniqueness of the matrix OZ★ fixed point** — the matrix analog of the scalar
`OZFIX.22` retirement of `oz_core_closure`.

**Assembled (unconditional given the symbol).**  `matOzStar_unique` — two `MatOZStar` solutions with
the same DCF forcing `Φ` coincide, given the coercive symbol `MatSymbolCoercive Φ ρ` and the
solutions' routine regularity.  It rests ONLY on the committed matrix Wiener–Hopf axiom
`matRadialShell_bounded_injective` (= MA.15, the multicomponent analog of the scalar kept
`radialShell_bounded_injective`; the unformalized Wiener tauberian `L∞` bound).

**Equal diameters — FULLY CLOSED.**  `matOzStar_equalDiam_unique` (`MixtureRDFEqualDiam.lean`): the
equal-diameter mixture RDF is EXACTLY the density-weighted single-component `baxterPsi`.  Existence
is the constructed `matOzStar_equalDiam_phys`; the coercive symbol is `matSymbolCoercive_equalDiam`
— the rank-1 reduction `Φᵢⱼ = uᵢuⱼ·c_HS` (`uᵢ = √ρᵢ/√ρ`, `∑ uᵢ² = 1`) of the matrix coercivity to
the PROVED scalar `one_sub_rho_radial_fourier_c_HS_coercive`.  No physics beyond `pyhs_no_spinodal`.

**General N / unequal diameters — ONE analytic input remaining.**  The sole missing piece is
`MatSymbolCoercive Φ ρ` for the general mixture DCF: the UNIFORM positive-definiteness of the
structure factor, `I − ρ·Ĉ(k) ⪰ εI` with a single `ε > 0`.  Its POINTWISE part is already
`det Q̂₀ ≠ 0`: the Baxter factorization `Cmix0_factorization` gives `I − ρĈ = T₀ = Q̂₀(k)·Q̂₀(−k)ᵀ`,
and `matStructureFactor_isUnit_of_det_ne_zero` turns `det Q̂₀ ≠ 0` — supplied unconditionally for
every `N` by `mixtureDet_pole_free_N` (LHP) + `pyhs_mixture_no_spinodal` (real axis) — into `T₀(k)`
invertible for each `k`.  The uniform `ε` GLUING is now DISCHARGED: `matSymbolCoercive_of_regions`
(`MixtureCoercivityReduction.lean`) proves the `k`-compactness argument abstractly (middle
compact-min via `IsCompact.exists_isMinOn` + `matSymbolCoercive_of_sphere` homogeneity), reducing
`MatSymbolCoercive` to the three CONCRETE symbol facts — near-`0` sign, middle continuity + pointwise
`det Q̂₀ ≠ 0` positivity, tail `Ĉ → 0` decay — the matrix analogs of the scalar proof's three regions.

**Independence + net.**  This route uses NO seed, NO Wertheim–Thiele identity, NO pole-exhaustion.
So MML.8 has two complementary routes — the real-space **seed** route (`MixtureCorrectedSeed.lean`,
fully explicit; WT terminus proved equal-diameter and numerically confirmed unequal) and this
**value** route (uniqueness; fully closed equal-diameter, reduced to one uniform-coercivity input
general-N) — and the literal pole-series route is provably BLOCKED (`even_subfamily_not_exhaustive`,
`MixturePoleExhaustion.lean`).  The value route's only axioms are MA.15 (Wiener tauberian) and the
physics no-spinodal — the same footing as the scalar `oz_fixed_pt_unique`. -/

end
end FMSA.MixtureOzStar
