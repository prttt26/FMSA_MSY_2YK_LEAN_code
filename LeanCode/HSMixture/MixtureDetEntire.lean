/-
Copyright (c) 2026. All rights reserved.
-/
import LeanCode.HSMixture.MixtureDetHomotopyPhys
import LeanCode.HSMixture.MixtureHSCounting

/-!
# `detF` extends to an entire function (`OZFIX.17` matrix — the `s=0` removable singularity)

The density homotopy for `det Q̂₀` pole-freeness must run on an **entire** object with no real-axis
zeros.  The monomial form `W = s⁶·detF` is entire but carries an artificial `z⁶` zero at the origin
(breaking `hreal` at `z=0`).  The right object is `detF` itself: the Lean `detF` is `0/0`-junk at
`s = 0` (the `φ₁,φ₂ = num/sⁿ` closed forms), but it is analytic away from `0`
(`Q0_det_c_differentiableAt`) with a **finite removable limit** there (`detC_tendsto`, from
`q0_entry_c_tendsto`: `φ₁(0)=−σ²/2`, `φ₂(0)=σ³/6`).

`detF_update_differentiable` fills the removable value in with `Function.update` and proves the result
**entire** by Riemann's removable-singularity theorem
(`analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`).  `detF_ext_differentiable`
packages it with the limit from `detF_tendsto`.  This is the entire object the homotopy needs (`hholo`)
— the matrix analog of the scalar track's `1−Q̂` (entire, nonzero at the origin).

Remaining for the full physical-path assembly on `detF_ext`: the origin value
`detF_ext(Pdens t, 0) ≠ 0` (`hreal` at `z=0`; dilute `= 1`), joint continuity `hcont`, and a
uniform-in-`t` escape radius.
-/

open Complex Filter Topology
namespace FMSA.MixtureHSPoles
noncomputable section

/-- **The removable extension of `detF` is entire.**  The Lean `detF` is `0/0`-junk at `s=0` but
analytic away from `0` (`Q0_det_c_differentiableAt`) with a finite removable limit `c`
(`detC_tendsto`); filling in `c` at `0` (`Function.update`) makes it entire (Riemann removable
singularity, `analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`). -/
theorem detF_update_differentiable (P : MixParams) {c : ℂ}
    (hlim : Tendsto P.detF (𝓝[≠] (0 : ℂ)) (𝓝 c)) :
    Differentiable ℂ (Function.update P.detF 0 c) := by
  have hdiff : ∀ z : ℂ, z ≠ 0 → DifferentiableAt ℂ P.detF z := fun z hz =>
    Q0_det_c_differentiableAt (fun i => ((![P.sig0, P.sig1] : Fin 2 → ℝ) i : ℂ))
      (fun i j => (P.rr i j : ℂ)) (fun i j => (P.Qp i j : ℂ)) (fun i j => (P.Qpp i j : ℂ)) hz
  intro z
  by_cases hz : z = 0
  · subst hz
    refine (analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_).differentiableAt
    · filter_upwards [self_mem_nhdsWithin] with w hw
      have hupd : Function.update P.detF 0 c =ᶠ[𝓝 w] P.detF := by
        filter_upwards [isOpen_ne.mem_nhds hw] with x hx
        exact Function.update_of_ne hx c P.detF
      exact (hdiff w hw).congr_of_eventuallyEq hupd
    · have hval : Function.update P.detF 0 c 0 = c := Function.update_self 0 c P.detF
      rw [ContinuousAt, hval, ← nhdsNE_sup_pure, tendsto_sup]
      refine ⟨hlim.congr' ?_, ?_⟩
      · filter_upwards [self_mem_nhdsWithin] with x hx
        exact (Function.update_of_ne hx c P.detF).symm
      · have := tendsto_pure_nhds (Function.update P.detF 0 c) 0
        rwa [hval] at this
  · have hupd : Function.update P.detF 0 c =ᶠ[𝓝 z] P.detF := by
      filter_upwards [isOpen_ne.mem_nhds hz] with x hx
      exact Function.update_of_ne hx c P.detF
    exact (hdiff z hz).congr_of_eventuallyEq hupd

/-- `detF` has a finite removable limit at `s = 0` (for nonzero diameters), from `detC_tendsto`. -/
theorem detF_tendsto (P : MixParams) (hσ0 : (P.sig0 : ℂ) ≠ 0) (hσ1 : (P.sig1 : ℂ) ≠ 0) :
    ∃ c, Tendsto P.detF (𝓝[≠] (0 : ℂ)) (𝓝 c) := by
  refine detC_tendsto ![P.sig0, P.sig1] _ _ _ ?_
  intro i; fin_cases i
  · exact hσ0
  · exact hσ1

/-- **`detF` extends to an entire function** (given nonzero diameters): the removable extension
`Function.update detF 0 (lim)` is entire. -/
theorem detF_ext_differentiable (P : MixParams) (hσ0 : (P.sig0 : ℂ) ≠ 0) (hσ1 : (P.sig1 : ℂ) ≠ 0) :
    ∃ c, Differentiable ℂ (Function.update P.detF 0 c)
      ∧ Tendsto P.detF (𝓝[≠] (0 : ℂ)) (𝓝 c) := by
  obtain ⟨c, hc⟩ := detF_tendsto P hσ0 hσ1
  exact ⟨c, detF_update_differentiable P hc, hc⟩

/-! ### Dilute base of the extension (`hbase`) -/

/-- At zero density the coupling vanishes: `(Pdens σ ρ 0).rr = 0`. -/
theorem Pdens_zero_rr (sigma rho : Fin 2 → ℝ) (i j : Fin 2) : (Pdens sigma rho 0).rr i j = 0 := by
  show FMSA.MatrixQ0.rhoGeoPhys ((0 : ℝ) • rho) i j = 0
  unfold FMSA.MatrixQ0.rhoGeoPhys; simp

/-- `Q0_mat_c` with zero coupling is the identity. -/
theorem Q0_mat_c_rho_geo_zero (s : ℂ) (sigma : Fin 2 → ℂ) (Qp Qpp : Fin 2 → Fin 2 → ℂ) :
    FMSA.Q0Complex.Q0_mat_c s sigma (fun _ _ => 0) Qp Qpp = 1 := by
  funext i j
  simp [FMSA.Q0Complex.Q0_mat_c, FMSA.Q0Complex.q0_entry_c, Matrix.one_apply]

/-- **Dilute base — `detF(Pdens σ ρ 0) ≡ 1`.**  Zero coupling ⇒ `Q̂₀ = I` ⇒ `det = 1`, for every `s`
(no `0/0` issue: `ρ_geo = 0` kills the singular bracket outright). -/
theorem detF_Pdens_zero (sigma rho : Fin 2 → ℝ) (s : ℂ) : (Pdens sigma rho 0).detF s = 1 := by
  have hrr : (fun i j => ((Pdens sigma rho 0).rr i j : ℂ)) = (fun _ _ => (0 : ℂ)) := by
    funext i j; rw [Pdens_zero_rr]; simp
  unfold MixParams.detF detC
  rw [hrr, Q0_mat_c_rho_geo_zero, Matrix.det_one]

/-- The dilute removable limit is `1`. -/
theorem detF_Pdens_zero_tendsto (sigma rho : Fin 2 → ℝ) :
    Tendsto (Pdens sigma rho 0).detF (𝓝[≠] (0 : ℂ)) (𝓝 1) := by
  have : (Pdens sigma rho 0).detF = fun _ => (1 : ℂ) := funext (detF_Pdens_zero sigma rho)
  rw [this]; exact tendsto_const_nhds

/-- **`hbase` for `detF_ext` — the dilute extension is `≡ 1`.**  `Function.update (detF(Pdens 0)) 0 1 ≡ 1`
(constant), hence nonzero everywhere including the origin `z = 0`. -/
theorem detF_ext_Pdens_zero (sigma rho : Fin 2 → ℝ) (z : ℂ) :
    Function.update (Pdens sigma rho 0).detF 0 1 z = 1 := by
  by_cases hz : z = 0
  · rw [hz, Function.update_self]
  · rw [Function.update_of_ne hz, detF_Pdens_zero]

end
end FMSA.MixtureHSPoles
