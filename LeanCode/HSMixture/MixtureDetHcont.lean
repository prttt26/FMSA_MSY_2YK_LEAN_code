/-
Copyright (c) 2026. All rights reserved.
-/
import LeanCode.HSMixture.MixtureDetOrigin
import LeanCode.HSMixture.MixtureDetUniform
import LeanCode.Analysis.ExpTaylorLimits

/-!
# `hcont` and the UNCONDITIONAL matrix pole-freeness theorem (`OZFIX.17`, N=2)

The last family-regularity input `hcont` — joint continuity of `(t,z) ↦ detF_ext(Pdens t)(I·z)` — is
discharged here, completing the fully unconditional `mixtureDet_pole_free`.

The `0/0`-junk of the Lean `detF` at `s = 0` comes solely from the `φ₁,φ₂ = num/sⁿ` Baxter kernels,
which depend on `s` and the (fixed) diameter `σ` — **not** on the homotopy parameter `t`.  Replacing
them with their continuous removable extensions `psi1`, `psi2` (`psi{1,2}_continuous`, via
`phi{1,2}_tendsto`) gives the `ψ`-form determinant `detFpsi`, which is **manifestly jointly continuous**
(`detFpsi_continuous`; fields of `Pdens t` continuous in `t`, `ψ` continuous in `s`) and equals `detF`
away from `0` (`detFpsi_eq_detF`).  Since `cf t = detFpsi (Pdens t) 0` (`cf_eq_detFpsi_zero`, the
removable limit is the continuous value), the update-based `detF_ext` equals `detFpsi`, so `hcont`
follows by `ContinuousOn.congr` (`hcont_Pdens`).

`mixtureDet_pole_free` : `det Q̂₀(I·z) ≠ 0` on the open lower half `z`-plane for every physical `N=2`
hard-sphere mixture — **unconditional**, depending only on the two existing axioms
`zeroFree_lowerHalfPlane_of_homotopy` (math) and `pyhs_mixture_no_spinodal` (physics).
-/

set_option linter.style.longLine false

open Filter Topology Complex
namespace FMSA.MixtureHSPoles
noncomputable section


/-- Continuous removable extension of the Baxter `φ₁` kernel `(1−sσ−e^{−sσ})/s²`. -/
def psi1 (sigma : ℂ) (s : ℂ) : ℂ :=
  Function.update (fun s => (1 - s * sigma - Complex.exp (-(s * sigma))) / s ^ 2) 0 (-sigma ^ 2 / 2) s

theorem psi1_continuous {sigma : ℂ} (hsigma : sigma ≠ 0) : Continuous (psi1 sigma) := by
  rw [continuous_iff_continuousAt]
  intro s
  by_cases hs : s = 0
  · subst hs
    have hd : ∀ᶠ z in 𝓝[≠] (0:ℂ),
        DifferentiableAt ℂ (fun s => (1 - s * sigma - Complex.exp (-(s * sigma))) / s ^ 2) z := by
      filter_upwards [self_mem_nhdsWithin] with w hw
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hw
      apply DifferentiableAt.div (by fun_prop) (by fun_prop)
      exact pow_ne_zero 2 hw
    have hc : ContinuousAt (psi1 sigma) 0 := by
      unfold psi1
      rw [ContinuousAt, Function.update_self, ← nhdsNE_sup_pure, tendsto_sup]
      refine ⟨?_, ?_⟩
      · refine Filter.Tendsto.congr' ?_ (FMSA.ExpTaylorLimits.phi1_tendsto sigma hsigma)
        filter_upwards [self_mem_nhdsWithin] with w hw
        rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hw
        rw [Function.update_of_ne hw]
      · have := tendsto_pure_nhds (Function.update
          (fun s => (1 - s * sigma - Complex.exp (-(s * sigma))) / s ^ 2) 0 (-sigma ^ 2 / 2)) 0
        rwa [Function.update_self] at this
    exact hc
  · unfold psi1
    have : Function.update (fun s => (1 - s * sigma - Complex.exp (-(s * sigma))) / s ^ 2) 0 (-sigma ^ 2 / 2)
        =ᶠ[𝓝 s] (fun s => (1 - s * sigma - Complex.exp (-(s * sigma))) / s ^ 2) := by
      filter_upwards [isOpen_ne.mem_nhds hs] with x hx
      exact Function.update_of_ne hx _ _
    refine ContinuousAt.congr ?_ this.symm
    exact (ContinuousAt.div (by fun_prop) (by fun_prop) (pow_ne_zero 2 hs))

/-- Continuous removable extension of the Baxter `φ₂` kernel. -/
def psi2 (sigma : ℂ) (s : ℂ) : ℂ :=
  Function.update (fun s => (1 - s * sigma + (s * sigma) ^ 2 / 2 - Complex.exp (-(s * sigma))) / s ^ 3) 0
    (sigma ^ 3 / 6) s

theorem psi2_continuous {sigma : ℂ} (hsigma : sigma ≠ 0) : Continuous (psi2 sigma) := by
  rw [continuous_iff_continuousAt]
  intro s
  by_cases hs : s = 0
  · subst hs
    have hc : ContinuousAt (psi2 sigma) 0 := by
      unfold psi2
      rw [ContinuousAt, Function.update_self, ← nhdsNE_sup_pure, tendsto_sup]
      refine ⟨?_, ?_⟩
      · refine Filter.Tendsto.congr' ?_ (FMSA.ExpTaylorLimits.phi2_tendsto sigma hsigma)
        filter_upwards [self_mem_nhdsWithin] with w hw
        rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hw
        rw [Function.update_of_ne hw]
      · have := tendsto_pure_nhds (Function.update
          (fun s => (1 - s * sigma + (s * sigma) ^ 2 / 2 - Complex.exp (-(s * sigma))) / s ^ 3) 0 (sigma ^ 3 / 6)) 0
        rwa [Function.update_self] at this
    exact hc
  · unfold psi2
    have heq : Function.update
        (fun s => (1 - s * sigma + (s * sigma) ^ 2 / 2 - Complex.exp (-(s * sigma))) / s ^ 3) 0 (sigma ^ 3 / 6)
        =ᶠ[𝓝 s] (fun s => (1 - s * sigma + (s * sigma) ^ 2 / 2 - Complex.exp (-(s * sigma))) / s ^ 3) := by
      filter_upwards [isOpen_ne.mem_nhds hs] with x hx
      exact Function.update_of_ne hx _ _
    refine ContinuousAt.congr ?_ heq.symm
    exact ContinuousAt.div (by fun_prop) (by fun_prop) (pow_ne_zero 3 hs)

/-- The `φ`-kernels agree with `ψ` away from `0`: `q0_entry_c` equals its `ψ`-form for `s ≠ 0`. -/
theorem q0_entry_c_eq_psi {s sigma lam Qp Qpp rho delta : ℂ} (hs : s ≠ 0) :
    FMSA.Q0Complex.q0_entry_c s sigma lam Qp Qpp rho delta
      = delta - rho * Complex.exp (-(lam * s)) * (Qp * psi1 sigma s + Qpp * psi2 sigma s) := by
  unfold FMSA.Q0Complex.q0_entry_c psi1 psi2
  rw [Function.update_of_ne hs, Function.update_of_ne hs]

/-- The `ψ`-form Baxter entry — jointly continuous (no `0/0` at `s=0`). -/
def q0_entry_psi (sigma lam Qp Qpp rho delta : ℂ) (s : ℂ) : ℂ :=
  delta - rho * Complex.exp (-(lam * s)) * (Qp * psi1 sigma s + Qpp * psi2 sigma s)

theorem q0_entry_psi_continuous {sigma lam Qp Qpp rho delta : ℂ} (hsigma : sigma ≠ 0) :
    Continuous (fun s => q0_entry_psi sigma lam Qp Qpp rho delta s) := by
  unfold q0_entry_psi
  have h1 := psi1_continuous hsigma
  have h2 := psi2_continuous hsigma
  fun_prop

/-- The `ψ`-form determinant (`N=2`): jointly continuous, equal to `detF` away from `0`. -/
def detFpsi (P : MixParams) (s : ℂ) : ℂ :=
  q0_entry_psi (P.sig0 : ℂ) 0 (P.Qp 0 0) (P.Qpp 0 0) (P.rr 0 0) 1 s
      * q0_entry_psi (P.sig1 : ℂ) 0 (P.Qp 1 1) (P.Qpp 1 1) (P.rr 1 1) 1 s
    - q0_entry_psi (P.sig0 : ℂ) (((P.sig1 : ℂ) - (P.sig0 : ℂ)) / 2) (P.Qp 0 1) (P.Qpp 0 1) (P.rr 0 1) 0 s
      * q0_entry_psi (P.sig1 : ℂ) (((P.sig0 : ℂ) - (P.sig1 : ℂ)) / 2) (P.Qp 1 0) (P.Qpp 1 0) (P.rr 1 0) 0 s

theorem detFpsi_eq_detF (P : MixParams) {s : ℂ} (hs : s ≠ 0) : detFpsi P s = P.detF s := by
  unfold detFpsi MixParams.detF detC
  rw [Matrix.det_fin_two]
  simp only [FMSA.Q0Complex.Q0_mat_c, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [q0_entry_c_eq_psi hs, q0_entry_c_eq_psi hs, q0_entry_c_eq_psi hs, q0_entry_c_eq_psi hs]
  norm_num [q0_entry_psi]

theorem detFpsi_continuous {P : MixParams} (hsigma0 : (P.sig0 : ℂ) ≠ 0) (hsigma1 : (P.sig1 : ℂ) ≠ 0) :
    Continuous (fun s => detFpsi P s) := by
  unfold detFpsi
  have c00 := q0_entry_psi_continuous (sigma := (P.sig0:ℂ)) (lam := 0) (Qp := P.Qp 0 0)
    (Qpp := P.Qpp 0 0) (rho := P.rr 0 0) (delta := 1) hsigma0
  have c11 := q0_entry_psi_continuous (sigma := (P.sig1:ℂ)) (lam := 0) (Qp := P.Qp 1 1)
    (Qpp := P.Qpp 1 1) (rho := P.rr 1 1) (delta := 1) hsigma1
  have c01 := q0_entry_psi_continuous (sigma := (P.sig0:ℂ)) (lam := ((P.sig1:ℂ)-(P.sig0:ℂ))/2)
    (Qp := P.Qp 0 1) (Qpp := P.Qpp 0 1) (rho := P.rr 0 1) (delta := 0) hsigma0
  have c10 := q0_entry_psi_continuous (sigma := (P.sig1:ℂ)) (lam := ((P.sig0:ℂ)-(P.sig1:ℂ))/2)
    (Qp := P.Qp 1 0) (Qpp := P.Qpp 1 0) (rho := P.rr 1 0) (delta := 0) hsigma1
  fun_prop

/-- `cf t = detFpsi (Pₜ) 0` — the removable limit equals the continuous `ψ`-value at the origin. -/
theorem cf_eq_detFpsi_zero {P : MixParams} (hsigma0 : (P.sig0 : ℂ) ≠ 0) (hsigma1 : (P.sig1 : ℂ) ≠ 0)
    {c : ℂ} (hc : Tendsto P.detF (𝓝[≠] (0:ℂ)) (𝓝 c)) : c = detFpsi P 0 := by
  have htp : Tendsto (fun s => detFpsi P s) (𝓝[≠] (0:ℂ)) (𝓝 (detFpsi P 0)) :=
    ((detFpsi_continuous hsigma0 hsigma1).continuousAt (x := 0)).mono_left nhdsWithin_le_nhds
  have heq : Tendsto P.detF (𝓝[≠] (0:ℂ)) (𝓝 (detFpsi P 0)) := by
    refine Filter.Tendsto.congr' ?_ htp
    filter_upwards [self_mem_nhdsWithin] with w hw
    rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hw
    exact detFpsi_eq_detF P hw
  exact tendsto_nhds_unique hc heq

open Set in
/-- **`hcont` — joint continuity of the density homotopy on the entire extension.**  The theorem's
family `(t,z) ↦ detF_ext(Pdens t)(I·z)` equals the `ψ`-form `detFpsi (Pdens t) (I·z)` (which has no
`0/0` and is manifestly jointly continuous), so it is `ContinuousOn (Icc 0 1 ×ˢ univ)`. -/
theorem hcont_Pdens {sigma rho : Fin 2 → ℝ} (hsig : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 < rho i)
    (heta : FMSA.MatrixQ0.etaMix rho sigma < 1) (cf : ℝ → ℂ)
    (hcf : ∀ t ∈ Icc (0:ℝ) 1, Tendsto (Pdens sigma rho t).detF (𝓝[≠] (0:ℂ)) (𝓝 (cf t))) :
    ContinuousOn (fun p : ℝ × ℂ =>
        Function.update (Pdens sigma rho p.1).detF 0 (cf p.1) (Complex.I * p.2))
      (Icc 0 1 ×ˢ (univ : Set ℂ)) := by
  have hsigma0 : ((Pdens sigma rho 0).sig0 : ℂ) ≠ 0 := by
    simp only [Pdens]; exact_mod_cast (hsig 0).ne'
  -- the ψ-form is jointly continuous
  have hmaps : MapsTo (Prod.fst : ℝ × ℂ → ℝ) (Icc (0:ℝ) 1 ×ˢ univ) (Icc 0 1) := fun p hp => hp.1
  have hjoint : ContinuousOn (fun p : ℝ × ℂ => detFpsi (Pdens sigma rho p.1) (Complex.I * p.2))
      (Icc 0 1 ×ˢ (univ : Set ℂ)) := by
    have L : ∀ (f : ℝ → ℝ), ContinuousOn f (Icc 0 1) →
        ContinuousOn (fun p : ℝ × ℂ => ((f p.1 : ℝ) : ℂ)) (Icc 0 1 ×ˢ (univ : Set ℂ)) :=
      fun f hf => (Complex.continuous_ofReal.comp_continuousOn (hf.comp continuousOn_fst hmaps))
    have q00 := L _ (Q0phys_cont hsig hrho heta 0 0)
    have q11 := L _ (Q0phys_cont hsig hrho heta 1 1)
    have q01 := L _ (Q0phys_cont hsig hrho heta 0 1)
    have q10 := L _ (Q0phys_cont hsig hrho heta 1 0)
    have p00 := L _ (Qppphys_cont hsig hrho heta 0 0)
    have p11 := L _ (Qppphys_cont hsig hrho heta 1 1)
    have p01 := L _ (Qppphys_cont hsig hrho heta 0 1)
    have p10 := L _ (Qppphys_cont hsig hrho heta 1 0)
    have g00 := L _ (rhoGeoPhys_cont (rho := rho) 0 0)
    have g11 := L _ (rhoGeoPhys_cont (rho := rho) 1 1)
    have g01 := L _ (rhoGeoPhys_cont (rho := rho) 0 1)
    have g10 := L _ (rhoGeoPhys_cont (rho := rho) 1 0)
    have hps1a : Continuous (fun z : ℂ => psi1 ((sigma 0 : ℝ) : ℂ) z) :=
      psi1_continuous (by exact_mod_cast (hsig 0).ne')
    have hps1b : Continuous (fun z : ℂ => psi1 ((sigma 1 : ℝ) : ℂ) z) :=
      psi1_continuous (by exact_mod_cast (hsig 1).ne')
    have hps2a : Continuous (fun z : ℂ => psi2 ((sigma 0 : ℝ) : ℂ) z) :=
      psi2_continuous (by exact_mod_cast (hsig 0).ne')
    have hps2b : Continuous (fun z : ℂ => psi2 ((sigma 1 : ℝ) : ℂ) z) :=
      psi2_continuous (by exact_mod_cast (hsig 1).ne')
    simp only [detFpsi, q0_entry_psi, Pdens]
    fun_prop
  refine ContinuousOn.congr hjoint (fun p hp => ?_)
  by_cases hz : p.2 = 0
  · rw [hz, mul_zero, Function.update_self]
    exact cf_eq_detFpsi_zero (by simp only [Pdens]; exact_mod_cast (hsig 0).ne')
      (by simp only [Pdens]; exact_mod_cast (hsig 1).ne') (hcf p.1 hp.1)
  · have hIz : Complex.I * p.2 ≠ 0 := mul_ne_zero Complex.I_ne_zero hz
    rw [Function.update_of_ne hIz, detFpsi_eq_detF _ hIz]

/-- **Matrix pole-freeness for the physical mixture — UNCONDITIONAL.**  `det Q̂₀(I·z) ≠ 0` throughout
the open lower half `z`-plane, for every physical `N=2` hard-sphere mixture.  All family-regularity
inputs (`hcont`, `hRunif`, `cf`) are now discharged; depends only on the two existing axioms
`zeroFree_lowerHalfPlane_of_homotopy` (math) and `pyhs_mixture_no_spinodal` (physics). -/
theorem mixtureDet_pole_free {sigma rho : Fin 2 → ℝ} (hsig : ∀ i, 0 < sigma i)
    (hsord : sigma 0 < sigma 1) (hrho : ∀ i, 0 < rho i)
    (heta : FMSA.MatrixQ0.etaMix rho sigma < 1) {z : ℂ} (hz : z.im < 0) :
    (Pdens sigma rho 1).detF (Complex.I * z) ≠ 0 := by
  have hsigma0 : ∀ t : ℝ, ((Pdens sigma rho t).sig0 : ℂ) ≠ 0 :=
    fun t => by simp only [Pdens]; exact_mod_cast (hsig 0).ne'
  have hsigma1 : ∀ t : ℝ, ((Pdens sigma rho t).sig1 : ℂ) ≠ 0 :=
    fun t => by simp only [Pdens]; exact_mod_cast (hsig 1).ne'
  set cf : ℝ → ℂ := fun t => Classical.choose (detF_tendsto (Pdens sigma rho t) (hsigma0 t) (hsigma1 t))
    with hcfdef
  have hcf : ∀ t ∈ Set.Icc (0:ℝ) 1, Tendsto (Pdens sigma rho t).detF (𝓝[≠] (0:ℂ)) (𝓝 (cf t)) :=
    fun t _ => Classical.choose_spec (detF_tendsto (Pdens sigma rho t) (hsigma0 t) (hsigma1 t))
  obtain ⟨R, hR1, hRunif⟩ := hRunif_Pdens hsig hsord hrho heta
  exact mixtureDet_pole_free_of_regular hsig hrho heta cf hcf
    (hcont_Pdens hsig hrho heta cf hcf) hR1 hRunif hz

/-- `psi1 σ` is **entire** (removable singularity filled): differentiable away from `0`, continuous
at `0` (`psi1_continuous`), so entire by Riemann's removable-singularity theorem. -/
theorem psi1_entire {sigma : ℂ} (hsigma : sigma ≠ 0) : Differentiable ℂ (psi1 sigma) := by
  intro z
  by_cases hz : z = 0
  · subst hz
    refine (analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_).differentiableAt
    · filter_upwards [self_mem_nhdsWithin] with w hw
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hw
      have : psi1 sigma =ᶠ[𝓝 w] (fun s => (1 - s * sigma - Complex.exp (-(s * sigma))) / s ^ 2) := by
        filter_upwards [isOpen_ne.mem_nhds hw] with x hx
        exact Function.update_of_ne hx _ _
      exact (((by fun_prop : DifferentiableAt ℂ (fun s : ℂ => 1 - s * sigma - Complex.exp (-(s * sigma))) w)).div
        (by fun_prop : DifferentiableAt ℂ (fun s : ℂ => s ^ 2) w) (pow_ne_zero 2 hw)).congr_of_eventuallyEq this
    · exact (psi1_continuous hsigma).continuousAt
  · have : psi1 sigma =ᶠ[𝓝 z] (fun s => (1 - s * sigma - Complex.exp (-(s * sigma))) / s ^ 2) := by
      filter_upwards [isOpen_ne.mem_nhds hz] with x hx
      exact Function.update_of_ne hx _ _
    exact (((by fun_prop : DifferentiableAt ℂ (fun s : ℂ => 1 - s * sigma - Complex.exp (-(s * sigma))) z)).div
      (by fun_prop : DifferentiableAt ℂ (fun s : ℂ => s ^ 2) z) (pow_ne_zero 2 hz)).congr_of_eventuallyEq this

theorem psi2_entire {sigma : ℂ} (hsigma : sigma ≠ 0) : Differentiable ℂ (psi2 sigma) := by
  intro z
  by_cases hz : z = 0
  · subst hz
    refine (analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_).differentiableAt
    · filter_upwards [self_mem_nhdsWithin] with w hw
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hw
      have : psi2 sigma =ᶠ[𝓝 w]
          (fun s => (1 - s * sigma + (s * sigma) ^ 2 / 2 - Complex.exp (-(s * sigma))) / s ^ 3) := by
        filter_upwards [isOpen_ne.mem_nhds hw] with x hx
        exact Function.update_of_ne hx _ _
      exact (((by fun_prop : DifferentiableAt ℂ (fun s : ℂ => 1 - s * sigma + (s * sigma) ^ 2 / 2 - Complex.exp (-(s * sigma))) w)).div
        (by fun_prop : DifferentiableAt ℂ (fun s : ℂ => s ^ 3) w) (pow_ne_zero 3 hw)).congr_of_eventuallyEq this
    · exact (psi2_continuous hsigma).continuousAt
  · have : psi2 sigma =ᶠ[𝓝 z]
        (fun s => (1 - s * sigma + (s * sigma) ^ 2 / 2 - Complex.exp (-(s * sigma))) / s ^ 3) := by
      filter_upwards [isOpen_ne.mem_nhds hz] with x hx
      exact Function.update_of_ne hx _ _
    exact (((by fun_prop : DifferentiableAt ℂ (fun s : ℂ => 1 - s * sigma + (s * sigma) ^ 2 / 2 - Complex.exp (-(s * sigma))) z)).div
      (by fun_prop : DifferentiableAt ℂ (fun s : ℂ => s ^ 3) z) (pow_ne_zero 3 hz)).congr_of_eventuallyEq this

end
end FMSA.MixtureHSPoles
