/-
Copyright (c) 2026. All rights reserved.
-/
import LeanCode.HSMixture.MixtureDetOrigin

/-!
# Uniform-in-`t` escape radius for the density homotopy (`hRunif`, `OFIX.17`)

The concrete pole-freeness theorem `mixtureDet_pole_free_of_regular` (`MixtureDetOrigin.lean`) is
conditional on `hRunif` — a single escape radius `R` valid for every `Pdens σ ρ t`, `t ∈ [0,1]`.  This
file discharges it.  The five envelope constants `K_Mc, K₀, μ, K₁, K₀₁` of `Pdens t` are **continuous
in `t`** on `[0,1]` (built from `Q0phys`/`Qppphys` = `…/vac`, `rhoGeoPhys`, `cB`, with `vac(t) =
1 − t·η(ρ) > 0` there), hence their sum is **bounded** on the compact `[0,1]`; `detF_ne_zero_of_Kbound`
then gives a uniform `R = max(1, 5B+1)`.  `Pdens_Phys` (physicality of `Pdens t` for `t > 0`) supplies
the `Phys` hypotheses.  Axiom-clean — pure `ContinuousOn`/compactness plumbing.
-/

open Filter Topology Set
namespace FMSA.MixtureHSPoles
open FMSA.MatrixQ0
noncomputable section


theorem vac_pos_on {sigma rho : Fin 2 → ℝ} (hsig : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 < rho i)
    (heta : etaMix rho sigma < 1) : ∀ t ∈ Icc (0:ℝ) 1, 0 < vacMix (t • rho) sigma := by
  intro t ht
  unfold vacMix
  rw [show etaMix (t • rho) sigma = t * etaMix rho sigma from etaMix_smul t rho sigma]
  nlinarith [etaMix_nonneg hsig hrho, heta, ht.1, ht.2]

theorem vacMix_cont {sigma rho : Fin 2 → ℝ} :
    ContinuousOn (fun t : ℝ => vacMix (t • rho) sigma) (Icc 0 1) := by
  unfold vacMix etaMix; fun_prop
theorem xi2_cont {sigma rho : Fin 2 → ℝ} :
    ContinuousOn (fun t : ℝ => xi2 (t • rho) sigma) (Icc 0 1) := by
  unfold xi2; fun_prop

theorem Q0phys_cont {sigma rho : Fin 2 → ℝ} (hsig : ∀ i, 0 < sigma i)
    (hrho : ∀ i, 0 < rho i) (heta : etaMix rho sigma < 1) (i j : Fin 2) :
    ContinuousOn (fun t : ℝ => Q0phys (t • rho) sigma i j) (Icc 0 1) := by
  have hv := vac_pos_on hsig hrho heta
  unfold Q0phys
  refine ContinuousOn.mul (continuousOn_const.div vacMix_cont (fun t ht => (hv t ht).ne'))
    (continuousOn_const.add (ContinuousOn.div ?_ ?_ ?_))
  · exact (continuousOn_const.mul xi2_cont).mul continuousOn_const |>.mul continuousOn_const
  · exact continuousOn_const.mul vacMix_cont
  · exact fun t ht => mul_ne_zero (by norm_num) (hv t ht).ne'

theorem Qppphys_cont {sigma rho : Fin 2 → ℝ} (hsig : ∀ i, 0 < sigma i)
    (hrho : ∀ i, 0 < rho i) (heta : etaMix rho sigma < 1) (i j : Fin 2) :
    ContinuousOn (fun t : ℝ => Qppphys (t • rho) sigma i j) (Icc 0 1) := by
  have hv := vac_pos_on hsig hrho heta
  unfold Qppphys
  refine ContinuousOn.mul (continuousOn_const.div vacMix_cont (fun t ht => (hv t ht).ne'))
    (continuousOn_const.add (ContinuousOn.div ?_ ?_ ?_))
  · exact (continuousOn_const.mul xi2_cont).mul continuousOn_const
  · exact continuousOn_const.mul vacMix_cont
  · exact fun t ht => mul_ne_zero (by norm_num) (hv t ht).ne'

theorem rhoGeoPhys_cont {rho : Fin 2 → ℝ} (i j : Fin 2) :
    ContinuousOn (fun t : ℝ => rhoGeoPhys (t • rho) i j) (Icc 0 1) := by
  unfold rhoGeoPhys; fun_prop

theorem Pdens_rr_cont {sigma rho : Fin 2 → ℝ} (i j : Fin 2) :
    ContinuousOn (fun t : ℝ => (Pdens sigma rho t).rr i j) (Icc 0 1) := rhoGeoPhys_cont i j
theorem Pdens_Qp_cont {sigma rho : Fin 2 → ℝ} (hsig : ∀ i, 0 < sigma i)
    (hrho : ∀ i, 0 < rho i) (heta : etaMix rho sigma < 1) (i j : Fin 2) :
    ContinuousOn (fun t : ℝ => (Pdens sigma rho t).Qp i j) (Icc 0 1) := Q0phys_cont hsig hrho heta i j
theorem Pdens_Qpp_cont {sigma rho : Fin 2 → ℝ} (hsig : ∀ i, 0 < sigma i)
    (hrho : ∀ i, 0 < rho i) (heta : etaMix rho sigma < 1) (i j : Fin 2) :
    ContinuousOn (fun t : ℝ => (Pdens sigma rho t).Qpp i j) (Icc 0 1) := Qppphys_cont hsig hrho heta i j

/-- The sum of the five envelope constants of `Pdens t` is continuous on `[0,1]`. -/
theorem Ksum_cont {sigma rho : Fin 2 → ℝ} (hsig : ∀ i, 0 < sigma i)
    (hrho : ∀ i, 0 < rho i) (heta : etaMix rho sigma < 1) :
    ContinuousOn (fun t : ℝ => (Pdens sigma rho t).KMc + (Pdens sigma rho t).K0
      + (Pdens sigma rho t).mu + (Pdens sigma rho t).K1 + (Pdens sigma rho t).K01) (Icc 0 1) := by
  have g00 := rhoGeoPhys_cont (rho:=rho) 0 0
  have g11 := rhoGeoPhys_cont (rho:=rho) 1 1
  have g01 := rhoGeoPhys_cont (rho:=rho) 0 1
  have g10 := rhoGeoPhys_cont (rho:=rho) 1 0
  have p00 := Q0phys_cont hsig hrho heta 0 0
  have p11 := Q0phys_cont hsig hrho heta 1 1
  have p01 := Q0phys_cont hsig hrho heta 0 1
  have p10 := Q0phys_cont hsig hrho heta 1 0
  have q00 := Qppphys_cont hsig hrho heta 0 0
  have q11 := Qppphys_cont hsig hrho heta 1 1
  have q01 := Qppphys_cont hsig hrho heta 0 1
  have q10 := Qppphys_cont hsig hrho heta 1 0
  simp only [MixParams.KMc, MixParams.K0, MixParams.mu, MixParams.K1, MixParams.K01, cB, Pdens]
  fun_prop

theorem rhoGeoPhys_pos {rho : Fin 2 → ℝ} (hrho : ∀ i, 0 < rho i) {t : ℝ} (ht0 : 0 < t) (i j : Fin 2) :
    0 < rhoGeoPhys (t • rho) i j := by
  unfold rhoGeoPhys
  apply Real.sqrt_pos.mpr
  simp only [Pi.smul_apply, smul_eq_mul]
  exact mul_pos (mul_pos ht0 (hrho i)) (mul_pos ht0 (hrho j))

theorem Q0phys_pos {sigma rho : Fin 2 → ℝ} (hsig : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 < rho i)
    (heta : etaMix rho sigma < 1) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (i j : Fin 2) :
    0 < Q0phys (t • rho) sigma i j := by
  have hv := vac_pos_on hsig hrho heta t ht
  have hsi := hsig i; have hsj := hsig j
  unfold Q0phys
  have hxi : 0 ≤ xi2 (t • rho) sigma := by
    unfold xi2; apply Finset.sum_nonneg; intro k _
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg (mul_nonneg ht.1 (hrho k).le) (sq_nonneg _)
  refine mul_pos (div_pos (by positivity) hv) ?_
  have h1 : 0 < (sigma i + sigma j) / 2 := by positivity
  have h2 : 0 ≤ Real.pi * xi2 (t • rho) sigma * sigma i * sigma j / (4 * vacMix (t • rho) sigma) :=
    div_nonneg (by positivity) (by positivity)
  linarith

theorem Qppphys_pos {sigma rho : Fin 2 → ℝ} (hsig : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 < rho i)
    (heta : etaMix rho sigma < 1) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (i j : Fin 2) :
    0 < Qppphys (t • rho) sigma i j := by
  have hv := vac_pos_on hsig hrho heta t ht
  have hsj := hsig j
  unfold Qppphys
  have hxi : 0 ≤ xi2 (t • rho) sigma := by
    unfold xi2; apply Finset.sum_nonneg; intro k _
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg (mul_nonneg ht.1 (hrho k).le) (sq_nonneg _)
  refine mul_pos (div_pos (by positivity) hv) ?_
  have h2 : 0 ≤ Real.pi * xi2 (t • rho) sigma * sigma j / (2 * vacMix (t • rho) sigma) :=
    div_nonneg (by positivity) (by positivity)
  linarith

theorem Pdens_Phys {sigma rho : Fin 2 → ℝ} (hsig : ∀ i, 0 < sigma i) (hsord : sigma 0 < sigma 1)
    (hrho : ∀ i, 0 < rho i) (heta : etaMix rho sigma < 1) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    (ht0 : 0 < t) : (Pdens sigma rho t).Phys :=
  ⟨hsig 0, hsord, fun i j => rhoGeoPhys_pos hrho ht0 i j,
    fun i j => Q0phys_pos hsig hrho heta ht i j, fun i j => Qppphys_pos hsig hrho heta ht i j⟩

/-- **`hRunif` — a uniform-in-`t` escape radius for the density homotopy.**  The five envelope
constants of `Pdens t` are continuous in `t`, hence bounded by some `B` on the compact `[0,1]`, so a
single `R = max(1, 5B+1)` gives `detF(Pdens t, s) ≠ 0` for `Re s ≥ 0`, `‖s‖ ≥ R`, uniformly in `t`. -/
theorem hRunif_Pdens {sigma rho : Fin 2 → ℝ} (hsig : ∀ i, 0 < sigma i) (hsord : sigma 0 < sigma 1)
    (hrho : ∀ i, 0 < rho i) (heta : etaMix rho sigma < 1) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ t ∈ Icc (0:ℝ) 1, ∀ s : ℂ, 0 ≤ s.re → R ≤ ‖s‖ →
      (Pdens sigma rho t).detF s ≠ 0 := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (Ksum_cont hsig hrho heta)
  refine ⟨max 1 (5 * max 0 C + 1), le_max_left _ _, ?_⟩
  intro t ht s hre hs
  rcases eq_or_lt_of_le ht.1 with h0 | ht0
  · rw [← h0, detF_Pdens_zero]; exact one_ne_zero
  · have hPhys := Pdens_Phys hsig hsord hrho heta ht ht0
    have hKsum : (Pdens sigma rho t).KMc + (Pdens sigma rho t).K0 + (Pdens sigma rho t).mu
        + (Pdens sigma rho t).K1 + (Pdens sigma rho t).K01 ≤ max 0 C := by
      have hle := Real.le_norm_self ((Pdens sigma rho t).KMc + (Pdens sigma rho t).K0
        + (Pdens sigma rho t).mu + (Pdens sigma rho t).K1 + (Pdens sigma rho t).K01)
      have := hC t ht
      have hCB := le_max_right (0:ℝ) C
      linarith
    have hKMc0 := KMc_nonneg (Pdens sigma rho t) hPhys
    have hK00 := K0_nonneg (Pdens sigma rho t) hPhys
    have hmu0 := mu_nonneg (Pdens sigma rho t) hPhys
    have hK10 := K1_nonneg (Pdens sigma rho t) hPhys
    have hK010 := K01_nonneg (Pdens sigma rho t) hPhys
    exact detF_ne_zero_of_Kbound (Pdens sigma rho t) hPhys (le_max_left 0 C)
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hre hs

end
end FMSA.MixtureHSPoles
