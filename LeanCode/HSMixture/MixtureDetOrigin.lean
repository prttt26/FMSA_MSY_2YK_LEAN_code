/-
Copyright (c) 2026. All rights reserved.
-/
import LeanCode.HSMixture.MixtureDetEntire
import LeanCode.HSMixture.Q0MomentGeOne
import LeanCode.Analysis.ZeroCountHomotopy

/-!
# The origin value `c ≠ 0` — the `k=0` compressibility (`OZFIX.17`, axiom-clean)

The last physical sub-fact of the matrix pole-freeness: the removable limit `c` of
`detF(Pdens σ ρ t)` at `s = 0` — the `k = 0` structure factor / compressibility — is nonzero, giving
`hreal` at `z = 0` for the density homotopy.  Route 1 (explicit moment determinant):

* `detF_Pdens_ofReal` — at a real argument, `detF(Pdens σ ρ t, z) = det Q0_mat_phys(z, σ, t·ρ)` cast
  to `ℂ` (`Q0_mat_c_phys_ofReal` + `RingHom.map_det`).
* `Q0_mat_phys_det_ge_one` (`Q0MomentGeOne.lean`) — `1 ≤ det Q0_mat_phys(z)` for real `z > 0`.
* Hence `Re(c) = lim_{z→0⁺} det ≥ 1 > 0` (`ge_of_tendsto`), so `c ≠ 0`.

`detF_Pdens_origin_ne_zero` depends only on `moment_key` (proved algebra) — **no physics axiom**: the
`k = 0` compressibility positivity is *proved*, not assumed (`pyhs_mixture_no_spinodal` covers only
`k ≠ 0`).
-/

open Filter Topology Complex Set

namespace FMSA.MixtureHSPoles
noncomputable section

/-- At a real argument the physical complex Baxter matrix is the cast of the real one. -/
theorem Q0_mat_c_phys_ofReal (z : ℝ) (sigma rho : Fin 2 → ℝ) :
    FMSA.MixtureNoSpinodal.Q0_mat_c_phys (z : ℂ) sigma rho
      = (FMSA.MatrixQ0.Q0_mat_phys z sigma rho).map Complex.ofReal := by
  funext i j
  simp only [FMSA.MixtureNoSpinodal.Q0_mat_c_phys, FMSA.MatrixQ0.Q0_mat_phys,
    FMSA.Q0Complex.Q0_mat_c, FMSA.MatrixQ0.Q0_mat, Matrix.map_apply,
    FMSA.Q0Complex.q0_entry_c, FMSA.MatrixQ0.q0_entry]
  split_ifs <;> push_cast [Complex.ofReal_exp] <;> ring

/-- `detF(Pdens σ ρ t, z) = det Q0_mat_phys(z, σ, t·ρ)` cast to `ℂ`, at real `z`. -/
theorem detF_Pdens_ofReal (sigma rho : Fin 2 → ℝ) (t : ℝ) (z : ℝ) :
    (Pdens sigma rho t).detF (z : ℂ)
      = ((FMSA.MatrixQ0.Q0_mat_phys z sigma (t • rho)).det : ℂ) := by
  rw [detF_Pdens_eq, Q0_mat_c_phys_ofReal]
  exact (RingHom.map_det Complex.ofRealHom _).symm

/-- **Origin value `c ≠ 0`.**  The removable limit `c` of `detF(Pdens σ ρ t)` at `s = 0` (the `k = 0`
compressibility) is nonzero.  `det Q0_mat_phys(z) ≥ 1` for real `z > 0` ⇒ `Re(c) ≥ 1 > 0`.  Depends
only on `moment_key` — no physics axiom. -/
theorem detF_Pdens_origin_ne_zero {sigma rho : Fin 2 → ℝ} (hsig : ∀ i, 0 < sigma i)
    (hrho : ∀ i, 0 < rho i) (heta : FMSA.MatrixQ0.etaMix rho sigma < 1)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1)
    {c : ℂ} (hc : Tendsto (Pdens sigma rho t).detF (𝓝[≠] (0:ℂ)) (𝓝 c)) :
    c ≠ 0 := by
  have hofR : Tendsto (fun z : ℝ => (z : ℂ)) (𝓝[>] (0:ℝ)) (𝓝[≠] (0:ℂ)) :=
    FMSA.MatrixQ0.ofReal_tendsto_nhdsNE.mono_left (nhdsWithin_mono 0 (fun x hx =>
      Set.mem_compl_singleton_iff.mpr (ne_of_gt (Set.mem_Ioi.mp hx))))
  have hreal : Tendsto (fun z : ℝ => ((FMSA.MatrixQ0.Q0_mat_phys z sigma (t • rho)).det : ℂ))
      (𝓝[>] (0:ℝ)) (𝓝 c) := by
    have hfe : (fun z : ℝ => ((FMSA.MatrixQ0.Q0_mat_phys z sigma (t • rho)).det : ℂ))
        = fun z : ℝ => (Pdens sigma rho t).detF (z : ℂ) := by
      funext z; exact (detF_Pdens_ofReal sigma rho t z).symm
    rw [hfe]; exact hc.comp hofR
  have hRe : Tendsto (fun z : ℝ => (FMSA.MatrixQ0.Q0_mat_phys z sigma (t • rho)).det)
      (𝓝[>] (0:ℝ)) (𝓝 c.re) := by
    have h := (Complex.continuous_re.tendsto c).comp hreal
    simpa only [Function.comp_def, Complex.ofReal_re] using h
  have hvac : 0 < FMSA.MatrixQ0.vacMix (t • rho) sigma := by
    unfold FMSA.MatrixQ0.vacMix
    rw [etaMix_smul]; nlinarith [etaMix_nonneg hsig hrho, heta, ht1, ht0]
  have h1 : (1:ℝ) ≤ c.re := by
    refine ge_of_tendsto hRe ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact FMSA.MatrixQ0.Q0_mat_phys_det_ge_one (rho := t • rho) (Set.mem_Ioi.mp hz) hvac
      (fun i => by rw [Pi.smul_apply, smul_eq_mul]; exact (mul_pos ht0 (hrho i)).le) hsig
  intro hc0
  rw [hc0, Complex.zero_re] at h1
  linarith

/-- **`hreal` at `z = 0` for the physical extension** — `detF_ext(Pdens σ ρ t, 0) ≠ 0`.  The removable
extension's origin value is the limit `c`, nonzero by `detF_Pdens_origin_ne_zero`. -/
theorem detF_ext_Pdens_origin_ne_zero {sigma rho : Fin 2 → ℝ} (hsig : ∀ i, 0 < sigma i)
    (hrho : ∀ i, 0 < rho i) (heta : FMSA.MatrixQ0.etaMix rho sigma < 1)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) {c : ℂ}
    (hc : Tendsto (Pdens sigma rho t).detF (𝓝[≠] (0:ℂ)) (𝓝 c)) :
    Function.update (Pdens sigma rho t).detF 0 c 0 ≠ 0 := by
  rw [Function.update_self]
  exact detF_Pdens_origin_ne_zero hsig hrho heta ht0 ht1 hc


/-! ### Concrete pole-freeness assembly (conditional on family regularity) -/

/-- Real-axis non-vanishing along the whole path: `detF(Pdens t, I·k) ≠ 0` for real `k ≠ 0`,
`t ∈ [0,1]` (t=0 dilute `≡ 1`, t>0 no-spinodal). -/
theorem Pdens_detF_imag_ne_zero {sigma rho : Fin 2 → ℝ} (hsig : ∀ i, 0 < sigma i)
    (hrho : ∀ i, 0 < rho i) (heta : FMSA.MatrixQ0.etaMix rho sigma < 1)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) {k : ℝ} (hk : k ≠ 0) :
    (Pdens sigma rho t).detF (Complex.I * (k : ℂ)) ≠ 0 := by
  rcases eq_or_lt_of_le ht.1 with h0 | ht0
  · rw [← h0, detF_Pdens_zero]; exact one_ne_zero
  · exact detF_Pdens_ne_zero hsig hrho heta ht0 ht.2 hk

/-- The origin limit is nonzero along the whole path (t=0: `cf 0 = 1`; t>0: compressibility). -/
theorem cf_ne_zero {sigma rho : Fin 2 → ℝ} (hsig : ∀ i, 0 < sigma i)
    (hrho : ∀ i, 0 < rho i) (heta : FMSA.MatrixQ0.etaMix rho sigma < 1)
    {cf : ℝ → ℂ} {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    (hcft : Tendsto (Pdens sigma rho t).detF (𝓝[≠] (0:ℂ)) (𝓝 (cf t))) :
    cf t ≠ 0 := by
  rcases eq_or_lt_of_le ht.1 with h0 | ht0
  · rw [← h0] at hcft ⊢
    rw [tendsto_nhds_unique hcft (detF_Pdens_zero_tendsto sigma rho)]; exact one_ne_zero
  · exact detF_Pdens_origin_ne_zero hsig hrho heta ht0 ht.2 hcft

theorem mixtureDet_pole_free_of_regular {sigma rho : Fin 2 → ℝ}
    (hsig : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 < rho i) (heta : FMSA.MatrixQ0.etaMix rho sigma < 1)
    (cf : ℝ → ℂ)
    (hcf : ∀ t ∈ Icc (0:ℝ) 1, Tendsto (Pdens sigma rho t).detF (𝓝[≠] (0:ℂ)) (𝓝 (cf t)))
    (hcont : ContinuousOn (fun p : ℝ × ℂ =>
        Function.update (Pdens sigma rho p.1).detF 0 (cf p.1) (Complex.I * p.2))
      (Icc 0 1 ×ˢ (univ : Set ℂ)))
    {R : ℝ} (hR1 : 1 ≤ R)
    (hRunif : ∀ t ∈ Icc (0:ℝ) 1, ∀ s : ℂ, 0 ≤ s.re → R ≤ ‖s‖ → (Pdens sigma rho t).detF s ≠ 0)
    {z : ℂ} (hz : z.im < 0) :
    (Pdens sigma rho 1).detF (Complex.I * z) ≠ 0 := by
  have hre_eq : ∀ w : ℂ, (Complex.I * w).re = -w.im := fun w => by simp [Complex.mul_re]
  have hnorm_eq : ∀ w : ℂ, ‖Complex.I * w‖ = ‖w‖ := fun w => by
    rw [norm_mul, Complex.norm_I, one_mul]
  have hkey := FMSA.Analysis.zeroFree_lowerHalfPlane_of_homotopy
    (H := fun t z => Function.update (Pdens sigma rho t).detF 0 (cf t) (Complex.I * z))
    (a := 0) (b := 1) (R := R) (by norm_num) (by linarith) hcont
    (fun t ht => (detF_update_differentiable (Pdens sigma rho t) (hcf t ht)).comp
      (differentiable_id.const_mul Complex.I))
    (fun t ht w hwim hHw => by
      by_contra hnot
      rw [not_lt] at hnot
      have hw0 : w ≠ 0 := fun h => by rw [h, norm_zero] at hnot; linarith
      have hIw : Complex.I * w ≠ 0 := mul_ne_zero Complex.I_ne_zero hw0
      rw [Function.update_of_ne hIw] at hHw
      exact hRunif t ht _ (by rw [hre_eq]; linarith) (by rw [hnorm_eq]; exact hnot) hHw)
    (fun t ht w hwim => by
      by_cases hw0 : w = 0
      · rw [hw0, mul_zero, Function.update_self]
        exact cf_ne_zero hsig hrho heta ht (hcf t ht)
      · have hIw : Complex.I * w ≠ 0 := mul_ne_zero Complex.I_ne_zero hw0
        rw [Function.update_of_ne hIw]
        have hwre : w = ((w.re : ℝ) : ℂ) := by
          apply Complex.ext <;> simp [hwim]
        rw [hwre]
        exact Pdens_detF_imag_ne_zero hsig hrho heta ht
          (by intro h; apply hw0; rw [hwre, h]; simp))
    (fun w hwim => by
      have hw0 : w ≠ 0 := fun h => by rw [h] at hwim; simp at hwim
      have hIw : Complex.I * w ≠ 0 := mul_ne_zero Complex.I_ne_zero hw0
      rw [Function.update_of_ne hIw, detF_Pdens_zero]; exact one_ne_zero)
    z hz
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  have hIz : Complex.I * z ≠ 0 := mul_ne_zero Complex.I_ne_zero hz0
  rwa [Function.update_of_ne hIz] at hkey
end
end FMSA.MixtureHSPoles
