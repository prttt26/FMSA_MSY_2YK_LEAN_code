/-
Copyright (c) 2026. All rights reserved.
-/
import LeanCode.HSMixture.MixtureDetHcont
import LeanCode.HSMixture.MatrixDetPoleFree
import LeanCode.HSMixture.MixtureNoSpinodal
import LeanCode.HSMixture.ArcAmplitudeBound

/-!
# General-`N` matrix pole-freeness (`OZFIX.17`, generalising the `N=2` result)

The `N=2` `mixtureDet_pole_free` (`MixtureDetHcont.lean`) generalises to arbitrary `N`, reduced to a
single remaining ingredient — the **escape** `hesc` (uniform-in-`t` boundedness of the density
homotopy's `det`-zeros for `Re s ≥ 0`).  Everything else is discharged here, `N`-uniformly, via the
already-general matrix homotopy framework `matDet_zeroFree_lowerHalfPlane_of_homotopy`
(`MatrixDetPoleFree.lean`) applied to the entire `ψ`-matrix `Mdens` (the physical Baxter matrix with
each `φ = num/sⁿ` kernel replaced by its entire removable extension `ψ`, so every entry is entire —
`hholo` — and jointly continuous — `hcont`):

* `Qpsi`/`Mdens` — the general-`N` `ψ`-matrix and its density homotopy `Mdens t = Q̂₀(ψ-form, t·ρ)`;
  `Qpsi_eq_Q0_mat_c` (`= Q0_mat_c` off `s=0`), `Mdens_eq_phys` (`= Q0_mat_c_phys` off `0`).
* `Mdens_hholo` / `Mdens_hcont` — entrywise entire / jointly continuous (from `psi{1,2}_entire`,
  `psi{1,2}_continuous`, and the `N`-general field continuities `Q0phys_contN` etc.).
* `Mdens_hbase` — dilute base `Mdens 0 = I`, `det = 1`.
* `Mdens_hreal` — no real-axis `det`-zero: `k ≠ 0` via `pyhs_mixture_no_spinodal` (`N`-general);
  `k = 0` via `detMdens_origin_ne_zero`, the **axiom-clean** `k=0` compressibility (`det ≥ 1` from
  the rank-2 reduction `Q0_mat_phys_det_ge_one_N` + `moment_key`, no physics axiom).

`mixtureDet_pole_free_N` : `det Q̂₀(I·z) ≠ 0` on the open lower half `z`-plane for every physical
`N`-component mixture — **fully unconditional**, depending only on the two existing axioms
(`zeroFree_lowerHalfPlane_of_homotopy`, `pyhs_mixture_no_spinodal`) — no new axiom.
(`mixtureDet_pole_free_N_of_escape` is the intermediate form, parametric in the escape.)

**The escape `hesc` — the genuine `N`-general obstacle — is discharged (`exists_uniform_escape`).**
Individual `Q̂₀` entries diverge as `Re s → ∞` (the `e^{−λ_{ij}s}` factors with
`λ_{ij} = (σⱼ−σᵢ)/2 < 0`), but the `det` stays bounded — the `λ`'s cancel per permutation
(`∑ᵢ(σ_{π(i)}−σᵢ) = 0`).  The `N=2` proof captured this via the 4-term monomial bridge; the
`N`-general route here is cleaner: the phase `e^{−λ_{ij}s} = e^{σᵢs/2}·e^{−σⱼs/2}` is exactly a
**diagonal similarity**, so `det Q̂₀ = det Mgauge` (`det_Q0_eq_det_gauge`) where `Mgauge` has the phase
stripped (`lam = 0`).  Then `Mgauge = 1 − A` with `‖A‖_{L∞ op} ≤ Abnd/‖s‖ → 0`
(`norm_one_sub_Mgauge_le`, from the kernel bounds `‖φ₁‖,‖φ₂‖ ≤ C/‖s‖`), uniformly in `t` since
`Abnd` is continuous hence bounded on `[0,1]` (`Abnd_cont` + compactness), so `Mgauge` is a unit
(`isUnit_one_sub_of_norm_lt_one`) and `det ≠ 0` for `‖s‖` large.
-/

open Filter Topology Complex Set Matrix
open scoped Matrix.Norms.Operator
namespace FMSA.MixtureGenN
open FMSA.MixtureHSPoles FMSA.MatrixQ0 FMSA.Q0Complex
noncomputable section


/-! ### General-N field continuity in the density parameter (proofs are N-agnostic) -/
theorem etaMix_smulN {N : ℕ} (t : ℝ) (rho sigma : Fin N → ℝ) :
    etaMix (t • rho) sigma = t * etaMix rho sigma := by
  simp only [etaMix, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring
theorem etaMix_nonnegN {N : ℕ} {sigma rho : Fin N → ℝ} (hsig : ∀ i, 0 < sigma i)
    (hrho : ∀ i, 0 < rho i) : 0 ≤ etaMix rho sigma := by
  unfold etaMix
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => ?_)
  exact mul_nonneg (hrho i).le (pow_nonneg (hsig i).le 3)
theorem vac_pos_onN {N : ℕ} {sigma rho : Fin N → ℝ} (hsig : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 < rho i)
    (heta : etaMix rho sigma < 1) : ∀ t ∈ Icc (0:ℝ) 1, 0 < vacMix (t • rho) sigma := by
  intro t ht
  unfold vacMix
  rw [show etaMix (t • rho) sigma = t * etaMix rho sigma from etaMix_smulN t rho sigma]
  nlinarith [etaMix_nonnegN hsig hrho, heta, ht.1, ht.2]

theorem vacMix_contN {N : ℕ} {sigma rho : Fin N → ℝ} :
    ContinuousOn (fun t : ℝ => vacMix (t • rho) sigma) (Icc 0 1) := by
  unfold vacMix etaMix; fun_prop
theorem xi2_contN {N : ℕ} {sigma rho : Fin N → ℝ} :
    ContinuousOn (fun t : ℝ => xi2 (t • rho) sigma) (Icc 0 1) := by
  unfold xi2; fun_prop
theorem Q0phys_contN {N : ℕ} {sigma rho : Fin N → ℝ} (hsig : ∀ i, 0 < sigma i)
    (hrho : ∀ i, 0 < rho i) (heta : etaMix rho sigma < 1) (i j : Fin N) :
    ContinuousOn (fun t : ℝ => Q0phys (t • rho) sigma i j) (Icc 0 1) := by
  have hv := vac_pos_onN hsig hrho heta
  unfold Q0phys
  refine ContinuousOn.mul (continuousOn_const.div vacMix_contN (fun t ht => (hv t ht).ne'))
    (continuousOn_const.add (ContinuousOn.div ?_ ?_ ?_))
  · exact (continuousOn_const.mul xi2_contN).mul continuousOn_const |>.mul continuousOn_const
  · exact continuousOn_const.mul vacMix_contN
  · exact fun t ht => mul_ne_zero (by norm_num) (hv t ht).ne'
theorem Qppphys_contN {N : ℕ} {sigma rho : Fin N → ℝ} (hsig : ∀ i, 0 < sigma i)
    (hrho : ∀ i, 0 < rho i) (heta : etaMix rho sigma < 1) (i j : Fin N) :
    ContinuousOn (fun t : ℝ => Qppphys (t • rho) sigma i j) (Icc 0 1) := by
  have hv := vac_pos_onN hsig hrho heta
  unfold Qppphys
  refine ContinuousOn.mul (continuousOn_const.div vacMix_contN (fun t ht => (hv t ht).ne'))
    (continuousOn_const.add (ContinuousOn.div ?_ ?_ ?_))
  · exact (continuousOn_const.mul xi2_contN).mul continuousOn_const
  · exact continuousOn_const.mul vacMix_contN
  · exact fun t ht => mul_ne_zero (by norm_num) (hv t ht).ne'
theorem rhoGeoPhys_contN {N : ℕ} {rho : Fin N → ℝ} (i j : Fin N) :
    ContinuousOn (fun t : ℝ => rhoGeoPhys (t • rho) i j) (Icc 0 1) := by
  unfold rhoGeoPhys; fun_prop

/-! ### General-N ψ-matrix -/

/-- General-`N` `ψ`-form Baxter matrix: `Q0_mat_c` with each `φ`-kernel replaced by its entire
removable extension `ψ`.  Entire and jointly continuous, and `= Q0_mat_c` away from `s = 0`. -/
def Qpsi {N : ℕ} (s : ℂ) (sigma : Fin N → ℂ) (rho_geo Qp Qpp : Fin N → Fin N → ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j => q0_entry_psi (sigma i) ((sigma j - sigma i) / 2)
    (Qp i j) (Qpp i j) (rho_geo i j) (if i = j then 1 else 0) s

theorem Qpsi_eq_Q0_mat_c {N : ℕ} {s : ℂ} (hs : s ≠ 0) (sigma : Fin N → ℂ)
    (rho_geo Qp Qpp : Fin N → Fin N → ℂ) :
    Qpsi s sigma rho_geo Qp Qpp = Q0_mat_c s sigma rho_geo Qp Qpp := by
  funext i j
  rw [Qpsi, Q0_mat_c, q0_entry_c_eq_psi hs, q0_entry_psi]

theorem q0_entry_psi_entire {σ lam Qp Qpp ρ δ : ℂ} (hσ : σ ≠ 0) :
    Differentiable ℂ (fun s => q0_entry_psi σ lam Qp Qpp ρ δ s) := by
  unfold q0_entry_psi
  have h1 := psi1_entire hσ
  have h2 := psi2_entire hσ
  fun_prop

/-! ### Density homotopy matrix and its regularity (hholo, hcont) -/

/-- The density-homotopy `ψ`-matrix at homotopy time `t` and Baxter variable `s`: the physical
mixture `Q̂₀` (`ψ`-form) at density `t·ρ`. -/
def Mdens {N : ℕ} (sigma rho : Fin N → ℝ) (t : ℝ) (s : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Qpsi s (fun i => (sigma i : ℂ)) (fun i j => (rhoGeoPhys (t • rho) i j : ℂ))
    (fun i j => (Q0phys (t • rho) sigma i j : ℂ)) (fun i j => (Qppphys (t • rho) sigma i j : ℂ))

/-- **`hholo`** — every entry of `z ↦ Mdens t (I·z)` is entire (the `ψ`-entries are entire). -/
theorem Mdens_hholo {N : ℕ} {sigma rho : Fin N → ℝ} (hsig : ∀ i, 0 < sigma i)
    (t : ℝ) (i j : Fin N) :
    Differentiable ℂ (fun z => (Mdens sigma rho t (Complex.I * z)) i j) := by
  have hσ : ((sigma i : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hsig i).ne'
  exact (q0_entry_psi_entire hσ).comp (differentiable_id.const_mul Complex.I)

/-- **`hcont`** — every entry of `(t,z) ↦ Mdens t (I·z)` is jointly continuous on `[0,1] × ℂ`
(`ψ` continuous in `z`; `rhoGeoPhys`/`Q0phys`/`Qppphys` continuous in `t`). -/
theorem Mdens_hcont {N : ℕ} {sigma rho : Fin N → ℝ} (hsig : ∀ i, 0 < sigma i)
    (hrho : ∀ i, 0 < rho i) (heta : etaMix rho sigma < 1) (i j : Fin N) :
    ContinuousOn (fun p : ℝ × ℂ => (Mdens sigma rho p.1 (Complex.I * p.2)) i j)
      (Icc 0 1 ×ˢ (univ : Set ℂ)) := by
  have hσ : ((sigma i : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hsig i).ne'
  have hmaps : Set.MapsTo (Prod.fst : ℝ × ℂ → ℝ) (Icc (0:ℝ) 1 ×ˢ univ) (Icc 0 1) := fun p hp => hp.1
  have L : ∀ (f : ℝ → ℝ), ContinuousOn f (Icc 0 1) →
      ContinuousOn (fun p : ℝ × ℂ => ((f p.1 : ℝ) : ℂ)) (Icc 0 1 ×ˢ (univ : Set ℂ)) :=
    fun f hf => (Complex.continuous_ofReal.comp_continuousOn (hf.comp continuousOn_fst hmaps))
  have hg := L _ (rhoGeoPhys_contN (rho := rho) i j)
  have hp := L _ (Q0phys_contN hsig hrho heta i j)
  have hq := L _ (Qppphys_contN hsig hrho heta i j)
  have hps1 : Continuous (fun z : ℂ => psi1 (sigma i : ℂ) z) := psi1_continuous hσ
  have hps2 : Continuous (fun z : ℂ => psi2 (sigma i : ℂ) z) := psi2_continuous hσ
  simp only [Mdens, Qpsi, q0_entry_psi]
  fun_prop

/-! ### hbase (dilute) and the bridge to the physical complex matrix -/

/-- Dilute base: zero density ⇒ `Mdens = I`. -/
theorem Mdens_zero_eq_one {N : ℕ} (sigma rho : Fin N → ℝ) (s : ℂ) :
    Mdens sigma rho 0 s = 1 := by
  funext i j
  have hz : (rhoGeoPhys ((0:ℝ) • rho) i j : ℂ) = 0 := by
    have : rhoGeoPhys ((0:ℝ) • rho) i j = 0 := by unfold rhoGeoPhys; simp
    rw [this]; simp
  simp only [Mdens, Qpsi, q0_entry_psi, hz, Matrix.one_apply]
  simp

/-- **`hbase`** — at zero density the determinant is `1`, nonzero everywhere. -/
theorem Mdens_hbase {N : ℕ} (sigma rho : Fin N → ℝ) {z : ℂ} (_ : z.im < 0) :
    (Mdens sigma rho 0 (Complex.I * z)).det ≠ 0 := by
  rw [Mdens_zero_eq_one, Matrix.det_one]; exact one_ne_zero

/-- The `ψ`-matrix equals the physical complex Baxter matrix away from `s = 0`. -/
theorem Mdens_eq_phys {N : ℕ} (sigma rho : Fin N → ℝ) (t : ℝ) {s : ℂ} (hs : s ≠ 0) :
    Mdens sigma rho t s = FMSA.MixtureNoSpinodal.Q0_mat_c_phys s sigma (t • rho) := by
  rw [Mdens, Qpsi_eq_Q0_mat_c hs]
  rfl

/-! ### General-N compressibility (k=0 origin value), axiom-clean via det ≥ 1 -/

/-- General-`N` real bridge: at a real argument, the physical complex Baxter matrix is the cast of
the real one. -/
theorem Q0_mat_c_phys_ofReal_N {N : ℕ} (z : ℝ) (sigma rho : Fin N → ℝ) :
    FMSA.MixtureNoSpinodal.Q0_mat_c_phys (z : ℂ) sigma rho
      = (FMSA.MatrixQ0.Q0_mat_phys z sigma rho).map Complex.ofReal := by
  funext i j
  simp only [FMSA.MixtureNoSpinodal.Q0_mat_c_phys, FMSA.MatrixQ0.Q0_mat_phys,
    FMSA.Q0Complex.Q0_mat_c, FMSA.MatrixQ0.Q0_mat, Matrix.map_apply,
    FMSA.Q0Complex.q0_entry_c, FMSA.MatrixQ0.q0_entry]
  split_ifs <;> push_cast [Complex.ofReal_exp] <;> ring

/-- `det (Mdens t)` is continuous in `s` (the `ψ`-entries are entire). -/
theorem detMdens_continuous {N : ℕ} {sigma rho : Fin N → ℝ} (hsig : ∀ i, 0 < sigma i) (t : ℝ) :
    Continuous (fun s => (Mdens sigma rho t s).det) := by
  refine (FMSA.MixtureOzStar.differentiable_matrix_det (f := fun s => Mdens sigma rho t s)
    (fun a b => ?_)).continuous
  have hσ : ((sigma a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hsig a).ne'
  exact q0_entry_psi_entire hσ

/-- **General-`N` compressibility (`k=0` origin value).**  `det (Mdens σ ρ t) 0 ≠ 0` for `t ∈ (0,1]`:
`Re` of the origin value is the limit of `det Q0_mat_phys(x) ≥ 1` along `x → 0⁺`, hence `≥ 1 > 0`.
Axiom-clean (via `moment_key`) — no physics axiom. -/
theorem detMdens_origin_ne_zero {N : ℕ} {sigma rho : Fin N → ℝ} (hsig : ∀ i, 0 < sigma i)
    (hrho : ∀ i, 0 < rho i) (heta : etaMix rho sigma < 1) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    (Mdens sigma rho t 0).det ≠ 0 := by
  set g : ℂ → ℂ := fun s => (Mdens sigma rho t s).det with hgdef
  have hgc : Continuous g := detMdens_continuous hsig t
  have hvac : 0 < vacMix (t • rho) sigma := by
    unfold vacMix; rw [etaMix_smulN]
    nlinarith [etaMix_nonnegN hsig hrho, heta, ht1, ht0]
  -- along the positive real axis, g = (det Q0_mat_phys : ℂ), with Re ≥ 1
  have hval : ∀ x : ℝ, 0 < x → g (x : ℂ) = ((Q0_mat_phys x sigma (t • rho)).det : ℂ) := by
    intro x hx
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    show (Mdens sigma rho t (x : ℂ)).det = ((Q0_mat_phys x sigma (t • rho)).det : ℂ)
    rw [Mdens_eq_phys sigma rho t hx0, Q0_mat_c_phys_ofReal_N]
    exact (RingHom.map_det Complex.ofRealHom _).symm
  have hofR : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] (0:ℝ)) (𝓝 (0:ℂ)) := by
    have h := (Complex.continuous_ofReal.tendsto (0:ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
    simpa using h
  have hlim : Tendsto (fun x : ℝ => g (x : ℂ)) (𝓝[>] (0:ℝ)) (𝓝 (g 0)) :=
    (hgc.tendsto (0:ℂ)).comp hofR
  have hRe : Tendsto (fun x : ℝ => (Q0_mat_phys x sigma (t • rho)).det) (𝓝[>] (0:ℝ)) (𝓝 (g 0).re) := by
    have h := (Complex.continuous_re.tendsto (g 0)).comp hlim
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [Function.comp_apply, hval x (Set.mem_Ioi.mp hx), Complex.ofReal_re]
  have h1 : (1:ℝ) ≤ (g 0).re := by
    refine ge_of_tendsto hRe ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact FMSA.MatrixQ0.Q0_mat_phys_det_ge_one_N (Set.mem_Ioi.mp hx) hvac
      (fun i => by rw [Pi.smul_apply, smul_eq_mul]; exact (mul_pos ht0 (hrho i)).le) hsig
  intro hg0
  have hg0' : g 0 = 0 := hg0
  rw [hg0', Complex.zero_re] at h1; linarith

/-! ### hreal (no real-axis det-zero) -/

/-- **`hreal`** — no `det`-zero on the whole real `z`-axis along the density path.  `k ≠ 0`:
`pyhs_mixture_no_spinodal` at density `t·ρ`.  `k = 0`: compressibility `detMdens_origin_ne_zero`
(`t > 0`) or dilute `det = 1` (`t = 0`). -/
theorem Mdens_hreal {N : ℕ} {sigma rho : Fin N → ℝ} (hsig : ∀ i, 0 < sigma i)
    (hrho : ∀ i, 0 < rho i) (heta : etaMix rho sigma < 1) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    {z : ℂ} (hzim : z.im = 0) :
    (Mdens sigma rho t (Complex.I * z)).det ≠ 0 := by
  have hzre : z = ((z.re : ℝ) : ℂ) := by apply Complex.ext <;> simp [hzim]
  by_cases hz0 : z = 0
  · rw [hz0, mul_zero]
    rcases eq_or_lt_of_le ht.1 with h0 | ht0
    · rw [← h0, Mdens_zero_eq_one, Matrix.det_one]; exact one_ne_zero
    · exact detMdens_origin_ne_zero hsig hrho heta ht0 ht.2
  · have hIz : Complex.I * z ≠ 0 := mul_ne_zero Complex.I_ne_zero hz0
    rcases eq_or_lt_of_le ht.1 with h0 | ht0
    · rw [← h0, Mdens_zero_eq_one, Matrix.det_one]; exact one_ne_zero
    · rw [Mdens_eq_phys sigma rho t hIz]
      have hk : z.re ≠ 0 := fun h => hz0 (by rw [hzre, h]; simp)
      have hns := FMSA.MixtureNoSpinodal.pyhs_mixture_no_spinodal (sigma := sigma) (rho := t • rho)
        hsig (fun i => by rw [Pi.smul_apply, smul_eq_mul]; exact mul_pos ht0 (hrho i))
        (by rw [etaMix_smulN]; nlinarith [etaMix_nonnegN hsig hrho, heta, ht.2, ht0]) hk
      rwa [show (Complex.I * ((z.re : ℝ) : ℂ)) = Complex.I * z from by rw [← hzre]] at hns

/-! ### General-N pole-freeness, conditional on the escape (hbound) -/

/-- **General-`N` matrix pole-freeness, conditional on the escape `hesc`.**  Given a uniform escape
radius `R` (no `det`-zero of the density homotopy for `Re s ≥ 0`, `‖z‖ ≥ R`), `det Q̂₀(I·z) ≠ 0`
throughout the open lower half `z`-plane, for every physical `N`-component mixture.  All other
homotopy inputs (`hcont`/`hholo`/`hreal`/`hbase`, incl. the axiom-clean `k=0` compressibility) are
discharged; the only remaining ingredient is `hesc`. -/
theorem mixtureDet_pole_free_N_of_escape {N : ℕ} {sigma rho : Fin N → ℝ}
    (hsig : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 < rho i) (heta : etaMix rho sigma < 1)
    {R : ℝ} (hR : 0 < R)
    (hesc : ∀ t ∈ Icc (0:ℝ) 1, ∀ z : ℂ, z.im ≤ 0 →
      (Mdens sigma rho t (Complex.I * z)).det = 0 → ‖z‖ < R)
    {z : ℂ} (hz : z.im < 0) :
    (FMSA.MixtureNoSpinodal.Q0_mat_c_phys (Complex.I * z) sigma rho).det ≠ 0 := by
  have hkey := FMSA.MixtureOzStar.matDet_zeroFree_lowerHalfPlane_of_homotopy
    (M := fun t z => Mdens sigma rho t (Complex.I * z)) (a := 0) (b := 1) (R := R)
    (by norm_num) hR
    (fun i j => Mdens_hcont hsig hrho heta i j)
    (fun t _ i j => Mdens_hholo hsig t i j)
    hesc
    (fun t ht z hzim => Mdens_hreal hsig hrho heta ht hzim)
    (fun z hz => Mdens_hbase sigma rho hz)
    z hz
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  have hIz : Complex.I * z ≠ 0 := mul_ne_zero Complex.I_ne_zero hz0
  rw [Mdens_eq_phys sigma rho 1 hIz, one_smul] at hkey
  exact hkey


/-! ## The escape (`hbound`) via diagonal-gauge similarity + operator-norm Neumann bound -/


def Mgauge {N : ℕ} (s : ℂ) (σ : Fin N → ℂ) (ρ Qp Qpp : Fin N → Fin N → ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j => q0_entry_c s (σ i) 0 (Qp i j) (Qpp i j) (ρ i j) (if i = j then 1 else 0)

theorem Q0_mat_c_eq_gauge {N : ℕ} (s : ℂ) (σ : Fin N → ℂ) (ρ Qp Qpp : Fin N → Fin N → ℂ) :
    Q0_mat_c s σ ρ Qp Qpp
      = Matrix.of (fun i j => Complex.exp (σ i * s / 2) *
          (Complex.exp (-(σ j * s / 2)) * Mgauge s σ ρ Qp Qpp i j)) := by
  funext i j
  by_cases hij : i = j
  · subst hij
    simp only [Q0_mat_c, Mgauge, Matrix.of_apply, q0_entry_c, sub_self, zero_div,
      zero_mul, neg_zero, Complex.exp_zero]
    rw [← mul_assoc, ← Complex.exp_add, show σ i * s / 2 + -(σ i * s / 2) = 0 from by ring,
      Complex.exp_zero, one_mul]
  · have hEF : Complex.exp (σ i * s / 2) * Complex.exp (-(σ j * s / 2))
        = Complex.exp (-((σ j - σ i) / 2 * s)) := by rw [← Complex.exp_add]; congr 1; ring
    simp only [Q0_mat_c, Mgauge, Matrix.of_apply, q0_entry_c, if_neg hij, zero_mul, neg_zero,
      Complex.exp_zero, one_mul]
    rw [← mul_assoc, hEF]; ring

theorem det_Q0_eq_det_gauge {N : ℕ} (s : ℂ) (σ : Fin N → ℂ) (ρ Qp Qpp : Fin N → Fin N → ℂ) :
    (Q0_mat_c s σ ρ Qp Qpp).det = (Mgauge s σ ρ Qp Qpp).det := by
  have hQ : Q0_mat_c s σ ρ Qp Qpp
      = Matrix.diagonal (fun i => Complex.exp (σ i * s / 2)) * Mgauge s σ ρ Qp Qpp
        * Matrix.diagonal (fun j => Complex.exp (-(σ j * s / 2))) := by
    funext i j
    rw [Q0_mat_c_eq_gauge, Matrix.of_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]; ring
  rw [hQ, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal,
    ← mul_rotate, ← Finset.prod_mul_distrib,
    show (∏ i, Complex.exp (-(σ i * s / 2)) * Complex.exp (σ i * s / 2)) = 1 from
      Finset.prod_eq_one (fun i _ => by
        rw [← Complex.exp_add, show -(σ i * s / 2) + σ i * s / 2 = 0 from by ring, Complex.exp_zero]),
    one_mul]


/-! ### Stage B: kernel bounds and the norm row bound (imported into namespace) -/

theorem norm_exp_neg_le {σ : ℝ} (hσ : 0 ≤ σ) {s : ℂ} (hre : 0 ≤ s.re) :
    ‖Complex.exp (-(s * (σ:ℂ)))‖ ≤ 1 := by
  rw [Complex.norm_exp]
  rw [show (-(s * (σ:ℂ))).re = -(σ * s.re) by
    simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero]; ring]
  rw [Real.exp_le_one_iff]
  exact neg_nonpos.mpr (mul_nonneg hσ hre)

theorem norm_phi1_le {σ : ℝ} (hσ : 0 ≤ σ) {s : ℂ} (hre : 0 ≤ s.re) (hs1 : 1 ≤ ‖s‖) :
    ‖(1 - s * (σ:ℂ) - Complex.exp (-(s * (σ:ℂ)))) / s ^ 2‖ ≤ (2 + σ) / ‖s‖ := by
  -- specialise the general complex-σ arc bound `normP2_arc_decay` (`ArcAmplitudeBound`) to real σ
  have hre' : 0 ≤ (s * (σ : ℂ)).re := by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact mul_nonneg hre hσ
  have h := FMSA.MixtureArcBound.normP2_arc_decay (σ := (σ : ℂ)) hs1 hre'
  rwa [Complex.norm_real, Real.norm_of_nonneg hσ] at h

theorem norm_phi2_le {σ : ℝ} (hσ : 0 ≤ σ) {s : ℂ} (hre : 0 ≤ s.re) (hs1 : 1 ≤ ‖s‖) :
    ‖(1 - s * (σ:ℂ) + (s * (σ:ℂ)) ^ 2 / 2 - Complex.exp (-(s * (σ:ℂ)))) / s ^ 3‖
      ≤ (2 + σ + σ ^ 2 / 2) / ‖s‖ := by
  -- specialise the general complex-σ arc bound `normP3_arc_decay` (`ArcAmplitudeBound`) to real σ
  have hre' : 0 ≤ (s * (σ : ℂ)).re := by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact mul_nonneg hre hσ
  have h := FMSA.MixtureArcBound.normP3_arc_decay (σ := (σ : ℂ)) hs1 hre'
  rwa [Complex.norm_real, Real.norm_of_nonneg hσ] at h

theorem linfty_opNorm_le_row {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i, ∑ j, ‖A i j‖ ≤ c) : ‖A‖ ≤ c := by
  rw [Matrix.linfty_opNorm_def, show c = ((c.toNNReal : NNReal) : ℝ) from (Real.coe_toNNReal c hc).symm,
    NNReal.coe_le_coe]
  refine Finset.sup_le fun i _ => ?_
  rw [← NNReal.coe_le_coe, NNReal.coe_sum]
  simp only [coe_nnnorm]
  rw [Real.coe_toNNReal c hc]
  exact h i

/-- Entry of `1 - Mgauge` is exactly the Baxter perturbation `ρ·(Qp·φ₁ + Qpp·φ₂)`. -/
theorem one_sub_Mgauge_apply {N : ℕ} (s : ℂ) (σ : Fin N → ℂ) (ρ Qp Qpp : Fin N → Fin N → ℂ)
    (i j : Fin N) :
    (1 - Mgauge s σ ρ Qp Qpp) i j
      = ρ i j * (Qp i j * ((1 - s * σ i - Complex.exp (-(s * σ i))) / s ^ 2) +
          Qpp i j * ((1 - s * σ i + (s * σ i) ^ 2 / 2 - Complex.exp (-(s * σ i))) / s ^ 3)) := by
  simp only [Matrix.sub_apply, Matrix.one_apply, Mgauge, q0_entry_c, zero_mul, neg_zero,
    Complex.exp_zero, one_mul]
  split_ifs <;> ring


/-- Per-entry envelope coefficient (real, `≥ 0`). -/
def ecoef {N : ℕ} (σ ρ' : Fin N → ℝ) (i j : Fin N) : ℝ :=
  rhoGeoPhys ρ' i j * (|Q0phys ρ' σ i j| * (2 + σ i)
    + |Qppphys ρ' σ i j| * (2 + σ i + (σ i) ^ 2 / 2))

theorem ecoef_nonneg {N : ℕ} {σ ρ' : Fin N → ℝ} (hσ : ∀ i, 0 < σ i) (i j : Fin N) :
    0 ≤ ecoef σ ρ' i j := by
  unfold ecoef rhoGeoPhys
  have := hσ i
  positivity

/-- Per-entry bound on the Baxter perturbation of the diagonal-gauge matrix. -/
theorem norm_A_entry_le {N : ℕ} {σ ρ' : Fin N → ℝ} (hσ : ∀ i, 0 < σ i) {s : ℂ}
    (hre : 0 ≤ s.re) (hs1 : 1 ≤ ‖s‖) (i j : Fin N) :
    ‖(1 - Mgauge s (fun i => (σ i : ℂ)) (fun i j => (rhoGeoPhys ρ' i j : ℂ))
        (fun i j => (Q0phys ρ' σ i j : ℂ)) (fun i j => (Qppphys ρ' σ i j : ℂ))) i j‖
      ≤ ecoef σ ρ' i j / ‖s‖ := by
  have hs0 : (0:ℝ) < ‖s‖ := lt_of_lt_of_le one_pos hs1
  rw [one_sub_Mgauge_apply]
  have hρge : (0:ℝ) ≤ rhoGeoPhys ρ' i j := Real.sqrt_nonneg _
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hρge]
  rw [ecoef, mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hρge
  calc ‖(Q0phys ρ' σ i j : ℂ) * ((1 - s * (σ i:ℂ) - Complex.exp (-(s * (σ i:ℂ)))) / s ^ 2) +
          (Qppphys ρ' σ i j : ℂ) *
            ((1 - s * (σ i:ℂ) + (s * (σ i:ℂ)) ^ 2 / 2 - Complex.exp (-(s * (σ i:ℂ)))) / s ^ 3)‖
      ≤ ‖(Q0phys ρ' σ i j : ℂ) * ((1 - s * (σ i:ℂ) - Complex.exp (-(s * (σ i:ℂ)))) / s ^ 2)‖ +
          ‖(Qppphys ρ' σ i j : ℂ) *
            ((1 - s * (σ i:ℂ) + (s * (σ i:ℂ)) ^ 2 / 2 - Complex.exp (-(s * (σ i:ℂ)))) / s ^ 3)‖ :=
        norm_add_le _ _
    _ ≤ |Q0phys ρ' σ i j| * ((2 + σ i) / ‖s‖) + |Qppphys ρ' σ i j| * ((2 + σ i + (σ i)^2/2) / ‖s‖) := by
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs]
        gcongr
        · exact norm_phi1_le (hσ i).le hre hs1
        · exact norm_phi2_le (hσ i).le hre hs1
    _ = (|Q0phys ρ' σ i j| * (2 + σ i) + |Qppphys ρ' σ i j| * (2 + σ i + (σ i)^2/2)) / ‖s‖ := by
        ring

/-- Total envelope constant (the `L∞` operator-norm bound coefficient). -/
def Abnd {N : ℕ} (σ ρ' : Fin N → ℝ) : ℝ := ∑ i, ∑ j, ecoef σ ρ' i j

theorem Abnd_nonneg {N : ℕ} {σ ρ' : Fin N → ℝ} (hσ : ∀ i, 0 < σ i) : 0 ≤ Abnd σ ρ' :=
  Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => ecoef_nonneg hσ i j))

/-- `L∞` operator-norm bound on the Baxter perturbation: `‖1 - Mgauge‖ ≤ Abnd / ‖s‖`. -/
theorem norm_one_sub_Mgauge_le {N : ℕ} {σ ρ' : Fin N → ℝ} (hσ : ∀ i, 0 < σ i) {s : ℂ}
    (hre : 0 ≤ s.re) (hs1 : 1 ≤ ‖s‖) :
    ‖1 - Mgauge s (fun i => (σ i : ℂ)) (fun i j => (rhoGeoPhys ρ' i j : ℂ))
        (fun i j => (Q0phys ρ' σ i j : ℂ)) (fun i j => (Qppphys ρ' σ i j : ℂ))‖
      ≤ Abnd σ ρ' / ‖s‖ := by
  have hs0 : (0:ℝ) < ‖s‖ := lt_of_lt_of_le one_pos hs1
  refine linfty_opNorm_le_row _ (div_nonneg (Abnd_nonneg hσ) hs0.le) (fun i => ?_)
  calc ∑ j, ‖(1 - Mgauge s (fun i => (σ i : ℂ)) (fun i j => (rhoGeoPhys ρ' i j : ℂ))
          (fun i j => (Q0phys ρ' σ i j : ℂ)) (fun i j => (Qppphys ρ' σ i j : ℂ))) i j‖
      ≤ ∑ j, ecoef σ ρ' i j / ‖s‖ := Finset.sum_le_sum (fun j _ => norm_A_entry_le hσ hre hs1 i j)
    _ = (∑ j, ecoef σ ρ' i j) / ‖s‖ := by rw [← Finset.sum_div]
    _ ≤ Abnd σ ρ' / ‖s‖ := by
        gcongr
        exact Finset.single_le_sum (fun i _ => Finset.sum_nonneg (fun j _ => ecoef_nonneg hσ i j))
          (Finset.mem_univ i)

/-- The envelope constant is continuous along the density path (hence bounded on `[0,1]`). -/
theorem Abnd_cont {N : ℕ} {σ ρ : Fin N → ℝ} (hσ : ∀ i, 0 < σ i) (hρ : ∀ i, 0 < ρ i)
    (heta : etaMix ρ σ < 1) : ContinuousOn (fun t : ℝ => Abnd σ (t • ρ)) (Icc 0 1) := by
  unfold Abnd ecoef
  refine continuousOn_finset_sum _ (fun i _ => continuousOn_finset_sum _ (fun j _ => ?_))
  exact (rhoGeoPhys_contN i j).mul
    (((Q0phys_contN hσ hρ heta i j).abs.mul continuousOn_const).add
      ((Qppphys_contN hσ hρ heta i j).abs.mul continuousOn_const))

/-- **The escape (`hbound`) — general `N`.**  A uniform radius `R` beyond which the density
homotopy's determinant cannot vanish for `Re s ≥ 0`.  The diagonal gauge sends the blow-up into a
similarity (`det Q̂₀ = det Mgauge`), and `Mgauge = 1 − A` with `‖A‖ ≤ Abnd/‖s‖ → 0` (uniformly in `t`,
as `Abnd` is continuous hence bounded on `[0,1]`), so `Mgauge` is a unit for `‖s‖` large. -/
theorem exists_uniform_escape {N : ℕ} {σ ρ : Fin N → ℝ} (hσ : ∀ i, 0 < σ i) (hρ : ∀ i, 0 < ρ i)
    (heta : etaMix ρ σ < 1) :
    ∃ R : ℝ, 0 < R ∧ ∀ t ∈ Icc (0:ℝ) 1, ∀ z : ℂ, z.im ≤ 0 →
      (Mdens σ ρ t (Complex.I * z)).det = 0 → ‖z‖ < R := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (Abnd_cont hσ hρ heta)
  refine ⟨max 1 C + 1, by positivity, fun t ht z hzim hdet => ?_⟩
  by_contra hnot
  rw [not_lt] at hnot
  have hz1 : (1:ℝ) ≤ ‖z‖ := le_trans (le_trans (le_max_left 1 C) (by linarith)) hnot
  set s := Complex.I * z with hsdef
  have hsnorm : ‖s‖ = ‖z‖ := by rw [hsdef, norm_mul, Complex.norm_I, one_mul]
  have hs1 : (1:ℝ) ≤ ‖s‖ := by rw [hsnorm]; exact hz1
  have hre : 0 ≤ s.re := by
    rw [hsdef, Complex.mul_re, Complex.I_re, Complex.I_im]; simp; linarith [hzim]
  have hIz : s ≠ 0 := by
    intro h; rw [h, norm_zero] at hsnorm; rw [← hsnorm] at hz1; linarith
  -- det Mgauge = det Mdens = 0
  have hdetg : (Mgauge s (fun i => (σ i : ℂ)) (fun i j => (rhoGeoPhys (t • ρ) i j : ℂ))
      (fun i j => (Q0phys (t • ρ) σ i j : ℂ)) (fun i j => (Qppphys (t • ρ) σ i j : ℂ))).det = 0 := by
    rw [Mdens_eq_phys σ ρ t hIz] at hdet
    rw [← det_Q0_eq_det_gauge]
    exact hdet
  -- ‖A‖ < 1
  have hbnd : ‖1 - Mgauge s (fun i => (σ i : ℂ)) (fun i j => (rhoGeoPhys (t • ρ) i j : ℂ))
      (fun i j => (Q0phys (t • ρ) σ i j : ℂ)) (fun i j => (Qppphys (t • ρ) σ i j : ℂ))‖ < 1 := by
    refine lt_of_le_of_lt (norm_one_sub_Mgauge_le hσ hre hs1) ?_
    rw [div_lt_one (by linarith [hs1] : (0:ℝ) < ‖s‖)]
    have hAC : Abnd σ (t • ρ) ≤ C := by
      have := hC t ht; rwa [Real.norm_of_nonneg (Abnd_nonneg hσ)] at this
    rw [hsnorm]; linarith [le_max_right 1 C, hnot]
  have hunit : IsUnit (Mgauge s (fun i => (σ i : ℂ)) (fun i j => (rhoGeoPhys (t • ρ) i j : ℂ))
      (fun i j => (Q0phys (t • ρ) σ i j : ℂ)) (fun i j => (Qppphys (t • ρ) σ i j : ℂ))) := by
    have h := isUnit_one_sub_of_norm_lt_one hbnd
    rwa [sub_sub_cancel] at h
  rw [Matrix.isUnit_iff_isUnit_det] at hunit
  exact hunit.ne_zero hdetg

/-- **Matrix pole-freeness for the physical mixture — general `N`, UNCONDITIONAL.**
`det Q̂₀(I·z) ≠ 0` throughout the open lower half `z`-plane, for every physical `N`-component
hard-sphere mixture.  The `N=2` `mixtureDet_pole_free` generalised to arbitrary `N`: the escape
`hbound` — the last `N`-general ingredient — is discharged via the diagonal-gauge similarity
(`det Q̂₀ = det Mgauge`, blow-up absorbed) and the `L∞` operator-norm Neumann bound
(`‖1 − Mgauge‖ ≤ Abnd/‖s‖ → 0`, uniform in `t` by compactness).  Depends only on the two existing
axioms `zeroFree_lowerHalfPlane_of_homotopy` (math) and `pyhs_mixture_no_spinodal` (physics) —
**no new axiom**. -/
theorem mixtureDet_pole_free_N {N : ℕ} {σ ρ : Fin N → ℝ} (hσ : ∀ i, 0 < σ i) (hρ : ∀ i, 0 < ρ i)
    (heta : etaMix ρ σ < 1) {z : ℂ} (hz : z.im < 0) :
    (FMSA.MixtureNoSpinodal.Q0_mat_c_phys (Complex.I * z) σ ρ).det ≠ 0 := by
  obtain ⟨R, hR, hesc⟩ := exists_uniform_escape hσ hρ heta
  exact mixtureDet_pole_free_N_of_escape hσ hρ heta hR hesc hz

end
end FMSA.MixtureGenN
