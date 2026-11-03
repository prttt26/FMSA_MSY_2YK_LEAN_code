import MSAConvergence.TracerEnergyYoung

/-! Exact integrated physical tracer-row c h energy split, with every
integrability obligation discharged from the actual radial L1/L2 fields. -/
noncomputable section
open MeasureTheory Real FMSA.HardSphere FMSA.ExactMSA.MultiTailMixture MSAMixture
open FMSA.Convergence.TracerCoreTrialField FMSA.Convergence.TracerTailSpectralBound
open FMSA.Convergence.TracerSpectralL2 FMSA.Convergence.CanonicalInverseCovariance
open FMSA.Paper FMSA.Paper.ActualRDFParameters
open scoped BigOperators
namespace FMSA.Convergence.TracerIntegratedEnergyIdentity
variable {N : ℕ} {T : Type*} [Fintype T]

def rowEnergy (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (K D G : TailMatrix T N) (i : Fin N) (w : ℝ) : ℝ :=
  ∑ j : Fin N, rho j *
    (w^2*radial_fourier (orderedRadialCorrelation z rho sigma K D G i j) (2*Real.pi*w)*
      radial_fourier (nonlinearH z rho sigma D G i j) (2*Real.pi*w))

def rowCoreForcing (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (K D G : TailMatrix T N) (i : Fin N) (w : ℝ) : ℝ :=
  ∑ j : Fin N, rho j *
    (w^2*radial_fourier (orderedRadialCorrelation z rho sigma K D G i j) (2*Real.pi*w)*
      radial_fourier (coreValue (edgeHi sigma i j)) (2*Real.pi*w))

def rowTailForcing (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (K D G : TailMatrix T N) (i : Fin N) (w : ℝ) : ℝ :=
  ∑ j : Fin N, rho j *
    (w^2*radial_fourier
      (tailField z (edgeHi sigma i j) (fun u => K u i j)) (2*Real.pi*w)*
      radial_fourier (nonlinearH z rho sigma D G i j) (2*Real.pi*w))

/-- Two genuine frequency-weighted radial L2 fields have an integrable
spectral product, with the physical w-squared normalization. -/
theorem weighted_radial_pair_integrable (f g : ℝ → ℝ)
    (hf : MemLp (fun w : ℝ => w*radial_fourier f (2*Real.pi*w)) 2 volume)
    (hg : MemLp (fun w : ℝ => w*radial_fourier g (2*Real.pi*w)) 2 volume) :
    Integrable (fun w : ℝ => w^2*radial_fourier f (2*Real.pi*w)*
      radial_fourier g (2*Real.pi*w)) := by
  have hi := hf.integrable_mul hg
  have he : (fun w : ℝ => w^2*radial_fourier f (2*Real.pi*w)*
      radial_fourier g (2*Real.pi*w)) =
      (fun w : ℝ => (w*radial_fourier f (2*Real.pi*w))*
        (w*radial_fourier g (2*Real.pi*w))) := by
    funext w; ring
  rw [he]
  exact hi

/-- The ACTUAL canonical c h row energy is integrable and its integral is
exactly the sum of the genuine hard-core and Yukawa-tail forcing integrals. -/
theorem actual_row_energy_integral_split (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hs : ∀ a, 0 < sigma a)
    (hv : FMSA.MatrixQ0.vacMix rho sigma ≠ 0)
    (K D G : TailMatrix T N) (hK : ∀ u a b, K u a b = K u b a)
    (hroot : IsRoot z rho sigma K D G)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit (causalFactor z rho sigma D G s))
    (i : Fin N) :
    Integrable (rowEnergy z rho sigma K D G i) ∧
    Integrable (rowCoreForcing z rho sigma K D G i) ∧
    Integrable (rowTailForcing z rho sigma K D G i) ∧
    (∫ w : ℝ, rowEnergy z rho sigma K D G i w) =
      (∫ w : ℝ, rowCoreForcing z rho sigma K D G i w) +
      (∫ w : ℝ, rowTailForcing z rho sigma K D G i w) := by
  let c (j : Fin N) := orderedRadialCorrelation z rho sigma K D G i j
  let h (j : Fin N) := nonlinearH z rho sigma D G i j
  let c0 (j : Fin N) := coreValue (edgeHi sigma i j)
  let t (j : Fin N) := tailField z (edgeHi sigma i j) (fun u => K u i j)
  have hc (j : Fin N) : MemLp (fun w : ℝ => w*radial_fourier (c j) (2*Real.pi*w)) 2 volume :=
    actual_c_weighted_spectral_memLp_two z hz rho sigma hs K D G hroot i j
  have hh (j : Fin N) : MemLp (fun w : ℝ => w*radial_fourier (h j) (2*Real.pi*w)) 2 volume :=
    actual_h_weighted_spectral_memLp_two z hz rho sigma hs hv D G hcanon i j
  have hc0 (j : Fin N) : MemLp (fun w : ℝ => w*radial_fourier (c0 j) (2*Real.pi*w)) 2 volume := by
    have hR : 0 < edgeHi sigma i j := by dsimp [edgeHi]; linarith [hs i,hs j]
    exact core_weighted_spectral_memLp_two (edgeHi sigma i j) hR
  have ht (j : Fin N) : MemLp (fun w : ℝ => w*radial_fourier (t j) (2*Real.pi*w)) 2 volume := by
    have hR : 0 < edgeHi sigma i j := by dsimp [edgeHi]; linarith [hs i,hs j]
    exact tail_field_weighted_spectral_memLp_two z hz (edgeHi sigma i j) hR (fun u => K u i j)
  have hE (j : Fin N) : Integrable (fun w : ℝ =>
      w^2*radial_fourier (c j) (2*Real.pi*w)*radial_fourier (h j) (2*Real.pi*w)) :=
    weighted_radial_pair_integrable (c j) (h j) (hc j) (hh j)
  have hC (j : Fin N) : Integrable (fun w : ℝ =>
      w^2*radial_fourier (c j) (2*Real.pi*w)*radial_fourier (c0 j) (2*Real.pi*w)) :=
    weighted_radial_pair_integrable (c j) (c0 j) (hc j) (hc0 j)
  have hT (j : Fin N) : Integrable (fun w : ℝ =>
      w^2*radial_fourier (t j) (2*Real.pi*w)*radial_fourier (h j) (2*Real.pi*w)) :=
    weighted_radial_pair_integrable (t j) (h j) (ht j) (hh j)
  have hEi : Integrable (rowEnergy z rho sigma K D G i) := by
    change Integrable (fun w : ℝ => ∑ j : Fin N, rho j*
      (w^2*radial_fourier (c j) (2*Real.pi*w)*radial_fourier (h j) (2*Real.pi*w)))
    exact integrable_finsetSum _ (fun j _ => (hE j).const_mul (rho j))
  have hCi : Integrable (rowCoreForcing z rho sigma K D G i) := by
    change Integrable (fun w : ℝ => ∑ j : Fin N, rho j*
      (w^2*radial_fourier (c j) (2*Real.pi*w)*radial_fourier (c0 j) (2*Real.pi*w)))
    exact integrable_finsetSum _ (fun j _ => (hC j).const_mul (rho j))
  have hTi : Integrable (rowTailForcing z rho sigma K D G i) := by
    change Integrable (fun w : ℝ => ∑ j : Fin N, rho j*
      (w^2*radial_fourier (t j) (2*Real.pi*w)*radial_fourier (h j) (2*Real.pi*w)))
    exact integrable_finsetSum _ (fun j _ => (hT j).const_mul (rho j))
  refine ⟨hEi,hCi,hTi,?_⟩
  have hpair (j : Fin N) :
      (∫ w : ℝ, w^2*radial_fourier (c j) (2*Real.pi*w)*
        radial_fourier (h j) (2*Real.pi*w)) =
      (∫ w : ℝ, w^2*radial_fourier (c j) (2*Real.pi*w)*
        radial_fourier (c0 j) (2*Real.pi*w))+
      (∫ w : ℝ, w^2*radial_fourier (t j) (2*Real.pi*w)*
        radial_fourier (h j) (2*Real.pi*w)) := by
    exact actual_spectral_pair_integral_split z hz rho sigma hs hv K D G
      hK hroot hcanon i j
  change (∫ w : ℝ, ∑ j : Fin N, rho j*
      (w^2*radial_fourier (c j) (2*Real.pi*w)*radial_fourier (h j) (2*Real.pi*w))) =
    (∫ w : ℝ, ∑ j : Fin N, rho j*
      (w^2*radial_fourier (c j) (2*Real.pi*w)*radial_fourier (c0 j) (2*Real.pi*w)))+
    (∫ w : ℝ, ∑ j : Fin N, rho j*
      (w^2*radial_fourier (t j) (2*Real.pi*w)*radial_fourier (h j) (2*Real.pi*w)))
  rw [integral_finsetSum _ (fun j _ => (hE j).const_mul (rho j)),
    integral_finsetSum _ (fun j _ => (hC j).const_mul (rho j)),
    integral_finsetSum _ (fun j _ => (hT j).const_mul (rho j))]
  simp_rw [integral_const_mul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [hpair j]
  ring

end FMSA.Convergence.TracerIntegratedEnergyIdentity
/-- info: 'FMSA.Convergence.TracerIntegratedEnergyIdentity.weighted_radial_pair_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerIntegratedEnergyIdentity.weighted_radial_pair_integrable
/-- info: 'FMSA.Convergence.TracerIntegratedEnergyIdentity.actual_row_energy_integral_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerIntegratedEnergyIdentity.actual_row_energy_integral_split
