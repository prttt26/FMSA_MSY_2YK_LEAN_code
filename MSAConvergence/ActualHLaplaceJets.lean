import MSAConvergence.ActualLaplaceJets

/-! Actual positive-radial h moment Laplace families and amplitude jets.
Fixed additive contacts and their affine core background remain explicit. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open scoped BigOperators ContDiff

namespace FMSA.Convergence.ActualHLaplaceJets
open FMSA.Paper FMSA.Paper.ActualRDFParameters FMSA.Paper.JacobianExterior
open FMSA.Convergence.ActualRDFTangent FMSA.Convergence.RDFExponentialOrder
open FMSA.Convergence.ActualLaplaceJets
open FMSA.ExactMSA.MultiTailMixture FMSA.ExactMSA.Breakpoint MSAMixture

/-- A causal shift is exactly the fixed-contact positive indicator. -/
theorem causalShift_eq_indicator (f : ℝ → ℝ) (R r : ℝ) :
    causalShift f R r = (Ici R).indicator (fun x => f (x-R)) r := by
  by_cases hr : R ≤ r
  · simp only [causalShift, causalFull, indicator_of_mem (show r-R ∈ Ici (0 : ℝ) from sub_nonneg.mpr hr),
      indicator_of_mem (show r ∈ Ici R from hr)]
  · simp only [causalShift, causalFull, indicator_of_notMem (show r-R ∉ Ici (0 : ℝ) from by simpa using hr),
      indicator_of_notMem (show r ∉ Ici R from hr)]

/-- Absolute integrability of a genuine damped causal field survives an
arbitrary fixed real shift, on the full real line. -/
theorem causalShift_laplace_integrable (f : ℝ → ℝ) (R : ℝ) (s : ℂ)
    (hi : IntegrableOn (fun r : ℝ => (f r : ℂ) * Complex.exp (-s*r)) (Ioi 0)) :
    Integrable (fun r : ℝ => (causalShift f R r : ℂ) * Complex.exp (-s*r)) := by
  let phi : ℝ → ℂ := fun r => (f r : ℂ) * Complex.exp (-s*r)
  have hfull : Integrable ((Ici (0 : ℝ)).indicator phi) :=
    ((integrableOn_Ici_iff_integrableOn_Ioi).mpr hi).integrable_indicator measurableSet_Ici
  have hshift : Integrable (fun r : ℝ => (Ici (0 : ℝ)).indicator phi (r-R)) := by
    have h := (measurePreserving_add_right volume (-R)).integrable_comp_of_integrable hfull
    convert! h using 1
  have he : (fun r : ℝ => (causalShift f R r : ℂ) * Complex.exp (-s*r)) =
      fun r => Complex.exp (-s*(R : ℂ)) * (Ici (0 : ℝ)).indicator phi (r-R) := by
    funext r
    by_cases hr : r-R ∈ Ici (0 : ℝ)
    · simp only [causalShift, causalFull, indicator_of_mem hr]
      dsimp only [phi]
      have hex : Complex.exp (-s*(r : ℂ)) = Complex.exp (-s*(R : ℂ)) * Complex.exp (-s*((r-R : ℝ) : ℂ)) := by
        rw [← Complex.exp_add]
        push_cast
        congr 1
        ring
      rw [hex]
      ring
    · simp only [causalShift, causalFull, indicator_of_notMem hr, Complex.ofReal_zero, zero_mul, mul_zero]
  rw [he]
  exact hshift.const_mul _

variable {N : ℕ} {T : Type*} [Fintype T]

/-- The existing actual h moment is a fixed negative affine core background
plus the contact-shifted actual causal G, including the contact point. -/
theorem weighted_h_positive_shift (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (i j : Fin N) (hR : 0 < edgeHi sigma i j)
    (r : ℝ) (hr : 0 < r) :
    r * nonlinearH z rho sigma p.1 p.2 i j r = -r +
      causalShift (fun u => nonlinearCausalG z rho sigma p.1 p.2 u i j) (edgeHi sigma i j) r := by
  by_cases hc : r < edgeHi sigma i j
  · rw [nonlinearH_hardcore z rho sigma p.1 p.2 i j r hr hc, causalShift_eq_zero_below _ _ _ hc]
    ring
  · rw [nonlinearH, nonlinearRDFMoment_outer z rho sigma p.1 p.2 i j hR r (not_lt.mp hc)]
    simp only [causalShift, causalFull,
      indicator_of_mem (show r-edgeHi sigma i j ∈ Ici (0 : ℝ) from sub_nonneg.mpr (not_lt.mp hc)),
      nonlinearCausalG, Matrix.of_apply]
    field_simp [hr.ne']
    ring

/-- The actual h variation has exactly the fixed contact shift of the
existing genuine causal variation, without a moving-contact derivative. -/
theorem weighted_hVariation_positive_shift (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) (hR : 0 < edgeHi sigma i j)
    (r : ℝ) (hr : 0 < r) :
    r * hVariation z rho sigma p v i j r =
      causalShift (causalVariation z rho sigma p v i j) (edgeHi sigma i j) r := by
  rw [weighted_hVariation_positive_indicator z rho sigma p v i j hR r hr, causalShift_eq_indicator]

def hMomentLaplace (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (s : ℂ) (i j : Fin N) : ℂ :=
  FMSA.causalComplexLaplace (fun r => r * nonlinearH z rho sigma p.1 p.2 i j r) s

/-- The actual h moment has a genuine integral and the exact affine-core
formula whenever the actual causal G has a genuine damped integral. -/
theorem hMomentLaplace_of_causal_integrable (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (i j : Fin N) (hR : 0 < edgeHi sigma i j)
    (s : ℂ) (hs : 0 < s.re)
    (hi : IntegrableOn (fun r : ℝ => (nonlinearCausalG z rho sigma p.1 p.2 r i j : ℂ) *
      Complex.exp (-s*r)) (Ioi 0)) :
    IntegrableOn (fun r : ℝ => ((r * nonlinearH z rho sigma p.1 p.2 i j r : ℝ) : ℂ) *
      Complex.exp (-s*r)) (Ioi 0) ∧
    hMomentLaplace z rho sigma p s i j = -1/s^2 +
      Complex.exp (-s*(edgeHi sigma i j : ℂ)) *
        rdfMatrixLaplace (nonlinearCausalG z rho sigma p.1 p.2) s i j := by
  let Y : ℝ → ℝ := fun u => nonlinearCausalG z rho sigma p.1 p.2 u i j
  let S := causalShift Y (edgeHi sigma i j)
  have hS : IntegrableOn (fun r : ℝ => (S r : ℂ) * Complex.exp (-s*r)) (Ioi 0) :=
    (causalShift_laplace_integrable Y _ s hi).integrableOn
  have heA : (fun r : ℝ => (-r : ℂ) * Complex.exp (-s*r)) =
      fun r : ℝ => -((r : ℂ) * Complex.exp (-s*r)) := by
    funext r
    ring
  have hA : IntegrableOn (fun r : ℝ => (-r : ℂ) * Complex.exp (-s*r)) (Ioi 0) := by
    rw [heA]
    exact (FMSA.complex_first_integrable hs).neg
  have he : ∀ r ∈ Ioi (0 : ℝ), ((r * nonlinearH z rho sigma p.1 p.2 i j r : ℝ) : ℂ) * Complex.exp (-s*r) =
      (-r : ℂ) * Complex.exp (-s*r) + (S r : ℂ) * Complex.exp (-s*r) := by
    intro r hr
    rw [weighted_h_positive_shift z rho sigma p i j hR r hr]
    dsimp only [S, Y]
    push_cast
    ring
  constructor
  · exact (hA.add hS).congr_fun (fun r hr => (he r hr).symm) measurableSet_Ioi
  · unfold hMomentLaplace FMSA.causalComplexLaplace
    have hsplit : (∫ r in Ioi (0 : ℝ), ((r * nonlinearH z rho sigma p.1 p.2 i j r : ℝ) : ℂ) * Complex.exp (-s*r)) =
        (∫ r in Ioi (0 : ℝ), (-r : ℂ) * Complex.exp (-s*r)) +
          ∫ r in Ioi (0 : ℝ), (S r : ℂ) * Complex.exp (-s*r) := by
      rw [← integral_add hA hS]
      exact setIntegral_congr_fun measurableSet_Ioi he
    rw [hsplit]
    have hneg : (∫ r in Ioi (0 : ℝ), (-r : ℂ) * Complex.exp (-s*r)) = -1/s^2 := by
      rw [heA, integral_neg, FMSA.complex_first_Ioi hs]
      ring
    rw [hneg, causalShift_positive_complex_laplace Y _ hR s]
    rfl

/-- The existing genuine h variation has a true damped integral and an exact
scalar shift factor whenever its actual causal tangent does. -/
theorem hVariation_laplace_shift (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) (hR : 0 < edgeHi sigma i j)
    (s : ℂ) (hi : IntegrableOn (fun r : ℝ => (causalVariation z rho sigma p v i j r : ℂ) *
      Complex.exp (-s*r)) (Ioi 0)) :
    IntegrableOn (fun r : ℝ => ((r * hVariation z rho sigma p v i j r : ℝ) : ℂ) * Complex.exp (-s*r)) (Ioi 0) ∧
    FMSA.causalComplexLaplace (fun r => r * hVariation z rho sigma p v i j r) s =
      Complex.exp (-s*(edgeHi sigma i j : ℂ)) *
        rdfMatrixLaplace (fun r => Matrix.of (fun a b => causalVariation z rho sigma p v a b r)) s i j := by
  let S := causalShift (causalVariation z rho sigma p v i j) (edgeHi sigma i j)
  have hS : IntegrableOn (fun r : ℝ => (S r : ℂ) * Complex.exp (-s*r)) (Ioi 0) :=
    (causalShift_laplace_integrable _ _ s hi).integrableOn
  constructor
  · apply hS.congr_fun _ measurableSet_Ioi
    intro r hr
    dsimp only
    rw [weighted_hVariation_positive_shift z rho sigma p v i j hR r hr]
  · unfold FMSA.causalComplexLaplace
    have he : (∫ r in Ioi (0 : ℝ), ((r * hVariation z rho sigma p v i j r : ℝ) : ℂ) * Complex.exp (-s*r)) =
        ∫ r in Ioi (0 : ℝ), (S r : ℂ) * Complex.exp (-s*r) :=
      setIntegral_congr_fun measurableSet_Ioi (fun r hr => by
        rw [weighted_hVariation_positive_shift z rho sigma p v i j hR r hr])
    rw [he, causalShift_positive_complex_laplace _ _ hR s]
    rfl

/-- A common amplitude neighbourhood gives genuine actual h-moment
integrals and their off-root affine-core representation in a far half-plane. -/
theorem actual_hMoment_local_laplace
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (p : TailMatrix T N × TailMatrix T N) :
    ∃ cutoff : ℝ, 0 < cutoff ∧ ∀ s : ℂ, cutoff < s.re → ∀ᶠ a in 𝓝 p, ∀ i j,
      IntegrableOn (fun r : ℝ => ((r * nonlinearH z rho sigma a.1 a.2 i j r : ℝ) : ℂ) *
        Complex.exp (-s*r)) (Ioi 0) ∧
      hMomentLaplace z rho sigma a s i j = -1/s^2 + Complex.exp (-s*(edgeHi sigma i j : ℂ)) *
        rdfMatrixLaplace (nonlinearCausalG z rho sigma a.1 a.2) s i j := by
  obtain ⟨gamma, B, hg, _, hb⟩ := actual_causal_local_exponential_order
    z hz rho sigma (fun i => (hsigma i).le) p
  refine ⟨gamma, hg, ?_⟩
  intro s hs
  filter_upwards [hb] with a ha
  intro i j
  have hR : 0 < edgeHi sigma i j := by unfold edgeHi; linarith [hsigma i, hsigma j]
  have hi : IntegrableOn (fun r : ℝ => (nonlinearCausalG z rho sigma a.1 a.2 r i j : ℂ) *
      Complex.exp (-s*r)) (Ioi 0) := by
    apply exp_order_complex_integrable _
      ((nonlinearCausalG_continuous z rho sigma a.1 a.2).matrix_elem i j).aestronglyMeasurable gamma B _ s hs
    intro r hr
    exact (mul_le_mul_of_nonneg_left (FMSA.matrixAbsSum_entry_le _ i j) (exp_pos _).le).trans (ha r hr.le)
  exact hMomentLaplace_of_causal_integrable z rho sigma a i j hR s (hg.trans hs) hi

/-- The actual h moment Laplace family is genuinely amplitude-smooth and
its whole-integral Frechet derivative is the integral of r*delta h, with
one cutoff for all amplitude directions. The affine core derivative is zero. -/
theorem actual_hMoment_laplace_jets
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (p : TailMatrix T N × TailMatrix T N) :
    ∃ cutoff : ℝ, 0 < cutoff ∧ ∀ s : ℂ, cutoff < s.re → ∀ i j,
      IntegrableOn (fun r : ℝ => ((r * nonlinearH z rho sigma p.1 p.2 i j r : ℝ) : ℂ) *
        Complex.exp (-s*r)) (Ioi 0) ∧
      ContDiffAt ℝ ∞ (fun a : TailMatrix T N × TailMatrix T N => hMomentLaplace z rho sigma a s i j) p ∧
      ∀ v : TailMatrix T N × TailMatrix T N,
        IntegrableOn (fun r : ℝ => ((r * hVariation z rho sigma p v i j r : ℝ) : ℂ) * Complex.exp (-s*r)) (Ioi 0) ∧
        FMSA.causalComplexLaplace (fun r => r * hVariation z rho sigma p v i j r) s =
          fderiv ℝ (fun a : TailMatrix T N × TailMatrix T N => hMomentLaplace z rho sigma a s i j) p v ∧
        fderiv ℝ (fun a : TailMatrix T N × TailMatrix T N => hMomentLaplace z rho sigma a s i j) p v =
          Complex.exp (-s*(edgeHi sigma i j : ℂ)) * fderiv ℝ
            (fun a : TailMatrix T N × TailMatrix T N =>
              rdfMatrixLaplace (nonlinearCausalG z rho sigma a.1 a.2) s i j) p v := by
  obtain ⟨c0, hc0, hrep⟩ := actual_hMoment_local_laplace z hz rho sigma hsigma p
  obtain ⟨c1, _, hG⟩ := actual_causal_laplace_fderiv_all_directions
    z hz rho sigma (fun i => (hsigma i).le) p
  refine ⟨max c0 c1, lt_of_lt_of_le hc0 (le_max_left _ _), ?_⟩
  intro s hs i j
  have hs0 : c0 < s.re := (le_max_left _ _).trans_lt hs
  have hs1 : c1 < s.re := (le_max_right _ _).trans_lt hs
  obtain ⟨hGreg, hGvar⟩ := hG s hs1
  have he : (fun a : TailMatrix T N × TailMatrix T N => hMomentLaplace z rho sigma a s i j) =ᶠ[𝓝 p]
      fun a => -1/s^2 + Complex.exp (-s*(edgeHi sigma i j : ℂ)) *
        rdfMatrixLaplace (nonlinearCausalG z rho sigma a.1 a.2) s i j :=
    (hrep s hs0).mono (fun a ha => (ha i j).2)
  have hreg : ContDiffAt ℝ ∞ (fun a : TailMatrix T N × TailMatrix T N =>
      -1/s^2 + Complex.exp (-s*(edgeHi sigma i j : ℂ)) *
        rdfMatrixLaplace (nonlinearCausalG z rho sigma a.1 a.2) s i j) p :=
    contDiffAt_const.add (contDiffAt_const.mul (hGreg i j))
  have hR : 0 < edgeHi sigma i j := by unfold edgeHi; linarith [hsigma i, hsigma j]
  have hder (v : TailMatrix T N × TailMatrix T N) :
      fderiv ℝ (fun a : TailMatrix T N × TailMatrix T N => hMomentLaplace z rho sigma a s i j) p v =
        Complex.exp (-s*(edgeHi sigma i j : ℂ)) * fderiv ℝ
          (fun a : TailMatrix T N × TailMatrix T N =>
            rdfMatrixLaplace (nonlinearCausalG z rho sigma a.1 a.2) s i j) p v := by
    have hd := (hasFDerivAt_const (-1/s^2) p).fun_add
      (((hGreg i j).differentiableAt (by simp)).hasFDerivAt.const_mul
        (Complex.exp (-s*(edgeHi sigma i j : ℂ))))
    have hh := congrArg (fun L : (TailMatrix T N × TailMatrix T N) →L[ℝ] ℂ => L v)
      (he.fderiv_eq.trans hd.fderiv)
    simpa only [add_apply, zero_apply, smul_apply, smul_eq_mul, zero_add] using hh
  refine ⟨((hrep s hs0).self_of_nhds i j).1, hreg.congr_of_eventuallyEq he, ?_⟩
  intro v
  obtain ⟨hi, hv⟩ := hVariation_laplace_shift z rho sigma p v i j hR s (hGvar v i j).1
  refine ⟨hi, ?_, hder v⟩
  rw [hv, (hGvar v i j).2]
  exact (hder v).symm

/-- For the frozen additive contact R_ij=(sigma_i+sigma_j)/2, the scalar
contact multipliers equal the existing diagonal matrix phase sandwich.
No such matrix factorization is asserted for non-additive contacts. -/
theorem additive_contact_phase_sandwich (sigma : Fin N → ℝ) (s : ℂ)
    (X : Matrix (Fin N) (Fin N) ℂ) :
    Matrix.of (fun i j => Complex.exp (-s*(edgeHi sigma i j : ℂ)) * X i j) =
      rdfPhase sigma s * X * rdfPhase sigma s := by
  ext i j
  simp only [rdfPhase, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply]
  rw [← rdfPhase_contact_product sigma s i j]
  ring

/-- Actual integrated h tangents have the genuine causal-G Laplace derivative
as their additive-contact phase transfer, uniformly over all directions. -/
theorem actual_hVariation_laplace_phase
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (p : TailMatrix T N × TailMatrix T N) :
    ∃ cutoff : ℝ, 0 < cutoff ∧ ∀ s : ℂ, cutoff < s.re → ∀ v : TailMatrix T N × TailMatrix T N,
      rdfMatrixLaplace (fun r => Matrix.of (fun i j => r * hVariation z rho sigma p v i j r)) s =
        rdfPhase sigma s * Matrix.of (fun i j => fderiv ℝ
          (fun a : TailMatrix T N × TailMatrix T N =>
            rdfMatrixLaplace (nonlinearCausalG z rho sigma a.1 a.2) s i j) p v) * rdfPhase sigma s := by
  obtain ⟨cutoff, hc, hj⟩ := actual_hMoment_laplace_jets z hz rho sigma hsigma p
  refine ⟨cutoff, hc, ?_⟩
  intro s hs v
  rw [← additive_contact_phase_sandwich]
  ext i j
  change FMSA.causalComplexLaplace (fun r => r * hVariation z rho sigma p v i j r) s = _
  exact (((hj s hs i j).2.2 v).2.1).trans (((hj s hs i j).2.2 v).2.2)

/-- The actual integrated h tangent equals the explicit finite source/kernel
resolvent response in one computed right half-plane, for every direction.
This eliminates the unknown G transform while retaining all matrix orders. -/
theorem actual_hVariation_laplace_resolvent
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (p : TailMatrix T N × TailMatrix T N) :
    ∃ cutoff : ℝ, 0 < cutoff ∧ ∀ s : ℂ, cutoff < s.re → ∀ v : TailMatrix T N × TailMatrix T N,
      rdfMatrixLaplace (fun r => Matrix.of (fun i j => r * hVariation z rho sigma p v i j r)) s =
        rdfPhase sigma s *
          ((rdfMatrixLaplace (fun r => Matrix.of (fun i j => sourceVariation z rho sigma p v i j r)) s +
            rdfMatrixLaplace (nonlinearGSource z rho sigma p.1 p.2) s *
              (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)⁻¹ *
                rdfMatrixLaplace (fun r => Matrix.of (fun i j => kernelVariation z rho sigma p v i j r)) s) *
            (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)⁻¹) * rdfPhase sigma s := by
  obtain ⟨c0, hc0, hphase⟩ := actual_hVariation_laplace_phase z hz rho sigma hsigma p
  obtain ⟨c1, _, hrep⟩ := actual_local_laplace_renewal_unit z hz rho sigma (fun i => (hsigma i).le) p
  obtain ⟨c2, _, hreg⟩ := actual_causal_laplace_contDiffAt z hz rho sigma (fun i => (hsigma i).le) p
  refine ⟨max c0 (max c1 c2), lt_of_lt_of_le hc0 (le_max_left _ _), ?_⟩
  intro s hs v
  have hs0 : c0 < s.re := (le_max_left _ _).trans_lt hs
  have hs1 : c1 < s.re := (le_trans (le_max_left _ _) (le_max_right _ _)).trans_lt hs
  have hs2 : c2 < s.re := (le_trans (le_max_right _ _) (le_max_right _ _)).trans_lt hs
  have hsr : 0 < s.re := hc0.trans hs0
  let q := fun a : TailMatrix T N × TailMatrix T N => rdfMatrixLaplace (nonlinearCausalKernel z rho sigma a.1 a.2) s
  let f := fun a : TailMatrix T N × TailMatrix T N => rdfMatrixLaplace (nonlinearGSource z rho sigma a.1 a.2) s
  let y := fun a : TailMatrix T N × TailMatrix T N => rdfMatrixLaplace (nonlinearCausalG z rho sigma a.1 a.2) s
  let A := 1-q p
  let dF := rdfMatrixLaplace (fun r => Matrix.of (fun i j => sourceVariation z rho sigma p v i j r)) s
  let dQ := rdfMatrixLaplace (fun r => Matrix.of (fun i j => kernelVariation z rho sigma p v i j r)) s
  let dY := Matrix.of (fun i j => fderiv ℝ (fun a => y a i j) p v)
  have hu : IsUnit A := (hrep s hs1).self_of_nhds.2
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp hu
  have hy : y p = f p * A⁻¹ := by
    calc
      _ = (y p * A) * A⁻¹ := (Matrix.mul_nonsing_inv_cancel_right A (y p) hdet).symm
      _ = _ := by rw [(hrep s hs1).self_of_nhds.1]
  have he : ∀ᶠ a in 𝓝 p, y a * (1-q a) = f a := (hrep s hs1).mono (fun _ h => h.1)
  have hd := matrix_renewal_family_fderiv q f y p v
    (fun i j => (kernel_laplace_contDiff z hz rho sigma (fun i => (hsigma i).le) s hsr i j).differentiable (by simp) p)
    (fun i j => (source_laplace_contDiff z hz rho sigma s hsr i j).differentiable (by simp) p)
    (fun i j => (hreg s hs2 i j).differentiableAt (by simp)) he
  have hq : Matrix.of (fun i j => fderiv ℝ (fun a => q a i j) p v) = dQ := by
    ext i j
    exact (kernelVariation_laplace z hz rho sigma (fun i => (hsigma i).le) p v s hsr i j).symm
  have hf : Matrix.of (fun i j => fderiv ℝ (fun a => f a i j) p v) = dF := by
    ext i j
    exact (sourceVariation_laplace z hz rho sigma p v s hsr i j).symm
  rw [hq, hf] at hd
  have hdy : dY = (dF + f p * A⁻¹ * dQ) * A⁻¹ := by
    calc
      _ = (dY * A) * A⁻¹ := (Matrix.mul_nonsing_inv_cancel_right A dY hdet).symm
      _ = (dF + y p * dQ) * A⁻¹ := by rw [hd]
      _ = _ := by rw [hy]
  rw [hphase s hs0 v]
  change rdfPhase sigma s * dY * rdfPhase sigma s =
    rdfPhase sigma s * ((dF + f p * A⁻¹ * dQ) * A⁻¹) * rdfPhase sigma s
  rw [hdy]

end FMSA.Convergence.ActualHLaplaceJets

/-- info: 'FMSA.Convergence.ActualHLaplaceJets.causalShift_eq_indicator' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualHLaplaceJets.causalShift_eq_indicator

/-- info: 'FMSA.Convergence.ActualHLaplaceJets.causalShift_laplace_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualHLaplaceJets.causalShift_laplace_integrable

/-- info: 'FMSA.Convergence.ActualHLaplaceJets.weighted_h_positive_shift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualHLaplaceJets.weighted_h_positive_shift

/-- info: 'FMSA.Convergence.ActualHLaplaceJets.weighted_hVariation_positive_shift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualHLaplaceJets.weighted_hVariation_positive_shift

/-- info: 'FMSA.Convergence.ActualHLaplaceJets.hMomentLaplace_of_causal_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualHLaplaceJets.hMomentLaplace_of_causal_integrable

/-- info: 'FMSA.Convergence.ActualHLaplaceJets.hVariation_laplace_shift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualHLaplaceJets.hVariation_laplace_shift

/-- info: 'FMSA.Convergence.ActualHLaplaceJets.actual_hMoment_local_laplace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualHLaplaceJets.actual_hMoment_local_laplace

/-- info: 'FMSA.Convergence.ActualHLaplaceJets.actual_hMoment_laplace_jets' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualHLaplaceJets.actual_hMoment_laplace_jets

/-- info: 'FMSA.Convergence.ActualHLaplaceJets.additive_contact_phase_sandwich' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualHLaplaceJets.additive_contact_phase_sandwich

/-- info: 'FMSA.Convergence.ActualHLaplaceJets.actual_hVariation_laplace_phase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualHLaplaceJets.actual_hVariation_laplace_phase

/-- info: 'FMSA.Convergence.ActualHLaplaceJets.actual_hVariation_laplace_resolvent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualHLaplaceJets.actual_hVariation_laplace_resolvent
