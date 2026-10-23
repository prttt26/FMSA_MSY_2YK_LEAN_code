import LeanCode.YukawaOZMix.MSAMultiTailMixtureRDFReference

/-! Actual first-order matrix OZ for the constructed causal RDF. The only
reference-physics premise is zeroth-order OZ of the supplied actual HS RDF;
all first-order transforms, support and factor identities are proved. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

theorem rdfCausalTwoSided_laplace_product (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (K : TailMatrix ι N)
    (hU : ∀ i j, IntegrableOn (fun r => rdfCausalTwoSided z ρ σ K r i j) (Ioi 0))
    (s : ℂ) (hs : 0 ≤ s.re) :
    (rdfRecenteredFactor ρ σ s).transpose*
        rdfMatrixLaplace (rdfCausalTwoSided z ρ σ K) s*rdfRecenteredFactor ρ σ s =
      rdfMatrixLaplace (rdfCausalSource z ρ σ K) s := by
  have hY := rdfCausalLeft_integrableOn_of_twoSided z ρ σ K hU
  rw [Matrix.mul_assoc, rdfCausalTwoSided_laplace z ρ σ K hY hU s hs,
    rdfCausalLeft_laplace z hz ρ σ K hY s hs]

theorem rdfFirstOrderH_moment_sandwich (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hv : 0 < vacMix ρ σ) (hρ : ∀ i, 0 < ρ i)
    (hσ : ∀ i, 0 < σ i) (K : TailMatrix ι N)
    (hU : ∀ i j, IntegrableOn (fun r => rdfCausalTwoSided z ρ σ K r i j) (Ioi 0))
    (k : ℝ) (hk : k ≠ 0) :
    rdfReferenceT z ρ σ k*
        (rdfPhase σ (Complex.I*k)*rdfMatrixLaplace (rdfCausalTwoSided z ρ σ K) (Complex.I*k)*
          rdfPhase σ (Complex.I*k))*(rdfReferenceT z ρ σ k).transpose =
      Matrix.of (dpWFourier z ρ σ K k) := by
  let T := rdfReferenceT z ρ σ k
  let E := rdfPhase σ (Complex.I*k)
  let F := rdfRecenteredFactor ρ σ (Complex.I*k)
  let A := complexHSRightFactor ρ σ (-(Complex.I*k))*E
  have he : T*E=A*F.transpose := rdfReferenceT_phase z hz ρ σ hv hρ hσ k hk
  have het := congrArg Matrix.transpose he
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, E, rdfPhase,
    Matrix.diagonal_transpose] at het
  change E*T.transpose=F*A.transpose at het
  have hf := rdfCausalTwoSided_laplace_product z hz ρ σ K hU (Complex.I*k) (by simp)
  calc
    _ = (T*E)*rdfMatrixLaplace (rdfCausalTwoSided z ρ σ K) (Complex.I*k)*(E*T.transpose) := by
      simp only [T, E, Matrix.mul_assoc]
    _ = A*(F.transpose*rdfMatrixLaplace (rdfCausalTwoSided z ρ σ K) (Complex.I*k)*F)*A.transpose := by
      rw [he, het]
      simp only [Matrix.mul_assoc]
    _ = A*rdfMatrixLaplace (rdfCausalSource z ρ σ K) (Complex.I*k)*A.transpose := by rw [hf]
    _ = _ := by
      rw [dpWFourier_eq_HS_sandwich z hz ρ σ (fun i => (hσ i).le) K k hk,
        dpBFourier_eq_causalSource_phase]
      simp only [A, E, Matrix.transpose_mul, rdfPhase, Matrix.diagonal_transpose, Matrix.mul_assoc]

theorem rdfFirstOrderH_actual_sandwich (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hv : 0 < vacMix ρ σ) (hρ : ∀ i, 0 < ρ i)
    (hσ : ∀ i, 0 < σ i) (K : TailMatrix ι N)
    (hK : ∀ u i j, K u i j=K u j i)
    (hU : ∀ i j, IntegrableOn (fun r => rdfCausalTwoSided z ρ σ K r i j) (Ioi 0))
    (k : ℝ) (hk : k ≠ 0) :
    rdfReferenceT z ρ σ k*rdfFirstOrderH z ρ σ K k*(rdfReferenceT z ρ σ k).transpose =
      rdfFirstOrderC z ρ σ K k := by
  have hp := rdfFirstOrderH_moment_sandwich z hz ρ σ hv hρ hσ K hU k hk
  have hm := rdfFirstOrderH_moment_sandwich z hz ρ σ hv hρ hσ K hU (-k) (neg_ne_zero.mpr hk)
  have hTneg : rdfReferenceT z ρ σ (-k)=rdfReferenceT z ρ σ k := by
    simp only [rdfReferenceT, rdfReferenceC_neg]
  rw [hTneg] at hm
  simp only [Complex.ofReal_neg, mul_neg] at hm
  rw [rdfFirstOrderH_eq_phase_difference z ρ σ hσ K hU k hk,
    rdfFirstOrderC_eq_W_difference z hz ρ σ hv (fun i => (hρ i).le) hσ K hK k hk]
  simp only [mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul]
  rw [hp]
  change (1/(Complex.I*k)) • (_-Matrix.of (dpWFourier z ρ σ K k)) = _
  rw [hm]

theorem matrix_firstOrderOZ_of_sandwich
    (C0 H0 C1 H1 R : Matrix (Fin N) (Fin N) ℂ)
    (hC0 : C0.transpose=C0) (hR : R.transpose=R)
    (hzero : H0=C0+C0*R*H0)
    (hfirst : (1-C0*R)*H1*(1-C0*R).transpose=C1) :
    H1=C1+C0*R*H1+C1*R*H0 := by
  have hi : (1-C0*R).transpose*(1+R*H0)=1 := by
    simp only [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul, hC0, hR]
    have hz : H0-C0-C0*R*H0=0 := by
      calc
        _ = H0-(C0+C0*R*H0) := by abel
        _ = 0 := sub_eq_zero.mpr hzero
    calc
      _ = 1+R*(H0-C0-C0*R*H0) := by noncomm_ring
      _ = 1 := by rw [hz]; simp
  have he := congrArg (fun X => X*(1+R*H0)) hfirst
  simp only [Matrix.mul_assoc, hi, Matrix.mul_one] at he
  have he' : H1-C0*R*H1=C1+C1*R*H0 := by
    simpa only [sub_mul, Matrix.one_mul, mul_add, Matrix.mul_one, Matrix.mul_assoc] using he
  rw [sub_eq_iff_eq_add] at he'
  calc
    _ = C1+C1*R*H0+C0*R*H1 := he'
    _ = _ := by abel

/-- Actual radial Fourier integrals satisfy first-order OZ, conditional only
on decay of the constructed Uc and zeroth-order OZ of the supplied HS RDF.
No inverse transform or first-order RDF/OZ condition occurs as a premise. -/
theorem rdfFirstOrderCausal_actual_fourier_OZ (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hv : 0 < vacMix ρ σ) (hρ : ∀ i, 0 < ρ i)
    (hσ : ∀ i, 0 < σ i) (K : TailMatrix ι N)
    (hK : ∀ u i j, K u i j=K u j i)
    (hU : ∀ i j, IntegrableOn (fun r => rdfCausalTwoSided z ρ σ K r i j) (Ioi 0))
    (h0 : Fin N → Fin N → ℝ → ℝ) (k : ℝ) (hk : k ≠ 0)
    (hzero : Matrix.of (fun i j => (FMSA.HardSphere.radial_fourier (h0 i j) k : ℂ)) =
      rdfReferenceC z ρ σ k+rdfReferenceC z ρ σ k*Matrix.diagonal (fun i => (ρ i : ℂ))*
        Matrix.of (fun i j => (FMSA.HardSphere.radial_fourier (h0 i j) k : ℂ))) :
    rdfFirstOrderH z ρ σ K k = rdfFirstOrderC z ρ σ K k+
      rdfReferenceC z ρ σ k*Matrix.diagonal (fun i => (ρ i : ℂ))*rdfFirstOrderH z ρ σ K k+
        rdfFirstOrderC z ρ σ K k*Matrix.diagonal (fun i => (ρ i : ℂ))*
          Matrix.of (fun i j => (FMSA.HardSphere.radial_fourier (h0 i j) k : ℂ)) := by
  exact matrix_firstOrderOZ_of_sandwich _ _ _ _ _
    (rdfReferenceC_symmetric z hz ρ σ hv hρ hσ k hk) (Matrix.diagonal_transpose _) hzero
    (rdfFirstOrderH_actual_sandwich z hz ρ σ hv hρ hσ K hK hU k hk)

end FMSA.ExactMSA.MultiTailMixture
