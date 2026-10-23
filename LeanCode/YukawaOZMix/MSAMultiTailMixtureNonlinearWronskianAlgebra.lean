import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearFourier

/-! Finite rational residuals for the nonlinear source Wronskian.
This algebra keeps all pair contact phases and density orientations. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ}

def nonlinearPhaseQ (σ : Fin N → ℝ) (J L : Matrix (Fin N) (Fin N) ℂ)
    (s : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  s⁻¹ • (rdfPhase σ (-s)*L*rdfPhase σ s-rdfPhase σ s*J*rdfPhase σ s)

def nonlinearWronskianU (J L Jm Lm : Matrix (Fin N) (Fin N) ℂ)
    (d : Fin N → ℂ) (s : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  -L+Lm.transpose+s⁻¹ • (Jm*Matrix.diagonal d*J.transpose-L*Matrix.diagonal d*Lm.transpose)

def nonlinearWronskianV (J L Lm : Matrix (Fin N) (Fin N) ℂ)
    (d : Fin N → ℂ) (s : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  J-J.transpose+s⁻¹ • (J*Matrix.diagonal d*Lm.transpose-Lm*Matrix.diagonal d*J.transpose)

theorem nonlinearPhaseQ_entry (σ : Fin N → ℝ) (J L : Matrix (Fin N) (Fin N) ℂ)
    (s : ℂ) (i j : Fin N) :
    nonlinearPhaseQ σ J L s i j=
      (Complex.exp (s*(σ i : ℂ)/2)*L i j*Complex.exp (-s*(σ j : ℂ)/2)-
        Complex.exp (-s*(σ i : ℂ)/2)*J i j*Complex.exp (-s*(σ j : ℂ)/2))/s := by
  simp only [nonlinearPhaseQ, Matrix.smul_apply, smul_eq_mul, inv_mul_eq_div,
    Matrix.sub_apply, rdfPhase, Matrix.diagonal_mul, Matrix.mul_diagonal, neg_neg]

theorem nonlinear_wronskian_cross_scalar (a b c d e f j l jm jmi lm lmt jt s : ℂ)
    (hs : s ≠ 0) (hef : e*f=1) :
    -((b*l*e-a*j*e)/s)*(f*jm*d)+((-a*lm*f+b*jmi*f)/s)*(e*jt*c)+
      s*((b*l*e-a*j*e)/s)*((-c*lmt*f+d*jm*f)/s)=
      b*((jmi*jt-l*lmt)/s)*c+a*((j*lmt-lm*jt)/s)*c := by
  calc
    _ = (e*f)*(b*((jmi*jt-l*lmt)/s)*c+a*((j*lmt-lm*jt)/s)*c) := by
      field_simp [hs]
      <;> ring
    _ = _ := by rw [hef, one_mul]

theorem nonlinear_wronskian_linear_scalar (a b c d j jt l lmt jm s : ℂ)
    (hs : s ≠ 0) :
    b*jm*d-a*jt*c-s*((b*l*c-a*j*c)/s-(b*lmt*c-b*jm*d)/s)=
      b*(-l+lmt)*c+a*(j-jt)*c := by field_simp [hs]; ring

/-- Exact matrix Wronskian residual. Only two rational matrix residuals
remain after cancelling all intermediate species contact phases. -/
theorem nonlinear_phase_wronskian_residual (σ : Fin N → ℝ)
    (J L Jm Lm : Matrix (Fin N) (Fin N) ℂ) (d : Fin N → ℂ)
    (s : ℂ) (hs : s ≠ 0) :
    (1-nonlinearPhaseQ σ J L s*Matrix.diagonal d)*
        (rdfPhase σ (-s)*Jm.transpose*rdfPhase σ (-s))-
      (1-nonlinearPhaseQ σ Jm Lm (-s)*Matrix.diagonal d)*
        (rdfPhase σ s*J.transpose*rdfPhase σ s)-
      s • (nonlinearPhaseQ σ J L s+(nonlinearPhaseQ σ Jm Lm (-s)).transpose-
        nonlinearPhaseQ σ J L s*Matrix.diagonal d*(nonlinearPhaseQ σ Jm Lm (-s)).transpose)=
      rdfPhase σ (-s)*nonlinearWronskianU J L Jm Lm d s*rdfPhase σ s+
        rdfPhase σ s*nonlinearWronskianV J L Lm d s*rdfPhase σ s := by
  ext i j
  simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.transpose_apply,
    Matrix.mul_apply (M := nonlinearPhaseQ σ J L s*Matrix.diagonal d),
    Matrix.mul_apply (M := nonlinearPhaseQ σ Jm Lm (-s)*Matrix.diagonal d)]
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, rdfPhase, Matrix.transpose_apply,
    neg_neg, nonlinearWronskianU, nonlinearWronskianV, Matrix.add_apply,
    Matrix.neg_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_apply (M := Jm*Matrix.diagonal d), Matrix.mul_apply (M := L*Matrix.diagonal d),
    Matrix.mul_apply (M := J*Matrix.diagonal d), Matrix.mul_apply (M := Lm*Matrix.diagonal d)]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, nonlinearPhaseQ_entry,
    neg_neg, div_neg, neg_div]
  let a := Complex.exp (-s*(σ i : ℂ)/2)
  let b := Complex.exp (s*(σ i : ℂ)/2)
  let c := Complex.exp (-s*(σ j : ℂ)/2)
  let v := Complex.exp (s*(σ j : ℂ)/2)
  have hef (m : Fin N) : Complex.exp (-s*(σ m : ℂ)/2)*Complex.exp (s*(σ m : ℂ)/2)=1 := by
    rw [← Complex.exp_add, show -s*(σ m : ℂ)/2+s*(σ m : ℂ)/2=0 by ring, Complex.exp_zero]
  have ht (m : Fin N) := nonlinear_wronskian_cross_scalar a b c v
    (Complex.exp (-s*(σ m : ℂ)/2)) (Complex.exp (s*(σ m : ℂ)/2))
    (J i m) (L i m) (Jm j m) (Jm i m) (Lm i m) (Lm j m) (J j m) s hs (hef m)
  have hl := nonlinear_wronskian_linear_scalar a b c v (J i j) (J j i)
    (L i j) (Lm j i) (Jm j i) s hs
  dsimp only [a, b, c, v] at ht hl
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun m (_ : m ∈ Finset.univ) =>
    congrArg (fun x : ℂ => d m*x) (ht m))
  linear_combination (norm := skip) hl+hsum
  simp only [div_eq_mul_inv, mul_add, mul_sub, add_mul, sub_mul,
    neg_mul, mul_neg, Finset.mul_sum, Finset.sum_mul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  ring_nf
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro m _
  ring

end FMSA.ExactMSA.MultiTailMixture
