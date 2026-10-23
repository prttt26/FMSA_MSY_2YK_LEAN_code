import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearReciprocity

/-! Algebraic Yukawa-pole cancellation from the actual two BH root blocks.
No symmetry of the unknown `G`, contact selection, density inverse, or
Wronskian certificate is assumed. These identities remove the finite Yukawa
poles; the remaining origin and polynomial terms still require a proof. -/
noncomputable section
open Real FMSA.MatrixQ0 MSAMixture FMSA.ExactMSA.Breakpoint
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ}

/-- The second root block and the tail cancellation share the same ordered
matrix product. The first root block supplies the only symmetry used here. -/
theorem bh_matrix_pole_cancellation {R : Type*} [CommRing R]
    (P E D H Q : Matrix (Fin N) (Fin N) R)
    (hP : P.transpose=P)
    (hB : (D*(1-P*Q.transpose)).transpose=D*(1-P*Q.transpose)) :
    let W := H*P*D
    let C := D-E*W
    let J := H*(1-P*Q)
    let L := Q+E*J
    (W.transpose-C*P*J.transpose-L*P*W.transpose=0) ∧
    (W-J*P*C.transpose-W*P*L.transpose=0) ∧
    (J*P*W.transpose-W*P*J.transpose=0) ∧
    (C-C.transpose+L*P*C.transpose-C*P*L.transpose=0) := by
  let B := D*(1-P*Q.transpose)
  let W := H*P*D
  let C := D-E*W
  let J := H*(1-P*Q)
  let L := Q+E*J
  change (W.transpose-C*P*J.transpose-L*P*W.transpose=0) ∧
    (W-J*P*C.transpose-W*P*L.transpose=0) ∧
    (J*P*W.transpose-W*P*J.transpose=0) ∧
    (C-C.transpose+L*P*C.transpose-C*P*L.transpose=0)
  have hb : B.transpose=B := hB
  have hv : J*P*W.transpose-W*P*J.transpose=
      H*P*(B.transpose-B)*P*H.transpose := by
    dsimp [J, W, B]
    simp only [Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_one,
      Matrix.transpose_transpose, hP]
    noncomm_ring
  have hu : W.transpose-C*P*J.transpose-L*P*W.transpose=
      (1-E*H*P)*(B.transpose-B)*P*H.transpose := by
    dsimp [J, W, C, L, B]
    simp only [Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_one,
      Matrix.transpose_transpose, hP]
    noncomm_ring
  have hv0 : J*P*W.transpose-W*P*J.transpose=0 := by
    rw [hv, hb, sub_self, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_mul]
  have hu0 : W.transpose-C*P*J.transpose-L*P*W.transpose=0 := by
    rw [hu, hb, sub_self, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_mul]
  have hum : W-J*P*C.transpose-W*P*L.transpose=0 := by
    have ht := congrArg Matrix.transpose hu0
    simpa only [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_zero, hP, Matrix.mul_assoc] using ht
  have hc : C-C.transpose+L*P*C.transpose-C*P*L.transpose=
      B-B.transpose+E*(J*P*W.transpose-W*P*J.transpose)*E.transpose := by
    have hup : L*P*W.transpose=W.transpose-C*P*J.transpose := by
      exact (sub_eq_zero.mp hu0).symm
    have hum' : W*P*L.transpose=W-J*P*C.transpose := by
      exact (sub_eq_zero.mp hum).symm
    calc
      _ = D-D.transpose-E*W+W.transpose*E.transpose+
          L*P*D.transpose-L*P*W.transpose*E.transpose-
          D*P*L.transpose+E*(W*P*L.transpose) := by
        dsimp only [C]
        simp only [Matrix.transpose_sub, Matrix.transpose_mul]
        noncomm_ring
      _ = D-D.transpose+L*P*D.transpose-D*P*L.transpose+
          C*P*J.transpose*E.transpose-E*J*P*C.transpose := by
        rw [hup, hum']
        noncomm_ring
      _ = _ := by
        dsimp only [L, C, B]
        simp only [Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_one,
          Matrix.transpose_transpose, Matrix.transpose_add, hP]
        noncomm_ring
  refine ⟨hu0, hum, hv0, ?_⟩
  rw [hc, hb, sub_self, hv0]
  simp

variable {ι : Type*} [Fintype ι]

def nonlinearRootRecenteredTransform (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (u : ι) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of (fun i j => exp (z u*edgeLo σ i j)*dressedQhat z ρ σ Dt G (z u) i j)

theorem nonlinearRoot_first_matrix (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (u : ι) :
    Matrix.of (firstLHS z ρ σ Dt G u)=Matrix.of (Dt u)*
      (1-Matrix.diagonal ρ*(nonlinearRootRecenteredTransform z ρ σ Dt G u).transpose) := by
  ext i j
  simp only [firstLHS, nonlinearRootRecenteredTransform, Matrix.of_apply,
    Matrix.mul_apply (M := Matrix.of (Dt u)), Matrix.sub_apply, Matrix.one_apply, Matrix.diagonal_mul,
    Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro m _
  ring

theorem nonlinearRoot_first_matrix_symmetric (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K Dt G : TailMatrix ι N) (hroot : IsRoot z ρ σ K Dt G)
    (hK : ∀ u i j, K u i j=K u j i) (u : ι) :
    (Matrix.of (Dt u)*(1-Matrix.diagonal ρ*
      (nonlinearRootRecenteredTransform z ρ σ Dt G u).transpose)).transpose=
      Matrix.of (Dt u)*(1-Matrix.diagonal ρ*
        (nonlinearRootRecenteredTransform z ρ σ Dt G u).transpose) := by
  rw [← nonlinearRoot_first_matrix]
  ext i j
  simp only [Matrix.transpose_apply, Matrix.of_apply, hroot.1, hK u j i]

omit [Fintype ι] in
theorem nonlinearRoot_W_matrix (z : ι → ℝ) (ρ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (u : ι) :
    Matrix.of (W z ρ Dt G u)=((2*π/z u) • Matrix.of (G u))*Matrix.diagonal ρ*Matrix.of (Dt u) := by
  ext i j
  simp only [W, Wt, Matrix.of_apply,
    Matrix.mul_apply (M := ((2*π/z u) • Matrix.of (G u))*Matrix.diagonal ρ), Matrix.smul_apply,
    Matrix.mul_diagonal, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  ring

omit [Fintype ι] in
theorem nonlinearRoot_C_matrix (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (u : ι) :
    Matrix.of (C z ρ σ Dt G u)=Matrix.of (Dt u)-
      Matrix.diagonal (fun i => exp (-z u*σ i))*Matrix.of (W z ρ Dt G u) := by
  ext i j
  simp only [Matrix.of_apply, Matrix.sub_apply, Matrix.diagonal_mul, C, W]
  exact (eq_sub_iff_add_eq.mpr (by
    linear_combination -cancellation_star (z u) ρ σ (G u) (Dt u) i j))

theorem nonlinearRoot_J_matrix (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u)
    (hroot : IsRoot z ρ σ K Dt G) (u : ι) :
    (z u)⁻¹ • nonlinearRationalJ z ρ σ Dt G (z u)=
      ((2*π/z u) • Matrix.of (G u))*
        (1-Matrix.diagonal ρ*nonlinearRootRecenteredTransform z ρ σ Dt G u) := by
  ext i j
  have he := hroot.2 u i j
  have hj : nonlinearRationalJ z ρ σ Dt G (z u) i j=
      secondRHS z ρ σ Dt G u i j := by
    simp only [nonlinearRationalJ, Matrix.of_apply, secondRHS]
    rw [add_div, add_div, Finset.sum_div]
    congr 1
    · field_simp [(hz u).ne']
    · apply Finset.sum_congr rfl
      intro t _
      field_simp [(hz u).ne']
  rw [← he] at hj
  simp only [Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_apply (M := ((2*π/z u) • Matrix.of (G u))),
    Matrix.sub_apply, Matrix.one_apply, Matrix.diagonal_mul,
    nonlinearRootRecenteredTransform, Matrix.of_apply, hj, secondLHS, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  ring

theorem nonlinearRoot_L_matrix (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (u : ι) :
    (z u)⁻¹ • nonlinearRationalL z ρ σ Dt G (z u)=
      nonlinearRootRecenteredTransform z ρ σ Dt G u+
        Matrix.diagonal (fun i => exp (-z u*σ i))*
          ((z u)⁻¹ • nonlinearRationalJ z ρ σ Dt G (z u)) := by
  ext i j
  have he := nonlinear_recentered_dictionary_rational z σ
    (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G)
    (W z ρ Dt G) (C z ρ σ Dt G) (z u) (hz u).ne'
    (fun t => (add_pos (hz u) (hz t)).ne') i j
  have hh : z u*exp (z u*edgeLo σ i j)*dressedQhat z ρ σ Dt G (z u) i j=
    nonlinearRationalL z ρ σ Dt G (z u) i j-
      exp (-z u*σ i)*nonlinearRationalJ z ρ σ Dt G (z u) i j := by
    simpa only [nonlinearRationalL, nonlinearRationalJ, nonlinearLowerQValue,
      Matrix.of_apply, dressedQhat, sub_eq_add_neg, add_assoc, neg_mul] using he
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.add_apply, Matrix.diagonal_mul,
    nonlinearRootRecenteredTransform, Matrix.of_apply]
  simp only [neg_mul] at hh ⊢
  field_simp [(hz u).ne']
  linear_combination -hh

/-- The four normalized finite-pole defects vanish for every actual root
with symmetric prescribed tails, including repeated rates and zero densities.
This conclusion does not assert that the complete Wronskian vanishes. -/
theorem nonlinearRoot_all_yukawa_pole_defects_zero (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u)
    (hroot : IsRoot z ρ σ K Dt G) (hK : ∀ u i j, K u i j=K u j i) (u : ι) :
    let P := Matrix.diagonal ρ
    let W := Matrix.of (W z ρ Dt G u)
    let C := Matrix.of (C z ρ σ Dt G u)
    let J := (z u)⁻¹ • nonlinearRationalJ z ρ σ Dt G (z u)
    let L := (z u)⁻¹ • nonlinearRationalL z ρ σ Dt G (z u)
    (W.transpose-C*P*J.transpose-L*P*W.transpose=0) ∧
    (W-J*P*C.transpose-W*P*L.transpose=0) ∧
    (J*P*W.transpose-W*P*J.transpose=0) ∧
    (C-C.transpose+L*P*C.transpose-C*P*L.transpose=0) := by
  have h := bh_matrix_pole_cancellation (Matrix.diagonal ρ)
    (Matrix.diagonal (fun i => exp (-z u*σ i))) (Matrix.of (Dt u))
    ((2*π/z u) • Matrix.of (G u)) (nonlinearRootRecenteredTransform z ρ σ Dt G u)
    (Matrix.diagonal_transpose ρ) (nonlinearRoot_first_matrix_symmetric z ρ σ K Dt G hroot hK u)
  simpa only [← nonlinearRoot_W_matrix z ρ Dt G u,
    ← nonlinearRoot_C_matrix z ρ σ Dt G u,
    ← nonlinearRoot_J_matrix z ρ σ K Dt G hz hroot u,
    ← nonlinearRoot_L_matrix z ρ σ Dt G hz u] using h

/-- Unnormalized residues. The factors of `z` agree with the residues of
`J(s)` and `L(s)` at the reflected Yukawa poles. -/
theorem nonlinearRoot_yukawa_residue_matrices_zero (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u)
    (hroot : IsRoot z ρ σ K Dt G) (hK : ∀ u i j, K u i j=K u j i) (u : ι) :
    let P := Matrix.diagonal ρ
    let W := Matrix.of (W z ρ Dt G u)
    let C := Matrix.of (C z ρ σ Dt G u)
    let J := nonlinearRationalJ z ρ σ Dt G (z u)
    let L := nonlinearRationalL z ρ σ Dt G (z u)
    ((z u) • W.transpose-C*P*J.transpose-L*P*W.transpose=0) ∧
    ((z u) • W-J*P*C.transpose-W*P*L.transpose=0) ∧
    (J*P*W.transpose-W*P*J.transpose=0) ∧
    ((z u) • (C-C.transpose)+L*P*C.transpose-C*P*L.transpose=0) := by
  have h := nonlinearRoot_all_yukawa_pole_defects_zero z ρ σ K Dt G hz hroot hK u
  dsimp only at h ⊢
  have hcancel : z u*(z u)⁻¹=1 := mul_inv_cancel₀ (hz u).ne'
  have hu := congrArg (fun M : Matrix (Fin N) (Fin N) ℝ => z u • M) h.1
  have hum := congrArg (fun M : Matrix (Fin N) (Fin N) ℝ => z u • M) h.2.1
  have hv := congrArg (fun M : Matrix (Fin N) (Fin N) ℝ => z u • M) h.2.2.1
  have hvm := congrArg (fun M : Matrix (Fin N) (Fin N) ℝ => z u • M) h.2.2.2
  simp only [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, smul_sub,
    smul_add, smul_smul, hcancel, one_smul, smul_zero] at hu hum hv hvm
  exact ⟨hu, hum, hv, by simpa only [smul_sub] using hvm⟩

end FMSA.ExactMSA.MultiTailMixture
