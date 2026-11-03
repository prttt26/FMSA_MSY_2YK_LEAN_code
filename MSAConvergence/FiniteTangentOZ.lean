import MSAConvergence.SymplecticTangent

/-! Finite first-order OZ algebra from actual phase/source defects.
Only genuine derivatives at one base point are used. -/
noncomputable section
namespace FMSA.Convergence.FiniteTangentOZ
open FMSA.Convergence.SymplecticTangent
variable {N : ℕ} {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- A smooth finite matrix defect has zero value and actual first variation
at the specified point and direction. -/
structure VanishingVariation (F : P → Matrix (Fin N) (Fin N) ℂ) (p v : P) : Prop where
  differentiable : EntryDiff F p
  value : F p = 0
  derivative : matrixDerivative F p v = 0

/-- Defect addition preserves zero value and genuine first variation. -/
theorem vanishing_add (F G : P → Matrix (Fin N) (Fin N) ℂ) (p v : P)
    (hF : VanishingVariation F p v) (hG : VanishingVariation G p v) :
    VanishingVariation (fun a => F a+G a) p v := by
  refine ⟨entry_diff_add _ _ p hF.differentiable hG.differentiable, ?_, ?_⟩
  · rw [hF.value, hG.value, add_zero]
  · rw [matrix_derivative_add _ _ p v hF.differentiable hG.differentiable, hF.derivative, hG.derivative, add_zero]

/-- Defect subtraction preserves zero value and genuine first variation. -/
theorem vanishing_sub (F G : P → Matrix (Fin N) (Fin N) ℂ) (p v : P)
    (hF : VanishingVariation F p v) (hG : VanishingVariation G p v) :
    VanishingVariation (fun a => F a-G a) p v := by
  refine ⟨entry_diff_sub _ _ p hF.differentiable hG.differentiable, ?_, ?_⟩
  · rw [hF.value, hG.value, sub_self]
  · rw [matrix_derivative_sub _ _ p v hF.differentiable hG.differentiable, hF.derivative, hG.derivative, sub_self]

/-- Left multiplication by any smooth family preserves a vanishing defect. -/
theorem vanishing_mul_left (F G : P → Matrix (Fin N) (Fin N) ℂ) (p v : P)
    (hF : EntryDiff F p) (hG : VanishingVariation G p v) :
    VanishingVariation (fun a => F a*G a) p v := by
  refine ⟨entry_diff_mul _ _ p hF hG.differentiable, ?_, ?_⟩
  · rw [hG.value, Matrix.mul_zero]
  · rw [matrix_derivative_mul _ _ p v hF hG.differentiable, hG.value, hG.derivative]
    simp only [Matrix.mul_zero, add_zero]

/-- Right multiplication by any smooth family preserves a vanishing defect. -/
theorem vanishing_mul_right (F G : P → Matrix (Fin N) (Fin N) ℂ) (p v : P)
    (hF : VanishingVariation F p v) (hG : EntryDiff G p) :
    VanishingVariation (fun a => F a*G a) p v := by
  refine ⟨entry_diff_mul _ _ p hF.differentiable hG, ?_, ?_⟩
  · rw [hF.value, Matrix.zero_mul]
  · rw [matrix_derivative_mul _ _ p v hF.differentiable hG, hF.value, hF.derivative]
    simp only [Matrix.zero_mul, add_zero]

/-- Fixed complex rescaling preserves zero value and genuine first variation. -/
theorem vanishing_smul (c : ℂ) (F : P → Matrix (Fin N) (Fin N) ℂ) (p v : P)
    (hF : VanishingVariation F p v) : VanishingVariation (fun a => c • F a) p v := by
  refine ⟨entry_diff_smul _ _ p hF.differentiable, ?_, ?_⟩
  · rw [hF.value, smul_zero]
  · rw [matrix_derivative_smul _ _ p v hF.differentiable, hF.derivative, smul_zero]

/-- All-amplitude OZ error decomposition. Every order of the species
matrices is retained, including a potentially singular density matrix. -/
theorem phase_source_OZ_error (Qp Qm R C Cm Ep Em Bp Bm : Matrix (Fin N) (Fin N) ℂ)
    (s : ℂ) (hC : C = Qp+Qm.transpose-Qp*R*Qm.transpose)
    (hCm : Cm = Qm+Qp.transpose-Qm*R*Qp.transpose) :
    (1-C*R)*(Em-Ep)-s • C =
      (1-Qp*R)*((1-Qm.transpose*R)*Em-Bm)-
      (1-Qm*R)*((1-Qp.transpose*R)*Ep-Bp)+
      ((1-Qp*R)*Bm-(1-Qm*R)*Bp-s • C)+(C-Cm)*R*Ep := by
  rw [hC, hCm]
  noncomm_ring

/-- Zero actual phase/source/evenness defects and their first variations
imply the unnormalized finite OZ defect and its actual variation vanish. -/
theorem phase_source_OZ_vanishing
    (Qp Qm C Cm Ep Em Bp Bm : P → Matrix (Fin N) (Fin N) ℂ)
    (R : Matrix (Fin N) (Fin N) ℂ) (s : ℂ) (p v : P)
    (hQp : EntryDiff Qp p) (hQm : EntryDiff Qm p) (hEp : EntryDiff Ep p)
    (hC : ∀ a, C a = Qp a+(Qm a).transpose-Qp a*R*(Qm a).transpose)
    (hCm : ∀ a, Cm a = Qm a+(Qp a).transpose-Qm a*R*(Qp a).transpose)
    (hp : VanishingVariation (fun a => (1-(Qp a).transpose*R)*Ep a-Bp a) p v)
    (hm : VanishingVariation (fun a => (1-(Qm a).transpose*R)*Em a-Bm a) p v)
    (hsource : VanishingVariation (fun a => (1-Qp a*R)*Bm a-(1-Qm a*R)*Bp a-s • C a) p v)
    (heven : VanishingVariation (fun a => C a-Cm a) p v) :
    VanishingVariation (fun a => (1-C a*R)*(Em a-Ep a)-s • C a) p v := by
  have hR := entry_diff_const R p
  have hI := entry_diff_const (1 : Matrix (Fin N) (Fin N) ℂ) p
  have hleftp := entry_diff_sub _ _ p hI (entry_diff_mul _ _ p hQp hR)
  have hleftm := entry_diff_sub _ _ p hI (entry_diff_mul _ _ p hQm hR)
  have hj := vanishing_add _ _ p v
    (vanishing_add _ _ p v
      (vanishing_sub _ _ p v (vanishing_mul_left _ _ p v hleftp hm)
        (vanishing_mul_left _ _ p v hleftm hp)) hsource)
    (vanishing_mul_right _ _ p v (vanishing_mul_right _ _ p v heven hR) hEp)
  have he : (fun a => (1-C a*R)*(Em a-Ep a)-s • C a) =
      fun a => (1-Qp a*R)*((1-(Qm a).transpose*R)*Em a-Bm a)-
        (1-Qm a*R)*((1-(Qp a).transpose*R)*Ep a-Bp a)+
        ((1-Qp a*R)*Bm a-(1-Qm a*R)*Bp a-s • C a)+(C a-Cm a)*R*Ep a :=
    funext (fun a => phase_source_OZ_error _ _ R _ _ _ _ _ _ s (hC a) (hCm a))
  rw [he]
  exact hj

/-- Nonzero-frequency normalization is performed only after the actual
unnormalized value/variation identities have been proved. -/
theorem normalized_OZ_vanishing (C E : P → Matrix (Fin N) (Fin N) ℂ)
    (R : Matrix (Fin N) (Fin N) ℂ) (s : ℂ) (hs : s ≠ 0) (p v : P)
    (h : VanishingVariation (fun a => (1-C a*R)*E a-s • C a) p v) :
    VanishingVariation (fun a => (1-C a*R)*(s⁻¹ • E a)-C a) p v := by
  have he : (fun a => (1-C a*R)*(s⁻¹ • E a)-C a) =
      fun a => s⁻¹ • ((1-C a*R)*E a-s • C a) := by
    funext a
    simp only [Matrix.mul_smul, smul_sub, smul_smul, inv_mul_cancel₀ hs, one_smul]
  rw [he]
  exact vanishing_smul s⁻¹ _ p v h

/-- A legitimate actual zero OZ defect gives the ordered linearized
matrix equation; a root-only neighbourhood identity is not differentiated. -/
theorem OZ_value_and_variation (C H : P → Matrix (Fin N) (Fin N) ℂ)
    (R : Matrix (Fin N) (Fin N) ℂ) (p v : P) (hC : EntryDiff C p) (hH : EntryDiff H p)
    (h : VanishingVariation (fun a => (1-C a*R)*H a-C a) p v) :
    (1-C p*R)*H p = C p ∧
    (1-C p*R)*matrixDerivative H p v =
      matrixDerivative C p v+matrixDerivative C p v*R*H p := by
  refine ⟨sub_eq_zero.mp h.value, ?_⟩
  have hCR := entry_diff_mul C (fun _ => R) p hC (entry_diff_const R p)
  have hA := entry_diff_sub (fun _ => 1) (fun a => C a*R) p (entry_diff_const _ p) hCR
  have hd := h.derivative
  rw [matrix_derivative_sub _ _ p v (entry_diff_mul _ _ p hA hH) hC,
    matrix_derivative_mul _ _ p v hA hH,
    matrix_derivative_sub _ _ p v (entry_diff_const _ p) hCR,
    matrix_derivative_const, matrix_derivative_mul_const _ _ p v hC, zero_sub] at hd
  linear_combination (norm := noncomm_ring) hd

/-- Density weighting and a unit physical denominator solve the ordered
tangent OZ equation without dividing by individual species densities. -/
theorem weighted_OZ_solution (C H dC dH S R : Matrix (Fin N) (Fin N) ℂ)
    (hR : S*S = R) (hu : IsUnit (1-S*C*S))
    (hb : (1-C*R)*H = C) (hd : (1-C*R)*dH = dC+dC*R*H) :
    S*dH*S = (1-S*C*S)⁻¹*(S*dC*S)*(1-S*C*S)⁻¹ := by
  let A := 1-S*C*S
  let X := S*H*S
  have hbX : A*X = S*C*S := by
    calc
      _ = S*((1-C*R)*H)*S := by dsimp only [A, X]; rw [← hR]; noncomm_ring
      _ = _ := by rw [hb]
  have hdX : A*(S*dH*S) = (S*dC*S)*(1+X) := by
    calc
      _ = S*((1-C*R)*dH)*S := by dsimp only [A]; rw [← hR]; noncomm_ring
      _ = S*(dC+dC*R*H)*S := by rw [hd]
      _ = _ := by dsimp only [X]; rw [← hR]; noncomm_ring
  have huD : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det _).mp hu
  have hAX : A*(1+X) = 1 := by rw [Matrix.mul_add, Matrix.mul_one, hbX]; dsimp only [A]; noncomm_ring
  have hX : 1+X = A⁻¹ := by
    have hh := congrArg (fun Z => A⁻¹*Z) hAX
    simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ huD, Matrix.one_mul, Matrix.mul_one] using hh
  calc
    _ = A⁻¹*(A*(S*dH*S)) := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ huD, Matrix.one_mul]
    _ = A⁻¹*((S*dC*S)*(1+X)) := by rw [hdX]
    _ = _ := by rw [hX]; simp only [A, Matrix.mul_assoc]

end FMSA.Convergence.FiniteTangentOZ

/-- info: 'FMSA.Convergence.FiniteTangentOZ.vanishing_add' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.FiniteTangentOZ.vanishing_add

/-- info: 'FMSA.Convergence.FiniteTangentOZ.vanishing_sub' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.FiniteTangentOZ.vanishing_sub

/-- info: 'FMSA.Convergence.FiniteTangentOZ.vanishing_mul_left' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.FiniteTangentOZ.vanishing_mul_left

/-- info: 'FMSA.Convergence.FiniteTangentOZ.vanishing_mul_right' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.FiniteTangentOZ.vanishing_mul_right

/-- info: 'FMSA.Convergence.FiniteTangentOZ.vanishing_smul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.FiniteTangentOZ.vanishing_smul

/-- info: 'FMSA.Convergence.FiniteTangentOZ.phase_source_OZ_error' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.FiniteTangentOZ.phase_source_OZ_error

/-- info: 'FMSA.Convergence.FiniteTangentOZ.phase_source_OZ_vanishing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.FiniteTangentOZ.phase_source_OZ_vanishing

/-- info: 'FMSA.Convergence.FiniteTangentOZ.normalized_OZ_vanishing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.FiniteTangentOZ.normalized_OZ_vanishing

/-- info: 'FMSA.Convergence.FiniteTangentOZ.OZ_value_and_variation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.FiniteTangentOZ.OZ_value_and_variation

/-- info: 'FMSA.Convergence.FiniteTangentOZ.weighted_OZ_solution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.FiniteTangentOZ.weighted_OZ_solution
