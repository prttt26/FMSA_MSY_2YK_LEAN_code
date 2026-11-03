import MSAConvergence.FiniteTangentOZ

/-! Additive density weighting recovers mixed tracer tangent directions
without an inverse species density matrix. -/
noncomputable section
namespace FMSA.Convergence.AdditiveDensityTangentOZ
open FMSA.Convergence.FiniteTangentOZ
variable {N : ℕ}

/-- Sylvester swapping transfers the weighted unit to the unweighted OZ denominator. -/
theorem unweighted_denominator_unit (C S R : Matrix (Fin N) (Fin N) ℂ)
    (hR : S*S = R) (hu : IsUnit (1-S*C*S)) : IsUnit (1-C*R) := by
  have hd : (1-C*R).det = (1-S*C*S).det := by
    rw [← hR]
    simpa only [Matrix.mul_assoc] using Matrix.det_one_sub_mul_comm (C*S) S
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [hd]
  exact (Matrix.isUnit_iff_isUnit_det _).mp hu

/-- The true weighted structure is I+S*H*S even for singular S. -/
theorem weighted_structure_identity (C H S R : Matrix (Fin N) (Fin N) ℂ)
    (hR : S*S = R) (hu : IsUnit (1-S*C*S)) (hb : (1-C*R)*H = C) :
    1+S*H*S = (1-S*C*S)⁻¹ := by
  have he : (1-S*C*S)*(1+S*H*S) = 1 := by
    calc
      _ = 1+S*((1-C*R)*H-C)*S := by rw [← hR]; noncomm_ring
      _ = 1 := by rw [hb, sub_self]; simp
  apply hu.mul_right_injective
  change (1-S*C*S)*(1+S*H*S) = (1-S*C*S)*(1-S*C*S)⁻¹
  rw [he, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hu)]

/-- Genuine unweighted tangent OZ solution, preserving both matrix orders. -/
theorem unweighted_tangent_solution (C H dC dH R : Matrix (Fin N) (Fin N) ℂ)
    (hu : IsUnit (1-C*R)) (hb : (1-C*R)*H = C)
    (hd : (1-C*R)*dH = dC+dC*R*H) :
    dH = (1+H*R)*dC*(1+R*H) := by
  have he : (1-C*R)*(1+H*R) = 1 := by
    calc
      _ = 1+((1-C*R)*H-C)*R := by noncomm_ring
      _ = 1 := by rw [hb, sub_self]; simp
  apply hu.mul_right_injective
  calc
    _ = dC+dC*R*H := hd
    _ = dC*(1+R*H) := by noncomm_ring
    _ = ((1-C*R)*(1+H*R))*dC*(1+R*H) := by rw [he, Matrix.one_mul]
    _ = _ := by simp only [Matrix.mul_assoc]

/-- Previously cancelled double weights imply a genuine additive-weight OZ
identity. No symmetry of C, H, dC or dH is assumed. -/
theorem additive_weighted_tangent_solution (C H dC dH S R : Matrix (Fin N) (Fin N) ℂ)
    (hR : S*S = R) (hu : IsUnit (1-S*C*S)) (hb : (1-C*R)*H = C)
    (hd : (1-C*R)*dH = dC+dC*R*H) (hz : S*dC*S = 0) :
    dH*S+S*dH = (1-S*C*S)⁻¹*(dC*S+S*dC)*(1-S*C*S)⁻¹ := by
  let T := 1+S*H*S
  have hs := unweighted_tangent_solution C H dC dH R (unweighted_denominator_unit C S R hR hu) hb hd
  have hleft : R*dC*S = 0 := by
    calc
      _ = S*(S*dC*S) := by rw [← hR]; noncomm_ring
      _ = 0 := by rw [hz, Matrix.mul_zero]
  have hright : S*dC*R = 0 := by
    calc
      _ = (S*dC*S)*S := by rw [← hR]; noncomm_ring
      _ = 0 := by rw [hz, Matrix.zero_mul]
  have hds : dH*S = (dC*S)*T := by
    rw [hs]
    calc
      _ = dC*S*T+H*(R*dC*S)*T := by dsimp only [T]; rw [← hR]; noncomm_ring
      _ = _ := by rw [hleft]; simp
  have hsd : S*dH = T*(S*dC) := by
    rw [hs]
    calc
      _ = T*(S*dC)+T*(S*dC*R)*H := by dsimp only [T]; rw [← hR]; noncomm_ring
      _ = _ := by rw [hright]; simp
  have htd : T*(dC*S) = dC*S := by
    calc
      _ = dC*S+S*H*(S*dC*S) := by dsimp only [T]; noncomm_ring
      _ = _ := by rw [hz]; simp
  have hdt : (S*dC)*T = S*dC := by
    calc
      _ = S*dC+(S*dC*S)*H*S := by dsimp only [T]; noncomm_ring
      _ = _ := by rw [hz]; simp
  have ht : T = (1-S*C*S)⁻¹ := weighted_structure_identity C H S R hR hu hb
  calc
    _ = (dC*S)*T+T*(S*dC) := by rw [hds, hsd]
    _ = T*(dC*S+S*dC)*T := by
      symm
      calc
        _ = (T*(dC*S))*T+T*((S*dC)*T) := by noncomm_ring
        _ = _ := by rw [htd, hdt]
    _ = _ := by rw [ht]

/-- A vanishing additive weight with nonnegative diagonal entries eliminates
any entry whose row or column weight is positive. -/
theorem additive_zero_entry (a : Fin N → ℝ) (ha : ∀ i, 0 ≤ a i)
    (D : Matrix (Fin N) (Fin N) ℂ)
    (hz : D*Matrix.diagonal (fun i => (a i : ℂ))+Matrix.diagonal (fun i => (a i : ℂ))*D = 0)
    (i j : Fin N) (hij : 0 < a i ∨ 0 < a j) : D i j = 0 := by
  have hpos : 0 < a i+a j := by rcases hij with hi | hj <;> linarith [ha i, ha j]
  have he := congrFun (congrFun hz i) j
  simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.zero_apply] at he
  have hh : ((a i+a j : ℝ) : ℂ)*D i j = 0 := by push_cast; linear_combination he
  exact (mul_eq_zero.mp hh).resolve_left (Complex.ofReal_ne_zero.mpr hpos.ne')

/-- The left and right weighted zeros are obtained separately, not by
cancelling their sum as arbitrary matrices. -/
theorem additive_zero_split (a : Fin N → ℝ) (ha : ∀ i, 0 ≤ a i)
    (D : Matrix (Fin N) (Fin N) ℂ)
    (hz : D*Matrix.diagonal (fun i => (a i : ℂ))+Matrix.diagonal (fun i => (a i : ℂ))*D = 0) :
    D*Matrix.diagonal (fun i => (a i : ℂ)) = 0 ∧
      Matrix.diagonal (fun i => (a i : ℂ))*D = 0 := by
  constructor
  · ext i j
    simp only [Matrix.mul_diagonal, Matrix.zero_apply]
    by_cases hj : a j = 0
    · simp [hj]
    · rw [additive_zero_entry a ha D hz i j (Or.inr (lt_of_le_of_ne (ha j) (Ne.symm hj))), zero_mul]
  · ext i j
    simp only [Matrix.diagonal_mul, Matrix.zero_apply]
    by_cases hi : a i = 0
    · simp [hi]
    · rw [additive_zero_entry a ha D hz i j (Or.inl (lt_of_le_of_ne (ha i) (Ne.symm hi))), mul_zero]

/-- Once both one-sided density weights vanish, the actual tangent OZ
solution reduces to dH=dC on the remaining double-tracer block. -/
theorem tangent_eq_of_one_sided_zero (C H dC dH S R : Matrix (Fin N) (Fin N) ℂ)
    (hR : S*S = R) (hu : IsUnit (1-S*C*S)) (hb : (1-C*R)*H = C)
    (hd : (1-C*R)*dH = dC+dC*R*H) (hl : S*dC = 0) (hr : dC*S = 0) : dH = dC := by
  rw [unweighted_tangent_solution C H dC dH R (unweighted_denominator_unit C S R hR hu) hb hd]
  have hzL : R*dC = 0 := by rw [← hR, Matrix.mul_assoc, hl, Matrix.mul_zero]
  have hzR : dC*R = 0 := by rw [← hR, ← Matrix.mul_assoc, hr, Matrix.zero_mul]
  calc
    _ = dC+H*(R*dC)+(dC*R)*H+H*(R*dC)*R*H := by noncomm_ring
    _ = _ := by rw [hzL, hzR]; simp

/-- Explicit mixed-density check: weights (0,1) eliminate BOTH cross entries
without asserting anything about the tracer-tracer entry D(0,0). -/
theorem mixed_pair_additive_zero (D : Matrix (Fin 2) (Fin 2) ℂ)
    (hz : D*Matrix.diagonal (fun i : Fin 2 => ((if i = 0 then 0 else 1 : ℝ) : ℂ))+
      Matrix.diagonal (fun i : Fin 2 => ((if i = 0 then 0 else 1 : ℝ) : ℂ))*D = 0) :
    D 0 1 = 0 ∧ D 1 0 = 0 := by
  have ha : ∀ i : Fin 2, 0 ≤ (if i = 0 then 0 else 1 : ℝ) := by intro i; split_ifs <;> norm_num
  constructor
  · exact additive_zero_entry _ ha D hz 0 1 (Or.inr (by norm_num))
  · exact additive_zero_entry _ ha D hz 1 0 (Or.inl (by norm_num))

end FMSA.Convergence.AdditiveDensityTangentOZ

/-- info: 'FMSA.Convergence.AdditiveDensityTangentOZ.unweighted_denominator_unit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.AdditiveDensityTangentOZ.unweighted_denominator_unit

/-- info: 'FMSA.Convergence.AdditiveDensityTangentOZ.weighted_structure_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.AdditiveDensityTangentOZ.weighted_structure_identity

/-- info: 'FMSA.Convergence.AdditiveDensityTangentOZ.unweighted_tangent_solution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.AdditiveDensityTangentOZ.unweighted_tangent_solution

/-- info: 'FMSA.Convergence.AdditiveDensityTangentOZ.additive_weighted_tangent_solution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.AdditiveDensityTangentOZ.additive_weighted_tangent_solution

/-- info: 'FMSA.Convergence.AdditiveDensityTangentOZ.additive_zero_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.AdditiveDensityTangentOZ.additive_zero_entry

/-- info: 'FMSA.Convergence.AdditiveDensityTangentOZ.additive_zero_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.AdditiveDensityTangentOZ.additive_zero_split

/-- info: 'FMSA.Convergence.AdditiveDensityTangentOZ.tangent_eq_of_one_sided_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.AdditiveDensityTangentOZ.tangent_eq_of_one_sided_zero

/-- info: 'FMSA.Convergence.AdditiveDensityTangentOZ.mixed_pair_additive_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.AdditiveDensityTangentOZ.mixed_pair_additive_zero
