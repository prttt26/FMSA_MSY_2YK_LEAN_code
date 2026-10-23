import LeanCode.YukawaOZMix.MSAMultiTailMixtureDPAmplitude

/-! Algebra of the actual Q tangent, including its essential compact quadratic
correction. These statements identify actual BH coefficients, rather than
postulating an independent DP Q formula. -/
noncomputable section
open Real MSAMixture FMSA.MatrixQ0 FMSA.ExactMSA.Breakpoint
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

theorem firstOrderDt_eq_block_edge (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hv : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i) (u : ι) :
    Matrix.of (firstOrderDt z ρ σ K u) =
      (Matrix.of (baseFirst z ρ σ u)).transpose * dressedEdgeSlope z ρ σ K u := by
  have hb : IsUnit ((Matrix.of (baseFirst z ρ σ u)).transpose).det := by
    rw [Matrix.det_transpose]
    convert! baseFirst_isUnit_det z ρ σ hz hv hρ hσ u using 1
  rw [firstOrderDt_matrix, dressedEdgeSlope, mul_smul_comm,
    Matrix.transpose_nonsing_inv]
  congr 1
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ hb, Matrix.one_mul]

theorem firstOrderDt_eq_moment_edge (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hv : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i) (u : ι) :
    Matrix.of (firstOrderDt z ρ σ K u) =
      (1-Matrix.of (hsMoment ρ σ (z u))*Matrix.diagonal ρ) * dressedEdgeSlope z ρ σ K u := by
  rw [firstOrderDt_eq_block_edge z ρ σ K hz hv hρ hσ u,
    baseFirst_transpose_matrix_moment]

theorem W_matrix (s : ℝ) (ρ : Fin N → ℝ) (G D : Matrix (Fin N) (Fin N) ℝ) :
    Matrix.of (Wt s ρ G D) = (2*π/s) • (G*Matrix.diagonal ρ*D) := by
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [Matrix.mul_apply (M := G*Matrix.diagonal ρ) (N := D)]
  simp only [Matrix.of_apply, Wt, Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_diagonal]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem firstOrderW_eq_source_edge (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hv : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i) (u : ι) :
    Matrix.of (W z ρ (firstOrderDt z ρ σ K) (baseSeed z ρ σ) u) =
      (1/(z u)) • (Matrix.of (baseSource z ρ σ u)*Matrix.diagonal ρ*dressedEdgeSlope z ρ σ K u) := by
  have hb : IsUnit (Matrix.of (baseSecond z ρ σ u)).det := by
    convert! baseSecond_isUnit_det z ρ σ hz hv hρ hσ u using 1
  have hi : Matrix.diagonal ρ*(Matrix.of (baseFirst z ρ σ u)).transpose =
      Matrix.of (baseSecond z ρ σ u)*Matrix.diagonal ρ := by
    rw [baseFirst_transpose_matrix_moment, baseSecond_matrix_moment]
    noncomm_ring
  change Matrix.of (Wt (z u) ρ (Matrix.of (baseSeed z ρ σ u))
    (Matrix.of (firstOrderDt z ρ σ K u))) = _
  rw [W_matrix, baseSeed_matrix, firstOrderDt_eq_block_edge z ρ σ K hz hv hρ hσ u,
    smul_mul_assoc, smul_mul_assoc, smul_smul]
  have hc : (2*π/z u)*(2*π)⁻¹ = 1/z u := by field_simp
  rw [hc]
  congr 1
  calc
    _ = Matrix.of (baseSource z ρ σ u)*(Matrix.of (baseSecond z ρ σ u))⁻¹ *
        (Matrix.diagonal ρ*(Matrix.of (baseFirst z ρ σ u)).transpose)*dressedEdgeSlope z ρ σ K u := by noncomm_ring
    _ = _ := by
      rw [hi, ← Matrix.mul_assoc,
        Matrix.nonsing_inv_mul_cancel_right _ _ hb]

def tangentACoeff (s : ℝ) (ρ σ : Fin N → ℝ) (l : Fin N) : ℝ :=
  -(2*π/vacMix ρ σ)/s-(2*π/vacMix ρ σ)*σ l +
    2*(π^2*xi2 ρ σ/vacMix ρ σ^2)/s^2+(π^2*xi2 ρ σ/vacMix ρ σ^2)*σ l/s

def tangentWCoeff (s : ℝ) (ρ σ : Fin N → ℝ) (l : Fin N) : ℝ :=
  -(2*π/vacMix ρ σ)/s-(π^2*xi2 ρ σ/vacMix ρ σ^2)*σ l/s +
    2*(π^2*xi2 ρ σ/vacMix ρ σ^2)/s^2

theorem mixDA_eq_tangent_coeff (s : ℝ) (hs : s ≠ 0) (ρ σ : Fin N → ℝ)
    (hv : vacMix ρ σ ≠ 0) (G D : Matrix (Fin N) (Fin N) ℝ) (j : Fin N) :
    mixDA s ρ σ G D j = ∑ l, ρ l * (tangentACoeff s ρ σ l*D l j +
      (tangentWCoeff s ρ σ l-exp (-s*σ l)*tangentACoeff s ρ σ l)*Wt s ρ G D l j) := by
  have he : mixDA s ρ σ G D j = (2*π/vacMix ρ σ)*mixM s ρ σ G D j +
      (π^2*xi2 ρ σ/vacMix ρ σ^2)*(σ j*mixM s ρ σ G D j+2*mixN s ρ σ G D j) := by
    unfold mixDA Qppphys
    ring
  rw [he, mix_edge_combination s hs]
  unfold mixM
  rw [← mul_assoc, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  have hc := cancellation_star s ρ σ G D l j
  rw [show Ct s ρ σ G D l j = D l j-exp (-s*σ l)*Wt s ρ G D l j by linarith [hc]]
  unfold tangentACoeff tangentWCoeff edgeMomentA edgeMomentM
  field_simp
  <;> ring

theorem hsMoment_tangentA_cancellation (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (u : ι) (hz : z u ≠ 0) (hv : vacMix ρ σ ≠ 0) (l m : Fin N) :
    -tangentACoeff (z u) ρ σ l*hsMoment ρ σ (z u) l m +
      (tangentWCoeff (z u) ρ σ l-exp (-z u*σ l)*tangentACoeff (z u) ρ σ l)*
        baseSource z ρ σ u l m/(z u) =
      -(2*π/vacMix ρ σ)^2*σ l^2*(1+z u*σ m)/(2*(z u)^2) := by
  unfold tangentACoeff tangentWCoeff hsMoment baseSource Q0phys Qppphys
  field_simp
  <;> ring

theorem tangentA_summed_cancellation (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (u : ι) (hz : z u ≠ 0) (hv : vacMix ρ σ ≠ 0) (m : Fin N) :
    tangentACoeff (z u) ρ σ m +
      (∑ l, ρ l*(-tangentACoeff (z u) ρ σ l*hsMoment ρ σ (z u) l m +
        (tangentWCoeff (z u) ρ σ l-exp (-z u*σ l)*tangentACoeff (z u) ρ σ l)*
          baseSource z ρ σ u l m/(z u))) =
      -(Qppphys ρ σ m m/(z u)+2*π*σ m/vacMix ρ σ) := by
  simp_rw [hsMoment_tangentA_cancellation z ρ σ u hz hv]
  have he : (∑ l, ρ l*(-(2*π/vacMix ρ σ)^2*σ l^2*(1+z u*σ m)/(2*(z u)^2))) =
      (-(2*π/vacMix ρ σ)^2*(1+z u*σ m)/(2*(z u)^2))*xi2 ρ σ := by
    unfold xi2
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [he]
  unfold tangentACoeff Qppphys
  field_simp
  <;> ring

theorem firstOrderDt_moment_entry (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hv : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i) (u : ι) (i j : Fin N) :
    firstOrderDt z ρ σ K u i j = dressedEdgeSlope z ρ σ K u i j -
      ∑ m, hsMoment ρ σ (z u) i m*ρ m*dressedEdgeSlope z ρ σ K u m j := by
  have he := congrFun (congrFun (firstOrderDt_eq_moment_edge z ρ σ K hz hv hρ hσ u) i) j
  rw [sub_mul, Matrix.one_mul] at he
  rw [Matrix.sub_apply, Matrix.mul_apply
    (M := Matrix.of (hsMoment ρ σ (z u))*Matrix.diagonal ρ)] at he
  simpa only [Matrix.of_apply, Matrix.mul_diagonal] using he

theorem firstOrderW_source_entry (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hv : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i) (u : ι) (i j : Fin N) :
    W z ρ (firstOrderDt z ρ σ K) (baseSeed z ρ σ) u i j =
      ∑ m, baseSource z ρ σ u i m*ρ m*dressedEdgeSlope z ρ σ K u m j/(z u) := by
  have he := congrFun (congrFun (firstOrderW_eq_source_edge z ρ σ K hz hv hρ hσ u) i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at he
  rw [Matrix.mul_apply (M := Matrix.of (baseSource z ρ σ u)*Matrix.diagonal ρ)] at he
  simpa only [Matrix.of_apply,
    Matrix.mul_diagonal, Finset.mul_sum, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm,
    one_mul] using he

theorem mixDA_firstOrderDt (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hv : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i) (u : ι) (j : Fin N) :
    mixDA (z u) ρ σ (Matrix.of (baseSeed z ρ σ u))
      (Matrix.of (firstOrderDt z ρ σ K u)) j =
      -∑ m, ρ m*(Qppphys ρ σ m m/(z u)+2*π*σ m/vacMix ρ σ)*dressedEdgeSlope z ρ σ K u m j := by
  rw [mixDA_eq_tangent_coeff (z u) (hz u).ne' ρ σ hv.ne']
  change (∑ l, ρ l*(tangentACoeff (z u) ρ σ l*firstOrderDt z ρ σ K u l j +
    (tangentWCoeff (z u) ρ σ l-exp (-z u*σ l)*tangentACoeff (z u) ρ σ l)*
      W z ρ (firstOrderDt z ρ σ K) (baseSeed z ρ σ) u l j)) = _
  simp_rw [firstOrderDt_moment_entry z ρ σ K hz hv hρ hσ,
    firstOrderW_source_entry z ρ σ K hz hv hρ hσ]
  simp only [mul_sub, mul_add, Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have he : (∑ l, ∑ m, ρ l*(tangentWCoeff (z u) ρ σ l-exp (-z u*σ l)*tangentACoeff (z u) ρ σ l)*
      (baseSource z ρ σ u l m*ρ m*dressedEdgeSlope z ρ σ K u m j/(z u))) -
    (∑ l, ∑ m, ρ l*(tangentACoeff (z u) ρ σ l*
      (hsMoment ρ σ (z u) l m*ρ m*dressedEdgeSlope z ρ σ K u m j))) =
    ∑ m, ρ m*(∑ l, ρ l*(-tangentACoeff (z u) ρ σ l*hsMoment ρ σ (z u) l m +
      (tangentWCoeff (z u) ρ σ l-exp (-z u*σ l)*tangentACoeff (z u) ρ σ l)*
        baseSource z ρ σ u l m/(z u)))*dressedEdgeSlope z ρ σ K u m j := by
    rw [← Finset.sum_sub_distrib]
    simp only [← Finset.sum_sub_distrib]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m _
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l _
    ring
  calc
    _ = (∑ m, ρ m*tangentACoeff (z u) ρ σ m*dressedEdgeSlope z ρ σ K u m j) +
      (∑ m, ρ m*(∑ l, ρ l*(-tangentACoeff (z u) ρ σ l*hsMoment ρ σ (z u) l m +
        (tangentWCoeff (z u) ρ σ l-exp (-z u*σ l)*tangentACoeff (z u) ρ σ l)*
          baseSource z ρ σ u l m/(z u)))*dressedEdgeSlope z ρ σ K u m j) := by
            rw [← he]
            simp only [mul_assoc, mul_comm, mul_left_comm]
            ring
    _ = _ := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro m _
      have hc := tangentA_summed_cancellation z ρ σ u (hz u).ne' hv.ne' m
      linear_combination ρ m*dressedEdgeSlope z ρ σ K u m j*hc

def compactQuadraticCorrection (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (u : ι) (j : Fin N) : ℝ :=
  -π/vacMix ρ σ*∑ m, ρ m*σ m*dressedEdgeSlope z ρ σ K u m j

/-- The missing compact quadratic coefficient in the actual first-order Q.
It need not vanish for mixtures. This is an identity of actual coefficients,
not yet equality with the independent DP core convolution. -/
theorem compactQuadraticCorrection_eq_actual (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hv : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i) (u : ι) (j : Fin N) :
    (mixDA (z u) ρ σ (Matrix.of (baseSeed z ρ σ u))
      (Matrix.of (firstOrderDt z ρ σ K u)) j +
      ∑ m, ρ m*Qppphys ρ σ m m*dressedEdgeSlope z ρ σ K u m j/(z u))/2 =
      compactQuadraticCorrection z ρ σ K u j := by
  rw [mixDA_firstOrderDt z ρ σ K hz hv hρ hσ u j]
  unfold compactQuadraticCorrection
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro m _
  ring

theorem mixDqp_eq_row_combination (s : ℝ) (ρ σ : Fin N → ℝ)
    (hv : vacMix ρ σ ≠ 0) (G D : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) :
    mixDqp s ρ σ G D i j = σ i/2*mixDA s ρ σ G D j +
      π/vacMix ρ σ*(σ j*mixM s ρ σ G D j+2*mixN s ρ σ G D j) := by
  unfold mixDqp mixDA Q0phys Qppphys
  field_simp
  <;> ring

theorem edge_moments_firstOrderDt (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hv : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i) (u : ι) (j : Fin N) :
    σ j*mixM (z u) ρ σ (Matrix.of (baseSeed z ρ σ u))
        (Matrix.of (firstOrderDt z ρ σ K u)) j +
      2*mixN (z u) ρ σ (Matrix.of (baseSeed z ρ σ u))
        (Matrix.of (firstOrderDt z ρ σ K u)) j =
      ∑ m, ρ m*(edgeMomentA (z u) (σ m)+
        π*xi2 ρ σ*σ m/(vacMix ρ σ*(z u)^2))*dressedEdgeSlope z ρ σ K u m j := by
  rw [mix_edge_combination (z u) (hz u).ne']
  change (∑ l, ρ l*(edgeMomentA (z u) (σ l)*firstOrderDt z ρ σ K u l j +
    edgeMomentM (z u) (σ l)*W z ρ (firstOrderDt z ρ σ K) (baseSeed z ρ σ) u l j)) = _
  simp_rw [firstOrderDt_moment_entry z ρ σ K hz hv hρ hσ,
    firstOrderW_source_entry z ρ σ K hz hv hρ hσ]
  simp only [mul_sub, mul_add, Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have he : (∑ l, ∑ m, ρ l*edgeMomentM (z u) (σ l)*
      (baseSource z ρ σ u l m*ρ m*dressedEdgeSlope z ρ σ K u m j/(z u))) -
    (∑ l, ∑ m, ρ l*(edgeMomentA (z u) (σ l)*
      (hsMoment ρ σ (z u) l m*ρ m*dressedEdgeSlope z ρ σ K u m j))) =
    ∑ m, ρ m*(π*xi2 ρ σ*σ m/(vacMix ρ σ*(z u)^2))*dressedEdgeSlope z ρ σ K u m j := by
    rw [← Finset.sum_sub_distrib]
    simp only [← Finset.sum_sub_distrib]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m _
    have hc : ∀ l, edgeMomentM (z u) (σ l)*baseSource z ρ σ u l m/(z u) -
        edgeMomentA (z u) (σ l)*hsMoment ρ σ (z u) l m =
        π/vacMix ρ σ/(z u)^2*σ l^2*σ m := by
      intro l
      have h := hsMoment_edge_cancellation z ρ σ u (hz u).ne' hv.ne' l m
      linear_combination -h
    calc
      _ = ∑ l, ρ l*ρ m*dressedEdgeSlope z ρ σ K u m j*
          (edgeMomentM (z u) (σ l)*baseSource z ρ σ u l m/(z u) -
            edgeMomentA (z u) (σ l)*hsMoment ρ σ (z u) l m) := by
              apply Finset.sum_congr rfl; intro l _; ring
      _ = _ := by
        simp_rw [hc]
        unfold xi2
        simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro l _
        ring
  calc
    _ = (∑ m, ρ m*edgeMomentA (z u) (σ m)*dressedEdgeSlope z ρ σ K u m j) +
      (∑ m, ρ m*(π*xi2 ρ σ*σ m/(vacMix ρ σ*(z u)^2))*dressedEdgeSlope z ρ σ K u m j) := by
        rw [← he]
        simp only [mul_assoc, mul_comm, mul_left_comm]
        ring
    _ = _ := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro m _
      ring

theorem mixDqp_firstOrderDt (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hv : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i) (u : ι) (i j : Fin N) :
    mixDqp (z u) ρ σ (Matrix.of (baseSeed z ρ σ u))
      (Matrix.of (firstOrderDt z ρ σ K u)) i j =
      ∑ m, ρ m*((1/(z u)^2-σ i/(2*z u))*Qppphys ρ σ m m +
        π*σ m/vacMix ρ σ*(1/(z u)-σ i))*dressedEdgeSlope z ρ σ K u m j := by
  rw [mixDqp_eq_row_combination _ ρ σ hv.ne',
    mixDA_firstOrderDt z ρ σ K hz hv hρ hσ u j,
    edge_moments_firstOrderDt z ρ σ K hz hv hρ hσ u j]
  rw [mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  unfold Qppphys edgeMomentA
  field_simp [(hz u).ne']
  <;> ring

end FMSA.ExactMSA.MultiTailMixture
