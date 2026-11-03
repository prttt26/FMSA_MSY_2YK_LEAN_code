import MSAConvergence.TracerCoreForcingBound

/-! Pointwise control of every positive covariance matrix entry by its
real trace, via the matrix-induced inner product. -/
open Matrix
open scoped ComplexOrder BigOperators
noncomputable section
namespace FMSA.Convergence.TracerCovarianceEntryTrace
variable {N : ℕ}
/-- Positive covariance controls each entry by two diagonal energies. -/
theorem posdef_entry_norm_le_sqrt_diags (A : Matrix (Fin N) (Fin N) ℂ) (hA : A.PosDef) (i j : Fin N) :
    ‖A i j‖ ≤ Real.sqrt (A i i).re * Real.sqrt (A j j).re := by
  let ei : Fin N → ℂ := fun k => if k=i then 1 else 0
  let ej : Fin N → ℂ := fun k => if k=j then 1 else 0
  letI : SeminormedAddCommGroup (Fin N → ℂ) := A.toSeminormedAddCommGroup hA.posSemidef
  letI : InnerProductSpace ℂ (Fin N → ℂ) := A.toInnerProductSpace hA.posSemidef
  have h := norm_inner_le_norm (𝕜 := ℂ) ei ej
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ) ei, norm_eq_sqrt_re_inner (𝕜 := ℂ) ej] at h
  change ‖(A*ᵥ ej) ⬝ᵥ star ei‖ ≤
    Real.sqrt (((A*ᵥ ei) ⬝ᵥ star ei).re) *
    Real.sqrt (((A*ᵥ ej) ⬝ᵥ star ej).re) at h
  have hentry (a b : Fin N) :
      (A*ᵥ (fun k : Fin N => if k=b then (1:ℂ) else 0)) ⬝ᵥ
        star (fun k : Fin N => if k=a then (1:ℂ) else 0) = A a b := by
    simp [Matrix.mulVec, dotProduct, Finset.sum_ite_eq']
  simpa only [ei,ej,hentry] using h

/-- Every positive covariance entry is bounded by the real trace. -/
theorem posdef_entry_norm_le_trace_re (A : Matrix (Fin N) (Fin N) ℂ) (hA : A.PosDef) (i j : Fin N) :
    ‖A i j‖ ≤ A.trace.re := by
  have he := posdef_entry_norm_le_sqrt_diags A hA i j
  have hd (l : Fin N) : 0 ≤ (A l l).re :=
    (RCLike.nonneg_iff.mp (hA.posSemidef.diag_nonneg)).1
  have ht : A.trace.re = ∑ l : Fin N, (A l l).re := by
    simp [Matrix.trace, Complex.re_sum]
  have hti (l : Fin N) : (A l l).re ≤ A.trace.re := by
    rw [ht]
    exact Finset.single_le_sum (fun m _ => hd m) (Finset.mem_univ l)
  have htr : 0 ≤ A.trace.re := by
    rw [ht]
    exact Finset.sum_nonneg (fun l _ => hd l)
  calc
    ‖A i j‖ ≤ Real.sqrt (A i i).re * Real.sqrt (A j j).re := he
    _ ≤ Real.sqrt A.trace.re * Real.sqrt A.trace.re :=
      mul_le_mul (Real.sqrt_le_sqrt (hti i)) (Real.sqrt_le_sqrt (hti j))
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = A.trace.re := Real.mul_self_sqrt htr

end FMSA.Convergence.TracerCovarianceEntryTrace
/-- info: 'FMSA.Convergence.TracerCovarianceEntryTrace.posdef_entry_norm_le_sqrt_diags' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerCovarianceEntryTrace.posdef_entry_norm_le_sqrt_diags
/-- info: 'FMSA.Convergence.TracerCovarianceEntryTrace.posdef_entry_norm_le_trace_re' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerCovarianceEntryTrace.posdef_entry_norm_le_trace_re
