import LeanCode.YukawaOZMix.MSAMixtureBHRootUneqDefs

open MSAMixture
namespace FMSA.ExactMSA.MixLeg3

/-- **The recentered unequal-σ transform collapses to the equal-σ transform at the ROW diameter.**
For *any* `σ` (not just equal), `e^{z·edgeLo σ j l} · qhatMixRuneq_jl(z) = qhatMixR z (σ_j)_jl` — the
recentering exactly cancels `qhatMixRuneq`'s prefactor `e^{−z·lam}` (`lam = edgeLo σ j l`), and the tail
term's exponent `lam − sij = −σ_j` erases the `σ_l` dependence, leaving the equal-σ `qhatMixR` at the
row diameter `σ_j`.  (`qhatMixRuneq_eq_qhatMixR_of_equal` is the `σ_j = sig` special case.)  This is the
structural key for an unequal-σ smooth family: the recentered root's amplitude dependence is *identical*
to the equal-σ one (the `e^{z·edgeLo}` factors are `σ`-constants), so the `C^∞`/residual scaffolding of
`MSAMixtureBHRootSmooth` transfers unchanged. -/
theorem qhatMixRuneq_recentered_eq_qhatMixR {N : ℕ} (z : ℝ) (σ : Fin N → ℝ)
    (qp Wt Ct : Matrix (Fin N) (Fin N) ℝ) (Av : Fin N → ℝ) (j l : Fin N) :
    Real.exp (z * edgeLo σ j l) * qhatMixRuneq z σ qp Wt Ct Av z j l
      = qhatMixR z (σ j) qp Wt Ct Av z j l := by
  have hL : Real.exp (z * edgeLo σ j l) * Real.exp (-(z * ((σ l - σ j) / 2))) = 1 := by
    rw [← Real.exp_add, show z * edgeLo σ j l + -(z * ((σ l - σ j) / 2)) = 0 from by
      unfold edgeLo; ring, Real.exp_zero]
  have hLS : Real.exp (z * edgeLo σ j l) * Real.exp (-(z * ((σ j + σ l) / 2)))
      = Real.exp (-(z * σ j)) := by
    rw [← Real.exp_add]; congr 1; unfold edgeLo; ring
  simp only [qhatMixRuneq, qhatMixR]
  rw [mul_add, ← mul_assoc, hL, one_mul,
      show Real.exp (z * edgeLo σ j l)
            * (Ct j l * (Real.exp (-(z * ((σ j + σ l) / 2))) / (z + z)))
          = Ct j l * (Real.exp (z * edgeLo σ j l) * Real.exp (-(z * ((σ j + σ l) / 2)))) / (z + z)
        from by ring, hLS]
  ring

end FMSA.ExactMSA.MixLeg3
