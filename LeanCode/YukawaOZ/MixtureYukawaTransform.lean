import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# One-Yukawa `U₁` transform (Tang & Lu eq (18))

The Laplace/Fourier transform of the first-order (one-Yukawa MSA) direct correlation function, which is
the input `U₁` to Tang & Lu's residue expansion (eqs 19–24) for the mixture first-order RDF.  The MSA
DCF `C¹ᵢⱼ(r) = −βuᵢⱼ(r) = βRᵢⱼεᵢⱼ·e^{−zᵢⱼ(r−Rᵢⱼ)}/r` carries a `1/r` that cancels the `r` weight of the
radial transform `∫ r·C¹ᵢⱼ(r)·e^{−sr}dr`, leaving a pure exponential integral — hence the clean pole
`1/(s+zᵢⱼ)`.
-/

open MeasureTheory Set Real

namespace FMSA.MixtureRDF

/-- **Tang & Lu eq (18) core — the Yukawa-tail Laplace transform.**
`∫_R^∞ e^{−z(r−R)}·e^{−sr} dr = e^{−sR}/(s+z)` for `s + z > 0`.  The single-exponential integral behind
the `U₁` matrix (via `integral_comp_mul_left_Ioi` + `integral_exp_neg_Ioi`). -/
theorem laplace_yukawa {R z s : ℝ} (hzs : 0 < z + s) :
    (∫ r in Ioi R, Real.exp (-z * (r - R)) * Real.exp (-s * r)) = Real.exp (-s * R) / (s + z) := by
  have hf : ∀ r : ℝ, Real.exp (-z * (r - R)) * Real.exp (-s * r)
      = Real.exp (z * R) * Real.exp (-((z + s) * r)) := by
    intro r
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  simp_rw [hf]
  rw [integral_const_mul, integral_comp_mul_left_Ioi (fun x => Real.exp (-x)) R hzs,
    integral_exp_neg_Ioi, smul_eq_mul, mul_comm ((z + s)⁻¹) _, ← mul_assoc, ← Real.exp_add,
    show z * R + -((z + s) * R) = -s * R from by ring]
  rw [div_eq_mul_inv, add_comm s z]

/-- **Tang & Lu eq (18) — the one-Yukawa `U₁` matrix entry (Laplace form).**  `r·C¹ᵢⱼ = βRε·e^{−z(r−R)}`
(the `r` cancels the Yukawa `1/r`), so its transform is `βRε·e^{−sR}/(s+z)`; times `2π(ρᵢρⱼ)^{1/2}`
this is `Kᵢⱼ·e^{−sR}/(s+z)`, `Kᵢⱼ = 2π(ρᵢρⱼ)^{1/2}·R·β·ε` — exactly eq (18). -/
theorem yukawa_U1_entry {R z s beta eps : ℝ} (hzs : 0 < z + s) :
    (∫ r in Ioi R, (beta * R * eps * Real.exp (-z * (r - R))) * Real.exp (-s * r))
      = beta * R * eps * (Real.exp (-s * R) / (s + z)) := by
  rw [show (fun r => (beta * R * eps * Real.exp (-z * (r - R))) * Real.exp (-s * r))
      = (fun r => (beta * R * eps) * (Real.exp (-z * (r - R)) * Real.exp (-s * r))) from by
        funext r; ring,
    integral_const_mul, laplace_yukawa hzs]

end FMSA.MixtureRDF
