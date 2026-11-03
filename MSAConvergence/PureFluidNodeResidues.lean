import MSAConvergence.PureFluidExponentialSplit

set_option linter.style.header false

/-! Exact node identities for the actual pure-fluid multi-tail BH root.
These are the algebraic residue coefficients needed by the proposed
H-function dressing; distinct rates are not needed for the node identities. -/
noncomputable section
open Real
namespace FMSA.Convergence.PureFluidNodeResidues
open FMSA.ExactMSA FMSA.Convergence.PureFluidExponentialSplit
variable {T : Type*} [Fintype T]

/-- The dressed tail strength `Lambda_t = rho D_t/F(z_t)` at a nonzero
factor node. The first root equation later identifies it with
`rho (2 pi K_t/z_t)/F(z_t)^2`. -/
def dressedStrength (xi : ℝ) (z D G : T → ℝ) (t : T) : ℝ :=
  rhoOf xi * D t / MultiTail.factor xi z D G (z t)

/-- The exponential coefficient at a node is the true second BH source
rewritten with the second root equation. -/
theorem node_exponentialPart_eq_G
    (xi : ℝ) (z K D G : T → ℝ) (hz : ∀ t, 0 < z t)
    (hroot : MultiTail.IsRoot xi z K D G) (t : T) :
    exponentialPart xi z D G (z t) =
      rhoOf xi * (2*Real.pi*G t*MultiTail.factor xi z D G (z t)) / z t := by
  rw [exponentialPart_eq_secondRHS xi z D G (z t) (hz t).ne'
    (fun u => (add_pos (hz t) (hz u)).ne')]
  rw [← hroot.2 t]

/-- At every actual root with a nonzero node factor, the W coefficient
is `Lambda_t` times the exponential part at that same node. -/
theorem node_W_dressed
    (xi : ℝ) (z K D G : T → ℝ) (hz : ∀ t, 0 < z t)
    (hroot : MultiTail.IsRoot xi z K D G) (t : T)
    (hF : MultiTail.factor xi z D G (z t) ≠ 0) :
    rhoOf xi * MultiTail.W xi z D G t =
      dressedStrength xi z D G t * exponentialPart xi z D G (z t) := by
  rw [node_exponentialPart_eq_G xi z K D G hz hroot t]
  unfold dressedStrength MultiTail.W
  field_simp [hF, (hz t).ne']

/-- The original BH identity `W + C exp(z) = D exp(z)` at node `t`
rewritten without the growing exponential. -/
theorem node_C_from_W (xi : ℝ) (z D G : T → ℝ) (t : T) :
    MultiTail.C xi z D G t =
      D t - exp (-(z t))*MultiTail.W xi z D G t := by
  have he : exp (-(z t))*exp (z t) = 1 := by
    rw [← exp_add]
    simp
  have h := MultiTail.W_add_C_exp xi z D G t
  calc
    MultiTail.C xi z D G t =
        exp (-(z t))*(MultiTail.C xi z D G t*exp (z t)) := by
          rw [show exp (-(z t))*(MultiTail.C xi z D G t*exp (z t)) =
            MultiTail.C xi z D G t*(exp (-(z t))*exp (z t)) by ring, he, mul_one]
    _ = exp (-(z t))*(D t*exp (z t)-MultiTail.W xi z D G t) := by
          congr 1
          linarith [h]
    _ = D t - exp (-(z t))*MultiTail.W xi z D G t := by
          rw [mul_sub]
          rw [show exp (-(z t))*(D t*exp (z t)) = D t by
            calc
              _ = D t*(exp (-(z t))*exp (z t)) := by ring
              _ = D t := by rw [he, mul_one]]

/-- The C coefficient is `Lambda_t` times the rational part at its node.
This is the actual-root residue identity underlying the proposed dressing. -/
theorem node_C_dressed
    (xi : ℝ) (z K D G : T → ℝ) (hz : ∀ t, 0 < z t)
    (hroot : MultiTail.IsRoot xi z K D G) (t : T)
    (hF : MultiTail.factor xi z D G (z t) ≠ 0) :
    rhoOf xi * MultiTail.C xi z D G t =
      dressedStrength xi z D G t * rationalPart xi z D G (z t) := by
  have hW := node_W_dressed xi z K D G hz hroot t hF
  have hC := node_C_from_W xi z D G t
  have hsplit := factor_split xi z D G (z t) (hz t).ne'
  have hLamF : dressedStrength xi z D G t *
      MultiTail.factor xi z D G (z t) = rhoOf xi * D t := by
    unfold dressedStrength
    field_simp [hF]
  calc
    rhoOf xi * MultiTail.C xi z D G t =
        rhoOf xi * (D t - exp (-(z t))*MultiTail.W xi z D G t) := by rw [hC]
    _ = dressedStrength xi z D G t * MultiTail.factor xi z D G (z t) -
          exp (-(z t))*(dressedStrength xi z D G t *
            exponentialPart xi z D G (z t)) := by rw [hLamF, ← hW]; ring
    _ = dressedStrength xi z D G t * rationalPart xi z D G (z t) := by
          rw [hsplit]
          ring

/-- The first ACTUAL root equation identifies the dressing strength with
the physical tail strength divided by the squared node factor. -/
theorem dressedStrength_eq_coupling
    (xi : ℝ) (z K D G : T → ℝ)
    (hroot : MultiTail.IsRoot xi z K D G) (t : T)
    (hF : MultiTail.factor xi z D G (z t) ≠ 0) :
    dressedStrength xi z D G t =
      rhoOf xi * (2*Real.pi*K t/z t) /
        (MultiTail.factor xi z D G (z t))^2 := by
  rw [← hroot.1 t]
  unfold dressedStrength
  field_simp [hF]

end FMSA.Convergence.PureFluidNodeResidues
/-- info: 'FMSA.Convergence.PureFluidNodeResidues.node_exponentialPart_eq_G' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidNodeResidues.node_exponentialPart_eq_G
/-- info: 'FMSA.Convergence.PureFluidNodeResidues.node_W_dressed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidNodeResidues.node_W_dressed
/-- info: 'FMSA.Convergence.PureFluidNodeResidues.node_C_from_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidNodeResidues.node_C_from_W
/-- info: 'FMSA.Convergence.PureFluidNodeResidues.node_C_dressed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidNodeResidues.node_C_dressed
/-- info: 'FMSA.Convergence.PureFluidNodeResidues.dressedStrength_eq_coupling' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidNodeResidues.dressedStrength_eq_coupling
