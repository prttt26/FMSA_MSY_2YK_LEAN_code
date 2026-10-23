import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic

/-! Thermodynamic scope of a structural mixture closure.
These are route-obstruction and coexistence algebra theorems. They do not
identify any constructed MSA DCF with an energy-route free-energy Hessian,
and the binary example is a thermodynamic counterexample, not an MSA state.
The PY pressure formulas below are explicit standard route formulas; their
identification with the project's actual RDF/DCF integrals is not assumed. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace FMSA.ExactMSA.MixtureThermodynamicScope

variable {N : ℕ}

/-- A negative thermodynamic curvature direction cannot be the same matrix
as a positive semidefinite structural inverse susceptibility. -/
theorem negative_curvature_obstructs_route_identity
    (S H : Matrix (Fin N) (Fin N) ℝ) (hS : S.PosSemidef)
    (v : Fin N → ℝ) (hH : star v ⬝ᵥ (H *ᵥ v) < 0) : H ≠ S := by
  intro he
  rw [he] at hH
  exact (not_lt_of_ge (hS.dotProduct_mulVec_nonneg v)) hH

/-- In particular, a real Baxter Gram representation alone cannot certify
the unstable curvature of a different thermodynamic route. -/
theorem negative_curvature_obstructs_baxter_gram_identity
    (F H : Matrix (Fin N) (Fin N) ℝ) (v : Fin N → ℝ)
    (hH : star v ⬝ᵥ (H *ᵥ v) < 0) : H ≠ F * F.conjTranspose :=
  negative_curvature_obstructs_route_identity _ H
    (Matrix.posSemidef_self_mul_conjTranspose F) v hH

def mixturePressure (ρ μ : Fin N → ℝ) (f : ℝ) : ℝ := ρ ⬝ᵥ μ - f

/-- With ALL chemical potentials fixed, pressure equality is the common
tangent-plane intercept condition. A composition-weighted scalar is weaker. -/
theorem pressure_eq_iff_common_tangent
    (ρa ρb μ : Fin N → ℝ) (fa fb : ℝ) :
    mixturePressure ρa μ fa = mixturePressure ρb μ fb ↔
      fb - fa = (ρb - ρa) ⬝ᵥ μ := by
  simp only [mixturePressure, sub_dotProduct]
  constructor <;> intro h <;> linarith

def binaryFreeEnergy (x y : ℝ) : ℝ := x^2 - y^2

theorem binaryFreeEnergy_partial_x (x y : ℝ) :
    HasDerivAt (fun t => binaryFreeEnergy t y) (2*x) x := by
  simpa [binaryFreeEnergy] using ((hasDerivAt_id x).pow 2).sub_const (y^2)

theorem binaryFreeEnergy_partial_y (x y : ℝ) :
    HasDerivAt (fun t => binaryFreeEnergy x t) (-2*y) y := by
  simpa [binaryFreeEnergy] using ((hasDerivAt_id y).pow 2).const_sub (x^2)

/-- Along the equimolar density ray both the free energy and pressure are
identically zero. This scalar degeneracy is not binary phase equilibrium. -/
theorem binaryFreeEnergy_equimolar_ray (t : ℝ) :
    binaryFreeEnergy t t = 0 ∧
      mixturePressure ![t,t] ![2*t,-2*t] (binaryFreeEnergy t t) = 0 := by
  simp [binaryFreeEnergy, mixturePressure, dotProduct, Fin.sum_univ_two]

/-- Equal pressure, equal composition-weighted chemical potential, and even
the tangent intercept along the density ray do NOT force componentwise
chemical-potential equality. The chemical potentials are actual partial
derivatives of the same polynomial free energy (proved above). -/
theorem fixed_composition_scalar_conditions_insufficient :
    mixturePressure ![1,1] ![2,-2] (binaryFreeEnergy 1 1) =
      mixturePressure ![2,2] ![4,-4] (binaryFreeEnergy 2 2) ∧
    (![1/2,1/2] : Fin 2 → ℝ) ⬝ᵥ ![2,-2] =
      (![1/2,1/2] : Fin 2 → ℝ) ⬝ᵥ ![4,-4] ∧
    binaryFreeEnergy 2 2 - binaryFreeEnergy 1 1 =
      ((![2,2] : Fin 2 → ℝ) - ![1,1]) ⬝ᵥ ![2,-2] ∧
    (![2,-2] : Fin 2 → ℝ) ≠ ![4,-4] := by
  norm_num [mixturePressure, binaryFreeEnergy, dotProduct, Fin.sum_univ_two,
    funext_iff, Fin.forall_fin_two]

/-- Dimensionless PY mixture pressure, scaled by pi/6. Here m_k are the
packing moments (pi/6) sum_i rho_i sigma_i^k and eta=m_3. -/
def pyCompressibilityPressure (m0 m1 m2 η : ℝ) : ℝ :=
  m0/(1-η) + 3*m1*m2/(1-η)^2 + 3*m2^3/(1-η)^3

def pyVirialPressure (m0 m1 m2 η : ℝ) : ℝ :=
  m0/(1-η) + 3*m1*m2/(1-η)^2 + 3*m2^3/(1-η)^2

theorem py_pressure_route_difference (m0 m1 m2 η : ℝ) (hη : η ≠ 1) :
    pyCompressibilityPressure m0 m1 m2 η - pyVirialPressure m0 m1 m2 η =
      3*η*m2^3/(1-η)^3 := by
  unfold pyCompressibilityPressure pyVirialPressure
  field_simp [sub_ne_zero.mpr (Ne.symm hη)]
  ring

/-- The prescribed PY mixture routes already differ at zero tail coupling
for positive packing fraction and positive second packing moment. Raising
the Yukawa coupling expansion order cannot change its tau=0 seed value. -/
theorem py_pressure_routes_strictly_differ (m0 m1 m2 η : ℝ)
    (hη0 : 0 < η) (hη1 : η < 1) (hm2 : 0 < m2) :
    pyVirialPressure m0 m1 m2 η < pyCompressibilityPressure m0 m1 m2 η := by
  have hd := py_pressure_route_difference m0 m1 m2 η (ne_of_lt hη1)
  have hp : 0 < 3*η*m2^3/(1-η)^3 := by positivity
  linarith

def couplingPressureJet (a : ℕ → ℝ) (order : ℕ) (τ : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (order+1), a n*τ^n

theorem couplingPressureJet_zero (a : ℕ → ℝ) (order : ℕ) :
    couplingPressureJet a order 0 = a 0 := by
  unfold couplingPressureJet
  rw [Finset.sum_eq_single 0]
  · simp
  · intro n _ hn
    simp [zero_pow hn]
  · simp

/-- This is a coefficient-level obstruction for any finite coupling order,
including zeroth and first order. It is conditional on retaining the two
prescribed PY seed routes, not an identification of physical jet coefficients. -/
theorem py_seed_route_mismatch_every_finite_order
    (a b : ℕ → ℝ) (order : ℕ) (m0 m1 m2 η : ℝ)
    (ha : a 0 = pyCompressibilityPressure m0 m1 m2 η)
    (hb : b 0 = pyVirialPressure m0 m1 m2 η)
    (hη0 : 0 < η) (hη1 : η < 1) (hm2 : 0 < m2) :
    couplingPressureJet b order 0 < couplingPressureJet a order 0 := by
  rw [couplingPressureJet_zero, couplingPressureJet_zero, ha, hb]
  exact py_pressure_routes_strictly_differ m0 m1 m2 η hη0 hη1 hm2

end FMSA.ExactMSA.MixtureThermodynamicScope
