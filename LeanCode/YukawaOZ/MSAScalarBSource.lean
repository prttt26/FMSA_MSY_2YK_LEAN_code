import LeanCode.YukawaOZMix.MSABSourceHierarchy
import LeanCode.Analysis.CausalLaplaceComplex

/-! The actual scalar single-tail source is a single exponential at EVERY
finite order. The cancellation is proved from the BH amplitude dictionary,
not from a supplied finite-basis hypothesis. Unit hard-core diameter. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
namespace FMSA.ExactMSA.ScalarBSource
open BSource

def tailW (xi z D G : ℝ) : ℝ := 2 * π * rhoOf xi * G * D / z
def tailC (xi z D G : ℝ) : ℝ := gam xi z G * D
def deltaA (xi z D G : ℝ) : ℝ := msaA xi z D G - bA0 xi
def deltaQp (xi z D G : ℝ) : ℝ := msaQp xi z D G - qp0 xi
def kappa (xi z D G : ℝ) : ℝ := z * tailC xi z D G + deltaQp xi z D G

theorem background_first (xi z D G : ℝ) (hz : z ≠ 0) (hv : 1 - xi ≠ 0) :
    2 * z * deltaA xi z D G + rhoOf xi *
      (deltaA xi z D G * qp0 xi * z - deltaQp xi z D G * bA0 xi * z+
        2 * tailC xi z D G * bA0 xi * z + 2 * tailC xi z D G * bA0 xi+
        2 * tailW xi z D G * bA0 xi) = 0 := by
  simp only [deltaA, deltaQp, tailC, tailW, msaA, msaQp, Mtil, Ntil,
    gam, rhoOf, bA0, bB0, qp0]
  field_simp
  ring

theorem background_second (xi z D G : ℝ) (hz : z ≠ 0) (hv : 1 - xi ≠ 0) :
    2 * deltaQp xi z D G * z ^ 2 + rhoOf xi *
      (2 * tailC xi z D G * qp0 xi * z ^ 2 + 2 * tailC xi z D G * qp0 xi * z-
        tailC xi z D G * bA0 xi * z ^ 2 - 2 * tailC xi z D G * bA0 xi * z-
        2 * tailC xi z D G * bA0 xi + 2 * tailW xi z D G * qp0 xi * z-
        2 * tailW xi z D G * bA0 xi) = 0 := by
  simp only [deltaQp, tailC, tailW, msaQp, Mtil, Ntil, gam, rhoOf, bA0, bB0, qp0]
  field_simp
  ring

def qMoment {𝕜 : Type*} [Field 𝕜] (a b W C z s e : 𝕜) : 𝕜 :=
  (1 - s - e) / s ^ 2 * a + (1 - s + s ^ 2 / 2 - e) / s ^ 3 * b+
    W / (s + z) + C * (1 - e) / s + C * e / (s + z)

def sourceJ {𝕜 : Type*} [Field 𝕜] (A b C z s : 𝕜) : 𝕜 := A / s ^ 2 + b / s + z * C / (s + z)

/-- Exact algebraic cancellation, even with an arbitrary contact exponential e.
The two displayed background constraints are discharged above for actual BH data. -/
theorem symbol_cancellation {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]
    (rho a b A B W C z s e : 𝕜)
    (hs : s ≠ 0) (hz : z ≠ 0) (hsz : s + z ≠ 0)
    (h1 : 2 * z * A + rho * (A * a * z - B * b * z + 2 * C * b * z + 2 * C * b + 2 * W * b)=0)
    (h2 : 2 * B * z ^ 2 + rho * (2 * C * a * z ^ 2 + 2 * C * a * z - C * b * z ^ 2-
      2 * C * b * z - 2 * C * b + 2 * W * a * z - 2 * W * b)=0) :
    (1 - rho * qMoment a b 0 0 z s e) * sourceJ A B C z s+
      rho * sourceJ b a 0 z s * qMoment B A W C z s e = (z * C + B) / (s + z) := by
  unfold qMoment sourceJ
  have hid :
      (1 - rho * ((1 - s - e) / s ^ 2 * a + (1 - s + s ^ 2 / 2 - e) / s ^ 3 * b+
        0 / (s + z) + 0 * (1 - e) / s + 0 * e / (s + z)))*
        (A / s ^ 2 + B / s + z * C / (s + z))+
      rho * (b / s ^ 2 + a / s + z * 0 / (s + z))*
        ((1 - s - e) / s ^ 2 * B + (1 - s + s ^ 2 / 2 - e) / s ^ 3 * A+
          W / (s + z) + C * (1 - e) / s + C * e / (s + z)) - (z * C + B) / (s + z) =
      (2 * z * A + rho * (A * a * z - B * b * z + 2 * C * b * z + 2 * C * b + 2 * W * b)) / (2 * z * s ^ 2)+
      (2 * B * z ^ 2 + rho * (2 * C * a * z ^ 2 + 2 * C * a * z - C * b * z ^ 2-
        2 * C * b * z - 2 * C * b + 2 * W * a * z - 2 * W * b)) / (2 * z * s * (s + z)) := by
    field_simp [hs, hz, hsz]
    ring
  simp only [h1, h2, zero_div, add_zero] at hid
  simpa only [zero_div, add_zero] using sub_eq_zero.mp hid

def actualQ (xi z D G s : ℝ) : ℝ :=
  1 - rhoOf xi * qMoment (msaQp xi z D G) (msaA xi z D G)
    (tailW xi z D G) (tailC xi z D G) z s (exp (-s))

def actualF (xi z D G s : ℝ) : ℝ :=
  sourceJ (msaA xi z D G) (msaQp xi z D G) (tailC xi z D G) z s / (2 * π)

theorem actual_source_cancellation (xi z D G s : ℝ)
    (hz : z ≠ 0) (hv : 1 - xi ≠ 0) (hs : s ≠ 0) (hsz : s + z ≠ 0) :
    actualQ xi z 0 G s * (actualF xi z D G s - actualF xi z 0 G s)-
      actualF xi z 0 G s * (actualQ xi z D G s - actualQ xi z 0 G s) =
        kappa xi z D G / (2 * π * (s + z)) := by
  have h := symbol_cancellation (rhoOf xi) (qp0 xi) (bA0 xi)
    (deltaA xi z D G) (deltaQp xi z D G) (tailW xi z D G) (tailC xi z D G)
    z s (exp (-s)) hs hz hsz (background_first xi z D G hz hv)
    (background_second xi z D G hz hv)
  simp only [actualQ, actualF, qMoment, sourceJ, deltaA, deltaQp, tailW, tailC,
    msaA, msaQp, kappa, mul_zero, zero_mul, add_zero, sub_zero, div_zero] at h ⊢
  convert congrArg (fun x : ℝ => x / (2 * π)) h using 1 <;>
    field_simp <;> ring

def sourceKernel (xi z D G r : ℝ) : ℝ := kappa xi z D G / (2 * π) * exp (-z * r)

theorem sourceKernel_laplace (xi z D G s : ℝ) (hsz : 0 < s + z) :
    (∫ r in Ioi (0: ℝ), sourceKernel xi z D G r * exp (-s * r)) =
      kappa xi z D G / (2 * π * (s + z)) := by
  have he : (fun r => sourceKernel xi z D G r * exp (-s * r)) =
      fun r => (kappa xi z D G / (2 * π)) * exp (-(s + z) * r) := by
    funext r
    unfold sourceKernel
    rw [mul_assoc, ← exp_add]
    congr 2
    ring
  rw [he, integral_const_mul, integral_exp_mul_Ioi (by linarith : -(s + z)<0)]
  simp only [mul_zero, exp_zero, neg_div_neg_eq]
  field_simp [hsz.ne'] <;> ring


theorem kappa_affine (xi z D G : ℝ) :
    kappa xi z D G = D * (kappa xi z 1 0 +
      (kappa xi z 1 1 - kappa xi z 1 0) * G) := by
  simp only [kappa, tailC, deltaQp, msaQp, gam, Mtil, Ntil]
  ring

/-- Constructed actual source family has one fixed spatial shape at all orders. -/
theorem source_jet_shape (xi z : ℝ) (D G : ℝ → ℝ) (n : ℕ) (r : ℝ)
    (hc : ContDiffAt ℝ n (fun t => kappa xi z (D t) (G t)) 0) :
    jet (fun t => sourceKernel xi z (D t) (G t) r) n =
      jet (fun t => kappa xi z (D t) (G t)) n / (2 * π) * exp (-z * r) := by
  have he : (fun t => sourceKernel xi z (D t) (G t) r) =
      fun t => kappa xi z (D t) (G t) * (exp (-z * r) / (2 * π)) := by
    funext t
    unfold sourceKernel
    ring
  rw [he]
  unfold jet
  rw [iteratedDeriv_mul_const_field]
  ring

theorem jet_linear (f g : ℝ → ℝ) (a b : ℝ) (n : ℕ)
    (hf : ContDiffAt ℝ n f 0) (hg : ContDiffAt ℝ n g 0) :
    jet (fun t => a * f t + b * g t) n = a * jet f n + b * jet g n := by
  unfold jet
  rw [iteratedDeriv_fun_add (show ContDiffAt ℝ n (fun t => a * f t) 0 from contDiffAt_const.mul hf)
    (show ContDiffAt ℝ n (fun t => b * g t) 0 from contDiffAt_const.mul hg),
    iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field]
  ring

/-- The source amplitude itself is a finite triangular coefficient expression. -/
theorem kappa_jet (xi z : ℝ) (D G : ℝ → ℝ) (n : ℕ)
    (hn : 0 < n) (hD0 : D 0 = 0)
    (hD : ContDiffAt ℝ n D 0) (hG : ContDiffAt ℝ n G 0) :
    jet (fun t => kappa xi z (D t) (G t)) n =
      kappa xi z 1 (G 0) * jet D n+
      (kappa xi z 1 1 - kappa xi z 1 0) * lowerProduct (jet D) (jet G) n := by
  have he : (fun t => kappa xi z (D t) (G t)) =
      fun t => kappa xi z 1 0 * D t + (kappa xi z 1 1 - kappa xi z 1 0) * (D t * G t) := by
    funext t
    rw [kappa_affine]
    ring
  rw [he, jet_linear D (fun t => D t * G t) _ _ n hD (hD.mul hG),
    normalized_mul D G n hD hG, convolution_split (jet D) (jet G) n hn]
  simp only [jet, iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one, hD0,
    zero_mul, zero_add]
  rw [kappa_affine xi z 1 (G 0)]
  ring

theorem kappa_seed_residual (xi z G : ℝ) (hz : z ≠ 0) (hv : 1 - xi ≠ 0) :
    kappa xi z 1 G * F0 xi z - z =
      (kappa xi z 1 1 - kappa xi z 1 0) / (2 * π) * (2 * π * G * F0 xi z - bhP0 xi z) := by
  simp only [kappa, tailC, deltaQp, msaQp, Mtil, Ntil, gam, F0, Qhat0,
    phi1, phi2, bhP0, bA0, bB0, qp0, rhoOf]
  field_simp
  ring

theorem kappa_seed (xi z G : ℝ) (hz : z ≠ 0) (hv : 1 - xi ≠ 0)
    (hF : F0 xi z ≠ 0) (hbase : 2 * π * G * F0 xi z = bhP0 xi z) :
    kappa xi z 1 G = z / F0 xi z := by
  have h := kappa_seed_residual xi z G hz hv
  rw [hbase, sub_self, mul_zero] at h
  apply (eq_div_iff hF).mpr
  linarith

theorem first_source_amplitude (xi z K G D1 : ℝ)
    (hz : z ≠ 0) (hv : 1 - xi ≠ 0) (hF : F0 xi z ≠ 0)
    (hbase : 2 * π * G * F0 xi z = bhP0 xi z)
    (hD1 : D1 = 2 * π * K / (z * F0 xi z)) :
    kappa xi z 1 G * D1 = 2 * π * K / (F0 xi z) ^ 2 := by
  rw [kappa_seed xi z G hz hv hF hbase, hD1]
  field_simp

end FMSA.ExactMSA.ScalarBSource
