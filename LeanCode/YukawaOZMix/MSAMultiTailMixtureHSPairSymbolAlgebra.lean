import LeanCode.YukawaOZMix.MSAMultiTailMixtureHSPairSeed

/-! Finite algebra used by the proposed actual HS Fourier route.
No actual RDF transform/source dictionary or OZ equation is inferred here.
The phase variables are retained, including the right inverse phase. -/
noncomputable section
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture

def hsPairSymbolP (x e s : ℂ) : ℂ := (2-s*x-(2+s*x)*e)/(2*s^3)
def hsPairSymbolT (x e s : ℂ) : ℂ := (1-s*x-e)/s^2
def hsPairSymbolAlpha (a c x : ℂ) : ℂ := a*(1+c*x)
def hsPairSymbolBeta (a x : ℂ) : ℂ := a*x/2
def hsPairSymbolAA (a c m0 m1 m2 : ℂ) : ℂ := a^2*(m0+2*c*m1+c^2*m2)
def hsPairSymbolAB (a c m1 m2 : ℂ) : ℂ := a^2*(m1+c*m2)/2
def hsPairSymbolBB (a m2 : ℂ) : ℂ := a^2*m2/4
def hsPairSymbolSource (a c x y s : ℂ) : ℂ :=
  hsPairSymbolAlpha a c x/s^2+hsPairSymbolBeta a x/s+y*hsPairSymbolAlpha a c x/(2*s)
def hsPairSymbolSourceProduct (p t a c m0 m1 m2 y s : ℂ) : ℂ :=
  p*(hsPairSymbolAA a c m0 m1 m2/s^2+hsPairSymbolAB a c m1 m2/s+
      y*hsPairSymbolAA a c m0 m1 m2/(2*s))+
    t*(hsPairSymbolAB a c m1 m2/s^2+hsPairSymbolBB a m2/s+
      y*hsPairSymbolAB a c m1 m2/(2*s))
def hsPairSymbolC (a c m0 m1 m2 x y L M s : ℂ) : ℂ :=
  hsPairSymbolP x L s*hsPairSymbolAlpha a c y+hsPairSymbolT x L s*hsPairSymbolBeta a y+
    hsPairSymbolP y (1/M) (-s)*hsPairSymbolAlpha a c x+
    hsPairSymbolT y (1/M) (-s)*hsPairSymbolBeta a x-
    (hsPairSymbolP x L s*hsPairSymbolP y (1/M) (-s)*hsPairSymbolAA a c m0 m1 m2+
      (hsPairSymbolP x L s*hsPairSymbolT y (1/M) (-s)+
        hsPairSymbolT x L s*hsPairSymbolP y (1/M) (-s))*hsPairSymbolAB a c m1 m2+
      hsPairSymbolT x L s*hsPairSymbolT y (1/M) (-s)*hsPairSymbolBB a m2)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem hsPairSymbol_residual_factor (a c m0 m1 m2 x y L M s : ℂ)
    (hs : s ≠ 0) (hL : L ≠ 0) (hM : M ≠ 0) :
    L*(hsPairSymbolSource a c x y s-
      hsPairSymbolSourceProduct (hsPairSymbolP x (1/L) (-s)) (hsPairSymbolT x (1/L) (-s))
        a c m0 m1 m2 y s)-
    (hsPairSymbolSource a c x y (-s)-
      hsPairSymbolSourceProduct (hsPairSymbolP x L s) (hsPairSymbolT x L s)
        a c m0 m1 m2 y (-s))/M+s*hsPairSymbolC a c m0 m1 m2 x y L M s =
    a*(a*m2-4*c)*(-L*x+L*y+s*x*y+x-y)/(4*s^2) := by
  unfold hsPairSymbolSource hsPairSymbolSourceProduct hsPairSymbolC
    hsPairSymbolP hsPairSymbolT hsPairSymbolAlpha hsPairSymbolBeta
    hsPairSymbolAA hsPairSymbolAB hsPairSymbolBB
  field_simp [hs, hL, hM]
  ring

theorem hsPairSymbol_identity_of_HS_relation (a c m0 m1 m2 x y L M s : ℂ)
    (hs : s ≠ 0) (hL : L ≠ 0) (hM : M ≠ 0) (hHS : a*m2=4*c) :
    L*(hsPairSymbolSource a c x y s-
      hsPairSymbolSourceProduct (hsPairSymbolP x (1/L) (-s)) (hsPairSymbolT x (1/L) (-s))
        a c m0 m1 m2 y s)-
    (hsPairSymbolSource a c x y (-s)-
      hsPairSymbolSourceProduct (hsPairSymbolP x L s) (hsPairSymbolT x L s)
        a c m0 m1 m2 y (-s))/M= -s*hsPairSymbolC a c m0 m1 m2 x y L M s := by
  have he := hsPairSymbol_residual_factor a c m0 m1 m2 x y L M s hs hL hM
  rw [hHS, sub_self, mul_zero, zero_mul, zero_div] at he
  linear_combination he

end FMSA.ExactMSA.MultiTailMixture
