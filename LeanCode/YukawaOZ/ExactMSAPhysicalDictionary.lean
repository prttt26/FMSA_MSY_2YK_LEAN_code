import LeanCode.YukawaOZ.ExactMSARationalData
namespace FMSA.ExactMSA.RationalBridge
open Real SparseCertificate SparseCheckpoints
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def deltaActual (xi z k Dt G K : ℝ) : ℝ :=
  (rhoOf xi *
        (4 * π / k *
            (-((msaA xi z Dt G / (2 * π)) ^ 2 - (1 + 2 * xi) ^ 2 / (1 - xi) ^ 4) *
                    ((sin k - k * cos k) / k ^ 2) +
                  -((msaQp xi z Dt G + z * gam xi z G * Dt) / (2 * π) - K -
                              (msaA xi z Dt G / (2 * π)) ^ 2 -
                            xi * (msaA xi z Dt G / (2 * π)) ^ 2 / 2 -
                          24 * xi * K * G * (1 - rexp (-z)) / z -
                        (24 * xi * K * G) ^ 2 * (1 - rexp (-z)) ^ 2 / (4 * K * z ^ 2) -
                      -6 * xi * (1 + xi / 2) ^ 2 / (1 - xi) ^ 4) *
                    ((2 / k ^ 3 - 1 / k) * cos k + 2 / k ^ 2 * sin k - 2 / k ^ 3) +
                -(xi * ((msaA xi z Dt G / (2 * π)) ^ 2 - (1 + 2 * xi) ^ 2 / (1 - xi) ^ 4) / 2) *
                  ((-24 / k ^ 5 + 12 / k ^ 3 - 1 / k) * cos k +
                      (-24 / k ^ 4 + 4 / k ^ 2) * sin k + 24 / k ^ 5) +
              -(24 * xi * K * G / z) *
                ((1 - cos k) / k -
                  (k - rexp (-z) * (k * cos k + z * sin k)) / (z ^ 2 + k ^ 2)) +
            -((24 * xi * K * G) ^ 2 / (2 * K * z ^ 2)) *
              (1 / 2 * rexp (-z) *
                    ((k - rexp z * (k * cos k - z * sin k)) / (z ^ 2 + k ^ 2)) +
                  1 / 2 * rexp (-z) *
                    ((k - rexp (-z) * (k * cos k + z * sin k)) / (z ^ 2 + k ^ 2)) -
                rexp (-z) * ((1 - cos k) / k))) +
          4 * π * K / k * ((k * cos k + z * sin k) / (z ^ 2 + k ^ 2)))) - (2 * Dt * ((1 - msaQre xi z 0 G k) * msaRez xi z G k -
            msaQim xi z 0 G k * msaImz xi z G k) -
        Dt ^ 2 * (msaRez xi z G k ^ 2 + msaImz xi z G k ^ 2))

variable (xi z k Dt G K : ℝ)
theorem bhF_dictionary (hvac : 1-xi ≠ 0) (hz : z ≠ 0) :
    bhF xi z (Dt,G) = fSource xi z k G (Real.cos k) (Real.sin k) (Real.exp (-z)) Real.pi Dt K := by
  have hvacAdd : 1 + -xi ≠ 0 := by simpa only [← sub_eq_add_neg] using hvac
  dsimp only [fSource,bhF,bhFRest,F0,Qhat0,phi1,phi2,bA0,bB0,qp0,rhoOf,Mtil,Ntil,tailtil,gam]
  field_simp [hvac,hvacAdd,hz,Real.pi_ne_zero]
  sparse_ring
#print axioms bhF_dictionary

theorem bhP_dictionary (hvac : 1-xi ≠ 0) (hz : z ≠ 0) :
    bhP xi z (Dt,G) = pSource xi z k G (Real.cos k) (Real.sin k) (Real.exp (-z)) Real.pi Dt K := by
  have hvacAdd : 1 + -xi ≠ 0 := by simpa only [← sub_eq_add_neg] using hvac
  dsimp only [pSource,bhP,bhP0,bhPRest,bA0,bB0,qp0,rhoOf,Mtil,Ntil,gam]
  field_simp [hvac,hvacAdd,hz,Real.pi_ne_zero]
  sparse_ring
#print axioms bhP_dictionary

end FMSA.ExactMSA.RationalBridge
