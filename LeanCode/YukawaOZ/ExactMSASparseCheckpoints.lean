import LeanCode.YukawaOZ.ExactMSASparseSmall
import LeanCode.YukawaOZ.ExactMSASparseDt1
import LeanCode.YukawaOZ.ExactMSASparseDt2
import LeanCode.YukawaOZ.ExactMSASparseReassembly

-- Fail the build if a physical axiom or an admitted proof enters these certificates.
/-- info: 'FMSA.ExactMSA.SparseCheckpoints.small323_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.SparseCheckpoints.small323_identity

/-- info: 'FMSA.ExactMSA.SparseCheckpoints.dt1_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.SparseCheckpoints.dt1_identity

/-- info: 'FMSA.ExactMSA.SparseCheckpoints.dt2_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.SparseCheckpoints.dt2_identity

/-- info: 'FMSA.ExactMSA.SparseCheckpoints.full_division_reassembled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.SparseCheckpoints.full_division_reassembled

/-- info: 'FMSA.ExactMSA.SparseCheckpoints.full_division_zero_of_residual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.SparseCheckpoints.full_division_zero_of_residual
