import LeanCode.YukawaOZMix.MatExactMSAEqualDiamCertificate
import LeanCode.YukawaOZMix.MSAMixtureFinOne
import LeanCode.YukawaOZMix.MixtureBlumHoyeDerivation

/-! Default dependency gates for the four retired matrix axioms and their faithful bridges. -/

/-- info: 'FMSA.ExactMSA.MultiTailMixture.W_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MultiTailMixture.W_single

/-- info: 'FMSA.ExactMSA.MultiTailMixture.C_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MultiTailMixture.C_single

/-- info: 'FMSA.ExactMSA.MultiTailMixture.amplitudeA_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MultiTailMixture.amplitudeA_single

/-- info: 'FMSA.ExactMSA.MultiTailMixture.amplitudeQp_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MultiTailMixture.amplitudeQp_single

/-- info: 'FMSA.ExactMSA.MultiTailMixture.Qhat_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MultiTailMixture.Qhat_single

/-- info: 'FMSA.ExactMSA.MultiTailMixture.QhatComplex_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MultiTailMixture.QhatComplex_single

/-- info: 'FMSA.ExactMSA.MultiTailMixture.dressedQhat_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MultiTailMixture.dressedQhat_single

/-- info: 'FMSA.ExactMSA.MultiTailMixture.isRoot_single_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MultiTailMixture.isRoot_single_iff

/-- info: 'FMSA.ExactMSA.MultiTailMixture.q_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MultiTailMixture.q_single

/-- info: 'FMSA.ExactMSA.MultiTailMixture.qPrime_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MultiTailMixture.qPrime_single

/-- info: 'FMSA.ExactMSA.MultiTailMixture.correlation_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MultiTailMixture.correlation_single

/-- info: 'FMSA.ExactMSA.MultiTailMixture.legacyRadial_eq_closed_ae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MultiTailMixture.legacyRadial_eq_closed_ae

/-- info: 'FMSA.ExactMSA.MultiTailMixture.fourierFactor_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MultiTailMixture.fourierFactor_single

/-- info: 'FMSA.ExactMSA.MultiTailMixture.FtMSAuneq_conjTranspose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MultiTailMixture.FtMSAuneq_conjTranspose

/-- info: 'FMSA.ExactMSA.MultiTailMixture.legacyRadial_matrix_gram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MultiTailMixture.legacyRadial_matrix_gram

/-- info: 'FMSA.ExactMSA.MultiTailMixture.legacyHS_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MultiTailMixture.legacyHS_root

/-- info: 'FMSA.ExactMSA.MultiTailMixture.legacyRadial_radius_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MultiTailMixture.legacyRadial_radius_integrable

/-- info: 'FMSA.ExactMSA.MultiTailMixture.legacyHS_radial_eq_closed_ae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MultiTailMixture.legacyHS_radial_eq_closed_ae

/-- info: 'FMSA.ExactMSA.MultiTailMixture.legacyTail_radius_integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MultiTailMixture.legacyTail_radius_integrable

/-- info: 'FMSA.ExactMSA.MultiTailMixture.legacyRadial_fourier_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MultiTailMixture.legacyRadial_fourier_split

/-- info: 'FMSA.ExactMSA.MultiTailMixture.radial_fourier_congr_positive_ae' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MultiTailMixture.radial_fourier_congr_positive_ae

/-- info: 'FMSA.ExactMSA.MultiTailMixture.FtMSAuneq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MultiTailMixture.FtMSAuneq_zero

/-- info: 'FMSA.ExactMSA.MultiTailMixture.legacyHS_matrix_gram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MultiTailMixture.legacyHS_matrix_gram

/-- info: 'FMSA.ExactMSA.MultiTailMixture.legacyUnequal_hcore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MultiTailMixture.legacyUnequal_hcore

/-- info: 'FMSA.ExactMSA.MixLeg3.qhatMixRuneq_eq_qhatMixR_of_equal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MixLeg3.qhatMixRuneq_eq_qhatMixR_of_equal

/-- info: 'FMSA.ExactMSA.MixLeg3.MixBHRoot_of_MixBHRootUneq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MixLeg3.MixBHRoot_of_MixBHRootUneq

/-- info: 'FMSA.ExactMSA.MixLeg3.MixBHRootUneq_of_MixBHRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MixLeg3.MixBHRootUneq_of_MixBHRoot

/-- info: 'FMSA.ExactMSA.MixLeg3.qhatMixCuneq_eq_qhatMixC_of_equal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MixLeg3.qhatMixCuneq_eq_qhatMixC_of_equal

/-- info: 'FMSA.ExactMSA.MixLeg3.FtMSAuneq_eq_FtMSA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MixLeg3.FtMSAuneq_eq_FtMSA

/-- info: 'FMSA.ExactMSA.MixLeg3.FtHSuneq_eq_FtHS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MixLeg3.FtHSuneq_eq_FtHS

/-- info: 'FMSA.ExactMSA.MixLeg3.Ft1uneq_eq_Ft1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MixLeg3.Ft1uneq_eq_Ft1

/-- info: 'FMSA.ExactMSA.MultiTailMixture.legacySingle_LNumerator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MultiTailMixture.legacySingle_LNumerator

/-- info: 'FMSA.ExactMSA.MultiTailMixture.legacySingle_JNumerator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MultiTailMixture.legacySingle_JNumerator

/-- info: 'FMSA.ExactMSA.MultiTailMixture.legacySingle_U_coeff6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MultiTailMixture.legacySingle_U_coeff6

/-- info: 'FMSA.ExactMSA.MultiTailMixture.legacyOuterNumerator_continuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MultiTailMixture.legacyOuterNumerator_continuous

/-- info: 'FMSA.ExactMSA.MultiTailMixture.correlation_equalDiam_reciprocal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MultiTailMixture.correlation_equalDiam_reciprocal

/-- info: 'FMSA.ExactMSA.MultiTailMixture.legacyOuterNumerator_equalDiam_reciprocal_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MultiTailMixture.legacyOuterNumerator_equalDiam_reciprocal_zero

/-- info: 'FMSA.ExactMSA.MultiTailMixture.legacyOuterNumerator_origin_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MultiTailMixture.legacyOuterNumerator_origin_sum

/-- info: 'FMSA.ExactMSA.MultiTailMixture.qpMat_equalDiam_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MultiTailMixture.qpMat_equalDiam_rows

/-- info: 'FMSA.ExactMSA.MultiTailMixture.legacyEqual_core_origin_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MultiTailMixture.legacyEqual_core_origin_zero

/-- info: 'FMSA.ExactMSA.MultiTailMixture.legacyS_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MultiTailMixture.legacyS_entry

/-- info: 'FMSA.ExactMSA.MultiTailMixture.Wt_matrix_dictionary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MultiTailMixture.Wt_matrix_dictionary

/-- info: 'FMSA.ExactMSA.MultiTailMixture.legacyRoot_first_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MultiTailMixture.legacyRoot_first_matrix

/-- info: 'FMSA.ExactMSA.MultiTailMixture.legacyRoot_second_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MultiTailMixture.legacyRoot_second_matrix

/-- info: 'FMSA.ExactMSA.MultiTailMixture.legacyD_S_contraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MultiTailMixture.legacyD_S_contraction

/-- info: 'FMSA.ExactMSA.MultiTailMixture.legacyW_S_contraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MultiTailMixture.legacyW_S_contraction

/-- info: 'FMSA.ExactMSA.MultiTailMixture.legacyW_root_contraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MultiTailMixture.legacyW_root_contraction

/-- info: 'FMSA.ExactMSA.MultiTailMixture.legacyCt_equalDiam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MultiTailMixture.legacyCt_equalDiam

/-- info: 'FMSA.ExactMSA.MultiTailMixture.legacyEm_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MultiTailMixture.legacyEm_kernel

/-- info: 'FMSA.ExactMSA.MultiTailMixture.legacyEp_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MultiTailMixture.legacyEp_kernel

/-- info: 'FMSA.ExactMSA.MultiTailMixture.legacyWeighted_transpose_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MultiTailMixture.legacyWeighted_transpose_entry

/-- info: 'FMSA.ExactMSA.MultiTailMixture.legacyEm_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MultiTailMixture.legacyEm_matrix

/-- info: 'FMSA.ExactMSA.MultiTailMixture.legacyEp_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MultiTailMixture.legacyEp_matrix

/-- info: 'FMSA.ExactMSA.MultiTailMixture.legacyZ_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MultiTailMixture.legacyZ_entry

/-- info: 'FMSA.ExactMSA.MultiTailMixture.coreC5_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MultiTailMixture.coreC5_swap

/-- info: 'FMSA.ExactMSA.MultiTailMixture.legacyLinear_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MultiTailMixture.legacyLinear_entry

/-- info: 'FMSA.ExactMSA.MultiTailMixture.legacyEqual_exp_coefficients' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MultiTailMixture.legacyEqual_exp_coefficients

/-- info: 'FMSA.ExactMSA.MultiTailMixture.legacyC1_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MultiTailMixture.legacyC1_kernel

/-- info: 'FMSA.ExactMSA.MultiTailMixture.legacyC2_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MultiTailMixture.legacyC2_kernel

/-- info: 'FMSA.ExactMSA.MultiTailMixture.legacyC3_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MultiTailMixture.legacyC3_zero

/-- info: 'FMSA.ExactMSA.MultiTailMixture.legacyEqual_poly_coefficients' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MultiTailMixture.legacyEqual_poly_coefficients

/-- info: 'FMSA.ExactMSA.MultiTailMixture.legacyEqual_core_pointwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MultiTailMixture.legacyEqual_core_pointwise

/-- info: 'FMSA.ExactMSA.MultiTailMixture.legacyEqual_core_ae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MultiTailMixture.legacyEqual_core_ae

/-- info: 'MSAMixture.matExactMSAEqualDiam_hcore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MSAMixture.matExactMSAEqualDiam_hcore

/-- info: 'MSAMixture.matMSAmixture_equalDiam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MSAMixture.matMSAmixture_equalDiam

/-- info: 'MSAMixture.matMSAmixture_equalDiam_WH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MSAMixture.matMSAmixture_equalDiam_WH

/-- info: 'MSAMixture.matExactMSAUnequalDiam_hcore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MSAMixture.matExactMSAUnequalDiam_hcore

/-- info: 'MSAMixture.matHSexactUnequalDiam_kspace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MSAMixture.matHSexactUnequalDiam_kspace

/-- info: 'MSAMixture.matMSAmixture_unequalDiam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MSAMixture.matMSAmixture_unequalDiam

/-- info: 'MSAMixture.matMSAmixture_unequalDiam_of_hcore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MSAMixture.matMSAmixture_unequalDiam_of_hcore

/-- info: 'MSAMixture.matMSAmixture_unequalDiam_physical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MSAMixture.matMSAmixture_unequalDiam_physical

/-- info: 'MSAMixture.matMSAmixture_fin_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MSAMixture.matMSAmixture_fin_one

/-- info: 'MSAMixture.msaMixture_reduces_to_scalar_at_fin_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MSAMixture.msaMixture_reduces_to_scalar_at_fin_one

/-- info: 'FMSA.ExactMSA.MatEqualDiamCertificate.matExactMSAEqualDiam_kspace_residual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MatEqualDiamCertificate.matExactMSAEqualDiam_kspace_residual

/-- info: 'FMSA.ExactMSA.MatEqualDiamCertificate.matExactMSAEqualDiam_hcore_of_residual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MatEqualDiamCertificate.matExactMSAEqualDiam_hcore_of_residual

/-- info: 'FMSA.ExactMSA.MixLeg3.matMSAmixture_unequalDiam_of_oz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MixLeg3.matMSAmixture_unequalDiam_of_oz

/-- info: 'FMSA.ExactMSA.MixLeg3.matMSAmixture_unequalDiam_physical_of_oz' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.ExactMSA.MixLeg3.matMSAmixture_unequalDiam_physical_of_oz

