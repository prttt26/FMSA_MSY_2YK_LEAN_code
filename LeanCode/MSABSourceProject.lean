import LeanCode.YukawaOZMix.MSABSourceHierarchy
import LeanCode.YukawaOZ.MSAScalarBSource
import LeanCode.YukawaOZ.MSABHJetRecurrence
import LeanCode.YukawaOZ.MSAScalarBSourceComplex
import LeanCode.YukawaOZMix.MSAMixtureFiniteBSource
import LeanCode.YukawaOZMix.MSABSourceTransfer
import LeanCode.YukawaOZMix.MSAMixtureBHJetRecurrence

/-! Actual finite renewal-source extension: axiom-footprint build gates.
Fourier-OZ B and one-sided source kernels have distinct scope. -/

/-- info: 'FMSA.ExactMSA.BSource.normalized_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.BSource.normalized_mul

/-- info: 'FMSA.ExactMSA.BSource.convolution_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.BSource.convolution_split

/-- info: 'FMSA.ExactMSA.BSource.bhFRest_affine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.BSource.bhFRest_affine

/-- info: 'FMSA.ExactMSA.BSource.bhPRest_affine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.BSource.bhPRest_affine

/-- info: 'FMSA.ExactMSA.BSource.solve_D_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.BSource.solve_D_order

/-- info: 'FMSA.ExactMSA.BSource.solve_G_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.BSource.solve_G_order

/-- info: 'FMSA.ExactMSA.BSource.source_reconstruction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.BSource.source_reconstruction

/-- info: 'FMSA.ExactMSA.BSource.matrix_source_reconstruction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.BSource.matrix_source_reconstruction

/-- info: 'FMSA.ExactMSA.BSource.fourier_second_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.BSource.fourier_second_order

/-- info: 'FMSA.ExactMSA.BSource.fourier_zero_obstruction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.BSource.fourier_zero_obstruction

/-- info: 'FMSA.ExactMSA.ScalarBSource.background_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.ScalarBSource.background_first

/-- info: 'FMSA.ExactMSA.ScalarBSource.background_second' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.ScalarBSource.background_second

/-- info: 'FMSA.ExactMSA.ScalarBSource.symbol_cancellation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.ScalarBSource.symbol_cancellation

/-- info: 'FMSA.ExactMSA.ScalarBSource.actual_source_cancellation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.ScalarBSource.actual_source_cancellation

/-- info: 'FMSA.ExactMSA.ScalarBSource.sourceKernel_laplace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.ScalarBSource.sourceKernel_laplace

/-- info: 'FMSA.ExactMSA.ScalarBSource.kappa_affine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.ScalarBSource.kappa_affine

/-- info: 'FMSA.ExactMSA.ScalarBSource.source_jet_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.ScalarBSource.source_jet_shape

/-- info: 'FMSA.ExactMSA.ScalarBSource.jet_linear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.ScalarBSource.jet_linear

/-- info: 'FMSA.ExactMSA.ScalarBSource.kappa_jet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.ScalarBSource.kappa_jet

/-- info: 'FMSA.ExactMSA.ScalarBSource.kappa_seed_residual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.ScalarBSource.kappa_seed_residual

/-- info: 'FMSA.ExactMSA.ScalarBSource.kappa_seed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.ScalarBSource.kappa_seed

/-- info: 'FMSA.ExactMSA.ScalarBSource.first_source_amplitude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.ScalarBSource.first_source_amplitude

/-- info: 'FMSA.ExactMSA.BSource.jet_const_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.BSource.jet_const_add

/-- info: 'FMSA.ExactMSA.BSource.affine_rest_jet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.BSource.affine_rest_jet

/-- info: 'FMSA.ExactMSA.BSource.actual_F_jet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.BSource.actual_F_jet

/-- info: 'FMSA.ExactMSA.BSource.actual_P_jet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.BSource.actual_P_jet

/-- info: 'FMSA.ExactMSA.BSource.jet_linear_coupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.BSource.jet_linear_coupling

/-- info: 'FMSA.ExactMSA.BSource.actual_BH_recurrence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.BSource.actual_BH_recurrence

/-- info: 'FMSA.ExactMSA.BSource.exists_actual_BH_jet_recurrence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.BSource.exists_actual_BH_jet_recurrence

/-- info: 'FMSA.ExactMSA.ScalarBSource.tailW_contact_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.ScalarBSource.tailW_contact_identity

/-- info: 'FMSA.ExactMSA.ScalarBSource.actualQ_real_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.ScalarBSource.actualQ_real_integral

/-- info: 'FMSA.ExactMSA.ScalarBSource.actualQ_at_tail_rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.ScalarBSource.actualQ_at_tail_rate

/-- info: 'FMSA.ExactMSA.ScalarBSource.actual_complex_source_cancellation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.ScalarBSource.actual_complex_source_cancellation

/-- info: 'FMSA.ExactMSA.ScalarBSource.sourceKernel_complex_laplace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.ScalarBSource.sourceKernel_complex_laplace

/-- info: 'FMSA.ExactMSA.ScalarBSource.contactSource_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.ScalarBSource.contactSource_support

/-- info: 'FMSA.ExactMSA.ScalarBSource.contactSource_complex_laplace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.ScalarBSource.contactSource_complex_laplace

/-- info: 'FMSA.ExactMSA.ScalarBSource.first_contact_source_paper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.ScalarBSource.first_contact_source_paper

/-- info: 'FMSA.ExactMSA.ScalarBSource.actual_first_fourier_zero_obstruction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.ScalarBSource.actual_first_fourier_zero_obstruction

/-- info: 'FMSA.ExactMSA.MultiTailMixture.FiniteBSource.innerQp_explicit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.MultiTailMixture.FiniteBSource.innerQp_explicit

/-- info: 'FMSA.ExactMSA.MultiTailMixture.FiniteBSource.innerA_explicit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.MultiTailMixture.FiniteBSource.innerA_explicit

/-- info: 'FMSA.ExactMSA.MultiTailMixture.FiniteBSource.innerC_explicit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.MultiTailMixture.FiniteBSource.innerC_explicit

/-- info: 'FMSA.ExactMSA.MultiTailMixture.FiniteBSource.innerW_explicit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.MultiTailMixture.FiniteBSource.innerW_explicit

/-- info: 'FMSA.ExactMSA.MultiTailMixture.FiniteBSource.polynomial_inner_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.MultiTailMixture.FiniteBSource.polynomial_inner_integral

/-- info: 'FMSA.ExactMSA.MultiTailMixture.FiniteBSource.exponential_inner_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.MultiTailMixture.FiniteBSource.exponential_inner_integral

/-- info: 'FMSA.ExactMSA.MultiTailMixture.FiniteBSource.actual_background_inner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.MultiTailMixture.FiniteBSource.actual_background_inner

/-- info: 'FMSA.ExactMSA.MultiTailMixture.FiniteBSource.backgroundW_no_knot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.MultiTailMixture.FiniteBSource.backgroundW_no_knot

/-- info: 'FMSA.ExactMSA.MultiTailMixture.FiniteBSource.actual_background_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.MultiTailMixture.FiniteBSource.actual_background_closed

/-- info: 'FMSA.ExactMSA.MultiTailMixture.FiniteBSource.actual_source_eq_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.MultiTailMixture.FiniteBSource.actual_source_eq_finite

/-- info: 'FMSA.ExactMSA.MultiTailMixture.FiniteBSource.actual_source_jet_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.MultiTailMixture.FiniteBSource.actual_source_jet_finite

/-- info: 'FMSA.ExactMSA.MultiTailMixture.FiniteBSource.actual_source_jet_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.MultiTailMixture.FiniteBSource.actual_source_jet_tail

/-- info: 'FMSA.ExactMSA.MultiTailMixture.FiniteBSource.sourceCoefficient_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.MultiTailMixture.FiniteBSource.sourceCoefficient_contDiff

/-- info: 'FMSA.ExactMSA.MultiTailMixture.FiniteBSource.source_dictionary_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.MultiTailMixture.FiniteBSource.source_dictionary_size

/-- info: 'FMSA.ExactMSA.MultiTailMixture.FiniteBSource.actual_source_jet_of_smooth_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.MultiTailMixture.FiniteBSource.actual_source_jet_of_smooth_pair

/-- info: 'FMSA.ExactMSA.MultiTailMixture.FiniteBSource.exists_actual_root_with_finite_sources' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.MultiTailMixture.FiniteBSource.exists_actual_root_with_finite_sources

/-- info: 'FMSA.ExactMSA.MultiTailMixture.FiniteBSource.actual_source_integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.MultiTailMixture.FiniteBSource.actual_source_integrable

/-- info: 'FMSA.ExactMSA.MultiTailMixture.FiniteBSource.actual_excess_source_renewal_of_integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.MultiTailMixture.FiniteBSource.actual_excess_source_renewal_of_integrable

/-- info: 'FMSA.ExactMSA.MultiTailMixture.FiniteBSource.actual_excess_source_complex_renewal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.MultiTailMixture.FiniteBSource.actual_excess_source_complex_renewal

/-- info: 'FMSA.ExactMSA.MultiTailMixture.FiniteBSource.actual_normalized_radial_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.MultiTailMixture.FiniteBSource.actual_normalized_radial_transfer

/-- info: 'FMSA.ExactMSA.MultiTailMixture.FiniteBSource.source_order_reconstruction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.MultiTailMixture.FiniteBSource.source_order_reconstruction

/-- info: 'FMSA.ExactMSA.MultiTailMixture.FiniteBSource.actual_finite_source_radial_OZ_bridge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.MultiTailMixture.FiniteBSource.actual_finite_source_radial_OZ_bridge

/-- info: 'FMSA.ExactMSA.MultiTailMixture.FiniteBSource.actual_finite_source_radial_OZ_automatic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.MultiTailMixture.FiniteBSource.actual_finite_source_radial_OZ_automatic

/-- info: 'FMSA.ExactMSA.MultiTailMixture.FiniteBSource.actual_hardcore_positive_jet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.MultiTailMixture.FiniteBSource.actual_hardcore_positive_jet

/-- info: 'FMSA.ExactMSA.MultiTailMixture.FiniteBSource.actual_ordered_DCF_exterior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.MultiTailMixture.FiniteBSource.actual_ordered_DCF_exterior

/-- info: 'FMSA.ExactMSA.MultiTailMixture.FiniteBSource.actual_exterior_DCF_jet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.MultiTailMixture.FiniteBSource.actual_exterior_DCF_jet

/-- info: 'FMSA.ExactMSA.BSource.normalized_complex_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.BSource.normalized_complex_mul

/-- info: 'FMSA.ExactMSA.BSource.normalized_matrix_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.BSource.normalized_matrix_mul

/-- info: 'FMSA.ExactMSA.BSource.normalized_renewal_line' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.BSource.normalized_renewal_line

/-- info: 'FMSA.ExactMSA.MultiTailMixture.BHJet.coeff_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.MultiTailMixture.BHJet.coeff_mul

/-- info: 'FMSA.ExactMSA.MultiTailMixture.BHJet.convolution_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.MultiTailMixture.BHJet.convolution_split

/-- info: 'FMSA.ExactMSA.MultiTailMixture.BHJet.coeff_local_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.MultiTailMixture.BHJet.coeff_local_eq

/-- info: 'FMSA.ExactMSA.MultiTailMixture.BHJet.coeff_scaled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.MultiTailMixture.BHJet.coeff_scaled

/-- info: 'FMSA.ExactMSA.MultiTailMixture.BHJet.actual_D_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.MultiTailMixture.BHJet.actual_D_order

/-- info: 'FMSA.ExactMSA.MultiTailMixture.BHJet.actual_G_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.MultiTailMixture.BHJet.actual_G_order

/-- info: 'FMSA.ExactMSA.MultiTailMixture.BHJet.jet_scaled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.MultiTailMixture.BHJet.jet_scaled

/-- info: 'FMSA.ExactMSA.MultiTailMixture.BHJet.jet_finite_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.MultiTailMixture.BHJet.jet_finite_sum

/-- info: 'FMSA.ExactMSA.MultiTailMixture.BHJet.product_zero_right_jet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.MultiTailMixture.BHJet.product_zero_right_jet

/-- info: 'FMSA.ExactMSA.MultiTailMixture.BHJet.affine_product_jet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.MultiTailMixture.BHJet.affine_product_jet

/-- info: 'FMSA.ExactMSA.MultiTailMixture.BHJet.actual_W_jet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.MultiTailMixture.BHJet.actual_W_jet

/-- info: 'FMSA.ExactMSA.MultiTailMixture.BHJet.actual_C_jet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.MultiTailMixture.BHJet.actual_C_jet

/-- info: 'FMSA.ExactMSA.MultiTailMixture.BHJet.actual_smooth_root_orders' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.MultiTailMixture.BHJet.actual_smooth_root_orders

/-- info: 'FMSA.ExactMSA.MultiTailMixture.BHJet.exists_actual_root_with_all_orders' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.MultiTailMixture.BHJet.exists_actual_root_with_all_orders

/-- info: 'FMSA.ExactMSA.MultiTailMixture.BHJet.first_order_amplitude_recovered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.ExactMSA.MultiTailMixture.BHJet.first_order_amplitude_recovered
