import CHS.Calculus.NativeInverseDivergence

-- S006 audit INPUT, not a saved audit RESULT.
set_option pp.universes true
set_option pp.explicit true

#check @CHS.Calculus.contract_transpose_swap
#print axioms CHS.Calculus.contract_transpose_swap

#check @CHS.Calculus.contract_inverse_transpose_swap
#print axioms CHS.Calculus.contract_inverse_transpose_swap

#check @CHS.Calculus.matrixDZ_congr_on
#print axioms CHS.Calculus.matrixDZ_congr_on

#check @CHS.Calculus.matrixDZ_two_congr_on
#print axioms CHS.Calculus.matrixDZ_two_congr_on

#check @CHS.Calculus.complexHessianIn_flip_eq_transpose
#print axioms CHS.Calculus.complexHessianIn_flip_eq_transpose

#check @CHS.Calculus.complexHessianIn_LH_first
#print axioms CHS.Calculus.complexHessianIn_LH_first

#check @CHS.Calculus.antiHessianIn_LC_first
#print axioms CHS.Calculus.antiHessianIn_LC_first

#check @CHS.Calculus.inverseDerivativeField_divergence_of_linearized
#print axioms CHS.Calculus.inverseDerivativeField_divergence_of_linearized

#check @CHS.Calculus.native_inverse_conjugate_mixed_divergence
#print axioms CHS.Calculus.native_inverse_conjugate_mixed_divergence

#check @CHS.Calculus.native_inverse_conjugate_pure_divergence
#print axioms CHS.Calculus.native_inverse_conjugate_pure_divergence

#check @CHS.Calculus.native_schur_LM_identity
#print axioms CHS.Calculus.native_schur_LM_identity
