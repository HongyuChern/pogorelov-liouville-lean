import CHS.Calculus.NativeCMAContractions

-- S006 audit INPUT, not a saved audit RESULT.
set_option pp.universes true
set_option pp.explicit true

#check @CHS.Calculus.contract_apply_eq
#print axioms CHS.Calculus.contract_apply_eq

#check @CHS.Calculus.contract_sandwich_apply
#print axioms CHS.Calculus.contract_sandwich_apply

#check @CHS.Calculus.contract_sandwich_swapped_apply
#print axioms CHS.Calculus.contract_sandwich_swapped_apply

#check @CHS.Calculus.native_cma_first_variation
#print axioms CHS.Calculus.native_cma_first_variation

#check @CHS.Calculus.complexHessianIn_linearized_trace
#print axioms CHS.Calculus.complexHessianIn_linearized_trace

#check @CHS.Calculus.pureHessianIn_linearized_trace
#print axioms CHS.Calculus.pureHessianIn_linearized_trace

#check @CHS.Calculus.complexHessianIn_LA_first
#print axioms CHS.Calculus.complexHessianIn_LA_first

#check @CHS.Calculus.pureHessianIn_LB_first
#print axioms CHS.Calculus.pureHessianIn_LB_first

#check @CHS.Calculus.complexHessianIn_LA_second
#print axioms CHS.Calculus.complexHessianIn_LA_second

#check @CHS.Calculus.pureHessianIn_LB_second
#print axioms CHS.Calculus.pureHessianIn_LB_second

#check @CHS.Calculus.native_cma_LA_first
#print axioms CHS.Calculus.native_cma_LA_first
