import CHS.Calculus.MatrixRegularity

-- S006 audit INPUT, not a saved audit RESULT.
set_option pp.universes true
set_option pp.explicit true

#check @CHS.Calculus.determinantPolynomial
#print axioms CHS.Calculus.determinantPolynomial

#check @CHS.Calculus.determinantPolynomial_apply
#print axioms CHS.Calculus.determinantPolynomial_apply

#check @CHS.Calculus.complex_det_contDiff
#print axioms CHS.Calculus.complex_det_contDiff

#check @CHS.Calculus.field_det_contDiffAt
#print axioms CHS.Calculus.field_det_contDiffAt

#check @CHS.Calculus.field_adjugate_contDiffAt
#print axioms CHS.Calculus.field_adjugate_contDiffAt

#check @CHS.Calculus.field_inverse_contDiffAt_of_det_one
#print axioms CHS.Calculus.field_inverse_contDiffAt_of_det_one

#check @CHS.Calculus.matrix_product_contDiffAt
#print axioms CHS.Calculus.matrix_product_contDiffAt

#check @CHS.Calculus.field_det_differentiableAt
#print axioms CHS.Calculus.field_det_differentiableAt

#check @CHS.Calculus.field_adjugate_differentiableAt
#print axioms CHS.Calculus.field_adjugate_differentiableAt

#check @CHS.Calculus.inverse_matrix_differentiableAt_of_det_one
#print axioms CHS.Calculus.inverse_matrix_differentiableAt_of_det_one
