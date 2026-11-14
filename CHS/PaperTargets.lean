import CHS.ChatProC02
import CHS.Analysis.ConvexityBoundaryJets
import CHS.Sections.ManuscriptGradient

/-!
# Stable public calls for the twelve frozen manuscript targets

These are proved aliases, not assumptions or replacement specifications.
The original statements and their historical acceptance flags in
data/paper_targets.json remain unchanged. Boundary Hessians in Proposition
2.4 are actual C2 closure jets, and Lemma 3.1 has both original geometric
alternatives with invariance required only on the domain.
-/

namespace CHS.Paper

alias theorem_1_1 := CHS.general_pogorelov_linf
alias theorem_1_1_positive := CHS.general_pogorelov_positive_linf
alias theorem_1_2 := CHS.convex_pogorelov_linf
alias theorem_1_3 := CHS.theorem_1_3_liouville
alias corollary_1_4 := CHS.corollary_1_4_exterior_convexity

alias lemma_2_1 := CHS.Calculus.matrix_differential_identities
alias lemma_2_2_nonnegative := CHS.Calculus.realBlockHessian_posSemidef_equivalences
alias lemma_2_2_positive := CHS.Calculus.realBlockHessian_posDef_equivalences
alias lemma_2_3_identity := CHS.Calculus.schurHessian_LM
alias lemma_2_3_nonpositive := CHS.Calculus.schurHessian_LM_nonpos
alias proposition_2_4 := CHS.Analysis.closure_realHessian_posSemidef_of_boundary
alias lemma_2_5 := CHS.Analysis.schur_and_realHessian_rank_constant
alias lemma_2_6 := CHS.tracefree_matrix_inequality
alias lemma_3_1 := CHS.Sections.normalized_section_gradient
alias proposition_3_2 := CHS.proposition_3_2_global_hessian_bound

alias local_hessian_holder := CHS.Analysis.exists_local_complexMongeAmpere_hessian_holder
alias scaled_hessian_holder := CHS.Analysis.exists_scaled_complexMongeAmpere_hessian_holder

end CHS.Paper
