import CHS.Calculus.BasisHessian

/-! # Quadratic form of the actual real block Hessian -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators ContDiff

namespace CHS.Calculus

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

theorem realHessian_sum_directions_quadratic {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (a b : ι → E) (z : ι ⊕ ι → ℝ) :
    realHessian u x (∑ i, z i • Sum.elim a b i) (∑ i, z i • Sum.elim a b i) =
      z ⬝ᵥ (realBlockHessian a b u x).mulVec z := by
  simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, dotProduct,
    Matrix.mulVec, Finset.mul_sum, realBlockHessian]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [realHessian_symm hu (Sum.elim a b j) (Sum.elim a b i)]
  ring

theorem realBlockHessian_posSemidef_of_quadratic_nonneg {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (a b : ι → E)
    (hQ : ∀ v : E, 0 ≤ realHessian u x v v) :
    (realBlockHessian a b u x).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (realBlockHessian_isHermitian hu a b)
  intro z
  rw [star_trivial, ← realHessian_sum_directions_quadratic hu a b z]
  exact hQ _

end CHS.Calculus
