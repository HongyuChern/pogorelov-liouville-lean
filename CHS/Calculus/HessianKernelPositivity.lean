import CHS.Calculus.AffinePullback
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Algebra.QuadraticDiscriminant

/-! # Strict positivity on the orthogonal complement of the actual Hessian kernel -/

set_option autoImplicit false
noncomputable section

open Set
open scoped ContDiff

namespace CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem realHessian_apply_eq_zero_of_quadratic_eq_zero
    {u : E → ℝ} {x v : E} (hu : ContDiffAt ℝ 2 u x)
    (hQ : ∀ z : E, 0 ≤ realHessian u x z z) (hv : realHessian u x v v = 0) :
    realHessian u x v = 0 := by
  ext w
  have hdisc : discrim (realHessian u x w w) (2 * realHessian u x v w) 0 ≤ 0 := by
    apply discrim_le_zero
    intro t
    have h := hQ (v + t • w)
    simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul] at h
    rw [hv, realHessian_symm hu w v] at h
    nlinarith
  unfold discrim at hdisc
  have hs := sq_nonneg (realHessian u x v w)
  change realHessian u x v w = 0
  nlinarith

end CHS.Calculus

namespace CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

theorem realHessian_pos_on_orthogonal_kernel
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x)
    (hQ : ∀ z : E, 0 ≤ realHessian u x z z)
    (K : Submodule ℝ E) (hker : (realHessian u x).ker = K)
    (v : Kᗮ) (hv : v ≠ 0) : 0 < realHessian u x (v : E) (v : E) := by
  by_contra! hn
  have hz := realHessian_apply_eq_zero_of_quadratic_eq_zero hu hQ (le_antisymm hn (hQ v))
  have hK : (v : E) ∈ K := hker ▸ hz
  have hbot : (v : E) ∈ (⊥ : Submodule ℝ E) := by
    rw [← K.inf_orthogonal_eq_bot]
    exact ⟨hK, v.property⟩
  exact hv (Subtype.ext ((Submodule.mem_bot ℝ).mp hbot))

theorem restricted_realHessian_pos_of_fixed_kernel
    {u : E → ℝ} (hu : ContDiff ℝ 2 u)
    (hQ : ∀ x z : E, 0 ≤ realHessian u x z z)
    (K : Submodule ℝ E) (hker : ∀ x, (realHessian u x).ker = K) :
    ∀ x v : Kᗮ, v ≠ 0 → 0 < realHessian (fun y : Kᗮ => u y) x v v := by
  intro x v hv
  have hH : realHessian (fun y : Kᗮ => u y) x v v =
      realHessian u (x : E) (v : E) (v : E) := by
    simpa only [zero_add, Submodule.subtypeL_apply] using
      realHessian_comp_affine Kᗮ.subtypeL (0 : E) hu.contDiffAt v v
  rw [hH]
  exact realHessian_pos_on_orthogonal_kernel hu.contDiffAt (hQ x) K (hker x) v hv

end CHS.Calculus
