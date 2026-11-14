import CHS.Calculus.BasisHessian
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Affine splitting along directions in the common real Hessian kernel

Once a fixed kernel is known, the normalized potential factors through
the orthogonal projection to its complement.
-/

set_option autoImplicit false
noncomputable section

open scoped ContDiff
namespace CHS.Analysis

open Calculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem fderiv_apply_eq_of_common_hessian_kernel
    {u : E → ℝ} (hu : ContDiff ℝ 2 u) {v : E}
    (hv : ∀ x, realHessian u x v = 0) (x y : E) :
    fderiv ℝ u x v = fderiv ℝ u y v := by
  have hD (z : E) : DifferentiableAt ℝ (fderiv ℝ u) z :=
    (hu.contDiffAt.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hF (z : E) : HasFDerivAt (fun w => fderiv ℝ u w v) (0 : E →L[ℝ] ℝ) z := by
    have h := (hD z).hasFDerivAt.clm_apply (hasFDerivAt_const v z)
    have hEq :
        (fderiv ℝ u z).comp (0 : E →L[ℝ] E) +
          (fderiv ℝ (fderiv ℝ u) z).flip v = 0 := by
      ext w
      simp only [add_apply, ContinuousLinearMap.comp_apply, zero_apply, map_zero,
        zero_add, ContinuousLinearMap.flip_apply]
      exact (realHessian_symm hu.contDiffAt w v).trans
        (congrArg (fun L : E →L[ℝ] ℝ => L w) (hv z))
    rwa [hEq] at h
  exact is_const_of_fderiv_eq_zero (fun z => (hF z).differentiableAt)
    (fun z => (hF z).fderiv) x y

theorem add_eq_of_common_hessian_kernel {u : E → ℝ} (hu : ContDiff ℝ 2 u) {v : E}
    (hv : ∀ x, realHessian u x v = 0) (x : E) :
    u (x + v) = u x + fderiv ℝ u 0 v := by
  let F (t : ℝ) := u (x + t • v)
  let G (t : ℝ) := u x + t * fderiv ℝ u 0 v
  have hF (t : ℝ) : HasDerivAt F (fderiv ℝ u 0 v) t := by
    have hline : HasDerivAt (fun t : ℝ => x + t • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add x
    have h := (hu.differentiable (by norm_num) (x + t • v)).hasFDerivAt.comp_hasDerivAt t hline
    rwa [fderiv_apply_eq_of_common_hessian_kernel hu hv (x + t • v) 0] at h
  have hG (t : ℝ) : HasDerivAt G (fderiv ℝ u 0 v) t := by
    simpa [G] using ((hasDerivAt_id t).mul_const (fderiv ℝ u 0 v)).const_add (u x)
  have heq : F = G := eq_of_fderiv_eq
    (fun t => (hF t).differentiableAt) (fun t => (hG t).differentiableAt)
    (fun t => (hF t).hasFDerivAt.fderiv.trans (hG t).hasFDerivAt.fderiv.symm)
    0 (by simp [F, G])
  simpa [F, G] using congrFun heq (1 : ℝ)

theorem splits_on_orthogonalComplement [FiniteDimensional ℝ E]
    {u : E → ℝ} (hu : ContDiff ℝ 2 u) (K : Submodule ℝ E)
    (hK : ∀ x (v : K), realHessian u x (v : E) = 0) (x : E) :
    u x = u (Kᗮ.orthogonalProjectionOnto x : E) +
      fderiv ℝ u 0 (K.orthogonalProjectionOnto x : E) := by
  have hsplit : (Kᗮ.orthogonalProjectionOnto x : E) +
      (K.orthogonalProjectionOnto x : E) = x := by
    rw [Submodule.orthogonalProjectionOnto_orthogonal]
    change x - K.starProjection x + K.starProjection x = x
    exact sub_add_cancel x _
  exact (congrArg u hsplit.symm).trans
    (add_eq_of_common_hessian_kernel hu
      (fun y => hK y (K.orthogonalProjectionOnto x)) (Kᗮ.orthogonalProjectionOnto x))

end CHS.Analysis
