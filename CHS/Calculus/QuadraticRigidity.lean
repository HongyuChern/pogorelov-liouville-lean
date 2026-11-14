import CHS.Calculus.FiniteWirtinger
import Mathlib.Analysis.Calculus.MeanValue

/-! # Exact integration of a constant actual real Hessian -/

set_option autoImplicit false
noncomputable section

open scoped ContDiff

namespace CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem eq_quadratic_of_realHessian_constant
    {u : E → ℝ} (hu : ContDiff ℝ 2 u)
    (hH : ∀ x, realHessian u x = realHessian u 0) :
    ∀ x, u x = u 0 + fderiv ℝ u 0 x + (1 / 2 : ℝ) * realHessian u 0 x x := by
  let H := realHessian u 0
  let D := fderiv ℝ u 0
  have hDdiff : Differentiable ℝ (fderiv ℝ u) :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hgrad : fderiv ℝ u = fun x => D + H x := by
    apply eq_of_fderiv_eq hDdiff
      (fun x => (H.hasFDerivAt.const_add D).differentiableAt)
      (fun x => (hH x).trans (H.hasFDerivAt.const_add D).fderiv.symm) 0
    simp only [map_zero, add_zero, D]
  let q : E → ℝ := fun x => u 0 + D x + (1 / 2 : ℝ) * H x x
  have hq (x : E) : HasFDerivAt q (D + H x) x := by
    have hdiag := (H.hasFDerivAt.clm_apply (hasFDerivAt_id x)).const_mul (1 / 2 : ℝ)
    have h := ((hasFDerivAt_const (u 0) x).add D.hasFDerivAt).add hdiag
    apply h.congr_fderiv
    ext v
    simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.flip_apply,
      zero_apply, zero_add, smul_eq_mul, id_eq]
    have hs : H v x = H x v := realHessian_symm hu.contDiffAt v x
    rw [hs]
    ring
  have heq : u = q := eq_of_fderiv_eq (hu.differentiable (by norm_num))
    (fun x => (hq x).differentiableAt)
    (fun x => (congrFun hgrad x).trans (hq x).fderiv.symm) 0 (by simp [q])
  exact fun x => congrFun heq x

end CHS.Calculus
