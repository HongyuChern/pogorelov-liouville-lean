import CHS.Calculus.HessianExtrema
import CHS.Calculus.PotentialNegation
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Actual Hessian identities for a quadratic perturbation

The quadratic function may be the squared norm of a continuous linear
projection.  Its second derivative is computed explicitly, so strict
curvature on a quotient slice is retained in the extremum argument.
-/

set_option autoImplicit false
noncomputable section

open Filter Set
open scoped ContDiff Topology RealInnerProductSpace

namespace CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem realHessian_add {u v : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x) :
    realHessian (fun y => u y + v y) x = realHessian u x + realHessian v x := by
  have hnear : fderiv ℝ (fun y => u y + v y) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ u y + fderiv ℝ v y) := by
    filter_upwards [hu.eventually (by simp), hv.eventually (by simp)] with y hyu hyv
    exact fderiv_fun_add (hyu.differentiableAt (by norm_num))
      (hyv.differentiableAt (by norm_num))
  unfold realHessian
  rw [hnear.fderiv_eq, fderiv_fun_add
    ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
    ((hv.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))]

theorem realHessian_const_mul (c : ℝ) (u : E → ℝ) (x : E) :
    realHessian (fun y => c * u y) x = c • realHessian u x := by
  change fderiv ℝ (fderiv ℝ (c • u)) x = c • fderiv ℝ (fderiv ℝ u) x
  rw [fderiv_const_smul_field (𝕜 := ℝ) (f := u) c]
  exact congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := fderiv ℝ u) c) x

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem realHessian_norm_sq_comp (P : E →L[ℝ] F) (x v w : E) :
    realHessian (fun y => ‖P y‖ ^ 2) x v w = 2 * ⟪P v, P w⟫ := by
  let T : E →L[ℝ] (E →L[ℝ] ℝ) :=
    ((ContinuousLinearMap.compL ℝ E F ℝ).flip P).comp
      ((2 : ℝ) • (innerSL ℝ).comp P)
  have hD : fderiv ℝ (fun y => ‖P y‖ ^ 2) = T := by
    funext y
    rw [(P.hasFDerivAt.norm_sq).fderiv]
    ext v
    simp [T, two_smul]
  unfold realHessian
  rw [hD, T.fderiv]
  simp [T, two_smul]
  ring

theorem realHessian_le_neg_quadratic_of_isLocalMax
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x)
    (P : E →L[ℝ] F) (ε : ℝ)
    (hmax : IsLocalMax (fun y => u y + ε * ‖P y‖ ^ 2) x) (v : E) :
    realHessian u x v v ≤ -2 * ε * ‖P v‖ ^ 2 := by
  have hq : ContDiffAt ℝ 2 (fun y => ‖P y‖ ^ 2) x :=
    (P.contDiff.norm_sq ℝ).contDiffAt
  have h := realHessian_nonpos_of_isLocalMax
    (hu.add (contDiffAt_const.mul hq)) hmax v
  rw [realHessian_add hu (contDiffAt_const.mul hq), realHessian_const_mul] at h
  change realHessian u x v v + ε * realHessian (fun y => ‖P y‖ ^ 2) x v v ≤ 0 at h
  rw [realHessian_norm_sq_comp, real_inner_self_eq_norm_sq] at h
  linarith

end CHS.Calculus
