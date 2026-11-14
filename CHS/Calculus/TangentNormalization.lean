import CHS.Calculus.PotentialConstants

/-! # Subtracting the actual tangent affine function at the origin -/

set_option autoImplicit false
noncomputable section

open scoped ContDiff

namespace CHS.Calculus

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def tangentNormalized (u : E → ℝ) (x : E) : ℝ :=
  u x - u 0 - fderiv ℝ u 0 x

theorem tangentNormalized_zero (u : E → ℝ) : tangentNormalized u 0 = 0 := by
  simp only [tangentNormalized, sub_self, map_zero]

theorem contDiff_tangentNormalized {k : ℕ∞ω} {u : E → ℝ} (hu : ContDiff ℝ k u) :
    ContDiff ℝ k (tangentNormalized u) :=
  (hu.sub contDiff_const).sub (fderiv ℝ u 0).contDiff

theorem fderiv_tangentNormalized {u : E → ℝ} (hu : Differentiable ℝ u) (x : E) :
    fderiv ℝ (tangentNormalized u) x = fderiv ℝ u x - fderiv ℝ u 0 := by
  unfold tangentNormalized
  simpa only [Pi.sub_apply, fderiv_sub_const, ContinuousLinearMap.fderiv] using
    fderiv_fun_sub ((hu x).sub_const (u 0)) (fderiv ℝ u 0).differentiableAt

theorem fderiv_tangentNormalized_zero {u : E → ℝ} (hu : Differentiable ℝ u) :
    fderiv ℝ (tangentNormalized u) 0 = 0 := by
  rw [fderiv_tangentNormalized hu, sub_self]

theorem realHessian_tangentNormalized {u : E → ℝ} (hu : Differentiable ℝ u) (x : E) :
    realHessian (tangentNormalized u) x = realHessian u x := by
  have hD : fderiv ℝ (tangentNormalized u) = fun y => fderiv ℝ u y - fderiv ℝ u 0 :=
    funext (fderiv_tangentNormalized hu)
  unfold realHessian
  rw [hD, fderiv_sub_const]

theorem realBlockHessian_tangentNormalized {u : E → ℝ} (hu : Differentiable ℝ u)
    (a b : ι → E) (x : E) :
    realBlockHessian a b (tangentNormalized u) x = realBlockHessian a b u x := by
  ext i j
  simp only [realBlockHessian, realHessian_tangentNormalized hu]

theorem complexHessian_tangentNormalized {u : E → ℝ} (hu : ContDiff ℝ 2 u)
    (a b : ι → E) (x : E) :
    complexHessian a b (tangentNormalized u) x = complexHessian a b u x := by
  ext i j
  rw [complexHessian_real_entry (contDiff_tangentNormalized hu).contDiffAt,
    complexHessian_real_entry hu.contDiffAt]
  simp only [realHessian_tangentNormalized (hu.differentiable (by norm_num))]

theorem pureHessian_tangentNormalized {u : E → ℝ} (hu : ContDiff ℝ 2 u)
    (a b : ι → E) (x : E) :
    pureHessian a b (tangentNormalized u) x = pureHessian a b u x := by
  ext i j
  rw [pureHessian_real_entry (contDiff_tangentNormalized hu).contDiffAt,
    pureHessian_real_entry hu.contDiffAt]
  simp only [realHessian_tangentNormalized (hu.differentiable (by norm_num))]

end CHS.Calculus
