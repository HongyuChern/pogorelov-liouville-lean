import CHS.Calculus.PotentialConstants

/-! # Exact scalar multiplication identities for actual Wirtinger derivatives -/

set_option autoImplicit false
noncomputable section

namespace CHS.Calculus

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem dz_const_mul_fun (a b : E) (f : E → ℂ) (c : ℂ) (x : E) :
    dz a b (fun y => c * f y) x = c * dz a b f x := by
  have hD : fderiv ℝ (fun y => c * f y) x = c • fderiv ℝ f x :=
    congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := f) c) x
  simp only [dz, rd, hD, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem dz_const_mul_function (a b : E) (f : E → ℂ) (c : ℂ) :
    dz a b (fun y => c * f y) = fun x => c * dz a b f x :=
  funext fun x => dz_const_mul_fun a b f c x

theorem complexHessian_const_mul (a b : ι → E) (u : E → ℝ) (c : ℝ) (x : E) :
    complexHessian a b (fun y => c * u y) x = c • complexHessian a b u x := by
  have heq : (fun y => ((c * u y : ℝ) : ℂ)) = fun y => (c : ℂ) * (u y : ℂ) := by
    funext y
    exact Complex.ofReal_mul _ _
  ext i j
  change dz (a i) (b i) (dz (a j) (-b j) (fun y => ((c * u y : ℝ) : ℂ))) x = _
  rw [heq, dz_const_mul_function, dz_const_mul_fun]
  rfl

theorem pureHessian_const_mul (a b : ι → E) (u : E → ℝ) (c : ℝ) (x : E) :
    pureHessian a b (fun y => c * u y) x = c • pureHessian a b u x := by
  have heq : (fun y => ((c * u y : ℝ) : ℂ)) = fun y => (c : ℂ) * (u y : ℂ) := by
    funext y
    exact Complex.ofReal_mul _ _
  ext i j
  change dz (a i) (b i) (dz (a j) (b j) (fun y => ((c * u y : ℝ) : ℂ))) x = _
  rw [heq, dz_const_mul_function, dz_const_mul_fun]
  rfl

end CHS.Calculus
