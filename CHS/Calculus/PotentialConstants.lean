import CHS.Calculus.PotentialNegation
import CHS.Pogorelov.GradientNorm

/-! # Actual derivatives are unchanged by addition of a real constant -/

set_option autoImplicit false
noncomputable section

namespace CHS.Calculus

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem dz_add_const_fun (a b : E) (f : E → ℂ) (c : ℂ) (x : E) :
    dz a b (fun y => f y + c) x = dz a b f x := by
  simp only [dz, rd, fderiv_add_const]

theorem dz_add_const_function (a b : E) (f : E → ℂ) (c : ℂ) :
    dz a b (fun y => f y + c) = dz a b f :=
  funext fun x => dz_add_const_fun a b f c x

theorem realHessian_add_const (u : E → ℝ) (c : ℝ) (x : E) :
    realHessian (fun y => u y + c) x = realHessian u x := by
  have hD : fderiv ℝ (fun y => u y + c) = fderiv ℝ u :=
    funext fun _ => fderiv_add_const c
  unfold realHessian
  rw [hD]

theorem realBlockHessian_add_const (a b : ι → E) (u : E → ℝ) (c : ℝ) (x : E) :
    realBlockHessian a b (fun y => u y + c) x = realBlockHessian a b u x := by
  ext i j
  simp only [realBlockHessian, realHessian_add_const]

theorem complexHessian_add_const (a b : ι → E) (u : E → ℝ) (c : ℝ) (x : E) :
    complexHessian a b (fun y => u y + c) x = complexHessian a b u x := by
  have heq : (fun y => ((u y + c : ℝ) : ℂ)) = fun y => (u y : ℂ) + (c : ℂ) := by
    funext y
    exact Complex.ofReal_add _ _
  ext i j
  change dz (a i) (b i) (dz (a j) (-b j) (fun y => ((u y + c : ℝ) : ℂ))) x = _
  rw [heq, dz_add_const_function]
  rfl

theorem pureHessian_add_const (a b : ι → E) (u : E → ℝ) (c : ℝ) (x : E) :
    pureHessian a b (fun y => u y + c) x = pureHessian a b u x := by
  have heq : (fun y => ((u y + c : ℝ) : ℂ)) = fun y => (u y : ℂ) + (c : ℂ) := by
    funext y
    exact Complex.ofReal_add _ _
  ext i j
  change dz (a i) (b i) (dz (a j) (b j) (fun y => ((u y + c : ℝ) : ℂ))) x = _
  rw [heq, dz_add_const_function]
  rfl

end CHS.Calculus

namespace CHS.Pogorelov

open CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

theorem gradientNormSq_add_const (a b : Fin n → E) (u : E → ℝ) (c : ℝ) (x : E) :
    gradientNormSq a b (fun y => u y + c) x = gradientNormSq a b u x := by
  have heq : (fun y => ((u y + c : ℝ) : ℂ)) = fun y => (u y : ℂ) + (c : ℂ) := by
    funext y
    exact Complex.ofReal_add _ _
  simp only [gradientNormSq, heq, dz_add_const_fun]

end CHS.Pogorelov
