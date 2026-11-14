import CHS.Calculus.BasisHessian
import CHS.Calculus.ClosureNegation

/-!
# Exact derivative identities under negation of a potential

These are identities of the actual total derivative definitions, including
points outside the open domain.  Regularity is not needed for negation.
-/

set_option autoImplicit false
noncomputable section

namespace CHS.Calculus

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem dz_neg_fun (a b : E) (f : E → ℂ) (x : E) :
    dz a b (fun y => -f y) x = -dz a b f x := by
  simp only [dz, rd, fderiv_fun_neg, neg_apply]
  ring

theorem dz_neg_function (a b : E) (f : E → ℂ) :
    dz a b (fun y => -f y) = fun x => -dz a b f x :=
  funext (dz_neg_fun a b f)

theorem realHessian_neg (u : E → ℝ) (x : E) :
    realHessian (fun y => -u y) x = -realHessian u x := by
  have hd : fderiv ℝ (fun y => -u y) = fun y => -fderiv ℝ u y :=
    funext fun _ => fderiv_fun_neg
  unfold realHessian
  rw [hd, fderiv_fun_neg]

theorem realBlockHessian_neg (a b : ι → E) (u : E → ℝ) (x : E) :
    realBlockHessian a b (fun y => -u y) x = -realBlockHessian a b u x := by
  ext i j
  simp only [realBlockHessian, realHessian_neg, neg_apply, Matrix.neg_apply]

theorem complexHessian_neg (a b : ι → E) (u : E → ℝ) (x : E) :
    complexHessian a b (fun y => -u y) x = -complexHessian a b u x := by
  have heq : (fun y => ((-u y : ℝ) : ℂ)) = fun y => -(u y : ℂ) := by
    funext y
    exact Complex.ofReal_neg _
  ext i j
  change dz (a i) (b i) (dz (a j) (-b j) (fun y => ((-u y : ℝ) : ℂ))) x = _
  rw [heq, dz_neg_function, dz_neg_fun]
  rfl

theorem pureHessian_neg (a b : ι → E) (u : E → ℝ) (x : E) :
    pureHessian a b (fun y => -u y) x = -pureHessian a b u x := by
  have heq : (fun y => ((-u y : ℝ) : ℂ)) = fun y => -(u y : ℂ) := by
    funext y
    exact Complex.ofReal_neg _
  ext i j
  change dz (a i) (b i) (dz (a j) (b j) (fun y => ((-u y : ℝ) : ℂ))) x = _
  rw [heq, dz_neg_function, dz_neg_fun]
  rfl

theorem matrix_inverse_neg_of_isUnit [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : IsUnit A.det) : (-A)⁻¹ = -A⁻¹ := by
  apply Matrix.inv_eq_left_inv
  simpa only [neg_mul_neg] using Matrix.nonsing_inv_mul A hA

theorem schurHessian_neg [Fintype ι] [DecidableEq ι]
    (a b : ι → E) (u : E → ℝ) (x : E)
    (hbar : IsUnit ((complexHessian a b u x).map star).det) :
    schurHessian a b (fun y => -u y) x = -schurHessian a b u x := by
  have hmap (M : Matrix ι ι ℂ) : (-M).map star = -M.map star := by
    ext i j
    simp only [Matrix.map_apply, Matrix.neg_apply, star_neg]
  simp only [schurHessian, schurField, complexHessian_neg, pureHessian_neg,
    hmap, matrix_inverse_neg_of_isUnit hbar, neg_mul_neg, Matrix.mul_neg, neg_sub_neg]
  abel

end CHS.Calculus
