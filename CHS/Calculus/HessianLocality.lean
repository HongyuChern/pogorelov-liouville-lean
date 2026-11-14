import CHS.Analysis.BlockCoordinates

/-! # Locality of the actual Frechet and complex Hessians -/

set_option autoImplicit false
noncomputable section

open Filter
open scoped Topology ContDiff

namespace CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem realHessian_eq_of_eventuallyEq {u v : E → ℝ} {x : E}
    (h : u =ᶠ[𝓝 x] v) : realHessian u x = realHessian v x :=
  h.fderiv.fderiv_eq

theorem realBlockHessian_eq_of_eventuallyEq {ι : Type*} (a b : ι → E)
    {u v : E → ℝ} {x : E} (h : u =ᶠ[𝓝 x] v) :
    realBlockHessian a b u x = realBlockHessian a b v x := by
  ext i j
  exact congrArg (fun D => D (Sum.elim a b i) (Sum.elim a b j)) (realHessian_eq_of_eventuallyEq h)

theorem complexHessian_eq_of_eventuallyEq {ι : Type*} (a b : ι → E)
    {u v : E → ℝ} {x : E} (h : u =ᶠ[𝓝 x] v)
    (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x) :
    complexHessian a b u x = complexHessian a b v x := by
  ext i j
  rw [complexHessian_real_entry hu, complexHessian_real_entry hv,
    realHessian_eq_of_eventuallyEq h]

end CHS.Calculus
