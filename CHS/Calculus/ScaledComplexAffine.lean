import CHS.Calculus.ComplexAffineEquiv
import CHS.Calculus.PotentialScalars

/-!
# The unnormalized quadratic under section coordinates

The factor `h` in the Hessian of `q(a + sqrt h G w)` is retained.
The associated real change of coordinates is an actual continuous
linear equivalence in the fixed block coordinate convention.
-/

set_option autoImplicit false
noncomputable section

open scoped ContDiff

namespace CHS.Calculus

open CHS.Analysis

variable {n : ℕ}
local notation "E₀" => DeGiorgi.AmbientSpace (n + n)

def scaledComplexRealEquiv
    (G : Matrix (Fin n) (Fin n) ℂ) (hG : IsUnit G.det) {h : ℝ} (hh : 0 < h) :
    E₀ ≃L[ℝ] E₀ :=
  (complexMatrixRealEquiv G hG).trans
    (LinearEquiv.smulOfNeZero ℝ E₀ (Real.sqrt h)
      (Real.sqrt_ne_zero'.mpr hh)).toContinuousLinearEquiv

theorem scaledComplexRealEquiv_apply
    (G : Matrix (Fin n) (Fin n) ℂ) (hG : IsUnit G.det) {h : ℝ} (hh : 0 < h) (x : E₀) :
    scaledComplexRealEquiv G hG hh x = Real.sqrt h • complexMatrixRealMap G x := rfl

theorem complexHessian_scaled_complex_affine
    (G : Matrix (Fin n) (Fin n) ℂ) (c : E₀) {h : ℝ} (hh : 0 < h)
    {q : E₀ → ℝ} {x : E₀}
    (hq : ContDiffAt ℝ 2 q (c + Real.sqrt h • complexMatrixRealMap G x)) :
    complexHessian realDirections imagDirections
        (fun y => q (c + Real.sqrt h • complexMatrixRealMap G y)) x =
      h • (G.transpose * complexHessian realDirections imagDirections q
        (c + Real.sqrt h • complexMatrixRealMap G x) * G.map star) := by
  have heq := complexHessian_normalized_complex_affine G c hh hq
  change complexHessian realDirections imagDirections
    (fun y => h⁻¹ * q (c + Real.sqrt h • complexMatrixRealMap G y) + -1) x = _ at heq
  rw [complexHessian_add_const, complexHessian_const_mul] at heq
  calc
    _ = h • (h⁻¹ • complexHessian realDirections imagDirections
        (fun y => q (c + Real.sqrt h • complexMatrixRealMap G y)) x) := by
      rw [smul_smul, mul_inv_cancel₀ hh.ne', one_smul]
    _ = _ := congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => h • A) heq

end CHS.Calculus
