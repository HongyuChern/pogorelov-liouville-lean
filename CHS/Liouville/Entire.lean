import CHS.Analysis.HessianRigidity
import CHS.Analysis.HessianOscillationRigidity
import CHS.Calculus.QuadraticRigidity
import CHS.Calculus.DimensionOneLift

/-!
# Theorem 1.3: real quadraticity in every positive complex dimension

For n>=2 the proof uses Proposition 3.2, the proved local Hessian Holder
estimate, and its radius-to-infinity limit.  The dimension-one case is lifted to dimension
two by u(z1)+|z2|² and restricted back.  The conclusion gives every
coefficient through the actual value, derivative, and Hessian at zero.
-/

set_option autoImplicit false
noncomputable section

open scoped ContDiff ComplexOrder

namespace CHS

open CHS.Calculus CHS.Analysis

theorem entire_convex_realHessian_constant_one
    {u : DeGiorgi.AmbientSpace 2 → ℝ} (hu : ContDiff ℝ 4 u)
    (hdet : ∀ x, (complexHessian (realDirections (n := 1)) imagDirections u x).det = 1)
    (hR : ∀ x, (realBlockHessian (realDirections (n := 1)) imagDirections u x).PosSemidef) :
    ∀ x y, realHessian u x = realHessian u y := by
  let v := dimensionOneExtension u
  have hv : ContDiff ℝ 4 v := dimensionOneExtension_contDiff hu
  have hu2 : ContDiff ℝ 2 u := hu.of_le (by norm_num)
  have hvdet : ∀ x, (complexHessian (realDirections (n := 2)) imagDirections v x).det = 1 := by
    intro x
    rw [dimensionOneExtension_complexHessian hu2 hdet, Matrix.det_one]
  have hvR := dimensionOneExtension_real_convex hu2 hR
  have hconst := entire_convex_realHessian_constant_of_oscillation (n := 2) (by norm_num) hv hvdet hvR
  have heq : (fun x => v (firstComplexInclusion x)) = u :=
    funext (dimensionOneExtension_restrict u)
  have hp (x a b : DeGiorgi.AmbientSpace 2) :
      realHessian u x a b = realHessian v (firstComplexInclusion x)
        (firstComplexInclusion a) (firstComplexInclusion b) := by
    have h := realHessian_comp_affine firstComplexInclusion 0 (x := x)
      (hv.of_le (by norm_num)).contDiffAt a b
    simpa only [zero_add, heq] using h
  intro x y
  ext a b
  rw [hp, hp, hconst (firstComplexInclusion x) (firstComplexInclusion y)]

theorem entire_convex_quadratic
    {n : ℕ} (hn : 1 ≤ n) {u : DeGiorgi.AmbientSpace (n + n) → ℝ}
    (hu : ContDiff ℝ 4 u)
    (hdet : ∀ x, (complexHessian realDirections imagDirections u x).det = 1)
    (hR : ∀ x, (realBlockHessian realDirections imagDirections u x).PosSemidef) :
    ∀ x, u x = u 0 + fderiv ℝ u 0 x + (1 / 2 : ℝ) * realHessian u 0 x x := by
  have hH : ∀ x y, realHessian u x = realHessian u y := by
    rcases eq_or_lt_of_le hn with h1 | h2
    · subst n
      exact entire_convex_realHessian_constant_one hu hdet hR
    · exact entire_convex_realHessian_constant_of_oscillation (by omega) hu hdet hR
  exact eq_quadratic_of_realHessian_constant (hu.of_le (by norm_num)) (fun x => hH x 0)

/-- The frozen manuscript's smooth Theorem 1.3, including n=1. -/
theorem theorem_1_3_liouville
    {n : ℕ} (hn : 1 ≤ n) {u : DeGiorgi.AmbientSpace (n + n) → ℝ}
    (hu : ContDiff ℝ ∞ u)
    (hdet : ∀ x, (complexHessian realDirections imagDirections u x).det = 1)
    (hR : ∀ x, (realBlockHessian realDirections imagDirections u x).PosSemidef) :
    ∀ x, u x = u 0 + fderiv ℝ u 0 x + (1 / 2 : ℝ) * realHessian u 0 x x :=
  entire_convex_quadratic hn
    (hu.of_le (WithTop.coe_le_coe.mpr (le_top : (4 : ℕ∞) ≤ ⊤))) hdet hR

end CHS
