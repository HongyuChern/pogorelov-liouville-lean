import CHS.Analysis.HessianUpperEnvelope
import CHS.Algebra.ComplexProjection
import CHS.Algebra.DeterminantRigidity

/-!
# Constancy of the actual Hessian in complex dimension at least two

The upper envelope belongs to the closure of the actual Hessian range,
so its complex projection has determinant one.  The positive difference
has zero complex projection by strict determinant monotonicity, hence
zero real trace and is zero.  This closes the whole-space Hessian argument
without assuming any local oscillation or Evans--Krylov theorem.
-/

set_option autoImplicit false
noncomputable section

open Set Matrix
open scoped BigOperators ComplexOrder ContDiff

namespace CHS

open Calculus Analysis CHS.Algebra

variable {n : ℕ}
local notation "E" => DeGiorgi.AmbientSpace (n + n)

theorem bounded_positive_complexMongeAmpere_realBlockHessian_constant
    (hn : 2 ≤ n) {u : E → ℝ} (hu : ContDiff ℝ 4 u)
    (hdet : ∀ x, (complexHessian realDirections imagDirections u x).det = 1)
    (hA : ∀ x, (complexHessian realDirections imagDirections u x).PosDef)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, ∀ i j, |euclideanHessian u x i j| ≤ C) :
    ∀ x y, realBlockHessian realDirections imagDirections u x =
      realBlockHessian realDirections imagDirections u y := by
  obtain ⟨Q, hQ, hdom⟩ := bounded_positive_complexMongeAmpere_upper_envelope hn hu hdet hA hC hbound
  have hQdet : (complexProjection Q).det = 1 := by
    apply closure_minimal (s := range (realBlockHessian realDirections imagDirections u))
      (t := {H | (complexProjection H).det = 1}) ?_
      (isClosed_eq continuous_complexProjection.matrix_det continuous_const) hQ
    rintro _ ⟨x, rfl⟩
    rw [mem_setOf_eq, complexProjection_realBlockHessian (hu.of_le (by norm_num)).contDiffAt]
    exact hdet x
  have hEq (x : E) : Q = realBlockHessian realDirections imagDirections u x := by
    have hu2 : ContDiffAt ℝ 2 u x := (hu.of_le (by norm_num)).contDiffAt
    have hdiff := complexProjection_posSemidef (hdom x)
    rw [complexProjection_sub, complexProjection_realBlockHessian hu2] at hdiff
    have hP := eq_of_posDef_of_posSemidef_sub_of_det_eq (hA x) hdiff (hQdet.trans (hdet x).symm)
    apply sub_eq_zero.mp
    apply eq_zero_of_posSemidef_complexProjection_zero (hdom x)
    rw [complexProjection_sub, complexProjection_realBlockHessian hu2, hP, sub_self]
  exact fun x y => (hEq x).symm.trans (hEq y)

theorem bounded_positive_complexMongeAmpere_realHessian_constant
    (hn : 2 ≤ n) {u : E → ℝ} (hu : ContDiff ℝ 4 u)
    (hdet : ∀ x, (complexHessian realDirections imagDirections u x).det = 1)
    (hA : ∀ x, (complexHessian realDirections imagDirections u x).PosDef)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, ∀ i j, |euclideanHessian u x i j| ≤ C) :
    ∀ x y, realHessian u x = realHessian u y := by
  intro x y
  have hb := bounded_positive_complexMongeAmpere_realBlockHessian_constant hn hu hdet hA hC hbound x y
  have he : euclideanHessian u x = euclideanHessian u y := by
    rw [← realBlockHessian_reindex, ← realBlockHessian_reindex, hb]
  let B := (EuclideanSpace.basisFun (Fin (n + n)) ℝ).toBasis
  apply ContinuousLinearMap.coe_injective
  apply B.ext
  intro i
  apply ContinuousLinearMap.coe_injective
  apply B.ext
  intro j
  have h := congrArg (fun M => M i j) he
  simpa only [euclideanHessian, B, OrthonormalBasis.coe_toBasis,
    EuclideanSpace.basisFun_apply, ContinuousLinearMap.coe_coe] using h

theorem entire_convex_realBlockHessian_constant
    (hn : 2 ≤ n) {u : E → ℝ} (hu : ContDiff ℝ 4 u)
    (hdet : ∀ x, (complexHessian realDirections imagDirections u x).det = 1)
    (hR : ∀ x, (realBlockHessian realDirections imagDirections u x).PosSemidef) :
    ∀ x y, realBlockHessian realDirections imagDirections u x =
      realBlockHessian realDirections imagDirections u y := by
  obtain ⟨C, hC, hbound, _, _⟩ := CHS.entire_convex_hessian_bound hn hu hdet hR
  exact bounded_positive_complexMongeAmpere_realBlockHessian_constant hn hu hdet
    (fun x => complexHessian_posDef_of_realBlockHessian (hu.of_le (by norm_num)).contDiffAt
      realDirections imagDirections (hR x) (hdet x)) hC hbound

theorem entire_convex_realHessian_constant
    (hn : 2 ≤ n) {u : E → ℝ} (hu : ContDiff ℝ 4 u)
    (hdet : ∀ x, (complexHessian realDirections imagDirections u x).det = 1)
    (hR : ∀ x, (realBlockHessian realDirections imagDirections u x).PosSemidef) :
    ∀ x y, realHessian u x = realHessian u y := by
  obtain ⟨C, hC, hbound, _, _⟩ := CHS.entire_convex_hessian_bound hn hu hdet hR
  exact bounded_positive_complexMongeAmpere_realHessian_constant hn hu hdet
    (fun x => complexHessian_posDef_of_realBlockHessian (hu.of_le (by norm_num)).contDiffAt
      realDirections imagDirections (hR x) (hdet x)) hC hbound

end CHS
