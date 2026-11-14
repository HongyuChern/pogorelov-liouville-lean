import CHS.Calculus.AffinePullback
import CHS.Analysis.BlockCoordinates

/-! # Exact R^-2 scaling of actual real and complex Hessians -/

set_option autoImplicit false
noncomputable section

open Set
open scoped ContDiff

namespace CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def euclideanRescalePotential (u : E → ℝ) (x₀ : E) (R : ℝ) (x : E) : ℝ :=
  (R * R)⁻¹ * u (x₀ + R • x)

theorem euclideanRescalePotential_contDiffOn {k : ℕ∞ω}
    {u : E → ℝ} {U V : Set E} (hu : ContDiffOn ℝ k u U) (x₀ : E) (R : ℝ)
    (hmap : MapsTo (fun x : E => x₀ + R • x) V U) :
    ContDiffOn ℝ k (euclideanRescalePotential u x₀ R) V := by
  apply contDiffOn_const.mul
  exact hu.comp (show ContDiffOn ℝ k (fun x : E => x₀ + R • x) V from by fun_prop) hmap

theorem realHessian_euclideanRescalePotential {u : E → ℝ} {x₀ x : E} {R : ℝ}
    (hR : R ≠ 0) (hu : ContDiffAt ℝ 2 u (x₀ + R • x)) :
    realHessian (euclideanRescalePotential u x₀ R) x = realHessian u (x₀ + R • x) := by
  ext v w
  have ha : realHessian (fun y => u (x₀ + R • y)) x v w =
      realHessian u (x₀ + R • x) (R • v) (R • w) := by
    simpa only [smul_apply, ContinuousLinearMap.id_apply] using
      realHessian_comp_affine (R • ContinuousLinearMap.id ℝ E) x₀ hu v w
  change realHessian (fun y => (R * R)⁻¹ * u (x₀ + R • y)) x v w = _
  rw [realHessian_const_mul]
  simp only [smul_apply, smul_eq_mul, ha, map_smul]
  field_simp

theorem complexHessian_euclideanRescalePotential {ι : Type*} (a b : ι → E)
    {u : E → ℝ} {x₀ x : E} {R : ℝ}
    (hR : R ≠ 0) (hu : ContDiffAt ℝ 2 u (x₀ + R • x)) :
    complexHessian a b (euclideanRescalePotential u x₀ R) x =
      complexHessian a b u (x₀ + R • x) := by
  have hv : ContDiffAt ℝ 2 (euclideanRescalePotential u x₀ R) x :=
    contDiffAt_const.mul (hu.comp x (by fun_prop))
  ext i j
  rw [complexHessian_real_entry hv, complexHessian_real_entry hu,
    realHessian_euclideanRescalePotential hR hu]

end CHS.Calculus
