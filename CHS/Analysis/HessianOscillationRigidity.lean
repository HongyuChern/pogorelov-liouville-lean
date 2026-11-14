import CHS.Analysis.HessianHolderScaled
import CHS.Sections.GlobalHessian

/-!
# The radius-to-infinity argument for the actual Hessian

The general local Holder estimate is proved upstream from directional
supersolutions and weak Harnack.  Its constants are independent of R.
Letting R tend to infinity gives constancy, with no oscillation, regularity
or Evans--Krylov theorem added as a hypothesis.
-/

set_option autoImplicit false
noncomputable section

open Set Metric Filter Matrix
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise Topology

namespace CHS

open CHS.Calculus CHS.Analysis

variable {n : ℕ}
local notation "E" => DeGiorgi.AmbientSpace (n + n)

theorem bounded_positive_complexMongeAmpere_realBlockHessian_constant_of_oscillation
    (hn : 2 ≤ n) {u : E → ℝ} (hu : ContDiff ℝ 4 u)
    (hdet : ∀ x, (complexHessian realDirections imagDirections u x).det = 1)
    (hA : ∀ x, (complexHessian realDirections imagDirections u x).PosDef)
    {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ x, ∀ i j, |euclideanHessian u x i j| ≤ M) :
    ∀ x y, realBlockHessian realDirections imagDirections u x =
      realBlockHessian realDirections imagDirections u y := by
  obtain ⟨α, C, hα, _, _, hlocal⟩ := exists_scaled_complexMongeAmpere_hessian_holder hn hM
  intro x y
  have hlim₀ : Tendsto (fun R : ℝ => ‖x - y‖ / R) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hlim : Tendsto (fun R : ℝ => C * (‖x - y‖ / R) ^ α) atTop (𝓝 0) := by
    simpa only [mul_zero] using (hlim₀.rpow_const_nhds_zero hα).const_mul C
  have hle : ‖realBlockHessian realDirections imagDirections u x -
      realBlockHessian realDirections imagDirections u y‖ ≤ 0 := by
    apply ge_of_tendsto hlim
    filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_gt_atTop ‖x‖,
      eventually_gt_atTop ‖y‖] with R hR hx hy
    exact hlocal 0 R hR u hu.contDiffOn (fun z _ => hdet z)
      (fun z _ => hA z) (fun z _ => hbound z)
      x (by simpa only [mem_ball, dist_zero_right] using hx)
      y (by simpa only [mem_ball, dist_zero_right] using hy)
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hle (norm_nonneg _)))

theorem bounded_positive_complexMongeAmpere_realHessian_constant_of_oscillation
    (hn : 2 ≤ n) {u : E → ℝ} (hu : ContDiff ℝ 4 u)
    (hdet : ∀ x, (complexHessian realDirections imagDirections u x).det = 1)
    (hA : ∀ x, (complexHessian realDirections imagDirections u x).PosDef)
    {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ x, ∀ i j, |euclideanHessian u x i j| ≤ M) :
    ∀ x y, realHessian u x = realHessian u y := by
  intro x y
  have hb := bounded_positive_complexMongeAmpere_realBlockHessian_constant_of_oscillation
    hn hu hdet hA hM hbound x y
  have he : euclideanHessian u x = euclideanHessian u y := by
    rw [← realBlockHessian_reindex, ← realBlockHessian_reindex, hb]
  let B := (EuclideanSpace.basisFun (Fin (n + n)) ℝ).toBasis
  apply ContinuousLinearMap.coe_injective
  apply B.ext
  intro i
  apply ContinuousLinearMap.coe_injective
  apply B.ext
  intro j
  have h := congrArg (fun A => A i j) he
  simpa only [euclideanHessian, B, OrthonormalBasis.coe_toBasis,
    EuclideanSpace.basisFun_apply, ContinuousLinearMap.coe_coe] using h

theorem entire_convex_realHessian_constant_of_oscillation
    (hn : 2 ≤ n) {u : E → ℝ} (hu : ContDiff ℝ 4 u)
    (hdet : ∀ x, (complexHessian realDirections imagDirections u x).det = 1)
    (hR : ∀ x, (realBlockHessian realDirections imagDirections u x).PosSemidef) :
    ∀ x y, realHessian u x = realHessian u y := by
  obtain ⟨M, hM, hbound, _, _⟩ := entire_convex_hessian_bound hn hu hdet hR
  exact bounded_positive_complexMongeAmpere_realHessian_constant_of_oscillation hn hu hdet
    (fun x => complexHessian_posDef_of_realBlockHessian (hu.of_le (by norm_num)).contDiffAt
      realDirections imagDirections (hR x) (hdet x)) hM hbound

end CHS
