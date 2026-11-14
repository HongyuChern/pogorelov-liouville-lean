import CHS.CoreImports
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# A positive trace direction increases the actual determinant

The proof uses the exact polynomial expansion of the determinant at the
identity.  It applies to actual continuous linear endomorphisms and gives
an arbitrarily small positive parameter, without an assumed variation
formula or a contact-point certificate.
-/

set_option autoImplicit false
noncomputable section

open Set Filter
open scoped Topology Matrix.Norms.Elementwise

namespace CHS.Sections

theorem exists_small_matrix_det_increase
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (htr : 0 < A.trace) {δ : ℝ} (hδ : 0 < δ) :
    ∃ t : ℝ, 0 < t ∧ t < δ ∧ 1 < (1 + t • A).det := by
  let p : Polynomial ℝ :=
    (Matrix.det (1 + (Polynomial.X : Polynomial ℝ) • A.map Polynomial.C)).divX.divX
  have hc : Continuous (fun t : ℝ => t * p.eval t) := continuous_id.mul p.continuous
  have hn : {t : ℝ | -A.trace < t * p.eval t} ∈ 𝓝 (0 : ℝ) :=
    hc.continuousAt.preimage_mem_nhds (Ioi_mem_nhds (by simpa using htr))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hn
  let t : ℝ := min r δ / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have htradius : t < r := by dsimp [t]; linarith [min_le_left r δ]
  have htδ : t < δ := by dsimp [t]; linarith [min_le_right r δ]
  have hsmall : -A.trace < t * p.eval t := hball (by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht]
    exact htradius)
  refine ⟨t, ht, htδ, ?_⟩
  rw [Matrix.det_one_add_smul]
  change 1 < 1 + A.trace * t + p.eval t * t ^ 2
  have hp := mul_pos ht (show 0 < A.trace + t * p.eval t by linarith)
  nlinarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E]

theorem exists_small_linear_det_increase
    (A : E →L[ℝ] E) (htr : 0 < LinearMap.trace ℝ E A.toLinearMap)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ t : ℝ, 0 < t ∧ t < δ ∧ 1 < (ContinuousLinearMap.id ℝ E + t • A).det := by
  let b := Module.finBasis ℝ E
  let M := LinearMap.toMatrix b b A.toLinearMap
  have hM : 0 < M.trace := by
    rwa [LinearMap.trace_eq_matrix_trace ℝ b] at htr
  obtain ⟨t, ht, htδ, hdet⟩ := exists_small_matrix_det_increase M hM hδ
  refine ⟨t, ht, htδ, ?_⟩
  change 1 < LinearMap.det ((ContinuousLinearMap.id ℝ E + t • A).toLinearMap)
  rw [← LinearMap.det_toMatrix b]
  simpa only [ContinuousLinearMap.toLinearMap_add, ContinuousLinearMap.toLinearMap_smul,
    ContinuousLinearMap.coe_id, map_add, map_smul, LinearMap.toMatrix_id] using hdet

end CHS.Sections
