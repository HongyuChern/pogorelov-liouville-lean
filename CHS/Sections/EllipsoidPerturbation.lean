import CHS.Sections.EllipsoidDetVariation
import CHS.Sections.MaximalAffineEllipsoid
import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# The quantitative perturbation behind the ellipsoid radius ratio

Suppose a set lies in the unit ball and in a half-space at distance less
than `1/d` from the origin.  An explicit affine perturbation still maps
the set into the unit ball and increases its determinant.  Consequently
a maximum-determinant normalization cannot admit such a half-space.
-/

set_option autoImplicit false
noncomputable section

open Set
open scoped RealInnerProductSpace

namespace CHS.Sections

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

theorem exists_det_improving_affine_of_one_sided_bound
    (hd : 0 < (Module.finrank ℝ E : ℝ)) {C : Set E} {v : E} (hv : ‖v‖ = 1)
    {a : ℝ} (ha : 0 ≤ a) (had : a * (Module.finrank ℝ E : ℝ) < 1)
    (hball : ∀ x ∈ C, ‖x‖ ≤ 1) (hsupport : ∀ x ∈ C, ⟪v, x⟫ ≤ a) :
    ∃ (S : E →L[ℝ] E) (b : E), 1 < S.det ∧ AffineBallFeasible C (S, b) := by
  obtain ⟨c, hac, hcd⟩ := exists_between ((lt_div_iff₀ hd).mpr had)
  have hc : 0 < c := ha.trans_lt hac
  have hdc : c * (Module.finrank ℝ E : ℝ) < 1 := (lt_div_iff₀ hd).mp hcd
  let A : E →L[ℝ] E := InnerProductSpace.rankOne ℝ v v - c • ContinuousLinearMap.id ℝ E
  let b : E := (1 - a) • v
  have htrace : 0 < LinearMap.trace ℝ E A.toLinearMap := by
    change 0 < LinearMap.trace ℝ E
      ((InnerProductSpace.rankOne ℝ v v).toLinearMap - c • (LinearMap.id : E →ₗ[ℝ] E))
    rw [map_sub, map_smul, InnerProductSpace.trace_rankOne, LinearMap.trace_id,
      real_inner_self_eq_norm_sq, hv, one_pow, smul_eq_mul]
    linarith
  let L : ℝ := ‖A‖ + ‖b‖
  have hL : 0 ≤ L := add_nonneg (norm_nonneg A) (norm_nonneg b)
  let δ : ℝ := min (1 / (4 * c)) ((c - a) / (L ^ 2 + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨t, ht, htδ, hdet⟩ := exists_small_linear_det_increase A htrace hδ
  have htc : 2 * t * c ≤ 1 := by
    have htt := htδ.trans_le (min_le_left _ _)
    have hp := (lt_div_iff₀ (by positivity : 0 < 4 * c)).mp htt
    nlinarith
  have htL : t * (L ^ 2 + 1) < c - a :=
    (lt_div_iff₀ (by positivity : 0 < L ^ 2 + 1)).mp (htδ.trans_le (min_le_right _ _))
  refine ⟨ContinuousLinearMap.id ℝ E + t • A, t • b, hdet, ?_⟩
  intro x hx
  have hxnorm := hball x hx
  have hxsq : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x]
  have hlower : -1 ≤ ⟪v, x⟫ := by
    have hi := abs_real_inner_le_norm v x
    rw [hv, one_mul] at hi
    linarith [(abs_le.mp hi).1]
  have hscalar : ⟪v, x⟫ ^ 2 + (1 - a) * ⟪v, x⟫ ≤ a := by
    have hp := mul_nonneg (sub_nonneg.mpr (hsupport x hx))
      (show 0 ≤ ⟪v, x⟫ + 1 by linarith)
    nlinarith
  have hinner : ⟪x, A x + b⟫ ≤ a - c * ‖x‖ ^ 2 := by
    simp only [A, b, ContinuousLinearMap.sub_apply, smul_apply,
      ContinuousLinearMap.id_apply, InnerProductSpace.rankOne_apply,
      inner_add_right, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
    rw [real_inner_comm x v]
    rw [real_inner_comm x v] at hscalar
    nlinarith
  have hnorm : ‖A x + b‖ ≤ L := by
    calc
      ‖A x + b‖ ≤ ‖A x‖ + ‖b‖ := norm_add_le _ _
      _ ≤ ‖A‖ * ‖x‖ + ‖b‖ := add_le_add (A.le_opNorm x) le_rfl
      _ ≤ L := by
        dsimp [L]
        exact add_le_add (mul_le_of_le_one_right (norm_nonneg A) hxnorm) le_rfl
  have hnormsq : ‖A x + b‖ ^ 2 ≤ L ^ 2 := by nlinarith [norm_nonneg (A x + b)]
  have hsq : ‖x + t • (A x + b)‖ ^ 2 ≤ 1 := by
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    have hi := mul_le_mul_of_nonneg_left hinner (show 0 ≤ 2 * t by positivity)
    have hquad := mul_le_mul_of_nonneg_left hnormsq (sq_nonneg t)
    have hremain := mul_le_mul_of_nonneg_left hxsq (show 0 ≤ 1 - 2 * t * c by linarith)
    have hsmall := mul_lt_mul_of_pos_left htL ht
    nlinarith [sq_nonneg t]
  have hnormfinal : ‖x + t • (A x + b)‖ ≤ 1 := by nlinarith [norm_nonneg (x + t • (A x + b))]
  change ‖(ContinuousLinearMap.id ℝ E + t • A) x + t • b‖ ≤ 1
  simpa only [ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply, smul_apply,
    smul_add, add_assoc] using hnormfinal

end CHS.Sections
