import CHS.Sections.EllipsoidPerturbation
import Mathlib.Analysis.LocallyConvex.Separation

/-!
# The inner ball of a maximum-determinant normalization

Separation of a point outside the convex body would put the body in a
half-space closer than `1/d` to the origin.  The explicit determinant
improving perturbation contradicts maximality.  The resulting radius
ratio is exactly `d`, including for nonsymmetric convex bodies.
-/

set_option autoImplicit false
noncomputable section

open Set Metric
open scoped RealInnerProductSpace

namespace CHS.Sections

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

theorem inner_ball_subset_of_maximal_affine_normalization
    (hd : 0 < (Module.finrank ℝ E : ℝ)) {C : Set E}
    (hconv : Convex ℝ C) (hclosed : IsClosed C) (hne : C.Nonempty)
    (hball : ∀ x ∈ C, ‖x‖ ≤ 1)
    (hmax : ∀ (S : E →L[ℝ] E) (b : E), AffineBallFeasible C (S, b) → S.det ≤ 1) :
    closedBall (0 : E) ((Module.finrank ℝ E : ℝ)⁻¹) ⊆ C := by
  intro y hy
  by_contra hyC
  obtain ⟨L, r, hCr, hry⟩ := geometric_hahn_banach_closed_point hconv hclosed hyC
  have hLne : L ≠ 0 := by
    intro hz
    obtain ⟨x, hx⟩ := hne
    have hlt := (hCr x hx).trans hry
    simp only [hz, zero_apply] at hlt
    exact lt_irrefl _ hlt
  have hL : 0 < ‖L‖ := norm_pos_iff.mpr hLne
  let v : E := ‖L‖⁻¹ • (InnerProductSpace.toDual ℝ E).symm L
  have hv : ‖v‖ = 1 := by
    simp only [v, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL),
      LinearIsometryEquiv.norm_map, inv_mul_cancel₀ hL.ne']
  have hvinner (x : E) : ⟪v, x⟫ = L x / ‖L‖ := by
    simp only [v, real_inner_smul_left, InnerProductSpace.toDual_symm_apply]
    rw [div_eq_inv_mul]
  have hrsmall : r / ‖L‖ < (Module.finrank ℝ E : ℝ)⁻¹ := by
    calc
      r / ‖L‖ < L y / ‖L‖ := (div_lt_div_iff_of_pos_right hL).mpr hry
      _ ≤ ‖y‖ := by
        apply (div_le_iff₀ hL).mpr
        calc
          L y ≤ ‖L y‖ := le_abs_self _
          _ ≤ ‖L‖ * ‖y‖ := L.le_opNorm y
          _ = ‖y‖ * ‖L‖ := mul_comm _ _
      _ ≤ (Module.finrank ℝ E : ℝ)⁻¹ := by simpa only [mem_closedBall, dist_zero_right] using hy
  let a : ℝ := max 0 (r / ‖L‖)
  have ha : 0 ≤ a := le_max_left _ _
  have haSmall : a < (Module.finrank ℝ E : ℝ)⁻¹ :=
    max_lt (inv_pos.mpr hd) hrsmall
  have had : a * (Module.finrank ℝ E : ℝ) < 1 :=
    (lt_div_iff₀ hd).mp (by simpa only [one_div] using haSmall)
  have hsupport (x : E) (hx : x ∈ C) : ⟪v, x⟫ ≤ a := by
    rw [hvinner]
    exact ((div_lt_div_iff_of_pos_right hL).mpr (hCr x hx)).le.trans (le_max_right _ _)
  obtain ⟨S, b, hdet, hfeasible⟩ :=
    exists_det_improving_affine_of_one_sided_bound hd hv ha had hball hsupport
  exact (not_lt_of_ge (hmax S b hfeasible)) hdet

end CHS.Sections
