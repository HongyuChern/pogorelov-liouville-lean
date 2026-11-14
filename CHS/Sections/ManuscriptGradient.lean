import CHS.Sections.LocalInvariantSection

/-!
# One manuscript-facing entry for both alternatives in Lemma 3.1

The explicit dimension-only constant is positive. The quadratic barrier
may be replaced by any globally convex function with the stated C2
regularity and lower complex Hessian bound; the upper Hessian bound of
the manuscript is not needed for this stronger formulation.
-/

set_option autoImplicit false
noncomputable section

open DeGiorgi Set Metric
open scoped ContDiff ComplexOrder BigOperators

namespace CHS.Sections

open CHS.Calculus CHS.Analysis

def sectionDepthConstant (n : ℕ) : ℝ :=
  Real.sqrt ((32 * (n : ℝ) ^ 2)⁻¹ ^ (n - 1) / 2) / 16

theorem sectionDepthConstant_pos {n : ℕ} (hn : 0 < n) : 0 < sectionDepthConstant n := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  unfold sectionDepthConstant
  positivity

variable {n : ℕ}
local notation "E" => AmbientSpace (n + n)

def SectionCompactGeometry (U : Set E) (u q : E → ℝ) : Prop :=
  Bornology.IsBounded U ∨ ∃ K : Submodule ℝ E,
    (∀ x ∈ U, ∀ w ∈ K, x + w ∈ U) ∧
    (∀ x ∈ U, ∀ w ∈ K, u (x + w) = u x) ∧
    (∀ x ∈ U, ∀ w ∈ K, q (x + w) = q x) ∧
    IsCompact ((Submodule.Quotient.mk : E → E ⧸ K) '' closure U)

theorem normalized_section_gradient
    (hn : 0 < n) {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U)
    {u q : E → ℝ} (hu : C2OnClosure u U)
    (hR : ∀ x ∈ U, (realBlockHessian realDirections imagDirections u x).PosSemidef)
    (huBounds : ∀ x ∈ U, -1 ≤ u x ∧ u x < 0)
    (hbd : ∀ x ∈ frontier U, u x = 0)
    (hdet : ∀ x ∈ U, (complexHessian realDirections imagDirections u x).det = 1)
    (hq : ContinuousOn q (closure U)) (hq₂ : ContDiffOn ℝ 2 q U)
    (hqConvex : ConvexOn ℝ univ q)
    (hqBounds : ∀ x ∈ closure U, 0 ≤ q x ∧ q x ≤ 4 * (n : ℝ) ^ 2)
    (hQ : ∀ x ∈ U, (complexHessian realDirections imagDirections q x - 1).PosSemidef)
    (hgeometry : SectionCompactGeometry U u q) :
    0 < sectionDepthConstant n ∧
      ∀ x ∈ U, u x ≤ -1 / 4 →
        sectionDepthConstant n ≤ infDist x (frontier U) ∧
        Real.sqrt (∑ i, ‖affineWirtinger realDirections imagDirections (fderiv ℝ u x) i‖ ^ 2) ≤
          (sectionDepthConstant n)⁻¹ := by
  letI : NeZero (n + n) := ⟨by omega⟩
  have hc := hu.jet.continuous_value
  have hlower (x : E) (hx : x ∈ closure U) : -1 ≤ u x :=
    le_on_closure (fun y hy => (huBounds y hy).1) continuousOn_const hc hx
  have hupper (x : E) (hx : x ∈ U) : u x ≤ 0 := (huBounds x hx).2.le
  refine ⟨sectionDepthConstant_pos hn, ?_⟩
  intro x hx hdeep
  rcases hgeometry with hb | ⟨K, hUinv, huinv, hqinv, hquot⟩
  · exact bounded_section_estimates hn hU hb.isCompact_closure hconv hc hu.1 hR
      hq hq₂ hqBounds hQ hlower hupper hbd hdet hx hdeep
  · exact cylindrical_section_estimates_of_local_invariance hn K hU hconv hquot
      hUinv huinv hqinv hc hu.1 hR hq hq₂ hqConvex hqBounds hQ
      hlower hupper hbd hdet hx hdeep

end CHS.Sections
