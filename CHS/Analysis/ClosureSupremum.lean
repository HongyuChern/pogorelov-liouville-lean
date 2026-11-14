import CHS.Calculus.ClosureHessian
import CHS.Analysis.SupremumNorm

/-!
# Bounded weighted Hessian entries from actual C² boundary data

Compact representatives preserve the value and second derivative jet.
This proves boundedness without presupposing the Pogorelov estimate.
-/

set_option autoImplicit false
noncomputable section

open Set

namespace CHS.Analysis

open CHS.Calculus

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem bounded_weighted_hessian_of_compact_jet_representatives
    {u : E → ℝ} {U C : Set E} (hC : IsCompact C) (hCU : C ⊆ closure U)
    (J : ClosureC2Jet u U) (a b : ι → E) {β : ℝ} (hβ : 0 ≤ β)
    (hrep : ∀ x ∈ closure U, ∃ y ∈ C,
      u x = u y ∧ J.derivative x = J.derivative y ∧ J.hessian x = J.hessian y)
    (i j : ι ⊕ ι) :
    BddAbove ((fun x => |((((-u x) ^ β) • realBlockHessian a b u x) i j)|) '' U) := by
  apply bddAbove_abs_image_of_compact_extension hC hCU
    (J.continuousOn_weighted_realField_entry a b hβ i j)
  · intro x hx
    simp only [Matrix.smul_apply, smul_eq_mul, J.realField_eq hx a b]
  · intro x hx
    obtain ⟨y, hy, huv, _, hH⟩ := hrep x hx
    exact ⟨y, hy, by simp only [ClosureC2Jet.realField, huv, hH]⟩

end CHS.Analysis
