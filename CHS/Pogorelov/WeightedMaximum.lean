import CHS.Pogorelov.PositiveMaximum

/-!
# Propagation from an attained maximum

This is the weighted form of (2.32).  The maximum is of the actual test
function, and its differential estimate is supplied by PositiveMaximum.
Attainment from the two geometric alternatives remains a separate input.
-/

set_option autoImplicit false
noncomputable section

open Matrix Filter
open scoped BigOperators ComplexOrder ContDiff Topology

namespace CHS.Pogorelov

open CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : ℕ}

theorem weighted_trace_bound_at_attained_test_maximum {u : E → ℝ} {U : Set E}
    (hn : 2 ≤ n) (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : Fin n → E)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = 1)
    (hpos : ∀ y ∈ U, (complexHessian a b u y).PosDef)
    {κ : ℝ} (hκ : 1 ≤ κ)
    (hmat : ∀ y ∈ U, (κ • complexHessian a b u y -
      pureHessian a b u y * ((complexHessian a b u y).map star)⁻¹ *
        (pureHessian a b u y).map star).PosSemidef)
    (K V : ℝ) (hK : ∀ y ∈ U, gradientNormSq a b u y ≤ K ^ 2)
    (hV : ∀ y ∈ U, -u y ≤ V) (hneg : ∀ y ∈ U, u y < 0)
    {x₀ : E} (hx₀ : x₀ ∈ U) (hmax : IsMaxOn (pogorelovTest a b u κ K) U x₀) :
    ∀ y ∈ U, (-u y) ^ beta n κ * traceCombination a b u (cChoice n κ) y ≤
      16 * (n : ℝ) * beta n κ * cChoice n κ * Real.exp (1 / 8) *
        (1 + K ^ 2) * V ^ (beta n κ - 1) := by
  have hu2 (y : E) (hy : y ∈ U) : ContDiffAt ℝ 2 u y :=
    (hu.contDiffAt (hU.mem_nhds hy)).of_le (by norm_num)
  have hlocal : IsLocalMax (pogorelovTest a b u κ K) x₀ :=
    hmax.isLocalMax (hU.mem_nhds hx₀)
  have htrace := trace_bound_at_test_maximum hn hU hu a b hdet hx₀ (hpos x₀ hx₀)
    hκ (hmat x₀ hx₀) K (hK x₀ hx₀) (hneg x₀ hx₀) hlocal
  have ha₀ : 0 ≤ (complexHessian a b u x₀).trace.re :=
    (Complex.nonneg_iff.mp (hpos x₀ hx₀).posSemidef.trace_nonneg).1
  have hm₀ : (κ • complexHessian a b u x₀ -
      (complexHessian a b u x₀ - schurHessian a b u x₀)).PosSemidef := by
    change (κ • complexHessian a b u x₀ - (_ - (_ - _))).PosSemidef
    rw [sub_sub_cancel]
    exact hmat x₀ hx₀
  have hd₀ : 0 ≤ (correctionTrace a b u x₀).re :=
    (schur_correction_trace_bounds (hu2 x₀ hx₀) a b (hpos x₀ hx₀) κ hm₀).1
  intro y hy
  have hS : 0 ≤ traceCombination a b u (cChoice n κ) y :=
    (traceCombination_pos_of_posDef hn (hu2 y hy) a b (hpos y hy) hκ (hmat y hy)).le
  exact weighted_trace_bound_of_test_maximum hn hκ K
    (neg_pos.mpr (hneg x₀ hx₀)) (hV x₀ hx₀) (neg_pos.mpr (hneg y hy))
    ha₀ hd₀ rfl (hK x₀ hx₀) (gradientNormSq_nonneg a b u y) hS htrace (hmax hy)

end CHS.Pogorelov
