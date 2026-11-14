import CHS.Pogorelov.BoundaryExtension
import CHS.Pogorelov.CompactMaximum
import CHS.Pogorelov.Negativity

/-!
# Maximum attainment and trace estimate from C² boundary data

This file discharges both strict negativity and maximum attainment.  Its
compact-closure specialization has no maximum-point input.  The compact
representative statement is used subsequently for the real-translation
quotient.
-/

set_option autoImplicit false
noncomputable section

open Matrix Set Filter
open scoped BigOperators ComplexOrder ContDiff Topology

namespace CHS.Pogorelov

open CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : ℕ}

theorem exists_pogorelovTest_maximum_of_compact_jet_representatives
    {u : E → ℝ} {U C : Set E} (hn : 2 ≤ n) (hU : IsOpen U) (hne : U.Nonempty)
    (hC : IsCompact C) (hCU : C ⊆ closure U) (hu : ContDiffOn ℝ 4 u U)
    (J : ClosureC2Jet u U) (a b : Fin n → E)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = 1)
    (hpos : ∀ y ∈ U, (complexHessian a b u y).PosDef)
    {κ : ℝ} (hκ : 1 ≤ κ)
    (hmat : ∀ y ∈ U, (κ • complexHessian a b u y -
      pureHessian a b u y * ((complexHessian a b u y).map star)⁻¹ *
        (pureHessian a b u y).map star).PosSemidef)
    (hbd : ∀ y ∈ frontier U, u y = 0)
    (hrep : ∀ x ∈ closure U, ∃ y ∈ C,
      u x = u y ∧ J.derivative x = J.derivative y ∧ J.hessian x = J.hessian y)
    (K : ℝ) :
    (∀ x ∈ U, u x < 0) ∧
      ∃ x ∈ U, 0 < pogorelovTest a b u κ K x ∧
        IsMaxOn (pogorelovTest a b u κ K) U x ∧
        IsLocalMax (pogorelovTest a b u κ K) x := by
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hu₂ : ContDiffOn ℝ 2 u U := hu.of_le (by norm_num)
  have hneg : ∀ x ∈ U, u x < 0 :=
    neg_on_of_compact_representatives hU hC hCU J.continuous_value hu₂ a b hpos hbd
      (fun x hx => by
        obtain ⟨y, hy, hxy, _, _⟩ := hrep x hx
        exact ⟨y, hy, hxy⟩)
  have hβ : 0 < beta n κ := by linarith [beta_sub_one_pos hn hκ]
  have hmatch : EqOn (closurePogorelovTest J a b κ K) (pogorelovTest a b u κ K) U := by
    intro x hx
    exact closurePogorelovTest_eq J hx (hu₂.contDiffAt (hU.mem_nhds hx)) a b
      (hdet x hx) κ K
  have hrepTest : ∀ x ∈ closure U, ∃ y ∈ C,
      closurePogorelovTest J a b κ K x = closurePogorelovTest J a b κ K y := by
    intro x hx
    obtain ⟨y, hy, huv, hD, hH⟩ := hrep x hx
    refine ⟨y, hy, ?_⟩
    simp only [closurePogorelovTest, ClosureC2Jet.traceField,
      ClosureC2Jet.gradientField, huv, hD, hH]
  have hpositive : ∃ x ∈ U, 0 < pogorelovTest a b u κ K x := by
    obtain ⟨x, hx⟩ := hne
    refine ⟨x, hx, ?_⟩
    exact mul_pos
      (mul_pos (Real.rpow_pos_of_pos (neg_pos.mpr (hneg x hx)) _)
        (traceCombination_pos_of_posDef hn (hu₂.contDiffAt (hU.mem_nhds hx))
          a b (hpos x hx) hκ (hmat x hx))) (Real.exp_pos _)
  exact ⟨hneg, exists_interior_maximum_of_compact_extension hU hC hCU
    (closurePogorelovTest_continuousOn J a b hβ.le K) hmatch
    (closurePogorelovTest_eq_zero_on_frontier J a b hβ K hbd) hrepTest hpositive⟩

theorem weighted_trace_bound_of_compact_jet_representatives
    {u : E → ℝ} {U C : Set E} (hn : 2 ≤ n) (hU : IsOpen U)
    (hC : IsCompact C) (hCU : C ⊆ closure U) (hu : ContDiffOn ℝ 4 u U)
    (J : ClosureC2Jet u U) (a b : Fin n → E)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = 1)
    (hpos : ∀ y ∈ U, (complexHessian a b u y).PosDef)
    {κ : ℝ} (hκ : 1 ≤ κ)
    (hmat : ∀ y ∈ U, (κ • complexHessian a b u y -
      pureHessian a b u y * ((complexHessian a b u y).map star)⁻¹ *
        (pureHessian a b u y).map star).PosSemidef)
    (hbd : ∀ y ∈ frontier U, u y = 0)
    (hrep : ∀ x ∈ closure U, ∃ y ∈ C,
      u x = u y ∧ J.derivative x = J.derivative y ∧ J.hessian x = J.hessian y)
    (K V : ℝ) (hK : ∀ y ∈ U, gradientNormSq a b u y ≤ K ^ 2)
    (hV : ∀ y ∈ U, -u y ≤ V) :
    ∀ y ∈ U, (-u y) ^ beta n κ * traceCombination a b u (cChoice n κ) y ≤
      16 * (n : ℝ) * beta n κ * cChoice n κ * Real.exp (1 / 8) *
        (1 + K ^ 2) * V ^ (beta n κ - 1) := by
  intro y hy
  obtain ⟨hneg, x, hx, _, hmax, _⟩ :=
    exists_pogorelovTest_maximum_of_compact_jet_representatives hn hU ⟨y, hy⟩
      hC hCU hu J a b hdet hpos hκ hmat hbd hrep K
  exact weighted_trace_bound_at_attained_test_maximum hn hU hu a b hdet hpos hκ hmat
    K V hK hV hneg hx hmax y hy

theorem weighted_trace_bound_of_compact_closure
    {u : E → ℝ} {U : Set E} (hn : 2 ≤ n) (hU : IsOpen U)
    (hcompact : IsCompact (closure U)) (hu : ContDiffOn ℝ 4 u U)
    (huBoundary : C2OnClosure u U) (a b : Fin n → E)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = 1)
    (hpos : ∀ y ∈ U, (complexHessian a b u y).PosDef)
    {κ : ℝ} (hκ : 1 ≤ κ)
    (hmat : ∀ y ∈ U, (κ • complexHessian a b u y -
      pureHessian a b u y * ((complexHessian a b u y).map star)⁻¹ *
        (pureHessian a b u y).map star).PosSemidef)
    (hbd : ∀ y ∈ frontier U, u y = 0)
    (K V : ℝ) (hK : ∀ y ∈ U, gradientNormSq a b u y ≤ K ^ 2)
    (hV : ∀ y ∈ U, -u y ≤ V) :
    ∀ y ∈ U, (-u y) ^ beta n κ * traceCombination a b u (cChoice n κ) y ≤
      16 * (n : ℝ) * beta n κ * cChoice n κ * Real.exp (1 / 8) *
        (1 + K ^ 2) * V ^ (beta n κ - 1) :=
  weighted_trace_bound_of_compact_jet_representatives hn hU hcompact Subset.rfl hu
    huBoundary.jet a b hdet hpos hκ hmat hbd
    (fun x hx => ⟨x, hx, rfl, rfl, rfl⟩) K V hK hV

end CHS.Pogorelov
