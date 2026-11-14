import CHS.Pogorelov.PositiveBranch
import CHS.Analysis.SupremumNorm

/-!
# Supremum-norm endpoint of the positive definite Pogorelov branch

All norms here are explicitly defined pointwise supremum seminorms.
Boundedness of the value and gradient is proved from the C² extension and
compact representatives, rather than added to the theorem's hypotheses.
-/

set_option autoImplicit false
noncomputable section

open Matrix Set
open scoped BigOperators ComplexOrder ContDiff

namespace CHS.Pogorelov

open CHS.Calculus CHS.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : ℕ}

def gradientSupNormOn (a b : Fin n → E) (u : E → ℝ) (U : Set E) : ℝ :=
  scalarSupNormOn U (fun x => Real.sqrt (gradientNormSq a b u x))

def weightedHessianSupNormOn (a b : Fin n → E) (u : E → ℝ) (U : Set E) (κ : ℝ) : ℝ :=
  entrySupNormOn U (fun x => ((-u x) ^ beta n κ) • realBlockHessian a b u x)

theorem bounded_value_and_gradient_of_compact_jet_representatives
    {u : E → ℝ} {U C : Set E} (hU : IsOpen U) (hC : IsCompact C) (hCU : C ⊆ closure U)
    (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U) (a b : Fin n → E)
    (hrep : ∀ x ∈ closure U, ∃ y ∈ C,
      u x = u y ∧ J.derivative x = J.derivative y ∧ J.hessian x = J.hessian y) :
    BddAbove ((fun x => |u x|) '' U) ∧
      BddAbove ((fun x => |Real.sqrt (gradientNormSq a b u x)|) '' U) := by
  constructor
  · exact bddAbove_abs_image_of_compact_extension hC hCU J.continuous_value
      (fun _ _ => rfl) (fun x hx => by
        obtain ⟨y, hy, hxy, _, _⟩ := hrep x hx
        exact ⟨y, hy, hxy⟩)
  · let F := fun x => Real.sqrt (J.gradientField a b x)
    have hF : ContinuousOn F (closure U) :=
      Real.continuous_sqrt.comp_continuousOn (J.continuousOn_gradientField a b)
    have hmatch : EqOn F (fun x => Real.sqrt (gradientNormSq a b u x)) U := by
      intro x hx
      change Real.sqrt (J.gradientField a b x) = _
      rw [J.gradientField_eq hx ((hu.contDiffAt (hU.mem_nhds hx)).differentiableAt
        (by norm_num)) a b]
    apply bddAbove_abs_image_of_compact_extension hC hCU hF hmatch
    intro x hx
    obtain ⟨y, hy, _, hD, _⟩ := hrep x hx
    exact ⟨y, hy, by simp only [F, ClosureC2Jet.gradientField, hD]⟩

theorem gradientNormSq_le_sup_sq {u : E → ℝ} {U : Set E} (a b : Fin n → E)
    (hbounded : BddAbove ((fun x => |Real.sqrt (gradientNormSq a b u x)|) '' U))
    {x : E} (hx : x ∈ U) : gradientNormSq a b u x ≤ (gradientSupNormOn a b u U) ^ 2 := by
  have h := abs_le_scalarSupNormOn hbounded hx
  rw [abs_of_nonneg (Real.sqrt_nonneg _)] at h
  have hs := Real.sq_sqrt (gradientNormSq_nonneg a b u x)
  have hn := scalarSupNormOn_nonneg hbounded
  change 0 ≤ gradientSupNormOn a b u U at hn
  change Real.sqrt (gradientNormSq a b u x) ≤ gradientSupNormOn a b u U at h
  nlinarith [Real.sqrt_nonneg (gradientNormSq a b u x)]

theorem positive_branch_supremum_estimate_of_compact_jet_representatives
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
      u x = u y ∧ J.derivative x = J.derivative y ∧ J.hessian x = J.hessian y) :
    weightedHessianSupNormOn a b u U κ ≤
      32 * (n : ℝ) * beta n κ * (1 + Real.sqrt κ) * Real.exp (1 / 8) *
        (1 + gradientSupNormOn a b u U ^ 2) * scalarSupNormOn U u ^ (beta n κ - 1) := by
  obtain ⟨hvalue, hgradient⟩ := bounded_value_and_gradient_of_compact_jet_representatives
    hU hC hCU (hu.of_le (by norm_num)) J a b hrep
  have hK : ∀ y ∈ U, gradientNormSq a b u y ≤ gradientSupNormOn a b u U ^ 2 :=
    fun _ hy => gradientNormSq_le_sup_sq a b hgradient hy
  have hV : ∀ y ∈ U, -u y ≤ scalarSupNormOn U u :=
    fun y hy => (neg_le_abs (u y)).trans (abs_le_scalarSupNormOn hvalue hy)
  have hpoint := positive_branch_estimate_of_compact_jet_representatives hn hU hC hCU hu J
    a b hdet hpos hκ hmat hbd hrep (gradientSupNormOn a b u U) (scalarSupNormOn U u) hK hV
  have hβ : 0 ≤ beta n κ := by linarith [beta_sub_one_pos hn hκ]
  have hV0 : 0 ≤ scalarSupNormOn U u := scalarSupNormOn_nonneg hvalue
  unfold weightedHessianSupNormOn
  apply entrySupNormOn_le (by positivity)
  intro x hx i j
  exact hpoint x hx i j

theorem positive_branch_supremum_estimate_of_compact_closure
    {u : E → ℝ} {U : Set E} (hn : 2 ≤ n) (hU : IsOpen U)
    (hcompact : IsCompact (closure U)) (hu : ContDiffOn ℝ 4 u U)
    (huBoundary : C2OnClosure u U) (a b : Fin n → E)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = 1)
    (hpos : ∀ y ∈ U, (complexHessian a b u y).PosDef)
    {κ : ℝ} (hκ : 1 ≤ κ)
    (hmat : ∀ y ∈ U, (κ • complexHessian a b u y -
      pureHessian a b u y * ((complexHessian a b u y).map star)⁻¹ *
        (pureHessian a b u y).map star).PosSemidef)
    (hbd : ∀ y ∈ frontier U, u y = 0) :
    weightedHessianSupNormOn a b u U κ ≤
      32 * (n : ℝ) * beta n κ * (1 + Real.sqrt κ) * Real.exp (1 / 8) *
        (1 + gradientSupNormOn a b u U ^ 2) * scalarSupNormOn U u ^ (beta n κ - 1) :=
  positive_branch_supremum_estimate_of_compact_jet_representatives hn hU hcompact Subset.rfl hu
    huBoundary.jet a b hdet hpos hκ hmat hbd (fun x hx => ⟨x, hx, rfl, rfl, rfl⟩)

end CHS.Pogorelov
