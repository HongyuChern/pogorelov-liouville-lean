import CHS.Pogorelov.SupremumEstimate
import CHS.Analysis.MatrixSupremum
import CHS.Analysis.ClosureSupremum

/-!
# The exact measure-theoretic L∞ endpoint

For a measure positive on nonempty open sets, the pointwise estimates
identify with the manuscript's essential supremum seminorms.  Boundedness
is discharged from the actual C² jets and compact representatives.
-/

set_option autoImplicit false
noncomputable section

open Set MeasureTheory
open scoped ContDiff ComplexOrder ENNReal

namespace CHS.Pogorelov

open CHS.Calculus CHS.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [MeasurableSpace E] [OpensMeasurableSpace E]
variable {μ : Measure E} [μ.IsOpenPosMeasure] {n : ℕ}

def scalarLinfNormOn (μ : Measure E) (U : Set E) (f : E → ℝ) : ℝ :=
  (eLpNorm f ∞ (μ.restrict U)).toReal

def gradientLinfNormOn (μ : Measure E) (a b : Fin n → E) (u : E → ℝ)
    (U : Set E) : ℝ :=
  scalarLinfNormOn μ U (fun x => Real.sqrt (gradientNormSq a b u x))

def weightedHessianLinfNormOn (μ : Measure E) (a b : Fin n → E) (u : E → ℝ)
    (U : Set E) (κ : ℝ) : ℝ :=
  entryLinfNormOn μ U (fun x => ((-u x) ^ beta n κ) • realBlockHessian a b u x)

theorem supremum_norms_eq_linf_of_compact_jet_representatives
    {u : E → ℝ} {U C : Set E} (hU : IsOpen U) (hC : IsCompact C) (hCU : C ⊆ closure U)
    (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U) (a b : Fin n → E)
    {κ : ℝ} (hβ : 0 ≤ beta n κ)
    (hrep : ∀ x ∈ closure U, ∃ y ∈ C,
      u x = u y ∧ J.derivative x = J.derivative y ∧ J.hessian x = J.hessian y) :
    scalarSupNormOn U u = scalarLinfNormOn μ U u ∧
      gradientSupNormOn a b u U = gradientLinfNormOn μ a b u U ∧
      weightedHessianSupNormOn a b u U κ = weightedHessianLinfNormOn μ a b u U κ := by
  obtain ⟨hvalue, hgradient⟩ := bounded_value_and_gradient_of_compact_jet_representatives
    hU hC hCU hu J a b hrep
  have hG : ContinuousOn (fun x => Real.sqrt (gradientNormSq a b u x)) U := by
    apply ((Real.continuous_sqrt.comp_continuousOn
      (J.continuousOn_gradientField a b)).mono subset_closure).congr
    intro x hx
    change Real.sqrt (gradientNormSq a b u x) = Real.sqrt (J.gradientField a b x)
    rw [J.gradientField_eq hx
      ((hu.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)) a b]
  refine ⟨scalarSupNormOn_eq_eLpNorm_top_toReal (μ := μ) hU hu.continuousOn hvalue, ?_, ?_⟩
  · exact scalarSupNormOn_eq_eLpNorm_top_toReal (μ := μ) hU hG hgradient
  · exact entrySupNormOn_eq_entryLinfNormOn (μ := μ) hU
      (J.continuousOn_weighted_realBlockHessian_entry a b hβ)
      (bounded_weighted_hessian_of_compact_jet_representatives hC hCU J a b hβ hrep)

theorem positive_branch_linf_estimate_of_compact_jet_representatives
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
    weightedHessianLinfNormOn μ a b u U κ ≤
      32 * (n : ℝ) * beta n κ * (1 + Real.sqrt κ) * Real.exp (1 / 8) *
        (1 + gradientLinfNormOn μ a b u U ^ 2) * scalarLinfNormOn μ U u ^ (beta n κ - 1) := by
  have hβ : 0 ≤ beta n κ := by linarith [beta_sub_one_pos hn hκ]
  obtain ⟨hvalue, hgradient, hH⟩ := supremum_norms_eq_linf_of_compact_jet_representatives
    (μ := μ) hU hC hCU (hu.of_le (by norm_num)) J a b hβ hrep
  have h := positive_branch_supremum_estimate_of_compact_jet_representatives
    hn hU hC hCU hu J a b hdet hpos hκ hmat hbd hrep
  rwa [hvalue, hgradient, hH] at h

end CHS.Pogorelov
