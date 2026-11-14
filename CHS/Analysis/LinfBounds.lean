import CHS.Analysis.MatrixSupremum

/-! # Entrywise essential-supremum bounds on measurable sets -/

set_option autoImplicit false
noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace CHS.Analysis

variable {E ι κ : Type*} [MeasurableSpace E]

theorem entrywise_eLpNorm_top_le_of_pointwise_bound
    (μ : Measure E) {U : Set E} (hU : MeasurableSet U) {H : E → Matrix ι κ ℝ}
    {R : ℝ} (hH : ∀ x ∈ U, ∀ i j, |H x i j| ≤ R) :
    ∀ i j, eLpNorm (fun x => H x i j) ∞ (μ.restrict U) ≤ ENNReal.ofReal R := by
  intro i j
  rw [eLpNorm_exponent_top]
  apply eLpNormEssSup_le_of_ae_bound
  exact (ae_restrict_mem hU).mono
    (fun x hx => by simpa only [Real.norm_eq_abs] using hH x hx i j)

theorem entrywise_eLpNorm_top_ne_top_of_pointwise_bound
    (μ : Measure E) {U : Set E} (hU : MeasurableSet U) {H : E → Matrix ι κ ℝ}
    {R : ℝ} (hH : ∀ x ∈ U, ∀ i j, |H x i j| ≤ R) :
    ∀ i j, eLpNorm (fun x => H x i j) ∞ (μ.restrict U) ≠ ∞ :=
  fun i j => ((entrywise_eLpNorm_top_le_of_pointwise_bound μ hU hH i j).trans_lt
    ENNReal.ofReal_lt_top).ne

theorem entryLinfNormOn_le_of_pointwise_bound
    (μ : Measure E) {U : Set E} (hU : MeasurableSet U) {H : E → Matrix ι κ ℝ}
    {R : ℝ} (hR : 0 ≤ R) (hH : ∀ x ∈ U, ∀ i j, |H x i j| ≤ R) :
    entryLinfNormOn μ U H ≤ R := by
  apply csSup_le ⟨0, mem_insert 0 _⟩
  intro r hr
  rcases mem_insert_iff.mp hr with rfl | hr
  · exact hR
  · obtain ⟨⟨i, j⟩, rfl⟩ := hr
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (entrywise_eLpNorm_top_le_of_pointwise_bound μ hU hH i j)
    simpa only [ENNReal.toReal_ofReal hR] using h

end CHS.Analysis
