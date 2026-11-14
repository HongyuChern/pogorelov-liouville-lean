import CHS.Analysis.SupremumNorm
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Topology.Order.Lattice

/-!
# Identification with the measure-theoretic L∞ norm

For a measure positive on nonempty open sets, a continuous function on an
open domain has the same supremum and essential supremum.  The finite
upper bound is explicit.  This also covers an empty domain.
-/

set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory
open scoped ENNReal

namespace CHS.Analysis

variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
variable {μ : Measure E} [μ.IsOpenPosMeasure]

theorem le_on_open_of_ae_le {U : Set E} (hU : IsOpen U) {f g : E → ℝ}
    (hf : ContinuousOn f U) (hg : ContinuousOn g U)
    (hae : ∀ᵐ x ∂μ.restrict U, f x ≤ g x) : ∀ x ∈ U, f x ≤ g x := by
  have heq : (fun x => min (f x) (g x)) =ᵐ[μ.restrict U] f :=
    hae.mono (fun _ h => min_eq_left h)
  have h := MeasureTheory.Measure.eqOn_open_of_ae_eq heq hU (hf.inf hg) hf
  intro x hx
  exact min_eq_left_iff.mp (h hx)

theorem eLpNorm_top_le_of_pointwise_bound {U : Set E} (hU : IsOpen U)
    {f : E → ℝ} {R : ℝ} (hf : ∀ x ∈ U, |f x| ≤ R) :
    eLpNorm f ∞ (μ.restrict U) ≤ ENNReal.ofReal R := by
  rw [eLpNorm_exponent_top]
  apply eLpNormEssSup_le_of_ae_bound
  exact (ae_restrict_mem hU.measurableSet).mono
    (fun x hx => by simpa only [Real.norm_eq_abs] using hf x hx)

theorem scalarSupNormOn_eq_eLpNorm_top_toReal {U : Set E} (hU : IsOpen U)
    {f : E → ℝ} (hf : ContinuousOn f U)
    (hbounded : BddAbove ((fun x => |f x|) '' U)) :
    scalarSupNormOn U f = (eLpNorm f ∞ (μ.restrict U)).toReal := by
  have hupper := eLpNorm_top_le_of_pointwise_bound (μ := μ) hU
    (fun _ hx => abs_le_scalarSupNormOn hbounded hx)
  have hfinite : eLpNorm f ∞ (μ.restrict U) ≠ ∞ :=
    (hupper.trans_lt ENNReal.ofReal_lt_top).ne
  have hae : ∀ᵐ x ∂μ.restrict U,
      |f x| ≤ (eLpNorm f ∞ (μ.restrict U)).toReal := by
    filter_upwards [enorm_ae_le_eLpNormEssSup f (μ.restrict U)] with x hx
    apply (ENNReal.ofReal_le_iff_le_toReal hfinite).mp
    simpa only [← Real.norm_eq_abs, ofReal_norm, eLpNorm_exponent_top] using hx
  have hnorm : ContinuousOn (fun x => |f x|) U := by
    simpa only [Real.norm_eq_abs] using hf.norm
  apply le_antisymm
  · exact scalarSupNormOn_le ENNReal.toReal_nonneg
      (le_on_open_of_ae_le (μ := μ) hU hnorm continuousOn_const hae)
  · have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hupper
    simpa only [ENNReal.toReal_ofReal (scalarSupNormOn_nonneg hbounded)] using h

theorem eLpNorm_top_eq_ofReal_scalarSupNormOn {U : Set E} (hU : IsOpen U)
    {f : E → ℝ} (hf : ContinuousOn f U)
    (hbounded : BddAbove ((fun x => |f x|) '' U)) :
    eLpNorm f ∞ (μ.restrict U) = ENNReal.ofReal (scalarSupNormOn U f) := by
  have hupper := eLpNorm_top_le_of_pointwise_bound (μ := μ) hU
    (fun _ hx => abs_le_scalarSupNormOn hbounded hx)
  have hfinite : eLpNorm f ∞ (μ.restrict U) ≠ ∞ :=
    (hupper.trans_lt ENNReal.ofReal_lt_top).ne
  rw [scalarSupNormOn_eq_eLpNorm_top_toReal (μ := μ) hU hf hbounded,
    ENNReal.ofReal_toReal hfinite]

end CHS.Analysis
