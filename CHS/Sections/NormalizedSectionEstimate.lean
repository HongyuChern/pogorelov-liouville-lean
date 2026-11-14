import CHS.Sections.DeepSublevel
import CHS.Sections.QuotientSections
import CHS.Pogorelov.QuotientSlice

/-!
# From Lemma 3.1 to the actual normalized Hessian estimate (3.7)--(3.8)

The gradient input of the Pogorelov estimate is derived here from the
accepted section lemma.  The case of a bounded section is included by
taking the translation subspace to be zero.
-/

set_option autoImplicit false
noncomputable section

open Set
open scoped BigOperators ContDiff ENNReal ComplexOrder

namespace CHS.Sections

open CHS.Calculus CHS.Analysis CHS.Algebra CHS.Pogorelov

variable {n : ℕ}
local notation "E₀" => DeGiorgi.AmbientSpace (n + n)

def sectionGradientConstant (n : ℕ) : ℝ :=
  (Real.sqrt ((32 * (n : ℝ) ^ 2)⁻¹ ^ (n - 1) / 2) / 16)⁻¹

theorem gradientNormSq_eq_affineWirtinger
    {v : E₀ → ℝ} {x : E₀} (hv : DifferentiableAt ℝ v x) :
    gradientNormSq realDirections imagDirections v x =
      ∑ i, ‖affineWirtinger realDirections imagDirections (fderiv ℝ v x) i‖ ^ 2 := by
  rw [gradientNormSq_eq_wirtinger hv]
  simp only [vecSq, wirtingerGradient, affineWirtinger, Complex.normSq_eq_norm_sq]

theorem normalized_section_gradient_bound
    (hn : 2 ≤ n) {v q : E₀ → ℝ} (hv : ContDiff ℝ 4 v) (hq : ContDiff ℝ 2 q)
    (hdet : ∀ x, (complexHessian realDirections imagDirections v x).det = 1)
    (hR : ∀ x, (realBlockHessian realDirections imagDirections v x).PosSemidef)
    (hlower : ∀ x, -1 ≤ v x) (hqconv : ConvexOn ℝ univ q)
    (hqBounds : ∀ x ∈ closure {y | v y < 0}, 0 ≤ q x ∧ q x ≤ 4 * (n : ℝ) ^ 2)
    (hQ : ∀ x, v x < 0 → (complexHessian realDirections imagDirections q x - 1).PosSemidef)
    (K : Submodule ℝ E₀)
    (hvinv : ∀ x w : E₀, w ∈ K → v (x + w) = v x)
    (hqinv : ∀ x w : E₀, w ∈ K → q (x + w) = q x)
    (hquot : IsCompact ((Submodule.Quotient.mk : E₀ → E₀ ⧸ K) '' closure {x | v x < 0})) :
    ∀ x, v x ≤ -1 / 4 →
      gradientNormSq realDirections imagDirections v x ≤ sectionGradientConstant n ^ 2 := by
  letI : NeZero (n + n) := ⟨by omega⟩
  let U : Set E₀ := {x | v x < 0}
  have hU : IsOpen U := isOpen_lt hv.continuous continuous_const
  have hv2 : ContDiff ℝ 2 v := hv.of_le (by norm_num)
  have hvconv : ConvexOn ℝ univ v := convexOn_of_realBlockHessian_posSemidef
    isOpen_univ convex_univ hv2.contDiffOn (fun x _ => hR x)
  have hUconv : Convex ℝ U := by
    simpa only [mem_univ, true_and] using hvconv.convex_lt 0
  have hUinv : ∀ x ∈ U, ∀ w ∈ K, x + w ∈ U := by
    intro x hx w hw
    change v (x + w) < 0
    rwa [hvinv x w hw]
  have hslice := compact_orthogonal_slice_of_compact_real_quotient K hUinv hquot
  have hboundary : ∀ x ∈ frontier U, v x = 0 :=
    fun x hx => frontier_lt_subset_eq hv.continuous continuous_const hx
  intro x hx
  have hxU : x ∈ U := by change v x < 0; linarith
  have hb := (cylindrical_section_estimates (by omega : 0 < n) K hU hUconv hslice hUinv
    hvinv hqinv hv.continuous.continuousOn hv2.contDiffOn (fun y _ => hR y)
    hq.continuous.continuousOn hq.contDiffOn hqconv hqBounds hQ
    (fun y _ => hlower y) (fun y hy => le_of_lt hy) hboundary (fun y _ => hdet y) hxU hx).2
  rw [← gradientNormSq_eq_affineWirtinger (hv.differentiable (by norm_num) x)] at hb
  have hs := pow_le_pow_left₀ (Real.sqrt_nonneg _) hb 2
  rw [Real.sq_sqrt (gradientNormSq_nonneg realDirections imagDirections v x)] at hs
  exact hs

theorem normalized_section_deep_hessian_bound
    (hn : 2 ≤ n) {v q : E₀ → ℝ} (hv : ContDiff ℝ 4 v) (hq : ContDiff ℝ 2 q)
    (hdet : ∀ x, (complexHessian realDirections imagDirections v x).det = 1)
    (hR : ∀ x, (realBlockHessian realDirections imagDirections v x).PosSemidef)
    (hlower : ∀ x, -1 ≤ v x) (hqconv : ConvexOn ℝ univ q)
    (hqBounds : ∀ x ∈ closure {y | v y < 0}, 0 ≤ q x ∧ q x ≤ 4 * (n : ℝ) ^ 2)
    (hQ : ∀ x, v x < 0 → (complexHessian realDirections imagDirections q x - 1).PosSemidef)
    (K : Submodule ℝ E₀)
    (hvinv : ∀ x w : E₀, w ∈ K → v (x + w) = v x)
    (hqinv : ∀ x w : E₀, w ∈ K → q (x + w) = q x)
    (hquot : IsCompact ((Submodule.Quotient.mk : E₀ → E₀ ⧸ K) '' closure {x | v x < 0})) :
    (∀ x, v x ≤ -1 / 2 → ∀ i j,
      |euclideanHessian v x i j| ≤ deepSublevelHessianConstant n (sectionGradientConstant n)) ∧
      entryLinfNormOn MeasureTheory.volume {x | v x ≤ -1 / 2} (euclideanHessian v) ≤
        deepSublevelHessianConstant n (sectionGradientConstant n) ∧
      ∀ i j, MeasureTheory.eLpNorm (fun x => euclideanHessian v x i j) (∞ : ℝ≥0∞)
        (MeasureTheory.volume.restrict {x | v x ≤ -1 / 2}) ≠ (∞ : ℝ≥0∞) := by
  have hgrad := normalized_section_gradient_bound hn hv hq hdet hR hlower hqconv
    hqBounds hQ K hvinv hqinv hquot
  have hgeometry : CHS.PogorelovCompactGeometry {x | v x < 0} v := by
    refine Or.inr ⟨K, ?_, fun x _ w hw => hvinv x w hw, hquot⟩
    intro x hx w hw
    change v (x + w) < 0
    rwa [hvinv x w hw]
  have hgeometry' := hgeometry.lower_sublevel (by norm_num : (-1 : ℝ) / 4 ≤ 0)
  have hK : ∀ x, v x < -1 / 4 →
      gradientNormSq realDirections imagDirections v x ≤ sectionGradientConstant n ^ 2 :=
    fun x hx => hgrad x hx.le
  exact ⟨normalized_deep_sublevel_hessian_pointwise hn hv hdet hR hlower
    (sectionGradientConstant n) hK hgeometry',
    normalized_deep_sublevel_hessian_linf hn hv hdet hR hlower
      (sectionGradientConstant n) hK hgeometry'⟩

end CHS.Sections
