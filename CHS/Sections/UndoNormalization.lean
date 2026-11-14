import CHS.Sections.NormalizedEntire
import CHS.Sections.SectionExhaustion

/-!
# Undoing the fixed normalization (3.3)

A global bound for the actual Hessian after subtraction of the tangent
affine function and a fixed complex linear change of coordinates gives
a global bound for the original actual Hessian.  The resulting constant
may depend on this fixed change of coordinates, as in Proposition 3.2.
-/

set_option autoImplicit false
noncomputable section

open Set
open scoped ContDiff ComplexOrder ENNReal

namespace CHS.Sections

open CHS.Calculus CHS.Analysis CHS.Algebra

variable {n : ℕ}
local notation "E₀" => DeGiorgi.AmbientSpace (n + n)

theorem global_hessian_bound_of_tangent_complex_pullback
    {u : E₀ → ℝ} (hu : ContDiff ℝ 2 u)
    (hdet : ∀ x, (complexHessian realDirections imagDirections u x).det = 1)
    (hR : ∀ x, (realBlockHessian realDirections imagDirections u x).PosSemidef)
    (G : Matrix (Fin n) (Fin n) ℂ) (hG : Complex.normSq G.det = 1)
    {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ x, ∀ i j, |euclideanHessian (tangentComplexPullback u G) x i j| ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ x, ∀ i j, |euclideanHessian u x i j| ≤ C) ∧
      entryLinfNormOn MeasureTheory.volume univ (euclideanHessian u) ≤ C ∧
      ∀ i j, MeasureTheory.eLpNorm (fun x => euclideanHessian u x i j) (∞ : ℝ≥0∞)
        MeasureTheory.volume ≠ (∞ : ℝ≥0∞) := by
  have hGunit := isUnit_det_of_normSq_eq_one hG
  obtain ⟨B, hB, hInvBound⟩ := exists_uniform_inverse_entry_bound n (Real.sqrt (hsSq G))
  have hInv : ∀ i j, ‖G⁻¹ i j‖ ≤ B :=
    hInvBound G hG (norm_entry_le_sqrt_hsSq G)
  let R : ℝ := (n : ℝ) * M / 2
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  let C : ℝ := 4 * ((n : ℝ) ^ 3 * B ^ 2 * R)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hpoint (x : E₀) (i j : Fin (n + n)) : |euclideanHessian u x i j| ≤ C := by
    obtain ⟨w, hw⟩ := (complexMatrixRealMap_bijective G hGunit).2 x
    have htrace := complexHessian_trace_re_le_of_euclidean_entry_bound
      (contDiff_tangentComplexPullback hu G).contDiffAt (hbound w)
    rw [complexHessian_tangentComplexPullback hu, hw] at htrace
    have hA := complexHessian_posDef_of_realBlockHessian hu.contDiffAt
      realDirections imagDirections (hR x) (hdet x)
    have htraceA := complex_congruence_trace_bound hA.posSemidef hGunit hB hR0 hInv htrace
    exact (euclideanHessian_entry_le_four_trace_of_convex hu.contDiffAt (hR x) (hdet x) i j).trans
      (mul_le_mul_of_nonneg_left htraceA (by norm_num : (0 : ℝ) ≤ 4))
  refine ⟨C, hC, hpoint,
    entryLinfNormOn_le_of_pointwise_bound MeasureTheory.volume MeasurableSet.univ hC
      (fun x _ => hpoint x), ?_⟩
  have hfinite := entrywise_eLpNorm_top_ne_top_of_pointwise_bound MeasureTheory.volume
    MeasurableSet.univ (fun x _ => hpoint x)
  simpa only [MeasureTheory.Measure.restrict_univ] using hfinite

end CHS.Sections
