import CHS.Sections.ConvexRealTrace
import CHS.Sections.NormalizedSectionEstimate
import CHS.Algebra.MatrixPullbackBounds

/-!
# Exhaustion and undoing the section coordinates in Proposition 3.2

The precise input still to be supplied by the ellipsoid construction is
a uniformly bounded family of normalized actual Hessians.  Given this
family, the proof derives the inverse-coordinate bound at the normalized
origin, pulls back the complex trace bound, exhausts the whole space, and
proves finiteness of the actual entrywise essential supremum.
This conditional assembly is not labelled Proposition 3.2 itself.
-/

set_option autoImplicit false
noncomputable section

open Set
open scoped ContDiff ComplexOrder ENNReal

namespace CHS.Sections

open CHS.Calculus CHS.Analysis CHS.Algebra

variable {n : ℕ}
local notation "E₀" => DeGiorgi.AmbientSpace (n + n)

theorem global_hessian_bound_of_normalized_section_family
    {u : E₀ → ℝ} (hu : ContDiff ℝ 2 u) (hu0 : u 0 = 0)
    (hA0 : complexHessian realDirections imagDirections u 0 = 1)
    (hdet : ∀ x, (complexHessian realDirections imagDirections u x).det = 1)
    (hR : ∀ x, (realBlockHessian realDirections imagDirections u x).PosSemidef)
    {M : ℝ} (hM : 0 ≤ M)
    (hfamily : ∀ h : ℝ, 0 < h → ∃ G : Matrix (Fin n) (Fin n) ℂ, ∃ c : E₀,
      Complex.normSq G.det = 1 ∧
      ∀ w : E₀, h⁻¹ * u (c + Real.sqrt h • complexMatrixRealMap G w) - 1 ≤ -1 / 2 →
        ∀ i j, |euclideanHessian
          (fun y => h⁻¹ * u (c + Real.sqrt h • complexMatrixRealMap G y) - 1) w i j| ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ x, ∀ i j, |euclideanHessian u x i j| ≤ C) ∧
      entryLinfNormOn MeasureTheory.volume univ (euclideanHessian u) ≤ C ∧
      ∀ i j, MeasureTheory.eLpNorm (fun x => euclideanHessian u x i j) (∞ : ℝ≥0∞)
        MeasureTheory.volume ≠ (∞ : ℝ≥0∞) := by
  let R : ℝ := (n : ℝ) * M / 2
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  obtain ⟨B, hB, hInvBound⟩ := exists_uniform_inverse_entry_bound n (Real.sqrt R)
  let C : ℝ := 4 * ((n : ℝ) ^ 3 * B ^ 2 * R)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hpoint (x : E₀) (i j : Fin (n + n)) : |euclideanHessian u x i j| ≤ C := by
    let h : ℝ := 2 * (|u x| + 1)
    have hh : 0 < h := by dsimp [h]; positivity
    obtain ⟨G, c, hGdet, hbound⟩ := hfamily h hh
    have hGunit := isUnit_det_of_normSq_eq_one hGdet
    obtain ⟨w0, hw0⟩ := exists_complex_affine_preimage G hGunit c hh (0 : E₀)
    have hM0 := hbound w0 (by rw [hw0, hu0]; norm_num)
    have hGHS : hsSq G ≤ R := hsSq_bound_at_normalized_origin hu hA0 G c hh w0 hw0 hM0
    have hInv : ∀ k l, ‖G⁻¹ k l‖ ≤ B := hInvBound G hGdet
      (fun k l => (norm_entry_le_sqrt_hsSq G k l).trans (Real.sqrt_le_sqrt hGHS))
    obtain ⟨w, hw⟩ := exists_complex_affine_preimage G hGunit c hh x
    have hdeep : h⁻¹ * u (c + Real.sqrt h • complexMatrixRealMap G w) - 1 ≤ -1 / 2 := by
      rw [hw]
      have hxhalf : u x ≤ h / 2 := by
        dsimp [h]
        linarith [le_abs_self (u x)]
      have hdiv : u x / h ≤ 1 / 2 := (div_le_iff₀ hh).mpr (by linarith)
      rw [div_eq_mul_inv, mul_comm] at hdiv
      linarith
    have hv := contDiff_normalized_affine hu (complexMatrixRealMap G) c h
    have htrace := complexHessian_trace_re_le_of_euclidean_entry_bound hv.contDiffAt (hbound w hdeep)
    rw [complexHessian_normalized_complex_affine G c hh hu.contDiffAt, hw] at htrace
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
