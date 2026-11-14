import CHS.Sections.SectionEllipsoidConstruction
import CHS.Sections.UndoNormalization

/-!
# Proposition 3.2: the global actual real Hessian bound

All section ellipsoids are constructed, rather than assumed.  The proof
uses the accepted fixed-kernel theorem, actual normalized section
estimates, exhaustion, and undoing the fixed initial normalization.
The main theorem needs only C⁴; the smooth manuscript statement is
provided as an immediate public specialization.
-/

set_option autoImplicit false
noncomputable section

open Set
open scoped ContDiff ComplexOrder ENNReal

namespace CHS

open Calculus Analysis Sections

variable {n : ℕ}
local notation "E₀" => DeGiorgi.AmbientSpace (n + n)

theorem entire_convex_hessian_bound
    (hn : 2 ≤ n) {u : E₀ → ℝ} (hu : ContDiff ℝ 4 u)
    (hdet : ∀ x, (complexHessian realDirections imagDirections u x).det = 1)
    (hR : ∀ x, (realBlockHessian realDirections imagDirections u x).PosSemidef) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ x, ∀ i j, |euclideanHessian u x i j| ≤ C) ∧
      entryLinfNormOn MeasureTheory.volume univ (euclideanHessian u) ≤ C ∧
      ∀ i j, MeasureTheory.eLpNorm (fun x => euclideanHessian u x i j) (∞ : ℝ≥0∞)
        MeasureTheory.volume ≠ (∞ : ℝ≥0∞) := by
  obtain ⟨G, hG, _, hv, hv0, hDv0, hAv0, hvdet, hvR, _, _⟩ :=
    exists_normalized_entire_convex_solution hn hu hdet hR
  have hsand := entire_convex_ellipsoid_section_sandwiches hn hv hv0 hDv0 hvdet hvR
  obtain ⟨M, hM, hbound, _, _⟩ := global_hessian_bound_of_ellipsoid_section_sandwiches
    hn hv hv0 hDv0 hAv0 hvdet hvR hsand
  exact global_hessian_bound_of_tangent_complex_pullback (hu.of_le (by norm_num))
    hdet hR G hG hM hbound

/-- The smooth statement of Proposition 3.2, with actual finite entrywise
essential supremum and a stronger everywhere pointwise bound. -/
theorem proposition_3_2_global_hessian_bound
    (hn : 2 ≤ n) {u : E₀ → ℝ} (hu : ContDiff ℝ ∞ u)
    (hdet : ∀ x, (complexHessian realDirections imagDirections u x).det = 1)
    (hR : ∀ x, (realBlockHessian realDirections imagDirections u x).PosSemidef) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ x, ∀ i j, |euclideanHessian u x i j| ≤ C) ∧
      entryLinfNormOn MeasureTheory.volume univ (euclideanHessian u) ≤ C ∧
      ∀ i j, MeasureTheory.eLpNorm (fun x => euclideanHessian u x i j) (∞ : ℝ≥0∞)
        MeasureTheory.volume ≠ (∞ : ℝ≥0∞) :=
  entire_convex_hessian_bound hn
    (hu.of_le (WithTop.coe_le_coe.mpr (le_top : (4 : ℕ∞) ≤ ⊤))) hdet hR

end CHS
