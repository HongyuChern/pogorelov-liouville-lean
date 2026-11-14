import CHS.Sections.EllipsoidQuadratic
import CHS.Sections.SectionRescaling
import CHS.Sections.SectionExhaustion

/-!
# The normalized global Hessian bound from actual ellipsoid sandwiches

The sole convex-geometric input is stated explicitly as a sandwich of
actual sublevel sets, with the factor `4 n²` of (3.4).  All subsequent
regularity, kernel, comparison, normalization, quotient, derivative,
matrix conditioning, exhaustion, and essential-supremum steps are proved.
This is a conditional reduction, not an unconditional Proposition 3.2.
-/

set_option autoImplicit false
noncomputable section

open Set
open scoped ContDiff ComplexOrder ENNReal

namespace CHS.Sections

open CHS.Calculus CHS.Analysis

variable {n : ℕ}
local notation "E₀" => DeGiorgi.AmbientSpace (n + n)

def HasEllipsoidSectionSandwiches (u : E₀ → ℝ) (K : Submodule ℝ E₀) : Prop :=
  ∀ h : ℝ, 0 < h → ∃ a : E₀, ∃ T : Kᗮ ≃L[ℝ] Kᗮ,
    (∀ x, ellipsoidQuadratic K T a x < 1 → u x < h) ∧
    (∀ x, u x < h → ellipsoidQuadratic K T a x < 4 * (n : ℝ) ^ 2)

theorem normalized_section_family_of_ellipsoid_sandwiches
    (hn : 2 ≤ n) {u : E₀ → ℝ} (hu : ContDiff ℝ 4 u)
    (hu0 : u 0 = 0) (hD0 : fderiv ℝ u 0 = 0)
    (hdet : ∀ x, (complexHessian realDirections imagDirections u x).det = 1)
    (hR : ∀ x, (realBlockHessian realDirections imagDirections u x).PosSemidef)
    (K : Submodule ℝ E₀) (hker : ∀ x, (realHessian u x).ker = K)
    (hsand : HasEllipsoidSectionSandwiches u K) :
    ∀ h : ℝ, 0 < h → ∃ G : Matrix (Fin n) (Fin n) ℂ, ∃ a : E₀,
      Complex.normSq G.det = 1 ∧
      ∀ w : E₀, h⁻¹ * u (a + Real.sqrt h • complexMatrixRealMap G w) - 1 ≤ -1 / 2 →
        ∀ i j, |euclideanHessian
          (fun y => h⁻¹ * u (a + Real.sqrt h • complexMatrixRealMap G y) - 1) w i j| ≤
            deepSublevelHessianConstant n (sectionGradientConstant n) := by
  letI : NeZero (n + n) := ⟨by omega⟩
  have hu2 : ContDiff ℝ 2 u := hu.of_le (by norm_num)
  have hA (x : E₀) := complexHessian_posDef_of_realBlockHessian hu2.contDiffAt
    realDirections imagDirections (hR x) (hdet x)
  have huconv : ConvexOn ℝ univ u := convexOn_of_realBlockHessian_posSemidef
    isOpen_univ convex_univ hu2.contDiffOn (fun x _ => hR x)
  have hunonneg (x : E₀) : 0 ≤ u x := by
    have hs := supporting_fderiv_of_convex huconv (hu2.differentiable (by norm_num)) 0 x
    simpa only [hu0, hD0, zero_apply, add_zero] using hs
  have huinv := invariant_of_fixed_realHessian_kernel hu2 hD0 K hker
  intro h hh
  obtain ⟨a, T, hinner, houter⟩ := hsand h hh
  let q := ellipsoidQuadratic K T a
  let C := complexHessian realDirections imagDirections q 0
  have hq : ContDiff ℝ 2 q := contDiff_ellipsoidQuadratic K T a 2
  have hC : C.PosDef := complexHessian_ellipsoidQuadratic_posDef K T a
    realDirections imagDirections hu2.contDiffAt (hA 0) (by rw [hker 0]) 0
  have hqH (x : E₀) : complexHessian realDirections imagDirections q x = C :=
    complexHessian_ellipsoidQuadratic_constant K T a realDirections imagDirections x 0
  have hquot := compact_quotient_section_of_fixed_kernel hu2 hu0 hD0
    (fun x z => realHessian_quadratic_nonneg_of_realBlockHessian hu2.contDiffAt (hR x) z)
    K hker h
  obtain ⟨G, hG, hbound⟩ := exists_normalized_section_hessian_bound_of_quadratic_sandwich
    hn hu hq hu0 hunonneg (ellipsoidQuadratic_nonneg K T a) hdet hR
    (realHessian_ellipsoidQuadratic_nonneg K T a) hC hqH a
    (ellipsoidQuadratic_center K T a) hh hinner houter K huinv
    (ellipsoidQuadratic_translation_invariant K T a) hquot
  exact ⟨G, a, hG, hbound⟩

theorem global_hessian_bound_of_ellipsoid_section_sandwiches
    (hn : 2 ≤ n) {u : E₀ → ℝ} (hu : ContDiff ℝ 4 u)
    (hu0 : u 0 = 0) (hD0 : fderiv ℝ u 0 = 0)
    (hA0 : complexHessian realDirections imagDirections u 0 = 1)
    (hdet : ∀ x, (complexHessian realDirections imagDirections u x).det = 1)
    (hR : ∀ x, (realBlockHessian realDirections imagDirections u x).PosSemidef)
    (hsand : HasEllipsoidSectionSandwiches u (realHessian u 0).ker) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ x, ∀ i j, |euclideanHessian u x i j| ≤ C) ∧
      entryLinfNormOn MeasureTheory.volume univ (euclideanHessian u) ≤ C ∧
      ∀ i j, MeasureTheory.eLpNorm (fun x => euclideanHessian u x i j) (∞ : ℝ≥0∞)
        MeasureTheory.volume ≠ (∞ : ℝ≥0∞) := by
  obtain ⟨K, hker, _, _⟩ :=
    entire_convex_sections_have_compact_real_quotient hn hu hu0 hD0 hdet hR
  have hker0 (x : E₀) : (realHessian u x).ker = (realHessian u 0).ker :=
    (hker x).trans (hker 0).symm
  have hfamily := normalized_section_family_of_ellipsoid_sandwiches hn hu hu0 hD0
    hdet hR (realHessian u 0).ker hker0 hsand
  apply global_hessian_bound_of_normalized_section_family (hu.of_le (by norm_num)) hu0
    hA0 hdet hR (M := deepSublevelHessianConstant n (sectionGradientConstant n)) ?_ hfamily
  unfold deepSublevelHessianConstant
  positivity

end CHS.Sections
