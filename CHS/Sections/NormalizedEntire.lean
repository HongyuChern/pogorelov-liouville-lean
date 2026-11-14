import CHS.Calculus.TangentNormalization
import CHS.Calculus.ComplexAffineEquiv
import CHS.Algebra.ComplexNormalization
import CHS.Sections.QuotientSections

/-!
# The actual normalization of an entire convex solution in (3.3)

Subtract the tangent affine function and pull back by a complex matrix
of determinant of modulus one.  The actual real map is invertible; all
regularity, convexity, determinant, and compact-quotient conclusions are
proved for the resulting potential.
-/

set_option autoImplicit false
noncomputable section

open Set
open scoped ContDiff ComplexOrder

namespace CHS.Sections

open CHS.Calculus CHS.Analysis CHS.Algebra

variable {n : ℕ}
local notation "E₀" => DeGiorgi.AmbientSpace (n + n)

def tangentComplexPullback (u : E₀ → ℝ) (G : Matrix (Fin n) (Fin n) ℂ) : E₀ → ℝ :=
  fun x => tangentNormalized u (complexMatrixRealMap G x)

theorem contDiff_tangentComplexPullback {k : ℕ∞ω} {u : E₀ → ℝ}
    (hu : ContDiff ℝ k u) (G : Matrix (Fin n) (Fin n) ℂ) :
    ContDiff ℝ k (tangentComplexPullback u G) :=
  (contDiff_tangentNormalized hu).comp (complexMatrixRealMap G).contDiff

theorem tangentComplexPullback_zero (u : E₀ → ℝ) (G : Matrix (Fin n) (Fin n) ℂ) :
    tangentComplexPullback u G 0 = 0 := by
  simp only [tangentComplexPullback, map_zero, tangentNormalized_zero]

theorem fderiv_tangentComplexPullback_zero {u : E₀ → ℝ} (hu : ContDiff ℝ 2 u)
    (G : Matrix (Fin n) (Fin n) ℂ) :
    fderiv ℝ (tangentComplexPullback u G) 0 = 0 := by
  have h := (((contDiff_tangentNormalized hu).differentiable (by norm_num)
    (complexMatrixRealMap G 0)).hasFDerivAt.comp (0 : E₀)
      (complexMatrixRealMap G).hasFDerivAt).fderiv
  rw [map_zero, fderiv_tangentNormalized_zero (hu.differentiable (by norm_num)),
    ContinuousLinearMap.zero_comp] at h
  exact h

theorem realHessian_tangentComplexPullback {u : E₀ → ℝ} (hu : ContDiff ℝ 2 u)
    (G : Matrix (Fin n) (Fin n) ℂ) (x v w : E₀) :
    realHessian (tangentComplexPullback u G) x v w =
      realHessian u (complexMatrixRealMap G x) (complexMatrixRealMap G v)
        (complexMatrixRealMap G w) := by
  unfold tangentComplexPullback
  have h := realHessian_comp_affine (complexMatrixRealMap G) (0 : E₀)
    (u := tangentNormalized u) (x := x) (by
      exact (contDiff_tangentNormalized hu).contDiffAt) v w
  simpa only [tangentComplexPullback, zero_add,
    realHessian_tangentNormalized (hu.differentiable (by norm_num))]
    using h

theorem complexHessian_tangentComplexPullback {u : E₀ → ℝ} (hu : ContDiff ℝ 2 u)
    (G : Matrix (Fin n) (Fin n) ℂ) (x : E₀) :
    complexHessian realDirections imagDirections (tangentComplexPullback u G) x =
      G.transpose * complexHessian realDirections imagDirections u (complexMatrixRealMap G x) *
        G.map star := by
  unfold tangentComplexPullback
  have h := complexHessian_complex_affine G (0 : E₀)
    (u := tangentNormalized u) (x := x) (contDiff_tangentNormalized hu).contDiffAt
  simpa only [tangentComplexPullback, zero_add, complexHessian_tangentNormalized hu] using h

theorem realBlockHessian_posSemidef_tangentComplexPullback
    {u : E₀ → ℝ} (hu : ContDiff ℝ 2 u)
    (hR : ∀ x, (realBlockHessian realDirections imagDirections u x).PosSemidef)
    (G : Matrix (Fin n) (Fin n) ℂ) (x : E₀) :
    (realBlockHessian realDirections imagDirections (tangentComplexPullback u G) x).PosSemidef := by
  apply realBlockHessian_posSemidef_of_quadratic_nonneg
    (contDiff_tangentComplexPullback hu G).contDiffAt
  intro v
  rw [realHessian_tangentComplexPullback hu]
  exact realHessian_quadratic_nonneg_of_realBlockHessian hu.contDiffAt (hR _) _

theorem exists_normalized_entire_convex_solution
    (hn : 2 ≤ n) {u : E₀ → ℝ} (hu : ContDiff ℝ 4 u)
    (hdet : ∀ x, (complexHessian realDirections imagDirections u x).det = 1)
    (hR : ∀ x, (realBlockHessian realDirections imagDirections u x).PosSemidef) :
    ∃ G : Matrix (Fin n) (Fin n) ℂ,
      Complex.normSq G.det = 1 ∧ Function.Bijective (complexMatrixRealMap G) ∧
      let v := tangentComplexPullback u G
      ContDiff ℝ 4 v ∧ v 0 = 0 ∧ fderiv ℝ v 0 = 0 ∧
        complexHessian realDirections imagDirections v 0 = 1 ∧
        (∀ x, (complexHessian realDirections imagDirections v x).det = 1) ∧
        (∀ x, (realBlockHessian realDirections imagDirections v x).PosSemidef) ∧
        (∀ x, 0 ≤ v x) ∧
        ∀ h : ℝ, CHS.PogorelovCompactGeometry {x | v x < h} v := by
  letI : NeZero (n + n) := ⟨by omega⟩
  have hu2 : ContDiff ℝ 2 u := hu.of_le (by norm_num)
  have hA0 := complexHessian_posDef_of_realBlockHessian hu2.contDiffAt
    realDirections imagDirections (hR 0) (hdet 0)
  obtain ⟨G, hG0, hGdet⟩ := exists_complex_normalization_of_det_one hA0 (hdet 0)
  let v := tangentComplexPullback u G
  have hv : ContDiff ℝ 4 v := contDiff_tangentComplexPullback hu G
  have hv0 : v 0 = 0 := tangentComplexPullback_zero u G
  have hDv0 : fderiv ℝ v 0 = 0 := fderiv_tangentComplexPullback_zero hu2 G
  have hvA0 : complexHessian realDirections imagDirections v 0 = 1 := by
    rw [complexHessian_tangentComplexPullback hu2, map_zero]
    exact hG0
  have hvdet (x : E₀) : (complexHessian realDirections imagDirections v x).det = 1 := by
    rw [complexHessian_tangentComplexPullback hu2]
    change (G.transpose * complexHessian realDirections imagDirections u
      (complexMatrixRealMap G x) * G.transpose.conjTranspose).det = 1
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_transpose,
      hdet, mul_one, Complex.star_def, Complex.mul_conj, hGdet, Complex.ofReal_one]
  have hvR (x : E₀) := realBlockHessian_posSemidef_tangentComplexPullback hu2 hR G x
  have hvconv : ConvexOn ℝ univ v := convexOn_of_realBlockHessian_posSemidef
    isOpen_univ convex_univ (hv.of_le (by norm_num)).contDiffOn (fun x _ => hvR x)
  have hvnonneg (x : E₀) : 0 ≤ v x := by
    have hs := supporting_fderiv_of_convex hvconv (hv.differentiable (by norm_num)) 0 x
    simpa only [hv0, hDv0, zero_apply, add_zero] using hs
  exact ⟨G, hGdet, complexMatrixRealMap_bijective G (isUnit_det_of_normSq_eq_one hGdet),
    hv, hv0, hDv0, hvA0, hvdet, hvR, hvnonneg,
    entire_convex_sections_have_pogorelov_geometry hn hv hv0 hDv0 hvdet hvR⟩

end CHS.Sections
