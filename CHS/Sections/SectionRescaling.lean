import CHS.Sections.SectionScale
import CHS.Sections.NormalizedSectionEstimate
import CHS.Calculus.ScaledComplexAffine
import CHS.Pogorelov.AffineGeometry

/-!
# Actual normalized section estimates from the quadratic sandwich

This file joins (3.4)--(3.8), including the scale bound, the matrix
normalization, the actual real affine map, the transformed translation
subspace, and compactness of the actual quotient of the section closure.
Existence of the initial ellipsoid sandwich remains a separate input.
-/

set_option autoImplicit false
noncomputable section

open Set
open scoped ContDiff ComplexOrder

namespace CHS.Sections

open CHS.Calculus CHS.Analysis CHS.Algebra CHS.Pogorelov

variable {n : ℕ}
local notation "E₀" => DeGiorgi.AmbientSpace (n + n)

theorem exists_normalized_section_hessian_bound_of_quadratic_sandwich
    (hn : 2 ≤ n) {u q : E₀ → ℝ} (hu : ContDiff ℝ 4 u) (hq : ContDiff ℝ 2 q)
    (hu0 : u 0 = 0) (hunonneg : ∀ x, 0 ≤ u x) (hqnonneg : ∀ x, 0 ≤ q x)
    (hdet : ∀ x, (complexHessian realDirections imagDirections u x).det = 1)
    (hR : ∀ x, (realBlockHessian realDirections imagDirections u x).PosSemidef)
    (hqR : ∀ x v, 0 ≤ realHessian q x v v)
    {C : Matrix (Fin n) (Fin n) ℂ} (hC : C.PosDef)
    (hqH : ∀ x, complexHessian realDirections imagDirections q x = C)
    (a : E₀) (hqa : q a = 0) {h : ℝ} (hh : 0 < h)
    (hinner : ∀ x, q x < 1 → u x < h)
    (houter : ∀ x, u x < h → q x < 4 * (n : ℝ) ^ 2)
    (K : Submodule ℝ E₀)
    (huinv : ∀ x z : E₀, z ∈ K → u (x + z) = u x)
    (hqinv : ∀ x z : E₀, z ∈ K → q (x + z) = q x)
    (hquot : IsCompact ((Submodule.Quotient.mk : E₀ → E₀ ⧸ K) '' closure {x | u x < h})) :
    ∃ G : Matrix (Fin n) (Fin n) ℂ, Complex.normSq G.det = 1 ∧
      ∀ w : E₀, h⁻¹ * u (a + Real.sqrt h • complexMatrixRealMap G w) - 1 ≤ -1 / 2 →
        ∀ i j, |euclideanHessian
          (fun y => h⁻¹ * u (a + Real.sqrt h • complexMatrixRealMap G y) - 1) w i j| ≤
            deepSublevelHessianConstant n (sectionGradientConstant n) := by
  letI : NeZero (n + n) := ⟨by omega⟩
  have hu2 : ContDiff ℝ 2 u := hu.of_le (by norm_num)
  have hA (x : E₀) := complexHessian_posDef_of_realBlockHessian hu2.contDiffAt
    realDirections imagDirections (hR x) (hdet x)
  have hscale := section_scale_bounds_of_quadratic_sandwich (by omega) hu2 hq hu0
    hunonneg hqnonneg hdet hA hC hqH a hqa hh hinner houter K huinv hqinv hquot
  obtain ⟨G, hG, hGdet⟩ := exists_complex_normalization_det_root (by omega : 0 < n) hC
  let T := scaledComplexRealEquiv G (isUnit_det_of_normSq_eq_one hGdet) hh
  let K' : Submodule ℝ E₀ := K.comap T.toLinearMap
  let v : E₀ → ℝ := fun w => h⁻¹ * u (a + Real.sqrt h • complexMatrixRealMap G w) - 1
  let Q : E₀ → ℝ := fun w => q (a + T w)
  have hv : ContDiff ℝ 4 v := contDiff_normalized_affine hu (complexMatrixRealMap G) a h
  have hv2 : ContDiff ℝ 2 v := hv.of_le (by norm_num)
  have hQ : ContDiff ℝ 2 Q := hq.comp (contDiff_const.add T.contDiff)
  have hvdet (x : E₀) : (complexHessian realDirections imagDirections v x).det = 1 :=
    complexHessian_det_normalized_complex_affine G a hh hu2.contDiffAt (hdet _) hGdet
  have hvR (x : E₀) : (realBlockHessian realDirections imagDirections v x).PosSemidef := by
    apply realBlockHessian_posSemidef_of_quadratic_nonneg hv2.contDiffAt
    intro z
    rw [realHessian_normalized_affine (complexMatrixRealMap G) a hh hu2.contDiffAt]
    exact realHessian_quadratic_nonneg_of_realBlockHessian hu2.contDiffAt (hR _) _
  have hvlower (x : E₀) : -1 ≤ v x := by
    dsimp only [v]
    have hp := mul_nonneg (inv_nonneg.mpr hh.le) (hunonneg (a + Real.sqrt h • complexMatrixRealMap G x))
    linarith
  have hviff (x : E₀) : v x < 0 ↔ u (a + T x) < h := by
    change h⁻¹ * u (a + T x) - 1 < 0 ↔ u (a + T x) < h
    rw [sub_lt_iff_lt_add, zero_add, mul_comm h⁻¹, ← div_eq_mul_inv, div_lt_iff₀ hh, one_mul]
  have hQR (x : E₀) : (realBlockHessian realDirections imagDirections Q x).PosSemidef := by
    apply realBlockHessian_posSemidef_of_quadratic_nonneg hQ.contDiffAt
    intro z
    change 0 ≤ realHessian (fun y => q (a + T.toContinuousLinearMap y)) x z z
    rw [realHessian_comp_affine T.toContinuousLinearMap a hq.contDiffAt]
    exact hqR _ _
  have hQconv : ConvexOn ℝ univ Q := convexOn_of_realBlockHessian_posSemidef
    isOpen_univ convex_univ hQ.contDiffOn (fun x _ => hQR x)
  have hQbar : closure {x | v x < 0} ⊆ {x | Q x ≤ 4 * (n : ℝ) ^ 2} := by
    apply closure_minimal ?_ (isClosed_le hQ.continuous continuous_const)
    intro x hx
    exact (houter (a + T x) ((hviff x).mp hx)).le
  have hQbounds (x : E₀) (hx : x ∈ closure {y | v y < 0}) :
      0 ≤ Q x ∧ Q x ≤ 4 * (n : ℝ) ^ 2 := ⟨hqnonneg _, hQbar hx⟩
  have hQH (x : E₀) : complexHessian realDirections imagDirections Q x =
      (h * hermitianDetRoot C) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    change complexHessian realDirections imagDirections
      (fun y => q (a + Real.sqrt h • complexMatrixRealMap G y)) x = _
    rw [complexHessian_scaled_complex_affine G a hh hq.contDiffAt, hqH, hG]
    change h • ((hermitianDetRoot C : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ)) = _
    rw [smul_smul]
  have hQge (x : E₀) (_ : v x < 0) :
      (complexHessian realDirections imagDirections Q x - 1).PosSemidef := by
    rw [hQH]
    have heq : (h * hermitianDetRoot C) • (1 : Matrix (Fin n) (Fin n) ℂ) - 1 =
        (h * hermitianDetRoot C - 1) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
      rw [sub_smul, one_smul]
    rw [heq]
    exact Matrix.PosSemidef.one.smul (sub_nonneg.mpr hscale.2.2.1)
  have hvinv (x z : E₀) (hz : z ∈ K') : v (x + z) = v x := by
    change h⁻¹ * u (a + T (x + z)) - 1 = h⁻¹ * u (a + T x) - 1
    rw [map_add, ← add_assoc, huinv (a + T x) (T z) hz]
  have hQinv (x z : E₀) (hz : z ∈ K') : Q (x + z) = Q x := by
    change q (a + T (x + z)) = q (a + T x)
    rw [map_add, ← add_assoc, hqinv (a + T x) (T z) hz]
  have hUinv : ∀ x ∈ {x | u x < h}, ∀ z ∈ K, x + z ∈ {x | u x < h} := by
    intro x hx z hz
    change u (x + z) < h
    rwa [huinv x z hz]
  have hVeq : {x | v x < 0} = {x | a + T x ∈ {y | u y < h}} := by
    ext x
    exact hviff x
  have hvquot : IsCompact ((Submodule.Quotient.mk : E₀ → E₀ ⧸ K') '' closure {x | v x < 0}) := by
    rw [hVeq]
    exact compact_real_quotient_affine_preimage T a K hUinv hquot
  exact ⟨G, hGdet, (normalized_section_deep_hessian_bound hn hv hQ hvdet hvR hvlower
    hQconv hQbounds hQge K' hvinv hQinv hvquot).1⟩

end CHS.Sections
