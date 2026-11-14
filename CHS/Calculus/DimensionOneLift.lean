import CHS.Calculus.HessianOrder
import CHS.Sections.QuotientSections

/-!
# An exact lift from one complex dimension to two

The new potential is u(z1)+|z2|², in the existing real-first block order.
The lift preserves determinant one and real convexity.  Its restriction
to z2=0 recovers the original actual potential and Hessian.
-/

set_option autoImplicit false
noncomputable section

open CHS.Analysis
open scoped BigOperators ComplexOrder ContDiff RealInnerProductSpace

namespace CHS.Calculus

local notation "E₁" => DeGiorgi.AmbientSpace 2
local notation "E₂" => DeGiorgi.AmbientSpace 4

def firstComplexProjection : E₂ →L[ℝ] E₁ :=
  (EuclideanSpace.proj (0 : Fin 4)).smulRight (EuclideanSpace.single (0 : Fin 2) 1) +
    (EuclideanSpace.proj (2 : Fin 4)).smulRight (EuclideanSpace.single (1 : Fin 2) 1)

def secondComplexProjection : E₂ →L[ℝ] E₁ :=
  (EuclideanSpace.proj (1 : Fin 4)).smulRight (EuclideanSpace.single (0 : Fin 2) 1) +
    (EuclideanSpace.proj (3 : Fin 4)).smulRight (EuclideanSpace.single (1 : Fin 2) 1)

def firstComplexInclusion : E₁ →L[ℝ] E₂ :=
  (EuclideanSpace.proj (0 : Fin 2)).smulRight (EuclideanSpace.single (0 : Fin 4) 1) +
    (EuclideanSpace.proj (1 : Fin 2)).smulRight (EuclideanSpace.single (2 : Fin 4) 1)

theorem firstComplexProjection_real (i : Fin 2) :
    firstComplexProjection (realDirections (n := 2) i) =
      if i = 0 then realDirections (n := 1) 0 else 0 := by
  fin_cases i <;> ext k <;> fin_cases k <;>
    norm_num [firstComplexProjection, realDirections, finSumFinEquiv, Fin.castAdd, Fin.ext_iff]

theorem firstComplexProjection_imag (i : Fin 2) :
    firstComplexProjection (imagDirections (n := 2) i) =
      if i = 0 then imagDirections (n := 1) 0 else 0 := by
  fin_cases i <;> ext k <;> fin_cases k <;>
    norm_num [firstComplexProjection, imagDirections, finSumFinEquiv, Fin.natAdd, Fin.ext_iff]

theorem secondComplexProjection_real (i : Fin 2) :
    secondComplexProjection (realDirections (n := 2) i) =
      if i = 1 then realDirections (n := 1) 0 else 0 := by
  fin_cases i <;> ext k <;> fin_cases k <;>
    norm_num [secondComplexProjection, realDirections, finSumFinEquiv, Fin.castAdd, Fin.ext_iff]

theorem secondComplexProjection_imag (i : Fin 2) :
    secondComplexProjection (imagDirections (n := 2) i) =
      if i = 1 then imagDirections (n := 1) 0 else 0 := by
  fin_cases i <;> ext k <;> fin_cases k <;>
    norm_num [secondComplexProjection, imagDirections, finSumFinEquiv, Fin.natAdd, Fin.ext_iff]

theorem firstComplexProjection_single (i : Fin 4) :
    firstComplexProjection (EuclideanSpace.single i 1) =
      if i = 0 then EuclideanSpace.single (0 : Fin 2) 1
      else if i = 2 then EuclideanSpace.single (1 : Fin 2) 1 else 0 := by
  fin_cases i <;> ext k <;> fin_cases k <;> norm_num [firstComplexProjection, Fin.ext_iff]

theorem secondComplexProjection_single (i : Fin 4) :
    secondComplexProjection (EuclideanSpace.single i 1) =
      if i = 1 then EuclideanSpace.single (0 : Fin 2) 1
      else if i = 3 then EuclideanSpace.single (1 : Fin 2) 1 else 0 := by
  fin_cases i <;> ext k <;> fin_cases k <;> norm_num [secondComplexProjection, Fin.ext_iff]

theorem firstComplexProjection_inclusion (x : E₁) :
    firstComplexProjection (firstComplexInclusion x) = x := by
  ext i
  fin_cases i <;> simp [firstComplexProjection, firstComplexInclusion]

theorem secondComplexProjection_inclusion (x : E₁) :
    secondComplexProjection (firstComplexInclusion x) = 0 := by
  ext i
  fin_cases i <;> simp [secondComplexProjection, firstComplexInclusion]

def dimensionOneExtension (u : E₁ → ℝ) (x : E₂) : ℝ :=
  u (firstComplexProjection x) + ‖secondComplexProjection x‖ ^ 2

theorem dimensionOneExtension_contDiff {u : E₁ → ℝ} {k : ℕ∞ω} (hu : ContDiff ℝ k u) :
    ContDiff ℝ k (dimensionOneExtension u) :=
  (hu.comp firstComplexProjection.contDiff).add (secondComplexProjection.contDiff.norm_sq ℝ)

theorem dimensionOneExtension_restrict (u : E₁ → ℝ) (x : E₁) :
    dimensionOneExtension u (firstComplexInclusion x) = u x := by
  simp only [dimensionOneExtension, firstComplexProjection_inclusion,
    secondComplexProjection_inclusion, norm_zero, zero_pow (by norm_num : 2 ≠ 0), add_zero]

theorem realHessian_dimensionOneExtension {u : E₁ → ℝ} (hu : ContDiff ℝ 2 u)
    (x v w : E₂) :
    realHessian (dimensionOneExtension u) x v w =
      realHessian u (firstComplexProjection x) (firstComplexProjection v) (firstComplexProjection w) +
        2 * ⟪secondComplexProjection v, secondComplexProjection w⟫ := by
  have hfirst : ContDiffAt ℝ 2 (fun y => u (firstComplexProjection y)) x :=
    (hu.comp firstComplexProjection.contDiff).contDiffAt
  have hsecond : ContDiffAt ℝ 2 (fun y => ‖secondComplexProjection y‖ ^ 2) x :=
    (secondComplexProjection.contDiff.norm_sq ℝ).contDiffAt
  change realHessian (fun y => u (firstComplexProjection y) + ‖secondComplexProjection y‖ ^ 2) x v w = _
  rw [realHessian_add hfirst hsecond]
  have hp := realHessian_comp_affine firstComplexProjection 0 (x := x) hu.contDiffAt v w
  simp only [zero_add] at hp
  rw [add_apply, add_apply, hp, realHessian_norm_sq_comp]

theorem dimensionOneExtension_real_convex {u : E₁ → ℝ} (hu : ContDiff ℝ 2 u)
    (hR : ∀ x, (realBlockHessian (realDirections (n := 1)) imagDirections u x).PosSemidef) :
    ∀ x, (realBlockHessian (realDirections (n := 2)) imagDirections (dimensionOneExtension u) x).PosSemidef := by
  intro x
  apply realBlockHessian_posSemidef_of_quadratic_nonneg
    (dimensionOneExtension_contDiff hu).contDiffAt (realDirections (n := 2)) imagDirections
  intro v
  rw [realHessian_dimensionOneExtension hu, real_inner_self_eq_norm_sq]
  exact add_nonneg
    (CHS.Sections.realHessian_quadratic_nonneg_of_realBlockHessian hu.contDiffAt (hR _) _)
    (mul_nonneg (by norm_num) (sq_nonneg _))

theorem dimensionOneExtension_hessian_bound {u : E₁ → ℝ} (hu : ContDiff ℝ 2 u)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, ∀ i j, |euclideanHessian (n := 1) u x i j| ≤ C) :
    ∀ x, ∀ i j, |euclideanHessian (n := 2) (dimensionOneExtension u) x i j| ≤ C + 2 := by
  intro x i j
  have h00 := hbound (firstComplexProjection x) 0 0
  have h01 := hbound (firstComplexProjection x) 0 1
  have h10 := hbound (firstComplexProjection x) 1 0
  have h11 := hbound (firstComplexProjection x) 1 1
  simp only [euclideanHessian] at h00 h01 h10 h11 ⊢
  rw [realHessian_dimensionOneExtension hu]
  rw [firstComplexProjection_single i, firstComplexProjection_single j,
    secondComplexProjection_single i, secondComplexProjection_single j]
  fin_cases i <;> fin_cases j <;>
    norm_num only [Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_ofNat, Nat.reduceMod,
      ite_true, ite_false] <;>
    norm_num [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two] <;> linarith

theorem dimensionOneExtension_complexHessian {u : E₁ → ℝ} (hu : ContDiff ℝ 2 u)
    (hdet : ∀ x, (complexHessian (realDirections (n := 1)) imagDirections u x).det = 1) (x : E₂) :
    complexHessian (realDirections (n := 2)) imagDirections (dimensionOneExtension u) x = 1 := by
  have h11 : complexHessian (realDirections (n := 1)) imagDirections u (firstComplexProjection x) 0 0 = 1 := by
    simpa only [Matrix.det_fin_one] using hdet (firstComplexProjection x)
  have hfirst := complexHessian_real_entry (hu.contDiffAt (x := firstComplexProjection x))
    realDirections imagDirections (0 : Fin 1) 0
  have h11' := hfirst.symm.trans h11
  ext i j
  rw [complexHessian_real_entry (dimensionOneExtension_contDiff hu).contDiffAt]
  simp only [realHessian_dimensionOneExtension hu, firstComplexProjection_real,
    firstComplexProjection_imag, secondComplexProjection_real, secondComplexProjection_imag]
  fin_cases i <;> fin_cases j <;>
    norm_num [realDirections, imagDirections,
      finSumFinEquiv, Fin.castAdd, Fin.natAdd,
      EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two] at h11' ⊢
  · exact h11'

end CHS.Calculus
