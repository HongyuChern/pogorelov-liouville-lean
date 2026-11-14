import CHS.Calculus.AffinePullback
import CHS.Calculus.ComplexFrame
import CHS.Analysis.BlockCoordinates

/-!
# Complex affine coordinates in the fixed real block model

`complexMatrixRealMap G` is the real linear map represented by `G` on
complex coordinates.  Its action on every fixed real/imaginary basis
vector is proved.  The resulting actual Hessian transformation has the
manuscript's order `Gᵀ A conjugate(G)` and `Gᵀ B G`.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped ContDiff

namespace CHS.Calculus

open CHS.Analysis

variable {n : ℕ}
local notation "E₀" => DeGiorgi.AmbientSpace (n + n)

def complexMatrixRealMap (G : Matrix (Fin n) (Fin n) ℂ) : E₀ →L[ℝ] E₀ :=
  (((EuclideanSpace.basisFun (Fin (n + n)) ℝ).toBasis).constr ℝ
    (fun k => Sum.elim (complexFrameReal G.transpose realDirections imagDirections)
      (complexFrameImag G.transpose realDirections imagDirections) (finSumFinEquiv.symm k))).toContinuousLinearMap

theorem complexMatrixRealMap_realDirection (G : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    complexMatrixRealMap G (realDirections i) =
      complexFrameReal G.transpose realDirections imagDirections i := by
  let B := (EuclideanSpace.basisFun (Fin (n + n)) ℝ).toBasis
  have hB : realDirections i = B (finSumFinEquiv (Sum.inl i)) :=
    (EuclideanSpace.basisFun_apply (Fin (n + n)) ℝ _).symm
  rw [hB]
  change (B.constr ℝ _) (B (finSumFinEquiv (Sum.inl i))) = _
  rw [B.constr_basis]
  simp only [Equiv.symm_apply_apply, Sum.elim_inl]

theorem complexMatrixRealMap_imagDirection (G : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    complexMatrixRealMap G (imagDirections i) =
      complexFrameImag G.transpose realDirections imagDirections i := by
  let B := (EuclideanSpace.basisFun (Fin (n + n)) ℝ).toBasis
  have hB : imagDirections i = B (finSumFinEquiv (Sum.inr i)) :=
    (EuclideanSpace.basisFun_apply (Fin (n + n)) ℝ _).symm
  rw [hB]
  change (B.constr ℝ _) (B (finSumFinEquiv (Sum.inr i))) = _
  rw [B.constr_basis]
  simp only [Equiv.symm_apply_apply, Sum.elim_inr]

theorem complexHessian_complex_affine
    (G : Matrix (Fin n) (Fin n) ℂ) (c : E₀) {u : E₀ → ℝ} {x : E₀}
    (hu : ContDiffAt ℝ 2 u (c + complexMatrixRealMap G x)) :
    complexHessian realDirections imagDirections (fun y => u (c + complexMatrixRealMap G y)) x =
      G.transpose * complexHessian realDirections imagDirections u (c + complexMatrixRealMap G x) *
        G.map star := by
  rw [complexHessian_comp_affine (complexMatrixRealMap G) c hu]
  simp only [complexMatrixRealMap_realDirection, complexMatrixRealMap_imagDirection]
  rw [complexHessian_complexFrame hu]
  rfl

theorem pureHessian_complex_affine
    (G : Matrix (Fin n) (Fin n) ℂ) (c : E₀) {u : E₀ → ℝ} {x : E₀}
    (hu : ContDiffAt ℝ 2 u (c + complexMatrixRealMap G x)) :
    pureHessian realDirections imagDirections (fun y => u (c + complexMatrixRealMap G y)) x =
      G.transpose * pureHessian realDirections imagDirections u (c + complexMatrixRealMap G x) * G := by
  rw [pureHessian_comp_affine (complexMatrixRealMap G) c hu]
  simp only [complexMatrixRealMap_realDirection, complexMatrixRealMap_imagDirection]
  rw [pureHessian_complexFrame hu, Matrix.transpose_transpose]

theorem complexHessian_normalized_complex_affine
    (G : Matrix (Fin n) (Fin n) ℂ) (c : E₀) {h : ℝ} (hh : 0 < h)
    {u : E₀ → ℝ} {x : E₀}
    (hu : ContDiffAt ℝ 2 u (c + Real.sqrt h • complexMatrixRealMap G x)) :
    complexHessian realDirections imagDirections
        (fun y => h⁻¹ * u (c + Real.sqrt h • complexMatrixRealMap G y) - 1) x =
      G.transpose * complexHessian realDirections imagDirections u
        (c + Real.sqrt h • complexMatrixRealMap G x) * G.map star := by
  rw [complexHessian_normalized_affine (complexMatrixRealMap G) c hh hu]
  simp only [complexMatrixRealMap_realDirection, complexMatrixRealMap_imagDirection]
  rw [complexHessian_complexFrame hu]
  rfl

theorem pureHessian_normalized_complex_affine
    (G : Matrix (Fin n) (Fin n) ℂ) (c : E₀) {h : ℝ} (hh : 0 < h)
    {u : E₀ → ℝ} {x : E₀}
    (hu : ContDiffAt ℝ 2 u (c + Real.sqrt h • complexMatrixRealMap G x)) :
    pureHessian realDirections imagDirections
        (fun y => h⁻¹ * u (c + Real.sqrt h • complexMatrixRealMap G y) - 1) x =
      G.transpose * pureHessian realDirections imagDirections u
        (c + Real.sqrt h • complexMatrixRealMap G x) * G := by
  rw [pureHessian_normalized_affine (complexMatrixRealMap G) c hh hu]
  simp only [complexMatrixRealMap_realDirection, complexMatrixRealMap_imagDirection]
  rw [pureHessian_complexFrame hu, Matrix.transpose_transpose]

theorem complexHessian_det_normalized_complex_affine
    (G : Matrix (Fin n) (Fin n) ℂ) (c : E₀) {h : ℝ} (hh : 0 < h)
    {u : E₀ → ℝ} {x : E₀}
    (hu : ContDiffAt ℝ 2 u (c + Real.sqrt h • complexMatrixRealMap G x))
    (hdet : (complexHessian realDirections imagDirections u
      (c + Real.sqrt h • complexMatrixRealMap G x)).det = 1)
    (hG : Complex.normSq G.det = 1) :
    (complexHessian realDirections imagDirections
      (fun y => h⁻¹ * u (c + Real.sqrt h • complexMatrixRealMap G y) - 1) x).det = 1 := by
  rw [complexHessian_normalized_complex_affine G c hh hu]
  change (G.transpose * complexHessian realDirections imagDirections u
    (c + Real.sqrt h • complexMatrixRealMap G x) * G.transpose.conjTranspose).det = 1
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_transpose,
    hdet, mul_one, Complex.star_def, Complex.mul_conj, hG, Complex.ofReal_one]

end CHS.Calculus
