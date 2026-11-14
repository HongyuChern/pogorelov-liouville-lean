import CHS.Analysis.LinearizedFlux
import CHS.Analysis.MatrixSupremum

/-!
# The actual Euclidean Hessian and the two-block coordinate indexing

The public Euclidean matrix is indexed by `Fin (n + n)`.  The two-block
matrix used in the complex calculations is its exact reindexing, with all
real directions first.  The entrywise L∞ seminorm is preserved exactly.
-/

set_option autoImplicit false
noncomputable section

open Set MeasureTheory

namespace CHS.Analysis

open CHS.Calculus

variable {n : ℕ}
local notation "E" => DeGiorgi.AmbientSpace (n + n)

def euclideanHessian (u : E → ℝ) (x : E) : Matrix (Fin (n + n)) (Fin (n + n)) ℝ :=
  fun i j => realHessian u x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)

theorem blockDirection_eq_single (i : Fin n ⊕ Fin n) :
    Sum.elim realDirections imagDirections i = EuclideanSpace.single (finSumFinEquiv i) (1 : ℝ) := by
  cases i <;> rfl

theorem realBlockHessian_reindex (u : E → ℝ) (x : E) :
    Matrix.reindex finSumFinEquiv finSumFinEquiv
      (realBlockHessian realDirections imagDirections u x) = euclideanHessian u x := by
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, realBlockHessian,
    blockDirection_eq_single, Equiv.apply_symm_apply, euclideanHessian]

theorem weighted_realBlockHessian_linf_eq_euclidean (μ : Measure E)
    [μ.IsOpenPosMeasure] (U : Set E) (u : E → ℝ) (w : E → ℝ) :
    entryLinfNormOn μ U (fun x => w x • realBlockHessian realDirections imagDirections u x) =
      entryLinfNormOn μ U (fun x => w x • euclideanHessian u x) := by
  have heq : (fun x => Matrix.reindex finSumFinEquiv finSumFinEquiv
      (w x • realBlockHessian realDirections imagDirections u x)) =
      (fun x => w x • euclideanHessian u x) := by
    funext x
    ext i j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.smul_apply,
      realBlockHessian, blockDirection_eq_single, Equiv.apply_symm_apply, euclideanHessian]
  have h := entryLinfNormOn_reindex (μ := μ) finSumFinEquiv finSumFinEquiv U
    (fun x => w x • realBlockHessian realDirections imagDirections u x)
  rw [heq] at h
  exact h.symm

end CHS.Analysis
