import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-!
# The actual weighted matrix square and its zero case

S004 reimplementation of one missing S002 dependency. This is not a recovered
copy of that missing file. It proves the precise `matrixSquare_pairing_zero`
interface used by the preserved `SchurHessianLM.lean`, using the positive
Kronecker form `transpose W ⊗ H`. The transpose is essential: the coefficient
in the paper is `W q p`, not `W p q`.

No PDE identity or kernel constancy is assumed here. The only hypotheses are
positive definiteness of the two weight matrices and an actual scalar zero.
All statements in this file remain uncompiled candidates in this environment.
-/

set_option autoImplicit false
open scoped BigOperators Matrix Kronecker ComplexOrder

namespace CHS.WeightedSquares

variable {ι ρ ν : Type*}
variable [Fintype ι] [Fintype ρ] [Fintype ν]
variable [DecidableEq ι] [DecidableEq ρ] [DecidableEq ν]

/-- The square appearing with a minus sign in the Schur-field identity. -/
noncomputable def matrixSquare (W : Matrix ι ι ℂ) (H : Matrix ν ν ℂ)
    (B : ι → Matrix ρ ν ℂ) : Matrix ρ ρ ℂ :=
  ∑ p, ∑ q, W q p • (B p * H * (B q).conjTranspose)

/-- Moving a matrix through the complex bilinear dot product explicitly
introduces its conjugate transpose. -/
lemma pairing_product (P Q : Matrix ρ ν ℂ) (H : Matrix ν ν ℂ) (ξ : ρ → ℂ) :
    star ξ ⬝ᵥ (P * H * Q.conjTranspose).mulVec ξ =
      star (P.conjTranspose.mulVec ξ) ⬝ᵥ
        H.mulVec (Q.conjTranspose.mulVec ξ) := by
  simp only [← Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_mulVec, Matrix.star_mulVec,
    Matrix.conjTranspose_conjTranspose]

lemma matrixSquare_pairing_sum (W : Matrix ι ι ℂ) (H : Matrix ν ν ℂ)
    (B : ι → Matrix ρ ν ℂ) (ξ : ρ → ℂ) :
    star ξ ⬝ᵥ (matrixSquare W H B).mulVec ξ =
      ∑ p, ∑ q, W q p * (star ((B p).conjTranspose.mulVec ξ) ⬝ᵥ
        H.mulVec ((B q).conjTranspose.mulVec ξ)) := by
  simp only [matrixSquare, Matrix.sum_mulVec, dotProduct_sum,
    Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, pairing_product]

lemma kronecker_pairing (W : Matrix ι ι ℂ) (H : Matrix ν ν ℂ)
    (v : ι × ν → ℂ) :
    star v ⬝ᵥ (W.transpose ⊗ₖ H).mulVec v =
      ∑ p, ∑ q, W q p * (star (fun r => v (p, r)) ⬝ᵥ
        H.mulVec (fun s => v (q, s))) := by
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type,
    Matrix.kronecker_apply, Matrix.transpose_apply, Pi.star_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- The tensor-product quadratic form is built from the actual adjoint
vectors, not from independently supplied square-root factors. -/
lemma matrixSquare_pairing_kronecker (W : Matrix ι ι ℂ) (H : Matrix ν ν ℂ)
    (B : ι → Matrix ρ ν ℂ) (ξ : ρ → ℂ) :
    star ξ ⬝ᵥ (matrixSquare W H B).mulVec ξ =
      star (fun t : ι × ν => (B t.1).conjTranspose.mulVec ξ t.2) ⬝ᵥ
        (W.transpose ⊗ₖ H).mulVec
          (fun t : ι × ν => (B t.1).conjTranspose.mulVec ξ t.2) := by
  rw [matrixSquare_pairing_sum, kronecker_pairing]

lemma matrixSquare_pairing_nonneg (W : Matrix ι ι ℂ) (H : Matrix ν ν ℂ)
    (hW : W.PosSemidef) (hH : H.PosSemidef)
    (B : ι → Matrix ρ ν ℂ) (ξ : ρ → ℂ) :
    0 ≤ (star ξ ⬝ᵥ (matrixSquare W H B).mulVec ξ).re := by
  rw [matrixSquare_pairing_kronecker]
  exact (hW.transpose.kronecker hH).re_dotProduct_nonneg _

theorem matrixSquare_posSemidef (W : Matrix ι ι ℂ) (H : Matrix ν ν ℂ)
    (hW : W.PosSemidef) (hH : H.PosSemidef) (B : ι → Matrix ρ ν ℂ) :
    (matrixSquare W H B).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · change (matrixSquare W H B).conjTranspose = _
    simp only [matrixSquare, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hH.isHermitian.eq]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    rw [hW.isHermitian.apply q p]
    exact congrArg (fun M : Matrix ρ ρ ℂ => W q p • M)
      (Matrix.mul_assoc (B p) H (B q).conjTranspose).symm
  · intro ξ
    rw [matrixSquare_pairing_kronecker]
    exact (hW.transpose.kronecker hH).dotProduct_mulVec_nonneg _

/-- Exact interface required by the preserved S002 `SchurHessianLM.lean`.
The zero-vector conclusion uses strict positivity of both actual weights. -/
theorem matrixSquare_pairing_zero (W : Matrix ι ι ℂ) (H : Matrix ν ν ℂ)
    (hW : W.PosDef) (hH : H.PosDef)
    (B : ι → Matrix ρ ν ℂ) (ξ : ρ → ℂ)
    (hzero : star ξ ⬝ᵥ (matrixSquare W H B).mulVec ξ = 0) :
    ∀ p, (B p).conjTranspose.mulVec ξ = 0 := by
  let v : ι × ν → ℂ := fun t => (B t.1).conjTranspose.mulVec ξ t.2
  have hvzero : star v ⬝ᵥ (W.transpose ⊗ₖ H).mulVec v = 0 := by
    rw [← matrixSquare_pairing_kronecker W H B ξ]
    exact hzero
  have hv : v = 0 := by
    by_contra hne
    have hpos := (hW.transpose.kronecker hH).re_dotProduct_pos hne
    rw [hvzero] at hpos
    norm_num at hpos
  intro p
  funext r
  simpa only [v, Pi.zero_apply] using congrFun hv (p, r)

lemma matrixSquare_pairing_zero_iff (W : Matrix ι ι ℂ) (H : Matrix ν ν ℂ)
    (hW : W.PosDef) (hH : H.PosDef)
    (B : ι → Matrix ρ ν ℂ) (ξ : ρ → ℂ) :
    star ξ ⬝ᵥ (matrixSquare W H B).mulVec ξ = 0 ↔
      ∀ p, (B p).conjTranspose.mulVec ξ = 0 := by
  constructor
  · exact matrixSquare_pairing_zero W H hW hH B ξ
  · intro h
    rw [matrixSquare_pairing_sum]
    simp only [h, Matrix.mulVec_zero, dotProduct_zero,
      mul_zero, Finset.sum_const_zero]

end CHS.WeightedSquares
