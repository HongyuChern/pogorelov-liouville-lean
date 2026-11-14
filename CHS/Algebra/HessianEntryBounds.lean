import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Entry estimates with the manuscript's Schur constant

The resulting bounds are for individual matrix entries.  They do not
replace the manuscript's maximum-entry seminorm by an operator norm.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder

namespace CHS.Algebra

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem norm_entry_sq_le_diag_mul_diag {A : Matrix ι ι ℂ}
    (hA : A.PosSemidef) (i j : ι) :
    ‖A i j‖ ^ 2 ≤ (A i i).re * (A j j).re := by
  letI := Matrix.toSeminormedAddCommGroup A hA
  letI := Matrix.toInnerProductSpace A hA
  let ei : ι → ℂ := Pi.single i 1
  let ej : ι → ℂ := Pi.single j 1
  have h := inner_mul_inner_self_le (𝕜 := ℂ) ei ej
  change ‖(A *ᵥ Pi.single j 1) ⬝ᵥ star (Pi.single i 1)‖ *
      ‖(A *ᵥ Pi.single i 1) ⬝ᵥ star (Pi.single j 1)‖ ≤
    ((A *ᵥ Pi.single i 1) ⬝ᵥ star (Pi.single i 1)).re *
      ((A *ᵥ Pi.single j 1) ⬝ᵥ star (Pi.single j 1)).re at h
  have heq : ‖A j i‖ = ‖A i j‖ := by
    simpa only [norm_star] using congrArg norm (hA.isHermitian.apply i j)
  have hsingle (k l : ι) :
      (A *ᵥ Pi.single l 1) ⬝ᵥ star (Pi.single k 1) = A k l := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, Pi.star_apply]
  simpa only [hsingle, heq, ← pow_two] using h

theorem diag_re_le_trace_re {A : Matrix ι ι ℂ} (hA : A.PosSemidef) (i : ι) :
    (A i i).re ≤ A.trace.re := by
  rw [Matrix.trace, Complex.re_sum]
  exact Finset.single_le_sum
    (fun j _ => (Complex.nonneg_iff.mp (hA.diag_nonneg (i := j))).1)
    (Finset.mem_univ i)

theorem norm_entry_le_trace_re {A : Matrix ι ι ℂ} (hA : A.PosSemidef) (i j : ι) :
    ‖A i j‖ ≤ A.trace.re := by
  have hi := diag_re_le_trace_re hA i
  have hj := diag_re_le_trace_re hA j
  have hi0 := (Complex.nonneg_iff.mp (hA.diag_nonneg (i := i))).1
  have hj0 := (Complex.nonneg_iff.mp (hA.diag_nonneg (i := j))).1
  have ht := (Complex.nonneg_iff.mp hA.trace_nonneg).1
  have hprod := mul_le_mul hi hj hj0 ht
  have hsq := norm_entry_sq_le_diag_mul_diag hA i j
  nlinarith [norm_nonneg (A i j)]

/-- The block Schur criterion gives the exact `sqrt κ` entry factor. -/
theorem norm_offdiag_le_sqrt_mul_trace {A B : Matrix ι ι ℂ}
    (hA : A.PosDef) (hB : B.conjTranspose = B.map star) {κ : ℝ} (hκ : 0 ≤ κ)
    (hbound : (κ • A - B * (A.map star)⁻¹ * B.map star).PosSemidef)
    (i j : ι) : ‖B i j‖ ≤ Real.sqrt κ * A.trace.re := by
  have hbar : A.map star = A.transpose := by
    ext k l
    exact hA.isHermitian.apply l k
  have hbarpos : (A.map star).PosDef := hbar ▸ hA.transpose
  letI : Invertible (A.map star) :=
    Matrix.invertibleOfIsUnitDet _ ((Matrix.isUnit_iff_isUnit_det _).mp hbarpos.isUnit)
  have hblock : (Matrix.fromBlocks (κ • A) B B.conjTranspose (A.map star)).PosSemidef := by
    apply (Matrix.PosDef.fromBlocks₂₂ (κ • A) B hbarpos).mpr
    simpa only [hB] using hbound
  have hs := norm_entry_sq_le_diag_mul_diag hblock (Sum.inl i) (Sum.inr j)
  have hi := diag_re_le_trace_re hA.posSemidef i
  have hj := diag_re_le_trace_re hA.posSemidef j
  have hi0 := (Complex.nonneg_iff.mp (hA.posSemidef.diag_nonneg (i := i))).1
  have hj0 := (Complex.nonneg_iff.mp (hA.posSemidef.diag_nonneg (i := j))).1
  have ht := (Complex.nonneg_iff.mp hA.posSemidef.trace_nonneg).1
  have hprod := mul_le_mul hi hj hj0 ht
  have hprodκ := mul_le_mul_of_nonneg_left hprod hκ
  have hsqrt := Real.sq_sqrt hκ
  have hsqrt0 := Real.sqrt_nonneg κ
  simp only [fromBlocks_apply₁₂, fromBlocks_apply₁₁, fromBlocks_apply₂₂,
    Matrix.smul_apply, Matrix.map_apply, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.star_def, Complex.conj_re] at hs
  nlinarith [norm_nonneg (B i j), mul_nonneg hsqrt0 ht]

end CHS.Algebra
