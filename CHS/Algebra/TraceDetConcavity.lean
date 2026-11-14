import CHS.Algebra.DeterminantRigidity
import CHS.Calculus.DirectionalHessian
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The supporting-plane inequality on a determinant level set

For positive Hermitian A and B with equal determinant,
Re tr(A⁻¹(B-A)) is nonnegative. The proof is the scalar inequality
log t <= t-1 applied to the eigenvalues of A⁻¹/² B A⁻¹/².
The strict zero-pairing lemma is also used to select finitely many
real directions for the local oscillation argument.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

namespace CHS.Algebra

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem card_le_trace_re_of_posDef_det_one {A : Matrix ι ι ℂ}
    (hA : A.PosDef) (hdet : A.det = 1) :
    (Fintype.card ι : ℝ) ≤ A.trace.re := by
  have hprod : (∏ i, hA.isHermitian.eigenvalues i) = (1 : ℝ) := by
    have h := hA.isHermitian.det_eq_prod_eigenvalues.symm.trans hdet
    simp only [RCLike.ofReal_eq_complex_ofReal] at h
    exact_mod_cast h
  have hlogs : (∑ i, Real.log (hA.isHermitian.eigenvalues i)) = 0 := by
    rw [← Real.log_prod (fun i _ => (hA.eigenvalues_pos i).ne'), hprod, Real.log_one]
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => Real.log_le_sub_one_of_pos (hA.eigenvalues_pos i))
  rw [hlogs, Finset.sum_sub_distrib] at hsum
  rw [hA.isHermitian.trace_eq_sum_eigenvalues, Complex.re_sum]
  simpa only [RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_re, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one]
    using (sub_nonneg.mp hsum)

theorem trace_inv_mul_sub_nonneg_of_det_eq {A B : Matrix ι ι ℂ}
    (hA : A.PosDef) (hB : B.PosDef) (hdet : B.det = A.det) :
    0 ≤ (A⁻¹ * (B - A)).trace.re := by
  let S := CFC.sqrt A⁻¹
  have hS : S.PosSemidef := (CFC.sqrt_nonneg A⁻¹).posSemidef
  have hSq : S * S = A⁻¹ := by
    simpa only [pow_two] using CFC.sq_sqrt A⁻¹ hA.inv.posSemidef.nonneg
  have hAunit : IsUnit A.det := (isUnit_iff_isUnit_det _).mp hA.isUnit
  have hSunit : IsUnit S.det := by
    have h := (isUnit_iff_isUnit_det _).mp hA.inv.isUnit
    rw [← hSq, det_mul] at h
    exact isUnit_of_mul_isUnit_left h
  let C := S * B * S
  have hC : C.PosDef := by
    have h := hB.conjTranspose_mul_mul_same
      (Matrix.mulVec_injective_of_isUnit ((isUnit_iff_isUnit_det _).mpr hSunit))
    rw [hS.isHermitian.eq] at h
    exact h
  have hCdet : C.det = 1 := by
    calc
      C.det = (S * S).det * B.det := by dsimp [C]; simp only [det_mul]; ring
      _ = A⁻¹.det * A.det := by rw [hSq, hdet]
      _ = 1 := Matrix.det_nonsing_inv_mul_det _ hAunit
  have ht : C.trace = (A⁻¹ * B).trace := by
    dsimp only [C]
    rw [trace_mul_cycle, hSq]
  have hle := card_le_trace_re_of_posDef_det_one hC hCdet
  rw [ht] at hle
  rw [Matrix.mul_sub, Matrix.nonsing_inv_mul _ hAunit, Matrix.trace_sub,
    Complex.sub_re, Matrix.trace_one]
  simpa only [Complex.natCast_re] using sub_nonneg.mpr hle

theorem eq_zero_of_posDef_trace_product_re_zero {W P : Matrix ι ι ℂ}
    (hW : W.PosDef) (hP : P.PosSemidef) (htrace : (W * P).trace.re = 0) : P = 0 := by
  let S := CFC.sqrt W
  have hS : S.PosSemidef := (CFC.sqrt_nonneg W).posSemidef
  have hSq : S * S = W := by simpa only [pow_two] using CFC.sq_sqrt W hW.posSemidef.nonneg
  have hSunit : IsUnit S.det := by
    have h := (isUnit_iff_isUnit_det _).mp hW.isUnit
    rw [← hSq, det_mul] at h
    exact isUnit_of_mul_isUnit_left h
  have hQ : (S * P * S).PosSemidef := by
    have h := hP.conjTranspose_mul_mul_same S
    rwa [hS.isHermitian.eq] at h
  have hQre : (S * P * S).trace.re = 0 := by
    rw [trace_mul_cycle, hSq]
    exact htrace
  have hQzero : S * P * S = 0 := hQ.trace_eq_zero_iff.mp
    (Complex.ext hQre (Complex.nonneg_iff.mp hQ.trace_nonneg).2.symm)
  have h := congrArg (fun Q => S⁻¹ * Q) hQzero
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hSunit,
    Matrix.one_mul, Matrix.mul_zero] at h
  have h' := congrArg (fun Q => Q * S⁻¹) h
  rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hSunit, Matrix.mul_one, Matrix.zero_mul] at h'
  exact h'

end CHS.Algebra
