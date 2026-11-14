import CHS.Algebra.DeterminantBounds

/-! # Strict determinant monotonicity on the positive Hermitian cone -/

set_option autoImplicit false
noncomputable section

open Matrix Unitary
open scoped BigOperators ComplexOrder MatrixOrder

namespace CHS.Algebra

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem eq_zero_of_posSemidef_det_one_add_eq_one
    {A : Matrix ι ι ℂ} (hA : A.PosSemidef) (hdet : (1 + A).det = 1) : A = 0 := by
  let U := hA.isHermitian.eigenvectorUnitary
  let D := diagonal (fun i => (hA.isHermitian.eigenvalues i : ℂ))
  have hA' : A = (conjStarAlgAut ℂ _ U) D := hA.isHermitian.spectral_theorem
  have hD : 1 + A = (conjStarAlgAut ℂ _ U) (1 + D) := by rw [map_add, map_one, ← hA']
  have hUnit : (↑U : Matrix ι ι ℂ).det * (star (↑U : Matrix ι ι ℂ)).det = 1 := by
    rw [← det_mul, ← Unitary.coe_star, coe_mul_star_self, det_one]
  rw [hD, conjStarAlgAut_apply, det_mul, det_mul,
    mul_right_comm (↑U : Matrix ι ι ℂ).det, hUnit, one_mul] at hdet
  have hdiag : 1 + D = diagonal (fun i => (1 : ℂ) + (hA.isHermitian.eigenvalues i : ℂ)) := by
    change (1 : Matrix ι ι ℂ) + diagonal _ = _
    rw [← diagonal_one]
    exact diagonal_add _ _
  rw [hdiag, det_diagonal] at hdet
  have hprod : (∏ i, (1 + hA.isHermitian.eigenvalues i)) = (1 : ℝ) := by
    exact_mod_cast hdet
  apply hA.isHermitian.eigenvalues_eq_zero_iff.mp
  funext i
  change hA.isHermitian.eigenvalues i = 0
  have hrest : 1 ≤ ∏ j ∈ Finset.univ.erase i, (1 + hA.isHermitian.eigenvalues j) :=
    Finset.one_le_prod fun j _ => le_add_of_nonneg_right (hA.eigenvalues_nonneg j)
  have hfactor : (1 + hA.isHermitian.eigenvalues i) *
      (∏ j ∈ Finset.univ.erase i, (1 + hA.isHermitian.eigenvalues j)) = 1 := by
    exact (Finset.mul_prod_erase Finset.univ
      (fun j => 1 + hA.isHermitian.eigenvalues j) (Finset.mem_univ i)).trans hprod
  nlinarith [hA.eigenvalues_nonneg i,
    mul_nonneg (hA.eigenvalues_nonneg i) (sub_nonneg.mpr hrest)]

theorem eq_of_posDef_of_posSemidef_sub_of_det_eq
    {A B : Matrix ι ι ℂ} (hA : A.PosDef) (hBA : (B - A).PosSemidef)
    (hdet : B.det = A.det) : B = A := by
  let S := CFC.sqrt A
  have hS : S.PosSemidef := (CFC.sqrt_nonneg A).posSemidef
  have hSq : S * S = A := by simpa only [pow_two] using CFC.sq_sqrt A hA.posSemidef.nonneg
  have hAunit : IsUnit A.det := (isUnit_iff_isUnit_det _).mp hA.isUnit
  have hSunit : IsUnit S.det := by
    have h := hAunit
    rw [← hSq, det_mul] at h
    exact isUnit_of_mul_isUnit_left h
  let C := S⁻¹ * (B - A) * S⁻¹
  have hC : C.PosSemidef := by
    have h := hBA.conjTranspose_mul_mul_same (S⁻¹)
    rw [hS.isHermitian.inv.eq] at h
    exact h
  have hB : B = S * (1 + C) * S := by
    dsimp only [C]
    rw [Matrix.mul_add, Matrix.mul_one, add_mul, hSq]
    have h : S * (S⁻¹ * (B - A) * S⁻¹) * S = B - A := by
      rw [← Matrix.mul_assoc S (S⁻¹ * (B - A)) S⁻¹,
        ← Matrix.mul_assoc S S⁻¹ (B - A), Matrix.mul_nonsing_inv _ hSunit,
        Matrix.one_mul, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hSunit, Matrix.mul_one]
    rw [h]
    abel
  have hfactor : B.det = A.det * (1 + C).det := by
    rw [hB, det_mul, det_mul, ← hSq, det_mul]
    ring
  have hdetC : (1 + C).det = 1 := by
    apply mul_left_cancel₀ hAunit.ne_zero
    rw [← hfactor, mul_one]
    exact hdet
  have hCzero := eq_zero_of_posSemidef_det_one_add_eq_one hC hdetC
  rw [hB, hCzero, add_zero, Matrix.mul_one, hSq]

end CHS.Algebra
