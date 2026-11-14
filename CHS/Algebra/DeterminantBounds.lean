import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Determinant estimates used in the convex-section barrier
-/

set_option autoImplicit false

open Matrix Unitary
open scoped BigOperators ComplexOrder MatrixOrder

namespace CHS.Algebra

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem det_one_le_of_posSemidef {A : Matrix ι ι ℂ} (hA : A.PosSemidef) :
    1 ≤ (1 + A).det := by
  let U := hA.isHermitian.eigenvectorUnitary
  let D := diagonal (fun i => (hA.isHermitian.eigenvalues i : ℂ))
  have hA' : A = (conjStarAlgAut ℂ _ U) D := hA.isHermitian.spectral_theorem
  have hD : 1 + A = (conjStarAlgAut ℂ _ U) (1 + D) := by
    rw [map_add, map_one, ← hA']
  have hUnit : (↑U : Matrix ι ι ℂ).det * (star (↑U : Matrix ι ι ℂ)).det = 1 := by
    rw [← det_mul, ← Unitary.coe_star, coe_mul_star_self, det_one]
  rw [hD, conjStarAlgAut_apply, det_mul, det_mul]
  rw [mul_right_comm (↑U : Matrix ι ι ℂ).det, hUnit, one_mul]
  have hdiag : 1 + D = diagonal (fun i => (1 : ℂ) + (hA.isHermitian.eigenvalues i : ℂ)) := by
    change (1 : Matrix ι ι ℂ) + diagonal _ = _
    rw [← diagonal_one]
    exact (diagonal_add (fun _ : ι => (1 : ℂ)) (fun i => (hA.isHermitian.eigenvalues i : ℂ)))
  rw [hdiag, det_diagonal]
  have h : 1 ≤ ∏ i, (1 + hA.isHermitian.eigenvalues i) :=
    Finset.one_le_prod fun i _ => le_add_of_nonneg_right (hA.eigenvalues_nonneg i)
  exact_mod_cast h

theorem det_le_of_posDef_of_posSemidef_sub
    {A B : Matrix ι ι ℂ} (hA : A.PosDef) (hBA : (B - A).PosSemidef) :
    A.det ≤ B.det := by
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
  have hdet : B.det = A.det * (1 + C).det := by
    rw [hB, det_mul, det_mul, ← hSq, det_mul]
    ring
  rw [hdet]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (det_one_le_of_posSemidef hC) hA.det_pos.le

theorem det_smul_one_add_vecMulVec (ε c : ℂ) (hε : ε ≠ 0) (v : ι → ℂ) :
    (ε • (1 : Matrix ι ι ℂ) + c • vecMulVec v (star v)).det =
      ε ^ Fintype.card ι * (1 + (c / ε) * (star v ⬝ᵥ v)) := by
  let w := (c / ε) • v
  have hscale : ε • (1 + vecMulVec w (star v)) =
      ε • (1 : Matrix ι ι ℂ) + c • vecMulVec v (star v) := by
    rw [smul_add]
    dsimp only [w]
    rw [smul_vecMulVec, smul_smul]
    congr 2
    field_simp
  rw [← hscale, det_smul]
  have h := det_one_add_replicateCol_mul_replicateRow (ι := Unit) w (star v)
  have hvec : replicateCol Unit w * replicateRow Unit (star v) = vecMulVec w (star v) := by
    ext i j
    simp [Matrix.mul_apply, vecMulVec_apply]
  rw [hvec] at h
  rw [h]
  simp [w, dotProduct_smul]


/-- The determinant of the barrier Hessian is strictly greater than one
under the section normalization. -/
theorem section_barrier_det_gt_one
    {n : ℕ} (hn : 0 < n) {Q : Matrix (Fin n) (Fin n) ℂ}
    (hQ : (Q - 1).PosSemidef) (v : Fin n → ℂ) (hv : (∑ i, ‖v i‖ ^ 2) = 1 / 4)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hscale : δ ^ 2 = ε ^ (n - 1) / 2) :
    1 < (((ε : ℂ) • Q) + ((2 / δ ^ 2 : ℝ) : ℂ) • vecMulVec v (star v)).det := by
  let c := 2 / δ ^ 2
  let R := vecMulVec v (star v)
  let A : Matrix (Fin n) (Fin n) ℂ := (ε : ℂ) • 1 + (c : ℂ) • R
  let B : Matrix (Fin n) (Fin n) ℂ := (ε : ℂ) • Q + (c : ℂ) • R
  have hA : A.PosDef := by
    change ((ε • (1 : Matrix (Fin n) (Fin n) ℂ)) + c • R).PosDef
    exact (Matrix.PosDef.one.smul hε).add_posSemidef
      ((posSemidef_vecMulVec_self_star v).smul (show 0 ≤ c by dsimp [c]; positivity))
  have hBA : (B - A).PosSemidef := by
    have heq : B - A = ε • (Q - 1) := by
      change ((ε • Q) + c • R) - (ε • (1 : Matrix (Fin n) (Fin n) ℂ) + c • R) =
        ε • (Q - 1)
      rw [smul_sub]
      abel
    rw [heq]
    exact hQ.smul hε.le
  have hvdot : star v ⬝ᵥ v = ((1 / 4 : ℝ) : ℂ) := by
    calc
      _ = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
        simp only [dotProduct, Complex.ofReal_sum, Pi.star_apply]
        apply Finset.sum_congr rfl
        intro i _
        rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.sq_norm]
      _ = _ := by rw [hv]
  have hdet : A.det = ((ε ^ n + 1 : ℝ) : ℂ) := by
    change ((ε : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + (c : ℂ) • R).det = _
    rw [det_smul_one_add_vecMulVec _ _ (Complex.ofReal_ne_zero.mpr hε.ne') v, hvdot,
      Fintype.card_fin]
    have hn' : n = (n - 1) + 1 := by omega
    have hpow : ε ^ n = ε ^ (n - 1) * ε := by
      calc
        _ = ε ^ ((n - 1) + 1) := congrArg (fun k : ℕ => ε ^ k) hn'
        _ = _ := pow_succ ε _
    push_cast
    have hscale' : (ε : ℂ) ^ (n - 1) = 2 * (δ : ℂ) ^ 2 := by
      exact_mod_cast (show ε ^ (n - 1) = 2 * δ ^ 2 by linarith)
    rw [show (ε : ℂ) ^ n = (ε : ℂ) ^ (n - 1) * (ε : ℂ) by exact_mod_cast hpow, hscale']
    have hδ' : (δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hδ.ne'
    have hε' : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hε.ne'
    simp only [c, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_ofNat]
    field_simp
    <;> ring
  have hpos : (1 : ℂ) < A.det := by
    rw [hdet]
    exact_mod_cast (show (1 : ℝ) < ε ^ n + 1 by have := pow_pos hε n; linarith)
  exact hpos.trans_le (det_le_of_posDef_of_posSemidef_sub hA hBA)

end CHS.Algebra
