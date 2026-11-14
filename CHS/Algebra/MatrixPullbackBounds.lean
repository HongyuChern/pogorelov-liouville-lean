import CHS.Algebra.HessianEntryBounds
import CHS.Pogorelov.UnitaryTrace

/-! # Entry and trace bounds after undoing a complex congruence -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators ComplexOrder

namespace CHS.Algebra

open CHS.Pogorelov

variable {n : ℕ}

theorem matrix_mul_entry_norm_bound
    {A B : Matrix (Fin n) (Fin n) ℂ} {R S : ℝ} (hR : 0 ≤ R)
    (hA : ∀ i j, ‖A i j‖ ≤ R) (hB : ∀ i j, ‖B i j‖ ≤ S) (i j : Fin n) :
    ‖(A * B) i j‖ ≤ (n : ℝ) * R * S := by
  rw [Matrix.mul_apply]
  calc
    _ ≤ ∑ k, ‖A i k * B k j‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin n, R * S := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul]
      exact mul_le_mul (hA i k) (hB k j) (norm_nonneg _) hR
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

theorem undo_complex_congruence
    (A G : Matrix (Fin n) (Fin n) ℂ) (hG : IsUnit G.det) :
    (G⁻¹).transpose * (G.transpose * A * G.map star) * (G⁻¹).map star = A := by
  have hl : (G⁻¹).transpose * G.transpose = 1 := by
    rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hG, Matrix.transpose_one]
  have hr : G.map star * (G⁻¹).map star = 1 := by
    rw [← matrix_conjugate_mul, Matrix.mul_nonsing_inv _ hG, matrix_conjugate_one]
  calc
    _ = ((G⁻¹).transpose * G.transpose) * A * (G.map star * (G⁻¹).map star) := by noncomm_ring
    _ = A := by rw [hl, hr, Matrix.one_mul, Matrix.mul_one]

theorem complex_congruence_entry_bound
    {A G : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosSemidef) (hG : IsUnit G.det)
    {B R : ℝ} (hB : 0 ≤ B) (hR : 0 ≤ R)
    (hInv : ∀ i j, ‖G⁻¹ i j‖ ≤ B)
    (htrace : (G.transpose * A * G.map star).trace.re ≤ R) :
    ∀ i j, ‖A i j‖ ≤ (n : ℝ) ^ 2 * B ^ 2 * R := by
  let H := G.transpose * A * G.map star
  have hH : H.PosSemidef := by
    have hh := hA.conjTranspose_mul_mul_same (G.map star)
    simpa only [matrix_adjoint_conjugate] using hh
  have hHB (i j : Fin n) : ‖H i j‖ ≤ R := (norm_entry_le_trace_re hH i j).trans htrace
  have hleft (i j : Fin n) : ‖(G⁻¹).transpose i j‖ ≤ B := hInv j i
  have hright (i j : Fin n) : ‖(G⁻¹).map star i j‖ ≤ B := by
    simpa only [Matrix.map_apply, norm_star] using hInv i j
  have hfirst := matrix_mul_entry_norm_bound hB hleft hHB
  intro i j
  have hlast := matrix_mul_entry_norm_bound
    (show 0 ≤ (n : ℝ) * B * R by positivity) hfirst hright i j
  rw [undo_complex_congruence A G hG] at hlast
  convert hlast using 1 <;> ring

theorem complex_congruence_trace_bound
    {A G : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosSemidef) (hG : IsUnit G.det)
    {B R : ℝ} (hB : 0 ≤ B) (hR : 0 ≤ R)
    (hInv : ∀ i j, ‖G⁻¹ i j‖ ≤ B)
    (htrace : (G.transpose * A * G.map star).trace.re ≤ R) :
    A.trace.re ≤ (n : ℝ) ^ 3 * B ^ 2 * R := by
  have hb := complex_congruence_entry_bound hA hG hB hR hInv htrace
  rw [Matrix.trace, Complex.re_sum]
  calc
    _ ≤ ∑ _i : Fin n, (n : ℝ) ^ 2 * B ^ 2 * R := by
      apply Finset.sum_le_sum
      intro i _
      exact (Complex.re_le_norm _).trans (hb i i)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end CHS.Algebra
