import CHS.Algebra.TraceFree
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Matrix.Normed

/-!
# Uniform inverse bounds at determinant of modulus one

The finite-dimensional compactness proof below is an alternative to
explicit singular-value estimates in (3.9).  The resulting constant
depends only on the matrix size and the given entry bound.
-/

set_option autoImplicit false
noncomputable section

open Set Metric
open scoped BigOperators Matrix.Norms.Elementwise

namespace CHS.Algebra

variable {n : ℕ}

theorem exists_uniform_inverse_entry_bound (n : ℕ) (R : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ G : Matrix (Fin n) (Fin n) ℂ,
      Complex.normSq G.det = 1 → (∀ i j, ‖G i j‖ ≤ R) →
      ∀ i j, ‖G⁻¹ i j‖ ≤ B := by
  let S : Set (Matrix (Fin n) (Fin n) ℂ) :=
    closedBall 0 (max 0 R) ∩ {G | Complex.normSq G.det = 1}
  have hclosed : IsClosed {G : Matrix (Fin n) (Fin n) ℂ | Complex.normSq G.det = 1} :=
    isClosed_eq (Complex.continuous_normSq.comp continuous_id.matrix_det) continuous_const
  have hS : IsCompact S := (isCompact_closedBall 0 (max 0 R)).inter_right hclosed
  have hInv : ContinuousOn (fun G : Matrix (Fin n) (Fin n) ℂ => G⁻¹) S := by
    intro G hG
    have hdet : G.det ≠ 0 := by
      intro hz
      have hg : Complex.normSq G.det = 1 := hG.2
      rw [hz] at hg
      norm_num at hg
    apply (continuousAt_matrix_inv G _).continuousWithinAt
    simpa only [Ring.inverse_eq_inv'] using (continuousAt_inv₀ hdet)
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.mp (hS.image_of_continuousOn hInv).isBounded
  refine ⟨max 0 B, le_max_left _ _, ?_⟩
  intro G hdet hbound i j
  have hnorm : ‖G‖ ≤ max 0 R := (Matrix.norm_le_iff (le_max_left 0 R)).mpr
    (fun k l => (hbound k l).trans (le_max_right _ _))
  have hGS : G ∈ S := ⟨by simpa only [mem_closedBall, dist_zero_right] using hnorm, hdet⟩
  exact (Matrix.norm_entry_le_entrywise_sup_norm (G⁻¹ : Matrix (Fin n) (Fin n) ℂ)
    (i := i) (j := j)).trans
    ((hB _ (mem_image_of_mem (fun G : Matrix (Fin n) (Fin n) ℂ => G⁻¹) hGS)).trans
      (le_max_right _ _))

theorem hsSq_le_of_entry_norm_bound
    {G : Matrix (Fin n) (Fin n) ℂ} {R : ℝ} (hR : 0 ≤ R) (hG : ∀ i j, ‖G i j‖ ≤ R) :
    hsSq G ≤ (n : ℝ) ^ 2 * R ^ 2 := by
  calc
    hsSq G ≤ ∑ _i : Fin n, ∑ _j : Fin n, R ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [Complex.normSq_eq_norm_sq]
      exact pow_le_pow_left₀ (norm_nonneg _) (hG i j) 2
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

theorem norm_entry_le_sqrt_hsSq (G : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    ‖G i j‖ ≤ Real.sqrt (hsSq G) := by
  apply (Real.le_sqrt (norm_nonneg _) (hsSq_nonneg G)).mpr
  rw [← Complex.normSq_eq_norm_sq]
  exact (Finset.single_le_sum (fun k _ => Complex.normSq_nonneg (G i k)) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun l _ => Complex.normSq_nonneg (G k l))
      (Finset.mem_univ i))

theorem exists_uniform_hs_inverse_bound (n : ℕ) (R : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ G : Matrix (Fin n) (Fin n) ℂ,
      Complex.normSq G.det = 1 → hsSq G ≤ R → hsSq G⁻¹ ≤ B := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_inverse_entry_bound n (Real.sqrt R)
  refine ⟨(n : ℝ) ^ 2 * C ^ 2, by positivity, ?_⟩
  intro G hdet hG
  apply hsSq_le_of_entry_norm_bound hC
  apply hbound G hdet
  intro i j
  exact (norm_entry_le_sqrt_hsSq G i j).trans (Real.sqrt_le_sqrt hG)

end CHS.Algebra
