import CHS.CoreImports
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# The radius implication of a John contact decomposition

For a contact certificate with total mass d, center balance, and identity
second moment, every point satisfying its supporting inequalities has
norm at most d.  This proves the numerical outer-radius implication of
John's argument.  Existence of the certificate is not assumed proved.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators RealInnerProductSpace

namespace CHS.Sections

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]

theorem john_contact_radius_bound
    (v : ι → E) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hunit : ∀ i, ‖v i‖ = 1) {d : ℝ} (hmass : ∑ i, c i = d)
    (hbalance : ∑ i, c i • v i = 0)
    (hframe : ∀ x : E, ∑ i, c i * ⟪v i, x⟫ ^ 2 = ‖x‖ ^ 2)
    (x : E) (hsupport : ∀ i, ⟪v i, x⟫ ≤ 1) : ‖x‖ ≤ d := by
  have hd : 0 ≤ d := hmass ▸ Finset.sum_nonneg (fun i _ => hc i)
  have hzero : ∑ i, c i * ⟪v i, x⟫ = 0 := by
    have hh := congrArg (fun y : E => ⟪y, x⟫) hbalance
    simpa only [sum_inner, real_inner_smul_left, inner_zero_left] using hh
  have hbound (i : ι) : ⟪v i, x⟫ ^ 2 ≤ (1 - ‖x‖) * ⟪v i, x⟫ + ‖x‖ := by
    have hi := abs_real_inner_le_norm (v i) x
    rw [hunit i, one_mul] at hi
    have hlo := (abs_le.mp hi).1
    have hp := mul_nonneg (sub_nonneg.mpr (hsupport i)) (show 0 ≤ ⟪v i, x⟫ + ‖x‖ by linarith)
    nlinarith
  have hnorm : ‖x‖ ^ 2 ≤ d * ‖x‖ := by
    calc
      ‖x‖ ^ 2 = ∑ i, c i * ⟪v i, x⟫ ^ 2 := (hframe x).symm
      _ ≤ ∑ i, c i * ((1 - ‖x‖) * ⟪v i, x⟫ + ‖x‖) :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hbound i) (hc i))
      _ = (1 - ‖x‖) * (∑ i, c i * ⟪v i, x⟫) + (∑ i, c i) * ‖x‖ := by
        rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = d * ‖x‖ := by rw [hzero, hmass, mul_zero, zero_add]
  by_cases hz : ‖x‖ = 0
  · simpa only [hz] using hd
  · have hp : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm hz)
    nlinarith

end CHS.Sections
