import CHS.Analysis.FiniteOscillation
import Mathlib.Algebra.Order.Archimedean.Basic

/-! # Scalar geometric iteration and its exact eighth-scale power bound -/

set_option autoImplicit false
noncomputable section

namespace CHS.Analysis

theorem exists_exponent_for_eighth_decay {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) :
    ∃ α : ℝ, 0 < α ∧ α < 1 ∧ θ ≤ (1 / 8 : ℝ) ^ α := by
  let α : ℝ := (1 - θ) / 8
  have hα : 0 < α := by dsimp [α]; positivity
  have hα1 : α < 1 := by dsimp [α]; linarith
  refine ⟨α, hα, hα1, ?_⟩
  have hlog : Real.log (8 : ℝ) ≤ 7 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : 0 < (8 : ℝ))]
  calc
    θ = 1 - 8 * α := by dsimp [α]; ring
    _ ≤ Real.exp (-(8 * α)) := by linarith [Real.add_one_le_exp (-(8 * α))]
    _ ≤ Real.exp (-(Real.log 8) * α) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    _ = (1 / 8 : ℝ) ^ α := by
      rw [Real.rpow_def_of_pos (by norm_num : 0 < (1 / 8 : ℝ)),
        show (1 / 8 : ℝ) = (8 : ℝ)⁻¹ by norm_num, Real.log_inv]

theorem eighth_radius_contraction_iterate {F : ℝ → ℝ} {θ R : ℝ}
    (hθ : 0 ≤ θ) (hR : 0 < R)
    (hstep : ∀ r : ℝ, 0 < r → r ≤ R → F (r / 8) ≤ θ * F r) :
    ∀ k : ℕ, F (R * (1 / 8 : ℝ) ^ k) ≤ θ ^ k * F R := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have hr : 0 < R * (1 / 8 : ℝ) ^ k := by positivity
    have hrR : R * (1 / 8 : ℝ) ^ k ≤ R := by
      exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (by norm_num) (by norm_num) :
        (1 / 8 : ℝ) ^ k ≤ 1) hR.le).trans_eq (mul_one R)
    calc
      F (R * (1 / 8 : ℝ) ^ (k + 1)) = F ((R * (1 / 8 : ℝ) ^ k) / 8) := by
        congr 1
        rw [pow_succ]
        ring
      _ ≤ θ * F (R * (1 / 8 : ℝ) ^ k) := hstep _ hr hrR
      _ ≤ θ * (θ ^ k * F R) := mul_le_mul_of_nonneg_left ih hθ
      _ = θ ^ (k + 1) * F R := by rw [pow_succ]; ring

theorem exists_eighth_scale_power_bound {θ α δ : ℝ}
    (hθ : 0 ≤ θ) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hdecay : θ ≤ (1 / 8 : ℝ) ^ α) (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 8) :
    ∃ k : ℕ, δ ≤ (1 / 8 : ℝ) * (1 / 8 : ℝ) ^ k ∧
      θ ^ k ≤ 64 * δ ^ α := by
  obtain ⟨k, hklt, hkle⟩ := exists_nat_pow_near_of_lt_one
    (by positivity : 0 < 8 * δ) (by linarith : 8 * δ ≤ 1)
    (by norm_num : 0 < (1 / 8 : ℝ)) (by norm_num : (1 / 8 : ℝ) < 1)
  refine ⟨k, by linarith, ?_⟩
  have hkbound : (1 / 8 : ℝ) ^ k ≤ 64 * δ := by
    rw [pow_succ] at hklt
    linarith
  calc
    θ ^ k ≤ ((1 / 8 : ℝ) ^ α) ^ k := pow_le_pow_left₀ hθ hdecay k
    _ = ((1 / 8 : ℝ) ^ k) ^ α := by
      rw [← Real.rpow_mul_natCast (by norm_num : 0 ≤ (1 / 8 : ℝ)),
        ← Real.rpow_natCast_mul (by norm_num : 0 ≤ (1 / 8 : ℝ))]
      congr 1
      ring
    _ ≤ (64 * δ) ^ α := Real.rpow_le_rpow (by positivity) hkbound hα
    _ = (64 : ℝ) ^ α * δ ^ α := Real.mul_rpow (by norm_num) hδ.le
    _ ≤ 64 * δ ^ α := mul_le_mul_of_nonneg_right
      (Real.rpow_le_self_of_one_le (by norm_num : (1 : ℝ) ≤ 64) hα1)
      (Real.rpow_nonneg hδ.le _)

end CHS.Analysis
