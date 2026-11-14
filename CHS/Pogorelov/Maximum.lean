import CHS.Pogorelov.Parameters

/-!
# Scalar inequalities at the maximum of the Pogorelov test function
-/

set_option autoImplicit false

namespace CHS.Pogorelov

theorem quadratic_completion {β XX YY XY : ℝ} (hβ : 1 < β)
    (hYX : 0 ≤ XX + YY - 2 * XY) :
    -YY ≤ (β ^ 2 * XX + YY - 2 * β * XY) / (β - 1) - β * XX := by
  have hden : 0 < β - 1 := by linarith
  have heq :
      (β ^ 2 * XX + YY - 2 * β * XY) / (β - 1) - β * XX + YY =
        (β / (β - 1)) * (XX + YY - 2 * XY) := by
    field_simp [hden.ne']
    <;> ring
  have hnonneg : 0 ≤ (β / (β - 1)) * (XX + YY - 2 * XY) :=
    mul_nonneg (div_nonneg (by linarith) hden.le) hYX
  linarith only [heq, hnonneg]

theorem trace_bound_at_maximum
    {n : ℕ} (hn : 2 ≤ n) {κ : ℝ} (hκ : 1 ≤ κ) (K : ℝ)
    {t H XX YY XY : ℝ} (ht : 0 < t) (hH : 0 ≤ H)
    (hYX : 0 ≤ XX + YY - 2 * XY)
    (hYY : YY ≤ 4 * (alpha K) ^ 2 * K ^ 2 * H)
    (hmax : -(n : ℝ) * beta n κ / t - beta n κ * XX +
      (beta n κ ^ 2 * XX + YY - 2 * beta n κ * XY) / (beta n κ - 1) +
      alpha K * H ≤ 0) :
    t * H ≤ 16 * (n : ℝ) * beta n κ * (1 + K ^ 2) := by
  let α := alpha K
  let β := beta n κ
  have hβ : 1 < β := by
    have := beta_sub_one_pos hn hκ
    linarith
  have hα : 0 < α := alpha_pos K
  have h1 : -(n : ℝ) * β / t - YY + α * H ≤ 0 := by
    have h := quadratic_completion hβ hYX
    linarith only [h, hmax]
  have h2 : α * (1 - 4 * α * K ^ 2) * H ≤ (n : ℝ) * β / t := by
    have heq : α * (1 - 4 * α * K ^ 2) * H = α * H - 4 * α ^ 2 * K ^ 2 * H := by ring
    change YY ≤ 4 * α ^ 2 * K ^ 2 * H at hYY
    rw [heq]
    rw [neg_mul, neg_div] at h1
    linarith only [h1, hYY]
  have hαK : 4 * α * K ^ 2 ≤ 1 / 2 := by
    have h := alpha_gradient_bound K (K ^ 2) le_rfl
    linarith
  have h3 : α / 2 * H ≤ (n : ℝ) * β / t := by
    apply le_trans _ h2
    apply mul_le_mul_of_nonneg_right _ hH
    have h := mul_le_mul_of_nonneg_left (show 1 / 2 ≤ 1 - 4 * α * K ^ 2 by linarith) hα.le
    linarith
  have h4 := (le_div_iff₀ ht).mp h3
  have hden : 0 < 16 * (1 + K ^ 2) := by positivity
  have halphaHalf : α / 2 = (16 * (1 + K ^ 2))⁻¹ := by
    dsimp [α, alpha]
    have hbase : 0 < 1 + K ^ 2 := by positivity
    field_simp [hbase.ne']
    <;> ring
  rw [halphaHalf] at h4
  have h5 : t * H / (16 * (1 + K ^ 2)) ≤ (n : ℝ) * β := by
    rw [div_eq_mul_inv]
    rw [show t * H * (16 * (1 + K ^ 2))⁻¹ = (16 * (1 + K ^ 2))⁻¹ * H * t by ring]
    exact h4
  have h6 := (div_le_iff₀ hden).mp h5
  change t * H ≤ 16 * (n : ℝ) * β * (1 + K ^ 2)
  calc
    _ ≤ (n : ℝ) * β * (16 * (1 + K ^ 2)) := h6
    _ = _ := by ring


theorem weighted_trace_bound_of_test_maximum
    {n : ℕ} (hn : 2 ≤ n) {κ : ℝ} (hκ : 1 ≤ κ) (K : ℝ)
    {U t₀ t a₀ d₀ S₀ S G₀ G : ℝ}
    (ht₀ : 0 < t₀) (ht₀U : t₀ ≤ U) (ht : 0 < t)
    (ha₀ : 0 ≤ a₀) (hd₀ : 0 ≤ d₀)
    (hS₀ : S₀ = cChoice n κ * a₀ + d₀)
    (hG₀ : G₀ ≤ K ^ 2) (hG : 0 ≤ G) (hS : 0 ≤ S)
    (hmaxTrace : t₀ * (a₀ + d₀) ≤ 16 * (n : ℝ) * beta n κ * (1 + K ^ 2))
    (hmax : t ^ beta n κ * S * Real.exp (alpha K * G) ≤
      t₀ ^ beta n κ * S₀ * Real.exp (alpha K * G₀)) :
    t ^ beta n κ * S ≤
      16 * (n : ℝ) * beta n κ * cChoice n κ * Real.exp (1 / 8) *
        (1 + K ^ 2) * U ^ (beta n κ - 1) := by
  let c := cChoice n κ
  let β := beta n κ
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hc : 1 ≤ c := by
    dsimp [c, cChoice]
    have hp := mul_nonneg (show 0 ≤ (2 * (n : ℝ) - 1) by linarith)
      (sub_nonneg.mpr hκ)
    nlinarith
  have hβ : 0 ≤ β - 1 := (beta_sub_one_pos hn hκ).le
  have hpow : t₀ ^ β = t₀ ^ (β - 1) * t₀ := by
    calc
      _ = t₀ ^ ((β - 1) + 1) := by rw [sub_add_cancel]
      _ = _ := by rw [Real.rpow_add ht₀, Real.rpow_one]
  have htest : t ^ β * S ≤ t ^ β * S * Real.exp (alpha K * G) := by
    apply le_mul_of_one_le_right (mul_nonneg (Real.rpow_nonneg ht.le _) hS)
    exact (Real.one_le_exp_iff).mpr (mul_nonneg (alpha_pos K).le hG)
  have hSbound : S₀ ≤ c * (a₀ + d₀) := by
    rw [hS₀]
    change c * a₀ + d₀ ≤ c * (a₀ + d₀)
    rw [mul_add]
    linarith [mul_le_mul_of_nonneg_right hc hd₀]
  have hSnonneg : 0 ≤ S₀ := by
    rw [hS₀]
    exact add_nonneg (mul_nonneg (cChoice_pos hn hκ).le ha₀) hd₀
  have hmaxExp : Real.exp (alpha K * G₀) ≤ Real.exp (1 / 8) :=
    Real.exp_le_exp.mpr (alpha_gradient_bound K G₀ hG₀)
  have hpows : t₀ ^ (β - 1) ≤ U ^ (β - 1) :=
    Real.rpow_le_rpow ht₀.le ht₀U hβ
  have hT : t₀ * S₀ ≤ c * (16 * (n : ℝ) * β * (1 + K ^ 2)) := by
    calc
      _ ≤ t₀ * (c * (a₀ + d₀)) := mul_le_mul_of_nonneg_left hSbound ht₀.le
      _ = c * (t₀ * (a₀ + d₀)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hmaxTrace (by linarith)
  calc
    _ ≤ t ^ β * S * Real.exp (alpha K * G) := htest
    _ ≤ t₀ ^ β * S₀ * Real.exp (alpha K * G₀) := hmax
    _ ≤ t₀ ^ β * S₀ * Real.exp (1 / 8) := mul_le_mul_of_nonneg_left hmaxExp
      (mul_nonneg (Real.rpow_nonneg ht₀.le _) hSnonneg)
    _ = t₀ ^ (β - 1) * (t₀ * S₀) * Real.exp (1 / 8) := by rw [hpow]; ring
    _ ≤ U ^ (β - 1) * (c * (16 * (n : ℝ) * β * (1 + K ^ 2))) * Real.exp (1 / 8) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hpows hT (mul_nonneg ht₀.le hSnonneg)
          (Real.rpow_nonneg (ht₀.le.trans ht₀U) _)) (Real.exp_pos _).le
    _ = _ := by change _ = 16 * (n : ℝ) * β * c * Real.exp (1 / 8) * (1 + K ^ 2) * U ^ (β - 1); ring

end CHS.Pogorelov
