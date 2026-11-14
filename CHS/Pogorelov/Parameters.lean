import CHS.CoreImports

/-!
# Exact scalar parameters from the Pogorelov proof

S001 candidate source, not typechecked. These are scalar identities and
inequalities only, NOT either of the paper's PDE estimates.
-/

set_option autoImplicit false

namespace CHS.Pogorelov

noncomputable def cChoice (n : ℕ) (κ : ℝ) : ℝ := (2 * (n : ℝ) - 1) * κ
noncomputable def beta (n : ℕ) (κ : ℝ) : ℝ := (4 * (n : ℝ) - 2) * κ + 2
noncomputable def logDenom (n : ℕ) (κ c : ℝ) : ℝ := c ^ 2 + c * κ + (n : ℝ) * κ
noncomputable def alpha (K : ℝ) : ℝ := 1 / (8 * (1 + K ^ 2))

lemma beta_eq_two_c_add_two (n : ℕ) (κ : ℝ) : beta n κ = 2 * cChoice n κ + 2 := by
  unfold beta cChoice
  ring

lemma cChoice_gap (n : ℕ) (κ : ℝ) :
    cChoice n κ - ((n : ℝ) - 1) * κ = (n : ℝ) * κ := by
  unfold cChoice
  ring

lemma logDenom_choice (n : ℕ) (κ : ℝ) :
    logDenom n κ (cChoice n κ) = ((n : ℝ) * κ) * (beta n κ - 1) := by
  unfold logDenom cChoice beta
  ring

lemma beta_ge_four_n {n : ℕ} (hn : 2 ≤ n) {κ : ℝ} (hκ : 1 ≤ κ) :
    4 * (n : ℝ) ≤ beta n κ := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 ≤ ((4 : ℝ) * n - 2) * (κ - 1) :=
    mul_nonneg (by linarith) (by linarith)
  unfold beta
  nlinarith

lemma beta_sub_one_pos {n : ℕ} (hn : 2 ≤ n) {κ : ℝ} (hκ : 1 ≤ κ) :
    0 < beta n κ - 1 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h := beta_ge_four_n hn hκ
  linarith

lemma cChoice_pos {n : ℕ} (hn : 2 ≤ n) {κ : ℝ} (hκ : 1 ≤ κ) :
    0 < cChoice n κ := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  exact mul_pos (by linarith) (by linarith)

lemma log_coefficient_exact {n : ℕ} (hn : 2 ≤ n) {κ : ℝ} (hκ : 1 ≤ κ) :
    (cChoice n κ - ((n : ℝ) - 1) * κ) / logDenom n κ (cChoice n κ) =
      1 / (beta n κ - 1) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnk : (n : ℝ) * κ ≠ 0 := ne_of_gt (mul_pos hnR (by linarith))
  have hb : beta n κ - 1 ≠ 0 := ne_of_gt (beta_sub_one_pos hn hκ)
  rw [cChoice_gap, logDenom_choice]
  field_simp [hnk, hb]
  <;> ring

/-- Difference of fractions, written as a polynomial certificate. -/
lemma ratio_cross_difference (c A t κ : ℝ) :
    (A + κ) * (c + t) - (A + t) * (c + κ) = (κ - t) * (c - A) := by
  ring

lemma ratio_monotone (c A t κ : ℝ) (ht : t ≤ κ) (hA : A ≤ c)
    (hct : 0 < c + t) (hck : 0 < c + κ) :
    (A + t) / (c + t) ≤ (A + κ) / (c + κ) := by
  apply (div_le_div_iff₀ hct hck).mpr
  have hp := mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr hA)
  have hid := ratio_cross_difference c A t κ
  linarith

lemma ratio_aux_gap (N κ c : ℝ) (hc : c + 1 ≠ 0) :
    c - (c ^ 2 + (N - 1) * κ) / (c + 1) = (c - (N - 1) * κ) / (c + 1) := by
  field_simp [hc]
  <;> ring

lemma ratio_endpoint (N κ c : ℝ) (hc : c + 1 ≠ 0) (hck : c + κ ≠ 0) :
    ((c ^ 2 + (N - 1) * κ) / (c + 1) + κ) / (c + κ) =
      (c ^ 2 + c * κ + N * κ) / ((c + 1) * (c + κ)) := by
  field_simp [hc, hck]
  <;> ring

lemma beta_one (n : ℕ) : beta n 1 = 4 * (n : ℝ) := by
  unfold beta
  ring

/-- Exact κ=1 reduction of the coefficient, including exp(1/8). -/
lemma convex_coefficient (n : ℕ) :
    32 * (n : ℝ) * beta n 1 * (1 + Real.sqrt (1 : ℝ)) * Real.exp (1 / 8 : ℝ) =
      256 * (n : ℝ) ^ 2 * Real.exp (1 / 8 : ℝ) := by
  rw [beta_one, Real.sqrt_one]
  ring

lemma alpha_pos (K : ℝ) : 0 < alpha K := by
  unfold alpha
  positivity

lemma alpha_gradient_bound (K G : ℝ) (hG : G ≤ K ^ 2) :
    alpha K * G ≤ (1 / 8 : ℝ) := by
  have hden : 0 < (8 : ℝ) * (1 + K ^ 2) := by positivity
  unfold alpha
  have hrewrite : (1 / (8 * (1 + K ^ 2))) * G = G / (8 * (1 + K ^ 2)) := by ring
  rw [hrewrite]
  apply (div_le_iff₀ hden).mpr
  nlinarith [sq_nonneg K]

end CHS.Pogorelov
