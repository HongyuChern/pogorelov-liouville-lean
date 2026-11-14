import CHS.Pogorelov.WeightedGradient
import CHS.Pogorelov.Parameters

/-!
# Combining the two trace-gradient terms

The finite-dimensional estimate below includes zero energies.  The scalar
lemmas retain the exact constants in equations (2.26)--(2.28).
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace CHS.Pogorelov

open CHS.Algebra

variable {n : ℕ}

theorem vecSq_add_le_sqrt (v w : CVector n) :
    vecSq (fun i => v i + w i) ≤
      (Real.sqrt (vecSq v) + Real.sqrt (vecSq w)) ^ 2 := by
  have hv := vecSq_nonneg v
  have hw := vecSq_nonneg w
  have hcs := dot_sq_le v w
  have hre : (dot v w).re ^ 2 ≤ vecSq v * vecSq w := by
    have h0 : (dot v w).re ^ 2 ≤ Complex.normSq (dot v w) := by
      simp only [Complex.normSq_apply]
      nlinarith [sq_nonneg (dot v w).im]
    exact h0.trans hcs
  have hp : 0 ≤ Real.sqrt (vecSq v) * Real.sqrt (vecSq w) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hp2 : (Real.sqrt (vecSq v) * Real.sqrt (vecSq w)) ^ 2 =
      vecSq v * vecSq w := by
    rw [mul_pow, Real.sq_sqrt hv, Real.sq_sqrt hw]
  have hcross : (dot v w).re ≤
      Real.sqrt (vecSq v) * Real.sqrt (vecSq w) := by
    nlinarith
  have hadd : vecSq (fun i => v i + w i) =
      vecSq v + vecSq w + 2 * (dot v w).re := by
    simp only [vecSq, complex_sq_add, Finset.sum_add_distrib,
      Finset.mul_sum, dot, Complex.re_sum]
  rw [hadd]
  nlinarith [Real.sq_sqrt hv, Real.sq_sqrt hw]

theorem sqrt_product_sum_sq_le {p q E F : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hE : 0 ≤ E) (hF : 0 ≤ F) :
    (Real.sqrt (p * E) + Real.sqrt (q * F)) ^ 2 ≤
      (p + q) * (E + F) := by
  have hcross : Real.sqrt (p * E) * Real.sqrt (q * F) =
      Real.sqrt (p * F) * Real.sqrt (q * E) := by
    rw [Real.sqrt_mul hp, Real.sqrt_mul hq,
      Real.sqrt_mul hp, Real.sqrt_mul hq]
    ring
  have h1 := Real.sq_sqrt (mul_nonneg hp hE)
  have h2 := Real.sq_sqrt (mul_nonneg hq hF)
  have h3 := Real.sq_sqrt (mul_nonneg hp hF)
  have h4 := Real.sq_sqrt (mul_nonneg hq hE)
  nlinarith [sq_nonneg (Real.sqrt (p * F) - Real.sqrt (q * E))]

/-- Cauchy--Schwarz for two vector terms whose squared norms have separate
energy bounds.  No division by either energy or either coefficient occurs. -/
theorem vecSq_add_energy_bound (v w : CVector n) {p q E F : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (hv : vecSq v ≤ p * E) (hw : vecSq w ≤ q * F) :
    vecSq (fun i => v i + w i) ≤ (p + q) * (E + F) := by
  have hvs := Real.sqrt_le_sqrt hv
  have hws := Real.sqrt_le_sqrt hw
  have hsum : Real.sqrt (vecSq v) + Real.sqrt (vecSq w) ≤
      Real.sqrt (p * E) + Real.sqrt (q * F) := add_le_add hvs hws
  calc
    _ ≤ (Real.sqrt (vecSq v) + Real.sqrt (vecSq w)) ^ 2 :=
      vecSq_add_le_sqrt v w
    _ ≤ (Real.sqrt (p * E) + Real.sqrt (q * F)) ^ 2 := by
      nlinarith [Real.sqrt_nonneg (vecSq v), Real.sqrt_nonneg (vecSq w),
        Real.sqrt_nonneg (p * E), Real.sqrt_nonneg (q * F)]
    _ ≤ _ := sqrt_product_sum_sq_le hp hq hE hF

/-- Equation (2.26), prior to substituting the actual diagonal covectors. -/
theorem trace_vecSq_combination (v w : CVector n)
    {N κ c a d E F : ℝ} (hN : 1 ≤ N) (hκ : 0 ≤ κ) (hc : 0 ≤ c)
    (ha : 0 ≤ a) (hd : 0 ≤ d) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (hv : vecSq v ≤ (c ^ 2 + (N - 1) * κ) * a * E)
    (hw : vecSq w ≤ d * F) :
    vecSq (fun i => v i + w i) ≤
      ((c ^ 2 + (N - 1) * κ) / (c + 1) * a + d) * ((c + 1) * E + F) := by
  have hc1 : 0 < c + 1 := by linarith
  have hp : 0 ≤ (c ^ 2 + (N - 1) * κ) / (c + 1) * a := by
    exact mul_nonneg (div_nonneg
      (add_nonneg (sq_nonneg c) (mul_nonneg (by linarith) hκ)) hc1.le) ha
  have hv' : vecSq v ≤
      ((c ^ 2 + (N - 1) * κ) / (c + 1) * a) * ((c + 1) * E) := by
    convert hv using 1 <;> field_simp [hc1.ne'] <;> ring
  exact vecSq_add_energy_bound v w hp hd (mul_nonneg hc1.le hE) hF hv' hw

/-- The exact cross-multiplied coefficient comparison used after (2.26). -/
theorem trace_coefficient_difference (N κ c a d : ℝ) (hc : c + 1 ≠ 0) :
    (c ^ 2 + c * κ + N * κ) * (c * a + d) -
      ((c + 1) * (c + κ)) *
        ((c ^ 2 + (N - 1) * κ) / (c + 1) * a + d) =
      (c - (N - 1) * κ) * (κ * a - d) := by
  field_simp [hc]
  <;> ring

theorem trace_coefficient_bound {N κ c a d : ℝ}
    (hN : 1 ≤ N) (hκ : 0 ≤ κ) (hc : (N - 1) * κ < c)
    (hd : d ≤ κ * a) :
    (c ^ 2 + (N - 1) * κ) / (c + 1) * a + d ≤
      (c ^ 2 + c * κ + N * κ) / ((c + 1) * (c + κ)) * (c * a + d) := by
  have hc0 : 0 < c := lt_of_le_of_lt (mul_nonneg (by linarith) hκ) hc
  have hc1 : 0 < c + 1 := by linarith
  have hck : 0 < c + κ := by linarith
  have hden := mul_pos hc1 hck
  have hdiff := trace_coefficient_difference N κ c a d hc1.ne'
  have hnonneg : 0 ≤ (c - (N - 1) * κ) * (κ * a - d) :=
    mul_nonneg (by linarith) (sub_nonneg.mpr hd)
  have hscaled : ((c ^ 2 + (N - 1) * κ) / (c + 1) * a + d) *
      ((c + 1) * (c + κ)) ≤ (c ^ 2 + c * κ + N * κ) * (c * a + d) := by
    nlinarith only [hdiff, hnonneg]
  calc
    _ ≤ ((c ^ 2 + c * κ + N * κ) * (c * a + d)) /
        ((c + 1) * (c + κ)) := (le_div_iff₀ hden).mpr hscaled
    _ = _ := by ring

/-- Scalar chain-rule implication in (2.27).  `Q` is the actual gradient
square once this lemma is used; it is not an assumed logarithmic estimate. -/
theorem log_gradient_bound_of_trace_bound {N κ c a d L Q : ℝ}
    (hN : 1 ≤ N) (hκ : 0 ≤ κ) (hc : (N - 1) * κ < c)
    (ha : 0 < a) (hd0 : 0 ≤ d) (hd : d ≤ κ * a) (hL : 0 ≤ L)
    (hQ : Q ≤ ((c ^ 2 + (N - 1) * κ) / (c + 1) * a + d) * L) :
    (c - (N - 1) * κ) / (c ^ 2 + c * κ + N * κ) *
        (Q / (c * a + d) ^ 2) ≤ L / (c * a + d) - Q / (c * a + d) ^ 2 := by
  have hc0 : 0 < c := lt_of_le_of_lt (mul_nonneg (by linarith) hκ) hc
  have hc1 : 0 < c + 1 := by linarith
  have hck : 0 < c + κ := by linarith
  have hden : 0 < (c + 1) * (c + κ) := mul_pos hc1 hck
  have hD : 0 < c ^ 2 + c * κ + N * κ := by
    have h1 := sq_pos_of_pos hc0
    have h2 := mul_nonneg hc0.le hκ
    have h3 := mul_nonneg (show 0 ≤ N by linarith) hκ
    linarith
  have hS : 0 < c * a + d := add_pos_of_pos_of_nonneg (mul_pos hc0 ha) hd0
  have hQ' := hQ.trans (mul_le_mul_of_nonneg_right
    (trace_coefficient_bound hN hκ hc hd) hL)
  have hQ'' : Q ≤ ((c ^ 2 + c * κ + N * κ) * (c * a + d) * L) /
      ((c + 1) * (c + κ)) := by
    simpa only [div_mul_eq_mul_div] using hQ'
  have hscaled := (le_div_iff₀ hden).mp hQ''
  have hid :
      (L / (c * a + d) - Q / (c * a + d) ^ 2 -
        (c - (N - 1) * κ) / (c ^ 2 + c * κ + N * κ) *
          (Q / (c * a + d) ^ 2)) *
          ((c ^ 2 + c * κ + N * κ) * (c * a + d) ^ 2) =
      (c ^ 2 + c * κ + N * κ) * (c * a + d) * L -
        Q * ((c + 1) * (c + κ)) := by
    field_simp [hD.ne', hS.ne']
    <;> ring
  have hfac : 0 < (c ^ 2 + c * κ + N * κ) * (c * a + d) ^ 2 :=
    mul_pos hD (sq_pos_of_pos hS)
  apply sub_nonneg.mp
  apply (mul_le_mul_iff_of_pos_right hfac).mp
  rw [zero_mul, hid]
  exact sub_nonneg.mpr hscaled

/-- The manuscript's choice of `c` gives precisely (2.28). -/
theorem chosen_log_gradient_bound {n : ℕ} (hn : 2 ≤ n) {κ : ℝ} (hκ : 1 ≤ κ)
    {a d L Q : ℝ} (ha : 0 < a) (hd0 : 0 ≤ d) (hd : d ≤ κ * a) (hL : 0 ≤ L)
    (hQ : Q ≤
      ((cChoice n κ ^ 2 + ((n : ℝ) - 1) * κ) / (cChoice n κ + 1) * a + d) * L) :
    (1 / (beta n κ - 1)) * (Q / (cChoice n κ * a + d) ^ 2) ≤
      L / (cChoice n κ * a + d) - Q / (cChoice n κ * a + d) ^ 2 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hc : ((n : ℝ) - 1) * κ < cChoice n κ := by
    have h := cChoice_gap n κ
    have hp := mul_pos hn0 (show 0 < κ by linarith)
    linarith
  have h := log_gradient_bound_of_trace_bound hnR (show 0 ≤ κ by linarith)
    hc ha hd0 hd hL hQ
  change (cChoice n κ - ((n : ℝ) - 1) * κ) / logDenom n κ (cChoice n κ) *
    (Q / (cChoice n κ * a + d) ^ 2) ≤ _ at h
  rw [log_coefficient_exact hn hκ] at h
  exact h

end CHS.Pogorelov
