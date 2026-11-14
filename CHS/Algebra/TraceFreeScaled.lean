import CHS.Algebra.TraceFree

/-!
# The general-kappa use of Lemma 2.6, without dividing by sqrt(kappa)

The exact estimate used in the proof after (2.21) is established directly.
In particular kappa = 0 is allowed in this algebraic result. No positivity
of kappa beyond nonnegativity, and no Hermitian hypothesis on C, is added.
S004 candidate source; NOT kernel-checked in the current environment.
-/

set_option autoImplicit false
open scoped BigOperators

namespace CHS.Algebra

lemma tracefree_scaled_defect_identity (N c κ V K r s t : ℝ) :
    N ^ 2 * ((c ^ 2 + (N - 1) * κ) * V) -
      (N ^ 2 * ((c ^ 2 + K) * V + 2 * c * t) -
        N * (c ^ 2 * r ^ 2 + s ^ 2 + 2 * c * t)) =
    N * ((c * r - (N - 1) * s) ^ 2 + N * (N - 2) * (κ * V - s ^ 2)) +
      N ^ 2 * (κ - K) * V + 2 * N * c * (N - 1) * (r * s - t) := by
  ring

lemma tracefree_scaled_projected_sq_bound
    (N c κ V K r s t : ℝ)
    (hN : 2 ≤ N) (hc : 0 ≤ c) (hV : 0 ≤ V)
    (hK : K ≤ κ) (hs : s ^ 2 ≤ κ * V) (ht : t ≤ r * s) :
    N ^ 2 * ((c ^ 2 + K) * V + 2 * c * t) -
        N * (c ^ 2 * r ^ 2 + s ^ 2 + 2 * c * t) ≤
      N ^ 2 * ((c ^ 2 + (N - 1) * κ) * V) := by
  have hN0 : 0 ≤ N := by linarith
  have hN1 : 0 ≤ N - 1 := by linarith
  have hN2 : 0 ≤ N - 2 := by linarith
  have hfirst : 0 ≤ N * ((c * r - (N - 1) * s) ^ 2 +
      N * (N - 2) * (κ * V - s ^ 2)) :=
    mul_nonneg hN0 (add_nonneg (sq_nonneg _)
      (mul_nonneg (mul_nonneg hN0 hN2) (sub_nonneg.mpr hs)))
  have hsecond : 0 ≤ N ^ 2 * (κ - K) * V :=
    mul_nonneg (mul_nonneg (sq_nonneg N) (sub_nonneg.mpr hK)) hV
  have hthird : 0 ≤ 2 * N * c * (N - 1) * (r * s - t) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hN0) hc) hN1)
      (sub_nonneg.mpr ht)
  have hid := tracefree_scaled_defect_identity N c κ V K r s t
  linarith

lemma projected_testMatrix_sq_bound_scaled {n : ℕ} (hn : 2 ≤ n)
    (c κ : ℝ) (hc : 0 ≤ c) (e k v : CVector n)
    (he : vecSq e = 1) (hk : vecSq k ≤ κ) :
    hsSq (projected (testMatrix c e k v)) ≤
      (n : ℝ) ^ 2 * ((c ^ 2 + ((n : ℝ) - 1) * κ) * vecSq v) := by
  have hN : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : ‖dot k v‖ ^ 2 ≤ κ * vecSq v := by
    rw [Complex.sq_norm]
    exact (dot_sq_le k v).trans (mul_le_mul_of_nonneg_right hk (vecSq_nonneg v))
  have ht : (dot v e * star (dot k v)).re ≤ ‖dot v e‖ * ‖dot k v‖ := by
    calc
      _ ≤ ‖dot v e * star (dot k v)‖ := Complex.re_le_norm _
      _ = _ := by rw [norm_mul, norm_star]
  rw [projected_sq, testMatrix_sq c e k v he, tr_testMatrix_sq]
  exact tracefree_scaled_projected_sq_bound (n : ℝ) c κ (vecSq v) (vecSq k)
    ‖dot v e‖ ‖dot k v‖ (dot v e * star (dot k v)).re
    hN hc (vecSq_nonneg v) hk hs ht

/-- The precise matrix estimate used in the general-kappa Pogorelov proof. -/
theorem tracefree_matrix_inequality_scaled {n : ℕ} (hn : 2 ≤ n)
    (c κ : ℝ) (hc : 0 ≤ c) (hκ : 0 ≤ κ)
    (C : CMatrix n) (htr : tr C = 0) (e k : CVector n)
    (he : vecSq e = 1) (hk : vecSq k ≤ κ) :
    vecSq (action c C e k) ≤ (c ^ 2 + ((n : ℝ) - 1) * κ) * hsSq C := by
  let w := action c C e k
  let Q := testMatrix c e k w
  have hp : pair C (projected Q) = (n : ℝ) * vecSq w := by
    rw [pair_projected_of_trace_zero C Q htr]
    change (n : ℝ) * pair C (testMatrix c e k w) = _
    rw [testMatrix_duality]
    change (n : ℝ) * (dot w w).re = _
    rw [dot_re_self]
  have hD := projected_testMatrix_sq_bound_scaled hn c κ hc e k w he hk
  have hcs := pair_sq_le C (projected Q)
  rw [hp] at hcs
  have hupper := mul_le_mul_of_nonneg_left hD (hsSq_nonneg C)
  have hcombined :
      (n : ℝ) ^ 2 * (vecSq w) ^ 2 ≤
        (n : ℝ) ^ 2 * (((c ^ 2 + ((n : ℝ) - 1) * κ) * hsSq C) * vecSq w) := by
    calc
      _ = ((n : ℝ) * vecSq w) ^ 2 := by ring
      _ ≤ hsSq C * hsSq (projected Q) := hcs
      _ ≤ hsSq C * ((n : ℝ) ^ 2 *
          ((c ^ 2 + ((n : ℝ) - 1) * κ) * vecSq w)) := hupper
      _ = _ := by ring
  have hN : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hcancel := le_of_mul_le_mul_left hcombined (sq_pos_of_pos hN)
  have hcoefficient : 0 ≤ c ^ 2 + ((n : ℝ) - 1) * κ := by
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    exact add_nonneg (sq_nonneg _) (mul_nonneg (by linarith) hκ)
  exact square_bound_cancel_nonneg (vecSq w)
    ((c ^ 2 + ((n : ℝ) - 1) * κ) * hsSq C) (vecSq_nonneg w)
    (mul_nonneg hcoefficient (hsSq_nonneg C)) hcancel

end CHS.Algebra

namespace CHS
open CHS.Algebra

/-- Euclidean-norm form; uses the exact coefficient `c^2 + (n-1)*kappa`. -/
theorem tracefree_matrix_inequality_scaled {n : ℕ} (hn : 2 ≤ n)
    (c κ : ℝ) (hc : 0 ≤ c) (hκ : 0 ≤ κ)
    (C : Matrix (Fin n) (Fin n) ℂ) (htr : Matrix.trace C = 0)
    (e k : Fin n → ℂ)
    (he : ‖(WithLp.toLp 2 e : EuclideanSpace ℂ (Fin n))‖ = 1)
    (hk : ‖(WithLp.toLp 2 k : EuclideanSpace ℂ (Fin n))‖ ^ 2 ≤ κ) :
    ‖(WithLp.toLp 2 (fun i => (c : ℂ) * C.mulVec e i +
        C.conjTranspose.mulVec k i) : EuclideanSpace ℂ (Fin n))‖ ^ 2 ≤
      (c ^ 2 + ((n : ℝ) - 1) * κ) * (Matrix.trace (C * C.conjTranspose)).re := by
  have he2 : vecSq e = 1 := by
    rw [vecSq_eq_euclidean_norm_sq, he]
    norm_num
  have hk2 : vecSq k ≤ κ := by simpa only [vecSq_eq_euclidean_norm_sq] using hk
  have ht : tr C = 0 := by simpa only [tr_eq_matrix_trace] using htr
  have h := Algebra.tracefree_matrix_inequality_scaled hn c κ hc hκ C ht e k he2 hk2
  rw [vecSq_eq_euclidean_norm_sq, hsSq_eq_trace_product] at h
  exact h

end CHS
