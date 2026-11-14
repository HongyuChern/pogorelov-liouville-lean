import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The scalar algebra behind Lemma 2.6

This file is new S001 source. It has not been typechecked in the current
execution environment. Every declaration has a proof body; no result from
this file is included in the kernel-verified count until a real build passes.

The identity below is the denominator-free version of the manuscript's
trace-free Hilbert--Schmidt projection estimate. `N` will be the real cast
of the matrix dimension, `V` a squared vector norm, and `K ≤ 1` the squared
norm of `k`.
-/

set_option autoImplicit false

namespace CHS.Algebra

/-- Exact polynomial certificate, valid without sign hypotheses. -/
theorem tracefree_defect_identity (N c V K r s t : ℝ) :
    N ^ 2 * ((c ^ 2 + N - 1) * V) -
      (N ^ 2 * ((c ^ 2 + K) * V + 2 * c * t) -
        N * (c ^ 2 * r ^ 2 + s ^ 2 + 2 * c * t)) =
    N * ((c * r - (N - 1) * s) ^ 2 + N * (N - 2) * (V - s ^ 2)) +
      N ^ 2 * (1 - K) * V + 2 * N * c * (N - 1) * (r * s - t) := by
  ring

/-- Scalar bound for `N Q - tr(Q) I`. There is no conclusion-valued premise. -/
theorem tracefree_projected_sq_bound
    (N c V K r s t : ℝ)
    (hN : 2 ≤ N) (hc : 0 ≤ c) (hV : 0 ≤ V)
    (hK : K ≤ 1) (hs : s ^ 2 ≤ V) (ht : t ≤ r * s) :
    N ^ 2 * ((c ^ 2 + K) * V + 2 * c * t) -
        N * (c ^ 2 * r ^ 2 + s ^ 2 + 2 * c * t) ≤
      N ^ 2 * ((c ^ 2 + N - 1) * V) := by
  have hN0 : 0 ≤ N := by linarith
  have hN1 : 0 ≤ N - 1 := by linarith
  have hN2 : 0 ≤ N - 2 := by linarith
  have hs0 : 0 ≤ V - s ^ 2 := sub_nonneg.mpr hs
  have hK0 : 0 ≤ 1 - K := sub_nonneg.mpr hK
  have ht0 : 0 ≤ r * s - t := sub_nonneg.mpr ht
  have hfirst :
      0 ≤ N * ((c * r - (N - 1) * s) ^ 2 + N * (N - 2) * (V - s ^ 2)) :=
    mul_nonneg hN0
      (add_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg hN0 hN2) hs0))
  have hsecond : 0 ≤ N ^ 2 * (1 - K) * V :=
    mul_nonneg (mul_nonneg (sq_nonneg N) hK0) hV
  have hthird : 0 ≤ 2 * N * c * (N - 1) * (r * s - t) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hN0) hc) hN1) ht0
  have hdef := tracefree_defect_identity N c V K r s t
  linarith

/-- Cancel the nonnegative squared norm only after treating its zero case. -/
theorem square_bound_cancel (W T : ℝ) (hW : 0 ≤ W)
    (h : W ^ 2 ≤ T * W) : W ≤ T ∨ W = 0 := by
  by_cases hzero : W = 0
  · exact Or.inr hzero
  · have hp : 0 < W := lt_of_le_of_ne hW (Ne.symm hzero)
    left
    apply le_of_mul_le_mul_right _ hp
    simpa only [pow_two] using h

/-- The form used after Hilbert--Schmidt Cauchy--Schwarz. -/
theorem square_bound_cancel_nonneg (W T : ℝ) (hW : 0 ≤ W) (hT : 0 ≤ T)
    (h : W ^ 2 ≤ T * W) : W ≤ T := by
  rcases square_bound_cancel W T hW h with hle | hz
  · exact hle
  · simpa only [hz] using hT

end CHS.Algebra
