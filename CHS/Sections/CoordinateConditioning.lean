import CHS.Calculus.ComplexAffineEquiv
import CHS.Algebra.UniformInverseBounds

/-!
# Trace and coordinate conditioning in (3.9)

The real-entry estimate is related to the complex trace with the exact
factor four.  At the point corresponding to the normalized origin,
this is an actual bound for the Hilbert--Schmidt square of `G`.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators ContDiff

namespace CHS.Calculus

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

theorem four_complexHessian_trace_re {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (a b : ι → E) :
    4 * (complexHessian a b u x).trace.re =
      ∑ i, (realHessian u x (a i) (a i) + realHessian u x (b i) (b i)) := by
  rw [Matrix.trace, Complex.re_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.diag_apply, complexHessian_real_entry hu]
  norm_num [Complex.mul_re, Complex.mul_im]
  <;> ring

end CHS.Calculus

namespace CHS.Algebra

variable {n : ℕ}

theorem hsSq_eq_transpose_conjugate_trace (G : Matrix (Fin n) (Fin n) ℂ) :
    hsSq G = (G.transpose * G.map star).trace.re := by
  change (∑ i, ∑ j, Complex.normSq (G i j)) =
    (∑ i, ∑ j, G j i * star (G j i)).re
  rw [Finset.sum_comm]
  simp only [Complex.re_sum, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]

theorem exists_uniform_hs_norm_sum_bound (n : ℕ) (R : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ G : Matrix (Fin n) (Fin n) ℂ,
      Complex.normSq G.det = 1 → hsSq G ≤ R →
      Real.sqrt (hsSq G) + Real.sqrt (hsSq G⁻¹) ≤ B := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_hs_inverse_bound n R
  refine ⟨Real.sqrt R + Real.sqrt C, by positivity, ?_⟩
  intro G hdet hG
  exact add_le_add (Real.sqrt_le_sqrt hG) (Real.sqrt_le_sqrt (hbound G hdet hG))

end CHS.Algebra

namespace CHS.Sections

open CHS.Calculus CHS.Analysis CHS.Algebra

variable {n : ℕ}
local notation "E₀" => DeGiorgi.AmbientSpace (n + n)

theorem complexHessian_trace_re_le_of_euclidean_entry_bound
    {v : E₀ → ℝ} {x : E₀} (hv : ContDiffAt ℝ 2 v x) {M : ℝ}
    (hM : ∀ i j, |euclideanHessian v x i j| ≤ M) :
    (complexHessian realDirections imagDirections v x).trace.re ≤ (n : ℝ) * M / 2 := by
  have hsum : (∑ i : Fin n,
      (realHessian v x (realDirections i) (realDirections i) +
        realHessian v x (imagDirections i) (imagDirections i))) ≤ (n : ℝ) * (2 * M) := by
    calc
      _ ≤ ∑ _i : Fin n, (2 * M) := by
        apply Finset.sum_le_sum
        intro i _
        have hr := hM (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl i))
        have hi := hM (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inr i))
        change |realHessian v x (realDirections i) (realDirections i)| ≤ M at hr
        change |realHessian v x (imagDirections i) (imagDirections i)| ≤ M at hi
        have hr' := (le_abs_self _).trans hr
        have hi' := (le_abs_self _).trans hi
        linarith
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← four_complexHessian_trace_re hv realDirections imagDirections] at hsum
  linarith

theorem hsSq_bound_at_normalized_origin
    {u : E₀ → ℝ} (hu : ContDiff ℝ 2 u)
    (hA0 : complexHessian realDirections imagDirections u 0 = 1)
    (G : Matrix (Fin n) (Fin n) ℂ) (c : E₀) {h : ℝ} (hh : 0 < h) (w : E₀)
    (hw : c + Real.sqrt h • complexMatrixRealMap G w = 0) {M : ℝ}
    (hM : ∀ i j, |euclideanHessian
      (fun y => h⁻¹ * u (c + Real.sqrt h • complexMatrixRealMap G y) - 1) w i j| ≤ M) :
    hsSq G ≤ (n : ℝ) * M / 2 := by
  have hT : ContDiff ℝ 2 (fun y => c + Real.sqrt h • complexMatrixRealMap G y) := by
    fun_prop
  have hcomp := hu.comp hT
  have hv : ContDiff ℝ 2 (fun y => h⁻¹ * u (c + Real.sqrt h • complexMatrixRealMap G y) - 1) :=
    (contDiff_const.mul hcomp).sub contDiff_const
  have hbound := complexHessian_trace_re_le_of_euclidean_entry_bound hv.contDiffAt hM
  rw [complexHessian_normalized_complex_affine G c hh hu.contDiffAt,
    hw, hA0, Matrix.mul_one, ← hsSq_eq_transpose_conjugate_trace] at hbound
  exact hbound

end CHS.Sections
