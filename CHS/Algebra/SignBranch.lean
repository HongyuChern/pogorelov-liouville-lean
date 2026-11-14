import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Algebraic implications in the independent Theorem 1.1 sign branch

These lemmas do not assume that the manuscript's independent hypotheses
already force the positive branch.  They establish the exact conclusions
of the matrix sandwich at the negative-branch extremum.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped ComplexOrder MatrixOrder

namespace CHS.Algebra

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem schur_sandwich_forces_kappa_one [Nonempty ι]
    {A C : Matrix ι ι ℂ} (hA : A.PosDef) {κ : ℝ} (hκ : 1 ≤ κ)
    (hlo : (C - κ • A).PosSemidef) (hhi : (A - C).PosSemidef) : κ = 1 ∧ C = A := by
  let i : ι := Classical.choice inferInstance
  have ha : 0 < (A i i).re := (Complex.pos_iff.mp (hA.diag_pos (i := i))).1
  have hl := (Complex.nonneg_iff.mp (hlo.diag_nonneg (i := i))).1
  have hh := (Complex.nonneg_iff.mp (hhi.diag_nonneg (i := i))).1
  simp only [Matrix.sub_apply, Matrix.smul_apply, Complex.sub_re,
    Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at hl hh
  have hk : κ = 1 := by nlinarith
  refine ⟨hk, ?_⟩
  rw [hk, one_smul] at hlo
  exact le_antisymm (Matrix.le_iff.mpr hhi) (Matrix.le_iff.mpr hlo)

theorem even_card_of_posDef_det_neg_eq_one {A : Matrix ι ι ℂ}
    (hA : A.PosDef) (hdet : (-A).det = 1) : Even (Fintype.card ι) := by
  by_contra hnot
  have hodd : Odd (Fintype.card ι) := Nat.not_even_iff_odd.mp hnot
  rw [Matrix.det_neg, hodd.neg_one_pow, neg_one_mul] at hdet
  have hpos := hA.det_pos
  have hAeq : A.det = -1 := neg_eq_iff_eq_neg.mp hdet
  rw [hAeq] at hpos
  norm_num at hpos

theorem det_eq_one_of_posDef_det_neg_eq_one {A : Matrix ι ι ℂ}
    (hA : A.PosDef) (hdet : (-A).det = 1) : A.det = 1 := by
  have heven := even_card_of_posDef_det_neg_eq_one hA hdet
  simpa only [Matrix.det_neg, heven.neg_one_pow, one_mul] using hdet

end CHS.Algebra

namespace CHS

/-- The exact even weight in the negative branch, after κ = 1. -/
theorem pogorelov_weight_neg_at_one (n : ℕ) (s : ℝ) :
    (-s) ^ ((4 * (n : ℝ) - 2) * 1 + 2) = s ^ ((4 * (n : ℝ) - 2) * 1 + 2) := by
  have exponent_eq : (4 * (n : ℝ) - 2) * 1 + 2 = ((4 * n : ℕ) : ℝ) := by
    push_cast
    ring
  rw [exponent_eq, Real.rpow_natCast, Real.rpow_natCast, pow_mul, pow_mul]
  have fourth_eq : (-s) ^ 4 = s ^ 4 := by ring
  rw [fourth_eq]

end CHS
