import CHS.Calculus.BasisHessian
import CHS.Algebra.HessianEntryBounds

/-!
# Full real Hessian entries with the exact Schur factor

The real coordinates are in two blocks: first all `a` directions, then all
`b` directions.  The bound is `2 (1 + sqrt κ) tr A` for every entry.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder ContDiff

namespace CHS.Pogorelov

open CHS.Calculus CHS.Algebra

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem realHessian_four_entry_bounds {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (a b : ι → E) (i j : ι) :
    let R := 2 * (‖complexHessian a b u x i j‖ + ‖pureHessian a b u x i j‖)
    |realHessian u x (a i) (a j)| ≤ R ∧
    |realHessian u x (b i) (b j)| ≤ R ∧
    |realHessian u x (a i) (b j)| ≤ R ∧
    |realHessian u x (b i) (a j)| ≤ R := by
  let A := complexHessian a b u x i j
  let B := pureHessian a b u x i j
  have haa : realHessian u x (a i) (a j) = 2 * (A + B).re := by
    dsimp [A, B]
    rw [complexHessian_real_entry hu, pureHessian_real_entry hu]
    norm_num [Complex.mul_re, Complex.mul_im] <;> ring
  have hbb : realHessian u x (b i) (b j) = 2 * (A - B).re := by
    dsimp [A, B]
    rw [complexHessian_real_entry hu, pureHessian_real_entry hu]
    norm_num [Complex.mul_re, Complex.mul_im] <;> ring
  have hab : realHessian u x (a i) (b j) = 2 * (A - B).im := by
    dsimp [A, B]
    rw [complexHessian_real_entry hu, pureHessian_real_entry hu]
    norm_num [Complex.mul_re, Complex.mul_im] <;> ring
  have hba : realHessian u x (b i) (a j) = -2 * (A + B).im := by
    dsimp [A, B]
    rw [complexHessian_real_entry hu, pureHessian_real_entry hu]
    norm_num [Complex.mul_re, Complex.mul_im] <;> ring
  have ha := (Complex.abs_re_le_norm (A + B)).trans (norm_add_le A B)
  have hb := (Complex.abs_re_le_norm (A - B)).trans (norm_sub_le A B)
  have hc := (Complex.abs_im_le_norm (A - B)).trans (norm_sub_le A B)
  have hd := (Complex.abs_im_le_norm (A + B)).trans (norm_add_le A B)
  change _ ≤ 2 * (‖A‖ + ‖B‖) ∧ _ ≤ 2 * (‖A‖ + ‖B‖) ∧
    _ ≤ 2 * (‖A‖ + ‖B‖) ∧ _ ≤ 2 * (‖A‖ + ‖B‖)
  rw [haa, hbb, hab, hba]
  simp only [abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem realBlockHessian_entry_bound {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (a b : ι → E)
    (hA : (complexHessian a b u x).PosDef) {κ : ℝ} (hκ : 0 ≤ κ)
    (hmat : (κ • complexHessian a b u x -
      pureHessian a b u x * ((complexHessian a b u x).map star)⁻¹ *
        (pureHessian a b u x).map star).PosSemidef)
    (i j : ι ⊕ ι) :
    |realBlockHessian a b u x i j| ≤
      2 * (1 + Real.sqrt κ) * (complexHessian a b u x).trace.re := by
  have hbound (k l : ι) :
      2 * (‖complexHessian a b u x k l‖ + ‖pureHessian a b u x k l‖) ≤
        2 * (1 + Real.sqrt κ) * (complexHessian a b u x).trace.re := by
    have h1 := norm_entry_le_trace_re hA.posSemidef k l
    have h2 := norm_offdiag_le_sqrt_mul_trace hA (pureHessian_conjTranspose hu a b)
      hκ hmat k l
    nlinarith
  cases i with
  | inl i =>
    cases j with
    | inl j => exact (realHessian_four_entry_bounds hu a b i j).1.trans (hbound i j)
    | inr j => exact (realHessian_four_entry_bounds hu a b i j).2.2.1.trans (hbound i j)
  | inr i =>
    cases j with
    | inl j => exact (realHessian_four_entry_bounds hu a b i j).2.2.2.trans (hbound i j)
    | inr j => exact (realHessian_four_entry_bounds hu a b i j).2.1.trans (hbound i j)

end CHS.Pogorelov
