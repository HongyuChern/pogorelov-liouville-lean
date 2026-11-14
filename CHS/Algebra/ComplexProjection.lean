import CHS.Calculus.BasisHessian

/-! # The exact real-to-complex Hessian projection in the frozen manuscript -/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder

namespace CHS.Algebra

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def complexProjection (H : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) : Matrix ι ι ℂ :=
  fun i j => (4 : ℂ)⁻¹ * ((H (.inl i) (.inl j) : ℂ) + (H (.inr i) (.inr j) : ℂ) +
    Complex.I * ((H (.inl i) (.inr j) : ℂ) - (H (.inr i) (.inl j) : ℂ)))

def complexInclusion : Matrix (ι ⊕ ι) ι ℂ :=
  fun i j => Sum.elim (fun k => (1 : Matrix ι ι ℂ) k j)
    (fun k => Complex.I * (1 : Matrix ι ι ℂ) k j) i

theorem complexProjection_congruence (H : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) :
    complexProjection H = (4 : ℝ)⁻¹ •
      (complexInclusion.conjTranspose * H.map Complex.ofReal * complexInclusion) := by
  ext i j
  simp [complexProjection, complexInclusion, Matrix.mul_apply, Fintype.sum_sum_type,
    Matrix.conjTranspose_apply, Matrix.one_apply, Matrix.map_apply, Matrix.smul_apply,
    Complex.real_smul, Complex.I_sq, apply_ite, Complex.star_def]
  <;> ring_nf <;> simp [Complex.I_sq] <;> ring

theorem complexProjection_posSemidef {H : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ}
    (hH : H.PosSemidef) : (complexProjection H).PosSemidef := by
  rw [complexProjection_congruence]
  have h := (CHS.Calculus.real_matrix_posSemidef_iff_complexification hH.isHermitian).mp hH
  exact (h.conjTranspose_mul_mul_same complexInclusion).smul (by norm_num : 0 ≤ (4 : ℝ)⁻¹)

theorem complexProjection_sub (H K : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) :
    complexProjection (H - K) = complexProjection H - complexProjection K := by
  ext i j
  simp only [complexProjection, Matrix.sub_apply, Complex.ofReal_sub]
  ring

theorem complexProjection_smul (c : ℝ) (H : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) :
    complexProjection (c • H) = c • complexProjection H := by
  ext i j
  simp only [complexProjection, Matrix.smul_apply, smul_eq_mul, Complex.ofReal_mul,
    Complex.real_smul]
  ring

theorem complexProjection_neg (H : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) :
    complexProjection (-H) = -complexProjection H := by
  simpa only [neg_one_smul] using complexProjection_smul (-1) H

theorem continuous_complexProjection :
    Continuous (complexProjection (ι := ι)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  unfold complexProjection
  fun_prop

theorem four_complexProjection_trace_re (H : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) :
    4 * (complexProjection H).trace.re = H.trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Complex.re_sum, Finset.mul_sum,
    complexProjection, Fintype.sum_sum_type]
  norm_num [Complex.mul_re, Complex.mul_im]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem eq_zero_of_posSemidef_complexProjection_zero
    {H : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ} (hH : H.PosSemidef)
    (hP : complexProjection H = 0) : H = 0 := by
  apply hH.trace_eq_zero_iff.mp
  rw [← four_complexProjection_trace_re, hP]
  simp

end CHS.Algebra

namespace CHS.Calculus

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [Fintype ι] [DecidableEq ι]

theorem complexProjection_realBlockHessian {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (a b : ι → E) :
    CHS.Algebra.complexProjection (realBlockHessian a b u x) = complexHessian a b u x := by
  ext i j
  exact (complexHessian_real_entry hu a b i j).symm

end CHS.Calculus
