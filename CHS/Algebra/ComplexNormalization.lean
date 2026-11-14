import CHS.Algebra.DeterminantBounds
import CHS.CoreImports

/-!
# Determinant-one complex normalization of a positive Hermitian form

This is the matrix construction in (3.6).  It also supplies the
normalization `A(0) = I` in (3.3) when the original determinant is one.
The covariance convention is the manuscript's `Gᵀ C conjugate(G)`.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped ComplexOrder MatrixOrder

namespace CHS.Algebra

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_complex_normalization_of_posDef
    {C : Matrix ι ι ℂ} (hC : C.PosDef) {c : ℝ} (hc : 0 < c)
    (hscale : C.det = (c : ℂ) ^ Fintype.card ι) :
    ∃ G : Matrix ι ι ℂ,
      G.transpose * C * G.map star = (c : ℂ) • 1 ∧ Complex.normSq G.det = 1 := by
  let S := CFC.sqrt C
  have hS : S.PosSemidef := (CFC.sqrt_nonneg C).posSemidef
  have hSq : S * S = C := by simpa only [pow_two] using CFC.sq_sqrt C hC.posSemidef.nonneg
  have hSunit : IsUnit S.det := by
    have h := (Matrix.isUnit_iff_isUnit_det C).mp hC.isUnit
    rw [← hSq, Matrix.det_mul] at h
    exact isUnit_of_mul_isUnit_left h
  have hInv : S⁻¹ * C * S⁻¹ = 1 := by
    rw [← hSq]
    calc
      S⁻¹ * (S * S) * S⁻¹ = (S⁻¹ * S) * (S * S⁻¹) := by noncomm_ring
      _ = 1 := by rw [Matrix.nonsing_inv_mul _ hSunit, Matrix.mul_nonsing_inv _ hSunit, Matrix.one_mul]
  let Q : Matrix ι ι ℂ := (Real.sqrt c : ℂ) • S⁻¹
  let G := Q.transpose
  have hnorm : G.transpose * C * G.map star = (c : ℂ) • 1 := by
    change Q * C * Q.conjTranspose = (c : ℂ) • 1
    dsimp only [Q]
    rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, hS.isHermitian.inv.eq,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, hInv]
    congr 1
    exact_mod_cast Real.mul_self_sqrt hc.le
  refine ⟨G, hnorm, ?_⟩
  have hdet := congrArg Matrix.det hnorm
  change (G.transpose * C * G.transpose.conjTranspose).det = ((c : ℂ) • (1 : Matrix ι ι ℂ)).det at hdet
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_transpose,
    Matrix.det_smul, Matrix.det_one, mul_one] at hdet
  have heq : (Complex.normSq G.det : ℂ) * (c : ℂ) ^ Fintype.card ι =
      1 * (c : ℂ) ^ Fintype.card ι := by
    calc
      _ = G.det * C.det * star G.det := by rw [hscale, Complex.star_def, ← Complex.mul_conj]; ring
      _ = _ := by simpa only [one_mul] using hdet
  have hz : (c : ℂ) ^ Fintype.card ι ≠ 0 :=
    pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hc.ne')
  have hreal : (Complex.normSq G.det : ℂ) = 1 := mul_right_cancel₀ hz heq
  exact_mod_cast hreal

theorem exists_complex_normalization_of_det_one
    {C : Matrix ι ι ℂ} (hC : C.PosDef) (hdet : C.det = 1) :
    ∃ G : Matrix ι ι ℂ, G.transpose * C * G.map star = 1 ∧ Complex.normSq G.det = 1 := by
  obtain ⟨G, hG, hdetG⟩ := exists_complex_normalization_of_posDef hC
    (c := 1) (by norm_num) (by simpa only [Complex.ofReal_one, one_pow] using hdet)
  exact ⟨G, by simpa only [Complex.ofReal_one, one_smul] using hG, hdetG⟩

/-- The positive real determinant root appearing in the manuscript. -/
def hermitianDetRoot {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  C.det.re ^ ((n : ℝ)⁻¹)

theorem hermitianDetRoot_pos {n : ℕ} {C : Matrix (Fin n) (Fin n) ℂ}
    (hC : C.PosDef) : 0 < hermitianDetRoot C :=
  Real.rpow_pos_of_pos (Complex.pos_iff.mp hC.det_pos).1 _

theorem hermitianDetRoot_pow {n : ℕ} (hn : 0 < n) {C : Matrix (Fin n) (Fin n) ℂ}
    (hC : C.PosDef) : (hermitianDetRoot C : ℂ) ^ n = C.det := by
  have hpos := Complex.pos_iff.mp hC.det_pos
  have hreal : (C.det.re : ℂ) = C.det := by
    apply Complex.ext
    · rfl
    · exact hpos.2
  calc
    _ = (C.det.re : ℂ) := by
      exact_mod_cast Real.rpow_inv_natCast_pow hpos.1.le hn.ne'
    _ = _ := hreal

theorem exists_complex_normalization_det_root
    {n : ℕ} (hn : 0 < n) {C : Matrix (Fin n) (Fin n) ℂ} (hC : C.PosDef) :
    ∃ G : Matrix (Fin n) (Fin n) ℂ,
      G.transpose * C * G.map star = (hermitianDetRoot C : ℂ) • 1 ∧
        Complex.normSq G.det = 1 :=
  exists_complex_normalization_of_posDef hC (hermitianDetRoot_pos hC)
    (by simpa only [Fintype.card_fin] using (hermitianDetRoot_pow hn hC).symm)

end CHS.Algebra
