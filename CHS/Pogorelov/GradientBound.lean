import CHS.Pogorelov.GradientNorm

/-!
# The gradient bound (2.31) in a diagonal frame

The algebra proves the stronger coefficient 2 used in the manuscript's
explanation.  The last theorem weakens it to the stated coefficient 4.
-/

set_option autoImplicit false
noncomputable section

open Matrix Filter
open scoped BigOperators ComplexOrder ContDiff Topology

namespace CHS.Pogorelov

open CHS.Calculus CHS.Algebra

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : ℕ}

theorem diagonal_symmetric_correction_trace (r : Fin n → ℝ) (B : CMatrix n)
    (hB : ∀ i j, B i j = B j i) :
    (B * diagonal (fun i => ((r i : ℂ) ^ 2)⁻¹) * B.conjTranspose).trace.re =
      ∑ i, vecSq (fun j => B i j / (r i : ℂ)) := by
  have hentry (i j : Fin n) :
      (B i j * ((r j : ℂ) ^ 2)⁻¹ * star (B i j)).re =
        Complex.normSq (B i j / (r j : ℂ)) := by
    rw [Complex.normSq_div, Complex.normSq_ofReal,
      mul_right_comm, Complex.star_def, Complex.mul_conj]
    simp only [← Complex.ofReal_pow, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
      Complex.ofReal_re, pow_two, div_eq_mul_inv]
  calc
    _ = ∑ i, ∑ j, Complex.normSq (B i j / (r j : ℂ)) := by
      simp only [Matrix.trace, Matrix.diag_apply, Complex.re_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Matrix.mul_apply, Complex.re_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [mul_diagonal, Matrix.conjTranspose_apply, hentry]
    _ = _ := by
      rw [Finset.sum_comm]
      unfold vecSq
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hB j i]

theorem diagonal_gradient_algebra_bound (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (B : CMatrix n) (hB : ∀ i j, B i j = B j i)
    (v : CVector n) (K : ℝ) (hv : vecSq v ≤ K ^ 2) :
    let A := diagonal (fun i => (r i : ℂ) ^ 2)
    let W := diagonal (fun i => ((r i : ℂ) ^ 2)⁻¹)
    let g := fun i => A.mulVec v i + B.mulVec (star v) i
    (star g ⬝ᵥ W.mulVec g).re ≤
      2 * K ^ 2 * ((∑ i, r i ^ 2) + (B * W * B.conjTranspose).trace.re) := by
  let A := diagonal (fun i => (r i : ℂ) ^ 2)
  let W := diagonal (fun i => ((r i : ℂ) ^ 2)⁻¹)
  let X (i : Fin n) := A.mulVec v i / (r i : ℂ)
  let Y (i : Fin n) := B.mulVec (star v) i / (r i : ℂ)
  have hcoord (i : Fin n) : Complex.normSq (v i) ≤ K ^ 2 := by
    have h := Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (v j))
      (Finset.mem_univ i)
    exact h.trans hv
  have hXentry (i : Fin n) : X i = (r i : ℂ) * v i := by
    dsimp only [X, A]
    rw [Matrix.mulVec_diagonal]
    have hne : (r i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hr i).ne'
    field_simp [hne]
    <;> ring
  have hX : vecSq X ≤ K ^ 2 * ∑ i, r i ^ 2 := by
    unfold vecSq
    simp_rw [hXentry, complex_sq_real_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have h := mul_le_mul_of_nonneg_left (hcoord i) (sq_nonneg (r i))
    simpa only [mul_comm] using h
  have hdot (i : Fin n) : dot (fun j => B i j / (r i : ℂ)) v = Y i := by
    simp only [dot, Y, Matrix.mulVec, dotProduct, Pi.star_apply, Finset.sum_div,
      div_eq_mul_inv, Finset.sum_mul, mul_right_comm]
  have hYentry (i : Fin n) : Complex.normSq (Y i) ≤
      K ^ 2 * vecSq (fun j => B i j / (r i : ℂ)) := by
    have hcs := dot_sq_le (fun j => B i j / (r i : ℂ)) v
    rw [hdot i] at hcs
    exact hcs.trans (by
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_left hv (vecSq_nonneg (fun j => B i j / (r i : ℂ))))
  have hY : vecSq Y ≤ K ^ 2 * (B * W * B.conjTranspose).trace.re := by
    change (∑ i, Complex.normSq (Y i)) ≤ _
    rw [diagonal_symmetric_correction_trace r B hB, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => hYentry i
  have hsum := vecSq_add_le_two X Y
  dsimp only
  rw [diagonal_covector_norm_eq]
  change vecSq (fun i => (A.mulVec v i + B.mulVec (star v) i) / (r i : ℂ)) ≤ _
  simp only [add_div]
  change vecSq (fun i => X i + Y i) ≤ _
  nlinarith only [hsum, hX, hY]

/-- The actual potential version of the stronger coefficient-2 estimate. -/
theorem diagonal_gradientNormSq_bound_two {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 3 u x) (a b : Fin n → E)
    (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (hA : complexHessian a b u x = diagonal (fun i => (r i : ℂ) ^ 2))
    (K : ℝ) (hK : gradientNormSq a b u x ≤ K ^ 2) :
    let W := (complexHessian a b u x)⁻¹
    let g := wirtingerGradient a b (gradientNormSq a b u) x
    (star g ⬝ᵥ W.mulVec g).re ≤
      2 * K ^ 2 * ((complexHessian a b u x).trace.re + (correctionTrace a b u x).re) := by
  have hu2 : ContDiffAt ℝ 2 u x := hu.of_le (by norm_num)
  have huc : ContDiffAt ℝ 2 (fun y => (u y : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hu2
  have hB (i j : Fin n) : pureHessian a b u x i j = pureHessian a b u x j i :=
    dz_comm_at huc (a i) (b i) (a j) (b j)
  have hv : vecSq (wirtingerGradient a b u x) ≤ K ^ 2 := by
    rwa [gradientNormSq_eq_wirtinger (hu.differentiableAt (by norm_num))] at hK
  have hG := (gradientNormSq_contDiffAt_two hu a b).differentiableAt (by norm_num)
  have hg : wirtingerGradient a b (gradientNormSq a b u) x = fun i =>
      (complexHessian a b u x).mulVec (wirtingerGradient a b u x) i +
        (pureHessian a b u x).mulVec (star (wirtingerGradient a b u x)) i := by
    funext i
    rw [wirtingerGradient_eq_dz hG, gradientNormSq_first_derivative hu2]
  have hAstar : (complexHessian a b u x).map star = complexHessian a b u x := by
    rw [hA, map_diagonal_star]
    congr 1
    ext i
    simp [star_pow, Complex.conj_ofReal]
  have hW : (complexHessian a b u x)⁻¹ = diagonal (fun i => ((r i : ℂ) ^ 2)⁻¹) := by
    rw [hA, diagonal_inverse_squares r hr]
  have htrace : (complexHessian a b u x).trace.re = ∑ i, r i ^ 2 := by
    rw [hA, Matrix.trace_diagonal, Complex.re_sum]
    simp only [← Complex.ofReal_pow, Complex.ofReal_re]
  dsimp only
  rw [hg, correctionTrace_eq, hAstar, ← pureHessian_conjTranspose hu2 a b, hW, htrace, hA]
  exact diagonal_gradient_algebra_bound r hr (pureHessian a b u x) hB
    (wirtingerGradient a b u x) K hv

/-- Equation (2.31), with its stated coefficient 4. -/
theorem diagonal_gradientNormSq_bound {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 3 u x) (a b : Fin n → E)
    (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (hA : complexHessian a b u x = diagonal (fun i => (r i : ℂ) ^ 2))
    (K : ℝ) (hK : gradientNormSq a b u x ≤ K ^ 2) :
    let W := (complexHessian a b u x)⁻¹
    let g := wirtingerGradient a b (gradientNormSq a b u) x
    (star g ⬝ᵥ W.mulVec g).re ≤
      4 * K ^ 2 * ((complexHessian a b u x).trace.re + (correctionTrace a b u x).re) := by
  have h := diagonal_gradientNormSq_bound_two hu a b r hr hA K hK
  have hpos : (complexHessian a b u x).PosDef := by
    rw [hA]
    apply Matrix.PosDef.diagonal
    intro i
    rw [← Complex.ofReal_pow]
    exact_mod_cast (sq_pos_of_pos (hr i))
  have hWpos := hpos.inv.posSemidef
  have hleft : 0 ≤ (star (wirtingerGradient a b (gradientNormSq a b u) x) ⬝ᵥ
      (complexHessian a b u x)⁻¹.mulVec
        (wirtingerGradient a b (gradientNormSq a b u) x)).re :=
    hWpos.re_dotProduct_nonneg _
  dsimp only at h ⊢
  nlinarith only [h, hleft]

/-- Equation (2.31) in the original frame, with the actual inverse Hessian
and actual derivative of `gradientNormSq`. -/
theorem gradientNormSq_bound {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 3 u x) (a b : Fin n → E)
    (hdet : (complexHessian a b u x).det = 1)
    (hpos : (complexHessian a b u x).PosDef)
    (K : ℝ) (hK : gradientNormSq a b u x ≤ K ^ 2) :
    let W := (complexHessian a b u x)⁻¹
    let g := wirtingerGradient a b (gradientNormSq a b u) x
    (star g ⬝ᵥ W.mulVec g).re ≤
      4 * K ^ 2 * ((complexHessian a b u x).trace.re + (correctionTrace a b u x).re) := by
  obtain ⟨Q, r, hQ, hQ', hr, hdiag⟩ := exists_unitary_diagonal_squares hpos
  let a' := complexFrameReal Q a b
  let b' := complexFrameImag Q a b
  let W := (complexHessian a b u x)⁻¹
  have hu2 : ContDiffAt ℝ 2 u x := hu.of_le (by norm_num)
  have hdiag' : complexHessian a' b' u x = diagonal (fun i => (r i : ℂ) ^ 2) := by
    rw [complexHessian_complexFrame hu2]
    exact hdiag
  have hG : gradientNormSq a' b' u = gradientNormSq a b u :=
    gradientNormSq_unitary_frame_eq Q a b u hQ
  have hK' : gradientNormSq a' b' u x ≤ K ^ 2 := by rwa [hG]
  have hW' : (complexHessian a' b' u x)⁻¹ = Q * W * Q.conjTranspose := by
    rw [complexHessian_complexFrame hu2]
    exact unitary_conjugate_inverse Q _ hQ hQ' (hdet ▸ isUnit_one)
  have h := diagonal_gradientNormSq_bound hu a' b' r hr hdiag' K hK'
  dsimp only at h ⊢
  rw [hG, hW', wirtingerGradient_complexFrame
      ((gradientNormSq_contDiffAt_two hu a b).differentiableAt (by norm_num)),
    unitary_covector_pairing Q W _ hQ, complexHessian_complexFrame hu2,
    unitary_conjugate_trace Q _ hQ,
    correctionTrace_unitary_frame hu2 Q a b hdet hQ hQ'] at h
  exact h

end CHS.Pogorelov
