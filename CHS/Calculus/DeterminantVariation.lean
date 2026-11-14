import CHS.Calculus.SchurContraction

/-!
# Actual first and second variations of a determinant-one matrix field

S006 candidate source. No Chat Lean executable is available: every proof body
below still requires the user's locked-toolchain compilation.

The determinant is the real differentiable map on actual matrix entries. Its
Jacobi formula is obtained from the continuous multilinear determinant and
Cramer's identity, not supplied as a field in an abstract solution structure.
Only local determinant one and finite C2 regularity are used in the second
variation. The input directions are constant real vectors.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ContDiff Topology

namespace CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Determinant linearity in one row, with the actual adjugate index order. -/
lemma det_updateRow_eq_adjugate_sum (A : Matrix ι ι ℂ) (i : ι) (v : ι → ℂ) :
    (A.updateRow i v).det = ∑ j, A.adjugate j i * v j := by
  rw [← Matrix.cramer_transpose_apply, Matrix.cramer_eq_adjugate_mulVec,
    ← Matrix.adjugate_transpose]
  rfl

/-- The derivative of the row-multilinear determinant in a matrix direction. -/
lemma determinantPolynomial_linearDeriv_apply (A V : Matrix ι ι ℂ) :
    determinantPolynomial.linearDeriv A V = ∑ i, ∑ j, A.adjugate j i * V i j := by
  rw [ContinuousMultilinearMap.linearDeriv_apply]
  change (∑ i, (A.updateRow i (V i)).det) = _
  exact Finset.sum_congr rfl (fun i _ => det_updateRow_eq_adjugate_sum A i (V i))

/-- Real-direction Jacobi formula, proved from real Fréchet differentiation. -/
lemma rd_det_at {G : E → Matrix ι ι ℂ} {x : E}
    (hG : MatrixDifferentiableAt G x) (v : E) :
    rd v (fun y => (G y).det) x =
      ∑ i, ∑ j, (G x).adjugate j i * rd v (fun y => G y i j) x := by
  let DG : E →L[ℝ] Matrix ι ι ℂ := ContinuousLinearMap.pi
    (fun i => ContinuousLinearMap.pi (fun j => fderiv ℝ (fun y => G y i j) x))
  have hDG : HasFDerivAt G DG x :=
    hasFDerivAt_pi.mpr (fun i => hasFDerivAt_pi.mpr (fun j => (hG i j).hasFDerivAt))
  have hdet := ((determinantPolynomial.hasFDerivAt (G x)).restrictScalars ℝ).comp x hDG
  change HasFDerivAt (fun y => (G y).det)
    (((determinantPolynomial.linearDeriv (G x)).restrictScalars ℝ).comp DG) x at hdet
  have hd : rd v (fun y => (G y).det) x =
      determinantPolynomial.linearDeriv (G x)
        (fun i j => rd v (fun y => G y i j) x) := by
    change (fderiv ℝ (fun y => (G y).det) x) v = _
    rw [hdet.fderiv] <;> rfl
  rw [hd, determinantPolynomial_linearDeriv_apply]

/-- Wirtinger Jacobi formula; the normalization is exactly 1/2. -/
lemma dz_det_at {G : E → Matrix ι ι ℂ} {x : E}
    (hG : MatrixDifferentiableAt G x) (a b : E) :
    dz a b (fun y => (G y).det) x =
      ∑ i, ∑ j, (G x).adjugate j i * matrixDZ a b G x i j := by
  change (2 : ℂ)⁻¹ * (rd a (fun y => (G y).det) x -
    Complex.I * rd b (fun y => (G y).det) x) = _
  rw [rd_det_at hG a, rd_det_at hG b]
  calc
    _ = ∑ i, ∑ j, (2 : ℂ)⁻¹ *
        ((G x).adjugate j i * rd a (fun y => G y i j) x -
          Complex.I * ((G x).adjugate j i * rd b (fun y => G y i j) x)) := by
      simp only [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      dsimp only [matrixDZ, dz]
      ring

/-- Fix the reversed inverse-matrix index convention once. -/
lemma trace_mul_eq_reversed_sum (K V : Matrix ι ι ℂ) :
    Matrix.trace (K * V) = ∑ p, ∑ q, K q p * V p q := by
  change (∑ q, ∑ p, K q p * V p q) = _
  exact Finset.sum_comm

/-- Four-factor trace expansion used in the native Hessian contraction. -/
lemma trace_four_eq_reversed_sum (K X Y : Matrix ι ι ℂ) :
    Matrix.trace (K * X * K * Y) =
      ∑ p, ∑ q, ∑ s, ∑ t, K q p * X p s * K s t * Y t q := by
  calc
    _ = ∑ q, ∑ p, ∑ s, ∑ t, K q p * (X p s * (K s t * Y t q)) := by
      simp only [mul_assoc, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
        Finset.mul_sum]
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [mul_assoc]

/-- Crossed four-factor expansion for the bar(A)-inverse Schur formula. -/
lemma trace_four_eq_crossed_sum (K X Y : Matrix ι ι ℂ) :
    Matrix.trace (K * X * K * Y) =
      ∑ p, ∑ q, ∑ s, ∑ t, K q p * X s q * K t s * Y p t := by
  have hcyclic : Matrix.trace (K * X * K * Y) = Matrix.trace (K * Y * K * X) := by
    calc
      _ = Matrix.trace ((K * X) * (K * Y)) := by rw [mul_assoc (K * X) K Y]
      _ = Matrix.trace ((K * Y) * (K * X)) := Matrix.trace_mul_comm _ _
      _ = _ := by rw [mul_assoc (K * Y) K X]
  rw [hcyclic, trace_four_eq_reversed_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  ring

lemma dz_trace_at {G : E → Matrix ι ι ℂ} {x : E}
    (hG : MatrixDifferentiableAt G x) (a b : E) :
    dz a b (fun y => Matrix.trace (G y)) x = Matrix.trace (matrixDZ a b G x) := by
  change dz a b (fun y => ∑ i, G y i i) x = ∑ i, dz a b (fun y => G y i i) x
  exact dz_sum_at (fun i => hG i i) a b

/-- The first differentiated equation for a genuine determinant-one field. -/
theorem trace_inverse_matrixDZ_eq_zero {G : E → Matrix ι ι ℂ} {x : E}
    (hG : MatrixDifferentiableAt G x)
    (hdet : (fun y => (G y).det) =ᶠ[𝓝 x] (fun _ => (1 : ℂ))) (a b : E) :
    Matrix.trace ((G x)⁻¹ * matrixDZ a b G x) = 0 := by
  have hinv := inv_eq_adjugate_of_det_one (G x) hdet.self_of_nhds
  calc
    _ = dz a b (fun y => (G y).det) x := by
      rw [trace_mul_eq_reversed_sum, hinv]
      exact (dz_det_at hG a b).symm
    _ = dz a b (fun _ : E => (1 : ℂ)) x := dz_congr_nhds hdet a b
    _ = 0 := dz_const a b 1 x

/-- Actual second Jacobi variation. The first variation is proved on U before
it is differentiated; pointwise determinant one would not suffice. -/
theorem trace_inverse_second_matrixDZ
    {G : E → Matrix ι ι ℂ} {U : Set E} (hU : IsOpen U)
    (hG : ∀ i j, ContDiffOn ℝ 2 (fun y => G y i j) U)
    (hdet : ∀ y ∈ U, (G y).det = 1) {x : E} (hx : x ∈ U) (a b c d : E) :
    Matrix.trace ((G x)⁻¹ * matrixDZ a b (matrixDZ c d G) x) =
      Matrix.trace ((G x)⁻¹ * matrixDZ a b G x * (G x)⁻¹ * matrixDZ c d G x) := by
  have hGx i j := (hG i j).contDiffAt (hU.mem_nhds hx)
  have hGd : MatrixDifferentiableAt G x :=
    fun i j => (hGx i j).differentiableAt (by norm_num)
  have hdetx : (fun y => (G y).det) =ᶠ[𝓝 x] (fun _ => (1 : ℂ)) :=
    Filter.Eventually.mono (hU.mem_nhds hx) (fun y hy => hdet y hy)
  have hKd := inverse_matrix_differentiableAt_of_det_one hGd hdetx
  have hDd := matrixDZ_differentiableAt hGx c d
  have hfirst : (fun y => Matrix.trace ((G y)⁻¹ * matrixDZ c d G y)) =ᶠ[𝓝 x]
      (fun _ => (0 : ℂ)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact trace_inverse_matrixDZ_eq_zero
      (fun i j => ((hG i j).contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num))
      (Filter.Eventually.mono (hU.mem_nhds hy) (fun z hz => hdet z hz)) c d
  have hz : dz a b (fun y => Matrix.trace ((G y)⁻¹ * matrixDZ c d G y)) x = 0 := by
    rw [dz_congr_nhds hfirst a b]
    exact dz_const a b 0 x
  rw [dz_trace_at (matrix_product_differentiable hKd hDd) a b,
    matrixDZ_product a b hKd hDd,
    matrixDZ_inverse_of_det_one a b hGd hdetx,
    neg_mul, Matrix.trace_add, Matrix.trace_neg] at hz
  apply eq_of_sub_eq_zero
  simpa only [sub_eq_add_neg, add_comm] using hz

end CHS.Calculus
