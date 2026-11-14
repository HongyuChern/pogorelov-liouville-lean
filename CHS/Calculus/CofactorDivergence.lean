/- The Jacobi formula code adapts the PoincareLib determinant proof
   (Copyright (c) 2026 The PoincareLib contributors, Apache-2.0) through
   our KE-Ball project. CHS uses complex matrices with real derivatives and
   its own Wirtinger normalization. See THIRD_PARTY.md and LICENSES/. -/
import CHS.Calculus.MatrixRegularity

/-!
# Jacobi's formula and cofactor divergence for finite-order matrix fields

Adapted from the bundled KE-Ball `ComplexDeterminant` and `CofactorDivergence`
proofs. Jacobi's formula is derived using row multilinearity over ℂ and
restriction of scalars to ℝ. The field derivatives use CHS's Wirtinger
normalization. Cofactor divergence uses the row-commutation identity.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ContDiff Matrix Matrix.Norms.Elementwise Topology

namespace CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private noncomputable def complexDetMultilinear :
    ContinuousMultilinearMap ℂ (fun _ : ι => ι → ℂ) ℂ where
  toMultilinearMap := Matrix.detRowAlternating.toMultilinearMap
  cont := continuous_id.matrix_det

private theorem complexDetMultilinear_linearDeriv (A B : Matrix ι ι ℂ) :
    ((complexDetMultilinear (ι := ι)).linearDeriv A) B = Matrix.trace (Matrix.adjugate A * B) := by
  change ((complexDetMultilinear (ι := ι)).linearDeriv (fun i j => A i j)) (fun i j => B i j) = _
  rw [ContinuousMultilinearMap.linearDeriv_apply]
  change (∑ i, (A.updateRow i (B i)).det) = _
  trans ∑ i, ∑ j, A.adjugate j i * B i j
  · apply Finset.sum_congr rfl
    intro i _
    rw [← Matrix.cramer_transpose_apply, Matrix.cramer_eq_adjugate_mulVec,
      ← Matrix.adjugate_transpose]
    rfl
  · rw [Finset.sum_comm]
    rfl

theorem fderiv_real_complex_det (A B : Matrix ι ι ℂ) :
    fderiv ℝ Matrix.det A B = Matrix.trace (Matrix.adjugate A * B) := by
  have h := ((complexDetMultilinear (ι := ι)).hasFDerivAt A).restrictScalars ℝ
  change HasFDerivAt (fun a : Matrix ι ι ℂ => a.det)
    (((complexDetMultilinear (ι := ι)).linearDeriv A).restrictScalars ℝ) A at h
  rw [h.fderiv]
  exact complexDetMultilinear_linearDeriv A B

theorem fderiv_real_complex_det_invertible (A B : Matrix ι ι ℂ)
    (hA : IsUnit A.det) :
    fderiv ℝ Matrix.det A B = A.det * Matrix.trace (A⁻¹ * B) := by
  rw [fderiv_real_complex_det]
  have hadj : Matrix.adjugate A = A.det • A⁻¹ := by
    rw [Matrix.inv_def, smul_smul, Ring.mul_inverse_cancel _ hA, one_smul]
  rw [hadj, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]

/-- Jacobi's formula for a real directional derivative of a complex matrix field. -/
lemma rd_det_field {G : E → Matrix ι ι ℂ} {x : E}
    (hG : ∀ i j, DifferentiableAt ℝ (fun y => G y i j) x) (v : E) :
    rd v (fun y => (G y).det) x =
      ∑ i, ∑ j, (G x).adjugate j i * rd v (fun y => G y i j) x := by
  have hdG : HasFDerivAt G
      (ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j =>
        fderiv ℝ (fun y => G y i j) x) x :=
    hasFDerivAt_pi.mpr fun i => hasFDerivAt_pi.mpr fun j => (hG i j).hasFDerivAt
  have hdet : DifferentiableAt ℝ Matrix.det (G x) :=
    (complex_det_contDiff (k := 1)).contDiffAt.differentiableAt (by norm_num)
  have h := hdet.hasFDerivAt.comp x hdG
  change HasFDerivAt (fun y => (G y).det)
    ((fderiv ℝ Matrix.det (G x)).comp
      (ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j =>
        fderiv ℝ (fun y => G y i j) x)) x at h
  rw [rd, h.fderiv, ContinuousLinearMap.comp_apply]
  change fderiv ℝ Matrix.det (G x)
    (fun i j => fderiv ℝ (fun y => G y i j) x v) = _
  rw [fderiv_real_complex_det]
  simp only [Matrix.trace]
  rw [Finset.sum_comm]
  rfl

/-- Jacobi's formula with precisely the paper's Wirtinger normalization. -/
lemma dz_det_field {G : E → Matrix ι ι ℂ} {x : E}
    (hG : ∀ i j, DifferentiableAt ℝ (fun y => G y i j) x) (a b : E) :
    dz a b (fun y => (G y).det) x =
      ∑ i, ∑ j, (G x).adjugate j i * dz a b (fun y => G y i j) x := by
  unfold dz
  rw [rd_det_field hG, rd_det_field hG]
  calc
    _ = ∑ i, ∑ j, (2 : ℂ)⁻¹ *
        ((G x).adjugate j i * rd a (fun y => G y i j) x -
          Complex.I * ((G x).adjugate j i * rd b (fun y => G y i j) x)) := by
      simp only [Finset.mul_sum, Finset.sum_sub_distrib, mul_sub]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- The differentiated adjugate identity for a matrix field with commuting rows. -/
theorem cofactor_divergence_of_commuting_rows {G : E → Matrix ι ι ℂ} {x : E}
    (a b : ι → E)
    (hG : ∀ i j, DifferentiableAt ℝ (fun y => G y i j) x)
    (hcomm : ∀ i r k,
      dz (a i) (b i) (fun y => G y r k) x =
        dz (a r) (b r) (fun y => G y i k) x)
    (hunit : IsUnit (G x).det) (j : ι) :
    (∑ i, dz (a i) (b i) (fun y => (G y).adjugate j i) x) = 0 := by
  let V : ι → ℂ := fun k =>
    ∑ i, dz (a i) (b i) (fun y => (G y).adjugate k i) x
  have hC := field_adjugate_differentiableAt hG
  have hdprod (r i : ι) :
      (∑ k, (dz (a i) (b i) (fun y => G y r k) x * (G x).adjugate k i +
        G x r k * dz (a i) (b i) (fun y => (G y).adjugate k i) x)) =
      if r = i then dz (a i) (b i) (fun y => (G y).det) x else 0 := by
    have hprod : (fun y => ∑ k, G y r k * (G y).adjugate k i) =
        if r = i then (fun y => (G y).det) else (fun _ : E => (0 : ℂ)) := by
      funext y
      have heq := congrArg (fun M : Matrix ι ι ℂ => M r i) (Matrix.mul_adjugate (G y))
      by_cases hri : r = i
      · simpa [hri, Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply] using heq
      · simpa [hri, Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply] using heq
    calc
      _ = dz (a i) (b i) (fun y => ∑ k, G y r k * (G y).adjugate k i) x := by
        rw [dz_sum_at
          (f := fun k y => G y r k * (G y).adjugate k i)
          (fun k => (hG r k).fun_mul (hC k i))]
        apply Finset.sum_congr rfl
        intro k _
        exact (dz_mul_at (hG r k) (hC k i) (a i) (b i)).symm
      _ = _ := by
        rw [hprod]
        split_ifs <;> simp [dz, rd]
  have hrow : (G x) *ᵥ V = 0 := by
    funext r
    have hfirst :
        (∑ i, ∑ k, dz (a i) (b i) (fun y => G y r k) x * (G x).adjugate k i) =
          dz (a r) (b r) (fun y => (G y).det) x := by
      rw [dz_det_field hG]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      rw [hcomm i r k, mul_comm]
    have hsum :
        (∑ i, ∑ k, (dz (a i) (b i) (fun y => G y r k) x * (G x).adjugate k i +
          G x r k * dz (a i) (b i) (fun y => (G y).adjugate k i) x)) =
          dz (a r) (b r) (fun y => (G y).det) x := by
      calc
        _ = ∑ i, if r = i then dz (a i) (b i) (fun y => (G y).det) x else 0 :=
          Finset.sum_congr rfl (fun i _ => hdprod r i)
        _ = _ := by simp
    simp only [Finset.sum_add_distrib] at hsum
    rw [hfirst] at hsum
    have hzero :
        (∑ i, ∑ k, G x r k * dz (a i) (b i) (fun y => (G y).adjugate k i) x) = 0 :=
      add_left_cancel (hsum.trans (add_zero _).symm)
    change (∑ k, G x r k * (∑ i,
      dz (a i) (b i) (fun y => (G y).adjugate k i) x)) = 0
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact hzero
  have hV := congrArg (fun w : ι → ℂ => (G x)⁻¹ *ᵥ w) hrow
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit,
    Matrix.one_mulVec, Matrix.mulVec_zero] at hV
  exact congrFun hV j

/-- On the local determinant-one locus the adjugate is the actual inverse. -/
theorem inverse_divergence_of_commuting_rows {G : E → Matrix ι ι ℂ} {x : E}
    (a b : ι → E) (hG : MatrixDifferentiableAt G x)
    (hcomm : ∀ i r k,
      dz (a i) (b i) (fun y => G y r k) x =
        dz (a r) (b r) (fun y => G y i k) x)
    (hdet : (fun y => (G y).det) =ᶠ[𝓝 x] (fun _ => (1 : ℂ))) (j : ι) :
    (∑ i, dz (a i) (b i) (fun y => (G y)⁻¹ j i) x) = 0 := by
  have hx : (G x).det = 1 := hdet.eq_of_nhds
  calc
    _ = ∑ i, dz (a i) (b i) (fun y => (G y).adjugate j i) x := by
      apply Finset.sum_congr rfl
      intro i _
      apply dz_congr_nhds _ (a i) (b i)
      exact hdet.mono fun y hy =>
        congrArg (fun M : Matrix ι ι ℂ => M j i) (inv_eq_adjugate_of_det_one (G y) hy)
    _ = 0 := cofactor_divergence_of_commuting_rows a b hG hcomm (hx ▸ isUnit_one) j

end CHS.Calculus
