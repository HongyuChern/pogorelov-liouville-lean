import CHS.Calculus.BasisHessian

/-!
# The scalar functions used to propagate the Schur kernel

The scalar pairing uses a fixed complex vector. Its linearization is the
pairing with the matrix linearization, and the actual Schur square supplies
the sign.
-/

set_option autoImplicit false
open scoped BigOperators ComplexOrder ContDiff Topology

namespace CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def matrixPair (G : E → Matrix ι ι ℂ) (ξ : ι → ℂ) (x : E) : ℂ :=
  star ξ ⬝ᵥ (G x).mulVec ξ

private theorem pair_eq_sum (G : E → Matrix ι ι ℂ) (ξ : ι → ℂ) (x : E) :
    matrixPair G ξ x = ∑ i, ∑ j, star (ξ i) * (G x i j * ξ j) := by
  simp [matrixPair, dotProduct, Matrix.mulVec, Finset.mul_sum]

theorem matrixPair_contDiffAt {G : E → Matrix ι ι ℂ} {x : E} {k : WithTop ℕ∞}
    (hG : ∀ i j, ContDiffAt ℝ k (fun y => G y i j) x) (ξ : ι → ℂ) :
    ContDiffAt ℝ k (matrixPair G ξ) x := by
  rw [show matrixPair G ξ = (fun y => ∑ i, ∑ j, star (ξ i) * (G y i j * ξ j)) by
    funext y; exact pair_eq_sum G ξ y]
  exact ContDiffAt.sum (fun i _ => ContDiffAt.sum (fun j _ =>
    contDiffAt_const.mul ((hG i j).mul contDiffAt_const)))

theorem dz_matrixPair {G : E → Matrix ι ι ℂ} {x : E}
    (hG : MatrixDifferentiableAt G x) (ξ : ι → ℂ) (a b : E) :
    dz a b (matrixPair G ξ) x = matrixPair (matrixDZ a b G) ξ x := by
  rw [show matrixPair G ξ = (fun y => ∑ i, ∑ j, star (ξ i) * (G y i j * ξ j)) by
    funext y; exact pair_eq_sum G ξ y, pair_eq_sum]
  rw [dz_sum_at (f := fun i y => ∑ j, star (ξ i) * (G y i j * ξ j))
    (fun i => DifferentiableAt.fun_sum (fun j _ => ((hG i j).mul_const _).const_mul _))]
  apply Finset.sum_congr rfl
  intro i _
  rw [dz_sum_at (f := fun j y => star (ξ i) * (G y i j * ξ j))
    (fun j => ((hG i j).mul_const _).const_mul _)]
  apply Finset.sum_congr rfl
  intro j _
  rw [dz_mul_at (differentiableAt_const _) ((hG i j).mul_const _),
    dz_mul_at (hG i j) (differentiableAt_const _)]
  simp only [dz_const, zero_mul, mul_zero, zero_add, add_zero, matrixDZ]

theorem dz_dz_matrixPair {G : E → Matrix ι ι ℂ} {U : Set E}
    (hU : IsOpen U) (hG : ∀ i j, ContDiffOn ℝ 2 (fun y => G y i j) U)
    {x : E} (hx : x ∈ U) (ξ : ι → ℂ) (a b c d : E) :
    dz c d (dz a b (matrixPair G ξ)) x =
      matrixPair (matrixDZ c d (matrixDZ a b G)) ξ x := by
  have hFirst : dz a b (matrixPair G ξ) =ᶠ[𝓝 x] matrixPair (matrixDZ a b G) ξ := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact dz_matrixPair
      (fun i j => ((hG i j).contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num))
      ξ a b
  rw [dz_congr_nhds hFirst c d]
  exact dz_matrixPair
    (matrixDZ_differentiableAt (fun i j => (hG i j).contDiffAt (hU.mem_nhds hx)) a b) ξ c d

theorem matrixPair_contract (W : Matrix ι ι ℂ) (F : ι → ι → Matrix ι ι ℂ)
    (ξ : ι → ℂ) :
    star ξ ⬝ᵥ (CHS.SchurContractionCore.contract W F).mulVec ξ =
      ∑ p, ∑ q, W q p * (star ξ ⬝ᵥ (F p q).mulVec ξ) := by
  simp only [CHS.SchurContractionCore.contract, Matrix.sum_mulVec, dotProduct_sum,
    Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

/-- The scalar linearized inequality for the fixed-vector Schur pairing. -/
theorem schurPair_linearized_nonpos {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : ι → E)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = 1)
    {x : E} (hx : x ∈ U) (hA : (complexHessian a b u x).PosDef) (ξ : ι → ℂ) :
    (∑ p, ∑ q, (complexHessian a b u x)⁻¹ q p *
      dz (a q) (-b q) (dz (a p) (b p) (matrixPair (schurHessian a b u) ξ)) x).re ≤ 0 := by
  have hM (i j : ι) : ContDiffOn ℝ 2 (fun y => schurHessian a b u y i j) U :=
    fun y hy => (schurHessian_contDiffAt_two hU hu a b hdet hy i j).contDiffWithinAt
  simp_rw [dz_dz_matrixPair hU hM hx ξ]
  unfold matrixPair
  rw [← matrixPair_contract]
  have h := (schurHessian_LM_nonpos hU hu a b hdet hx hA).re_dotProduct_nonneg ξ
  simpa only [RCLike.re_to_complex, Matrix.neg_mulVec, dotProduct_neg,
    Complex.neg_re, neg_nonneg] using h

theorem schurPair_nonneg {u : E → ℝ} {x : E} (a b : ι → E) (ξ : ι → ℂ)
    (hM : (schurHessian a b u x).PosSemidef) :
    0 ≤ (matrixPair (schurHessian a b u) ξ x).re :=
  hM.re_dotProduct_nonneg ξ

theorem schurPair_re_eq_zero_iff {u : E → ℝ} {x : E} (a b : ι → E) (ξ : ι → ℂ)
    (hM : (schurHessian a b u x).PosSemidef) :
    (matrixPair (schurHessian a b u) ξ x).re = 0 ↔
      (schurHessian a b u x).mulVec ξ = 0 := by
  let z := matrixPair (schurHessian a b u) ξ x
  have hz : 0 ≤ z := hM.dotProduct_mulVec_nonneg ξ
  have hIm : z.im = 0 := (Complex.nonneg_iff.mp hz).2.symm
  refine ⟨fun hr => (hM.dotProduct_mulVec_zero_iff ξ).mp ?_, fun hv => ?_⟩
  · apply Complex.ext
    · exact hr
    · exact hIm
  · unfold matrixPair
    rw [hv, dotProduct_zero, Complex.zero_re]


/-- The fixed-vector Schur pairing is a classical supersolution for the real
coefficient matrix of the complex linearization. -/
theorem schurPair_realHessian_nonpos {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : ι → E)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = 1)
    {x : E} (hx : x ∈ U) (hA : (complexHessian a b u x).PosDef) (ξ : ι → ℂ) :
    (∑ i, ∑ j, realLinearizationMatrix (complexHessian a b u x)⁻¹ i j *
      realBlockHessian a b (fun y => (matrixPair (schurHessian a b u) ξ y).re) x i j) ≤ 0 := by
  let g := matrixPair (schurHessian a b u) ξ
  have hg : ContDiffAt ℝ 2 g x :=
    matrixPair_contDiffAt (schurHessian_contDiffAt_two hU hu a b hdet hx) ξ
  have hre : ContDiffAt ℝ 2 (fun y => (g y).re) x :=
    Complex.reCLM.contDiff.contDiffAt.comp x hg
  have hreal : Set.EqOn (fun y => ((g y).re : ℂ)) g U := by
    intro y hy
    have hu2 : ContDiffAt ℝ 2 u y := (hu.contDiffAt (hU.mem_nhds hy)).of_le (by norm_num)
    have hIm : (g y).im = 0 :=
      (schurHessian_isHermitian hu2 a b).im_star_dotProduct_mulVec_self ξ
    exact Complex.ext rfl (by simpa using hIm.symm)
  rw [← realLinearizationMatrix_pairing hre a b _]
  change (∑ p, ∑ q, (complexHessian a b u x)⁻¹ q p *
    dz (a p) (b p) (dz (a q) (-b q) (fun y => ((g y).re : ℂ))) x).re ≤ 0
  have hentry (p q : ι) :
      dz (a p) (b p) (dz (a q) (-b q) (fun y => ((g y).re : ℂ))) x =
      dz (a q) (-b q) (dz (a p) (b p) g) x := by
    rw [dz_congr_on hU (fun y hy => dz_congr_on hU hreal (a q) (-b q) hy)
      (a p) (b p) hx]
    exact dz_comm_at hg _ _ _ _
  simp_rw [hentry]
  exact schurPair_linearized_nonpos hU hu a b hdet hx hA ξ

end CHS.Calculus
