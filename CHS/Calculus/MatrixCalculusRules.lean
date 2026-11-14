import CHS.Calculus.FiniteWirtinger

/-!
# Entrywise finite-dimensional matrix differentiation

S004 REIMPLEMENTATION. The original S002 file was not recoverable. This file
supplies actual, proved entrywise derivative operations, and the determinant-one
inverse identities required by the recovered `MatrixRegularity.lean`.
It is not a claim that the unavailable Schur-contraction/PDE code has been
recovered. Status: candidate source; Lean has not been run in this environment.
-/

set_option autoImplicit false
open scoped BigOperators Topology

namespace CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Regularity of the actual entries, not independent derivative data. -/
def MatrixDifferentiableAt (G : E → Matrix ι ι ℂ) (x : E) : Prop :=
  ∀ i j, DifferentiableAt ℝ (fun y => G y i j) x

/-- The actual entrywise Wirtinger derivative. -/
noncomputable def matrixDZ (a b : E) (G : E → Matrix ι ι ℂ) (x : E) :
    Matrix ι ι ℂ := fun i j => dz a b (fun y => G y i j) x

noncomputable def vectorDZ (a b : E) (v : E → (ι → ℂ)) (x : E) : ι → ℂ :=
  fun i => dz a b (fun y => v y i) x

lemma inv_eq_adjugate_of_det_one (A : Matrix ι ι ℂ) (h : A.det = 1) :
    A⁻¹ = A.adjugate := by
  simp [Matrix.inv_def, h]

lemma inverse_mul_self_of_det_one (A : Matrix ι ι ℂ) (h : A.det = 1) :
    A⁻¹ * A = 1 := by
  exact Matrix.nonsing_inv_mul A (by rw [h]; exact isUnit_one)

lemma self_mul_inverse_of_det_one (A : Matrix ι ι ℂ) (h : A.det = 1) :
    A * A⁻¹ = 1 := by
  exact Matrix.mul_nonsing_inv A (by rw [h]; exact isUnit_one)

lemma rd_mul_at {f g : E → ℂ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (v : E) :
    rd v (fun y => f y * g y) x = rd v f x * g x + f x * rd v g x := by
  simp [rd, fderiv_fun_mul hf hg, smul_eq_mul] <;> ring

lemma rd_sum_at {f : ι → E → ℂ} {x : E}
    (hf : ∀ i, DifferentiableAt ℝ (f i) x) (v : E) :
    rd v (fun y => ∑ i, f i y) x = ∑ i, rd v (f i) x := by
  simp [rd, fderiv_fun_sum (fun i _ => hf i)]

lemma dz_mul_at {f g : E → ℂ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (a b : E) :
    dz a b (fun y => f y * g y) x = dz a b f x * g x + f x * dz a b g x := by
  unfold dz
  rw [rd_mul_at hf hg, rd_mul_at hf hg]
  ring

lemma dz_sum_at {f : ι → E → ℂ} {x : E}
    (hf : ∀ i, DifferentiableAt ℝ (f i) x) (a b : E) :
    dz a b (fun y => ∑ i, f i y) x = ∑ i, dz a b (f i) x := by
  unfold dz
  rw [rd_sum_at hf, rd_sum_at hf]
  simp only [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]

lemma dz_const (a b : E) (c : ℂ) (x : E) :
    dz a b (fun _ : E => c) x = 0 := by
  simp [dz, rd]

lemma matrix_product_differentiable {G H : E → Matrix ι ι ℂ} {x : E}
    (hG : MatrixDifferentiableAt G x) (hH : MatrixDifferentiableAt H x) :
    MatrixDifferentiableAt (fun y => G y * H y) x := by
  intro i j
  change DifferentiableAt ℝ (fun y => ∑ k, G y i k * H y k j) x
  exact DifferentiableAt.fun_sum (fun k _ => (hG i k).mul (hH k j))

lemma matrixDZ_product (a b : E) {G H : E → Matrix ι ι ℂ} {x : E}
    (hG : MatrixDifferentiableAt G x) (hH : MatrixDifferentiableAt H x) :
    matrixDZ a b (fun y => G y * H y) x =
      matrixDZ a b G x * H x + G x * matrixDZ a b H x := by
  ext i j
  change dz a b (fun y => ∑ k, G y i k * H y k j) x = _
  have hentry (k : ι) : DifferentiableAt ℝ (fun y => G y i k * H y k j) x :=
    (hG i k).mul (hH k j)
  rw [dz_sum_at hentry]
  change (∑ k, dz a b (fun y => G y i k * H y k j) x) =
    (∑ k, dz a b (fun y => G y i k) x * H x k j) +
      (∑ k, G x i k * dz a b (fun y => H y k j) x)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  exact dz_mul_at (hG i k) (hH k j) a b

lemma matrixDZ_differentiableAt {G : E → Matrix ι ι ℂ} {x : E}
    (hG : ∀ i j, ContDiffAt ℝ 2 (fun y => G y i j) x) (a b : E) :
    MatrixDifferentiableAt (matrixDZ a b G) x := by
  intro i j
  exact (dz_contDiffAt_one (hG i j) a b).differentiableAt (by norm_num)

lemma vectorDZ_const (a b : E) (v : ι → ℂ) (x : E) :
    vectorDZ a b (fun _ : E => v) x = 0 := by
  funext i
  exact dz_const a b (v i) x

lemma vectorDZ_congr_nhds (a b : E) {f g : E → (ι → ℂ)} {x : E}
    (h : f =ᶠ[𝓝 x] g) : vectorDZ a b f x = vectorDZ a b g x := by
  funext i
  exact dz_congr_nhds (h.mono fun y hy => congrFun hy i) a b

lemma vectorDZ_mulVec_const (a b : E) {G : E → Matrix ι ι ℂ} {x : E}
    (hG : MatrixDifferentiableAt G x) (ξ : ι → ℂ) :
    vectorDZ a b (fun y => (G y).mulVec ξ) x = (matrixDZ a b G x).mulVec ξ := by
  funext i
  change dz a b (fun y => ∑ j, G y i j * ξ j) x =
    ∑ j, dz a b (fun y => G y i j) x * ξ j
  rw [dz_sum_at (fun j => (hG i j).mul_const (ξ j))]
  apply Finset.sum_congr rfl
  intro j _
  rw [dz_mul_at (hG i j) (differentiableAt_const (ξ j)), dz_const,
    mul_zero, add_zero]

end CHS.Calculus
