import CHS.Calculus.MatrixRegularity
import CHS.Algebra.SchurContractionCore

/-!
# Actual matrix-field Schur derivatives and the weighted LM contraction

S005 REIMPLEMENTATION, not a recovery of the missing S002 file.
All derivatives here are the actual `matrixDZ` built from `fderiv`.
C2 entries and local determinant one give the inverse regularity.

`schurField_LM_square` is a CONDITIONAL intermediate theorem. Its four explicit
inputs are the differentiated equations (LA cancellation, compensated
contraction, return contraction, and adjoint derivative). The final two helper
lemmas discharge the last/compensated algebra once the native equations are
proved. This file DOES NOT prove paper Lemma 2.3 for a potential: the native
C4 Hessian representation and differentiated Monge-Ampere identities remain
open and the preserved S002 caller stays out of the production import tree.

STATUS: proof bodies saved; no Lean compilation in the Chat sandbox.
-/

set_option autoImplicit false
open scoped BigOperators ContDiff Topology

namespace CHS.Calculus

open CHS.SchurContractionCore

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma dz_sub_at {f g : E → ℂ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (a b : E) :
    dz a b (fun y => f y - g y) x = dz a b f x - dz a b g x := by
  unfold dz
  rw [rd_sub_at hf hg, rd_sub_at hf hg]
  ring

lemma matrix_sub_differentiable {F G : E → Matrix ι ι ℂ} {x : E}
    (hF : MatrixDifferentiableAt F x) (hG : MatrixDifferentiableAt G x) :
    MatrixDifferentiableAt (fun y => F y - G y) x := by
  intro i j
  exact (hF i j).sub (hG i j)

lemma matrixDZ_sub (a b : E) {F G : E → Matrix ι ι ℂ} {x : E}
    (hF : MatrixDifferentiableAt F x) (hG : MatrixDifferentiableAt G x) :
    matrixDZ a b (fun y => F y - G y) x = matrixDZ a b F x - matrixDZ a b G x := by
  ext i j
  exact dz_sub_at (hF i j) (hG i j) a b

lemma matrixDZ_const (a b : E) (C : Matrix ι ι ℂ) (x : E) :
    matrixDZ a b (fun _ : E => C) x = 0 := by
  ext i j
  exact dz_const a b (C i j) x

lemma matrixDZ_congr_nhds (a b : E) {F G : E → Matrix ι ι ℂ} {x : E}
    (h : F =ᶠ[𝓝 x] G) : matrixDZ a b F x = matrixDZ a b G x := by
  ext i j
  exact dz_congr_nhds (h.mono fun y hy => congrFun (congrFun hy i) j) a b

/-- Local determinant one is enough; inverse differentiability is derived. -/
lemma matrixDZ_inverse_of_det_one (a b : E) {H : E → Matrix ι ι ℂ} {x : E}
    (hH : MatrixDifferentiableAt H x)
    (hdet : (fun y => (H y).det) =ᶠ[𝓝 x] (fun _ => (1 : ℂ))) :
    matrixDZ a b (fun y => (H y)⁻¹) x =
      -((H x)⁻¹ * matrixDZ a b H x * (H x)⁻¹) := by
  have hK := inverse_matrix_differentiableAt_of_det_one hH hdet
  have hprod : (fun y => H y * (H y)⁻¹) =ᶠ[𝓝 x] (fun _ => 1) := by
    filter_upwards [hdet] with y hy
    exact self_mul_inverse_of_det_one (H y) hy
  have hd : matrixDZ a b H x * (H x)⁻¹ +
      H x * matrixDZ a b (fun y => (H y)⁻¹) x = 0 := by
    calc
      _ = matrixDZ a b (fun y => H y * (H y)⁻¹) x :=
        (matrixDZ_product a b hH hK).symm
      _ = matrixDZ a b (fun _ : E => (1 : Matrix ι ι ℂ)) x :=
        matrixDZ_congr_nhds a b hprod
      _ = 0 := matrixDZ_const a b 1 x
  exact inverse_derivative_of_product_zero (H x) (H x)⁻¹
    (matrixDZ a b H x) (matrixDZ a b (fun y => (H y)⁻¹) x)
    (inverse_mul_self_of_det_one (H x) hdet.self_of_nhds) hd

noncomputable def schurField (A B C H : E → Matrix ι ι ℂ) (x : E) :
    Matrix ι ι ℂ := A x - B x * (H x)⁻¹ * C x

noncomputable def compensatedField (a b : ι → E)
    (B H : E → Matrix ι ι ℂ) (p : ι) (x : E) : Matrix ι ι ℂ :=
  matrixDZ (a p) (b p) B x - B x * (H x)⁻¹ * matrixDZ (a p) (b p) H x

noncomputable def returnField (H C : E → Matrix ι ι ℂ) (x : E) :
    Matrix ι ι ℂ := (H x)⁻¹ * C x

noncomputable def inverseDerivativeField (a b : ι → E)
    (H C : E → Matrix ι ι ℂ) (p : ι) (x : E) : Matrix ι ι ℂ :=
  (H x)⁻¹ * matrixDZ (a p) (b p) C x

lemma schurField_contDiffAt_two {A B C H : E → Matrix ι ι ℂ} {x : E}
    (hA : ∀ i j, ContDiffAt ℝ 2 (fun y => A y i j) x)
    (hB : ∀ i j, ContDiffAt ℝ 2 (fun y => B y i j) x)
    (hC : ∀ i j, ContDiffAt ℝ 2 (fun y => C y i j) x)
    (hH : ∀ i j, ContDiffAt ℝ 2 (fun y => H y i j) x)
    (hdet : (fun y => (H y).det) =ᶠ[𝓝 x] (fun _ => (1 : ℂ))) (i j : ι) :
    ContDiffAt ℝ 2 (fun y => schurField A B C H y i j) x := by
  have hK := field_inverse_contDiffAt_of_det_one hH hdet
  exact (hA i j).sub (matrix_product_contDiffAt (matrix_product_contDiffAt hB hK) hC i j)

lemma returnField_contDiffAt_two {H C : E → Matrix ι ι ℂ} {x : E}
    (hH : ∀ i j, ContDiffAt ℝ 2 (fun y => H y i j) x)
    (hC : ∀ i j, ContDiffAt ℝ 2 (fun y => C y i j) x)
    (hdet : (fun y => (H y).det) =ᶠ[𝓝 x] (fun _ => (1 : ℂ))) (i j : ι) :
    ContDiffAt ℝ 2 (fun y => returnField H C y i j) x := by
  exact matrix_product_contDiffAt (field_inverse_contDiffAt_of_det_one hH hdet) hC i j

lemma inverseDerivativeField_contDiffAt_one (a b : ι → E)
    {H C : E → Matrix ι ι ℂ} {x : E}
    (hH : ∀ i j, ContDiffAt ℝ 2 (fun y => H y i j) x)
    (hC : ∀ i j, ContDiffAt ℝ 2 (fun y => C y i j) x)
    (hdet : (fun y => (H y).det) =ᶠ[𝓝 x] (fun _ => (1 : ℂ))) (p i j : ι) :
    ContDiffAt ℝ 1 (fun y => inverseDerivativeField a b H C p y i j) x := by
  exact matrix_product_contDiffAt
    (fun r s => (field_inverse_contDiffAt_of_det_one hH hdet r s).of_le (by norm_num))
    (fun r s => dz_contDiffAt_one (hC r s) (a p) (b p)) i j

lemma compensatedField_contDiffAt_one (a b : ι → E)
    {B H : E → Matrix ι ι ℂ} {x : E}
    (hB : ∀ i j, ContDiffAt ℝ 2 (fun y => B y i j) x)
    (hH : ∀ i j, ContDiffAt ℝ 2 (fun y => H y i j) x)
    (hdet : (fun y => (H y).det) =ᶠ[𝓝 x] (fun _ => (1 : ℂ))) (p i j : ι) :
    ContDiffAt ℝ 1 (fun y => compensatedField a b B H p y i j) x := by
  exact (dz_contDiffAt_one (hB i j) (a p) (b p)).sub
    (matrix_product_contDiffAt
      (matrix_product_contDiffAt
        (fun r s => (hB r s).of_le (by norm_num))
        (fun r s => (field_inverse_contDiffAt_of_det_one hH hdet r s).of_le (by norm_num)))
      (fun r s => dz_contDiffAt_one (hH r s) (a p) (b p)) i j)

/-- Equation (2.12), for actual matrix fields at a differentiability point. -/
lemma matrixDZ_schurField (a b : ι → E) (p : ι)
    {A B C H : E → Matrix ι ι ℂ} {x : E}
    (hA : MatrixDifferentiableAt A x) (hB : MatrixDifferentiableAt B x)
    (hC : MatrixDifferentiableAt C x) (hH : MatrixDifferentiableAt H x)
    (hdet : (fun y => (H y).det) =ᶠ[𝓝 x] (fun _ => (1 : ℂ))) :
    matrixDZ (a p) (b p) (schurField A B C H) x =
      matrixDZ (a p) (b p) A x -
        compensatedField a b B H p x * returnField H C x -
        B x * inverseDerivativeField a b H C p x := by
  have hK := inverse_matrix_differentiableAt_of_det_one hH hdet
  have hBK := matrix_product_differentiable hB hK
  change matrixDZ (a p) (b p) (fun y => A y - (B y * (H y)⁻¹) * C y) x = _
  rw [matrixDZ_sub (a p) (b p) hA (matrix_product_differentiable hBK hC),
    matrixDZ_product (a p) (b p) hBK hC,
    matrixDZ_product (a p) (b p) hB hK]
  have h := schur_first_derivative_algebra
    (matrixDZ (a p) (b p) A x) (B x) (C x) (H x)⁻¹
    (matrixDZ (a p) (b p) B x) (matrixDZ (a p) (b p) C x)
    (matrixDZ (a p) (b p) H x) (matrixDZ (a p) (b p) (fun y => (H y)⁻¹) x)
    (matrixDZ_inverse_of_det_one (a p) (b p) hH hdet)
  simpa only [compensatedField, returnField, inverseDerivativeField, mul_assoc] using h

/-- Product-rule expansion before any PDE cancellation. The first-derivative
identity is established on a neighbourhood before it is differentiated. -/
lemma schurField_mixed_expansion (a b : ι → E)
    {A B C H : E → Matrix ι ι ℂ} {U : Set E} (hU : IsOpen U)
    (hA : ∀ i j, ContDiffOn ℝ 2 (fun y => A y i j) U)
    (hB : ∀ i j, ContDiffOn ℝ 2 (fun y => B y i j) U)
    (hC : ∀ i j, ContDiffOn ℝ 2 (fun y => C y i j) U)
    (hH : ∀ i j, ContDiffOn ℝ 2 (fun y => H y i j) U)
    (hdet : ∀ y ∈ U, (H y).det = 1) {x : E} (hx : x ∈ U) (p q : ι) :
    matrixDZ (a q) (-b q) (matrixDZ (a p) (b p) (schurField A B C H)) x =
      matrixDZ (a q) (-b q) (matrixDZ (a p) (b p) A) x -
      matrixDZ (a q) (-b q) (compensatedField a b B H p) x * returnField H C x -
      compensatedField a b B H p x * matrixDZ (a q) (-b q) (returnField H C) x -
      matrixDZ (a q) (-b q) B x * inverseDerivativeField a b H C p x -
      B x * matrixDZ (a q) (-b q) (inverseDerivativeField a b H C p) x := by
  have hAx i j := (hA i j).contDiffAt (hU.mem_nhds hx)
  have hBx i j := (hB i j).contDiffAt (hU.mem_nhds hx)
  have hCx i j := (hC i j).contDiffAt (hU.mem_nhds hx)
  have hHx i j := (hH i j).contDiffAt (hU.mem_nhds hx)
  have hdetx : (fun y => (H y).det) =ᶠ[𝓝 x] (fun _ => (1 : ℂ)) :=
    Filter.Eventually.mono (hU.mem_nhds hx) fun y hy => hdet y hy
  have hDA := matrixDZ_differentiableAt hAx (a p) (b p)
  have hBd : MatrixDifferentiableAt B x :=
    fun i j => (hBx i j).differentiableAt (by norm_num)
  have hEd : MatrixDifferentiableAt (compensatedField a b B H p) x :=
    fun i j => (compensatedField_contDiffAt_one a b hBx hHx hdetx p i j).differentiableAt (by norm_num)
  have hRd : MatrixDifferentiableAt (returnField H C) x :=
    fun i j => (returnField_contDiffAt_two hHx hCx hdetx i j).differentiableAt (by norm_num)
  have hTd : MatrixDifferentiableAt (inverseDerivativeField a b H C p) x :=
    fun i j => (inverseDerivativeField_contDiffAt_one a b hHx hCx hdetx p i j).differentiableAt (by norm_num)
  have hfirst : matrixDZ (a p) (b p) (schurField A B C H) =ᶠ[𝓝 x]
      (fun y => matrixDZ (a p) (b p) A y -
        compensatedField a b B H p y * returnField H C y -
        B y * inverseDerivativeField a b H C p y) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact matrixDZ_schurField a b p
      (fun i j => ((hA i j).contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num))
      (fun i j => ((hB i j).contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num))
      (fun i j => ((hC i j).contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num))
      (fun i j => ((hH i j).contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num))
      (Filter.Eventually.mono (hU.mem_nhds hy) fun z hz => hdet z hz)
  rw [matrixDZ_congr_nhds (a q) (-b q) hfirst]
  rw [matrixDZ_sub (a q) (-b q)
      (matrix_sub_differentiable hDA (matrix_product_differentiable hEd hRd))
      (matrix_product_differentiable hBd hTd),
    matrixDZ_sub (a q) (-b q) hDA (matrix_product_differentiable hEd hRd),
    matrixDZ_product (a q) (-b q) hEd hRd,
    matrixDZ_product (a q) (-b q) hBd hTd]
  abel

/-- Conditional LM theorem with genuine derivatives. The four equations
below must be proved for the actual Hessian; none is silently assumed as data. -/
theorem schurField_LM_square (a b : ι → E) (W : Matrix ι ι ℂ)
    {A B C H : E → Matrix ι ι ℂ} {U : Set E} (hU : IsOpen U)
    (hA : ∀ i j, ContDiffOn ℝ 2 (fun y => A y i j) U)
    (hB : ∀ i j, ContDiffOn ℝ 2 (fun y => B y i j) U)
    (hC : ∀ i j, ContDiffOn ℝ 2 (fun y => C y i j) U)
    (hH : ∀ i j, ContDiffOn ℝ 2 (fun y => H y i j) U)
    (hdet : ∀ y ∈ U, (H y).det = 1) {x : E} (hx : x ∈ U)
    (hLA : contract W (fun p q => matrixDZ (a q) (-b q) (matrixDZ (a p) (b p) A) x) =
      contract W (fun p q => matrixDZ (a q) (-b q) B x * (H x)⁻¹ * matrixDZ (a p) (b p) C x))
    (hComp : contract W (fun p q => matrixDZ (a q) (-b q) (compensatedField a b B H p) x) = 0)
    (hReturnDiv : contract W (fun p q => matrixDZ (a q) (-b q) (inverseDerivativeField a b H C p) x) = 0)
    (hReturnAdjoint : ∀ q, matrixDZ (a q) (-b q) (returnField H C) x =
      (H x)⁻¹ * (compensatedField a b B H q x).conjTranspose) :
    contract W (fun p q =>
      matrixDZ (a q) (-b q) (matrixDZ (a p) (b p) (schurField A B C H)) x) =
      -contract W (fun p q => compensatedField a b B H p x * (H x)⁻¹ *
        (compensatedField a b B H q x).conjTranspose) := by
  have hexp := schurField_mixed_expansion a b hU hA hB hC hH hdet hx
  simp_rw [hexp]
  apply schur_contraction_cancel W (B x) (H x)⁻¹ (returnField H C x)
    (fun p => compensatedField a b B H p x)
    (fun q => matrixDZ (a q) (-b q) B x)
    (fun p => inverseDerivativeField a b H C p x)
    (fun q => matrixDZ (a q) (-b q) (returnField H C) x)
    (fun p q => matrixDZ (a q) (-b q) (matrixDZ (a p) (b p) A) x)
    (fun p q => matrixDZ (a q) (-b q) (compensatedField a b B H p) x)
    (fun p q => matrixDZ (a q) (-b q) (inverseDerivativeField a b H C p) x)
  · simpa only [inverseDerivativeField, mul_assoc] using hLA
  · exact hComp
  · exact hReturnDiv
  · exact hReturnAdjoint

/-- The independent compensated-divergence reduction in equation (2.11). -/
theorem compensatedField_contraction_zero (a b : ι → E) (W : Matrix ι ι ℂ)
    {B H : E → Matrix ι ι ℂ} {x : E}
    (hB : ∀ i j, ContDiffAt ℝ 2 (fun y => B y i j) x)
    (hH : ∀ i j, ContDiffAt ℝ 2 (fun y => H y i j) x)
    (hdet : (fun y => (H y).det) =ᶠ[𝓝 x] (fun _ => (1 : ℂ)))
    (hLB : contract W (fun p q => matrixDZ (a q) (-b q) (matrixDZ (a p) (b p) B) x) =
      contract W (fun p q => matrixDZ (a q) (-b q) B x * (H x)⁻¹ * matrixDZ (a p) (b p) H x))
    (hDiv : contract W (fun p q => matrixDZ (a q) (-b q) (inverseDerivativeField a b H H p) x) = 0) :
    contract W (fun p q => matrixDZ (a q) (-b q) (compensatedField a b B H p) x) = 0 := by
  have hBd : MatrixDifferentiableAt B x :=
    fun i j => (hB i j).differentiableAt (by norm_num)
  have hQd (p : ι) : MatrixDifferentiableAt (inverseDerivativeField a b H H p) x :=
    fun i j => (inverseDerivativeField_contDiffAt_one a b hH hH hdet p i j).differentiableAt (by norm_num)
  have hexp (p q : ι) : matrixDZ (a q) (-b q) (compensatedField a b B H p) x =
      matrixDZ (a q) (-b q) (matrixDZ (a p) (b p) B) x -
      matrixDZ (a q) (-b q) B x * inverseDerivativeField a b H H p x -
      B x * matrixDZ (a q) (-b q) (inverseDerivativeField a b H H p) x := by
    have hfield : compensatedField a b B H p =
        (fun y => matrixDZ (a p) (b p) B y - B y * inverseDerivativeField a b H H p y) := by
      funext y
      simp only [compensatedField, inverseDerivativeField, mul_assoc]
    rw [hfield,
      matrixDZ_sub (a q) (-b q) (matrixDZ_differentiableAt hB (a p) (b p))
        (matrix_product_differentiable hBd (hQd p)),
      matrixDZ_product (a q) (-b q) hBd (hQd p)]
    abel
  simp_rw [hexp]
  apply compensated_contraction_cancel W (B x)
    (fun q => matrixDZ (a q) (-b q) B x)
    (fun p => inverseDerivativeField a b H H p x)
    (fun p q => matrixDZ (a q) (-b q) (matrixDZ (a p) (b p) B) x)
    (fun p q => matrixDZ (a q) (-b q) (inverseDerivativeField a b H H p) x)
  · simpa only [inverseDerivativeField, mul_assoc] using hLB
  · exact hDiv

lemma rd_star (v : E) (f : E → ℂ) (x : E) :
    rd v (fun y => star (f y)) x = star (rd v f x) := by
  exact DFunLike.congr_fun (fderiv_star (𝕜 := ℝ) (f := f) (x := x)) v

lemma rd_neg_direction (v : E) (f : E → ℂ) (x : E) :
    rd (-v) f x = -rd v f x := by
  simp [rd]

/-- Complex conjugation exchanges the two Wirtinger directions. -/
lemma dz_star_flip (a b : E) (f : E → ℂ) (x : E) :
    dz a (-b) (fun y => star (f y)) x = star (dz a b f x) := by
  unfold dz
  rw [rd_star, rd_neg_direction, rd_star]
  simp [Complex.star_def] <;> ring

lemma matrixDZ_conjTranspose (a b : E) (G : E → Matrix ι ι ℂ) (x : E) :
    matrixDZ a (-b) (fun y => (G y).conjTranspose) x =
      (matrixDZ a b G x).conjTranspose := by
  ext i j
  exact dz_star_flip a b (fun y => G y j i) x

/-- The adjoint-return derivative in equation (2.8), from genuine local
adjoint identities and determinant one. There is no target-valued premise. -/
theorem matrixDZ_inverse_return (a b : ι → E)
    {B C H : E → Matrix ι ι ℂ} {x : E} {q : ι}
    (hC : MatrixDifferentiableAt C x) (hH : MatrixDifferentiableAt H x)
    (hdet : (fun y => (H y).det) =ᶠ[𝓝 x] (fun _ => (1 : ℂ)))
    (hCstar : C =ᶠ[𝓝 x] (fun y => (B y).conjTranspose))
    (hHstar : H =ᶠ[𝓝 x] (fun y => (H y).conjTranspose)) :
    matrixDZ (a q) (-b q) (returnField H C) x =
      (H x)⁻¹ * (compensatedField a b B H q x).conjTranspose := by
  have hK := inverse_matrix_differentiableAt_of_det_one hH hdet
  have hCD : matrixDZ (a q) (-b q) C x =
      (matrixDZ (a q) (b q) B x).conjTranspose :=
    (matrixDZ_congr_nhds (a q) (-b q) hCstar).trans (matrixDZ_conjTranspose (a q) (b q) B x)
  have hHD : matrixDZ (a q) (-b q) H x =
      (matrixDZ (a q) (b q) H x).conjTranspose :=
    (matrixDZ_congr_nhds (a q) (-b q) hHstar).trans (matrixDZ_conjTranspose (a q) (b q) H x)
  have hHx : (H x).conjTranspose = H x := hHstar.self_of_nhds.symm
  have hKstar : ((H x)⁻¹).conjTranspose = (H x)⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, hHx]
  change matrixDZ (a q) (-b q) (fun y => (H y)⁻¹ * C y) x = _
  rw [matrixDZ_product (a q) (-b q) hK hC,
    matrixDZ_inverse_of_det_one (a q) (-b q) hH hdet,
    hCD, hHD, hCstar.self_of_nhds]
  simp only [compensatedField, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_mul, hKstar]
  noncomm_ring

end CHS.Calculus
