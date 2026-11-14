import CHS.Calculus.NativeSchurReduction

/-!
# Eliminate the two inverse-divergence obligations for an actual CMA potential

S006 candidate; NOT compiled in Chat. This module completes the differential
identity part of the Schur LM calculation, not its positive-definite sign or
all of paper Lemma 2.3. The final theorem has no LA/LB/divergence hypotheses.

The flipped complex Hessian equals transpose(A) only on the open domain.
Both derivative transports below therefore use neighbourhood equality,
not an unjustified global identification of total Frechet derivatives.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ContDiff Topology

namespace CHS.Calculus

open CHS.SchurContractionCore

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma contract_transpose_swap (W : Matrix ι ι ℂ)
    (F : ι → ι → Matrix ι ι ℂ) :
    contract W.transpose F = contract W (fun p q => F q p) := by
  change (∑ p, ∑ q, W p q • F p q) = (∑ q, ∑ p, W p q • F p q)
  exact Finset.sum_comm

lemma contract_inverse_transpose_swap (A : Matrix ι ι ℂ)
    (F : ι → ι → Matrix ι ι ℂ) :
    contract A.transpose⁻¹ F = contract A⁻¹ (fun p q => F q p) := by
  rw [← Matrix.transpose_nonsing_inv, contract_transpose_swap]

lemma matrixDZ_congr_on (a b : E) {F G : E → Matrix ι ι ℂ} {U : Set E}
    (hU : IsOpen U) (hFG : Set.EqOn F G U) {x : E} (hx : x ∈ U) :
    matrixDZ a b F x = matrixDZ a b G x :=
  matrixDZ_congr_nhds a b (Filter.Eventually.mono (hU.mem_nhds hx) (fun y hy => hFG hy))

lemma matrixDZ_two_congr_on (a b c d : E) {F G : E → Matrix ι ι ℂ}
    {U : Set E} (hU : IsOpen U) (hFG : Set.EqOn F G U) {x : E} (hx : x ∈ U) :
    matrixDZ a b (matrixDZ c d F) x = matrixDZ a b (matrixDZ c d G) x := by
  apply matrixDZ_congr_on a b hU (hx := hx)
  intro y hy
  exact matrixDZ_congr_on c d hU hFG hy

lemma complexHessianIn_flip_eq_transpose (a b : ι → E) {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) :
    complexHessianIn a (fun i => -b i) u x = (complexHessianIn a b u x).transpose := by
  have hc : ContDiffAt ℝ 2 (complexify u) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hu
  ext i j
  simp only [complexHessianIn, neg_neg, Matrix.transpose_apply]
  exact dz_comm_at hc (a i) (-b i) (a j) (b j)

/-- Conjugating the native LA equation changes the weight to K-transpose;
the p,q swap is explicit. This is the actual LH equation. -/
theorem complexHessianIn_LH_first (a b : ι → E) {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U)
    (hdet : ∀ y ∈ U, (complexHessianIn a b u y).det = 1)
    {x : E} (hx : x ∈ U) :
    let A := complexHessianIn a b u
    let H := fun y => (A y).transpose
    let K := (A x)⁻¹
    contract K (fun p q => matrixDZ (a q) (-b q) (matrixDZ (a p) (b p) H) x) =
      contract K (fun p q => matrixDZ (a q) (-b q) H x * (H x)⁻¹ *
        matrixDZ (a p) (b p) H x) := by
  dsimp only
  let A := complexHessianIn a b u
  let H := fun y => (A y).transpose
  let Z := complexHessianIn a (fun i => -b i) u
  have hZH : Set.EqOn Z H U := by
    intro y hy
    exact complexHessianIn_flip_eq_transpose a b
      ((hu.contDiffAt (hU.mem_nhds hy)).of_le (by norm_num))
  have hZdet : ∀ y ∈ U, (Z y).det = 1 := by
    intro y hy
    rw [hZH hy]
    simpa only [H, A, Matrix.det_transpose] using hdet y hy
  have h := complexHessianIn_LA_first a (fun i => -b i) hU hu hZdet hx
  simp only [neg_neg] at h
  have hD (v w : E) : matrixDZ v w Z x = matrixDZ v w H x :=
    matrixDZ_congr_on v w hU hZH hx
  have hD₂ (v w r s : E) :
      matrixDZ v w (matrixDZ r s Z) x = matrixDZ v w (matrixDZ r s H) x :=
    matrixDZ_two_congr_on v w r s hU hZH hx
  change contract (Z x)⁻¹ (fun p q => matrixDZ (a q) (b q)
    (matrixDZ (a p) (-b p) Z) x) =
    contract (Z x)⁻¹ (fun p q => matrixDZ (a p) (-b p) Z x * (Z x)⁻¹ *
      matrixDZ (a q) (b q) Z x) at h
  simp only [hD₂, hD, hZH hx] at h
  change contract ((A x).transpose)⁻¹ (fun p q => matrixDZ (a q) (b q)
    (matrixDZ (a p) (-b p) H) x) =
    contract ((A x).transpose)⁻¹ (fun p q => matrixDZ (a p) (-b p) H x *
      (H x)⁻¹ * matrixDZ (a q) (b q) H x) at h
  simp only [contract_inverse_transpose_swap] at h
  have hHx i j := (complexHessianIn_contDiffOn a b hU hu j i).contDiffAt
    (hU.mem_nhds hx)
  change contract (A x)⁻¹ (fun p q => matrixDZ (a q) (-b q)
    (matrixDZ (a p) (b p) H) x) = _
  calc
    _ = contract (A x)⁻¹ (fun p q => matrixDZ (a p) (b p)
        (matrixDZ (a q) (-b q) H) x) := by
      unfold contract
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      exact congrArg (fun M : Matrix ι ι ℂ => (A x)⁻¹ q p • M)
        (matrixDZ_comm_at hHx (a q) (-b q) (a p) (b p))
    _ = _ := h

/-- The same flipped LB equation gives LC, with C the genuine anti-pure
Hessian. Neither LC nor its inverse divergence is an input assumption. -/
theorem antiHessianIn_LC_first (a b : ι → E) {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U)
    (hdet : ∀ y ∈ U, (complexHessianIn a b u y).det = 1)
    {x : E} (hx : x ∈ U) :
    let A := complexHessianIn a b u
    let H := fun y => (A y).transpose
    let C := antiHessianIn a b u
    let K := (A x)⁻¹
    contract K (fun p q => matrixDZ (a q) (-b q) (matrixDZ (a p) (b p) C) x) =
      contract K (fun p q => matrixDZ (a q) (-b q) H x * (H x)⁻¹ *
        matrixDZ (a p) (b p) C x) := by
  dsimp only
  let A := complexHessianIn a b u
  let H := fun y => (A y).transpose
  let C := antiHessianIn a b u
  let Z := complexHessianIn a (fun i => -b i) u
  have hZH : Set.EqOn Z H U := by
    intro y hy
    exact complexHessianIn_flip_eq_transpose a b
      ((hu.contDiffAt (hU.mem_nhds hy)).of_le (by norm_num))
  have hZdet : ∀ y ∈ U, (Z y).det = 1 := by
    intro y hy
    rw [hZH hy]
    simpa only [H, A, Matrix.det_transpose] using hdet y hy
  have h := pureHessianIn_LB_first a (fun i => -b i) hU hu hZdet hx
  simp only [neg_neg] at h
  have hD (v w : E) : matrixDZ v w Z x = matrixDZ v w H x :=
    matrixDZ_congr_on v w hU hZH hx
  change contract (Z x)⁻¹ (fun p q => matrixDZ (a q) (b q)
    (matrixDZ (a p) (-b p) C) x) =
    contract (Z x)⁻¹ (fun p q => matrixDZ (a p) (-b p) Z x * (Z x)⁻¹ *
      matrixDZ (a q) (b q) C x) at h
  simp only [hD, hZH hx] at h
  change contract ((A x).transpose)⁻¹ (fun p q => matrixDZ (a q) (b q)
    (matrixDZ (a p) (-b p) C) x) =
    contract ((A x).transpose)⁻¹ (fun p q => matrixDZ (a p) (-b p) H x *
      (H x)⁻¹ * matrixDZ (a q) (b q) C x) at h
  simp only [contract_inverse_transpose_swap] at h
  have hCx i j := (antiHessianIn_contDiffOn a b hU hu i j).contDiffAt (hU.mem_nhds hx)
  change contract (A x)⁻¹ (fun p q => matrixDZ (a q) (-b q)
    (matrixDZ (a p) (b p) C) x) = _
  calc
    _ = contract (A x)⁻¹ (fun p q => matrixDZ (a p) (b p)
        (matrixDZ (a q) (-b q) C) x) := by
      unfold contract
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      exact congrArg (fun M : Matrix ι ι ℂ => (A x)⁻¹ q p • M)
        (matrixDZ_comm_at hCx (a q) (-b q) (a p) (b p))
    _ = _ := h

/-- The actual product-rule cancellation for H-inverse times a first
derivative. The only equation input is the separately proved L-equation. -/
lemma inverseDerivativeField_divergence_of_linearized
    (a b : ι → E) (W : Matrix ι ι ℂ)
    {H C : E → Matrix ι ι ℂ} {x : E}
    (hH : ∀ i j, ContDiffAt ℝ 2 (fun y => H y i j) x)
    (hC : ∀ i j, ContDiffAt ℝ 2 (fun y => C y i j) x)
    (hdet : (fun y => (H y).det) =ᶠ[𝓝 x] (fun _ => (1 : ℂ)))
    (hLC : contract W (fun p q => matrixDZ (a q) (-b q) (matrixDZ (a p) (b p) C) x) =
      contract W (fun p q => matrixDZ (a q) (-b q) H x * (H x)⁻¹ *
        matrixDZ (a p) (b p) C x)) :
    contract W (fun p q => matrixDZ (a q) (-b q)
      (inverseDerivativeField a b H C p) x) = 0 := by
  have hHd : MatrixDifferentiableAt H x :=
    fun i j => (hH i j).differentiableAt (by norm_num)
  have hKd := inverse_matrix_differentiableAt_of_det_one hHd hdet
  have hexp (p q : ι) : matrixDZ (a q) (-b q)
      (inverseDerivativeField a b H C p) x =
      (H x)⁻¹ * (matrixDZ (a q) (-b q) (matrixDZ (a p) (b p) C) x -
        matrixDZ (a q) (-b q) H x * (H x)⁻¹ * matrixDZ (a p) (b p) C x) := by
    unfold inverseDerivativeField
    rw [matrixDZ_product (a q) (-b q) hKd
      (matrixDZ_differentiableAt hC (a p) (b p)),
      matrixDZ_inverse_of_det_one (a q) (-b q) hHd hdet]
    noncomm_ring
  simp_rw [hexp]
  rw [contract_mul_left, contract_sub, hLC]
  simp

/-- The mixed inverse-divergence identity (paper's bar(A) field). -/
theorem native_inverse_conjugate_mixed_divergence
    (a b : ι → E) {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U)
    (hdet : ∀ y ∈ U, (complexHessianIn a b u y).det = 1)
    {x : E} (hx : x ∈ U) :
    let A := complexHessianIn a b u
    let H := fun y => (A y).transpose
    contract (A x)⁻¹ (fun p q => matrixDZ (a q) (-b q)
      (inverseDerivativeField a b H H p) x) = 0 := by
  dsimp only
  have hH i j := (complexHessianIn_contDiffOn a b hU hu j i).contDiffAt
    (hU.mem_nhds hx)
  apply inverseDerivativeField_divergence_of_linearized a b _ hH hH
  · filter_upwards [hU.mem_nhds hx] with y hy
    change ((complexHessianIn a b u y).transpose).det = 1
    rw [Matrix.det_transpose]
    exact hdet y hy
  · exact complexHessianIn_LH_first a b hU hu hdet hx

/-- The pure inverse-divergence identity, using the true anti-pure Hessian. -/
theorem native_inverse_conjugate_pure_divergence
    (a b : ι → E) {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U)
    (hdet : ∀ y ∈ U, (complexHessianIn a b u y).det = 1)
    {x : E} (hx : x ∈ U) :
    let A := complexHessianIn a b u
    let H := fun y => (A y).transpose
    let C := antiHessianIn a b u
    contract (A x)⁻¹ (fun p q => matrixDZ (a q) (-b q)
      (inverseDerivativeField a b H C p) x) = 0 := by
  dsimp only
  have hH i j := (complexHessianIn_contDiffOn a b hU hu j i).contDiffAt
    (hU.mem_nhds hx)
  have hC i j := (antiHessianIn_contDiffOn a b hU hu i j).contDiffAt (hU.mem_nhds hx)
  apply inverseDerivativeField_divergence_of_linearized a b _ hH hC
  · filter_upwards [hU.mem_nhds hx] with y hy
    change ((complexHessianIn a b u y).transpose).det = 1
    rw [Matrix.det_transpose]
    exact hdet y hy
  · exact antiHessianIn_LC_first a b hU hu hdet hx

/-- Actual Schur LM IDENTITY from the genuine C4 real potential and CMA
on an open set. The sign requires the separate positive-definite input.
This candidate has no free inverse-divergence or LA/LB assumptions. -/
theorem native_schur_LM_identity
    (a b : ι → E) {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U)
    (hdet : ∀ y ∈ U, (complexHessianIn a b u y).det = 1)
    {x : E} (hx : x ∈ U) :
    let A := complexHessianIn a b u
    let B := pureHessianIn a b u
    let C := antiHessianIn a b u
    let H := fun y => (A y).transpose
    let K := (A x)⁻¹
    contract K (fun p q => matrixDZ (a q) (-b q)
      (matrixDZ (a p) (b p) (schurField A B C H)) x) =
      -contract K (fun p q => compensatedField a b B H p x * (H x)⁻¹ *
        (compensatedField a b B H q x).conjTranspose) := by
  exact native_schur_LM_of_two_inverse_divergences a b hU hu hdet hx
    (native_inverse_conjugate_mixed_divergence a b hU hu hdet hx)
    (native_inverse_conjugate_pure_divergence a b hU hu hdet hx)

end CHS.Calculus
