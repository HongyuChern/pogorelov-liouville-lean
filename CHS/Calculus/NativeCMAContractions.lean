import CHS.Calculus.DeterminantVariation
import CHS.Calculus.NativeComplexHessian

/-!
# Differentiated CMA contractions from the actual C4 potential

S006 candidate. No new kernel acceptance is claimed in Chat.
The hypotheses below are openness, finite C4 regularity of a real function,
and its actual complex-Hessian determinant equation on that open set.
No trace equation, Jacobi identity, LA or LB equation is an input hypothesis.
The first matrix formulas in paper (2.2) and (2.3) are the initial targets.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ContDiff Topology

namespace CHS.Calculus

open CHS.SchurContractionCore

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma contract_apply_eq (W : Matrix ι ι ℂ) (F : ι → ι → Matrix ι ι ℂ) (i j : ι) :
    contract W F i j = ∑ p, ∑ q, W q p * F p q i j := by
  simp only [contract, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

lemma contract_sandwich_apply (W K : Matrix ι ι ℂ)
    (X Y : ι → Matrix ι ι ℂ) (i j : ι) :
    contract W (fun p q => X p * K * Y q) i j =
      ∑ p, ∑ q, ∑ s, ∑ t, W q p * X p i s * K s t * Y q t j := by
  rw [contract_apply_eq]
  simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  exact Finset.sum_comm

lemma contract_sandwich_swapped_apply (W K : Matrix ι ι ℂ)
    (X Y : ι → Matrix ι ι ℂ) (i j : ι) :
    contract W (fun p q => X q * K * Y p) i j =
      ∑ p, ∑ q, ∑ s, ∑ t, W q p * X q i s * K s t * Y p t j := by
  rw [contract_apply_eq]
  simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  exact Finset.sum_comm

/-- The actual first derivative equation (paper (2.1)). -/
theorem native_cma_first_variation (a b : ι → E) {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U)
    (hdet : ∀ y ∈ U, (complexHessianIn a b u y).det = 1)
    {x : E} (hx : x ∈ U) (v w : E) :
    Matrix.trace ((complexHessianIn a b u x)⁻¹ *
      matrixDZ v w (complexHessianIn a b u) x) = 0 := by
  apply trace_inverse_matrixDZ_eq_zero
    (fun i j => ((complexHessianIn_contDiffOn a b hU hu i j).contDiffAt
      (hU.mem_nhds hx)).differentiableAt (by norm_num))
    (Filter.Eventually.mono (hU.mem_nhds hx) (fun y hy => hdet y hy))

/-- The fourth derivative contraction is obtained from determinant one,
not assumed as a separate property of the potential. -/
theorem complexHessianIn_linearized_trace (a b : ι → E) {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U)
    (hdet : ∀ y ∈ U, (complexHessianIn a b u y).det = 1)
    {x : E} (hx : x ∈ U) (i j : ι) :
    let A := complexHessianIn a b u
    let K := (A x)⁻¹
    (∑ p, ∑ q, K q p *
      matrixDZ (a q) (-b q) (matrixDZ (a p) (b p) A) x i j) =
      Matrix.trace (K * matrixDZ (a i) (b i) A x * K * matrixDZ (a j) (-b j) A x) := by
  dsimp only
  have h := trace_inverse_second_matrixDZ hU
    (complexHessianIn_contDiffOn a b hU hu) hdet hx (a i) (b i) (a j) (-b j)
  rw [trace_mul_eq_reversed_sum] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  rw [complexHessianIn_second_exchange a b hU hu hx i j p q]

/-- The pure second derivative analogue needed for LB. -/
theorem pureHessianIn_linearized_trace (a b : ι → E) {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U)
    (hdet : ∀ y ∈ U, (complexHessianIn a b u y).det = 1)
    {x : E} (hx : x ∈ U) (i j : ι) :
    let A := complexHessianIn a b u
    let B := pureHessianIn a b u
    let K := (A x)⁻¹
    (∑ p, ∑ q, K q p *
      matrixDZ (a q) (-b q) (matrixDZ (a p) (b p) B) x i j) =
      Matrix.trace (K * matrixDZ (a i) (b i) A x * K * matrixDZ (a j) (b j) A x) := by
  dsimp only
  have h := trace_inverse_second_matrixDZ hU
    (complexHessianIn_contDiffOn a b hU hu) hdet hx (a i) (b i) (a j) (b j)
  rw [trace_mul_eq_reversed_sum] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  rw [pureHessianIn_second_exchange a b hU hu hx i j p q]

/-- Paper (2.2), first matrix expression, for the actual potential. -/
theorem complexHessianIn_LA_first (a b : ι → E) {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U)
    (hdet : ∀ y ∈ U, (complexHessianIn a b u y).det = 1)
    {x : E} (hx : x ∈ U) :
    let A := complexHessianIn a b u
    let K := (A x)⁻¹
    contract K (fun p q => matrixDZ (a q) (-b q) (matrixDZ (a p) (b p) A) x) =
      contract K (fun p q => matrixDZ (a p) (b p) A x * K * matrixDZ (a q) (-b q) A x) := by
  dsimp only
  ext i j
  rw [contract_apply_eq, contract_sandwich_apply,
    complexHessianIn_linearized_trace a b hU hu hdet hx i j,
    trace_four_eq_reversed_sum]
  have hc : ContDiffOn ℝ 3 (complexify u) U :=
    (complexify_contDiffOn hu).of_le (by norm_num)
  have hcx := hc.contDiffAt (hU.mem_nhds hx)
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  have hhol : matrixDZ (a i) (b i) (complexHessianIn a b u) x p s =
      matrixDZ (a p) (b p) (complexHessianIn a b u) x i s :=
    third_outer_comm_at hcx (a i) (b i) (a p) (b p) (a s) (-b s)
  have hanti : matrixDZ (a j) (-b j) (complexHessianIn a b u) x t q =
      matrixDZ (a q) (-b q) (complexHessianIn a b u) x t j :=
    third_reverse_on hU hc (a j) (-b j) (a t) (b t) (a q) (-b q) hx
  rw [hhol, hanti]

/-- Paper (2.3), first matrix expression, from the same actual determinant
variation. The third derivative on the right is a derivative of B, not A. -/
theorem pureHessianIn_LB_first (a b : ι → E) {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U)
    (hdet : ∀ y ∈ U, (complexHessianIn a b u y).det = 1)
    {x : E} (hx : x ∈ U) :
    let A := complexHessianIn a b u
    let B := pureHessianIn a b u
    let K := (A x)⁻¹
    contract K (fun p q => matrixDZ (a q) (-b q) (matrixDZ (a p) (b p) B) x) =
      contract K (fun p q => matrixDZ (a p) (b p) A x * K * matrixDZ (a q) (-b q) B x) := by
  dsimp only
  ext i j
  rw [contract_apply_eq, contract_sandwich_apply,
    pureHessianIn_linearized_trace a b hU hu hdet hx i j,
    trace_four_eq_reversed_sum]
  have hc : ContDiffOn ℝ 3 (complexify u) U :=
    (complexify_contDiffOn hu).of_le (by norm_num)
  have hcx := hc.contDiffAt (hU.mem_nhds hx)
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  have hhol : matrixDZ (a i) (b i) (complexHessianIn a b u) x p s =
      matrixDZ (a p) (b p) (complexHessianIn a b u) x i s :=
    third_outer_comm_at hcx (a i) (b i) (a p) (b p) (a s) (-b s)
  have hpure : matrixDZ (a j) (b j) (complexHessianIn a b u) x t q =
      matrixDZ (a q) (-b q) (pureHessianIn a b u) x t j :=
    third_reverse_on hU hc (a j) (b j) (a t) (b t) (a q) (-b q) hx
  rw [hhol, hpure]

/-- Paper (2.2), second matrix expression. H = transpose(A) is exactly bar(A)
for the real potential, and C is its actual anti-pure Hessian = bar(B). -/
theorem complexHessianIn_LA_second (a b : ι → E) {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U)
    (hdet : ∀ y ∈ U, (complexHessianIn a b u y).det = 1)
    {x : E} (hx : x ∈ U) :
    let A := complexHessianIn a b u
    let B := pureHessianIn a b u
    let C := antiHessianIn a b u
    let K := (A x)⁻¹
    contract K (fun p q => matrixDZ (a q) (-b q) (matrixDZ (a p) (b p) A) x) =
      contract K (fun p q => matrixDZ (a q) (-b q) B x * (A x).transpose⁻¹ *
        matrixDZ (a p) (b p) C x) := by
  dsimp only
  ext i j
  rw [contract_apply_eq, contract_sandwich_swapped_apply,
    complexHessianIn_linearized_trace a b hU hu hdet hx i j,
    trace_four_eq_crossed_sum, ← Matrix.transpose_nonsing_inv]
  have hc : ContDiffOn ℝ 3 (complexify u) U :=
    (complexify_contDiffOn hu).of_le (by norm_num)
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  have hB : matrixDZ (a i) (b i) (complexHessianIn a b u) x s q =
      matrixDZ (a q) (-b q) (pureHessianIn a b u) x i s :=
    third_cycle_on hU hc (a i) (b i) (a s) (b s) (a q) (-b q) hx
  have hC : matrixDZ (a j) (-b j) (complexHessianIn a b u) x p t =
      matrixDZ (a p) (b p) (antiHessianIn a b u) x t j :=
    (third_cycle_on hU hc (a p) (b p) (a t) (-b t) (a j) (-b j) hx).symm
  simp only [hB, hC, Matrix.transpose_apply]

/-- Paper (2.3), second matrix expression used by compensatedField. -/
theorem pureHessianIn_LB_second (a b : ι → E) {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U)
    (hdet : ∀ y ∈ U, (complexHessianIn a b u y).det = 1)
    {x : E} (hx : x ∈ U) :
    let A := complexHessianIn a b u
    let B := pureHessianIn a b u
    let H := fun y => (A y).transpose
    let K := (A x)⁻¹
    contract K (fun p q => matrixDZ (a q) (-b q) (matrixDZ (a p) (b p) B) x) =
      contract K (fun p q => matrixDZ (a q) (-b q) B x * (H x)⁻¹ *
        matrixDZ (a p) (b p) H x) := by
  dsimp only
  ext i j
  rw [contract_apply_eq, contract_sandwich_swapped_apply,
    pureHessianIn_linearized_trace a b hU hu hdet hx i j,
    trace_four_eq_crossed_sum, ← Matrix.transpose_nonsing_inv]
  have hc : ContDiffOn ℝ 3 (complexify u) U :=
    (complexify_contDiffOn hu).of_le (by norm_num)
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  have hB : matrixDZ (a i) (b i) (complexHessianIn a b u) x s q =
      matrixDZ (a q) (-b q) (pureHessianIn a b u) x i s :=
    third_cycle_on hU hc (a i) (b i) (a s) (b s) (a q) (-b q) hx
  have hH : matrixDZ (a j) (b j) (complexHessianIn a b u) x p t =
      matrixDZ (a p) (b p) (fun y => (complexHessianIn a b u y).transpose) x t j :=
    third_outer_comm_at (hc.contDiffAt (hU.mem_nhds hx))
      (a j) (b j) (a p) (b p) (a t) (-b t)
  simp only [hB, hH, Matrix.transpose_apply]

/-- Specialization to the actual frozen interleaved Euclidean coordinates. -/
theorem native_cma_LA_first {n : ℕ} {u : CMARealSpace n → ℝ} {U : Set (CMARealSpace n)}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U)
    (hdet : ∀ y ∈ U, (nativeComplexHessian u y).det = 1)
    {x : CMARealSpace n} (hx : x ∈ U) :
    let A := nativeComplexHessian u
    let K := (A x)⁻¹
    contract K (fun p q => matrixDZ (cmaRealDirection q) (-cmaImagDirection q)
      (matrixDZ (cmaRealDirection p) (cmaImagDirection p) A) x) =
      contract K (fun p q => matrixDZ (cmaRealDirection p) (cmaImagDirection p) A x *
        K * matrixDZ (cmaRealDirection q) (-cmaImagDirection q) A x) :=
  complexHessianIn_LA_first cmaRealDirection cmaImagDirection hU hu hdet hx

end CHS.Calculus
