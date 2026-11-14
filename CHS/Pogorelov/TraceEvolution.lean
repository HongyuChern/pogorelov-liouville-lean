import CHS.Calculus.SchurHessianLM
import CHS.Pogorelov.Parameters

/-!
# The trace evolution in the Pogorelov test function
-/

set_option autoImplicit false
noncomputable section

open Matrix Filter
open scoped BigOperators ComplexOrder ContDiff Topology

namespace CHS.Pogorelov

open CHS.Calculus CHS.SchurContractionCore

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem dz_trace {G : E → Matrix ι ι ℂ} {x : E}
    (hG : MatrixDifferentiableAt G x) (a b : E) :
    dz a b (fun y => (G y).trace) x = (matrixDZ a b G x).trace := by
  unfold Matrix.trace
  exact dz_sum_at (fun i => hG i i) a b

private theorem dz_dz_trace {G : E → Matrix ι ι ℂ} {U : Set E}
    (hU : IsOpen U) (hG : ∀ i j, ContDiffOn ℝ 2 (fun y => G y i j) U)
    {x : E} (hx : x ∈ U) (a b c d : E) :
    dz c d (dz a b (fun y => (G y).trace)) x = (matrixDZ c d (matrixDZ a b G) x).trace := by
  have hFirst : dz a b (fun y => (G y).trace) =ᶠ[𝓝 x]
      (fun y => (matrixDZ a b G y).trace) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact dz_trace
      (fun i j => ((hG i j).contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num)) a b
  rw [dz_congr_nhds hFirst]
  exact dz_trace (matrixDZ_differentiableAt (fun i j => (hG i j).contDiffAt (hU.mem_nhds hx)) a b) c d

def linearizedScalar (a b : ι → E) (W : Matrix ι ι ℂ) (f : E → ℂ) (x : E) : ℂ :=
  ∑ p, ∑ q, W q p * dz (a q) (-b q) (dz (a p) (b p) f) x

theorem linearizedScalar_trace {G : E → Matrix ι ι ℂ} {U : Set E}
    (hU : IsOpen U) (hG : ∀ i j, ContDiffOn ℝ 2 (fun y => G y i j) U)
    {x : E} (hx : x ∈ U) (a b : ι → E) (W : Matrix ι ι ℂ) :
    linearizedScalar a b W (fun y => (G y).trace) x =
      (contract W (fun p q => matrixDZ (a q) (-b q) (matrixDZ (a p) (b p) G) x)).trace := by
  unfold linearizedScalar contract
  simp_rw [dz_dz_trace hU hG hx, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]

/-- The two nonnegative quadratic energies in equation (2.19). -/
theorem trace_evolution {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : ι → E)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = 1)
    {x : E} (hx : x ∈ U) (hA : (complexHessian a b u x).PosDef) :
    let A := complexHessian a b u
    let M := schurHessian a b u
    let W := (A x)⁻¹
    let F := CHS.WeightedSquares.matrixSquare W (((A x).map star)⁻¹)
      (fun p => compensatedHessian a b u p x)
    let Q := CHS.WeightedSquares.matrixSquare W W (fun p => matrixDZ (a p) (b p) A x)
    0 ≤ Q.trace ∧ 0 ≤ F.trace ∧
      linearizedScalar a b W (fun y => (A y).trace) x = Q.trace ∧
      linearizedScalar a b W (fun y => (M y).trace) x = -F.trace := by
  let A := complexHessian a b u
  let W := (A x)⁻¹
  let D := ((A x).map star)⁻¹
  let F := CHS.WeightedSquares.matrixSquare W D (fun p => compensatedHessian a b u p x)
  let Q := CHS.WeightedSquares.matrixSquare W W (fun p => matrixDZ (a p) (b p) A x)
  have hu4 (y : E) (hy : y ∈ U) := hu.contDiffAt (hU.mem_nhds hy)
  have hAreg (i j : ι) : ContDiffOn ℝ 2 (fun y => A y i j) U :=
    fun y hy => (complexHessian_contDiffAt_two (hu4 y hy) a b i j).contDiffWithinAt
  have hMreg (i j : ι) : ContDiffOn ℝ 2 (fun y => schurHessian a b u y i j) U :=
    fun y hy => (schurHessian_contDiffAt_two hU hu a b hdet hy i j).contDiffWithinAt
  have hW : W.PosSemidef := hA.inv.posSemidef
  have hD : D.PosSemidef := by
    have hT : (A x).map star = (A x).transpose := by
      ext i j
      exact (complexHessian_isHermitian ((hu4 x hx).of_le (by norm_num)) a b).apply j i
    change ((A x).map star)⁻¹.PosSemidef
    rw [hT]
    exact hA.transpose.inv.posSemidef
  change 0 ≤ Q.trace ∧ 0 ≤ F.trace ∧ _ ∧ _
  refine ⟨(CHS.WeightedSquares.matrixSquare_posSemidef _ _ hW hW _).trace_nonneg,
    (CHS.WeightedSquares.matrixSquare_posSemidef _ _ hW hD _).trace_nonneg, ?_, ?_⟩
  · rw [linearizedScalar_trace hU hAreg hx]
    obtain ⟨hLA, _, _, _, _⟩ := matrix_differential_identities hU hu a b hdet hx
    dsimp only at hLA
    dsimp only [A]
    rw [hLA]
    have hHerm : (fun y => (A y).conjTranspose) =ᶠ[𝓝 x] A := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact (complexHessian_isHermitian ((hu4 y hy).of_le (by norm_num)) a b).eq
    have hAdj (q : ι) : matrixDZ (a q) (-b q) A x =
        (matrixDZ (a q) (b q) A x).conjTranspose := by
      rw [← matrixDZ_conjTranspose]
      exact (matrixDZ_congr_nhds _ _ hHerm).symm
    dsimp only [A] at hAdj
    simp_rw [hAdj]
    rfl
  · rw [linearizedScalar_trace hU hMreg hx, schurHessian_LM hU hu a b hdet hx, Matrix.trace_neg]
    rfl


theorem schur_trace_fields_regular {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : ι → E)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = 1) :
    let A := complexHessian a b u
    let M := schurHessian a b u
    ContDiffOn ℝ 2 (fun y => (A y).trace) U ∧
      ContDiffOn ℝ 2 (fun y => (A y - M y).trace) U := by
  let A := complexHessian a b u
  let M := schurHessian a b u
  have hA (i j : ι) (y : E) (hy : y ∈ U) :=
    complexHessian_contDiffAt_two (hu.contDiffAt (hU.mem_nhds hy)) a b i j
  have hM (i j : ι) (y : E) (hy : y ∈ U) :=
    schurHessian_contDiffAt_two hU hu a b hdet hy i j
  constructor
  · intro y hy
    exact (ContDiffAt.sum (fun i _ => hA i i y hy)).contDiffWithinAt
  · intro y hy
    exact (ContDiffAt.sum (fun i _ => (hA i i y hy).sub (hM i i y hy))).contDiffWithinAt


theorem linearizedScalar_sub {f g : E → ℂ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x)
    (a b : ι → E) (W : Matrix ι ι ℂ) :
    linearizedScalar a b W (fun y => f y - g y) x =
      linearizedScalar a b W f x - linearizedScalar a b W g x := by
  have hnear (p : ι) : dz (a p) (b p) (fun y => f y - g y) =ᶠ[𝓝 x]
      (fun y => dz (a p) (b p) f y - dz (a p) (b p) g y) := by
    filter_upwards [hf.eventually (by simp), hg.eventually (by simp)] with y hyf hyg
    exact dz_sub_at (hyf.differentiableAt (by norm_num)) (hyg.differentiableAt (by norm_num)) _ _
  unfold linearizedScalar
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q _
  rw [dz_congr_nhds (hnear p), dz_sub_at
    ((dz_contDiffAt_one hf (a p) (b p)).differentiableAt (by norm_num))
    ((dz_contDiffAt_one hg (a p) (b p)).differentiableAt (by norm_num)), mul_sub]

/-- Equation (2.19) in the form used in the manuscript, with the trace of
the Schur correction and the actual positive quadratic energies. -/
theorem correction_trace_evolution {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : ι → E)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = 1)
    {x : E} (hx : x ∈ U) (hA : (complexHessian a b u x).PosDef) :
    let A := complexHessian a b u
    let B := pureHessian a b u
    let W := (A x)⁻¹
    let d := fun y => (B y * ((A y).map star)⁻¹ * (B y).map star).trace
    let F := CHS.WeightedSquares.matrixSquare W (((A x).map star)⁻¹)
      (fun p => compensatedHessian a b u p x)
    let Q := CHS.WeightedSquares.matrixSquare W W (fun p => matrixDZ (a p) (b p) A x)
    0 ≤ Q.trace ∧ 0 ≤ F.trace ∧
      linearizedScalar a b W (fun y => (A y).trace) x = Q.trace ∧
      linearizedScalar a b W d x = Q.trace + F.trace := by
  obtain ⟨hQ, hF, hLA, hLM⟩ := trace_evolution hU hu a b hdet hx hA
  dsimp only at hQ hF hLA hLM ⊢
  refine ⟨hQ, hF, hLA, ?_⟩
  let A := complexHessian a b u
  let M := schurHessian a b u
  have hreg (y : E) (hy : y ∈ U) := hu.contDiffAt (hU.mem_nhds hy)
  have hAreg : ContDiffAt ℝ 2 (fun y => (A y).trace) x :=
    ContDiffAt.sum fun i _ => complexHessian_contDiffAt_two (hreg x hx) a b i i
  have hMreg : ContDiffAt ℝ 2 (fun y => (M y).trace) x :=
    ContDiffAt.sum fun i _ => schurHessian_contDiffAt_two hU hu a b hdet hx i i
  have heq :
      (fun y => ((pureHessian a b u y) * ((A y).map star)⁻¹ *
        (pureHessian a b u y).map star).trace) = fun y => (A y).trace - (M y).trace := by
    funext y
    rw [← Matrix.trace_sub]
    change _ = (A y - (A y - _)).trace
    rw [sub_sub_cancel]
  change linearizedScalar a b _ (fun y => ((pureHessian a b u y) * ((A y).map star)⁻¹ *
    (pureHessian a b u y).map star).trace) x = _
  rw [heq, linearizedScalar_sub hAreg hMreg]
  dsimp only [A, M]
  rw [hLA, hLM, sub_neg_eq_add]


/-- The first derivative of the Schur correction, equation (2.21). -/
theorem correction_trace_first_derivative {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : ι → E)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = 1)
    {x : E} (hx : x ∈ U) (p : ι) :
    let A := complexHessian a b u
    let B := pureHessian a b u
    let H := fun y => (A y).map star
    let C := fun y => (B y).map star
    dz (a p) (b p) (fun y => (B y * (H y)⁻¹ * C y).trace) x =
      (compensatedHessian a b u p x * (H x)⁻¹ * C x).trace +
        (B x * (H x)⁻¹ * matrixDZ (a p) (b p) C x).trace := by
  let A := complexHessian a b u
  let B := pureHessian a b u
  let H := fun y => (A y).map star
  let C := fun y => (B y).map star
  have hu4 := hu.contDiffAt (hU.mem_nhds hx)
  have hA : MatrixDifferentiableAt A x := fun i j =>
    (complexHessian_contDiffAt_two hu4 a b i j).differentiableAt (by norm_num)
  have hB : MatrixDifferentiableAt B x := fun i j =>
    (pureHessian_contDiffAt_two hu4 a b i j).differentiableAt (by norm_num)
  have hH : MatrixDifferentiableAt H x := fun i j =>
    Complex.conjCLE.differentiableAt.comp x (hA i j)
  have hC : MatrixDifferentiableAt C x := fun i j =>
    Complex.conjCLE.differentiableAt.comp x (hB i j)
  have hdetH : (fun y => (H y).det) =ᶠ[𝓝 x] fun _ => (1 : ℂ) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    have hT : H y = (A y).transpose := by
      ext i j
      exact (complexHessian_isHermitian
        ((hu.contDiffAt (hU.mem_nhds hy)).of_le (by norm_num)) a b).apply j i
    rw [hT, Matrix.det_transpose]
    exact hdet y hy
  have hK := inverse_matrix_differentiableAt_of_det_one hH hdetH
  have hBK := matrix_product_differentiable hB hK
  change dz (a p) (b p) (fun y => (B y * (H y)⁻¹ * C y).trace) x = _
  rw [dz_trace (matrix_product_differentiable hBK hC),
    matrixDZ_product (a p) (b p) hBK hC,
    matrixDZ_product (a p) (b p) hB hK,
    matrixDZ_inverse_of_det_one (a p) (b p) hH hdetH]
  rw [Matrix.trace_add]
  congr 2
  change (_ * (H x)⁻¹ + B x * -((H x)⁻¹ * _ * (H x)⁻¹)) * C x =
    (matrixDZ (a p) (b p) B x - B x * (H x)⁻¹ * matrixDZ (a p) (b p) H x) *
      (H x)⁻¹ * C x
  noncomm_ring


/-- Positivity and the upper bound on the correction trace follow directly
from the matrix hypothesis in Theorem 1.1. -/
theorem schur_correction_trace_bounds {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (a b : ι → E)
    (hA : (complexHessian a b u x).PosDef) (κ : ℝ)
    (hκ : (κ • complexHessian a b u x - (complexHessian a b u x - schurHessian a b u x)).PosSemidef) :
    let A := complexHessian a b u x
    let d := (A - schurHessian a b u x).trace.re
    0 ≤ d ∧ d ≤ κ * A.trace.re := by
  let A := complexHessian a b u x
  let B := pureHessian a b u x
  let H := A.map star
  have hH : H.PosDef := by
    have hT : H = A.transpose := by
      ext i j
      exact (complexHessian_isHermitian hu a b).apply j i
    rw [hT]
    exact hA.transpose
  have hEq : A - schurHessian a b u x = B * H⁻¹ * B.conjTranspose := by
    change A - (A - B * H⁻¹ * B.map star) = _
    rw [sub_sub_cancel, pureHessian_conjTranspose hu a b]
  have hD : (A - schurHessian a b u x).PosSemidef := by
    rw [hEq]
    exact hH.inv.posSemidef.mul_mul_conjTranspose_same B
  refine ⟨(Complex.nonneg_iff.mp hD.trace_nonneg).1, ?_⟩
  have hh := (Complex.nonneg_iff.mp hκ.trace_nonneg).1
  rw [Matrix.trace_sub, Matrix.trace_smul, Complex.sub_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hh
  exact sub_nonneg.mp hh

end CHS.Pogorelov
