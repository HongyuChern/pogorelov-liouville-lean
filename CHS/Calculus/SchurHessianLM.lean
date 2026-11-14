import CHS.Calculus.DetOneSecondVariation
import CHS.Algebra.WeightedSquares

/-!
# The linearized Schur identity for a constant-density potential

The Schur complement and its compensated derivatives are constructed from
the actual mixed and pure Hessians. The needed cancellations follow from
the local determinant-one equation.
-/

set_option autoImplicit false
open scoped BigOperators ComplexOrder ContDiff Topology

namespace CHS.Calculus
open CHS.SchurContractionCore

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def schurHessian (a b : ι → E) (u : E → ℝ) (x : E) : Matrix ι ι ℂ :=
  schurField (complexHessian a b u) (pureHessian a b u)
    (fun y => (pureHessian a b u y).map star)
    (fun y => (complexHessian a b u y).map star) x

noncomputable def compensatedHessian (a b : ι → E) (u : E → ℝ) (p : ι) (x : E) :
    Matrix ι ι ℂ :=
  compensatedField a b (pureHessian a b u) (fun y => (complexHessian a b u y).map star) p x

theorem pureHessian_conjTranspose {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (a b : ι → E) :
    (pureHessian a b u x).conjTranspose = (pureHessian a b u x).map star := by
  have huc : ContDiffAt ℝ 2 (fun y => (u y : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hu
  ext i j
  change star (dz (a j) (b j) (dz (a i) (b i) (fun y => (u y : ℂ))) x) =
    star (dz (a i) (b i) (dz (a j) (b j) (fun y => (u y : ℂ))) x)
  rw [dz_comm_at huc (a j) (b j) (a i) (b i)]


theorem schurHessian_isHermitian {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (a b : ι → E) :
    (schurHessian a b u x).IsHermitian := by
  let A := complexHessian a b u x
  let B := pureHessian a b u x
  have hA : A.IsHermitian := complexHessian_isHermitian hu a b
  have hD : (A.map star).IsHermitian := by
    have heq : A.map star = A.transpose := by
      ext i j
      exact hA.apply j i
    rw [heq]
    exact hA.transpose
  change (A - B * (A.map star)⁻¹ * B.map star).IsHermitian
  rw [← pureHessian_conjTranspose hu a b]
  change (A - B * (A.map star)⁻¹ * B.conjTranspose).IsHermitian
  have hQ := Matrix.isHermitian_conjTranspose_mul_mul B.conjTranspose hD.inv
  rw [Matrix.conjTranspose_conjTranspose] at hQ
  exact hA.sub hQ

/-- Lemma 2.3, with the weight indexed by the inverse mixed Hessian's
column and row in the same order as the manuscript. -/
theorem schurHessian_LM {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : ι → E)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = 1)
    {x : E} (hx : x ∈ U) :
    contract (complexHessian a b u x)⁻¹ (fun p q =>
      matrixDZ (a q) (-b q) (matrixDZ (a p) (b p) (schurHessian a b u)) x) =
    -contract (complexHessian a b u x)⁻¹ (fun p q =>
      compensatedHessian a b u p x * ((complexHessian a b u x).map star)⁻¹ *
        (compensatedHessian a b u q x).conjTranspose) := by
  let A := complexHessian a b u
  let B := pureHessian a b u
  let H := fun y => (A y).map star
  let C := fun y => (B y).map star
  have hux (y : E) (hy : y ∈ U) : ContDiffAt ℝ 4 u y :=
    hu.contDiffAt (hU.mem_nhds hy)
  have hu2 (y : E) (hy : y ∈ U) : ContDiffAt ℝ 2 u y := (hux y hy).of_le (by norm_num)
  have hA (i j : ι) : ContDiffOn ℝ 2 (fun y => A y i j) U :=
    fun y hy => (complexHessian_contDiffAt_two (hux y hy) a b i j).contDiffWithinAt
  have hBAt (i j : ι) (y : E) (hy : y ∈ U) : ContDiffAt ℝ 2 (fun z => B z i j) y :=
    pureHessian_contDiffAt_two (hux y hy) a b i j
  have hB (i j : ι) : ContDiffOn ℝ 2 (fun y => B y i j) U :=
    fun y hy => (hBAt i j y hy).contDiffWithinAt
  have hHAt (i j : ι) (y : E) (hy : y ∈ U) : ContDiffAt ℝ 2 (fun z => H z i j) y :=
    Complex.conjCLE.contDiff.contDiffAt.comp y
      (complexHessian_contDiffAt_two (hux y hy) a b i j)
  have hCAt (i j : ι) (y : E) (hy : y ∈ U) : ContDiffAt ℝ 2 (fun z => C z i j) y :=
    Complex.conjCLE.contDiff.contDiffAt.comp y (hBAt i j y hy)
  have hH (i j : ι) : ContDiffOn ℝ 2 (fun y => H y i j) U :=
    fun y hy => (hHAt i j y hy).contDiffWithinAt
  have hC (i j : ι) : ContDiffOn ℝ 2 (fun y => C y i j) U :=
    fun y hy => (hCAt i j y hy).contDiffWithinAt
  have hHdet (y : E) (hy : y ∈ U) : (H y).det = 1 := by
    have hT : H y = (A y).transpose := by
      ext i j
      exact (complexHessian_isHermitian (hu2 y hy) a b).apply j i
    rw [hT, Matrix.det_transpose, hdet y hy]
  have hHdetAt : (fun y => (H y).det) =ᶠ[𝓝 x] fun _ => (1 : ℂ) :=
    Filter.Eventually.mono (hU.mem_nhds hx) hHdet
  obtain ⟨_, hLA, _, hLB, hReturn⟩ := matrix_differential_identities hU hu a b hdet hx
  change contract (A x)⁻¹ (fun p q =>
    matrixDZ (a q) (-b q) (matrixDZ (a p) (b p) (schurField A B C H)) x) = _
  refine schurField_LM_square a b (A x)⁻¹ hU hA hB hC hH hHdet hx hLA ?_ hReturn ?_
  · exact compensatedField_contraction_zero a b (A x)⁻¹
      (fun i j => hBAt i j x hx) (fun i j => hHAt i j x hx) hHdetAt hLB
      (inverse_conjugate_hessian_divergence hU hu a b hdet hx A (Or.inl rfl))
  · intro q
    apply matrixDZ_inverse_return a b
      (fun i j => (hCAt i j x hx).differentiableAt (by norm_num))
      (fun i j => (hHAt i j x hx).differentiableAt (by norm_num)) hHdetAt
    · filter_upwards [hU.mem_nhds hx] with y hy
      exact (pureHessian_conjTranspose (hu2 y hy) a b).symm
    · filter_upwards [hU.mem_nhds hx] with y hy
      ext i j
      change star (A y i j) = star (star (A y j i))
      rw [star_star]
      exact (complexHessian_isHermitian (hu2 y hy) a b).apply j i

/-- The Hermitian inequality in Lemma 2.3. It uses the positive branch. -/
theorem schurHessian_LM_nonpos {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : ι → E)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = 1)
    {x : E} (hx : x ∈ U) (hA : (complexHessian a b u x).PosDef) :
    (-contract (complexHessian a b u x)⁻¹ (fun p q =>
      matrixDZ (a q) (-b q) (matrixDZ (a p) (b p) (schurHessian a b u)) x)).PosSemidef := by
  have hu2 : ContDiffAt ℝ 2 u x := (hu.contDiffAt (hU.mem_nhds hx)).of_le (by norm_num)
  have hW : ((complexHessian a b u x)⁻¹).PosDef := hA.inv
  have hH : (((complexHessian a b u x).map star)⁻¹).PosDef := by
    have hT : (complexHessian a b u x).map star = (complexHessian a b u x).transpose := by
      ext i j
      exact (complexHessian_isHermitian hu2 a b).apply j i
    rw [hT]
    exact hA.transpose.inv
  rw [schurHessian_LM hU hu a b hdet hx, neg_neg]
  exact CHS.WeightedSquares.matrixSquare_posSemidef _ _ hW.posSemidef hH.posSemidef
    (fun p => compensatedHessian a b u p x)

/-- Each entry of the actual Schur complement has the two derivatives
required for the scalar minimum principle. -/
theorem schurHessian_contDiffAt_two {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : ι → E)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = 1)
    {x : E} (hx : x ∈ U) (i j : ι) :
    ContDiffAt ℝ 2 (fun y => schurHessian a b u y i j) x := by
  have hu4 := hu.contDiffAt (hU.mem_nhds hx)
  have hA := complexHessian_contDiffAt_two hu4 a b
  have hB := pureHessian_contDiffAt_two hu4 a b
  apply schurField_contDiffAt_two hA hB
    (fun r s => Complex.conjCLE.contDiff.contDiffAt.comp x (hB r s))
    (fun r s => Complex.conjCLE.contDiff.contDiffAt.comp x (hA r s)) _ i j
  filter_upwards [hU.mem_nhds hx] with y hy
  have h2 : ContDiffAt ℝ 2 u y :=
    (hu.contDiffAt (hU.mem_nhds hy)).of_le (by norm_num)
  have hT : (complexHessian a b u y).map star = (complexHessian a b u y).transpose := by
    ext r s
    exact (complexHessian_isHermitian h2 a b).apply s r
  change ((complexHessian a b u y).map star).det = 1
  rw [hT, Matrix.det_transpose, hdet y hy]

end CHS.Calculus
