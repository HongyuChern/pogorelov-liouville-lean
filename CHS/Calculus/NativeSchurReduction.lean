import CHS.Calculus.NativeCMAContractions

/-!
# A consuming interface from actual CMA contractions to Schur LM

S006 candidate, not kernel-checked in Chat. This is explicitly NOT the complete
paper Lemma 2.3: the two inverse-divergence equations are still visible inputs.
The previous LA, LB, regularity and adjoint-return inputs are now discharged
from the actual real C4 potential and determinant equation. No assumed matrix
jets or solution-structure fields stand in for these proofs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ContDiff Topology

namespace CHS.Calculus

open CHS.SchurContractionCore

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual order of the two constant derivatives in the linearized
operator may be exchanged under its precise C2 hypothesis. -/
lemma matrixDZ_comm_at {G : E → Matrix ι ι ℂ} {x : E}
    (hG : ∀ i j, ContDiffAt ℝ 2 (fun y => G y i j) x) (a b c d : E) :
    matrixDZ a b (matrixDZ c d G) x = matrixDZ c d (matrixDZ a b G) x := by
  ext i j
  exact dz_comm_at (hG i j) a b c d

/-- Actual Schur field, with H = bar(A) represented by transpose(A), and
C = bar(B) represented by actual anti-holomorphic second derivatives.
Only the two named inverse-divergence obligations remain conditional. -/
theorem native_schur_LM_of_two_inverse_divergences
    (a b : ι → E) {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U)
    (hdet : ∀ y ∈ U, (complexHessianIn a b u y).det = 1)
    {x : E} (hx : x ∈ U) :
    let A := complexHessianIn a b u
    let B := pureHessianIn a b u
    let C := antiHessianIn a b u
    let H := fun y => (A y).transpose
    let K := (A x)⁻¹
    (contract K (fun p q => matrixDZ (a q) (-b q)
      (inverseDerivativeField a b H H p) x) = 0) →
    (contract K (fun p q => matrixDZ (a q) (-b q)
      (inverseDerivativeField a b H C p) x) = 0) →
    contract K (fun p q => matrixDZ (a q) (-b q)
      (matrixDZ (a p) (b p) (schurField A B C H)) x) =
      -contract K (fun p q => compensatedField a b B H p x * (H x)⁻¹ *
        (compensatedField a b B H q x).conjTranspose) := by
  dsimp only
  intro hHH hHC
  let A := complexHessianIn a b u
  let B := pureHessianIn a b u
  let C := antiHessianIn a b u
  let H := fun y => (A y).transpose
  let K := (A x)⁻¹
  have hA : ∀ i j, ContDiffOn ℝ 2 (fun y => A y i j) U :=
    complexHessianIn_contDiffOn a b hU hu
  have hB : ∀ i j, ContDiffOn ℝ 2 (fun y => B y i j) U :=
    pureHessianIn_contDiffOn a b hU hu
  have hC : ∀ i j, ContDiffOn ℝ 2 (fun y => C y i j) U :=
    antiHessianIn_contDiffOn a b hU hu
  have hH : ∀ i j, ContDiffOn ℝ 2 (fun y => H y i j) U :=
    fun i j => hA j i
  have hdetH : ∀ y ∈ U, (H y).det = 1 := by
    intro y hy
    simpa only [H, A, Matrix.det_transpose] using hdet y hy
  have hdetHx : (fun y => (H y).det) =ᶠ[𝓝 x] (fun _ => (1 : ℂ)) :=
    Filter.Eventually.mono (hU.mem_nhds hx) (fun y hy => hdetH y hy)
  have hCx i j := (hC i j).contDiffAt (hU.mem_nhds hx)
  have hBx i j := (hB i j).contDiffAt (hU.mem_nhds hx)
  have hHx i j := (hH i j).contDiffAt (hU.mem_nhds hx)
  have hCstar : C =ᶠ[𝓝 x] (fun y => (B y).conjTranspose) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact antiHessianIn_eq_conjTranspose a b
      ((hu.contDiffAt (hU.mem_nhds hy)).of_le (by norm_num))
  have hHstar : H =ᶠ[𝓝 x] (fun y => (H y).conjTranspose) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    ext i j
    exact (complexHessianIn_star_entry a b
      ((hu.contDiffAt (hU.mem_nhds hy)).of_le (by norm_num)) i j).symm
  change contract K (fun p q => matrixDZ (a q) (-b q)
    (matrixDZ (a p) (b p) (schurField A B C H)) x) = _
  apply schurField_LM_square a b K hU hA hB hC hH hdetH hx
  · exact complexHessianIn_LA_second a b hU hu hdet hx
  · exact compensatedField_contraction_zero a b K hBx hHx hdetHx
      (pureHessianIn_LB_second a b hU hu hdet hx) hHH
  · exact hHC
  · intro q
    exact matrixDZ_inverse_return a b
      (fun i j => (hCx i j).differentiableAt (by norm_num))
      (fun i j => (hHx i j).differentiableAt (by norm_num)) hdetHx hCstar hHstar

end CHS.Calculus
