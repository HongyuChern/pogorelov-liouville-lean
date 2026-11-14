import CHS.Analysis.LocalEllipticity
import CHS.Analysis.ConnectedMinimum
import CHS.Algebra.SchurRank

/-!
# Strong minimum principle for the fixed-vector Schur pairings

The coefficients are constructed on each ball from the actual linearization,
then the De Giorgi theorem propagates zeros on the connected domain.
-/

set_option autoImplicit false
noncomputable section

open DeGiorgi Filter Metric Set
open scoped BigOperators ComplexOrder ContDiff Topology

namespace CHS.Analysis

open Calculus

variable {n : ℕ} [NeZero (n + n)]
local notation "E" => AmbientSpace (n + n)

theorem complexLinearizedCoeff_posDef {u : E → ℝ} {x : E}
    (hA : (complexHessian realDirections imagDirections u x).PosDef) :
    (complexLinearizedCoeff u x).PosDef :=
  (realLinearizationMatrix_posDef hA.inv).submatrix finSumFinEquiv.symm.injective

theorem schurPair_local_supersolutions
    {u : E → ℝ} {U : Set E} (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U)
    (hdet : ∀ y ∈ U, (complexHessian realDirections imagDirections u y).det = 1)
    (hA : ∀ y ∈ U, (complexHessian realDirections imagDirections u y).PosDef)
    (ξ : Fin n → ℂ) :
    ∀ x ∈ U, ∃ r : ℝ, 0 < r ∧ ∃ B : NormalizedEllipticCoeff (n + n) (ball x r),
      ball x r ⊆ U ∧ IsSupersolution B.1
        (fun y => (matrixPair (schurHessian realDirections imagDirections u) ξ y).re) := by
  let v (y : E) := (matrixPair (schurHessian realDirections imagDirections u) ξ y).re
  have hvAt (y : E) (hy : y ∈ U) : ContDiffAt ℝ 2 v y :=
    Complex.reCLM.contDiff.contDiffAt.comp y
      (matrixPair_contDiffAt (schurHessian_contDiffAt_two hU hu _ _ hdet hy) ξ)
  have hv : ContDiffOn ℝ 2 v U := fun y hy => (hvAt y hy).contDiffWithinAt
  have hcoeff (i j : Fin (n + n)) (y : E) (hy : y ∈ U) :
      ContDiffAt ℝ 2 (fun z => complexLinearizedCoeff u z i j) y := by
    apply complexLinearizedCoeff_contDiffAt (hu.contDiffAt (hU.mem_nhds hy))
    filter_upwards [hU.mem_nhds hy] with z hz
    exact hdet z hz
  intro x hx
  obtain ⟨R, hR, hRsub⟩ := Metric.isOpen_iff.mp hU x hx
  let r := R / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrR : r < R := by dsimp [r]; linarith
  have hclosed : closedBall x r ⊆ U := (closedBall_subset_ball hrR).trans hRsub
  obtain ⟨c, hc, B, hB⟩ := exists_normalizedEllipticCoeff_on_ball hr
    (fun i j y hy => (hcoeff i j y (hclosed hy)).continuousAt.continuousWithinAt)
    (fun y hy => complexLinearizedCoeff_posDef (hA y (hclosed hy)))
  refine ⟨r, hr, B, ball_subset_closedBall.trans hclosed, ?_⟩
  have hrmid : r < (r + R) / 2 := by linarith
  have hmidR : (r + R) / 2 < R := by linarith
  let F (y : E) := c⁻¹ • matMulE (complexLinearizedCoeff u y) (smoothGradField v y)
  have hF (i : Fin (n + n)) (y : E) (hy : y ∈ U) :
      ContDiffAt ℝ 1 (fun z => F z i) y := by
    change ContDiffAt ℝ 1 (fun z => c⁻¹ *
      ∑ j, complexLinearizedCoeff u z i j * fderiv ℝ v z (EuclideanSpace.single j 1)) y
    apply contDiffAt_const.mul
    apply ContDiffAt.sum
    intro j _
    exact ((hcoeff i j y hy).of_le (by norm_num)).mul
      (((hvAt y hy).fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const)
  apply supersolution_of_local_classical_flux hU hr hrmid
    ((closedBall_subset_ball hmidR).trans hRsub) B.1 (hv.of_le (by norm_num))
    (F := F) (fun i y hy => (hF i y hy).contDiffWithinAt)
  · intro y hy
    rw [hB y hy, matMulE_smul_matrix]
  · intro y hy
    have hyU := hclosed (ball_subset_closedBall hy)
    have hscale :
        classicalDivergence F y =
          c⁻¹ * classicalDivergence
            (fun z => matMulE (complexLinearizedCoeff u z) (smoothGradField v z)) y := by
      unfold classicalDivergence
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      change fderiv ℝ (fun z => c⁻¹ * matMulE (complexLinearizedCoeff u z)
        (smoothGradField v z) i) y (EuclideanSpace.single i 1) = _
      have hdF : DifferentiableAt ℝ (fun z => matMulE (complexLinearizedCoeff u z)
          (smoothGradField v z) i) y := by
        change DifferentiableAt ℝ (fun z => ∑ j, complexLinearizedCoeff u z i j *
          fderiv ℝ v z (EuclideanSpace.single j 1)) y
        apply DifferentiableAt.fun_sum
        intro j _
        have hj : ContDiffAt ℝ 1 (fun z => fderiv ℝ v z (EuclideanSpace.single j 1)) y :=
          ((hvAt y hyU).fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
        exact ((hcoeff i j y hyU).differentiableAt (by norm_num)).mul
          (hj.differentiableAt (by norm_num))
      rw [fderiv_const_mul hdF, smul_apply, smul_eq_mul]
    rw [hscale]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hc.le)
      (schurPair_flux_divergence_nonpos hU hu hdet hyU (hA y hyU) ξ)


theorem schurPair_eq_zero_on_connected
    (hd : 2 < ((n + n : ℕ) : ℝ)) {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hconn : IsPreconnected U) (hu : ContDiffOn ℝ 4 u U)
    (hdet : ∀ y ∈ U, (complexHessian realDirections imagDirections u y).det = 1)
    (hA : ∀ y ∈ U, (complexHessian realDirections imagDirections u y).PosDef)
    (hM : ∀ y ∈ U, (schurHessian realDirections imagDirections u y).PosSemidef)
    (ξ : Fin n → ℂ) {x₀ : E} (hx₀ : x₀ ∈ U)
    (hzero : (matrixPair (schurHessian realDirections imagDirections u) ξ x₀).re = 0) :
    EqOn (fun y => (matrixPair (schurHessian realDirections imagDirections u) ξ y).re)
      (fun _ => 0) U := by
  apply eq_zero_on_connected_of_local_supersolutions hd hU hconn
  · intro y hy
    have hpair : ContDiffAt ℝ 2
        (fun z => (matrixPair (schurHessian realDirections imagDirections u) ξ z).re) y :=
      Complex.reCLM.contDiff.contDiffAt.comp y
        (matrixPair_contDiffAt (schurHessian_contDiffAt_two hU hu _ _ hdet hy) ξ)
    exact hpair.continuousAt.continuousWithinAt
  · exact fun y hy => schurPair_nonneg realDirections imagDirections ξ (hM y hy)
  · exact schurPair_local_supersolutions hU hu hdet hA ξ
  · exact hx₀
  · exact hzero

/-- The kernel of the actual Schur Hessian is independent of the point.
The complex Hessian's strict positivity and the Schur Hessian's weak
positivity follow from the real Hessian and the determinant-one equation. -/
theorem schurHessian_ker_eq_on
    (hd : 2 < ((n + n : ℕ) : ℝ)) {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hconn : IsPreconnected U) (hu : ContDiffOn ℝ 4 u U)
    (hdet : ∀ y ∈ U, (complexHessian realDirections imagDirections u y).det = 1)
    (hR : ∀ y ∈ U, (realBlockHessian realDirections imagDirections u y).PosSemidef)
    {x y : E} (hx : x ∈ U) (hy : y ∈ U) :
    LinearMap.ker (schurHessian realDirections imagDirections u x).mulVecLin =
      LinearMap.ker (schurHessian realDirections imagDirections u y).mulVecLin := by
  have hu2 (z : E) (hz : z ∈ U) : ContDiffAt ℝ 2 u z :=
    (hu.contDiffAt (hU.mem_nhds hz)).of_le (by norm_num)
  have hA (z : E) (hz : z ∈ U) := complexHessian_posDef_of_realBlockHessian
    (hu2 z hz) realDirections imagDirections (hR z hz) (hdet z hz)
  have hM (z : E) (hz : z ∈ U) : (schurHessian realDirections imagDirections u z).PosSemidef := by
    obtain ⟨hRC, hCM⟩ := realBlockHessian_posSemidef_equivalences
      (hu2 z hz) realDirections imagDirections (hA z hz)
    exact hCM.mp (hRC.mp (hR z hz))
  have hprop (z w : E) (hz : z ∈ U) (hw : w ∈ U) (ξ : Fin n → ℂ)
      (hξ : (schurHessian realDirections imagDirections u z).mulVec ξ = 0) :
      (schurHessian realDirections imagDirections u w).mulVec ξ = 0 := by
    have hzero := (schurPair_re_eq_zero_iff realDirections imagDirections ξ (hM z hz)).mpr hξ
    exact (schurPair_re_eq_zero_iff realDirections imagDirections ξ (hM w hw)).mp
      (schurPair_eq_zero_on_connected hd hU hconn hu hdet hA hM ξ hz hzero hw)
  ext ξ
  exact ⟨hprop x y hx hy ξ, hprop y x hy hx ξ⟩


/-- Lemma 2.5. The Schur Hessian and the real Hessian have constant rank
for the actual determinant-one equation on a connected domain. -/
theorem schur_and_realHessian_rank_constant
    (hd : 2 < ((n + n : ℕ) : ℝ)) {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hconn : IsPreconnected U) (hu : ContDiffOn ℝ 4 u U)
    (hdet : ∀ y ∈ U, (complexHessian realDirections imagDirections u y).det = 1)
    (hR : ∀ y ∈ U, (realBlockHessian realDirections imagDirections u y).PosSemidef)
    {x y : E} (hx : x ∈ U) (hy : y ∈ U) :
    (schurHessian realDirections imagDirections u x).rank =
      (schurHessian realDirections imagDirections u y).rank ∧
    (realBlockHessian realDirections imagDirections u x).rank =
      (realBlockHessian realDirections imagDirections u y).rank := by
  have hker := schurHessian_ker_eq_on hd hU hconn hu hdet hR hx hy
  have hnx := (schurHessian realDirections imagDirections u x).mulVecLin.finrank_range_add_finrank_ker
  have hny := (schurHessian realDirections imagDirections u y).mulVecLin.finrank_range_add_finrank_ker
  have hSchur : (schurHessian realDirections imagDirections u x).rank =
      (schurHessian realDirections imagDirections u y).rank := by
    rw [hker] at hnx
    exact Nat.add_right_cancel (hnx.trans hny.symm)
  have hreal (z : E) (hz : z ∈ U) :
      (realBlockHessian realDirections imagDirections u z).rank =
        (schurHessian realDirections imagDirections u z).rank + Fintype.card (Fin n) := by
    have hz2 : ContDiffAt ℝ 2 u z := (hu.contDiffAt (hU.mem_nhds hz)).of_le (by norm_num)
    exact realBlockHessian_rank_eq_schur hz2 realDirections imagDirections
      (complexHessian_posDef_of_realBlockHessian hz2 realDirections imagDirections (hR z hz) (hdet z hz))
  exact ⟨hSchur, (hreal x hx).trans ((congrArg (· + Fintype.card (Fin n)) hSchur).trans (hreal y hy).symm)⟩

end CHS.Analysis
