import CHS.Analysis.DirectionalSupersolutions

/-!
# Actual directional supersolutions with only local hypotheses

The equation and positive branch are required only on the open domain U.
The smooth-cutoff flux theorem supplies complete H01 weak supersolutions
on every relatively compact ball, with the fixed local coefficient field.
-/

set_option autoImplicit false
noncomputable section

open DeGiorgi Set Metric Filter
open scoped BigOperators ComplexOrder ContDiff Topology

namespace CHS.Analysis

open CHS.Calculus

variable {n : ℕ} [NeZero (n + n)]
local notation "E" => AmbientSpace (n + n)

theorem scaled_linearized_local_supersolution_on_ball
    {U : Set E} (hU : IsOpen U) {u v : E → ℝ}
    (hu : ContDiffOn ℝ 4 u U) (hv : ContDiffOn ℝ 2 v U)
    (hdet : ∀ x ∈ U, (complexHessian realDirections imagDirections u x).det = 1)
    {c : ℝ} (hc : 0 < c) (B : NormalizedEllipticCoeff (n + n) U)
    (hB : ∀ x ∈ U, B.1.a x = c⁻¹ • complexLinearizedCoeff u x)
    (hlin : ∀ x ∈ U, (∑ i, ∑ j, complexLinearizedCoeff u x i j * euclideanHessian v x i j) ≤ 0)
    {x₀ : E} {r R : ℝ} (hr : 0 < r) (hrR : r < R) (hclosed : closedBall x₀ R ⊆ U) :
    IsSupersolution (B.restrict
      ((ball_subset_closedBall.trans (closedBall_subset_closedBall hrR.le)).trans hclosed)).1 v := by
  have hdetAt (x : E) (hx : x ∈ U) :
      (fun y => (complexHessian realDirections imagDirections u y).det) =ᶠ[𝓝 x] (fun _ => 1) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hdet y hy
  have hcoeff (i j : Fin (n + n)) (x : E) (hx : x ∈ U) :
      ContDiffAt ℝ 2 (fun y => complexLinearizedCoeff u y i j) x :=
    complexLinearizedCoeff_contDiffAt (hu.contDiffAt (hU.mem_nhds hx)) (hdetAt x hx) i j
  let F (y : E) := c⁻¹ • matMulE (complexLinearizedCoeff u y) (smoothGradField v y)
  have hF (i : Fin (n + n)) : ContDiffOn ℝ 1 (fun y => F y i) U := by
    intro x hx
    apply ContDiffAt.contDiffWithinAt
    change ContDiffAt ℝ 1 (fun y => c⁻¹ *
      ∑ j, complexLinearizedCoeff u y i j * fderiv ℝ v y (EuclideanSpace.single j 1)) x
    apply contDiffAt_const.mul
    apply ContDiffAt.sum
    intro j _
    exact ((hcoeff i j x hx).of_le (by norm_num)).mul
      (((hv.contDiffAt (hU.mem_nhds hx)).fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const)
  have hsub : ball x₀ r ⊆ U :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall hrR.le)).trans hclosed
  apply supersolution_of_local_classical_flux hU hr hrR hclosed _ (hv.of_le (by norm_num)) hF
  · intro x hx
    change matMulE (B.1.a x) (smoothGradField v x) = _
    rw [hB x (hsub hx), matMulE_smul_matrix]
  · intro x hx
    have hxU := hsub hx
    rw [show F = fun y => c⁻¹ • matMulE (complexLinearizedCoeff u y)
      (smoothGradField v y) by rfl, classicalDivergence_const_smul,
      classicalDivergence_matMulE_gradient
        (fun i j => (hcoeff i j x hxU).differentiableAt (by norm_num))
        (hv.contDiffAt (hU.mem_nhds hxU))
        (complexLinearizedCoeff_divergence
          ((hu.contDiffAt (hU.mem_nhds hxU)).of_le (by norm_num)) (hdetAt x hxU))]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hc.le) (hlin x hxU)

theorem directionalHessian_local_linearized_euclidean_nonneg
    {U : Set E} (hU : IsOpen U) {u : E → ℝ} (hu : ContDiffOn ℝ 4 u U)
    (hdet : ∀ x ∈ U, (complexHessian realDirections imagDirections u x).det = 1)
    (hA : ∀ x ∈ U, (complexHessian realDirections imagDirections u x).PosDef)
    (e : E) {x : E} (hx : x ∈ U) :
    0 ≤ ∑ i, ∑ j, complexLinearizedCoeff u x i j *
      euclideanHessian (fun y => realHessian u y e e) x i j := by
  rw [← Equiv.sum_comp finSumFinEquiv]
  simp_rw [← Equiv.sum_comp finSumFinEquiv]
  simp only [complexLinearizedCoeff, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, euclideanHessian]
  have heq (i : Fin n ⊕ Fin n) : EuclideanSpace.single (finSumFinEquiv i) (1 : ℝ) =
      Sum.elim realDirections imagDirections i := by cases i <;> rfl
  simp only [heq]
  exact directionalHessian_linearized_nonneg hU hu realDirections imagDirections hdet hx (hA x hx) e

theorem directionalHessian_deficit_local_supersolution_on_ball
    {U : Set E} (hU : IsOpen U) {u : E → ℝ} (hu : ContDiffOn ℝ 4 u U)
    (hdet : ∀ x ∈ U, (complexHessian realDirections imagDirections u x).det = 1)
    (hA : ∀ x ∈ U, (complexHessian realDirections imagDirections u x).PosDef)
    {c : ℝ} (hc : 0 < c) (B : NormalizedEllipticCoeff (n + n) U)
    (hB : ∀ x ∈ U, B.1.a x = c⁻¹ • complexLinearizedCoeff u x)
    (e : E) (M : ℝ) {x₀ : E} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hclosed : closedBall x₀ R ⊆ U) :
    IsSupersolution (B.restrict
      ((ball_subset_closedBall.trans (closedBall_subset_closedBall hrR.le)).trans hclosed)).1
      (fun y => M - realHessian u y e e) := by
  have hv : ContDiffOn ℝ 2 (fun y => realHessian u y e e) U :=
    fun x hx => (realHessian_contDiffAt_two (hu.contDiffAt (hU.mem_nhds hx)) e e).contDiffWithinAt
  apply scaled_linearized_local_supersolution_on_ball hU hu (contDiffOn_const.sub hv)
    hdet hc B hB _ hr hrR hclosed
  intro x hx
  have heq : (fun y => M - realHessian u y e e) =
      fun y => -realHessian u y e e + M := by funext y; ring
  simp only [euclideanHessian, heq, realHessian_add_const, realHessian_neg,
    neg_apply, mul_neg, Finset.sum_neg_distrib, neg_nonpos]
  exact directionalHessian_local_linearized_euclidean_nonneg hU hu hdet hA e hx

end CHS.Analysis
