import CHS.Analysis.GlobalEllipticity
import CHS.Calculus.DirectionalHessian

/-!
# Directional Hessian deficits are genuine weak supersolutions

The coefficient field is fixed globally.  Its restrictions retain the same
ellipticity ratio on every ball.  Classical divergence is converted to the
vendored all-H01 weak supersolution definition using actual Sobolev witnesses.
-/

set_option autoImplicit false
noncomputable section

open DeGiorgi Set Metric
open scoped BigOperators ComplexOrder ContDiff

namespace CHS.Analysis

open CHS.Calculus

theorem classicalDivergence_const_smul {d : ℕ} [NeZero d]
    (F : AmbientSpace d → AmbientSpace d) (c : ℝ) (x : AmbientSpace d) :
    classicalDivergence (fun y => c • F y) x = c * classicalDivergence F x := by
  unfold classicalDivergence
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change fderiv ℝ (fun y => c * F y i) x _ = _
  have hD := congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := fun y => F y i) c) x
  change fderiv ℝ (fun y => c * F y i) x = c • fderiv ℝ (fun y => F y i) x at hD
  rw [hD, smul_apply, smul_eq_mul]

variable {n : ℕ} [NeZero (n + n)]
local notation "E" => AmbientSpace (n + n)

theorem scaled_linearized_supersolution_on_ball
    {u v : E → ℝ} (hu : ContDiff ℝ 4 u) (hv : ContDiff ℝ 2 v)
    (hdet : ∀ x, (complexHessian realDirections imagDirections u x).det = 1)
    {c : ℝ} (hc : 0 < c) (B : NormalizedEllipticCoeff (n + n) univ)
    (hB : ∀ x, B.1.a x = c⁻¹ • complexLinearizedCoeff u x)
    (hlin : ∀ x, (∑ i, ∑ j, complexLinearizedCoeff u x i j * euclideanHessian v x i j) ≤ 0)
    (x₀ : E) (r : ℝ) :
    IsSupersolution (B.restrict (subset_univ (ball x₀ r))).1 v := by
  have hcoeff (i j : Fin (n + n)) (x : E) :
      ContDiffAt ℝ 2 (fun y => complexLinearizedCoeff u y i j) x :=
    complexLinearizedCoeff_contDiffAt hu.contDiffAt (Filter.Eventually.of_forall hdet) i j
  let F (y : E) := c⁻¹ • matMulE (complexLinearizedCoeff u y) (smoothGradField v y)
  have hF (i : Fin (n + n)) : ContDiff ℝ 1 (fun y => F y i) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    change ContDiffAt ℝ 1 (fun y => c⁻¹ *
      ∑ j, complexLinearizedCoeff u y i j * fderiv ℝ v y (EuclideanSpace.single j 1)) x
    apply contDiffAt_const.mul
    apply ContDiffAt.sum
    intro j _
    exact ((hcoeff i j x).of_le (by norm_num)).mul
      ((hv.contDiffAt.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const)
  apply supersolution_of_classical_flux_on_ball x₀ r _ (hv.of_le (by norm_num)) hF
  · intro x _
    change matMulE (B.1.a x) (smoothGradField v x) = _
    rw [hB, matMulE_smul_matrix]
  · intro x _
    rw [show F = fun y => c⁻¹ • matMulE (complexLinearizedCoeff u y)
      (smoothGradField v y) by rfl, classicalDivergence_const_smul,
      classicalDivergence_matMulE_gradient
        (fun i j => (hcoeff i j x).differentiableAt (by norm_num)) hv.contDiffAt
        (complexLinearizedCoeff_divergence (hu.of_le (by norm_num)).contDiffAt
          (Filter.Eventually.of_forall hdet))]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hc.le) (hlin x)

theorem directionalHessian_linearized_euclidean_nonneg
    {u : E → ℝ} (hu : ContDiff ℝ 4 u)
    (hdet : ∀ x, (complexHessian realDirections imagDirections u x).det = 1)
    (hA : ∀ x, (complexHessian realDirections imagDirections u x).PosDef)
    (e x : E) :
    0 ≤ ∑ i, ∑ j, complexLinearizedCoeff u x i j *
      euclideanHessian (fun y => realHessian u y e e) x i j := by
  rw [← Equiv.sum_comp finSumFinEquiv]
  simp_rw [← Equiv.sum_comp finSumFinEquiv]
  simp only [complexLinearizedCoeff, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, euclideanHessian]
  have heq (i : Fin n ⊕ Fin n) : EuclideanSpace.single (finSumFinEquiv i) (1 : ℝ) =
      Sum.elim realDirections imagDirections i := by cases i <;> rfl
  simp only [heq]
  exact directionalHessian_linearized_nonneg isOpen_univ hu.contDiffOn
    realDirections imagDirections (fun y _ => hdet y) (mem_univ x) (hA x) e

theorem directionalHessian_deficit_supersolution_on_ball
    {u : E → ℝ} (hu : ContDiff ℝ 4 u)
    (hdet : ∀ x, (complexHessian realDirections imagDirections u x).det = 1)
    (hA : ∀ x, (complexHessian realDirections imagDirections u x).PosDef)
    {c : ℝ} (hc : 0 < c) (B : NormalizedEllipticCoeff (n + n) univ)
    (hB : ∀ x, B.1.a x = c⁻¹ • complexLinearizedCoeff u x)
    (e : E) (M : ℝ) (x₀ : E) (r : ℝ) :
    IsSupersolution (B.restrict (subset_univ (ball x₀ r))).1
      (fun y => M - realHessian u y e e) := by
  have hv : ContDiff ℝ 2 (fun y => realHessian u y e e) :=
    contDiff_iff_contDiffAt.mpr fun _ => realHessian_contDiffAt_two hu.contDiffAt e e
  apply scaled_linearized_supersolution_on_ball hu (contDiff_const.sub hv) hdet hc B hB
  intro x
  have heq : (fun y => M - realHessian u y e e) =
      fun y => -realHessian u y e e + M := by funext y; ring
  simp only [euclideanHessian, heq, realHessian_add_const, realHessian_neg,
    neg_apply, mul_neg, Finset.sum_neg_distrib, neg_nonpos]
  exact directionalHessian_linearized_euclidean_nonneg hu hdet hA e x

end CHS.Analysis
