import CHS.Analysis.HessianOscillationStep
import CHS.Analysis.GeometricOscillationDecay

/-!
# The uniform Hessian Holder bound for a global C4 representative

Only the equation, positive complex Hessian and bounded real Hessian on
B(0,3/2) are used. Eighth-scale contraction and the actual compact extrema
give the estimate on B(0,1), with constants chosen before the potential.
-/

set_option autoImplicit false
noncomputable section

open DeGiorgi Set Metric Matrix
open scoped BigOperators ComplexOrder ContDiff Matrix.Norms.Elementwise

namespace CHS.Analysis

open CHS.Calculus CHS.Algebra

variable {n : ℕ}
local notation "E" => AmbientSpace (n + n)
local notation "J" => Fin n ⊕ Fin n

theorem realBlockHessian_norm_le_of_euclidean_bound {u : E → ℝ} {x : E} {M : ℝ}
    (hM : 0 ≤ M) (hbound : ∀ i j, |euclideanHessian u x i j| ≤ M) :
    ‖realBlockHessian realDirections imagDirections u x‖ ≤ M := by
  rw [Matrix.norm_le_iff hM]
  intro i j
  have h := hbound (finSumFinEquiv i) (finSumFinEquiv j)
  simpa only [realBlockHessian, blockDirection_eq_single, euclideanHessian, Real.norm_eq_abs] using h

theorem hessianDirectionalOscillation_le {u : E → ℝ} (hu : ContDiff ℝ 4 u)
    (t : Finset (J → ℝ)) {x₀ : E} {R M : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hbound : ∀ x ∈ closedBall x₀ R, ‖realBlockHessian realDirections imagDirections u x‖ ≤ M) :
    hessianDirectionalOscillation t u x₀ R ≤
      2 * M * ∑ z : t, realMatrixQuadraticWeight z.1 := by
  have habs (z : t) (x : E) (hx : x ∈ closedBall x₀ R) :
      |hessianObservable u z.1 x| ≤ realMatrixQuadraticWeight z.1 * M :=
    (abs_realMatrixQuadratic_le _ _).trans
      (mul_le_mul_of_nonneg_left (hbound x hx) (sq_nonneg _))
  have hosc (z : t) : compactOsc (hessianObservable u z.1) (closedBall x₀ R) ≤
      2 * M * realMatrixQuadraticWeight z.1 := by
    apply compactOsc_le_of_sub_le (isCompact_closedBall _ _)
      ⟨x₀, mem_closedBall_self hR⟩ (hessianObservable_continuous hu z.1).continuousOn
    intro x hx y hy
    have h1 := (abs_le.mp (habs z x hx)).2
    have h2 := (abs_le.mp (habs z y hy)).1
    nlinarith
  calc
    _ ≤ ∑ z : t, 2 * M * realMatrixQuadraticWeight z.1 := Finset.sum_le_sum fun z _ => hosc z
    _ = _ := (Finset.mul_sum ..).symm

theorem exists_uniform_hessian_holder_global_representative
    (hn : 2 ≤ n) {M : ℝ} (hM : 0 ≤ M) :
    ∃ α C : ℝ, 0 < α ∧ α < 1 ∧ 0 < C ∧
      ∀ u : E → ℝ, ContDiff ℝ 4 u →
      (∀ x ∈ ball (0 : E) (3 / 2 : ℝ),
        (complexHessian realDirections imagDirections u x).det = 1) →
      (∀ x ∈ ball (0 : E) (3 / 2 : ℝ),
        (complexHessian realDirections imagDirections u x).PosDef) →
      (∀ x ∈ ball (0 : E) (3 / 2 : ℝ), ∀ i j, |euclideanHessian u x i j| ≤ M) →
      ∀ x ∈ ball (0 : E) 1, ∀ y ∈ ball (0 : E) 1,
        ‖realBlockHessian realDirections imagDirections u x -
          realBlockHessian realDirections imagDirections u y‖ ≤ C * ‖x - y‖ ^ α := by
  classical
  obtain ⟨t, D, hD, θ, hθ, hθ1, hstep⟩ := exists_uniform_hessian_oscillation_step hn M
  obtain ⟨α, hα, hα1, hdecay⟩ := exists_exponent_for_eighth_decay hθ hθ1
  let S : ℝ := ∑ z : t, realMatrixQuadraticWeight z.1
  have hS : 0 ≤ S := Finset.sum_nonneg fun z _ => sq_nonneg _
  let B : ℝ := 2 * M * S
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let C : ℝ := max 1 (max (64 * D * B) (16 * M))
  have hC : 0 < C := zero_lt_one.trans_le (le_max_left _ _)
  have hCnear : 64 * D * B ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCfar : 16 * M ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨α, C, hα, hα1, hC, ?_⟩
  intro u hu hdet hA hentry x hx y hy
  let U : Set E := ball 0 (3 / 2 : ℝ)
  have hsmall : ball (0 : E) 1 ⊆ U := ball_subset_ball (by norm_num)
  have hnorm (z : E) (hz : z ∈ U) : ‖realBlockHessian realDirections imagDirections u z‖ ≤ M :=
    realBlockHessian_norm_le_of_euclidean_bound hM (hentry z hz)
  have hclosed (r : ℝ) (hr : r ≤ 1 / 8) : closedBall x (2 * r) ⊆ U := by
    intro z hz
    have hx' : dist x (0 : E) < 1 := hx
    have hz' : dist z x ≤ 2 * r := hz
    change dist z (0 : E) < 3 / 2
    have ht := dist_triangle z x (0 : E)
    linarith
  have hlocal (r : ℝ) (hr : 0 < r) (hrsmall : r ≤ 1 / 8) :=
    hstep U isOpen_ball u hu hdet hA hentry x r hr (hclosed r hrsmall)
  let F : ℝ → ℝ := hessianDirectionalOscillation t u x
  have hiter : ∀ k : ℕ, F ((1 / 8 : ℝ) * (1 / 8 : ℝ) ^ k) ≤ θ ^ k * F (1 / 8) :=
    eighth_radius_contraction_iterate hθ.le (by norm_num)
      (fun r hr hrsmall => (hlocal r hr hrsmall).1)
  have hbase : F (1 / 8) ≤ B := by
    apply hessianDirectionalOscillation_le hu t (by norm_num) hM
    intro z hz
    exact hnorm z (hclosed (1 / 8) le_rfl
      ((closedBall_subset_closedBall (by norm_num : (1 / 8 : ℝ) ≤ 2 * (1 / 8))) hz))
  by_cases hxy : x = y
  · subst y
    simp only [sub_self, norm_zero, Real.zero_rpow hα.ne', mul_zero, le_refl]
  have hδ : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  by_cases hnear : ‖x - y‖ ≤ 1 / 8
  · obtain ⟨k, hkdist, hkpow⟩ := exists_eighth_scale_power_bound hθ.le hα.le hα1.le hdecay hδ hnear
    let r : ℝ := (1 / 8 : ℝ) * (1 / 8 : ℝ) ^ k
    have hr : 0 < r := by dsimp [r]; positivity
    have hrsmall : r ≤ 1 / 8 := by
      exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (by norm_num) (by norm_num) :
        (1 / 8 : ℝ) ^ k ≤ 1) (by norm_num : 0 ≤ (1 / 8 : ℝ))).trans_eq (mul_one _)
    have hyball : y ∈ closedBall x r := by
      simpa only [mem_closedBall, dist_eq_norm, norm_sub_rev] using hkdist
    have hpair := (hlocal r hr hrsmall).2 x (mem_closedBall_self hr.le) y hyball
    calc
      _ ≤ D * F r := hpair
      _ ≤ D * (θ ^ k * F (1 / 8)) := mul_le_mul_of_nonneg_left (hiter k) hD.le
      _ ≤ D * (θ ^ k * B) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hbase (pow_nonneg hθ.le _)) hD.le
      _ ≤ D * ((64 * ‖x - y‖ ^ α) * B) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hkpow hB) hD.le
      _ = (64 * D * B) * ‖x - y‖ ^ α := by ring
      _ ≤ C * ‖x - y‖ ^ α := mul_le_mul_of_nonneg_right hCnear (Real.rpow_nonneg hδ.le _)
  · have hδlarge : (1 / 8 : ℝ) ≤ ‖x - y‖ := (lt_of_not_ge hnear).le
    have hpow : (1 / 8 : ℝ) ≤ ‖x - y‖ ^ α :=
      (Real.self_le_rpow_of_le_one (by norm_num : 0 ≤ (1 / 8 : ℝ)) (by norm_num) hα1.le).trans
        (Real.rpow_le_rpow (by norm_num) hδlarge hα.le)
    calc
      _ ≤ ‖realBlockHessian realDirections imagDirections u x‖ +
          ‖realBlockHessian realDirections imagDirections u y‖ := norm_sub_le _ _
      _ ≤ 2 * M := by linarith [hnorm x (hsmall hx), hnorm y (hsmall hy)]
      _ ≤ (16 * M) * ‖x - y‖ ^ α := by nlinarith
      _ ≤ C * ‖x - y‖ ^ α := mul_le_mul_of_nonneg_right hCfar (Real.rpow_nonneg hδ.le _)

end CHS.Analysis
