import CHS.Calculus.HessianKernelPositivity
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Domination of real Hessian forms with a common kernel

The strictly positive form on the orthogonal slice has a positive minimum
on its unit sphere.  This proves the quantitative comparison used to
show that the complex Hessian of the section ellipsoid is positive.
-/

set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ContDiff

namespace CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

theorem realHessian_projection_quadratic
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x)
    (K : Submodule ℝ E) (hK : K ≤ (realHessian u x).ker) (v : E) :
    realHessian u x v v = realHessian u x
      (Kᗮ.orthogonalProjectionOnto v : E) (Kᗮ.orthogonalProjectionOnto v : E) := by
  have hN : realHessian u x (K.orthogonalProjectionOnto v : E) = 0 :=
    hK (K.orthogonalProjectionOnto v).property
  have hsplit : (Kᗮ.orthogonalProjectionOnto v : E) + (K.orthogonalProjectionOnto v : E) = v := by
    rw [Submodule.orthogonalProjectionOnto_orthogonal]
    change v - K.starProjection v + K.starProjection v = v
    exact sub_add_cancel _ _
  calc
    _ = realHessian u x ((Kᗮ.orthogonalProjectionOnto v : E) + (K.orthogonalProjectionOnto v : E))
      ((Kᗮ.orthogonalProjectionOnto v : E) + (K.orthogonalProjectionOnto v : E)) := by rw [hsplit]
    _ = _ := by
      simp only [map_add, add_apply, hN, zero_apply, zero_add, add_zero]
      rw [realHessian_symm hu (Kᗮ.orthogonalProjectionOnto v) (K.orthogonalProjectionOnto v),
        hN, zero_apply, add_zero]

theorem exists_pos_realHessian_domination_of_kernel_inclusion
    {u q : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) (hq : ContDiffAt ℝ 2 q x)
    (hQ : ∀ v : E, 0 ≤ realHessian q x v v)
    (K : Submodule ℝ E) (hqker : (realHessian q x).ker = K)
    (huK : K ≤ (realHessian u x).ker) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ v : E, ε * realHessian u x v v ≤ realHessian q x v v := by
  let P := Kᗮ.orthogonalProjectionOnto
  have hQK : K ≤ (realHessian q x).ker := le_of_eq hqker.symm
  rcases subsingleton_or_nontrivial Kᗮ with htrivial | hnontrivial
  · letI := htrivial
    have hPzero (v : E) : P v = 0 := Subsingleton.elim _ _
    refine ⟨1, by norm_num, ?_⟩
    intro v
    rw [realHessian_projection_quadratic hu K huK v,
      realHessian_projection_quadratic hq K hQK v]
    change 1 * realHessian u x (P v : E) (P v : E) ≤ realHessian q x (P v : E) (P v : E)
    rw [hPzero]
    simp
  · letI := hnontrivial
    let F : Kᗮ → ℝ := fun v => realHessian q x (v : E) (v : E)
    have hF : Continuous F :=
      ((realHessian q x).continuous.comp Kᗮ.subtypeL.continuous).clm_apply Kᗮ.subtypeL.continuous
    have hs : (sphere (0 : Kᗮ) 1).Nonempty := NormedSpace.sphere_nonempty.mpr (by norm_num)
    obtain ⟨p, hp, hmin⟩ := (isCompact_sphere (0 : Kᗮ) 1).exists_isMinOn hs hF.continuousOn
    have hpnorm : ‖p‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hp
    have hpne : p ≠ 0 := by intro hz; simp [hz] at hpnorm
    have hFp : 0 < F p := realHessian_pos_on_orthogonal_kernel hq hQ K hqker p hpne
    have hLower (y : Kᗮ) : F p * ‖y‖ ^ 2 ≤ F y := by
      by_cases hy : y = 0
      · simp [hy, F]
      · have hyn : 0 < ‖y‖ := norm_pos_iff.mpr hy
        have hz : ‖(‖y‖⁻¹ • y : Kᗮ)‖ = 1 := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hyn), inv_mul_cancel₀ hyn.ne']
        have hm := hmin (by simpa only [mem_sphere, dist_zero_right] using hz)
        have hscale : F (‖y‖⁻¹ • y) * ‖y‖ ^ 2 = F y := by
          dsimp only [F]
          simp only [SetLike.val_smul, map_smul, smul_apply, smul_eq_mul]
          field_simp
          <;> ring
        have hmul := mul_le_mul_of_nonneg_right hm (sq_nonneg ‖y‖)
        rwa [hscale] at hmul
    let N := ‖realHessian u x‖
    have hN : 0 ≤ N := norm_nonneg (realHessian u x)
    let ε := F p / (N + 1)
    have hε : 0 < ε := div_pos hFp (by linarith)
    have heq : ε * (N + 1) = F p := div_mul_cancel₀ _ (by positivity)
    have hcoef : ε * N ≤ F p := by nlinarith
    have hUpper (y : Kᗮ) : realHessian u x (y : E) (y : E) ≤ N * ‖y‖ ^ 2 := by
      calc
        _ ≤ ‖realHessian u x (y : E) (y : E)‖ := le_abs_self _
        _ ≤ ‖realHessian u x‖ * ‖(y : E)‖ * ‖(y : E)‖ :=
          (realHessian u x).le_opNorm₂ y y
        _ = _ := by change N * ‖y‖ * ‖y‖ = N * ‖y‖ ^ 2; ring
    refine ⟨ε, hε, ?_⟩
    intro v
    rw [realHessian_projection_quadratic hu K huK v,
      realHessian_projection_quadratic hq K hQK v]
    change ε * realHessian u x (P v : E) (P v : E) ≤ F (P v)
    calc
      _ ≤ ε * (N * ‖P v‖ ^ 2) := mul_le_mul_of_nonneg_left (hUpper (P v)) hε.le
      _ = (ε * N) * ‖P v‖ ^ 2 := by ring
      _ ≤ F p * ‖P v‖ ^ 2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
      _ ≤ F (P v) := hLower (P v)

end CHS.Calculus
