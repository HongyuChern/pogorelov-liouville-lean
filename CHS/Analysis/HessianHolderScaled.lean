import CHS.Analysis.HessianHolder
import CHS.Calculus.EuclideanRescaling

/-!
# Radius-independent local Hessian estimate

The exact potential rescaling R^-2 u(x0 + R x) keeps both Hessians
unchanged.  The constants below are chosen before the centre, radius,
domain and potential.  Only local C4 regularity on B(x0,2R) is used.
-/

set_option autoImplicit false
noncomputable section

open DeGiorgi Set Metric Matrix
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise

namespace CHS.Analysis

open CHS.Calculus

variable {n : ℕ}
local notation "E" => AmbientSpace (n + n)

theorem exists_scaled_complexMongeAmpere_hessian_holder
    (hn : 2 ≤ n) {M : ℝ} (hM : 0 ≤ M) :
    ∃ α C : ℝ, 0 < α ∧ α < 1 ∧ 0 < C ∧
      ∀ (x₀ : E) (R : ℝ), 0 < R → ∀ u : E → ℝ,
      ContDiffOn ℝ 4 u (ball x₀ (2 * R)) →
      (∀ x ∈ ball x₀ (2 * R), (complexHessian realDirections imagDirections u x).det = 1) →
      (∀ x ∈ ball x₀ (2 * R), (complexHessian realDirections imagDirections u x).PosDef) →
      (∀ x ∈ ball x₀ (2 * R), ∀ i j, |euclideanHessian u x i j| ≤ M) →
      ∀ x ∈ ball x₀ R, ∀ y ∈ ball x₀ R,
        ‖realBlockHessian realDirections imagDirections u x -
          realBlockHessian realDirections imagDirections u y‖ ≤
            C * (‖x - y‖ / R) ^ α := by
  obtain ⟨α, C, hα, hα1, hC, hunit⟩ := exists_local_complexMongeAmpere_hessian_holder hn hM
  refine ⟨α, C, hα, hα1, hC, ?_⟩
  intro x₀ R hR u hu hdet hA hentry
  let v := euclideanRescalePotential u x₀ R
  have hmap : MapsTo (fun z : E => x₀ + R • z) (ball (0 : E) 2) (ball x₀ (2 * R)) := by
    intro z hz
    rw [mem_ball, dist_eq_norm]
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hR]
    have hz' : ‖z‖ < 2 := by simpa only [mem_ball, dist_zero_right] using hz
    nlinarith
  have hv : ContDiffOn ℝ 4 v (ball (0 : E) 2) :=
    euclideanRescalePotential_contDiffOn hu x₀ R hmap
  have hH (z : E) (hz : z ∈ ball (0 : E) 2) :
      realHessian v z = realHessian u (x₀ + R • z) :=
    realHessian_euclideanRescalePotential hR.ne'
      ((hu.contDiffAt (isOpen_ball.mem_nhds (hmap hz))).of_le (by norm_num))
  have hcomplex (z : E) (hz : z ∈ ball (0 : E) 2) :
      complexHessian realDirections imagDirections v z =
        complexHessian realDirections imagDirections u (x₀ + R • z) :=
    complexHessian_euclideanRescalePotential realDirections imagDirections hR.ne'
      ((hu.contDiffAt (isOpen_ball.mem_nhds (hmap hz))).of_le (by norm_num))
  have hvdet (z : E) (hz : z ∈ ball (0 : E) 2) :
      (complexHessian realDirections imagDirections v z).det = 1 := by
    rw [hcomplex z hz]
    exact hdet _ (hmap hz)
  have hvA (z : E) (hz : z ∈ ball (0 : E) 2) :
      (complexHessian realDirections imagDirections v z).PosDef := by
    rw [hcomplex z hz]
    exact hA _ (hmap hz)
  have hventry (z : E) (hz : z ∈ ball (0 : E) 2) (i j : Fin (n + n)) :
      |euclideanHessian v z i j| ≤ M := by
    simp only [euclideanHessian, hH z hz]
    exact hentry _ (hmap hz) i j
  intro x hx y hy
  let ξ : E := R⁻¹ • (x - x₀)
  let η : E := R⁻¹ • (y - x₀)
  have hξ : ξ ∈ ball (0 : E) 1 := by
    have hx' : ‖x - x₀‖ < R := by simpa only [mem_ball, dist_eq_norm] using hx
    simp only [ξ, mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hR)]
    exact (inv_mul_lt_iff₀ hR).mpr (by simpa using hx')
  have hη : η ∈ ball (0 : E) 1 := by
    have hy' : ‖y - x₀‖ < R := by simpa only [mem_ball, dist_eq_norm] using hy
    simp only [η, mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hR)]
    exact (inv_mul_lt_iff₀ hR).mpr (by simpa using hy')
  have hbackx : x₀ + R • ξ = x := by
    simp only [ξ, smul_smul, mul_inv_cancel₀ hR.ne', one_smul, add_sub_cancel]
  have hbacky : x₀ + R • η = y := by
    simp only [η, smul_smul, mul_inv_cancel₀ hR.ne', one_smul, add_sub_cancel]
  have hξ2 := (ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2)) hξ
  have hη2 := (ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2)) hη
  have hblockx : realBlockHessian realDirections imagDirections v ξ =
      realBlockHessian realDirections imagDirections u x := by
    ext i j
    change realHessian v ξ _ _ = realHessian u x _ _
    rw [hH ξ hξ2, hbackx]
  have hblocky : realBlockHessian realDirections imagDirections v η =
      realBlockHessian realDirections imagDirections u y := by
    ext i j
    change realHessian v η _ _ = realHessian u y _ _
    rw [hH η hη2, hbacky]
  have hnorm : ‖ξ - η‖ = ‖x - y‖ / R := by
    have hdiff : ξ - η = R⁻¹ • (x - y) := by
      dsimp [ξ, η]
      rw [← smul_sub]
      congr 1
      abel
    rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
    ring
  have h := hunit v hv hvdet hvA hventry ξ hξ η hη
  rwa [hblockx, hblocky, hnorm] at h

theorem exists_scaled_complexMongeAmpere_hessian_holder_entry
    (hn : 2 ≤ n) {M : ℝ} (hM : 0 ≤ M) :
    ∃ α C : ℝ, 0 < α ∧ α < 1 ∧ 0 < C ∧
      ∀ (x₀ : E) (R : ℝ), 0 < R → ∀ u : E → ℝ,
      ContDiffOn ℝ 4 u (ball x₀ (2 * R)) →
      (∀ x ∈ ball x₀ (2 * R), (complexHessian realDirections imagDirections u x).det = 1) →
      (∀ x ∈ ball x₀ (2 * R), (complexHessian realDirections imagDirections u x).PosDef) →
      (∀ x ∈ ball x₀ (2 * R), ∀ i j, |euclideanHessian u x i j| ≤ M) →
      ∀ x ∈ ball x₀ R, ∀ y ∈ ball x₀ R, ∀ i j,
        |euclideanHessian u x i j - euclideanHessian u y i j| ≤
          C * (‖x - y‖ / R) ^ α := by
  obtain ⟨α, C, hα, hα1, hC, hbound⟩ := exists_scaled_complexMongeAmpere_hessian_holder hn hM
  refine ⟨α, C, hα, hα1, hC, ?_⟩
  intro x₀ R hR u hu hdet hA hentry x hx y hy i j
  exact (abs_euclideanHessian_sub_le_block_norm u x y i j).trans
    (hbound x₀ R hR u hu hdet hA hentry x hx y hy)

end CHS.Analysis
