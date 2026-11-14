import CHS.CoreImports
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact

/-!
# Existence of a maximum-determinant affine normalization into the unit ball

For a bounded set containing a neighborhood of the origin, the feasible
linear maps and translation vectors form a compact set.  A small scalar
multiple of the identity has positive determinant, so a maximizer is
invertible.  This is the existence step for the ellipsoid construction.
-/

set_option autoImplicit false
noncomputable section

open Set Metric
open scoped Topology

namespace CHS.Sections

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E]

def AffineBallFeasible (C : Set E) (p : (E →L[ℝ] E) × E) : Prop :=
  ∀ x ∈ C, ‖p.1 x + p.2‖ ≤ 1

theorem affineBallFeasible_bounds
    {C : Set E} {r : ℝ} (hr : 0 < r) (hball : closedBall (0 : E) r ⊆ C)
    {p : (E →L[ℝ] E) × E} (hp : AffineBallFeasible C p) :
    ‖p.1‖ ≤ 2 / r ∧ ‖p.2‖ ≤ 1 := by
  have hzero : (0 : E) ∈ C := hball (mem_closedBall_self hr.le)
  have hb : ‖p.2‖ ≤ 1 := by simpa only [map_zero, zero_add] using hp 0 hzero
  refine ⟨?_, hb⟩
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro v hv
  have hy : r • v ∈ C := hball (by
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hr, hv, mul_one])
  have hnorm : ‖p.1 (r • v)‖ ≤ 2 := by
    calc
      ‖p.1 (r • v)‖ = ‖(p.1 (r • v) + p.2) - p.2‖ := by rw [add_sub_cancel_right]
      _ ≤ ‖p.1 (r • v) + p.2‖ + ‖p.2‖ := norm_sub_le _ _
      _ ≤ 2 := by linarith [hp (r • v) hy]
  rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hr] at hnorm
  exact (le_div_iff₀ hr).mpr (by linarith)

theorem isCompact_affineBallFeasible
    {C : Set E} {r : ℝ} (hr : 0 < r) (hball : closedBall (0 : E) r ⊆ C) :
    IsCompact {p : (E →L[ℝ] E) × E | AffineBallFeasible C p} := by
  apply isCompact_iff_isClosed_bounded.mpr
  constructor
  · have heq : {p : (E →L[ℝ] E) × E | AffineBallFeasible C p} =
        ⋂ x ∈ C, {p : (E →L[ℝ] E) × E | ‖p.1 x + p.2‖ ≤ 1} := by
      ext p
      simp only [mem_setOf_eq, mem_iInter, AffineBallFeasible]
    rw [heq]
    apply isClosed_biInter
    intro x _
    apply isClosed_le ?_ continuous_const
    fun_prop
  · apply isBounded_iff_forall_norm_le.mpr
    refine ⟨max (2 / r) 1, ?_⟩
    intro p hp
    obtain ⟨hA, hb⟩ := affineBallFeasible_bounds hr hball hp
    rw [Prod.norm_def]
    exact max_le_max hA hb

theorem exists_maximal_det_affine_ball_normalization
    {C : Set E} (hbounded : Bornology.IsBounded C) (hzero : (0 : E) ∈ interior C) :
    ∃ (A : E →L[ℝ] E) (b : E), 0 < A.det ∧ AffineBallFeasible C (A, b) ∧
      ∀ (S : E →L[ℝ] E) (t : E), AffineBallFeasible C (S, t) → S.det ≤ A.det := by
  obtain ⟨r, hr, hrC⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hzero)
  have hrhalf : 0 < r / 2 := by positivity
  have hball : closedBall (0 : E) (r / 2) ⊆ C := by
    apply Subset.trans ?_ hrC
    exact closedBall_subset_ball (by linarith)
  have hcompact := isCompact_affineBallFeasible hrhalf hball
  obtain ⟨R, hR⟩ := hbounded.exists_norm_le
  let s : ℝ := (max R 0 + 1)⁻¹
  have hs : 0 < s := by dsimp [s]; positivity
  have htest : AffineBallFeasible C (s • ContinuousLinearMap.id ℝ E, 0) := by
    intro x hx
    simp only [Prod.fst, Prod.snd, smul_apply, ContinuousLinearMap.id_apply, add_zero,
      norm_smul, Real.norm_eq_abs, abs_of_pos hs]
    calc
      s * ‖x‖ ≤ s * max R 0 := mul_le_mul_of_nonneg_left ((hR x hx).trans (le_max_left R 0)) hs.le
      _ ≤ 1 := by
        dsimp [s]
        rw [← div_eq_inv_mul]
        apply (div_le_one (by positivity : 0 < max R 0 + 1)).mpr
        linarith
  have htestdet : 0 < (s • ContinuousLinearMap.id ℝ E).det := by
    change 0 < LinearMap.det (s • (LinearMap.id : E →ₗ[ℝ] E))
    rw [LinearMap.det_smul, LinearMap.det_id, mul_one]
    exact pow_pos hs _
  obtain ⟨p, hp, hmax⟩ := hcompact.exists_isMaxOn
    ⟨(s • ContinuousLinearMap.id ℝ E, 0), htest⟩
    (ContinuousLinearMap.continuous_det.comp continuous_fst).continuousOn
  exact ⟨p.1, p.2, htestdet.trans_le (hmax htest), hp, fun S t hSt => hmax hSt⟩

theorem linearMap_bijective_of_det_pos (A : E →L[ℝ] E) (hA : 0 < A.det) :
    Function.Bijective A :=
  (Module.End.isUnit_iff A.toLinearMap).mp
    ((LinearMap.isUnit_iff_isUnit_det A.toLinearMap).mpr (isUnit_iff_ne_zero.mpr hA.ne'))

end CHS.Sections
