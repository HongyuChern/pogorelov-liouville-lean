import CHS.Analysis.ConvexGradient
import CHS.Calculus.AffinePullback
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Bounded sections on a strictly convex transverse slice

The positivity away from the normalized minimum is proved using actual
second derivatives along a line.  Compactness of the unit sphere and
convexity then give linear growth outside the unit ball.  This is the
coercivity step preceding the ellipsoid normalization in Proposition 3.2.
-/

set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ContDiff Topology

namespace CHS.Sections

open CHS.Calculus CHS.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem positive_off_zero_of_strict_realHessian
    {u : E → ℝ} (hu : ContDiff ℝ 2 u) (hu0 : u 0 = 0) (hD0 : fderiv ℝ u 0 = 0)
    (hH : ∀ x v : E, v ≠ 0 → 0 < realHessian u x v v) :
    ∀ v : E, v ≠ 0 → 0 < u v := by
  intro v hv
  let line := fun t : ℝ => t • v
  let f := fun t : ℝ => u (line t)
  let g := fun t : ℝ => fderiv ℝ u (line t) v
  have hline (t : ℝ) : HasDerivAt line v t := by
    simpa only [line, id_eq, one_smul] using (hasDerivAt_id t).smul_const v
  have hf (t : ℝ) : HasDerivAt f (g t) t :=
    (hu.differentiable (by norm_num) (line t)).hasFDerivAt.comp_hasDerivAt t (hline t)
  have hg (t : ℝ) : HasDerivAt g (realHessian u (line t) v v) t := by
    have hd : DifferentiableAt ℝ (fderiv ℝ u) (line t) :=
      (hu.contDiffAt.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have heval := hd.hasFDerivAt.clm_apply (hasFDerivAt_const v (line t))
    have hEval : HasFDerivAt (fun y => fderiv ℝ u y v)
        ((realHessian u (line t)).flip v) (line t) := by
      simpa only [realHessian, ContinuousLinearMap.comp_zero, zero_add] using heval
    exact hEval.comp_hasDerivAt t (hline t)
  have hg0 : g 0 = 0 := by simp [g, line, hD0]
  have hgmono : StrictMonoOn g (Icc 0 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 1)
    · intro t ht
      exact (hg t).continuousAt.continuousWithinAt
    · intro t ht
      rw [(hg t).deriv]
      exact hH (line t) v hv
  have hfmono : StrictMonoOn f (Icc 0 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 1)
    · intro t ht
      exact (hf t).continuousAt.continuousWithinAt
    · intro t ht
      have ht' : t ∈ Icc 0 1 := interior_subset ht
      rw [interior_Icc] at ht
      rw [(hf t).deriv, ← hg0]
      exact hgmono (by norm_num) ht' ht.1
  have h := hfmono (by norm_num : (0 : ℝ) ∈ Icc 0 1)
    (by norm_num : (1 : ℝ) ∈ Icc 0 1) (by norm_num)
  simpa only [f, line, zero_smul, one_smul, hu0] using h

theorem linear_growth_of_positive_unit_sphere
    {u : E → ℝ} (hconv : ConvexOn ℝ univ u) (hu0 : u 0 = 0)
    {c : ℝ} (hsphere : ∀ x : E, ‖x‖ = 1 → c ≤ u x) :
    ∀ x : E, 1 ≤ ‖x‖ → c * ‖x‖ ≤ u x := by
  intro x hx
  have hn : 0 < ‖x‖ := lt_of_lt_of_le (by norm_num) hx
  let t := ‖x‖⁻¹
  have ht0 : 0 ≤ t := inv_nonneg.mpr hn.le
  have ht1 : t ≤ 1 := inv_le_one_of_one_le₀ hx
  have hunit : ‖t • x‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
    exact inv_mul_cancel₀ hn.ne'
  have hcv := hconv.2 (mem_univ (0 : E)) (mem_univ x)
    (sub_nonneg.mpr ht1) ht0 (by ring : (1 - t) + t = 1)
  have hcv' : u (t • x) ≤ t * u x := by
    simpa only [smul_zero, zero_add, hu0, smul_eq_mul, mul_zero, zero_add] using hcv
  have hsmall : c ≤ t * u x := (hsphere (t • x) hunit).trans hcv'
  have hscale := mul_le_mul_of_nonneg_right hsmall hn.le
  calc
    c * ‖x‖ ≤ (t * u x) * ‖x‖ := hscale
    _ = u x := by dsimp [t]; field_simp

theorem bounded_sublevels_of_normalized_positive_convex
    [FiniteDimensional ℝ E] {u : E → ℝ} (hu : Continuous u)
    (hconv : ConvexOn ℝ univ u) (hu0 : u 0 = 0)
    (hpos : ∀ x : E, x ≠ 0 → 0 < u x) (h : ℝ) :
    Bornology.IsBounded {x | u x < h} := by
  rcases subsingleton_or_nontrivial E with htrivial | hnontrivial
  · letI := htrivial
    exact (Set.toFinite {x | u x < h}).isBounded
  · letI := hnontrivial
    have hs : (sphere (0 : E) 1).Nonempty := NormedSpace.sphere_nonempty.mpr (by norm_num)
    obtain ⟨p, hp, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn hs hu.continuousOn
    have hpnorm : ‖p‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hp
    have hpne : p ≠ 0 := by intro hp0; simp [hp0] at hpnorm
    have hc : 0 < u p := hpos p hpne
    have hgrowth := linear_growth_of_positive_unit_sphere hconv hu0
      (c := u p) (fun x hx => hmin (by simpa only [mem_sphere, dist_zero_right] using hx))
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨max 1 (h / u p), ?_⟩
    intro x hx
    by_cases hnorm : 1 ≤ ‖x‖
    · have hx' : u x < h := hx
      have hbound : ‖x‖ ≤ h / u p := (le_div_iff₀ hc).mpr (by
        have hg := hgrowth x hnorm
        nlinarith)
      exact hbound.trans (le_max_right _ _)
    · exact (le_of_lt (lt_of_not_ge hnorm)).trans (le_max_left _ _)

end CHS.Sections

namespace CHS.Sections

open CHS.Calculus CHS.Analysis

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable [FiniteDimensional ℝ F]

theorem compact_closure_sublevel_of_strict_realHessian
    {u : F → ℝ} (hu : ContDiff ℝ 2 u)
    (hu0 : u 0 = 0) (hD0 : fderiv ℝ u 0 = 0)
    (hH : ∀ x v : F, v ≠ 0 → 0 < realHessian u x v v) (h : ℝ) :
    IsCompact (closure {x | u x < h}) := by
  have hconv : ConvexOn ℝ univ u := convexOn_of_realHessian_nonneg (u := u) isOpen_univ
    (convex_univ) hu.contDiffOn (fun x hx v => by
      by_cases hv : v = 0
      · simp [hv]
      · exact (hH x v hv).le)
  exact (bounded_sublevels_of_normalized_positive_convex hu.continuous hconv hu0
    (positive_off_zero_of_strict_realHessian hu hu0 hD0 hH) h).isCompact_closure

end CHS.Sections
