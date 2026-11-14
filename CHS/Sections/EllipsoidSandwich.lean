import CHS.Sections.EllipsoidInnerBall
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# An ellipsoid sandwich with the exact real dimension factor

For a bounded open convex set containing the origin, construct an actual
ellipsoid with inner radius `1` and outer radius the real dimension.
The proof constructs a determinant-maximizing enclosing ellipsoid,
proves its `1/d` inner ball by separation and an explicit perturbation,
and passes from the closed convex body to its open interior.
-/

set_option autoImplicit false
noncomputable section

open Set Metric

namespace CHS.Sections

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

theorem exists_closed_ellipsoid_sandwich
    (hd : 0 < (Module.finrank ℝ E : ℝ)) {C : Set E}
    (hcompact : IsCompact C) (hconv : Convex ℝ C) (hzero : (0 : E) ∈ interior C) :
    ∃ (a : E) (T : E ≃L[ℝ] E),
      (∀ x : E, ‖T (x - a)‖ ≤ (Module.finrank ℝ E : ℝ)⁻¹ → x ∈ C) ∧
      (∀ x ∈ C, ‖T (x - a)‖ ≤ 1) := by
  obtain ⟨A, b, hA, hfeasible, hmax⟩ :=
    exists_maximal_det_affine_ball_normalization hcompact.isBounded hzero
  let T : E ≃L[ℝ] E :=
    (LinearEquiv.ofBijective A.toLinearMap (linearMap_bijective_of_det_pos A hA)).toContinuousLinearEquiv
  let C' : Set E := (fun x => A x + b) '' C
  have hcompact' : IsCompact C' := hcompact.image (A.continuous.add continuous_const)
  have hconv' : Convex ℝ C' := by
    have hh := (hconv.linear_image A.toLinearMap).translate b
    rw [image_image] at hh
    change Convex ℝ ((fun x => b + A x) '' C) at hh
    simpa only [C', add_comm] using hh
  have hne' : C'.Nonempty := (nonempty_of_mem (interior_subset hzero)).image _
  have hball' : ∀ x ∈ C', ‖x‖ ≤ 1 := by
    rintro x ⟨y, hy, rfl⟩
    exact hfeasible y hy
  have hmax' : ∀ (S : E →L[ℝ] E) (t : E), AffineBallFeasible C' (S, t) → S.det ≤ 1 := by
    intro S t hSt
    have hcomp : AffineBallFeasible C (S.comp A, S b + t) := by
      intro x hx
      have hx' : A x + b ∈ C' := mem_image_of_mem _ hx
      simpa only [Prod.fst, Prod.snd, ContinuousLinearMap.comp_apply, map_add, add_assoc]
        using hSt (A x + b) hx'
    have hdet := hmax (S.comp A) (S b + t) hcomp
    change LinearMap.det (S.toLinearMap.comp A.toLinearMap) ≤ A.det at hdet
    rw [LinearMap.det_comp] at hdet
    exact (mul_le_mul_iff_of_pos_right hA).mp (by simpa only [one_mul] using hdet)
  have hinner' := inner_ball_subset_of_maximal_affine_normalization
    hd hconv' hcompact'.isClosed hne' hball' hmax'
  let a : E := T.symm (-b)
  have heq (x : E) : T (x - a) = A x + b := by
    rw [map_sub]
    dsimp only [a]
    rw [T.apply_symm_apply, sub_neg_eq_add]
    rfl
  refine ⟨a, T, ?_, fun x hx => by rw [heq]; exact hfeasible x hx⟩
  intro x hx
  have hx' : A x + b ∈ C' := hinner' (by
    rw [mem_closedBall, dist_zero_right, ← heq]
    exact hx)
  obtain ⟨y, hy, hyx⟩ := hx'
  have hxy : y = x := (linearMap_bijective_of_det_pos A hA).1 (add_right_cancel hyx)
  rwa [hxy] at hy

theorem exists_open_ellipsoid_sandwich
    (hd : 0 < (Module.finrank ℝ E : ℝ)) {U : Set E}
    (hU : IsOpen U) (hbounded : Bornology.IsBounded U) (hconv : Convex ℝ U)
    (hzero : (0 : E) ∈ U) :
    ∃ (a : E) (T : E ≃L[ℝ] E),
      (∀ x : E, ‖T (x - a)‖ < 1 → x ∈ U) ∧
      (∀ x ∈ U, ‖T (x - a)‖ < (Module.finrank ℝ E : ℝ)) := by
  have hzero' : (0 : E) ∈ interior (closure U) := by
    apply interior_mono subset_closure
    rwa [hU.interior_eq]
  obtain ⟨a, T, hinner, houter⟩ := exists_closed_ellipsoid_sandwich hd
    hbounded.isCompact_closure hconv.closure hzero'
  have hint : interior (closure U) = U := by
    rw [hconv.interior_closure_eq_interior_of_nonempty_interior
      (by rw [hU.interior_eq]; exact ⟨0, hzero⟩), hU.interior_eq]
  have hinnerOpen : ∀ x : E, ‖T (x - a)‖ < (Module.finrank ℝ E : ℝ)⁻¹ → x ∈ U := by
    intro x hx
    have hV : IsOpen {y : E | ‖T (y - a)‖ < (Module.finrank ℝ E : ℝ)⁻¹} := by
      apply isOpen_lt ?_ continuous_const
      fun_prop
    have hsub : {y : E | ‖T (y - a)‖ < (Module.finrank ℝ E : ℝ)⁻¹} ⊆ closure U :=
      fun y hy => hinner y hy.le
    have hxint : x ∈ interior (closure U) :=
      mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (hV.mem_nhds hx) hsub)
    rwa [hint] at hxint
  have houterOpen : ∀ x ∈ U, ‖T (x - a)‖ < 1 := by
    let H : E ≃ₜ E := (Homeomorph.subRight a).trans T.toHomeomorph
    have hopen : IsOpen (H '' U) := H.isOpenMap U hU
    have hsub : H '' U ⊆ closedBall (0 : E) 1 := by
      rintro _ ⟨x, hx, rfl⟩
      rw [mem_closedBall, dist_zero_right]
      change ‖T (x - a)‖ ≤ 1
      exact houter x (subset_closure hx)
    intro x hx
    have hxint : H x ∈ interior (closedBall (0 : E) 1) :=
      mem_interior_iff_mem_nhds.mpr
        (Filter.mem_of_superset (hopen.mem_nhds (mem_image_of_mem H hx)) hsub)
    rw [interior_closedBall (0 : E) (by norm_num : (1 : ℝ) ≠ 0)] at hxint
    rw [mem_ball, dist_zero_right] at hxint
    change ‖T (x - a)‖ < 1 at hxint
    exact hxint
  let D : E ≃L[ℝ] E :=
    (LinearEquiv.smulOfNeZero ℝ E (Module.finrank ℝ E : ℝ) hd.ne').toContinuousLinearEquiv
  refine ⟨a, T.trans D, ?_, ?_⟩
  · intro x hx
    apply hinnerOpen x
    change ‖(Module.finrank ℝ E : ℝ) • T (x - a)‖ < 1 at hx
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hd, mul_comm] at hx
    simpa only [one_div] using (lt_div_iff₀ hd).mpr hx
  · intro x hx
    change ‖(Module.finrank ℝ E : ℝ) • T (x - a)‖ < (Module.finrank ℝ E : ℝ)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hd]
    simpa only [mul_one] using mul_lt_mul_of_pos_left (houterOpen x hx) hd

end CHS.Sections
