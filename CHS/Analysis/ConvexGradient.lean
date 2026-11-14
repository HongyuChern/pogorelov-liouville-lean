import CHS.Analysis.AffineSplitting
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Supporting slopes and the range of the gradient of an entire convex function

An interior point of the convex hull of finitely many gradients is an
actual gradient: subtract that linear slope and minimize the resulting
coercive convex function.
-/

set_option autoImplicit false
noncomputable section

open Metric Set MeasureTheory Filter
open scoped ContDiff Gradient InnerProductSpace Topology

namespace CHS.Analysis

open Calculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem supporting_fderiv_of_convexOn {u : E → ℝ} {U : Set E} (hconv : ConvexOn ℝ U u)
    {x y : E} (hx : x ∈ U) (hy : y ∈ U) (hu : DifferentiableAt ℝ u x) :
    u x + fderiv ℝ u x (y - x) ≤ u y := by
  let F (t : ℝ) := u (x + t • (y - x))
  let e : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x y
  have hE (t : ℝ) : e t = x + t • (y - x) := by
    change AffineMap.lineMap x y t = _
    rw [AffineMap.lineMap_apply_module, sub_smul, one_smul, smul_sub]
    abel
  have hF : ConvexOn ℝ (e ⁻¹' U) F := by
    have h := hconv.comp_affineMap e
    have hEq : u ∘ e = F := funext fun t => congrArg u (hE t)
    rwa [hEq] at h
  have hline : HasDerivAt (fun t : ℝ => x + t • (y - x)) (y - x) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (y - x)).const_add x
  have hF' : HasDerivAt F (fderiv ℝ u x (y - x)) 0 := by
    have h := hu.hasFDerivAt
    have hx0 : x + (0 : ℝ) • (y - x) = x := by simp
    exact h.comp_hasDerivAt_of_eq 0 hline hx0.symm
  have h0 : (0 : ℝ) ∈ e ⁻¹' U := by simpa [e] using hx
  have h1 : (1 : ℝ) ∈ e ⁻¹' U := by simpa [e] using hy
  have h := hF.le_slope_of_hasDerivAt h0 h1 zero_lt_one hF' 
  have h' : fderiv ℝ u x (y - x) ≤ u y - u x := by
    simpa [slope_def_field, F] using h
  linarith

theorem supporting_fderiv_of_convex {u : E → ℝ} (hconv : ConvexOn ℝ univ u)
    (hu : Differentiable ℝ u) (x y : E) :
    u x + fderiv ℝ u x (y - x) ≤ u y :=
  supporting_fderiv_of_convexOn hconv (mem_univ x) (mem_univ y) (hu x)


theorem convexOn_of_realHessian_nonneg {u : E → ℝ} {U : Set E} (hU : IsOpen U)
    (hconv : Convex ℝ U) (hu : ContDiffOn ℝ 2 u U)
    (hH : ∀ x ∈ U, ∀ v, 0 ≤ realHessian u x v v) :
    ConvexOn ℝ U u := by
  refine ⟨hconv, ?_⟩
  intro x hx y hy a b ha hb hab
  let line : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x y
  let D := line ⁻¹' U
  let v := y - x
  have hline (t : ℝ) : line t = x + t • v := by
    change AffineMap.lineMap x y t = x + t • (y - x)
    rw [AffineMap.lineMap_apply_module, sub_smul, one_smul, smul_sub]
    abel
  have hDline (t : ℝ) : HasDerivAt (fun t => line t) v t := by
    simpa only [hline, id, one_smul] using ((hasDerivAt_id t).smul_const v).const_add x
  have hD : Convex ℝ D := hconv.affine_preimage line
  let f (t : ℝ) := u (line t)
  let g (t : ℝ) := fderiv ℝ u (line t) v
  let h (t : ℝ) := realHessian u (line t) v v
  have hu' (t : ℝ) (ht : t ∈ D) : ContDiffAt ℝ 2 u (line t) :=
    hu.contDiffAt (hU.mem_nhds ht)
  have hf (t : ℝ) (ht : t ∈ D) : HasDerivAt f (g t) t :=
    ((hu' t ht).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hDline t)
  have hg (t : ℝ) (ht : t ∈ D) : HasDerivAt g (h t) t := by
    have hd := ((hu' t ht).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have heval := hd.hasFDerivAt.clm_apply (hasFDerivAt_const v (line t))
    have hEval : HasFDerivAt (fun z => fderiv ℝ u z v)
        ((realHessian u (line t)).flip v) (line t) := by
      simpa only [realHessian, ContinuousLinearMap.comp_zero, zero_add] using heval
    exact hEval.comp_hasDerivAt t (hDline t)
  have hfconv : ConvexOn ℝ D f := convexOn_of_hasDerivWithinAt2_nonneg hD
    (fun t ht => (hf t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hf t (interior_subset ht)).hasDerivWithinAt)
    (fun t ht => (hg t (interior_subset ht)).hasDerivWithinAt)
    (fun t ht => hH (line t) (show t ∈ D from interior_subset ht) v)
  have hzero : (0 : ℝ) ∈ D := by simpa [D, line] using hx
  have hone : (1 : ℝ) ∈ D := by simpa [D, line] using hy
  have hh := hfconv.2 hzero hone ha hb hab
  have he : (1 - b : ℝ) = a := by linarith
  simpa [f, line, AffineMap.lineMap_apply_module, he] using hh

variable [FiniteDimensional ℝ E]

theorem exists_gradient_of_uniform_support {u : E → ℝ} (hu : Differentiable ℝ u)
    (p : E) {ε C : ℝ} (hε : 0 < ε)
    (hbound : ∀ x, C + ε * ‖x‖ ≤ u x - ⟪p, x⟫_ℝ) :
    p ∈ range (gradient u) := by
  let v (x : E) := u x - ⟪p, x⟫_ℝ
  have hv : Continuous v := hu.continuous.sub (continuous_const.inner continuous_id)
  let K : Set E := {x | v x ≤ v 0}
  have hK : IsCompact K := by
    apply isCompact_of_isClosed_isBounded
    · exact isClosed_le hv continuous_const
    · refine isBounded_iff_forall_norm_le.mpr ⟨(v 0 - C) / ε, ?_⟩
      intro x hx
      exact (le_div_iff₀ hε).mpr (by
        change v x ≤ v 0 at hx
        have h := hbound x
        change C + ε * ‖x‖ ≤ v x at h
        linarith)
  have hz : (0 : E) ∈ K := show v 0 ≤ v 0 from le_rfl
  obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn ⟨0, hz⟩ hv.continuousOn
  have hglobal : IsMinOn v univ x := by
    intro y _
    by_cases hy : y ∈ K
    · exact hmin hy
    · change ¬v y ≤ v 0 at hy
      exact (hmin hz).trans (le_of_not_ge hy)
  have hlocal : IsLocalMin v x := hglobal.isLocalMin univ_mem
  let L := InnerProductSpace.toDual ℝ E p
  have hV : HasFDerivAt v (fderiv ℝ u x - L) x :=
    (hu x).hasFDerivAt.sub L.hasFDerivAt
  have hD := sub_eq_zero.mp (hlocal.hasFDerivAt_eq_zero hV)
  exact ⟨x, by simp [gradient, hD, L]⟩


private theorem interior_convexHull_finite_subset_range_gradient
    {u : E → ℝ} (hconv : ConvexOn ℝ univ u) (hu : Differentiable ℝ u)
    (s : Finset E) {p : E} (hp : p ∈ interior (convexHull ℝ (gradient u '' (s : Set E)))) :
    p ∈ range (gradient u) := by
  classical
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hp)
  have hs : s.Nonempty := by
    by_contra! hs
    simp [hs] at hp
  let L (z : E) := u z - ⟪gradient u z, z⟫_ℝ
  let C := (s.image L).min' (hs.image L)
  have hline (x z : E) (hz : z ∈ s) : C + ⟪gradient u z, x⟫_ℝ ≤ u x := by
    have hC : C ≤ L z := Finset.min'_le _ _ (Finset.mem_image_of_mem _ hz)
    have hsupp := supporting_fderiv_of_convex hconv hu z x
    have hgrad (y : E) : ⟪gradient u z, y⟫_ℝ = fderiv ℝ u z y :=
      InnerProductSpace.toDual_symm_apply
    rw [← hgrad, inner_sub_right] at hsupp
    change C ≤ u z - ⟪gradient u z, z⟫_ℝ at hC
    linarith
  have hlinHull (x q : E) (hq : q ∈ convexHull ℝ (gradient u '' (s : Set E))) :
      ⟪q, x⟫_ℝ ≤ u x - C := by
    rw [real_inner_comm x q]
    apply convexHull_min _ (convex_halfSpace_le ((innerSL ℝ x).isLinear) (u x - C)) hq
    rintro _ ⟨z, hz, rfl⟩
    change ⟪x, gradient u z⟫_ℝ ≤ u x - C
    rw [real_inner_comm]
    linarith [hline x z hz]
  apply exists_gradient_of_uniform_support hu p (show 0 < δ / 2 by positivity) (C := C)
  intro x
  by_cases hx : x = 0
  · subst x
    have h := hlinHull 0 p (interior_subset hp)
    simpa using (show C + (δ / 2) * ‖(0 : E)‖ ≤ u 0 - ⟪p, 0⟫_ℝ by
      simp at h ⊢
      linarith)
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let q := p + (δ / 2 / ‖x‖) • x
  have hq : q ∈ ball p δ := by
    rw [mem_ball_iff_norm]
    change ‖p + (δ / 2 / ‖x‖) • x - p‖ < δ
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos (by positivity) hn), div_mul_cancel₀ _ hn.ne']
    linarith
  have hqVal : ⟪q, x⟫_ℝ = ⟪p, x⟫_ℝ + (δ / 2) * ‖x‖ := by
    change ⟪p + (δ / 2 / ‖x‖) • x, x⟫_ℝ = _
    rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp [hn.ne']
  linarith [hlinHull x q (hball hq)]


theorem affineSpan_range_gradient_ne_top_of_singular {u : E → ℝ}
    (hconv : ConvexOn ℝ univ u) (hu : Differentiable ℝ u)
    (hgrad : Differentiable ℝ (gradient u))
    (hdet : ∀ x, (fderiv ℝ (gradient u) x).det = 0) :
    affineSpan ℝ (range (gradient u)) ≠ ⊤ := by
  classical
  intro htop
  obtain ⟨S, hS, b, hb⟩ := AffineBasis.exists_affine_subbasis htop
  have hSfin := b.finite_set
  letI : Fintype S := hSfin.fintype
  have hI : (interior (convexHull ℝ S)).Nonempty := by
    have h := b.centroid_mem_interior_convexHull
    rw [hb, Subtype.range_coe] at h
    exact ⟨_, h⟩
  choose pre hpre using fun q : S => hS q.prop
  let s := Finset.univ.image pre
  have himage : gradient u '' (s : Set E) = S := by
    ext q
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
      simpa only [hpre i] using i.prop
    · intro hq
      let i : S := ⟨q, hq⟩
      exact ⟨pre i, Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ i)), hpre i⟩
  have hsub : interior (convexHull ℝ S) ⊆ range (gradient u) := by
    rw [← himage]
    exact fun _ hx => interior_convexHull_finite_subset_range_gradient hconv hu s hx
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  let μ : Measure E := Measure.addHaar
  have hzero : μ (range (gradient u)) = 0 := by
    rw [← image_univ]
    exact addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ
      (fun x _ => (hgrad x).hasFDerivAt.hasFDerivWithinAt) (fun x _ => hdet x)
  have hpos := isOpen_interior.measure_pos μ hI
  exact (hpos.trans_le (measure_mono hsub)).ne' hzero


/-- An entire (C^2) convex function with singular real Hessian everywhere
has a common nonzero Hessian-kernel direction. -/
theorem exists_common_realHessian_kernel_of_singular {u : E → ℝ}
    (hu : ContDiff ℝ 2 u) (hconv : ConvexOn ℝ univ u)
    (hsing : ∀ x, ∃ v : E, v ≠ 0 ∧ realHessian u x v = 0) :
    ∃ v : E, v ≠ 0 ∧ ∀ x, realHessian u x v = 0 := by
  let T := (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv
  have hdiff (x : E) : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.contDiffAt.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hg (x : E) : HasFDerivAt (gradient u) (T.toContinuousLinearMap.comp (realHessian u x)) x :=
    T.toContinuousLinearMap.hasFDerivAt.comp x (hdiff x).hasFDerivAt
  have hdet (x : E) : (fderiv ℝ (gradient u) x).det = 0 := by
    rw [(hg x).fderiv]
    apply LinearMap.det_eq_zero_iff_ker_ne_bot.mpr
    intro hbot
    obtain ⟨v, hv, hv0⟩ := hsing x
    have hvker : v ∈ (T.toContinuousLinearMap.comp (realHessian u x)).ker := by
      change T (realHessian u x v) = 0
      rw [hv0, map_zero]
    rw [hbot] at hvker
    exact hv (by simpa using hvker)
  let W := affineSpan ℝ (range (gradient u))
  have hW : W ≠ ⊤ :=
    affineSpan_range_gradient_ne_top_of_singular hconv (hu.differentiable (by norm_num))
      (fun x => (hg x).differentiableAt) hdet
  have hWne : (W : Set E).Nonempty := ⟨gradient u 0, subset_affineSpan _ _ (mem_range_self _)⟩
  have hdir : W.direction ≠ ⊤ := fun h => hW
    ((AffineSubspace.direction_eq_top_iff_of_nonempty hWne).mp h)
  have horth : W.directionᗮ ≠ ⊥ := fun h => hdir (Submodule.orthogonal_eq_bot_iff.mp h)
  obtain ⟨v, hv, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot horth
  have hconst (x : E) : fderiv ℝ u x v = fderiv ℝ u 0 v := by
    have hWmem (y : E) : gradient u y ∈ W :=
      subset_affineSpan _ _ (mem_range_self _)
    have hmem : gradient u x - gradient u 0 ∈ W.direction :=
      AffineSubspace.vsub_mem_direction (hWmem x) (hWmem 0)
    have hzero := (Submodule.mem_orthogonal W.direction v).mp hv _ hmem
    rw [inner_sub_left, gradient, gradient, InnerProductSpace.toDual_symm_apply,
      InnerProductSpace.toDual_symm_apply] at hzero
    exact sub_eq_zero.mp hzero
  refine ⟨v, hvne, fun x => ?_⟩
  have hF := (hdiff x).hasFDerivAt.clm_apply (hasFDerivAt_const v x)
  have hF' : HasFDerivAt (fun y => fderiv ℝ u y v) ((realHessian u x).flip v) x := by
    simpa only [realHessian, ContinuousLinearMap.comp_zero, zero_add] using hF
  rw [show (fun y => fderiv ℝ u y v) = (fun _ => fderiv ℝ u 0 v) from funext hconst] at hF'
  have hflip := hF'.unique (hasFDerivAt_const (fderiv ℝ u 0 v) x)
  ext w
  exact (realHessian_symm hu.contDiffAt v w).trans
    (congrArg (fun L : E →L[ℝ] ℝ => L w) hflip)

end CHS.Analysis
