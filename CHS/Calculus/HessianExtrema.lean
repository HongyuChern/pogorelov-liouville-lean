import CHS.Calculus.BasisHessian
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Hessian sign at an interior extremum
-/

set_option autoImplicit false

open Filter Metric Set
open scoped BigOperators ComplexOrder ContDiff Topology

namespace CHS.Calculus

private theorem deriv_deriv_nonpos_of_localMax {f g h : ℝ → ℝ}
    (hm : IsLocalMax f 0) (hhc : ContinuousAt h 0)
    (hf : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt f (g t) t)
    (hg : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt g (h t) t) :
    h 0 ≤ 0 := by
  have hg0 : g 0 = 0 := hf.self_of_nhds.deriv.symm.trans hm.deriv_eq_zero
  by_contra! hpos
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ),
      f t ≤ f 0 ∧ HasDerivAt f (g t) t ∧ HasDerivAt g (h t) t ∧ 0 < h t :=
    hm.and (hf.and (hg.and (continuousAt_const.eventually_lt hhc hpos)))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let b := r / 2
  have hb : 0 < b := by dsimp [b]; positivity
  have hsub : Icc 0 b ⊆ ball (0 : ℝ) r := by
    intro t ht
    rw [mem_ball_zero_iff, Real.norm_eq_abs, abs_of_nonneg ht.1]
    dsimp [b] at ht
    linarith [ht.2]
  have hgmono : StrictMonoOn g (Icc 0 b) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 b)
    · intro t ht
      exact ((hball (hsub ht)).2.2.1.continuousAt).continuousWithinAt
    · intro t ht
      have ht' : t ∈ Icc 0 b := interior_subset ht
      rw [(hball (hsub ht')).2.2.1.deriv]
      exact (hball (hsub ht')).2.2.2
  have hfmono : StrictMonoOn f (Icc 0 b) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 b)
    · intro t ht
      exact ((hball (hsub ht)).2.1.continuousAt).continuousWithinAt
    · intro t ht
      have ht' : t ∈ Icc 0 b := interior_subset ht
      rw [(hball (hsub ht')).2.1.deriv, ← hg0]
      rw [interior_Icc] at ht
      exact hgmono ⟨le_rfl, hb.le⟩ ht' ht.1
  exact (not_lt_of_ge (hball (hsub ⟨hb.le, le_rfl⟩)).1)
    (hfmono ⟨le_rfl, hb.le⟩ ⟨hb.le, le_rfl⟩ hb)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem realHessian_nonpos_of_isLocalMax {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hmax : IsLocalMax u x) (v : E) :
    realHessian u x v v ≤ 0 := by
  let line (t : ℝ) := x + t • v
  have hline (t : ℝ) : HasDerivAt line v t := by
    simpa [line] using ((hasDerivAt_id t).smul_const v).const_add x
  have hline0 : line 0 = x := by simp [line]
  let f := u ∘ line
  let g (t : ℝ) := fderiv ℝ u (line t) v
  let h (t : ℝ) := realHessian u (line t) v v
  have hfmax : IsLocalMax f 0 :=
    (show IsLocalMax u (line 0) by rwa [hline0]).comp_continuous (hline 0).continuousAt
  have hlineT : Tendsto line (𝓝 (0 : ℝ)) (𝓝 x) := by
    rw [← hline0]
    exact (hline 0).continuousAt
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), ContDiffAt ℝ 2 u (line t) :=
    hlineT.eventually (hu.eventually (by simp))
  have hf : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt f (g t) t :=
    hnear.mono fun t ht =>
      ((ht.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hline t))
  have hg : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt g (h t) t := by
    filter_upwards [hnear] with t ht
    have hd := (ht.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have heval := hd.hasFDerivAt.clm_apply (hasFDerivAt_const v (line t))
    have hEval : HasFDerivAt (fun y => fderiv ℝ u y v)
        ((realHessian u (line t)).flip v) (line t) := by
      simpa only [realHessian, ContinuousLinearMap.comp_zero, zero_add] using heval
    exact hEval.comp_hasDerivAt t (hline t)
  have hhu : ContinuousAt (fun y => realHessian u y v v) x := by
    have h0 := ((hu.fderiv_right (m := 1) (by norm_num)).fderiv_right
      (m := 0) (by norm_num)).continuousAt
    have h1 := h0.clm_apply (continuousAt_const (x := x) (y := v))
    exact h1.clm_apply (continuousAt_const (x := x) (y := v))
  have hh : ContinuousAt h 0 :=
    hhu.comp_of_eq (hline 0).continuousAt hline0
  simpa only [h, hline0] using deriv_deriv_nonpos_of_localMax hfmax
    hh hf hg


theorem neg_realBlockHessian_posSemidef_of_isLocalMax {ι : Type*} [Fintype ι] {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hmax : IsLocalMax u x) (a b : ι → E) :
    (-realBlockHessian a b u x).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (realBlockHessian_isHermitian hu a b).neg
  intro v
  let e := Sum.elim a b
  let w := ∑ i, v i • e i
  have hform : realHessian u x w w = v ⬝ᵥ (realBlockHessian a b u x).mulVec v := by
    simp only [w, map_sum, map_smul, sum_apply, smul_apply, dotProduct, Matrix.mulVec,
      smul_eq_mul, realBlockHessian, e, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [realHessian_symm hu (Sum.elim a b j) (Sum.elim a b i)]
    ring
  rw [star_trivial, Matrix.neg_mulVec, dotProduct_neg, ← hform]
  exact neg_nonneg.mpr (realHessian_nonpos_of_isLocalMax hu hmax w)

theorem complexHessian_sub_posSemidef_of_isLocalMax {ι : Type*} [Fintype ι] [DecidableEq ι]
    {u v : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x)
    (hmax : IsLocalMax (fun y => u y - v y) x) (a b : ι → E) :
    (complexHessian a b v x - complexHessian a b u x).PosSemidef := by
  let f (y : E) := v y - u y
  have hf : ContDiffAt ℝ 2 f x := hv.sub hu
  have hneg : (fun y => u y - v y) = fun y => -f y := by
    funext y
    dsimp [f]
    ring
  rw [hneg] at hmax
  have H : ∀ i j, realHessian f x i j =
      realHessian v x i j - realHessian u x i j := by
    intro i j
    have hnear : fderiv ℝ f =ᶠ[𝓝 x] (fun y => fderiv ℝ v y - fderiv ℝ u y) := by
      filter_upwards [hu.eventually (by simp), hv.eventually (by simp)] with y hyu hyv
      exact fderiv_fun_sub (hyv.differentiableAt (by norm_num)) (hyu.differentiableAt (by norm_num))
    unfold realHessian
    rw [hnear.fderiv_eq, fderiv_fun_sub
      ((hv.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
      ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))]
    rfl
  have hminus : ∀ i j, realHessian (fun y => -f y) x i j = -realHessian f x i j := by
    intro i j
    have hEq : fderiv ℝ (fun y => -f y) = fun y => -fderiv ℝ f y :=
      funext fun _ => fderiv_fun_neg
    unfold realHessian
    rw [hEq, fderiv_fun_neg]
    rfl
  have hReal : (realBlockHessian a b f x).PosSemidef := by
    have h := neg_realBlockHessian_posSemidef_of_isLocalMax hf.neg hmax a b
    have heq : -realBlockHessian a b (fun y => -f y) x = realBlockHessian a b f x := by
      ext i j
      simp only [Matrix.neg_apply, realBlockHessian, hminus, neg_neg]
    rwa [heq] at h
  have hBlock := (actual_block_posSemidef_iff_complexification hf a b).mpr
    ((real_matrix_posSemidef_iff_complexification (realBlockHessian_isHermitian hf a b)).mp hReal)
  have hA : (complexHessian a b f x).PosSemidef :=
    hBlock.submatrix (Sum.inl : ι → ι ⊕ ι)
  have heq : complexHessian a b f x = complexHessian a b v x - complexHessian a b u x := by
    ext i j
    rw [Matrix.sub_apply, complexHessian_real_entry hf, complexHessian_real_entry hv,
      complexHessian_real_entry hu]
    simp only [H, Complex.ofReal_sub]
    ring
  rwa [heq] at hA

end CHS.Calculus
