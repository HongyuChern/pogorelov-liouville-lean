import CHS.Pogorelov.LogLinearization
import CHS.Pogorelov.TraceCombination

/-!
# The real trace field used in the Pogorelov test function

All derivatives in this file are derivatives of the potential's actual
Hessians.  Interior regularity is C4; no boundary extension is used.
-/

set_option autoImplicit false
noncomputable section

open Matrix Filter
open scoped BigOperators ComplexOrder ContDiff Topology

namespace CHS.Pogorelov

open CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def correctionTrace (a b : ι → E) (u : E → ℝ) (x : E) : ℂ :=
  (complexHessian a b u x - schurHessian a b u x).trace

def traceCombination (a b : ι → E) (u : E → ℝ) (c : ℝ) (x : E) : ℝ :=
  c * (complexHessian a b u x).trace.re + (correctionTrace a b u x).re

theorem correctionTrace_eq (a b : ι → E) (u : E → ℝ) (x : E) :
    correctionTrace a b u x =
      (pureHessian a b u x * ((complexHessian a b u x).map star)⁻¹ *
        (pureHessian a b u x).map star).trace := by
  unfold correctionTrace schurHessian schurField
  rw [sub_sub_cancel]

theorem correctionTrace_function_eq (a b : ι → E) (u : E → ℝ) :
    correctionTrace a b u = fun x =>
      (pureHessian a b u x * ((complexHessian a b u x).map star)⁻¹ *
        (pureHessian a b u x).map star).trace :=
  funext (correctionTrace_eq a b u)

theorem ofReal_trace_re_of_isHermitian {M : Matrix ι ι ℂ} (hM : M.IsHermitian) :
    (M.trace.re : ℂ) = M.trace := by
  have hdiag (i : ι) : (M i i).im = 0 := by
    have h := congrArg Complex.im (hM.apply i i)
    simp only [Complex.star_def, Complex.conj_im] at h
    linarith
  have him : M.trace.im = 0 := by
    simp only [Matrix.trace, Matrix.diag_apply, Complex.im_sum, hdiag,
      Finset.sum_const_zero]
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im] using him.symm

theorem traceCombination_complex {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (a b : ι → E) (c : ℝ) :
    (traceCombination a b u c x : ℂ) =
      (c : ℂ) * (complexHessian a b u x).trace + correctionTrace a b u x := by
  have hA := complexHessian_isHermitian hu a b
  have hD := hA.sub (schurHessian_isHermitian hu a b)
  simp only [traceCombination, correctionTrace, Complex.ofReal_add, Complex.ofReal_mul,
    ofReal_trace_re_of_isHermitian hA, ofReal_trace_re_of_isHermitian hD]

theorem correctionTrace_contDiffOn {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : ι → E)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = 1) :
    ContDiffOn ℝ 2 (correctionTrace a b u) U :=
  (schur_trace_fields_regular hU hu a b hdet).2

theorem traceCombination_contDiffOn {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : ι → E)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = 1) (c : ℝ) :
    ContDiffOn ℝ 2 (traceCombination a b u c) U := by
  have hreg := schur_trace_fields_regular hU hu a b hdet
  have hA := Complex.reCLM.contDiff.comp_contDiffOn hreg.1
  have hD := Complex.reCLM.contDiff.comp_contDiffOn hreg.2
  exact (contDiffOn_const.mul hA).add hD

theorem traceCombination_pos_of_posDef {n : ℕ} (hn : 2 ≤ n)
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) (a b : Fin n → E)
    (hpos : (complexHessian a b u x).PosDef) {κ : ℝ} (hκ : 1 ≤ κ)
    (hmat : (κ • complexHessian a b u x -
      pureHessian a b u x * ((complexHessian a b u x).map star)⁻¹ *
        (pureHessian a b u x).map star).PosSemidef) :
    0 < traceCombination a b u (cChoice n κ) x := by
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have ha : 0 < (complexHessian a b u x).trace.re := by
    have h := hpos.trace_pos
    rw [← ofReal_trace_re_of_isHermitian hpos.isHermitian] at h
    exact_mod_cast h
  have hm : (κ • complexHessian a b u x -
      (complexHessian a b u x - schurHessian a b u x)).PosSemidef := by
    change (κ • complexHessian a b u x - (_ - (_ - _))).PosSemidef
    rw [sub_sub_cancel]
    exact hmat
  have hd : 0 ≤ (correctionTrace a b u x).re :=
    (schur_correction_trace_bounds hu a b hpos κ hm).1
  exact add_pos_of_pos_of_nonneg (mul_pos (cChoice_pos hn hκ) ha) hd

theorem dz_add_at {f g : E → ℂ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (v w : E) :
    dz v w (fun y => f y + g y) x = dz v w f x + dz v w g x := by
  have hrd (e : E) : rd e (fun y => f y + g y) x = rd e f x + rd e g x := by
    simp only [rd, fderiv_fun_add hf hg, ContinuousLinearMap.add_apply]
  unfold dz
  rw [hrd, hrd]
  ring

theorem dz_const_mul_at {f : E → ℂ} {x : E}
    (hf : DifferentiableAt ℝ f x) (v w : E) (c : ℂ) :
    dz v w (fun y => c * f y) x = c * dz v w f x := by
  unfold dz
  rw [rd_const_mul_at hf, rd_const_mul_at hf]
  ring

theorem linearizedScalar_congr_on {f g : E → ℂ} {U : Set E}
    (hU : IsOpen U) (hfg : Set.EqOn f g U) {x : E} (hx : x ∈ U)
    (a b : ι → E) (W : Matrix ι ι ℂ) :
    linearizedScalar a b W f x = linearizedScalar a b W g x := by
  unfold linearizedScalar
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  congr 1
  apply dz_congr_on hU (hx := hx)
  intro y hy
  exact dz_congr_on hU hfg (a p) (b p) hy

theorem linearizedScalar_add {f g : E → ℂ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x)
    (a b : ι → E) (W : Matrix ι ι ℂ) :
    linearizedScalar a b W (fun y => f y + g y) x =
      linearizedScalar a b W f x + linearizedScalar a b W g x := by
  have hnear (p : ι) : dz (a p) (b p) (fun y => f y + g y) =ᶠ[𝓝 x]
      (fun y => dz (a p) (b p) f y + dz (a p) (b p) g y) := by
    filter_upwards [hf.eventually (by simp), hg.eventually (by simp)] with y hyf hyg
    exact dz_add_at (hyf.differentiableAt (by norm_num))
      (hyg.differentiableAt (by norm_num)) _ _
  unfold linearizedScalar
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  rw [dz_congr_nhds (hnear p), dz_add_at
    ((dz_contDiffAt_one hf (a p) (b p)).differentiableAt (by norm_num))
    ((dz_contDiffAt_one hg (a p) (b p)).differentiableAt (by norm_num)), mul_add]

theorem linearizedScalar_const_mul {f : E → ℂ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (a b : ι → E) (W : Matrix ι ι ℂ) (c : ℂ) :
    linearizedScalar a b W (fun y => c * f y) x =
      c * linearizedScalar a b W f x := by
  have hnear (p : ι) : dz (a p) (b p) (fun y => c * f y) =ᶠ[𝓝 x]
      (fun y => c * dz (a p) (b p) f y) := by
    filter_upwards [hf.eventually (by simp)] with y hy
    exact dz_const_mul_at (hy.differentiableAt (by norm_num)) _ _ c
  unfold linearizedScalar
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [dz_congr_nhds (hnear p), dz_const_mul_at
    ((dz_contDiffAt_one hf (a p) (b p)).differentiableAt (by norm_num))]
  ring

theorem correctionTrace_first_derivative {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : ι → E)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = 1)
    {x : E} (hx : x ∈ U) (p : ι) :
    dz (a p) (b p) (correctionTrace a b u) x =
      (compensatedHessian a b u p x * ((complexHessian a b u x).map star)⁻¹ *
        (pureHessian a b u x).map star).trace +
      (pureHessian a b u x * ((complexHessian a b u x).map star)⁻¹ *
        matrixDZ (a p) (b p) (fun y => (pureHessian a b u y).map star) x).trace := by
  rw [correctionTrace_function_eq]
  exact correction_trace_first_derivative hU hu a b hdet hx p

/-- The gradient decomposition (2.21) with the `c ∂a` term included. -/
theorem traceCombination_first_derivative {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : ι → E)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = 1)
    {x : E} (hx : x ∈ U) (c : ℝ) (p : ι) :
    dz (a p) (b p) (fun y => (traceCombination a b u c y : ℂ)) x =
      ((c : ℂ) * dz (a p) (b p) (fun y => (complexHessian a b u y).trace) x +
        (pureHessian a b u x * ((complexHessian a b u x).map star)⁻¹ *
          matrixDZ (a p) (b p) (fun y => (pureHessian a b u y).map star) x).trace) +
      (compensatedHessian a b u p x * ((complexHessian a b u x).map star)⁻¹ *
        (pureHessian a b u x).map star).trace := by
  have heq : Set.EqOn (fun y => (traceCombination a b u c y : ℂ))
      (fun y => (c : ℂ) * (complexHessian a b u y).trace + correctionTrace a b u y) U := by
    intro y hy
    exact traceCombination_complex ((hu.contDiffAt (hU.mem_nhds hy)).of_le (by norm_num)) a b c
  have hreg := schur_trace_fields_regular hU hu a b hdet
  have hA := (hreg.1.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
  have hD := ((correctionTrace_contDiffOn hU hu a b hdet).contDiffAt
    (hU.mem_nhds hx)).differentiableAt (by norm_num)
  rw [dz_congr_on hU heq (a p) (b p) hx,
    dz_add_at (hA.const_mul (c : ℂ)) hD,
    dz_const_mul_at hA, correctionTrace_first_derivative hU hu a b hdet hx]
  ring

/-- Equation (2.20) for the actual real scalar field `S_c`. -/
theorem traceCombination_evolution {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : ι → E)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = 1)
    {x : E} (hx : x ∈ U) (hA : (complexHessian a b u x).PosDef) (c : ℝ) :
    let A := complexHessian a b u
    let W := (A x)⁻¹
    let Q := CHS.WeightedSquares.matrixSquare W W
      (fun p => matrixDZ (a p) (b p) A x)
    let F := CHS.WeightedSquares.matrixSquare W (((A x).map star)⁻¹)
      (fun p => compensatedHessian a b u p x)
    linearizedScalar a b W (fun y => (traceCombination a b u c y : ℂ)) x =
      ((c : ℂ) + 1) * Q.trace + F.trace := by
  obtain ⟨_, _, hLA, hLD⟩ := correction_trace_evolution hU hu a b hdet hx hA
  dsimp only at hLA hLD ⊢
  have hLD' : linearizedScalar a b (complexHessian a b u x)⁻¹
      (correctionTrace a b u) x =
      (CHS.WeightedSquares.matrixSquare (complexHessian a b u x)⁻¹
        (complexHessian a b u x)⁻¹
          (fun p => matrixDZ (a p) (b p) (complexHessian a b u) x)).trace +
      (CHS.WeightedSquares.matrixSquare (complexHessian a b u x)⁻¹
        (((complexHessian a b u x).map star)⁻¹)
          (fun p => compensatedHessian a b u p x)).trace := by
    rw [correctionTrace_function_eq]
    exact hLD
  have heq : Set.EqOn (fun y => (traceCombination a b u c y : ℂ))
      (fun y => (c : ℂ) * (complexHessian a b u y).trace + correctionTrace a b u y) U := by
    intro y hy
    exact traceCombination_complex ((hu.contDiffAt (hU.mem_nhds hy)).of_le (by norm_num)) a b c
  have hreg := schur_trace_fields_regular hU hu a b hdet
  have hAreg := hreg.1.contDiffAt (hU.mem_nhds hx)
  have hDreg := (correctionTrace_contDiffOn hU hu a b hdet).contDiffAt (hU.mem_nhds hx)
  rw [linearizedScalar_congr_on hU heq hx,
    linearizedScalar_add (contDiffAt_const.mul hAreg) hDreg,
    linearizedScalar_const_mul hAreg, hLA, hLD']
  ring

end CHS.Pogorelov
