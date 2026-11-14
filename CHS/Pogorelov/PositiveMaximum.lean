import CHS.Pogorelov.GradientEvolution
import CHS.Pogorelov.Maximum

/-!
# The actual local-maximum assembly in the positive branch

The endpoint starts with an actual local maximum of the logarithmic test
function.  Its first derivative vanishes and its linearized second derivative
is nonpositive by the calculus of that function.  Neither condition is an
independently supplied scalar inequality.

Existence of a maximum on a bounded closure or a real translation quotient
is a separate global interface; it is not claimed by this file.
-/

set_option autoImplicit false
noncomputable section

open Matrix Filter
open scoped BigOperators ComplexOrder ContDiff Topology

namespace CHS.Pogorelov

open CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {n : ℕ}

theorem wirtingerGradient_add {f g : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (a b : ι → E) :
    wirtingerGradient a b (fun y => f y + g y) x =
      fun i => wirtingerGradient a b f x i + wirtingerGradient a b g x i := by
  funext i
  simp only [wirtingerGradient, fderiv_fun_add hf hg,
    ContinuousLinearMap.add_apply, Complex.ofReal_add]
  ring

theorem wirtingerGradient_const_mul {f : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (a b : ι → E) (c : ℝ) :
    wirtingerGradient a b (fun y => c * f y) x =
      fun i => (c : ℂ) * wirtingerGradient a b f x i := by
  funext i
  simp only [wirtingerGradient, fderiv_const_mul hf,
    ContinuousLinearMap.smul_apply, smul_eq_mul, Complex.ofReal_mul]
  ring

theorem wirtingerGradient_neg (a b : ι → E) (f : E → ℝ) (x : E) :
    wirtingerGradient a b (fun y => -f y) x = -wirtingerGradient a b f x := by
  funext i
  simp only [wirtingerGradient, fderiv_fun_neg, _root_.neg_apply,
    Pi.neg_apply, Complex.ofReal_neg]
  ring

/-- A real quadratic identity with both cross pairings retained.  It is valid
even before symmetry of the weight is used. -/
theorem covector_norm_real_sub (W : Matrix ι ι ℂ) (v w : ι → ℂ) (s : ℝ) :
    (star (fun i => (s : ℂ) * v i - w i) ⬝ᵥ
      W.mulVec (fun i => (s : ℂ) * v i - w i)).re =
      s ^ 2 * (star v ⬝ᵥ W.mulVec v).re + (star w ⬝ᵥ W.mulVec w).re -
        s * ((star v ⬝ᵥ W.mulVec w).re + (star w ⬝ᵥ W.mulVec v).re) := by
  have hcomplex : star ((s : ℂ) • v - w) ⬝ᵥ W.mulVec ((s : ℂ) • v - w) =
      (s : ℂ) ^ 2 * (star v ⬝ᵥ W.mulVec v) + (star w ⬝ᵥ W.mulVec w) -
        (s : ℂ) * ((star v ⬝ᵥ W.mulVec w) + (star w ⬝ᵥ W.mulVec v)) := by
    simp only [star_sub, star_smul, Matrix.mulVec_sub, Matrix.mulVec_smul,
      sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
    ring
  change (star ((s : ℂ) • v - w) ⬝ᵥ W.mulVec ((s : ℂ) • v - w)).re = _
  rw [hcomplex]
  simp only [← Complex.ofReal_pow, Complex.sub_re, Complex.add_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

def logPogorelovTest (a b : Fin n → E) (u : E → ℝ) (κ K : ℝ) (x : E) : ℝ :=
  beta n κ * Real.log (-u x) + Real.log (traceCombination a b u (cChoice n κ) x) +
    alpha K * gradientNormSq a b u x

def pogorelovTest (a b : Fin n → E) (u : E → ℝ) (κ K : ℝ) (x : E) : ℝ :=
  (-u x) ^ beta n κ * traceCombination a b u (cChoice n κ) x *
    Real.exp (alpha K * gradientNormSq a b u x)

theorem exp_logPogorelovTest (a b : Fin n → E) (u : E → ℝ) (κ K : ℝ) (x : E)
    (hu : u x < 0) (hS : 0 < traceCombination a b u (cChoice n κ) x) :
    Real.exp (logPogorelovTest a b u κ K x) = pogorelovTest a b u κ K x := by
  simp only [logPogorelovTest, pogorelovTest, Real.exp_add, Real.exp_log hS,
    Real.rpow_def_of_pos (neg_pos.mpr hu)]
  rw [mul_comm (beta n κ) (Real.log (-u x))]

theorem isLocalMax_logPogorelovTest {u : E → ℝ} {x : E}
    (a b : Fin n → E) (κ K : ℝ) (hu : ContinuousAt u x)
    (hS : ContinuousAt (traceCombination a b u (cChoice n κ)) x)
    (hux : u x < 0) (hSx : 0 < traceCombination a b u (cChoice n κ) x)
    (hmax : IsLocalMax (pogorelovTest a b u κ K) x) :
    IsLocalMax (logPogorelovTest a b u κ K) x := by
  have hunear : ∀ᶠ y in 𝓝 x, u y < 0 := hu.eventually_lt continuousAt_const hux
  have hSnear : ∀ᶠ y in 𝓝 x, 0 < traceCombination a b u (cChoice n κ) y :=
    continuousAt_const.eventually_lt hS hSx
  filter_upwards [hmax, hunear, hSnear] with y hy huy hSy
  apply Real.exp_le_exp.mp
  rw [exp_logPogorelovTest a b u κ K y huy hSy,
    exp_logPogorelovTest a b u κ K x hux hSx]
  exact hy

/-- The differential and algebraic maximum argument following (2.31),
with the exact constants of the frozen manuscript. -/
theorem trace_bound_at_log_test_maximum {u : E → ℝ} {U : Set E}
    (hn : 2 ≤ n) (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : Fin n → E)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = 1)
    {x : E} (hx : x ∈ U) (hpos : (complexHessian a b u x).PosDef)
    {κ : ℝ} (hκ : 1 ≤ κ)
    (hmat : (κ • complexHessian a b u x -
      pureHessian a b u x * ((complexHessian a b u x).map star)⁻¹ *
        (pureHessian a b u x).map star).PosSemidef)
    (K : ℝ) (hK : gradientNormSq a b u x ≤ K ^ 2) (hux : u x < 0)
    (hmax : IsLocalMax (logPogorelovTest a b u κ K) x) :
    (-u x) * ((complexHessian a b u x).trace.re + (correctionTrace a b u x).re) ≤
      16 * (n : ℝ) * beta n κ * (1 + K ^ 2) := by
  let β := beta n κ
  let α := alpha K
  let t := -u x
  let S := traceCombination a b u (cChoice n κ)
  let G := gradientNormSq a b u
  let W := (complexHessian a b u x)⁻¹
  let H := (complexHessian a b u x).trace.re + (correctionTrace a b u x).re
  let X := fun i => ((t⁻¹ : ℝ) : ℂ) * wirtingerGradient a b u x i
  let Y := fun i => (α : ℂ) * wirtingerGradient a b G x i
  let XX := (star X ⬝ᵥ W.mulVec X).re
  let YY := (star Y ⬝ᵥ W.mulVec Y).re
  let XY := ((star X ⬝ᵥ W.mulVec Y).re + (star Y ⬝ᵥ W.mulVec X).re) / 2
  have ht : 0 < t := neg_pos.mpr hux
  have hu3 : ContDiffAt ℝ 3 u x := (hu.contDiffAt (hU.mem_nhds hx)).of_le (by norm_num)
  have hu2 : ContDiffAt ℝ 2 u x := hu3.of_le (by norm_num)
  have hud := hu2.differentiableAt (by norm_num)
  have hS : ContDiffAt ℝ 2 S x :=
    (traceCombination_contDiffOn hU hu a b hdet _).contDiffAt (hU.mem_nhds hx)
  have hG : ContDiffAt ℝ 2 G x := gradientNormSq_contDiffAt_two hu3 a b
  have hW : W.PosSemidef := hpos.inv.posSemidef
  have hm : (κ • complexHessian a b u x -
      (complexHessian a b u x - schurHessian a b u x)).PosSemidef := by
    change (κ • complexHessian a b u x - (_ - (_ - _))).PosSemidef
    rw [sub_sub_cancel]
    exact hmat
  have hd : 0 ≤ (correctionTrace a b u x).re :=
    (schur_correction_trace_bounds hu2 a b hpos κ hm).1
  have ha : 0 < (complexHessian a b u x).trace.re := by
    letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    have h := hpos.trace_pos
    rw [← ofReal_trace_re_of_isHermitian hpos.isHermitian] at h
    exact_mod_cast h
  have hH : 0 ≤ H := add_nonneg ha.le hd
  have hSpos : 0 < S x :=
    add_pos_of_pos_of_nonneg (mul_pos (cChoice_pos hn hκ) ha) hd
  have hlogu : ContDiffAt ℝ 2 (fun y => Real.log (-u y)) x := hu2.neg.log ht.ne'
  have hlogS : ContDiffAt ℝ 2 (fun y => Real.log (S y)) x := hS.log hSpos.ne'
  have hF : ContDiffAt ℝ 2 (logPogorelovTest a b u κ K) x :=
    ((contDiffAt_const.mul hlogu).add hlogS).add (contDiffAt_const.mul hG)
  have hXlog : wirtingerGradient a b (fun y => Real.log (-u y)) x =
      fun i => -X i := by
    rw [wirtingerGradient_log (f := fun y => -u y) hud.neg ht.ne',
      wirtingerGradient_neg]
    funext i
    simp only [X, t, Pi.neg_apply, Complex.ofReal_inv]
    ring
  have hstat : wirtingerGradient a b (fun y => Real.log (S y)) x =
      fun i => (β : ℂ) * X i - Y i := by
    have hz : wirtingerGradient a b (logPogorelovTest a b u κ K) x = 0 := by
      funext i
      simp [wirtingerGradient, hmax.fderiv_eq_zero]
    have hldu := hlogu.differentiableAt (by norm_num)
    have hlds := hlogS.differentiableAt (by norm_num)
    have hgd := hG.differentiableAt (by norm_num)
    change wirtingerGradient a b (fun y =>
      β * Real.log (-u y) + Real.log (S y) + α * G y) x = 0 at hz
    rw [wirtingerGradient_add
      (f := fun y => β * Real.log (-u y) + Real.log (S y)) (g := fun y => α * G y)
      ((hldu.const_mul β).add hlds) (hgd.const_mul α),
      wirtingerGradient_add (f := fun y => β * Real.log (-u y))
        (g := fun y => Real.log (S y)) (hldu.const_mul β) hlds,
      wirtingerGradient_const_mul hldu, wirtingerGradient_const_mul hgd, hXlog] at hz
    funext i
    have hi := congrFun hz i
    change (β : ℂ) * (-X i) + wirtingerGradient a b (fun y => Real.log (S y)) x i +
      Y i = 0 at hi
    linear_combination hi
  have hnorm (s : ℝ) :
      (star (fun i => (s : ℂ) * X i - Y i) ⬝ᵥ
        W.mulVec (fun i => (s : ℂ) * X i - Y i)).re =
      s ^ 2 * XX + YY - 2 * s * XY := by
    rw [covector_norm_real_sub]
    dsimp only [XX, YY, XY]
    ring
  have hYX : 0 ≤ XX + YY - 2 * XY := by
    have h : 0 ≤ (star (fun i => ((1 : ℝ) : ℂ) * X i - Y i) ⬝ᵥ
        W.mulVec (fun i => ((1 : ℝ) : ℂ) * X i - Y i)).re :=
      hW.re_dotProduct_nonneg _
    rw [hnorm 1] at h
    norm_num only [one_pow, one_mul, mul_one] at h
    exact h
  have hYY : YY ≤ 4 * α ^ 2 * K ^ 2 * H := by
    have hbound := gradientNormSq_bound hu3 a b (hdet x hx) hpos K hK
    have hmul := mul_le_mul_of_nonneg_left hbound (sq_nonneg α)
    have hYnorm : YY = α ^ 2 *
        (star (wirtingerGradient a b G x) ⬝ᵥ W.mulVec (wirtingerGradient a b G x)).re :=
      covector_norm_real_mul W _ α
    rw [hYnorm]
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hmul
  have hLneg : (linearizedScalar a b W (fun y => (Real.log (-u y) : ℂ)) x).re =
      -(n : ℝ) / t - XX := by
    have heq : linearizedScalar a b W (fun y => (Real.log (-u y) : ℂ)) x =
        ((-(n : ℝ) / t : ℝ) : ℂ) - (((t⁻¹ : ℝ) : ℂ) ^ 2) *
          (star (wirtingerGradient a b u x) ⬝ᵥ W.mulVec (wirtingerGradient a b u x)) := by
      simpa only [Fintype.card_fin, W, t, Complex.ofReal_div, Complex.ofReal_neg,
        Complex.ofReal_natCast, Complex.ofReal_inv] using
        linearizedScalar_neg_log_potential hu2 a b (hdet x hx) hux
    have hXnorm : XX = (t⁻¹) ^ 2 *
        (star (wirtingerGradient a b u x) ⬝ᵥ W.mulVec (wirtingerGradient a b u x)).re :=
      covector_norm_real_mul W _ (t⁻¹)
    rw [heq, hXnorm]
    simp only [← Complex.ofReal_pow, Complex.sub_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hLG : linearizedScalar a b W (fun y => (G y : ℂ)) x =
      (complexHessian a b u x).trace + correctionTrace a b u x :=
    gradientNormSq_evolution hU (hu.of_le (by norm_num)) a b hdet hx
  have hLc : (linearizedScalar a b W
      (fun y => (logPogorelovTest a b u κ K y : ℂ)) x).re =
      β * (linearizedScalar a b W (fun y => (Real.log (-u y) : ℂ)) x).re +
        (linearizedScalar a b W (fun y => (Real.log (S y) : ℂ)) x).re + α * H := by
    have huc : ContDiffAt ℝ 2 (fun y => (Real.log (-u y) : ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x hlogu
    have hsc : ContDiffAt ℝ 2 (fun y => (Real.log (S y) : ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x hlogS
    have hgc : ContDiffAt ℝ 2 (fun y => (G y : ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x hG
    have heq : (fun y => (logPogorelovTest a b u κ K y : ℂ)) =
        fun y => (β : ℂ) * (Real.log (-u y) : ℂ) + (Real.log (S y) : ℂ) +
          (α : ℂ) * (G y : ℂ) := by
      funext y
      simp only [logPogorelovTest, β, α, S, G, Complex.ofReal_add, Complex.ofReal_mul]
    rw [heq, linearizedScalar_add ((contDiffAt_const.mul huc).add hsc)
      (contDiffAt_const.mul hgc), linearizedScalar_add (contDiffAt_const.mul huc) hsc,
      linearizedScalar_const_mul huc, linearizedScalar_const_mul hgc, hLG]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, H]
  have hLnonpos : (linearizedScalar a b W
      (fun y => (logPogorelovTest a b u κ K y : ℂ)) x).re ≤ 0 := by
    have h := linearizedScalar_nonpos_of_isLocalMax hF hmax a b hW
    have hr := (Complex.nonneg_iff.mp (neg_nonneg.mpr h)).1
    simpa only [Complex.neg_re, neg_nonneg] using hr
  have hLS := traceCombination_log_bound hn hU hu a b hdet hx hpos hκ hmat
  change (1 / (β - 1)) *
    (star (wirtingerGradient a b (fun y => Real.log (S y)) x) ⬝ᵥ
      W.mulVec (wirtingerGradient a b (fun y => Real.log (S y)) x)).re ≤
    (linearizedScalar a b W (fun y => (Real.log (S y) : ℂ)) x).re at hLS
  rw [hstat, hnorm β] at hLS
  have hmaxScalar : -(n : ℝ) * β / t - β * XX +
      (β ^ 2 * XX + YY - 2 * β * XY) / (β - 1) + α * H ≤ 0 := by
    calc
      _ = β * (-(n : ℝ) / t - XX) +
          (1 / (β - 1)) * (β ^ 2 * XX + YY - 2 * β * XY) + α * H := by ring
      _ ≤ β * (-(n : ℝ) / t - XX) +
          (linearizedScalar a b W (fun y => (Real.log (S y) : ℂ)) x).re + α * H := by
        linarith only [hLS]
      _ = (linearizedScalar a b W
          (fun y => (logPogorelovTest a b u κ K y : ℂ)) x).re := by rw [hLc, hLneg]
      _ ≤ 0 := hLnonpos
  exact trace_bound_at_maximum hn hκ K ht hH hYX hYY hmaxScalar

/-- The same bound at a local maximum of the manuscript's test function
itself, before taking its logarithm. -/
theorem trace_bound_at_test_maximum {u : E → ℝ} {U : Set E}
    (hn : 2 ≤ n) (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : Fin n → E)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = 1)
    {x : E} (hx : x ∈ U) (hpos : (complexHessian a b u x).PosDef)
    {κ : ℝ} (hκ : 1 ≤ κ)
    (hmat : (κ • complexHessian a b u x -
      pureHessian a b u x * ((complexHessian a b u x).map star)⁻¹ *
        (pureHessian a b u x).map star).PosSemidef)
    (K : ℝ) (hK : gradientNormSq a b u x ≤ K ^ 2) (hux : u x < 0)
    (hmax : IsLocalMax (pogorelovTest a b u κ K) x) :
    (-u x) * ((complexHessian a b u x).trace.re + (correctionTrace a b u x).re) ≤
      16 * (n : ℝ) * beta n κ * (1 + K ^ 2) := by
  have hu2 : ContDiffAt ℝ 2 u x := (hu.contDiffAt (hU.mem_nhds hx)).of_le (by norm_num)
  have hS := (traceCombination_contDiffOn hU hu a b hdet (cChoice n κ)).contDiffAt
    (hU.mem_nhds hx)
  have hSx := traceCombination_pos_of_posDef hn hu2 a b hpos hκ hmat
  have hlogmax := isLocalMax_logPogorelovTest a b κ K hu2.continuousAt hS.continuousAt
    hux hSx hmax
  exact trace_bound_at_log_test_maximum hn hU hu a b hdet hx hpos hκ hmat K hK hux hlogmax

end CHS.Pogorelov
