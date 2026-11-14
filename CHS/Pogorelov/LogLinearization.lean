import CHS.Calculus.HessianExtrema
import CHS.Pogorelov.TraceEvolution

/-!
# Logarithmic derivatives and the linearized sign at a maximum
-/

set_option autoImplicit false
noncomputable section

open Filter Matrix
open scoped BigOperators ComplexOrder ContDiff MatrixOrder Topology

namespace CHS.Pogorelov

open CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem realHessian_log {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hx : f x ≠ 0) (v w : E) :
    realHessian (fun y => Real.log (f y)) x v w =
      (f x)⁻¹ * realHessian f x v w -
        (f x)⁻¹ ^ 2 * (fderiv ℝ f x v * fderiv ℝ f x w) := by
  have hnear : fderiv ℝ (fun y => Real.log (f y)) =ᶠ[𝓝 x]
      (fun y => (f y)⁻¹ • fderiv ℝ f y) := by
    filter_upwards [hf.eventually (by simp), hf.continuousAt.eventually_ne hx] with y hy hy0
    exact fderiv.log (hy.differentiableAt (by norm_num)) hy0
  have hD := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hInv : HasFDerivAt (fun y => (f y)⁻¹) (-(f x ^ 2)⁻¹ • fderiv ℝ f x) x :=
    (hasDerivAt_inv hx).comp_hasFDerivAt x (hf.differentiableAt (by norm_num)).hasFDerivAt
  have h := hInv.smul hD.hasFDerivAt
  change HasFDerivAt (fun y => (f y)⁻¹ • fderiv ℝ f y) _ x at h
  unfold realHessian
  rw [hnear.fderiv_eq, h.fderiv]
  simp only [_root_.add_apply, _root_.smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  field_simp
  <;> ring

theorem linearizedScalar_ofReal_eq_trace {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (a b : ι → E) (W : Matrix ι ι ℂ) :
    linearizedScalar a b W (fun y => (f y : ℂ)) x =
      (W * complexHessian a b f x).trace := by
  have hc : ContDiffAt ℝ 2 (fun y => (f y : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hf
  unfold linearizedScalar
  simp_rw [← dz_comm_at hc]
  rw [Finset.sum_comm]
  rfl

theorem linearizedScalar_nonpos_of_isLocalMax
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (hmax : IsLocalMax f x)
    (a b : ι → E) {W : Matrix ι ι ℂ} (hW : W.PosSemidef) :
    linearizedScalar a b W (fun y => (f y : ℂ)) x ≤ 0 := by
  have hA : (-complexHessian a b f x).PosSemidef := by
    have h := complexHessian_sub_posSemidef_of_isLocalMax hf
      (contDiffAt_const (c := (0 : ℝ))) (by simpa using hmax) a b
    have hz : complexHessian a b (fun _ : E => (0 : ℝ)) x = 0 := by
      ext i j
      have hinner : dz (a j) (-b j) (fun _ : E => (0 : ℂ)) = fun _ => (0 : ℂ) :=
        funext fun y => dz_const _ _ _ y
      change dz (a i) (b i) (dz (a j) (-b j) (fun _ : E => (0 : ℂ))) x = 0
      rw [hinner, dz_const]
    simpa only [hz, zero_sub] using h
  let P := CFC.sqrt W
  have hP : P.PosSemidef := (CFC.sqrt_nonneg W).posSemidef
  have hP2 : P * P = W := by simpa only [pow_two] using CFC.sq_sqrt W hW.nonneg
  have hprod : 0 ≤ (W * -complexHessian a b f x).trace := by
    have h := hA.conjTranspose_mul_mul_same P
    rw [hP.isHermitian.eq] at h
    rw [← hP2, ← trace_mul_cycle]
    exact h.trace_nonneg
  rw [linearizedScalar_ofReal_eq_trace hf]
  simpa only [Matrix.mul_neg, Matrix.trace_neg, neg_nonneg] using hprod


def wirtingerGradient (a b : ι → E) (f : E → ℝ) (x : E) (i : ι) : ℂ :=
  (2 : ℂ)⁻¹ * ((fderiv ℝ f x (a i) : ℂ) - Complex.I * (fderiv ℝ f x (b i) : ℂ))

theorem complexHessian_log {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hx : f x ≠ 0) (a b : ι → E) :
    complexHessian a b (fun y => Real.log (f y)) x =
      ((f x : ℂ)⁻¹) • complexHessian a b f x -
        ((f x : ℂ)⁻¹ ^ 2) • vecMulVec (wirtingerGradient a b f x)
          (star (wirtingerGradient a b f x)) := by
  have hl : ContDiffAt ℝ 2 (fun y => Real.log (f y)) x := hf.log hx
  ext i j
  rw [complexHessian_real_entry hl, Matrix.sub_apply, Matrix.smul_apply, Matrix.smul_apply,
    complexHessian_real_entry hf, vecMulVec_apply]
  simp only [realHessian_log hf hx, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_inv,
    Complex.ofReal_pow, smul_eq_mul, wirtingerGradient, Pi.star_apply, star_mul, star_sub,
    star_inv₀, star_ofNat, Complex.star_def, Complex.conj_ofReal, Complex.conj_I]
  ring_nf
  simp [Complex.I_sq]
  ring

theorem linearizedScalar_log {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hx : f x ≠ 0) (a b : ι → E) (W : Matrix ι ι ℂ) :
    linearizedScalar a b W (fun y => (Real.log (f y) : ℂ)) x =
      (f x : ℂ)⁻¹ * linearizedScalar a b W (fun y => (f y : ℂ)) x -
        (f x : ℂ)⁻¹ ^ 2 * (star (wirtingerGradient a b f x) ⬝ᵥ
          W.mulVec (wirtingerGradient a b f x)) := by
  rw [linearizedScalar_ofReal_eq_trace (hf.log hx), linearizedScalar_ofReal_eq_trace hf,
    complexHessian_log hf hx, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul,
    Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul, Matrix.mul_vecMulVec,
    Matrix.trace_vecMulVec, dotProduct_comm (W.mulVec _)]
  rfl


theorem linearizedScalar_potential {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (a b : ι → E)
    (hdet : (complexHessian a b u x).det = 1) :
    linearizedScalar a b (complexHessian a b u x)⁻¹ (fun y => (u y : ℂ)) x =
      Fintype.card ι := by
  rw [linearizedScalar_ofReal_eq_trace hu,
    Matrix.nonsing_inv_mul _ (hdet ▸ isUnit_one), Matrix.trace_one]

theorem linearizedScalar_neg_log_potential {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (a b : ι → E)
    (hdet : (complexHessian a b u x).det = 1) (hx : u x < 0) :
    let W := (complexHessian a b u x)⁻¹
    linearizedScalar a b W (fun y => (Real.log (-u y) : ℂ)) x =
      -(Fintype.card ι : ℂ) / ((-u x : ℝ) : ℂ) -
        (((-u x : ℝ) : ℂ)⁻¹ ^ 2) *
          (star (wirtingerGradient a b u x) ⬝ᵥ W.mulVec (wirtingerGradient a b u x)) := by
  have hA : complexHessian a b (fun y => -u y) x = -complexHessian a b u x := by
    have heq : fderiv ℝ (fun y => -u y) = fun y => -fderiv ℝ u y :=
      funext fun _ => fderiv_fun_neg
    have hH (v w : E) : realHessian (fun y => -u y) x v w = -realHessian u x v w := by
      unfold realHessian
      rw [heq, fderiv_fun_neg]
      rfl
    ext i j
    rw [Matrix.neg_apply, complexHessian_real_entry hu.neg, complexHessian_real_entry hu]
    simp only [hH, Complex.ofReal_neg]
    ring
  have hG : wirtingerGradient a b (fun y => -u y) x = -wirtingerGradient a b u x := by
    funext i
    simp only [wirtingerGradient, fderiv_fun_neg, _root_.neg_apply, Pi.neg_apply, Complex.ofReal_neg]
    ring
  dsimp only
  rw [linearizedScalar_log hu.neg (neg_ne_zero.mpr hx.ne), hG,
    linearizedScalar_ofReal_eq_trace hu.neg, hA, Matrix.mul_neg, Matrix.trace_neg,
    Matrix.nonsing_inv_mul _ (hdet ▸ isUnit_one), Matrix.trace_one,
    star_neg, Matrix.mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg]
  ring

end CHS.Pogorelov
