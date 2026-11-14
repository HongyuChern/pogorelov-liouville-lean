import CHS.Calculus.BasisHessian
import CHS.Calculus.PotentialScalars
import CHS.Calculus.AffinePullback

/-!
# Actual directional second derivatives are linearized subsolutions

For a real C4 determinant-one potential with positive complex Hessian,
the actual function x ↦ D²u(x)[e,e] is C2 and its complex linearization
is nonnegative.  The square on the right comes from differentiating the
equation twice in the real direction e; all factors of 1/2 are retained.
-/

set_option autoImplicit false
noncomputable section

open Matrix Set
open scoped BigOperators ComplexOrder ContDiff MatrixOrder Topology

namespace CHS.Algebra

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem trace_product_posSemidef_nonneg {P Q : Matrix ι ι ℂ}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) : 0 ≤ (P * Q).trace.re := by
  let S := CFC.sqrt P
  have hS : S.PosSemidef := (CFC.sqrt_nonneg P).posSemidef
  have hS2 : S * S = P := by simpa only [pow_two] using CFC.sq_sqrt P hP.nonneg
  have h := hQ.conjTranspose_mul_mul_same S
  rw [hS.isHermitian.eq] at h
  rw [← hS2, ← trace_mul_cycle]
  exact (Complex.nonneg_iff.mp h.trace_nonneg).1

theorem trace_hermitian_weighted_square_nonneg {W X : Matrix ι ι ℂ}
    (hW : W.PosSemidef) (hX : X.IsHermitian) :
    0 ≤ (W * X * W * X).trace.re := by
  have h := hW.conjTranspose_mul_mul_same X
  rw [hX.eq] at h
  simpa only [Matrix.mul_assoc] using trace_product_posSemidef_nonneg hW h

end CHS.Algebra

namespace CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem realHessian_contDiffAt_two {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 4 u x) (v w : E) :
    ContDiffAt ℝ 2 (fun y => realHessian u y v w) x := by
  have h := (hu.fderiv_right (m := 3) (by norm_num)).fderiv_right (m := 2) (by norm_num)
  exact (h.clm_apply contDiffAt_const).clm_apply contDiffAt_const

theorem dz_zero_direction (v : E) (f : E → ℂ) (x : E) :
    dz v 0 f x = (2 : ℂ)⁻¹ * rd v f x := by simp [dz, rd]

theorem dz_dz_zero_ofReal {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (v w : E) :
    dz v 0 (dz w 0 (fun y => (u y : ℂ))) x =
      (4 : ℂ)⁻¹ * (realHessian u x v w : ℂ) := by
  have heq : dz w 0 (fun y => (u y : ℂ)) =
      fun y => (2 : ℂ)⁻¹ * rd w (fun z => (u z : ℂ)) y :=
    funext (dz_zero_direction w _)
  rw [heq, dz_const_mul_fun, dz_zero_direction, rd_rd_ofReal hu]
  ring

theorem matrixDZ_real_direction_isHermitian {G : E → Matrix ι ι ℂ} {x : E}
    (hG : ∀ᶠ y in 𝓝 x, (G y).IsHermitian) (e : E) :
    (matrixDZ e 0 G x).IsHermitian := by
  have heq : (fun y => (G y).conjTranspose) =ᶠ[𝓝 x] G := hG
  have h := matrixDZ_conjTranspose e 0 G x
  rw [neg_zero, matrixDZ_congr_nhds e 0 heq] at h
  exact h.symm

theorem directionalHessian_linearized_nonneg
    {u : E → ℝ} {U : Set E} (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U)
    (a b : ι → E) (hdet : ∀ y ∈ U, (complexHessian a b u y).det = 1)
    {x : E} (hx : x ∈ U) (hA : (complexHessian a b u x).PosDef) (e : E) :
    0 ≤ ∑ i, ∑ j, realLinearizationMatrix (complexHessian a b u x)⁻¹ i j *
      realBlockHessian a b (fun y => realHessian u y e e) x i j := by
  let v : E → ℝ := fun y => realHessian u y e e
  let f : E → ℝ := fun y => (4 : ℝ)⁻¹ * v y
  have hv : ContDiffAt ℝ 2 v x :=
    realHessian_contDiffAt_two (hu.contDiffAt (hU.mem_nhds hx)) e e
  have hf : ContDiffAt ℝ 2 f x := contDiffAt_const.mul hv
  have hreal : EqOn (fun y => (f y : ℂ))
      (dz e 0 (dz e 0 (fun y => (u y : ℂ)))) U := by
    intro y hy
    rw [dz_dz_zero_ofReal ((hu.contDiffAt (hU.mem_nhds hy)).of_le (by norm_num))]
    simp only [f, v, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_ofNat]
  have hDX : (matrixDZ e 0 (complexHessian a b u) x).IsHermitian := by
    apply matrixDZ_real_direction_isHermitian
    filter_upwards [hU.mem_nhds hx] with y hy
    exact complexHessian_isHermitian
      ((hu.contDiffAt (hU.mem_nhds hy)).of_le (by norm_num)) a b
  have hsquare := CHS.Algebra.trace_hermitian_weighted_square_nonneg hA.inv.posSemidef hDX
  have hfirst : 0 ≤ (∑ p, ∑ q, (complexHessian a b u x)⁻¹ q p *
      complexHessian a b f x p q).re := by
    have hentry (p q : ι) : complexHessian a b f x p q =
        dz (a q) (-b q) (dz (a p) (b p)
          (dz e 0 (dz e 0 (fun y => (u y : ℂ))))) x := by
      change dz (a p) (b p) (dz (a q) (-b q) (fun y => (f y : ℂ))) x = _
      have hfc : ContDiffAt ℝ 2 (fun y => (f y : ℂ)) x :=
        Complex.ofRealCLM.contDiff.contDiffAt.comp x hf
      rw [dz_comm_at hfc]
      rw [dz_congr_on hU (fun y hy => dz_congr_on hU hreal (a p) (b p) hy)
        (a q) (-b q) hx]
    simp_rw [hentry]
    rw [linearized_secondDerivative_det_one hU hu a b hdet hx e 0 e 0]
    exact hsquare
  rw [realLinearizationMatrix_pairing hf a b _] at hfirst
  have hscale (i j : ι ⊕ ι) : realBlockHessian a b f x i j =
      (4 : ℝ)⁻¹ * realBlockHessian a b v x i j := by
    simp only [realBlockHessian, f, realHessian_const_mul, _root_.smul_apply, smul_eq_mul]
  simp only [hscale, ← mul_assoc] at hfirst
  have heq : (∑ i, ∑ j, realLinearizationMatrix (complexHessian a b u x)⁻¹ i j *
      ((4 : ℝ)⁻¹ * realBlockHessian a b v x i j)) =
      (4 : ℝ)⁻¹ * (∑ i, ∑ j,
        realLinearizationMatrix (complexHessian a b u x)⁻¹ i j *
          realBlockHessian a b v x i j) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hfirst' : 0 ≤ (4 : ℝ)⁻¹ * (∑ i, ∑ j,
      realLinearizationMatrix (complexHessian a b u x)⁻¹ i j *
        realBlockHessian a b v x i j) := by
    rw [← heq]
    simpa only [mul_assoc] using hfirst
  exact nonneg_of_mul_nonneg_right hfirst' (by norm_num)

end CHS.Calculus
