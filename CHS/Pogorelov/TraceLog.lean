import CHS.Pogorelov.DiagonalTrace

/-!
# The logarithmic inequality for the actual Pogorelov trace

The final theorem proves (2.28) in a constant frame which diagonalizes the
mixed Hessian at the evaluation point.  It does not assume a logarithmic
gradient inequality or an independently supplied derivative field.
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

theorem wirtingerGradient_eq_dz {f : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (a b : ι → E) (i : ι) :
    wirtingerGradient a b f x i = dz (a i) (b i) (fun y => (f y : ℂ)) x := by
  have h := Complex.ofRealCLM.hasFDerivAt.comp x hf.hasFDerivAt
  change HasFDerivAt (fun y => (f y : ℂ))
    (Complex.ofRealCLM.comp (fderiv ℝ f x)) x at h
  simp only [wirtingerGradient, dz, rd, h.fderiv,
    ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]

theorem wirtingerGradient_log {f : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hx : f x ≠ 0) (a b : ι → E) :
    wirtingerGradient a b (fun y => Real.log (f y)) x =
      fun i => ((f x : ℂ)⁻¹) * wirtingerGradient a b f x i := by
  funext i
  simp only [wirtingerGradient, fderiv.log hf hx,
    ContinuousLinearMap.smul_apply, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_inv]
  ring

theorem covector_norm_real_mul (W : Matrix ι ι ℂ) (v : ι → ℂ) (t : ℝ) :
    (star (fun i => (t : ℂ) * v i) ⬝ᵥ W.mulVec (fun i => (t : ℂ) * v i)).re =
      t ^ 2 * (star v ⬝ᵥ W.mulVec v).re := by
  change (star ((t : ℂ) • v) ⬝ᵥ W.mulVec ((t : ℂ) • v)).re = _
  rw [star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct]
  simp only [smul_eq_mul, Complex.star_def, Complex.conj_ofReal,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero, add_zero]
  ring

theorem log_covector_norm_eq {f : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hx : f x ≠ 0)
    (a b : ι → E) (W : Matrix ι ι ℂ) :
    (star (wirtingerGradient a b (fun y => Real.log (f y)) x) ⬝ᵥ
      W.mulVec (wirtingerGradient a b (fun y => Real.log (f y)) x)).re =
    (star (wirtingerGradient a b f x) ⬝ᵥ W.mulVec (wirtingerGradient a b f x)).re /
      (f x) ^ 2 := by
  rw [wirtingerGradient_log hf hx]
  have h := covector_norm_real_mul W (wirtingerGradient a b f x) (f x)⁻¹
  simpa only [Complex.ofReal_inv, div_eq_mul_inv, inv_pow, mul_comm] using h

theorem linearizedScalar_log_re {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hx : f x ≠ 0)
    (a b : ι → E) (W : Matrix ι ι ℂ) :
    (linearizedScalar a b W (fun y => (Real.log (f y) : ℂ)) x).re =
      (linearizedScalar a b W (fun y => (f y : ℂ)) x).re / f x -
      (star (wirtingerGradient a b f x) ⬝ᵥ W.mulVec (wirtingerGradient a b f x)).re /
        (f x) ^ 2 := by
  rw [linearizedScalar_log hf hx]
  simp only [← Complex.ofReal_inv, ← Complex.ofReal_pow, Complex.sub_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [inv_pow]
  ring

/-- Equation (2.28), with actual first and second derivatives and with no
assumption of the desired scalar estimate. -/
theorem diagonal_traceCombination_log_bound {u : E → ℝ} {U : Set E}
    (hn : 2 ≤ n) (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : Fin n → E)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = 1)
    {x : E} (hx : x ∈ U) (hpos : (complexHessian a b u x).PosDef)
    (r : Fin n → ℝ) (hr : ∀ p, 0 < r p)
    (hA : complexHessian a b u x = diagonal (fun i => (r i : ℂ) ^ 2))
    {κ : ℝ} (hκ : 1 ≤ κ)
    (hmat : (κ • complexHessian a b u x -
      pureHessian a b u x * ((complexHessian a b u x).map star)⁻¹ *
        (pureHessian a b u x).map star).PosSemidef) :
    let S := traceCombination a b u (cChoice n κ)
    let W := (complexHessian a b u x)⁻¹
    let g := wirtingerGradient a b (fun y => Real.log (S y)) x
    (1 / (beta n κ - 1)) * (star g ⬝ᵥ W.mulVec g).re ≤
      (linearizedScalar a b W (fun y => (Real.log (S y) : ℂ)) x).re := by
  let c := cChoice n κ
  let A := complexHessian a b u
  let W := (A x)⁻¹
  let S := traceCombination a b u c
  let Q := CHS.WeightedSquares.matrixSquare W W (fun p => matrixDZ (a p) (b p) A x)
  let F := CHS.WeightedSquares.matrixSquare W (((A x).map star)⁻¹)
    (fun p => compensatedHessian a b u p x)
  let L := (linearizedScalar a b W (fun y => (S y : ℂ)) x).re
  let Z := (star (wirtingerGradient a b S x) ⬝ᵥ W.mulVec (wirtingerGradient a b S x)).re
  have hc : 0 < c := cChoice_pos hn hκ
  have hu2 : ContDiffAt ℝ 2 u x := (hu.contDiffAt (hU.mem_nhds hx)).of_le (by norm_num)
  have hSreg : ContDiffAt ℝ 2 S x :=
    (traceCombination_contDiffOn hU hu a b hdet c).contDiffAt (hU.mem_nhds hx)
  have htr : (A x).trace.re = ∑ p, r p ^ 2 := by
    change (complexHessian a b u x).trace.re = _
    rw [hA, Matrix.trace_diagonal, Complex.re_sum]
    simp only [← Complex.ofReal_pow, Complex.ofReal_re]
  have ha : 0 < (A x).trace.re := by
    rw [htr]
    let p : Fin n := ⟨0, by omega⟩
    have hle : r p ^ 2 ≤ ∑ q, r q ^ 2 :=
      Finset.single_le_sum (fun q _ => sq_nonneg (r q)) (Finset.mem_univ p)
    exact (sq_pos_of_pos (hr p)).trans_le hle
  have hmat' : (κ • A x - (A x - schurHessian a b u x)).PosSemidef := by
    change (κ • A x - (A x - (A x - _))).PosSemidef
    rw [sub_sub_cancel]
    exact hmat
  have hd := schur_correction_trace_bounds hu2 a b hpos κ hmat'
  have hd0 : 0 ≤ (correctionTrace a b u x).re := hd.1
  have hdκ : (correctionTrace a b u x).re ≤ κ * (A x).trace.re := hd.2
  have hSpos : 0 < S x := add_pos_of_pos_of_nonneg (mul_pos hc ha) hd0
  have hLeq : L = (c + 1) * Q.trace.re + F.trace.re := by
    have h := congrArg Complex.re (traceCombination_evolution hU hu a b hdet hx hpos c)
    change L = (((c : ℂ) + 1) * Q.trace + F.trace).re at h
    simpa only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.one_re, Complex.one_im, add_zero,
      zero_add, zero_mul, sub_zero] using h
  obtain ⟨hQ, hF, _, _⟩ := trace_evolution hU hu a b hdet hx hpos
  have hQ0 : 0 ≤ Q.trace.re := (Complex.nonneg_iff.mp hQ).1
  have hF0 : 0 ≤ F.trace.re := (Complex.nonneg_iff.mp hF).1
  have hL0 : 0 ≤ L := by
    rw [hLeq]
    exact add_nonneg (mul_nonneg (by linarith) hQ0) hF0
  have hZ := diagonal_traceCombination_gradient_bound hn hU hu a b hdet hx hpos r hr hA
    c κ hc.le (by linarith) hmat
  have hg : wirtingerGradient a b S x = fun i =>
      dz (a i) (b i) (fun y => (S y : ℂ)) x := by
    funext i
    exact wirtingerGradient_eq_dz (hSreg.differentiableAt (by norm_num)) a b i
  have hZ' : Z ≤ ((c ^ 2 + ((n : ℝ) - 1) * κ) / (c + 1) * (A x).trace.re +
      (correctionTrace a b u x).re) * L := by
    dsimp only [Z]
    rw [hg, hLeq]
    exact hZ
  have hscalar := chosen_log_gradient_bound hn hκ ha hd0 hdκ hL0 hZ'
  dsimp only
  change (1 / (beta n κ - 1)) *
    (star (wirtingerGradient a b (fun y => Real.log (S y)) x) ⬝ᵥ
      W.mulVec (wirtingerGradient a b (fun y => Real.log (S y)) x)).re ≤
    (linearizedScalar a b W (fun y => (Real.log (S y) : ℂ)) x).re
  rw [log_covector_norm_eq (hSreg.differentiableAt (by norm_num)) hSpos.ne',
    linearizedScalar_log_re hSreg hSpos.ne']
  exact hscalar

end CHS.Pogorelov
