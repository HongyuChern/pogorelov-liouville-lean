import CHS.Calculus.ClosureJets
import CHS.Pogorelov.WeightedMaximum

/-!
# The actual Pogorelov test and its C² boundary extension

The polynomial jet extension agrees with the actual test on the open
domain.  On its boundary only the continuous value and the positive
exponent are needed; no boundary derivatives of an ambient extension are
taken.
-/

set_option autoImplicit false
noncomputable section

open Matrix Set Filter
open scoped BigOperators ContDiff Topology

namespace CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem jetWirtinger_eq_dz {u : E → ℝ} {x : E}
    (hu : DifferentiableAt ℝ u x) (a b : ι → E) (i : ι) :
    jetWirtinger a b (fderiv ℝ u x) i = dz (a i) (b i) (fun y => (u y : ℂ)) x := by
  have h := Complex.ofRealCLM.hasFDerivAt.comp x hu.hasFDerivAt
  change HasFDerivAt (fun y => (u y : ℂ))
    (Complex.ofRealCLM.comp (fderiv ℝ u x)) x at h
  simp only [jetWirtinger, dz, rd, h.fderiv,
    ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]

namespace ClosureC2Jet

variable {u : E → ℝ} {U : Set E}

theorem complexField_eq (J : ClosureC2Jet u U) {x : E} (hx : x ∈ U)
    (hu : ContDiffAt ℝ 2 u x) (a b : ι → E) :
    J.complexField a b x = complexHessian a b u x := by
  ext i j
  rw [complexField, J.hessian_eq hx]
  exact (complexHessian_real_entry hu a b i j).symm

theorem pureField_eq (J : ClosureC2Jet u U) {x : E} (hx : x ∈ U)
    (hu : ContDiffAt ℝ 2 u x) (a b : ι → E) :
    J.pureField a b x = pureHessian a b u x := by
  ext i j
  rw [pureField, J.hessian_eq hx]
  exact (pureHessian_real_entry hu a b i j).symm

theorem gradientField_eq (J : ClosureC2Jet u U) {x : E} (hx : x ∈ U)
    (hu : DifferentiableAt ℝ u x) {n : ℕ} (a b : Fin n → E) :
    J.gradientField a b x = CHS.Pogorelov.gradientNormSq a b u x := by
  simp only [gradientField, jetGradientNormSq, CHS.Pogorelov.gradientNormSq,
    J.derivative_eq hx, jetWirtinger_eq_dz hu]

theorem traceField_eq (J : ClosureC2Jet u U) {x : E} (hx : x ∈ U)
    (hu : ContDiffAt ℝ 2 u x) (a b : ι → E)
    (hdet : (complexHessian a b u x).det = 1) (c : ℝ) :
    J.traceField a b c x = CHS.Pogorelov.traceCombination a b u c x := by
  have hbar : (complexHessian a b u x).map star = (complexHessian a b u x).transpose := by
    ext i j
    exact (complexHessian_isHermitian hu a b).apply j i
  have hinv : ((complexHessian a b u x).map star)⁻¹ =
      ((complexHessian a b u x).map star).adjugate := by
    rw [Matrix.inv_def, hbar, Matrix.det_transpose, hdet]
    simp
  change c * (J.complexField a b x).trace.re +
    (J.pureField a b x * ((J.complexField a b x).map star).adjugate *
      (J.pureField a b x).map star).trace.re = _
  rw [J.complexField_eq hx hu a b, J.pureField_eq hx hu a b]
  simp only [CHS.Pogorelov.traceCombination, CHS.Pogorelov.correctionTrace_eq, hinv]

end ClosureC2Jet
end CHS.Calculus

namespace CHS.Pogorelov

open CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : ℕ} {u : E → ℝ} {U : Set E}

def closurePogorelovTest (J : ClosureC2Jet u U) (a b : Fin n → E)
    (κ K : ℝ) (x : E) : ℝ :=
  (-u x) ^ beta n κ * J.traceField a b (cChoice n κ) x *
    Real.exp (alpha K * J.gradientField a b x)

theorem closurePogorelovTest_continuousOn (J : ClosureC2Jet u U)
    (a b : Fin n → E) {κ : ℝ} (hβ : 0 ≤ beta n κ) (K : ℝ) :
    ContinuousOn (closurePogorelovTest J a b κ K) (closure U) := by
  exact ((J.continuous_value.neg.rpow_const (fun _ _ => Or.inr hβ)).mul
    (J.continuousOn_traceField a b (cChoice n κ))).mul
      (Real.continuous_exp.comp_continuousOn
        ((J.continuousOn_gradientField a b).const_mul (alpha K)))

theorem closurePogorelovTest_eq (J : ClosureC2Jet u U)
    {x : E} (hx : x ∈ U) (hu : ContDiffAt ℝ 2 u x) (a b : Fin n → E)
    (hdet : (complexHessian a b u x).det = 1) (κ K : ℝ) :
    closurePogorelovTest J a b κ K x = pogorelovTest a b u κ K x := by
  simp only [closurePogorelovTest, pogorelovTest,
    J.traceField_eq hx hu a b hdet,
    J.gradientField_eq hx (hu.differentiableAt (by norm_num)) a b]

theorem closurePogorelovTest_eq_zero_on_frontier (J : ClosureC2Jet u U)
    (a b : Fin n → E) {κ : ℝ} (hβ : 0 < beta n κ) (K : ℝ)
    (hbd : ∀ x ∈ frontier U, u x = 0) :
    ∀ x ∈ frontier U, closurePogorelovTest J a b κ K x = 0 := by
  intro x hx
  simp only [closurePogorelovTest, hbd x hx, neg_zero,
    Real.zero_rpow hβ.ne', zero_mul]

end CHS.Pogorelov
