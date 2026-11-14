import CHS.Calculus.ClosureRegularity
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic.FunProp

/-!
# Polynomial complex fields of the continuous boundary jets

The correction trace is written with an adjugate.  On the solution set,
`det A = 1` identifies it with `tr (B (conj A)⁻¹ conj B)`.  Consequently its
boundary continuity follows from the C² jets without differentiating an
arbitrary extension or introducing any boundary ellipticity assumption.
-/

set_option autoImplicit false
noncomputable section

open Matrix Set
open scoped BigOperators

namespace CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*}

def jetWirtinger (a b : ι → E) (D : E →L[ℝ] ℝ) (i : ι) : ℂ :=
  (2 : ℂ)⁻¹ * ((D (a i) : ℂ) - Complex.I * (D (b i) : ℂ))

def jetComplexHessian (a b : ι → E) (H : E →L[ℝ] E →L[ℝ] ℝ) : Matrix ι ι ℂ :=
  fun i j => (4 : ℂ)⁻¹ *
    ((H (a i) (a j) : ℂ) + (H (b i) (b j) : ℂ) +
      Complex.I * ((H (a i) (b j) : ℂ) - (H (b i) (a j) : ℂ)))

def jetPureHessian (a b : ι → E) (H : E →L[ℝ] E →L[ℝ] ℝ) : Matrix ι ι ℂ :=
  fun i j => (4 : ℂ)⁻¹ *
    ((H (a i) (a j) : ℂ) - (H (b i) (b j) : ℂ) -
      Complex.I * ((H (a i) (b j) : ℂ) + (H (b i) (a j) : ℂ)))

theorem continuous_jetWirtinger (a b : ι → E) :
    Continuous (jetWirtinger a b) := by
  unfold jetWirtinger
  fun_prop

theorem continuous_jetComplexHessian (a b : ι → E) :
    Continuous (jetComplexHessian a b) := by
  unfold jetComplexHessian
  fun_prop

theorem continuous_jetPureHessian (a b : ι → E) :
    Continuous (jetPureHessian a b) := by
  unfold jetPureHessian
  fun_prop

variable [Fintype ι] [DecidableEq ι]

def jetGradientNormSq (a b : ι → E) (D : E →L[ℝ] ℝ) : ℝ :=
  ∑ i, Complex.normSq (jetWirtinger a b D i)

def jetTraceCombination (a b : ι → E) (c : ℝ)
    (H : E →L[ℝ] E →L[ℝ] ℝ) : ℝ :=
  let A := jetComplexHessian a b H
  let B := jetPureHessian a b H
  c * A.trace.re + (B * (A.map star).adjugate * B.map star).trace.re

theorem continuous_jetGradientNormSq (a b : ι → E) :
    Continuous (jetGradientNormSq a b) := by
  unfold jetGradientNormSq jetWirtinger
  simp only [Complex.normSq_apply]
  fun_prop

theorem continuous_jetTraceCombination (a b : ι → E) (c : ℝ) :
    Continuous (jetTraceCombination a b c) := by
  have hA := continuous_jetComplexHessian a b
  have hB := continuous_jetPureHessian a b
  have hbarA : Continuous (fun H => (jetComplexHessian a b H).map star) := by
    exact continuous_pi fun i => continuous_pi fun j =>
      ((continuous_apply j).comp ((continuous_apply i).comp hA)).star
  have hbarB : Continuous (fun H => (jetPureHessian a b H).map star) := by
    exact continuous_pi fun i => continuous_pi fun j =>
      ((continuous_apply j).comp ((continuous_apply i).comp hB)).star
  exact (Complex.continuous_re.comp hA.matrix_trace |>.const_mul c).add
    (Complex.continuous_re.comp
      ((hB.matrix_mul hbarA.matrix_adjugate).matrix_mul hbarB).matrix_trace)

namespace ClosureC2Jet

variable {u : E → ℝ} {U : Set E}

def complexField (J : ClosureC2Jet u U) (a b : ι → E) (x : E) : Matrix ι ι ℂ :=
  jetComplexHessian a b (J.hessian x)

def pureField (J : ClosureC2Jet u U) (a b : ι → E) (x : E) : Matrix ι ι ℂ :=
  jetPureHessian a b (J.hessian x)

def gradientField (J : ClosureC2Jet u U) (a b : ι → E) (x : E) : ℝ :=
  jetGradientNormSq a b (J.derivative x)

def traceField (J : ClosureC2Jet u U) (a b : ι → E) (c : ℝ) (x : E) : ℝ :=
  jetTraceCombination a b c (J.hessian x)

theorem continuousOn_complexField (J : ClosureC2Jet u U) (a b : ι → E) :
    ContinuousOn (J.complexField a b) (closure U) :=
  (continuous_jetComplexHessian a b).comp_continuousOn J.continuous_hessian

theorem continuousOn_pureField (J : ClosureC2Jet u U) (a b : ι → E) :
    ContinuousOn (J.pureField a b) (closure U) :=
  (continuous_jetPureHessian a b).comp_continuousOn J.continuous_hessian

theorem continuousOn_gradientField (J : ClosureC2Jet u U) (a b : ι → E) :
    ContinuousOn (J.gradientField a b) (closure U) :=
  (continuous_jetGradientNormSq a b).comp_continuousOn J.continuous_derivative

theorem continuousOn_traceField (J : ClosureC2Jet u U) (a b : ι → E) (c : ℝ) :
    ContinuousOn (J.traceField a b c) (closure U) :=
  (continuous_jetTraceCombination a b c).comp_continuousOn J.continuous_hessian

end ClosureC2Jet
end CHS.Calculus
