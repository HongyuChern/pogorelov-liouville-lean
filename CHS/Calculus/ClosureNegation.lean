import CHS.Calculus.ClosureRegularity
import Mathlib.Analysis.Normed.Group.Continuity

/-! # Negation preserves the actual C² boundary regularity -/

set_option autoImplicit false
noncomputable section

open Set
open scoped ContDiff

namespace CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {u : E → ℝ} {U : Set E}

def ClosureC2Jet.neg (J : ClosureC2Jet u U) : ClosureC2Jet (fun x => -u x) U where
  derivative := fun x => -J.derivative x
  hessian := fun x => -J.hessian x
  continuous_value := J.continuous_value.neg
  continuous_derivative := J.continuous_derivative.neg
  continuous_hessian := by
    apply (J.continuous_hessian.const_smul (-1 : ℝ)).congr
    intro x hx
    ext v w
    simp
  derivative_eq := by
    intro x hx
    change -J.derivative x = fderiv ℝ (fun y => -u y) x
    rw [fderiv_fun_neg, J.derivative_eq hx]
  hessian_eq := by
    intro x hx
    have hd : fderiv ℝ (fun y => -u y) = fun y => -fderiv ℝ u y :=
      funext fun _ => fderiv_fun_neg
    change -J.hessian x = fderiv ℝ (fderiv ℝ (fun y => -u y)) x
    rw [hd, fderiv_fun_neg, J.hessian_eq hx]

theorem C2OnClosure.neg (hu : C2OnClosure u U) : C2OnClosure (fun x => -u x) U :=
  ⟨hu.1.neg, ⟨hu.jet.neg⟩⟩

end CHS.Calculus
