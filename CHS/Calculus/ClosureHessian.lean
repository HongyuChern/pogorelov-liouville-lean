import CHS.Calculus.ClosureJets
import CHS.Calculus.BasisHessian
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Real Hessian fields from the actual C² boundary jets

Every entry is a fixed evaluation of the continuous second derivative jet.
The equality on the domain uses the actual second Fréchet derivative.  The
weighted extension is continuous for each nonnegative real exponent.
-/

set_option autoImplicit false
noncomputable section

open Set

namespace CHS.Calculus.ClosureC2Jet

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {u : E → ℝ} {U : Set E}

def realField (J : ClosureC2Jet u U) (a b : ι → E) (x : E) :
    Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  fun i j => J.hessian x (Sum.elim a b i) (Sum.elim a b j)

theorem realField_eq (J : ClosureC2Jet u U) {x : E} (hx : x ∈ U) (a b : ι → E) :
    J.realField a b x = realBlockHessian a b u x := by
  ext i j
  change J.hessian x (Sum.elim a b i) (Sum.elim a b j) = _
  rw [J.hessian_eq hx]
  rfl

theorem continuousOn_realField_entry (J : ClosureC2Jet u U) (a b : ι → E)
    (i j : ι ⊕ ι) : ContinuousOn (fun x => J.realField a b x i j) (closure U) := by
  exact (J.continuous_hessian.clm_apply continuousOn_const).clm_apply continuousOn_const

theorem continuousOn_realBlockHessian_entry (J : ClosureC2Jet u U) (a b : ι → E)
    (i j : ι ⊕ ι) : ContinuousOn (fun x => realBlockHessian a b u x i j) U := by
  apply ((J.continuousOn_realField_entry a b i j).mono subset_closure).congr
  intro x hx
  exact congrArg (fun M => M i j) (J.realField_eq hx a b).symm

theorem continuousOn_weighted_realField_entry (J : ClosureC2Jet u U) (a b : ι → E)
    {β : ℝ} (hβ : 0 ≤ β) (i j : ι ⊕ ι) :
    ContinuousOn (fun x => (-u x) ^ β * J.realField a b x i j) (closure U) := by
  exact (J.continuous_value.neg.rpow_const (fun _ _ => Or.inr hβ)).mul
    (J.continuousOn_realField_entry a b i j)

theorem continuousOn_weighted_realBlockHessian_entry (J : ClosureC2Jet u U)
    (a b : ι → E) {β : ℝ} (hβ : 0 ≤ β) (i j : ι ⊕ ι) :
    ContinuousOn (fun x => (((-u x) ^ β) • realBlockHessian a b u x) i j) U := by
  apply ((J.continuousOn_weighted_realField_entry a b hβ i j).mono subset_closure).congr
  intro x hx
  simp only [Matrix.smul_apply, smul_eq_mul, J.realField_eq hx a b]

end CHS.Calculus.ClosureC2Jet
