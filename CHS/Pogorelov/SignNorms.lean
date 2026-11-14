import CHS.Pogorelov.GeneralEstimate
import CHS.Calculus.PotentialNegation
import CHS.Algebra.SignBranch

/-!
# Exact norm and geometry identities for the negative branch

Negation preserves the actual derivative seminorms.  At κ = 1 the
manuscript's weight is an even integer power, so the weighted Hessian
seminorm is preserved as well.  No sign assumption on the potential is
used in these identities.
-/

set_option autoImplicit false
noncomputable section

open Set MeasureTheory Matrix
open scoped ContDiff ENNReal

namespace CHS.Analysis

variable {E ι κ : Type*} [MeasurableSpace E]

theorem entryLinfNormOn_neg (μ : Measure E) (U : Set E) (H : E → Matrix ι κ ℝ) :
    entryLinfNormOn μ U (fun x => -H x) = entryLinfNormOn μ U H := by
  have heq : (fun p : ι × κ =>
      (eLpNorm (fun x => (-H x) p.1 p.2) ∞ (μ.restrict U)).toReal) =
      (fun p : ι × κ => (eLpNorm (fun x => H x p.1 p.2) ∞ (μ.restrict U)).toReal) := by
    funext p
    exact congrArg ENNReal.toReal (eLpNorm_neg (fun x => H x p.1 p.2) ∞ (μ.restrict U))
  unfold entryLinfNormOn
  rw [heq]

end CHS.Analysis

namespace CHS.Pogorelov

open CHS.Calculus CHS.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : ℕ}

theorem gradientNormSq_neg (a b : Fin n → E) (u : E → ℝ) (x : E) :
    gradientNormSq a b (fun y => -u y) x = gradientNormSq a b u x := by
  have heq : (fun y => ((-u y : ℝ) : ℂ)) = fun y => -(u y : ℂ) := by
    funext y
    exact Complex.ofReal_neg _
  simp only [gradientNormSq, heq, dz_neg_fun, Complex.normSq_neg]

variable [MeasurableSpace E]

theorem scalarLinfNormOn_neg (μ : Measure E) (U : Set E) (u : E → ℝ) :
    scalarLinfNormOn μ U (fun x => -u x) = scalarLinfNormOn μ U u := by
  unfold scalarLinfNormOn
  exact congrArg ENNReal.toReal (eLpNorm_neg u ∞ (μ.restrict U))

theorem gradientLinfNormOn_neg (μ : Measure E) (a b : Fin n → E)
    (u : E → ℝ) (U : Set E) :
    gradientLinfNormOn μ a b (fun x => -u x) U = gradientLinfNormOn μ a b u U := by
  simp only [gradientLinfNormOn, gradientNormSq_neg]

theorem weightedHessianLinfNormOn_neg_at_one (μ : Measure E) (a b : Fin n → E)
    (u : E → ℝ) (U : Set E) :
    weightedHessianLinfNormOn μ a b (fun x => -u x) U 1 =
      weightedHessianLinfNormOn μ a b u U 1 := by
  have hw (x : E) : u x ^ beta n 1 = (-u x) ^ beta n 1 :=
    (CHS.pogorelov_weight_neg_at_one n (u x)).symm
  unfold weightedHessianLinfNormOn
  simp only [neg_neg, realBlockHessian_neg, hw, smul_neg]
  exact entryLinfNormOn_neg μ U _

end CHS.Pogorelov

namespace CHS

open Calculus Analysis Pogorelov

variable {n : ℕ}
local notation "E" => DeGiorgi.AmbientSpace (n + n)

theorem PogorelovCompactGeometry.neg {U : Set E} {u : E → ℝ}
    (h : PogorelovCompactGeometry U u) : PogorelovCompactGeometry U (fun x => -u x) := by
  rcases h with hbounded | ⟨L, hUinv, huinv, hquot⟩
  · exact Or.inl hbounded
  · exact Or.inr ⟨L, hUinv, fun x hx v hv => congrArg Neg.neg (huinv x hx v hv), hquot⟩

theorem euclideanHessian_neg (u : E → ℝ) (x : E) :
    euclideanHessian (fun y => -u y) x = -euclideanHessian u x := by
  ext i j
  simp only [euclideanHessian, realHessian_neg, Matrix.neg_apply]
  rfl

theorem weighted_euclideanHessian_linf_neg_at_one (μ : Measure E)
    (u : E → ℝ) (U : Set E) :
    entryLinfNormOn μ U (fun x => ((-(-u x)) ^ beta n 1) •
      euclideanHessian (fun y => -u y) x) =
    entryLinfNormOn μ U (fun x => ((-u x) ^ beta n 1) • euclideanHessian u x) := by
  have hw (x : E) : u x ^ beta n 1 = (-u x) ^ beta n 1 :=
    (pogorelov_weight_neg_at_one n (u x)).symm
  simp only [neg_neg, euclideanHessian_neg, hw, smul_neg]
  exact entryLinfNormOn_neg μ U _

end CHS
