import CHS.Calculus.ClosureRegularity
import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
# Translation invariance of the actual boundary jets

Invariance is assumed only on the open domain.  First and second derivative
invariance is proved there by the chain rule, and then extended to the
closure by continuity and density.  Values outside the closure play no role.
-/

set_option autoImplicit false
noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem translation_maps_closure {U : Set E} (L : Submodule ℝ E)
    (hUinv : ∀ x ∈ U, ∀ v ∈ L, x + v ∈ U) {v : E} (hv : v ∈ L) :
    MapsTo (fun x => x + v) (closure U) (closure U) :=
  (show MapsTo (fun x => x + v) U U from fun x hx => hUinv x hx v hv).closure
    (continuous_id.add_const v)

theorem translation_invariant_on_closure {F : Type*} [TopologicalSpace F] [T2Space F]
    {U : Set E} (L : Submodule ℝ E)
    (hUinv : ∀ x ∈ U, ∀ v ∈ L, x + v ∈ U)
    {f : E → F} (hf : ContinuousOn f (closure U))
    (hfinv : ∀ x ∈ U, ∀ v ∈ L, f (x + v) = f x) :
    ∀ x ∈ closure U, ∀ v ∈ L, f (x + v) = f x := by
  intro x hx v hv
  have heq : EqOn (fun y => f (y + v)) f U := fun y hy => hfinv y hy v hv
  exact heq.of_subset_closure
    (hf.comp (continuous_id.add_const v).continuousOn (translation_maps_closure L hUinv hv))
    hf subset_closure Subset.rfl hx

theorem fderiv_translation_invariant_on {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} (hU : IsOpen U) (L : Submodule ℝ E)
    (hUinv : ∀ x ∈ U, ∀ v ∈ L, x + v ∈ U) {f : E → F}
    (hf : ∀ x ∈ U, DifferentiableAt ℝ f x)
    (hfinv : ∀ x ∈ U, ∀ v ∈ L, f (x + v) = f x) :
    ∀ x ∈ U, ∀ v ∈ L, fderiv ℝ f (x + v) = fderiv ℝ f x := by
  intro x hx v hv
  have hd := (hf (x + v) (hUinv x hx v hv)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).add_const v)
  have hd' : HasFDerivAt (fun y => f (y + v)) (fderiv ℝ f (x + v)) x := by
    simpa only [ContinuousLinearMap.comp_id, Function.comp_def, id_eq] using hd
  have heq : (fun y => f (y + v)) =ᶠ[𝓝 x] f :=
    Filter.eventually_of_mem (hU.mem_nhds hx) (fun y hy => hfinv y hy v hv)
  exact hd'.fderiv.symm.trans heq.fderiv_eq

namespace ClosureC2Jet

variable {u : E → ℝ} {U : Set E}

theorem translation_invariant (J : ClosureC2Jet u U) (hU : IsOpen U)
    (hu : ContDiffOn ℝ 2 u U) (L : Submodule ℝ E)
    (hUinv : ∀ x ∈ U, ∀ v ∈ L, x + v ∈ U)
    (huinv : ∀ x ∈ U, ∀ v ∈ L, u (x + v) = u x) :
    ∀ x ∈ closure U, ∀ v ∈ L,
      u (x + v) = u x ∧ J.derivative (x + v) = J.derivative x ∧
        J.hessian (x + v) = J.hessian x := by
  have huAt (x : E) (hx : x ∈ U) : ContDiffAt ℝ 2 u x :=
    hu.contDiffAt (hU.mem_nhds hx)
  have hD := fderiv_translation_invariant_on hU L hUinv
    (fun x hx => (huAt x hx).differentiableAt (by norm_num)) huinv
  have hH := fderiv_translation_invariant_on hU L hUinv
    (fun x hx => ((huAt x hx).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)) hD
  have hDJ : ∀ x ∈ U, ∀ v ∈ L, J.derivative (x + v) = J.derivative x := by
    intro x hx v hv
    rw [J.derivative_eq (hUinv x hx v hv), J.derivative_eq hx, hD x hx v hv]
  have hHJ : ∀ x ∈ U, ∀ v ∈ L, J.hessian (x + v) = J.hessian x := by
    intro x hx v hv
    rw [J.hessian_eq (hUinv x hx v hv), J.hessian_eq hx, hH x hx v hv]
  intro x hx v hv
  exact ⟨translation_invariant_on_closure L hUinv J.continuous_value huinv x hx v hv,
    translation_invariant_on_closure L hUinv J.continuous_derivative hDJ x hx v hv,
    translation_invariant_on_closure L hUinv J.continuous_hessian hHJ x hx v hv⟩

end ClosureC2Jet
end CHS.Calculus
