import CHS.Calculus.TranslationJets
import CHS.Calculus.BasisHessian
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Real translation directions lie in the actual Hessian kernel

Only invariance on the open domain is assumed.  First differentiate along
an invariant affine line; then apply the same argument to the actual first
derivative, whose translation invariance follows by the chain rule.
-/

set_option autoImplicit false
noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace CHS.Calculus

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem fderiv_vanishes_on_translation_directions (L : Submodule ℝ E)
    {f : E → F} {x : E} (hf : DifferentiableAt ℝ f x)
    (hinv : ∀ v ∈ L, f (x + v) = f x) {v : E} (hv : v ∈ L) :
    fderiv ℝ f x v = 0 := by
  let line := fun t : ℝ => x + t • v
  have hline : HasDerivAt line v 0 := by
    simpa [line] using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have heq : f ∘ line = fun _ : ℝ => f x := by
    funext t
    exact hinv (t • v) (L.smul_mem t hv)
  have hd := hf.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp [line])
  rw [heq] at hd
  exact hd.unique (hasDerivAt_const (0 : ℝ) (f x))

theorem translation_subspace_le_realHessian_ker
    {U : Set E} (hU : IsOpen U) (L : Submodule ℝ E)
    (hUinv : ∀ x ∈ U, ∀ v ∈ L, x + v ∈ U) {u : E → ℝ}
    (hu : ContDiffOn ℝ 2 u U)
    (huinv : ∀ x ∈ U, ∀ v ∈ L, u (x + v) = u x)
    {x : E} (hx : x ∈ U) : L ≤ (realHessian u x).ker := by
  have hD := fderiv_translation_invariant_on hU L hUinv
    (fun y hy => (hu.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num)) huinv
  have hdiff : DifferentiableAt ℝ (fderiv ℝ u) x :=
    ((hu.contDiffAt (hU.mem_nhds hx)).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)
  intro v hv
  exact fderiv_vanishes_on_translation_directions L hdiff (hD x hx) hv

end CHS.Calculus
