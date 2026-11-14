import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic.NormNum

/-!
# C² regularity up to the boundary through actual interior derivatives

For a general open set, the PDE notation `C²(closure U)` means that the
interior derivatives through order two extend continuously to the closure.
The ambient function may have arbitrary values outside the closure.  Its
total Fréchet derivatives at boundary points are therefore not used.

`ClosureC2Jet` records precisely those extensions, with equality to the
actual first and second Fréchet derivatives on `U`.  They are unique on the
closure.  No smooth extension across the boundary is required.
-/

set_option autoImplicit false
noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure ClosureC2Jet (u : E → ℝ) (U : Set E) where
  derivative : E → E →L[ℝ] ℝ
  hessian : E → E →L[ℝ] E →L[ℝ] ℝ
  continuous_value : ContinuousOn u (closure U)
  continuous_derivative : ContinuousOn derivative (closure U)
  continuous_hessian : ContinuousOn hessian (closure U)
  derivative_eq : EqOn derivative (fderiv ℝ u) U
  hessian_eq : EqOn hessian (fderiv ℝ (fderiv ℝ u)) U

/-- The boundary regularity convention used for the manuscript's
`C⁴(U) ∩ C²(closure U)` hypotheses. -/
def C2OnClosure (u : E → ℝ) (U : Set E) : Prop :=
  ContDiffOn ℝ 2 u U ∧ Nonempty (ClosureC2Jet u U)

def C2OnClosure.jet {u : E → ℝ} {U : Set E} (hu : C2OnClosure u U) :
    ClosureC2Jet u U := Classical.choice hu.2

theorem ClosureC2Jet.derivative_unique {u : E → ℝ} {U : Set E}
    (J K : ClosureC2Jet u U) : EqOn J.derivative K.derivative (closure U) := by
  have h : EqOn J.derivative K.derivative U :=
    fun x hx => (J.derivative_eq hx).trans (K.derivative_eq hx).symm
  exact h.of_subset_closure J.continuous_derivative K.continuous_derivative
    subset_closure Subset.rfl

theorem ClosureC2Jet.hessian_unique {u : E → ℝ} {U : Set E}
    (J K : ClosureC2Jet u U) : EqOn J.hessian K.hessian (closure U) := by
  have h : EqOn J.hessian K.hessian U :=
    fun x hx => (J.hessian_eq hx).trans (K.hessian_eq hx).symm
  exact h.of_subset_closure J.continuous_hessian K.continuous_hessian
    subset_closure Subset.rfl

/-- A C² function on an open neighborhood supplies the boundary jets.
This is a sufficient condition, not the definition of boundary regularity. -/
theorem c2OnClosure_of_neighborhood {u : E → ℝ} {U V : Set E}
    (hV : IsOpen V) (hUV : closure U ⊆ V) (hu : ContDiffOn ℝ 2 u V) :
    C2OnClosure u U := by
  have hd : ContDiffOn ℝ 1 (fderiv ℝ u) V :=
    hu.fderiv_of_isOpen hV (by norm_num)
  refine ⟨hu.mono (subset_closure.trans hUV), ⟨{
    derivative := fderiv ℝ u
    hessian := fderiv ℝ (fderiv ℝ u)
    continuous_value := hu.continuousOn.mono hUV
    continuous_derivative := hd.continuousOn.mono hUV
    continuous_hessian := (hd.continuousOn_fderiv_of_isOpen hV (by norm_num)).mono hUV
    derivative_eq := fun _ _ => rfl
    hessian_eq := fun _ _ => rfl }⟩⟩

/-- Mathlib's within-set C² hypothesis also supplies the boundary jets
when the closure has unique derivatives.  This assumption is confined to
this conversion lemma; it is absent from `C2OnClosure` itself. -/
theorem c2OnClosure_of_contDiffOn_closure {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (huniq : UniqueDiffOn ℝ (closure U))
    (hu : ContDiffOn ℝ 2 u (closure U)) : C2OnClosure u U := by
  let D := fderivWithin ℝ u (closure U)
  let H := fderivWithin ℝ D (closure U)
  have hD : ContDiffOn ℝ 1 D (closure U) :=
    hu.fderivWithin huniq (by norm_num)
  have hDeq : EqOn D (fderiv ℝ u) U := by
    intro x hx
    exact fderivWithin_of_mem_nhds (mem_of_superset (hU.mem_nhds hx) subset_closure)
  have hHeq : EqOn H (fderiv ℝ (fderiv ℝ u)) U := by
    intro x hx
    change fderivWithin ℝ D (closure U) x = _
    rw [fderivWithin_of_mem_nhds (mem_of_superset (hU.mem_nhds hx) subset_closure)]
    have heq : D =ᶠ[𝓝 x] fderiv ℝ u :=
      Filter.eventually_of_mem (hU.mem_nhds hx) (fun _ hy => hDeq hy)
    exact heq.fderiv_eq
  exact ⟨hu.mono subset_closure, ⟨{
    derivative := D
    hessian := H
    continuous_value := hu.continuousOn
    continuous_derivative := hD.continuousOn
    continuous_hessian := hD.continuousOn_fderivWithin huniq (by norm_num)
    derivative_eq := hDeq
    hessian_eq := hHeq }⟩⟩

end CHS.Calculus
