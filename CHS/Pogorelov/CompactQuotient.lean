import CHS.Calculus.TranslationJets
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic.Abel

/-!
# Compact representatives of a real-translation quotient

Compactness is assumed for the actual quotient image of the closure.  A
continuous linear section gives a compact representative set inside the
closure.  The jet invariance proof then supplies the hypotheses used in
the Pogorelov maximum construction.
-/

set_option autoImplicit false
noncomputable section

open Set
open scoped ContDiff

namespace CHS.Pogorelov

open CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

theorem compact_representatives_of_compact_real_quotient
    (L : Submodule ℝ E) {U : Set E}
    (hUinv : ∀ x ∈ U, ∀ v ∈ L, x + v ∈ U)
    (hquot : IsCompact ((Submodule.Quotient.mk : E → E ⧸ L) '' closure U)) :
    ∃ C : Set E, IsCompact C ∧ C ⊆ closure U ∧
      ∀ x ∈ closure U, ∃ y ∈ C, y - x ∈ L := by
  letI : IsClosed (L : Set E) := L.closed_of_finiteDimensional
  let s : E ⧸ L →L[ℝ] E := Lᗮ.subtypeL.comp
    ((L.quotientEquivOfIsCompl Lᗮ L.isCompl_orthogonal).toLinearMap.toContinuousLinearMap)
  have hs (q : E ⧸ L) : (Submodule.Quotient.mk (s q) : E ⧸ L) = q := by
    exact Submodule.mk_quotientEquivOfIsCompl_apply L.isCompl_orthogonal q
  let q : E → E ⧸ L := Submodule.Quotient.mk
  let C : Set E := s '' (q '' closure U)
  have hdiff (x : E) : s (q x) - x ∈ L :=
    (Submodule.Quotient.eq L).mp (hs (q x))
  have hmem (x : E) (hx : x ∈ closure U) : s (q x) ∈ closure U := by
    have ht := translation_maps_closure L hUinv (hdiff x) hx
    change x + (s (q x) - x) ∈ closure U at ht
    have heq : x + (s (q x) - x) = s (q x) := by abel
    rwa [heq] at ht
  refine ⟨C, hquot.image s.continuous, ?_, ?_⟩
  · rintro y ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact hmem x hx
  · intro x hx
    exact ⟨s (q x), ⟨q x, ⟨x, hx, rfl⟩, rfl⟩, hdiff x⟩

theorem compact_jet_representatives_of_compact_real_quotient
    (L : Submodule ℝ E) {U : Set E} {u : E → ℝ}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    (hUinv : ∀ x ∈ U, ∀ v ∈ L, x + v ∈ U)
    (huinv : ∀ x ∈ U, ∀ v ∈ L, u (x + v) = u x)
    (hquot : IsCompact ((Submodule.Quotient.mk : E → E ⧸ L) '' closure U)) :
    ∃ C : Set E, IsCompact C ∧ C ⊆ closure U ∧
      ∀ x ∈ closure U, ∃ y ∈ C,
        u x = u y ∧ J.derivative x = J.derivative y ∧ J.hessian x = J.hessian y := by
  obtain ⟨C, hC, hCU, hrep⟩ :=
    compact_representatives_of_compact_real_quotient L hUinv hquot
  refine ⟨C, hC, hCU, ?_⟩
  intro x hx
  obtain ⟨y, hy, hv⟩ := hrep x hx
  have hJ := J.translation_invariant hU hu L hUinv huinv x hx (y - x) hv
  have heq : x + (y - x) = y := by abel
  rw [heq] at hJ
  exact ⟨y, hy, hJ.1.symm, hJ.2.1.symm, hJ.2.2.symm⟩

end CHS.Pogorelov
