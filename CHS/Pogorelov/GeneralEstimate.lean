import CHS.Pogorelov.LinfEstimate
import CHS.Analysis.BlockCoordinates

/-!
# Manuscript Theorem 1.1: positive definite branch in the fixed block coordinates

`realDirections` and `imagDirections` are the baseline directions, ordered
as all real coordinates followed by all imaginary coordinates.  The
quotient alternative is compactness of the actual quotient image of the
closure, with invariance required only on the domain.

The independent manuscript statement has no explicit positive-branch
hypothesis.  Its sign reduction is proved separately in `GeneralTheorem`.
-/

set_option autoImplicit false
noncomputable section

open Set Matrix
open scoped ContDiff ComplexOrder

namespace CHS

open Calculus Analysis Pogorelov

variable {n : ℕ}
local notation "E" => DeGiorgi.AmbientSpace (n + n)

def PogorelovCompactGeometry (U : Set E) (u : E → ℝ) : Prop :=
  Bornology.IsBounded U ∨
    ∃ L : Submodule ℝ E,
      (∀ x ∈ U, ∀ v ∈ L, x + v ∈ U) ∧
      (∀ x ∈ U, ∀ v ∈ L, u (x + v) = u x) ∧
      IsCompact ((Submodule.Quotient.mk : E → E ⧸ L) '' closure U)

theorem PogorelovCompactGeometry.compact_jet_representatives
    {U : Set E} {u : E → ℝ} (hgeometry : PogorelovCompactGeometry U u)
    (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U) :
    ∃ C : Set E, IsCompact C ∧ C ⊆ closure U ∧
      ∀ x ∈ closure U, ∃ y ∈ C,
        u x = u y ∧ J.derivative x = J.derivative y ∧ J.hessian x = J.hessian y := by
  rcases hgeometry with hbounded | ⟨L, hUinv, huinv, hquot⟩
  · exact ⟨closure U, hbounded.isCompact_closure, Subset.rfl,
      fun x hx => ⟨x, hx, rfl, rfl, rfl⟩⟩
  · exact compact_jet_representatives_of_compact_real_quotient L hU hu J hUinv huinv hquot

/-- The positive definite branch, with actual Hessians and the exact
constant and exponent.  This is not the independent sign-free theorem. -/
theorem general_pogorelov_positive
    (hn : 2 ≤ n) {κ : ℝ} (hκ : 1 ≤ κ) {U : Set E} (hU : IsOpen U) {u : E → ℝ}
    (hu : ContDiffOn ℝ 4 u U) (huBoundary : C2OnClosure u U)
    (hdet : ∀ x ∈ U, (complexHessian realDirections imagDirections u x).det = 1)
    (hpos : ∀ x ∈ U, (complexHessian realDirections imagDirections u x).PosDef)
    (hbd : ∀ x ∈ frontier U, u x = 0)
    (hmat : ∀ x ∈ U, (κ • complexHessian realDirections imagDirections u x -
      pureHessian realDirections imagDirections u x *
        ((complexHessian realDirections imagDirections u x).map star)⁻¹ *
          (pureHessian realDirections imagDirections u x).map star).PosSemidef)
    (hgeometry : PogorelovCompactGeometry U u) :
    weightedHessianSupNormOn realDirections imagDirections u U κ ≤
      32 * (n : ℝ) * beta n κ * (1 + Real.sqrt κ) * Real.exp (1 / 8) *
        (1 + gradientSupNormOn realDirections imagDirections u U ^ 2) *
          scalarSupNormOn U u ^ (beta n κ - 1) := by
  rcases hgeometry with hbounded | ⟨L, hUinv, huinv, hquot⟩
  · exact positive_branch_supremum_estimate_of_compact_closure hn hU
      hbounded.isCompact_closure hu huBoundary realDirections imagDirections
      hdet hpos hκ hmat hbd
  · obtain ⟨C, hC, hCU, hrep⟩ :=
      compact_jet_representatives_of_compact_real_quotient L hU
        (hu.of_le (by norm_num)) huBoundary.jet hUinv huinv hquot
    exact positive_branch_supremum_estimate_of_compact_jet_representatives hn hU hC hCU hu
      huBoundary.jet realDirections imagDirections hdet hpos hκ hmat hbd hrep

/-- The positive definite branch with the manuscript's actual essential
supremum seminorms and its precise block coordinate normalization. -/
theorem general_pogorelov_positive_linf
    (hn : 2 ≤ n) {κ : ℝ} (hκ : 1 ≤ κ) {U : Set E} (hU : IsOpen U) {u : E → ℝ}
    (hu : ContDiffOn ℝ 4 u U) (huBoundary : C2OnClosure u U)
    (hdet : ∀ x ∈ U, (complexHessian realDirections imagDirections u x).det = 1)
    (hpos : ∀ x ∈ U, (complexHessian realDirections imagDirections u x).PosDef)
    (hbd : ∀ x ∈ frontier U, u x = 0)
    (hmat : ∀ x ∈ U, (κ • complexHessian realDirections imagDirections u x -
      pureHessian realDirections imagDirections u x *
        ((complexHessian realDirections imagDirections u x).map star)⁻¹ *
          (pureHessian realDirections imagDirections u x).map star).PosSemidef)
    (hgeometry : PogorelovCompactGeometry U u) :
    entryLinfNormOn MeasureTheory.volume U
        (fun x => ((-u x) ^ beta n κ) • euclideanHessian u x) ≤
      32 * (n : ℝ) * beta n κ * (1 + Real.sqrt κ) * Real.exp (1 / 8) *
        (1 + gradientLinfNormOn MeasureTheory.volume realDirections imagDirections u U ^ 2) *
          scalarLinfNormOn MeasureTheory.volume U u ^ (beta n κ - 1) := by
  obtain ⟨C, hC, hCU, hrep⟩ := hgeometry.compact_jet_representatives hU
    (hu.of_le (by norm_num)) huBoundary.jet
  have h := positive_branch_linf_estimate_of_compact_jet_representatives
    (μ := MeasureTheory.volume) hn hU hC hCU hu
      huBoundary.jet realDirections imagDirections hdet hpos hκ hmat hbd hrep
  unfold weightedHessianLinfNormOn at h
  rwa [weighted_realBlockHessian_linf_eq_euclidean] at h

end CHS
