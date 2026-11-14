import CHS.Pogorelov.SignClassification

/-!
# The independent manuscript Theorem 1.1

This statement has no positive-definiteness or negativity hypothesis.
On a connected domain the strict projected extremum selects the branch.
The negative branch has κ = 1, determinant one after negation, and zero
Schur complement.  Exact norm identities then transfer the positive
estimate without changing the exponent or constant.
-/

set_option autoImplicit false
noncomputable section

open Set Matrix
open scoped ContDiff ComplexOrder

namespace CHS

open Calculus Analysis Pogorelov

variable {n : ℕ}
local notation "E₀" => DeGiorgi.AmbientSpace (n + n)

/-- Manuscript Theorem 1.1, with its independent sign-free hypotheses,
actual derivatives, C² boundary jets, both geometric alternatives and
the exact entrywise essential supremum seminorm and constant. -/
theorem general_pogorelov_linf
    (hn : 2 ≤ n) {κ : ℝ} (hκ : 1 ≤ κ) {U : Set E₀}
    (hU : IsOpen U) (hconn : IsConnected U) {u : E₀ → ℝ}
    (hu : ContDiffOn ℝ 4 u U) (huBoundary : C2OnClosure u U)
    (hdet : ∀ x ∈ U, (complexHessian realDirections imagDirections u x).det = 1)
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
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨x₀, hx₀, hu₀⟩ := exists_value_ne_zero_of_complex_det_one hU hconn.nonempty
    (hu.of_le (by norm_num)) realDirections imagDirections hdet
  rcases lt_or_gt_of_ne hu₀ with hnegative | hpositive
  · have hA := pogorelov_positive_branch_of_negative_value hn hU hconn.isPreconnected hu
      huBoundary.jet.continuous_value hdet hbd hgeometry hx₀ hnegative
    exact general_pogorelov_positive_linf hn hκ hU hu huBoundary hdet hA hbd hmat hgeometry
  · obtain ⟨hk, hA, hdetw, hM⟩ := pogorelov_negative_branch_of_positive_value hn hκ hU
      hconn.isPreconnected hu huBoundary.jet.continuous_value hdet hbd hmat hgeometry hx₀ hpositive
    subst κ
    have hwbd : ∀ x ∈ frontier U, (-u x) = 0 := fun x hx => by rw [hbd x hx, neg_zero]
    have hwmat : ∀ x ∈ U,
        ((1 : ℝ) • complexHessian realDirections imagDirections (fun y => -u y) x -
          pureHessian realDirections imagDirections (fun y => -u y) x *
            ((complexHessian realDirections imagDirections (fun y => -u y) x).map star)⁻¹ *
              (pureHessian realDirections imagDirections (fun y => -u y) x).map star).PosSemidef := by
      intro x hx
      rw [one_smul]
      change (schurHessian realDirections imagDirections (fun y => -u y) x).PosSemidef
      rw [hM x hx]
      exact Matrix.PosSemidef.zero
    have h := general_pogorelov_positive_linf hn (by norm_num : (1 : ℝ) ≤ 1) hU
      (u := fun y => -u y) hu.neg huBoundary.neg hdetw hA hwbd hwmat hgeometry.neg
    rwa [weighted_euclideanHessian_linf_neg_at_one, gradientLinfNormOn_neg,
      scalarLinfNormOn_neg] at h

end CHS
