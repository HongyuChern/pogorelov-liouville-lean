import CHS.Pogorelov.GeneralEstimate

/-!
# Theorem 1.2 as the exact κ = 1 specialization

Real convexity is a condition on the actual real Hessian.  Lemma 2.2 and
the determinant equation provide positive definiteness and the Schur
bound.  The kernel condition in the cylindrical alternative is retained
in the public manuscript-facing statement.
-/

set_option autoImplicit false
noncomputable section

open Set Matrix
open scoped ContDiff ComplexOrder

namespace CHS

open Calculus Analysis Pogorelov

variable {n : ℕ}
local notation "E" => DeGiorgi.AmbientSpace (n + n)

def ConvexPogorelovCompactGeometry (U : Set E) (u : E → ℝ) : Prop :=
  Bornology.IsBounded U ∨
    ∃ L : Submodule ℝ E,
      (∀ x ∈ U, ∀ v ∈ L, realHessian u x v = 0) ∧
      (∀ x ∈ U, ∀ v ∈ L, x + v ∈ U) ∧
      (∀ x ∈ U, ∀ v ∈ L, u (x + v) = u x) ∧
      IsCompact ((Submodule.Quotient.mk : E → E ⧸ L) '' closure U)

theorem ConvexPogorelovCompactGeometry.toPogorelov {U : Set E} {u : E → ℝ}
    (h : ConvexPogorelovCompactGeometry U u) : PogorelovCompactGeometry U u := by
  rcases h with hbounded | ⟨L, _, hUinv, huinv, hquot⟩
  · exact Or.inl hbounded
  · exact Or.inr ⟨L, hUinv, huinv, hquot⟩

theorem convex_pogorelov
    (hn : 2 ≤ n) {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) {u : E → ℝ}
    (hu : ContDiffOn ℝ 4 u U) (huBoundary : C2OnClosure u U)
    (hdet : ∀ x ∈ U, (complexHessian realDirections imagDirections u x).det = 1)
    (hR : ∀ x ∈ U, (realBlockHessian realDirections imagDirections u x).PosSemidef)
    (hbd : ∀ x ∈ frontier U, u x = 0)
    (hgeometry : ConvexPogorelovCompactGeometry U u) :
    entrySupNormOn U (fun x => ((-u x) ^ (4 * (n : ℝ))) •
      realBlockHessian realDirections imagDirections u x) ≤
      256 * (n : ℝ) ^ 2 * Real.exp (1 / 8) *
        (1 + gradientSupNormOn realDirections imagDirections u U ^ 2) *
          scalarSupNormOn U u ^ (4 * (n : ℝ) - 1) := by
  have hu₂ (x : E) (hx : x ∈ U) : ContDiffAt ℝ 2 u x :=
    (hu.contDiffAt (hU.mem_nhds hx)).of_le (by norm_num)
  have hpos (x : E) (hx : x ∈ U) :
      (complexHessian realDirections imagDirections u x).PosDef :=
    complexHessian_posDef_of_realBlockHessian (hu₂ x hx) realDirections imagDirections
      (hR x hx) (hdet x hx)
  have hmat (x : E) (hx : x ∈ U) :
      ((1 : ℝ) • complexHessian realDirections imagDirections u x -
        pureHessian realDirections imagDirections u x *
          ((complexHessian realDirections imagDirections u x).map star)⁻¹ *
            (pureHessian realDirections imagDirections u x).map star).PosSemidef := by
    rw [one_smul]
    change (schurHessian realDirections imagDirections u x).PosSemidef
    have heq := realBlockHessian_posSemidef_equivalences (hu₂ x hx)
      realDirections imagDirections (hpos x hx)
    exact heq.2.mp (heq.1.mp (hR x hx))
  have hgeom : PogorelovCompactGeometry U u := by
    rcases hgeometry with hbounded | ⟨L, _, hUinv, huinv, hquot⟩
    · exact Or.inl hbounded
    · exact Or.inr ⟨L, hUinv, huinv, hquot⟩
  have h := general_pogorelov_positive hn (by norm_num : (1 : ℝ) ≤ 1) hU
    hu huBoundary hdet hpos hbd hmat hgeom
  rw [convex_coefficient] at h
  simpa only [weightedHessianSupNormOn, beta_one] using h

/-- Theorem 1.2 in the manuscript's entrywise essential supremum norm.
Both the bounded and the invariant compact-quotient alternatives are kept. -/
theorem convex_pogorelov_linf
    (hn : 2 ≤ n) {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) {u : E → ℝ}
    (hu : ContDiffOn ℝ 4 u U) (huBoundary : C2OnClosure u U)
    (hdet : ∀ x ∈ U, (complexHessian realDirections imagDirections u x).det = 1)
    (hR : ∀ x ∈ U, (realBlockHessian realDirections imagDirections u x).PosSemidef)
    (hbd : ∀ x ∈ frontier U, u x = 0)
    (hgeometry : ConvexPogorelovCompactGeometry U u) :
    entryLinfNormOn MeasureTheory.volume U (fun x => ((-u x) ^ (4 * (n : ℝ))) •
      euclideanHessian u x) ≤
      256 * (n : ℝ) ^ 2 * Real.exp (1 / 8) *
        (1 + gradientLinfNormOn MeasureTheory.volume realDirections imagDirections u U ^ 2) *
          scalarLinfNormOn MeasureTheory.volume U u ^ (4 * (n : ℝ) - 1) := by
  obtain ⟨C, hC, hCU, hrep⟩ := hgeometry.toPogorelov.compact_jet_representatives
    hU (hu.of_le (by norm_num)) huBoundary.jet
  have hβ : 0 ≤ beta n 1 := by rw [beta_one]; positivity
  obtain ⟨hvalue, hgradient, hH⟩ := supremum_norms_eq_linf_of_compact_jet_representatives
    (μ := MeasureTheory.volume) hU hC hCU (hu.of_le (by norm_num)) huBoundary.jet
      realDirections imagDirections hβ hrep
  simp only [weightedHessianSupNormOn, weightedHessianLinfNormOn, beta_one] at hH
  rw [weighted_realBlockHessian_linf_eq_euclidean] at hH
  have h := convex_pogorelov hn hU hconv hu huBoundary hdet hR hbd hgeometry
  rwa [hvalue, hgradient, hH] at h

end CHS
