import CHS.Analysis.GlobalEllipticity
import CHS.Analysis.UniformLocalEllipticity

/-!
# Compact coefficient families fixed by an actual Hessian bound

The family depends only on n and the entrywise real Hessian bound M.
Every member is positive definite because it is semidefinite with
determinant one. Inverting and taking the exact real linearization
therefore gives one normalization for every local solution in this class.
-/

set_option autoImplicit false
noncomputable section

open DeGiorgi Set Matrix Metric Filter
open scoped BigOperators ComplexOrder ContDiff Matrix.Norms.Elementwise Topology

namespace CHS.Analysis

open CHS.Calculus CHS.Algebra CHS.Sections

variable {n : ℕ}
local notation "E" => AmbientSpace (n + n)
local notation "W" => Matrix (Fin n) (Fin n) ℂ
local notation "V" => Matrix (Fin (n + n)) (Fin (n + n)) ℝ

def complexDetOneFamily (n : ℕ) (M : ℝ) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  closedBall 0 (max 1 ((n : ℝ) * M / 2)) ∩ {A | A.PosSemidef} ∩ {A | A.det = 1}

theorem complexDetOneFamily_compact (M : ℝ) : IsCompact (complexDetOneFamily n M) :=
  ((isCompact_closedBall 0 _).inter_right isClosed_complex_posSemidef).inter_right
    (isClosed_eq continuous_id.matrix_det continuous_const)

theorem complexDetOneFamily_posDef {M : ℝ} {A : W} (hA : A ∈ complexDetOneFamily n M) : A.PosDef :=
  hA.1.2.posDef_iff_det_ne_zero.mpr (by rw [hA.2]; exact one_ne_zero)

theorem complexDetOneFamily_nonempty (M : ℝ) : (complexDetOneFamily n M).Nonempty := by
  refine ⟨1, ⟨⟨?_, Matrix.PosSemidef.one⟩, Matrix.det_one⟩⟩
  rw [mem_closedBall, dist_zero_right, Matrix.norm_le_iff (zero_le_one.trans (le_max_left _ _))]
  intro i j
  by_cases h : i = j
  · simp only [Matrix.one_apply, if_pos h, norm_one]
    exact le_max_left _ _
  · simp only [Matrix.one_apply, if_neg h, norm_zero]
    exact zero_le_one.trans (le_max_left _ _)

def inverseComplexDetOneFamily (n : ℕ) (M : ℝ) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  (fun A => A⁻¹) '' complexDetOneFamily n M

theorem inverseComplexDetOneFamily_compact (M : ℝ) : IsCompact (inverseComplexDetOneFamily n M) := by
  apply (complexDetOneFamily_compact M).image_of_continuousOn
  intro A hA
  apply (continuousAt_matrix_inv A _).continuousWithinAt
  simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀
    (by rw [hA.2]; exact one_ne_zero : A.det ≠ 0)

theorem inverseComplexDetOneFamily_posDef {M : ℝ} {A : W}
    (hA : A ∈ inverseComplexDetOneFamily n M) : A.PosDef := by
  obtain ⟨B, hB, rfl⟩ := hA
  exact (complexDetOneFamily_posDef hB).inv

def realLinearizedWeight (A : W) : V :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (realLinearizationMatrix A)

theorem continuous_realLinearizedWeight : Continuous (realLinearizedWeight (n := n)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact ((continuous_apply (finSumFinEquiv.symm j)).comp
    ((continuous_apply (finSumFinEquiv.symm i)).comp continuous_realLinearizationMatrix))

theorem realLinearizedWeight_posDef {A : W} (hA : A.PosDef) :
    (realLinearizedWeight A).PosDef :=
  (realLinearizationMatrix_posDef hA).submatrix finSumFinEquiv.symm.injective

theorem complexHessian_mem_complexDetOneFamily {M : ℝ} {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x)
    (hA : (complexHessian realDirections imagDirections u x).PosDef)
    (hdet : (complexHessian realDirections imagDirections u x).det = 1)
    (hM : ∀ i j, |euclideanHessian u x i j| ≤ M) :
    complexHessian realDirections imagDirections u x ∈ complexDetOneFamily n M := by
  refine ⟨⟨?_, hA.posSemidef⟩, hdet⟩
  rw [mem_closedBall, dist_zero_right, Matrix.norm_le_iff (zero_le_one.trans (le_max_left _ _))]
  intro i j
  exact (norm_entry_le_trace_re hA.posSemidef i j).trans
    ((complexHessian_trace_re_le_of_euclidean_entry_bound hu hM).trans (le_max_right _ _))

theorem exists_uniform_local_complex_coefficients [NeZero (n + n)] (M : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∃ Λ : ℝ, 1 ≤ Λ ∧
      ∀ U : Set E, IsOpen U → ∀ u : E → ℝ, ContDiffOn ℝ 4 u U →
      (∀ x ∈ U, (complexHessian realDirections imagDirections u x).det = 1) →
      (∀ x ∈ U, (complexHessian realDirections imagDirections u x).PosDef) →
      (∀ x ∈ U, ∀ i j, |euclideanHessian u x i j| ≤ M) →
      ∃ B : NormalizedEllipticCoeff (n + n) U, B.1.Λ = Λ ∧
        ∀ x ∈ U, B.1.a x = c⁻¹ • complexLinearizedCoeff u x := by
  let S := realLinearizedWeight '' inverseComplexDetOneFamily n M
  have hS : IsCompact S :=
    (inverseComplexDetOneFamily_compact M).image continuous_realLinearizedWeight
  have hSne : S.Nonempty := ((complexDetOneFamily_nonempty M).image _).image _
  have hSpos : ∀ A ∈ S, A.PosDef := by
    rintro _ ⟨A, hA, rfl⟩
    exact realLinearizedWeight_posDef (inverseComplexDetOneFamily_posDef hA)
  obtain ⟨c, hc, Λ, hΛ, hnormalize⟩ := uniform_local_normalization_of_compact_family hS hSne hSpos
  refine ⟨c, hc, Λ, hΛ, ?_⟩
  intro U hU u hu hdet hA hM
  apply hnormalize U hU.measurableSet (complexLinearizedCoeff u)
  · intro x hx
    apply continuousWithinAt_pi.mpr
    intro i
    apply continuousWithinAt_pi.mpr
    intro j
    apply (complexLinearizedCoeff_contDiffAt (hu.contDiffAt (hU.mem_nhds hx)) ?_ i j).continuousAt.continuousWithinAt
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hdet y hy
  · intro x hx
    exact mem_image_of_mem _ (mem_image_of_mem _
      (complexHessian_mem_complexDetOneFamily
        ((hu.contDiffAt (hU.mem_nhds hx)).of_le (by norm_num)) (hA x hx) (hdet x hx) (hM x hx)))

end CHS.Analysis
