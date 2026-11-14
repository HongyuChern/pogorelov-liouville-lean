import CHS.Analysis.CompactEllipticity
import CHS.Sections.GlobalHessian
import CHS.Algebra.PositiveCone

/-!
# Global ellipticity of the actual complex Monge--Ampère linearization

Proposition 3.2 bounds the complex Hessian in a compact set of positive
semidefinite determinant-one matrices.  Every matrix in that compact set
is positive definite.  Its inverse real linearization therefore has one
uniform ellipticity normalization on the whole space, valid on every ball.
-/

set_option autoImplicit false
noncomputable section

open Set Matrix DeGiorgi
open scoped BigOperators ComplexOrder Matrix.Norms.Elementwise ContDiff

namespace CHS.Algebra

theorem isClosed_complex_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι] :
    IsClosed {A : Matrix ι ι ℂ | A.PosSemidef} := by
  have heq : {A : Matrix ι ι ℂ | A.PosSemidef} =
      {A | A.IsHermitian} ∩ ⋂ v : ι → ℂ, {A | 0 ≤ realQuadratic A v} := by
    ext A
    simp only [mem_setOf_eq, mem_inter_iff, mem_iInter]
    constructor
    · intro h
      exact ⟨h.isHermitian, h.re_dotProduct_nonneg⟩
    · rintro ⟨hA, hq⟩
      exact Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hA
        (fun v => Complex.nonneg_iff.mpr
          ⟨hq v, (hA.im_star_dotProduct_mulVec_self v).symm⟩)
  rw [heq]
  apply IsClosed.inter
  · exact isClosed_eq continuous_id.matrix_conjTranspose continuous_id
  · apply isClosed_iInter
    intro v
    apply isClosed_le continuous_const
    unfold realQuadratic dotProduct Matrix.mulVec
    fun_prop

end CHS.Algebra

namespace CHS.Analysis

open CHS.Calculus CHS.Algebra CHS.Sections

variable {n : ℕ}
local notation "E" => AmbientSpace (n + n)

theorem continuous_realLinearizationMatrix :
    Continuous (realLinearizationMatrix (ι := Fin n)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  rcases i with i | i <;> rcases j with j | j <;>
    simp only [realLinearizationMatrix, Matrix.smul_apply, smul_eq_mul,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.map_apply, Matrix.transpose_apply, Matrix.neg_apply] <;> fun_prop

theorem global_complexLinearizedCoeff_of_hessian_bound [NeZero (n + n)]
    {u : E → ℝ} (hu : ContDiff ℝ 4 u)
    (hdet : ∀ x, (complexHessian realDirections imagDirections u x).det = 1)
    (hA : ∀ x, (complexHessian realDirections imagDirections u x).PosDef)
    {M : ℝ} (hM : ∀ x, ∀ i j, |euclideanHessian u x i j| ≤ M) :
    ∃ c : ℝ, 0 < c ∧ ∃ B : NormalizedEllipticCoeff (n + n) univ,
      ∀ x, B.1.a x = c⁻¹ • complexLinearizedCoeff u x := by
  let R : ℝ := max 0 ((n : ℝ) * M / 2)
  let S : Set (Matrix (Fin n) (Fin n) ℂ) :=
    Metric.closedBall 0 R ∩ {A | A.PosSemidef} ∩ {A | A.det = 1}
  have hS : IsCompact S :=
    ((isCompact_closedBall 0 R).inter_right isClosed_complex_posSemidef).inter_right
      (isClosed_eq continuous_id.matrix_det continuous_const)
  have hSpos : ∀ A ∈ S, A.PosDef := by
    intro A h
    exact h.1.2.posDef_iff_det_ne_zero.mpr (by rw [h.2]; exact one_ne_zero)
  have hrange : ∀ x, complexHessian realDirections imagDirections u x ∈ S := by
    intro x
    refine ⟨⟨?_, (hA x).posSemidef⟩, hdet x⟩
    rw [Metric.mem_closedBall, dist_zero_right, Matrix.norm_le_iff (le_max_left _ _)]
    intro i j
    exact (norm_entry_le_trace_re (hA x).posSemidef i j).trans
      ((complexHessian_trace_re_le_of_euclidean_entry_bound
        (hu.of_le (by norm_num)).contDiffAt (hM x)).trans (le_max_right _ _))
  let F : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin (n + n)) (Fin (n + n)) ℝ :=
    fun A => Matrix.reindex finSumFinEquiv finSumFinEquiv (realLinearizationMatrix A⁻¹)
  have hF : ContinuousOn F S := by
    intro A hA
    have hinv : ContinuousAt (fun A : Matrix (Fin n) (Fin n) ℂ => A⁻¹) A := by
      apply continuousAt_matrix_inv
      simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀
        (by rw [hA.2]; exact one_ne_zero : A.det ≠ 0)
    apply continuousWithinAt_pi.mpr
    intro i
    apply continuousWithinAt_pi.mpr
    intro j
    exact (((continuous_apply (finSumFinEquiv.symm j)).comp
      ((continuous_apply (finSumFinEquiv.symm i)).comp
        continuous_realLinearizationMatrix)).continuousAt.comp hinv).continuousWithinAt
  have hcoeff : Continuous (complexLinearizedCoeff u) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact continuous_iff_continuousAt.mpr fun x =>
      (complexLinearizedCoeff_contDiffAt hu.contDiffAt
        (Filter.Eventually.of_forall hdet) i j).continuousAt
  apply exists_global_normalizedEllipticCoeff_of_compact_range hcoeff
    (hS.image_of_continuousOn hF) (fun x => mem_image_of_mem F (hrange x))
  rintro _ ⟨A, hA, rfl⟩
  exact (realLinearizationMatrix_posDef (hSpos A hA).inv).submatrix
    finSumFinEquiv.symm.injective

theorem entire_convex_global_ellipticity [NeZero (n + n)]
    (hn : 2 ≤ n) {u : E → ℝ} (hu : ContDiff ℝ 4 u)
    (hdet : ∀ x, (complexHessian realDirections imagDirections u x).det = 1)
    (hR : ∀ x, (realBlockHessian realDirections imagDirections u x).PosSemidef) :
    ∃ c : ℝ, 0 < c ∧ ∃ B : NormalizedEllipticCoeff (n + n) univ,
      ∀ x, B.1.a x = c⁻¹ • complexLinearizedCoeff u x := by
  letI : NeZero (n + n) := ⟨by omega⟩
  obtain ⟨M, _, hM, _, _⟩ := entire_convex_hessian_bound hn hu hdet hR
  exact global_complexLinearizedCoeff_of_hessian_bound hu hdet
    (fun x => complexHessian_posDef_of_realBlockHessian
      (hu.of_le (by norm_num)).contDiffAt realDirections imagDirections (hR x) (hdet x)) hM

end CHS.Analysis
