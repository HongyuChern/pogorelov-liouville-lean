import CHS.Algebra.SchurRank
import CHS.Analysis.BlockCoordinates
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# The actual Hessian kernel and the Schur rank identity

The coordinate-rank calculation is the accepted fixed-kernel calculation,
now exposed as a reusable public interface.  The propagation lemma below
uses a prescribed translation kernel and a single extremum with vanishing
Schur complement; it does not assume global constant rank.
-/

set_option autoImplicit false
noncomputable section

open Set Matrix
open scoped BigOperators ContDiff ComplexOrder

namespace CHS.Analysis

open CHS.Calculus

variable {n : ℕ}
local notation "E₀" => DeGiorgi.AmbientSpace (n + n)

theorem realHessian_finrank_range_eq_realBlockHessian_rank (u : E₀ → ℝ) (x : E₀) :
    Module.finrank ℝ (realHessian u x).range =
      (realBlockHessian realDirections imagDirections u x).rank := by
  let B := (EuclideanSpace.basisFun (Fin (n + n)) ℝ).toBasis
  let T := (InnerProductSpace.toDual ℝ E₀).symm.toContinuousLinearEquiv
  let H := (realHessian u x).toLinearMap
  let L := T.toContinuousLinearMap.toLinearMap.comp H
  have hR : L.range = H.range.map T.toContinuousLinearMap.toLinearMap :=
    LinearMap.range_comp H _
  have hrange : Module.finrank ℝ L.range = Module.finrank ℝ H.range := by
    rw [hR]
    exact (Submodule.equivMapOfInjective _ T.injective _).finrank_eq.symm
  have heq : LinearMap.toMatrix B B L =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (realBlockHessian realDirections imagDirections u x).transpose := by
    ext i j
    rw [LinearMap.toMatrix_apply, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.transpose_apply]
    have hB (k : Fin (n + n)) : B k = EuclideanSpace.single k 1 :=
      EuclideanSpace.basisFun_apply (Fin (n + n)) ℝ k
    have hB' (z : E₀) (k : Fin (n + n)) : B.repr z k = z k :=
      EuclideanSpace.basisFun_repr (Fin (n + n)) ℝ z k
    have hdir (k : Fin (n + n)) :
        Sum.elim (realDirections (n := n)) imagDirections (finSumFinEquiv.symm k) =
          EuclideanSpace.single k 1 := by
      obtain ⟨l, rfl⟩ := finSumFinEquiv.surjective k
      rw [Equiv.symm_apply_apply]
      cases l <;> rfl
    rw [hB, hB']
    change T (realHessian u x (EuclideanSpace.single j 1)) i =
      realHessian u x (Sum.elim realDirections imagDirections (finSumFinEquiv.symm j))
        (Sum.elim realDirections imagDirections (finSumFinEquiv.symm i))
    rw [hdir, hdir]
    rw [← InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := E₀)]
    rw [real_inner_comm]
    simp [T, EuclideanSpace.inner_single_left]
  have hMatrix := (LinearMap.toMatrix B B L).rank_eq_finrank_range_toLin B B
  rw [Matrix.toLin_toMatrix] at hMatrix
  rw [heq, Matrix.rank_reindex, Matrix.rank_transpose] at hMatrix
  exact hrange.symm.trans hMatrix.symm

theorem schurHessian_eq_zero_of_fixed_subspace_and_one_kernel
    {u : E₀ → ℝ} {U : Set E₀} (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U)
    (hA : ∀ x ∈ U, (complexHessian realDirections imagDirections u x).PosDef)
    (K : Submodule ℝ E₀)
    (hK : ∀ x ∈ U, K ≤ (realHessian u x).ker)
    {p : E₀} (hp : p ∈ U) (hker : (realHessian u p).ker = K)
    (hM : schurHessian realDirections imagDirections u p = 0) :
    ∀ x ∈ U, schurHessian realDirections imagDirections u x = 0 := by
  have hpRank : Module.finrank ℝ (realHessian u p).range = n := by
    rw [realHessian_finrank_range_eq_realBlockHessian_rank,
      realBlockHessian_rank_eq_schur (hu.contDiffAt (hU.mem_nhds hp))
        realDirections imagDirections (hA p hp), hM, Matrix.rank_zero, zero_add,
      Fintype.card_fin]
  have hdimP := (realHessian u p).toLinearMap.finrank_range_add_finrank_ker
  change Module.finrank ℝ (realHessian u p).range +
    Module.finrank ℝ (realHessian u p).ker = Module.finrank ℝ E₀ at hdimP
  rw [hpRank, hker] at hdimP
  intro x hx
  have hdimX := (realHessian u x).toLinearMap.finrank_range_add_finrank_ker
  change Module.finrank ℝ (realHessian u x).range +
    Module.finrank ℝ (realHessian u x).ker = Module.finrank ℝ E₀ at hdimX
  have hmono := Submodule.finrank_mono (hK x hx)
  rw [realHessian_finrank_range_eq_realBlockHessian_rank,
    realBlockHessian_rank_eq_schur (hu.contDiffAt (hU.mem_nhds hx))
      realDirections imagDirections (hA x hx), Fintype.card_fin] at hdimX
  have hrank : (schurHessian realDirections imagDirections u x).rank = 0 := by omega
  have hrange : (schurHessian realDirections imagDirections u x).mulVecLin.range = ⊥ :=
    Submodule.finrank_eq_zero.mp hrank
  have hlin := LinearMap.range_eq_bot.mp hrange
  ext i j
  have hentry := congrArg (fun L : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) =>
    L (Pi.single j 1) i) hlin
  simpa only [Matrix.mulVecLin_apply, Matrix.mulVec_single_one, Matrix.col_apply,
    LinearMap.zero_apply, Pi.zero_apply, Matrix.zero_apply] using hentry

end CHS.Analysis

namespace CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

theorem realHessian_ker_eq_of_strict_projected_bound
    (K : Submodule ℝ E) {u : E → ℝ} {x : E}
    (hK : K ≤ (realHessian u x).ker) {c : ℝ} (hc : 0 < c)
    (hbound : ∀ v : E, c * ‖Kᗮ.orthogonalProjectionOnto v‖ ^ 2 ≤ realHessian u x v v) :
    (realHessian u x).ker = K := by
  apply le_antisymm _ hK
  intro v hv
  have hv0 : realHessian u x v = 0 := hv
  have hb := hbound v
  rw [hv0, ContinuousLinearMap.zero_apply] at hb
  have hsq : ‖Kᗮ.orthogonalProjectionOnto v‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖Kᗮ.orthogonalProjectionOnto v‖]
  have hz : Kᗮ.orthogonalProjectionOnto v = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hsq)
  have hm := Kᗮ.orthogonalProjectionOnto_eq_zero_iff.mp hz
  simpa only [K.orthogonal_orthogonal] using hm

end CHS.Calculus
