import CHS.Analysis.ConvexGradient
import CHS.Analysis.SchurMinimum

/-!
# The common real kernel of an entire convex function of constant Hessian rank
-/

set_option autoImplicit false
noncomputable section

open DeGiorgi Set
open scoped ContDiff Gradient InnerProductSpace

namespace CHS.Analysis

open Calculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem realHessian_comp_linear
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : E → ℝ} (hu : ContDiff ℝ 2 u) (T : F →L[ℝ] E) (x v w : F) :
    realHessian (u ∘ T) x v w = realHessian u (T x) (T v) (T w) := by
  have hd (y : E) : DifferentiableAt ℝ (fderiv ℝ u) y :=
    (hu.contDiffAt.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  let P : (E →L[ℝ] ℝ) →L[ℝ] (F →L[ℝ] ℝ) := (ContinuousLinearMap.compL ℝ F E ℝ).flip T
  have heq : fderiv ℝ (u ∘ T) = fun y => P (fderiv ℝ u (T y)) := by
    funext y
    exact ((hu.differentiable (by norm_num) (T y)).hasFDerivAt.comp y T.hasFDerivAt).fderiv
  unfold realHessian
  rw [heq]
  have h := P.hasFDerivAt.comp x ((hd (T x)).hasFDerivAt.comp x T.hasFDerivAt)
  change HasFDerivAt (fun y => P (fderiv ℝ u (T y))) _ x at h
  rw [h.fderiv]
  rfl

private theorem realHessian_at_orthogonalProjection
    [FiniteDimensional ℝ E] {u : E → ℝ} (hu : ContDiff ℝ 2 u)
    (K : Submodule ℝ E) (hK : ∀ x (v : K), realHessian u x (v : E) = 0)
    (x v w : E) :
    realHessian u x v w =
      realHessian u (Kᗮ.starProjection x) (Kᗮ.starProjection v) (Kᗮ.starProjection w) := by
  let T := Kᗮ.starProjection
  let L := (fderiv ℝ u 0).comp K.starProjection
  have heq : u = fun y => (u ∘ T) y + L y := by
    funext y
    exact splits_on_orthogonalComplement hu K hK y
  have hd (y : E) : DifferentiableAt ℝ (u ∘ T) y :=
    (hu.differentiable (by norm_num) (T y)).comp y T.differentiableAt
  have heq' : fderiv ℝ u = fun y => fderiv ℝ (u ∘ T) y + L := by
    funext y
    have h := (hd y).hasFDerivAt.add L.hasFDerivAt
    change HasFDerivAt (fun y => (u ∘ T) y + L y) _ y at h
    rw [← heq] at h
    exact h.fderiv
  have hdu : ContDiff ℝ 2 (u ∘ T) := hu.comp T.contDiff
  have hD : DifferentiableAt ℝ (fderiv ℝ (u ∘ T)) x := (hdu.contDiffAt.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  calc
    realHessian u x v w = realHessian (u ∘ T) x v w := by
      unfold realHessian
      rw [heq', (hD.hasFDerivAt.add_const L).fderiv]
    _ = _ := realHessian_comp_linear hu T x v w

/-- For an entire convex function of constant real Hessian rank, the kernel
of the Hessian is one fixed subspace. -/
theorem realHessian_ker_eq_of_const_finrank
    [FiniteDimensional ℝ E] {u : E → ℝ} (hu : ContDiff ℝ 2 u) (hconv : ConvexOn ℝ univ u)
    (hrank : ∀ x : E, Module.finrank ℝ (realHessian u x).ker =
      Module.finrank ℝ (realHessian u 0).ker) :
    ∃ K : Submodule ℝ E, ∀ x, (realHessian u x).ker = K := by
  let K : Submodule ℝ E := ⨅ x : E, (realHessian u x).ker
  have hle (x : E) : K ≤ (realHessian u x).ker := iInf_le _ x
  have hK (x : E) (v : K) : realHessian u x (v : E) = 0 := hle x v.prop
  refine ⟨K, fun x => ?_⟩
  by_contra hne
  have hlt : K < (realHessian u x).ker := lt_of_le_of_ne (hle x) (Ne.symm hne)
  have hdim (y : E) : Module.finrank ℝ K < Module.finrank ℝ (realHessian u y).ker := by
    rw [hrank y, ← hrank x]
    exact Submodule.finrank_lt_finrank_of_lt hlt
  let V := Kᗮ
  let f : V → ℝ := u ∘ V.subtypeL
  have hf : ContDiff ℝ 2 f := hu.comp V.subtypeL.contDiff
  have hfconv : ConvexOn ℝ univ f := by
    have h := hconv.comp_affineMap V.subtypeL.toLinearMap.toAffineMap
    rw [preimage_univ] at h
    exact h
  have hsing (y : V) : ∃ v : V, v ≠ 0 ∧ realHessian f y v = 0 := by
    have hproper : K ≠ (realHessian u y).ker := by
      intro he
      exact (lt_irrefl _ <| he ▸ hdim y)
    obtain ⟨v, hvH, hvK⟩ := SetLike.exists_of_lt (lt_of_le_of_ne (hle y) hproper)
    let w := V.orthogonalProjectionOnto v
    have hwne : w ≠ 0 := by
      intro hw
      have hproj : v - K.starProjection v = 0 := by
        have h := congrArg (fun z : V => (z : E)) hw
        simpa [w, V, Submodule.orthogonalProjectionOnto_orthogonal] using h
      apply hvK
      rw [sub_eq_zero.mp hproj]
      exact (K.orthogonalProjectionOnto v).prop
    refine ⟨w, hwne, ?_⟩
    ext z
    rw [realHessian_comp_linear hu V.subtypeL]
    change realHessian u (y : E) (w : E) (z : E) = 0
    have hvH' : realHessian u (y : E) v = 0 := hvH
    have hproj : realHessian u (y : E) (K.starProjection v) = 0 :=
      hK y (K.orthogonalProjectionOnto v)
    change realHessian u (y : E) (Kᗮ.starProjection v) (z : E) = 0
    rw [Submodule.starProjection_apply, Submodule.orthogonalProjectionOnto_orthogonal]
    change realHessian u (y : E) (v - K.starProjection v) (z : E) = 0
    rw [map_sub, sub_apply, hvH', hproj, sub_self]
  obtain ⟨v, hv, hzero⟩ := exists_common_realHessian_kernel_of_singular hf hfconv hsing
  have hvK : (v : E) ∈ K := by
    apply (Submodule.mem_iInf _).mpr
    intro y
    change realHessian u y (v : E) = 0
    ext w
    rw [realHessian_at_orthogonalProjection hu K hK]
    have hpv : Kᗮ.starProjection (v : E) = v := by
      rw [Submodule.starProjection_apply, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
    rw [hpv]
    have hz := congrArg (fun L : V →L[ℝ] ℝ => L (V.orthogonalProjectionOnto w))
      (hzero (V.orthogonalProjectionOnto y))
    rw [realHessian_comp_linear hu V.subtypeL] at hz
    exact hz
  have hbot : (v : E) ∈ (⊥ : Submodule ℝ E) := by
    rw [← K.inf_orthogonal_eq_bot]
    exact ⟨hvK, v.prop⟩
  exact hv (Subtype.ext ((Submodule.mem_bot ℝ).mp hbot))


variable {n : ℕ} [NeZero (n + n)]
local notation "Eℂ" => AmbientSpace (n + n)

private theorem realHessian_finrank_range_eq_matrix_rank (u : Eℂ → ℝ) (x : Eℂ) :
    Module.finrank ℝ (realHessian u x).range =
      (realBlockHessian realDirections imagDirections u x).rank := by
  let B := (EuclideanSpace.basisFun (Fin (n + n)) ℝ).toBasis
  let T := (InnerProductSpace.toDual ℝ Eℂ).symm.toContinuousLinearEquiv
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
    have hB' (z : Eℂ) (k : Fin (n + n)) : B.repr z k = z k :=
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
    rw [← InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := Eℂ)]
    rw [real_inner_comm]
    simp [T, EuclideanSpace.inner_single_left]
  have hMatrix := (LinearMap.toMatrix B B L).rank_eq_finrank_range_toLin B B
  rw [Matrix.toLin_toMatrix] at hMatrix
  rw [heq, Matrix.rank_reindex, Matrix.rank_transpose] at hMatrix
  exact hrange.symm.trans hMatrix.symm

/-- Fixed real kernel and affine splitting for the entire CHS solution,
with the rank supplied by Lemma 2.5. -/
theorem exists_fixed_realHessian_kernel_and_split
    (hd : 2 < ((n + n : ℕ) : ℝ)) {u : Eℂ → ℝ}
    (hu : ContDiff ℝ 4 u) (hconv : ConvexOn ℝ univ u)
    (hdet : ∀ y, (complexHessian realDirections imagDirections u y).det = 1)
    (hR : ∀ y, (realBlockHessian realDirections imagDirections u y).PosSemidef) :
    ∃ K : Submodule ℝ Eℂ, (∀ x, (realHessian u x).ker = K) ∧
      ∀ x, u x = u (Kᗮ.orthogonalProjectionOnto x : Eℂ) +
        fderiv ℝ u 0 (K.orthogonalProjectionOnto x : Eℂ) := by
  have hdim (x : Eℂ) : Module.finrank ℝ (realHessian u x).ker =
      Module.finrank ℝ (realHessian u 0).ker := by
    have hrank := (schur_and_realHessian_rank_constant hd isOpen_univ isPreconnected_univ
      hu.contDiffOn (fun y _ => hdet y) (fun y _ => hR y) (mem_univ x) (mem_univ 0)).2
    have hnx := (realHessian u x).toLinearMap.finrank_range_add_finrank_ker
    have hn0 := (realHessian u 0).toLinearMap.finrank_range_add_finrank_ker
    rw [show (realHessian u x).toLinearMap.range = (realHessian u x).range from rfl,
      realHessian_finrank_range_eq_matrix_rank, hrank, ← realHessian_finrank_range_eq_matrix_rank] at hnx
    exact Nat.add_left_cancel (hnx.trans hn0.symm)
  have hu2 : ContDiff ℝ 2 u := hu.of_le (by norm_num)
  obtain ⟨K, hK⟩ := realHessian_ker_eq_of_const_finrank hu2 hconv hdim
  refine ⟨K, hK, splits_on_orthogonalComplement hu2 K ?_⟩
  intro x v
  exact (hK x).symm ▸ v.prop

end CHS.Analysis
