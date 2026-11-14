import CHS.Calculus.BasisHessian
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Rank of the real Hessian and of its Schur complement

The rank passes through the fixed complex congruence and the block
elimination. Complexification preserves the rank of the real symmetric
Hessian by diagonalizing it over the reals first.
-/

set_option autoImplicit false
open Matrix Unitary
open scoped BigOperators ComplexOrder ContDiff

namespace CHS.Calculus

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

private theorem rank_ofReal_of_isHermitian {R : Matrix ι ι ℝ} (hR : R.IsHermitian) :
    (R.map Complex.ofReal).rank = R.rank := by
  classical
  let P : Matrix ι ι ℝ := hR.eigenvectorUnitary
  let D := diagonal hR.eigenvalues
  have hR_eq : R = P * D * P.conjTranspose := by
    simpa [P, D, conjStarAlgAut_apply, star_eq_conjTranspose] using hR.spectral_theorem
  have hP : IsUnit P := Unitary.isUnit_coe
  have hPt : IsUnit P.conjTranspose := by
    have ht : IsUnit (↑(hR.eigenvectorUnitary⁻¹) : Matrix ι ι ℝ) := Unitary.isUnit_coe
    exact ht
  have hPmap := hP.map (Complex.ofRealHom.mapMatrix (m := ι))
  have hPtmap := hPt.map (Complex.ofRealHom.mapMatrix (m := ι))
  change (Complex.ofRealHom.mapMatrix R).rank = R.rank
  rw [hR_eq, map_mul, map_mul]
  rw [rank_mul_eq_left_of_isUnit_det _ _ ((isUnit_iff_isUnit_det _).mp hPtmap),
    rank_mul_eq_right_of_isUnit_det _ _ ((isUnit_iff_isUnit_det _).mp hPmap),
    rank_mul_eq_left_of_isUnit_det _ _ ((isUnit_iff_isUnit_det _).mp hPt),
    rank_mul_eq_right_of_isUnit_det _ _ ((isUnit_iff_isUnit_det _).mp hP)]
  have hD : D.map Complex.ofReal = diagonal (fun i => (hR.eigenvalues i : ℂ)) := by
    ext i j
    by_cases h : i = j <;> simp [D, h]
  change (D.map Complex.ofReal).rank = D.rank
  rw [hD, rank_diagonal]
  change _ = (diagonal hR.eigenvalues).rank
  rw [rank_diagonal]
  exact Fintype.card_congr (Equiv.subtypeEquivRight fun i => Complex.ofReal_ne_zero)

private theorem rank_blockDiagonal {A : Matrix ι ι ℂ} {D : Matrix κ κ ℂ} :
    (fromBlocks A 0 0 D).rank = A.rank + D.rank := by
  let e := LinearEquiv.sumArrowLequivProdArrow ι κ ℂ ℂ
  let L := (fromBlocks A 0 0 D).mulVecLin
  let M := A.mulVecLin.prodMap D.mulVecLin
  have hcomp : (e : _ →ₗ[ℂ] _).comp L = M.comp (e : _ →ₗ[ℂ] _) := by
    apply LinearMap.ext
    intro v
    change e ((fromBlocks A 0 0 D).mulVec v) = (A.mulVec (v ∘ Sum.inl), D.mulVec (v ∘ Sum.inr))
    rw [fromBlocks_mulVec]
    simp only [zero_mulVec, add_zero, zero_add]
    rfl
  have hrange : L.range.map (e : _ →ₗ[ℂ] _) = M.range := by
    rw [← LinearMap.range_comp, hcomp, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]
  change Module.finrank ℂ L.range = Module.finrank ℂ A.mulVecLin.range +
    Module.finrank ℂ D.mulVecLin.range
  rw [(e.submoduleMap L.range).finrank_eq, hrange, LinearMap.range_prodMap]
  let eProd : ↥(A.mulVecLin.range.prod D.mulVecLin.range) ≃ₗ[ℂ]
      ↥A.mulVecLin.range × ↥D.mulVecLin.range := {
    toFun := fun p => (⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2⟩)
    invFun := fun p => ⟨(p.1.1, p.2.1), p.1.2, p.2.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  exact eProd.finrank_eq.trans (Module.finrank_prod)

private theorem rank_fromBlocks_schur
    (A B C D : Matrix ι ι ℂ) (hD : IsUnit D.det) :
    (fromBlocks A B C D).rank = (A - B * D⁻¹ * C).rank + Fintype.card ι := by
  let : Invertible D := invertibleOfIsUnitDet _ hD
  have hL : IsUnit (fromBlocks 1 (B * ⅟D) 0 1).det := by
    simp
  have hR : IsUnit (fromBlocks 1 0 (⅟D * C) 1).det := by
    simp
  rw [fromBlocks_eq_of_invertible₂₂ A B C D,
    rank_mul_eq_left_of_isUnit_det _ _ hR, rank_mul_eq_right_of_isUnit_det _ _ hL,
    rank_blockDiagonal, invOf_eq_nonsing_inv,
    rank_of_isUnit D ((isUnit_iff_isUnit_det _).mpr hD)]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem realBlockHessian_rank_eq_schur
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) (a b : ι → E)
    (hA : (complexHessian a b u x).PosDef) :
    (realBlockHessian a b u x).rank =
      (schurHessian a b u x).rank + Fintype.card ι := by
  let P : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ := (2 : ℂ)⁻¹ • hessianTransform
  have hP : IsUnit P := halfHessianTransform_isUnit
  have hPs : IsUnit (star P) := by
    obtain ⟨q, hq⟩ := hP
    rw [← hq]
    exact (star q).isUnit
  have hblock : (complexBlockHessian a b u x).rank = (realBlockHessian a b u x).rank := by
    rw [actual_block_congruence_scaled hu a b,
      rank_mul_eq_left_of_isUnit_det _ _ ((isUnit_iff_isUnit_det _).mp hPs),
      rank_mul_eq_right_of_isUnit_det _ _ ((isUnit_iff_isUnit_det _).mp hP)]
    exact rank_ofReal_of_isHermitian (realBlockHessian_isHermitian hu a b)
  rw [← hblock]
  have hT : (complexHessian a b u x).map star = (complexHessian a b u x).transpose := by
    ext i j
    exact (complexHessian_isHermitian hu a b).apply j i
  have hD : IsUnit ((complexHessian a b u x).map star).det := by
    rw [hT, det_transpose]
    exact (isUnit_iff_isUnit_det _).mp hA.isUnit
  exact rank_fromBlocks_schur _ _ _ _ hD

end CHS.Calculus
