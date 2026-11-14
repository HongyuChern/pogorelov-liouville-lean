import CHS.Calculus.ComplexAffineMap

/-! # The actual real map of an invertible complex matrix is an equivalence -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace CHS.Calculus

open CHS.Analysis

variable {n : ℕ}
local notation "E₀" => DeGiorgi.AmbientSpace (n + n)

def blockComplexCoordinates : E₀ →ₗ[ℝ] (Fin n → ℂ) where
  toFun x i := ⟨x (finSumFinEquiv (Sum.inl i)), x (finSumFinEquiv (Sum.inr i))⟩
  map_add' x y := by ext i <;> rfl
  map_smul' r x := by
    ext i
    apply Complex.ext <;> simp [Complex.real_smul]

theorem blockComplexCoordinates_injective :
    Function.Injective (blockComplexCoordinates (n := n)) := by
  intro x y h
  ext k
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective k
  cases i with
  | inl i => exact congrArg (fun z : Fin n → ℂ => (z i).re) h
  | inr i => exact congrArg (fun z : Fin n → ℂ => (z i).im) h

theorem blockComplexCoordinates_realDirection (i : Fin n) :
    blockComplexCoordinates (realDirections i) = Pi.single i (1 : ℂ) := by
  ext j
  change (⟨(realDirections i) (finSumFinEquiv (Sum.inl j)),
    (realDirections i) (finSumFinEquiv (Sum.inr j))⟩ : ℂ) =
      (Pi.single i (1 : ℂ) : Fin n → ℂ) j
  simp only [realDirections, PiLp.single_apply, Equiv.apply_eq_iff_eq, Sum.inl.injEq,
    Sum.inr_ne_inl, ite_false, Pi.single_apply]
  split_ifs <;> rfl

theorem blockComplexCoordinates_imagDirection (i : Fin n) :
    blockComplexCoordinates (imagDirections i) = Pi.single i Complex.I := by
  ext j
  change (⟨(imagDirections i) (finSumFinEquiv (Sum.inl j)),
    (imagDirections i) (finSumFinEquiv (Sum.inr j))⟩ : ℂ) =
      (Pi.single i Complex.I : Fin n → ℂ) j
  simp only [imagDirections, PiLp.single_apply, Equiv.apply_eq_iff_eq, Sum.inr.injEq,
    Sum.inl_ne_inr, ite_false, Pi.single_apply]
  split_ifs <;> rfl

theorem blockComplexCoordinates_frameReal
    (Q : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    blockComplexCoordinates (complexFrameReal Q realDirections imagDirections i) = Q i := by
  unfold complexFrameReal
  simp only [map_sum, map_add, map_smul, blockComplexCoordinates_realDirection,
    blockComplexCoordinates_imagDirection]
  ext j
  simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply]
  calc
    _ = ∑ k, if k = j then Q i k else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : k = j
      · subst k
        simp [Pi.single_apply, Complex.real_smul, Complex.re_add_im]
      · simp [Pi.single_apply, hk, Ne.symm hk]
    _ = _ := by simp

theorem blockComplexCoordinates_frameImag
    (Q : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    blockComplexCoordinates (complexFrameImag Q realDirections imagDirections i) =
      fun j => Q i j * Complex.I := by
  unfold complexFrameImag
  simp only [map_sum, map_sub, map_smul, blockComplexCoordinates_realDirection,
    blockComplexCoordinates_imagDirection]
  ext j
  simp only [Finset.sum_apply, Pi.sub_apply, Pi.smul_apply]
  calc
    _ = ∑ k, if k = j then Q i k * Complex.I else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : k = j
      · subst k
        simp only [Pi.single_apply, ite_true, Complex.real_smul, mul_one]
        apply Complex.ext <;> simp
      · simp [Pi.single_apply, hk, Ne.symm hk]
    _ = _ := by simp

theorem blockComplexCoordinates_complexMatrixRealMap
    (G : Matrix (Fin n) (Fin n) ℂ) (x : E₀) :
    blockComplexCoordinates (complexMatrixRealMap G x) =
      G.mulVec (blockComplexCoordinates x) := by
  let B := (EuclideanSpace.basisFun (Fin (n + n)) ℝ).toBasis
  have hB (k : Fin (n + n)) : B k = EuclideanSpace.single k (1 : ℝ) :=
    EuclideanSpace.basisFun_apply (Fin (n + n)) ℝ k
  have hmaps : blockComplexCoordinates.comp (complexMatrixRealMap G).toLinearMap =
      (G.mulVecLin.restrictScalars ℝ).comp blockComplexCoordinates := by
    apply B.ext
    intro k
    rw [hB]
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective k
    cases i with
    | inl i =>
      change blockComplexCoordinates (complexMatrixRealMap G (realDirections i)) =
        G.mulVec (blockComplexCoordinates (realDirections i))
      rw [complexMatrixRealMap_realDirection, blockComplexCoordinates_frameReal,
        blockComplexCoordinates_realDirection, Matrix.mulVec_single_one]
      rfl
    | inr i =>
      change blockComplexCoordinates (complexMatrixRealMap G (imagDirections i)) =
        G.mulVec (blockComplexCoordinates (imagDirections i))
      rw [complexMatrixRealMap_imagDirection, blockComplexCoordinates_frameImag,
        blockComplexCoordinates_imagDirection, Matrix.mulVec_single]
      rfl
  exact congrArg (fun L : E₀ →ₗ[ℝ] (Fin n → ℂ) => L x) hmaps

theorem complexMatrixRealMap_one (x : E₀) : complexMatrixRealMap 1 x = x := by
  apply blockComplexCoordinates_injective
  rw [blockComplexCoordinates_complexMatrixRealMap, Matrix.one_mulVec]

theorem complexMatrixRealMap_mul
    (G H : Matrix (Fin n) (Fin n) ℂ) (x : E₀) :
    complexMatrixRealMap (G * H) x = complexMatrixRealMap G (complexMatrixRealMap H x) := by
  apply blockComplexCoordinates_injective
  simp only [blockComplexCoordinates_complexMatrixRealMap, Matrix.mulVec_mulVec]

theorem complexMatrixRealMap_bijective
    (G : Matrix (Fin n) (Fin n) ℂ) (hG : IsUnit G.det) :
    Function.Bijective (complexMatrixRealMap G) := by
  have hleft : Function.LeftInverse (complexMatrixRealMap G⁻¹) (complexMatrixRealMap G) := by
    intro x
    rw [← complexMatrixRealMap_mul, Matrix.nonsing_inv_mul _ hG, complexMatrixRealMap_one]
  have hright : Function.RightInverse (complexMatrixRealMap G⁻¹) (complexMatrixRealMap G) := by
    intro x
    rw [← complexMatrixRealMap_mul, Matrix.mul_nonsing_inv _ hG, complexMatrixRealMap_one]
  exact ⟨hleft.injective, hright.surjective⟩

def complexMatrixRealEquiv (G : Matrix (Fin n) (Fin n) ℂ) (hG : IsUnit G.det) : E₀ ≃L[ℝ] E₀ :=
  (LinearEquiv.ofBijective (complexMatrixRealMap G).toLinearMap
    (complexMatrixRealMap_bijective G hG)).toContinuousLinearEquiv

theorem complexMatrixRealEquiv_apply
    (G : Matrix (Fin n) (Fin n) ℂ) (hG : IsUnit G.det) (x : E₀) :
    complexMatrixRealEquiv G hG x = complexMatrixRealMap G x := rfl

theorem isUnit_det_of_normSq_eq_one
    {G : Matrix (Fin n) (Fin n) ℂ} (hG : Complex.normSq G.det = 1) : IsUnit G.det := by
  apply isUnit_iff_ne_zero.mpr
  intro hz
  simp only [hz, map_zero] at hG
  norm_num at hG

theorem exists_complex_affine_preimage
    (G : Matrix (Fin n) (Fin n) ℂ) (hG : IsUnit G.det) (c : E₀)
    {h : ℝ} (hh : 0 < h) (x : E₀) :
    ∃ w : E₀, c + Real.sqrt h • complexMatrixRealMap G w = x := by
  obtain ⟨w, hw⟩ := (complexMatrixRealMap_bijective G hG).2
    ((Real.sqrt h)⁻¹ • (x - c))
  refine ⟨w, ?_⟩
  rw [hw, smul_smul, mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr hh), one_smul]
  abel

end CHS.Calculus
