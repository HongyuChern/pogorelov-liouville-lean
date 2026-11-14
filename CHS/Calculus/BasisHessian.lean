import CHS.Calculus.SchurHessianLM

/-!
# Real and complex Hessian entries in fixed real directions

These are the coordinate identities for the block congruence in Lemma 2.2.
The real Hessian is the second Fréchet derivative.
-/

set_option autoImplicit false
open scoped BigOperators ComplexOrder ContDiff Topology

namespace CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*}

private theorem rd_ofReal_at {u : E → ℝ} {x : E}
    (hu : DifferentiableAt ℝ u x) (v : E) :
    rd v (fun y => (u y : ℂ)) x = (fderiv ℝ u x v : ℂ) := by
  have h := Complex.ofRealCLM.hasFDerivAt.comp x hu.hasFDerivAt
  change HasFDerivAt (fun y => (u y : ℂ))
    (Complex.ofRealCLM.comp (fderiv ℝ u x)) x at h
  rw [rd, h.fderiv]
  rfl

theorem rd_rd_ofReal {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (a b : E) :
    rd a (rd b (fun y => (u y : ℂ))) x = (realHessian u x a b : ℂ) := by
  have hnear : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 1 u y :=
    (hu.of_le (m := 1) (by norm_num)).eventually (by simp)
  have heq : rd b (fun y => (u y : ℂ)) =ᶠ[𝓝 x]
      (fun y => (fderiv ℝ u y b : ℂ)) :=
    hnear.mono fun y hy => rd_ofReal_at (hy.differentiableAt (by norm_num)) b
  change fderiv ℝ (rd b (fun y => (u y : ℂ))) x a = _
  rw [heq.fderiv_eq]
  have hdf := (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h := Complex.ofRealCLM.hasFDerivAt.comp x
    (hdf.hasFDerivAt.clm_apply (hasFDerivAt_const b x))
  change HasFDerivAt (fun y => (fderiv ℝ u y b : ℂ)) _ x at h
  rw [h.fderiv]
  simp only [ContinuousLinearMap.comp_apply, add_apply, zero_apply, map_zero,
    zero_add, Complex.ofRealCLM_apply, realHessian]
  rfl

theorem complexHessian_real_entry {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (a b : ι → E) (i j : ι) :
    complexHessian a b u x i j = (4 : ℂ)⁻¹ *
      ((realHessian u x (a i) (a j) : ℂ) + (realHessian u x (b i) (b j) : ℂ) +
        Complex.I * ((realHessian u x (a i) (b j) : ℂ) -
          (realHessian u x (b i) (a j) : ℂ))) := by
  have huc : ContDiffAt ℝ 2 (fun y => (u y : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hu
  unfold complexHessian
  change (2 : ℂ)⁻¹ * (rd (a i) (dz (a j) (-b j) (fun y => (u y : ℂ))) x -
    Complex.I * rd (b i) (dz (a j) (-b j) (fun y => (u y : ℂ))) x) = _
  rw [rd_dz_at huc, rd_dz_at huc]
  simp only [rd_rd_ofReal hu, map_neg, Complex.ofReal_neg]
  ring_nf
  simp
  ring

theorem pureHessian_real_entry {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (a b : ι → E) (i j : ι) :
    pureHessian a b u x i j = (4 : ℂ)⁻¹ *
      ((realHessian u x (a i) (a j) : ℂ) - (realHessian u x (b i) (b j) : ℂ) -
        Complex.I * ((realHessian u x (a i) (b j) : ℂ) +
          (realHessian u x (b i) (a j) : ℂ))) := by
  have huc : ContDiffAt ℝ 2 (fun y => (u y : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hu
  unfold pureHessian
  change (2 : ℂ)⁻¹ * (rd (a i) (dz (a j) (b j) (fun y => (u y : ℂ))) x -
    Complex.I * rd (b i) (dz (a j) (b j) (fun y => (u y : ℂ))) x) = _
  rw [rd_dz_at huc, rd_dz_at huc]
  simp only [rd_rd_ofReal hu]
  ring_nf
  simp
  ring

noncomputable def complexBlockHessian (a b : ι → E) (u : E → ℝ) (x : E) :
    Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
  Matrix.fromBlocks (complexHessian a b u x) (pureHessian a b u x)
    ((pureHessian a b u x).map star) ((complexHessian a b u x).map star)

set_option maxHeartbeats 400000 in
theorem complexBlockHessian_posSemidef_iff [Fintype ι] [DecidableEq ι]
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) (a b : ι → E)
    (hA : (complexHessian a b u x).PosDef) :
    (complexBlockHessian a b u x).PosSemidef ↔ (schurHessian a b u x).PosSemidef := by
  have hT : (complexHessian a b u x).map star = (complexHessian a b u x).transpose := by
    ext i j
    exact (complexHessian_isHermitian hu a b).apply j i
  have hH : ((complexHessian a b u x).map star).PosDef := hT ▸ hA.transpose
  letI : Invertible ((complexHessian a b u x).map star) :=
    Matrix.invertibleOfIsUnitDet _ ((Matrix.isUnit_iff_isUnit_det _).mp hH.isUnit)
  have h := Matrix.PosDef.fromBlocks₂₂
    (complexHessian a b u x) (pureHessian a b u x) hH
  rw [pureHessian_conjTranspose hu a b] at h
  exact h

/-- The constant real-to-complex change of coordinates in the manuscript. -/
noncomputable def hessianTransform [DecidableEq ι] : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
  Matrix.fromBlocks 1 ((-Complex.I) • 1) 1 (Complex.I • 1)

theorem hessianTransform_adjoint [DecidableEq ι] :
    (hessianTransform (ι := ι)).conjTranspose =
      Matrix.fromBlocks 1 1 (Complex.I • 1) ((-Complex.I) • 1) := by
  simp [hessianTransform, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_smul]

theorem hessianTransform_adjoint_mul [Fintype ι] [DecidableEq ι] :
    (hessianTransform (ι := ι)).conjTranspose * hessianTransform = (2 : ℂ) • 1 := by
  rw [hessianTransform_adjoint]
  unfold hessianTransform
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_smul, smul_smul, Matrix.mul_one]
  norm_num [Matrix.fromBlocks_one, ← add_smul, Complex.I_sq]
  rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul]
  simp [two_smul, one_add_one_eq_two]

noncomputable def realBlockHessian (a b : ι → E) (u : E → ℝ) (x : E) :
    Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  fun i j => realHessian u x (Sum.elim a b i) (Sum.elim a b j)

theorem actual_block_congruence [Fintype ι] [DecidableEq ι]
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) (a b : ι → E) :
    complexBlockHessian a b u x = (4 : ℂ)⁻¹ •
      (hessianTransform * (realBlockHessian a b u x).map Complex.ofReal *
        (hessianTransform (ι := ι)).conjTranspose) := by
  let R (v w : ι → E) : Matrix ι ι ℝ := fun i j => realHessian u x (v i) (w j)
  have hR : realBlockHessian a b u x = Matrix.fromBlocks (R a a) (R a b) (R b a) (R b b) := by
    ext (i | i) (j | j) <;> rfl
  rw [hR, Matrix.fromBlocks_map, hessianTransform_adjoint]
  unfold hessianTransform
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  ext (i | i) (j | j) <;>
    simp only [complexBlockHessian, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.map_apply,
      Matrix.smul_apply, Matrix.add_apply, smul_eq_mul,
      complexHessian_real_entry hu, pureHessian_real_entry hu] <;>
    dsimp only [R] <;>
    (try simp only [star_mul, star_add, star_sub, star_inv₀, star_ofNat,
      Complex.star_def, Complex.conj_I, Complex.conj_ofReal]) <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

theorem halfHessianTransform_isUnit [Fintype ι] [DecidableEq ι] :
    IsUnit ((2 : ℂ)⁻¹ • (hessianTransform (ι := ι))) := by
  let T := hessianTransform (ι := ι)
  let P : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ := (2 : ℂ)⁻¹ • T
  have hLeft : T.conjTranspose * P = 1 := by
    dsimp only [P]
    rw [Matrix.mul_smul, hessianTransform_adjoint_mul, smul_smul]
    norm_num
  have hDet : T.conjTranspose.det * P.det = 1 := by
    rw [← Matrix.det_mul, hLeft, Matrix.det_one]
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  exact isUnit_of_mul_isUnit_right (hDet ▸ isUnit_one)

theorem actual_block_congruence_scaled [Fintype ι] [DecidableEq ι]
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) (a b : ι → E) :
    let P := (2 : ℂ)⁻¹ • (hessianTransform (ι := ι))
    complexBlockHessian a b u x =
      P * (realBlockHessian a b u x).map Complex.ofReal * star P := by
  let T := hessianTransform (ι := ι)
  let P : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ := (2 : ℂ)⁻¹ • T
  change complexBlockHessian a b u x =
    P * (realBlockHessian a b u x).map Complex.ofReal * star P
  rw [actual_block_congruence hu a b]
  simp only [P, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_smul,
    star_inv₀, star_ofNat, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  norm_num
  rfl

theorem actual_block_posSemidef_iff_complexification [Fintype ι] [DecidableEq ι]
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) (a b : ι → E) :
    (complexBlockHessian a b u x).PosSemidef ↔
      ((realBlockHessian a b u x).map Complex.ofReal).PosSemidef := by
  rw [actual_block_congruence_scaled hu a b]
  exact Matrix.IsUnit.posSemidef_star_right_conjugate_iff
    (halfHessianTransform_isUnit (ι := ι))

private theorem ofReal_quadraticForm [Fintype ι] (R : Matrix ι ι ℝ)
    (hR : R.IsHermitian) (z : ι → ℂ) :
    star z ⬝ᵥ ((R.map Complex.ofReal).mulVec z) =
      ((fun i => (z i).re) ⬝ᵥ R.mulVec (fun i => (z i).re) +
        (fun i => (z i).im) ⬝ᵥ R.mulVec (fun i => (z i).im) : ℝ) := by
  have hSymm (i j : ι) : R j i = R i j := hR.apply i j
  apply Complex.ext
  · simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Complex.re_sum,
      Pi.star_apply, Matrix.map_apply, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.star_def, Complex.conj_re,
      Complex.conj_im, zero_mul, add_zero, sub_zero]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  · simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Complex.im_sum,
      Pi.star_apply, Matrix.map_apply, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.star_def, Complex.conj_re,
      Complex.conj_im, zero_mul, add_zero, sub_zero, Finset.sum_add_distrib,
      neg_mul]
    have hSwap : (∑ i, ∑ j, -((z i).im * (R i j * (z j).re))) =
        -(∑ i, ∑ j, (z i).re * ((R i j) * (z j).im)) := by
      rw [Finset.sum_comm]
      simp only [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hSymm]
      ring
    linarith

theorem real_matrix_posSemidef_iff_complexification [Fintype ι] {R : Matrix ι ι ℝ}
    (hR : R.IsHermitian) : R.PosSemidef ↔ (R.map Complex.ofReal).PosSemidef := by
  constructor
  · intro h
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · ext i j
      change star (R j i : ℂ) = (R i j : ℂ)
      simpa only [Complex.star_def, Complex.conj_ofReal, star_trivial] using
        congrArg Complex.ofReal (hR.apply i j)
    · intro z
      rw [ofReal_quadraticForm R hR z]
      apply Complex.nonneg_iff.mpr
      simpa only [Complex.ofReal_re, Complex.ofReal_im, and_true, star_trivial] using
        add_nonneg (h.dotProduct_mulVec_nonneg (fun i => (z i).re))
          (h.dotProduct_mulVec_nonneg (fun i => (z i).im))
  · intro h
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hR
    intro z
    have hz := h.dotProduct_mulVec_nonneg (fun i => (z i : ℂ))
    rw [ofReal_quadraticForm R hR] at hz
    simpa [Complex.nonneg_iff] using hz

theorem realBlockHessian_isHermitian {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (a b : ι → E) : (realBlockHessian a b u x).IsHermitian := by
  ext i j
  exact realHessian_symm hu _ _

theorem realBlockHessian_posSemidef_equivalences [Fintype ι] [DecidableEq ι]
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) (a b : ι → E)
    (hA : (complexHessian a b u x).PosDef) :
    ((realBlockHessian a b u x).PosSemidef ↔ (complexBlockHessian a b u x).PosSemidef) ∧
      ((complexBlockHessian a b u x).PosSemidef ↔ (schurHessian a b u x).PosSemidef) :=
  ⟨(real_matrix_posSemidef_iff_complexification (realBlockHessian_isHermitian hu a b)).trans
      (actual_block_posSemidef_iff_complexification hu a b).symm,
    complexBlockHessian_posSemidef_iff hu a b hA⟩


theorem complexHessian_posDef_of_realBlockHessian [Fintype ι] [DecidableEq ι]
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) (a b : ι → E)
    (hR : (realBlockHessian a b u x).PosSemidef)
    (hdet : (complexHessian a b u x).det = 1) :
    (complexHessian a b u x).PosDef := by
  have hC := (actual_block_posSemidef_iff_complexification hu a b).mpr
    ((real_matrix_posSemidef_iff_complexification (realBlockHessian_isHermitian hu a b)).mp hR)
  have hA : (complexHessian a b u x).PosSemidef :=
    hC.submatrix (Sum.inl : ι → ι ⊕ ι)
  exact hA.posDef_iff_det_ne_zero.mpr (hdet ▸ one_ne_zero)

theorem real_matrix_posDef_iff_complexification [Fintype ι] [DecidableEq ι]
    {R : Matrix ι ι ℝ} (hR : R.IsHermitian) :
    R.PosDef ↔ (R.map Complex.ofReal).PosDef := by
  have hSemi := real_matrix_posSemidef_iff_complexification hR
  have hDet : (R.map Complex.ofReal).det = (R.det : ℂ) :=
    (Complex.ofRealHom.map_det R).symm
  constructor
  · intro h
    exact ((hSemi.mp h.posSemidef).posDef_iff_det_ne_zero).mpr
      (by rw [hDet]; exact Complex.ofReal_ne_zero.mpr (ne_of_gt h.det_pos))
  · intro h
    apply ((hSemi.mpr h.posSemidef).posDef_iff_det_ne_zero).mpr
    exact Complex.ofReal_ne_zero.mp (hDet ▸ ne_of_gt h.det_pos)

set_option maxHeartbeats 400000 in
theorem complexBlockHessian_posDef_iff [Fintype ι] [DecidableEq ι]
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) (a b : ι → E)
    (hA : (complexHessian a b u x).PosDef) :
    (complexBlockHessian a b u x).PosDef ↔ (schurHessian a b u x).PosDef := by
  let A := complexHessian a b u x
  let B := pureHessian a b u x
  let H := A.map star
  have hT : H = A.transpose := by
    ext i j
    exact (complexHessian_isHermitian hu a b).apply j i
  have hH : H.PosDef := hT ▸ hA.transpose
  have hHdet : H.det ≠ 0 := by rw [hT, Matrix.det_transpose]; exact ne_of_gt hA.det_pos
  letI : Invertible H := Matrix.invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr hHdet)
  have hDet : (complexBlockHessian a b u x).det = H.det * (schurHessian a b u x).det := by
    change (Matrix.fromBlocks A B (B.map star) H).det =
      H.det * (A - B * H⁻¹ * B.map star).det
    rw [Matrix.det_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv]
  have hNonzero :
      (complexBlockHessian a b u x).det ≠ 0 ↔ (schurHessian a b u x).det ≠ 0 := by
    rw [hDet, mul_ne_zero_iff]
    exact ⟨And.right, fun h => ⟨hHdet, h⟩⟩
  have hSemi := complexBlockHessian_posSemidef_iff hu a b hA
  constructor
  · intro h
    exact ((hSemi.mp h.posSemidef).posDef_iff_det_ne_zero).mpr
      (hNonzero.mp ((h.posSemidef.posDef_iff_det_ne_zero).mp h))
  · intro h
    exact ((hSemi.mpr h.posSemidef).posDef_iff_det_ne_zero).mpr
      (hNonzero.mpr ((h.posSemidef.posDef_iff_det_ne_zero).mp h))

theorem realBlockHessian_posDef_equivalences [Fintype ι] [DecidableEq ι]
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) (a b : ι → E)
    (hA : (complexHessian a b u x).PosDef) :
    ((realBlockHessian a b u x).PosDef ↔ (complexBlockHessian a b u x).PosDef) ∧
      ((complexBlockHessian a b u x).PosDef ↔ (schurHessian a b u x).PosDef) := by
  refine ⟨?_, complexBlockHessian_posDef_iff hu a b hA⟩
  rw [actual_block_congruence_scaled hu a b, Matrix.IsUnit.posDef_star_right_conjugate_iff
    (halfHessianTransform_isUnit (ι := ι))]
  exact real_matrix_posDef_iff_complexification (realBlockHessian_isHermitian hu a b)

/-- Real coefficient matrix of the complex linearization in the order
`(x₁,…,xₙ,y₁,…,yₙ)`. In particular the coefficient of the Euclidean
Laplacian at the identity is `1/4`. -/
noncomputable def realLinearizationMatrix (W : Matrix ι ι ℂ) :
    Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  (4 : ℝ)⁻¹ • Matrix.fromBlocks (W.transpose.map Complex.re)
    ((-W.transpose).map Complex.im) (W.transpose.map Complex.im)
    (W.transpose.map Complex.re)

theorem realLinearizationMatrix_pairing [Fintype ι]
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) (a b : ι → E)
    (W : Matrix ι ι ℂ) :
    (∑ p, ∑ q, W q p * complexHessian a b u x p q).re =
      ∑ i, ∑ j, realLinearizationMatrix W i j * realBlockHessian a b u x i j := by
  simp only [realLinearizationMatrix, Fintype.sum_sum_type, Matrix.smul_apply,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.map_apply,
    Matrix.neg_apply, Matrix.transpose_apply, Complex.neg_im, realBlockHessian, Sum.elim_inl, Sum.elim_inr,
    smul_eq_mul, Complex.re_sum]
  simp_rw [complexHessian_real_entry hu]
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, zero_mul, mul_zero, zero_add, add_zero,
    sub_self, one_mul, Complex.inv_re,
    Complex.inv_im, Complex.normSq_ofNat]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  norm_num
  ring




theorem realLinearizationMatrix_posDef [Fintype ι] {W : Matrix ι ι ℂ}
    (hW : W.PosDef) : (realLinearizationMatrix W).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · have hRe (i j : ι) : (W j i).re = (W i j).re := by
      simpa using congrArg Complex.re (hW.isHermitian.apply i j)
    have hIm (i j : ι) : -(W j i).im = (W i j).im := by
      simpa using congrArg Complex.im (hW.isHermitian.apply i j)
    ext (i | i) (j | j) <;>
      simp only [Matrix.conjTranspose_apply, star_trivial, realLinearizationMatrix,
        Matrix.smul_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.map_apply,
        Matrix.neg_apply, Matrix.transpose_apply, Complex.neg_im] <;>
      first | rw [hRe] | rw [hIm] | rw [← hIm]
  · intro v hv
    let z : ι → ℂ := fun i => ⟨v (.inl i), v (.inr i)⟩
    have hz : z ≠ 0 := by
      intro h
      apply hv
      funext i
      rcases i with i | i
      · exact congrArg Complex.re (congrFun h i)
      · exact congrArg Complex.im (congrFun h i)
    have hpos : 0 < (star z ⬝ᵥ W.transpose.mulVec z).re :=
      hW.transpose.re_dotProduct_pos hz
    have hform :
        star v ⬝ᵥ (realLinearizationMatrix W).mulVec v =
          (4 : ℝ)⁻¹ * (star z ⬝ᵥ W.transpose.mulVec z).re := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Complex.re_sum,
        Fintype.sum_sum_type, Pi.star_apply, star_trivial, realLinearizationMatrix,
        Matrix.smul_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.map_apply,
        Matrix.neg_apply, Matrix.transpose_apply, Complex.neg_im, smul_eq_mul,
        Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im,
        z, Finset.sum_add_distrib]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      have hfold (c d : ℝ) (F G : ι → ℝ) :
          c * (∑ j, F j) + d * (∑ j, G j) = ∑ j, (c * F j + d * G j) := by
        simp only [Finset.mul_sum, Finset.sum_add_distrib]
      rw [hfold]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hform]
    exact mul_pos (by norm_num) hpos

theorem realLinearizationMatrix_contDiffAt {W : E → Matrix ι ι ℂ} {x : E}
    {k : WithTop ℕ∞} (hW : ∀ i j, ContDiffAt ℝ k (fun y => W y i j) x)
    (i j : ι ⊕ ι) : ContDiffAt ℝ k (fun y => realLinearizationMatrix (W y) i j) x := by
  have hre i j := Complex.reCLM.contDiff.contDiffAt.comp x (hW j i)
  have him i j := Complex.imCLM.contDiff.contDiffAt.comp x (hW j i)
  rcases i with i | i <;> rcases j with j | j <;>
    simp only [realLinearizationMatrix, Matrix.smul_apply, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.map_apply, Matrix.neg_apply, Matrix.transpose_apply, Complex.neg_im, smul_eq_mul]
  · exact contDiffAt_const.mul (hre i j)
  · exact contDiffAt_const.mul (him i j).neg
  · exact contDiffAt_const.mul (him i j)
  · exact contDiffAt_const.mul (hre i j)

private theorem fderiv_comp_complex_at (l : ℂ →L[ℝ] ℝ)
    {f : E → ℂ} {x : E} (hf : DifferentiableAt ℝ f x) (v : E) :
    fderiv ℝ (fun y => l (f y)) x v = l (rd v f x) := by
  change fderiv ℝ (l ∘ f) x v = _
  rw [(l.hasFDerivAt.comp x hf.hasFDerivAt).fderiv]
  rfl

private theorem dz_real_parts (a b : E) (f : E → ℂ) (x : E) :
    (dz a b f x).re = (1 / 2) * ((rd a f x).re + (rd b f x).im) ∧
      (dz a b f x).im = (1 / 2) * ((rd a f x).im - (rd b f x).re) := by
  constructor <;>
    norm_num [dz, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.inv_re, Complex.inv_im, Complex.normSq_ofNat]

/-- Complex cofactor divergence implies column divergence of the real
coefficient matrix. The same column convention is used in the real
Hessian pairing. -/
theorem realLinearizationMatrix_divergence [Fintype ι]
    {W : E → Matrix ι ι ℂ} {x : E} (hW : MatrixDifferentiableAt W x) (a b : ι → E)
    (hdiv : ∀ j, (∑ i, dz (a i) (b i) (fun y => W y j i) x) = 0) (j : ι ⊕ ι) :
    (∑ i, fderiv ℝ (fun y => realLinearizationMatrix (W y) i j) x
      (Sum.elim a b i)) = 0 := by
  have hre (i j : ι) (v : E) :
      fderiv ℝ (fun y => (W y j i).re) x v = (rd v (fun y => W y j i) x).re :=
    fderiv_comp_complex_at Complex.reCLM (hW j i) v
  have him (i j : ι) (v : E) :
      fderiv ℝ (fun y => (W y j i).im) x v = (rd v (fun y => W y j i) x).im :=
    fderiv_comp_complex_at Complex.imCLM (hW j i) v
  have hdre (i j : ι) :
      DifferentiableAt ℝ (fun y => (W y j i).re) x :=
    (Complex.reCLM.hasFDerivAt.comp x (hW j i).hasFDerivAt).differentiableAt
  have hdim (i j : ι) :
      DifferentiableAt ℝ (fun y => (W y j i).im) x :=
    (Complex.imCLM.hasFDerivAt.comp x (hW j i).hasFDerivAt).differentiableAt
  rcases j with j | j
  · have hz := congrArg Complex.re (hdiv j)
    simp only [Complex.re_sum, (dz_real_parts _ _ _ _).1, Complex.zero_re,
      ← Finset.mul_sum, Finset.sum_add_distrib] at hz
    simp only [Fintype.sum_sum_type, realLinearizationMatrix, Matrix.smul_apply,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁, Matrix.map_apply,
      Matrix.transpose_apply, Sum.elim_inl, Sum.elim_inr, smul_eq_mul,
      fderiv_const_mul (hdre _ _), fderiv_const_mul (hdim _ _),
      smul_apply, hre, him, ← Finset.mul_sum]
    linarith
  · have hz := congrArg Complex.im (hdiv j)
    simp only [Complex.im_sum, (dz_real_parts _ _ _ _).2, Complex.zero_im,
      ← Finset.mul_sum, Finset.sum_sub_distrib] at hz
    have hleft (i : ι) :
        fderiv ℝ (fun y => (4 : ℝ)⁻¹ * -(W y j i).im) x (a i) =
          -(4 : ℝ)⁻¹ * (rd (a i) (fun y => W y j i) x).im := by
      have hfun : (fun y => (4 : ℝ)⁻¹ * -(W y j i).im) =
          (fun y => (-(4 : ℝ)⁻¹) * (W y j i).im) := by
        funext y
        rw [mul_neg, neg_mul]
      rw [hfun, fderiv_const_mul (hdim i j), smul_apply, smul_eq_mul, him]
    simp only [Fintype.sum_sum_type, realLinearizationMatrix, Matrix.smul_apply,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, Matrix.map_apply,
      Matrix.neg_apply, Matrix.transpose_apply, Complex.neg_im, Sum.elim_inl, Sum.elim_inr,
      smul_eq_mul, hleft, fderiv_const_mul (hdre _ _), smul_apply, hre, ← Finset.mul_sum]
    linarith

/-- On the local determinant-one locus, the real linearized coefficients
have zero column divergence. -/
theorem complexHessian_realLinearization_divergence [Fintype ι] [DecidableEq ι]
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 3 u x) (a b : ι → E)
    (hdet : (fun y => (complexHessian a b u y).det) =ᶠ[𝓝 x] (fun _ => (1 : ℂ)))
    (j : ι ⊕ ι) :
    (∑ i, fderiv ℝ (fun y => realLinearizationMatrix (complexHessian a b u y)⁻¹ i j) x
      (Sum.elim a b i)) = 0 :=
  realLinearizationMatrix_divergence
    (inverse_matrix_differentiableAt_of_det_one (complexHessian_differentiableAt hu a b) hdet)
    a b (complexHessian_inverse_divergence hu a b hdet) j

end CHS.Calculus
