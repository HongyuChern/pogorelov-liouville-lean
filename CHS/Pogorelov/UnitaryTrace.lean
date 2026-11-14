import CHS.Calculus.ComplexFrame
import CHS.Pogorelov.TraceLog

/-!
# Unitary transfer of the Pogorelov logarithmic inequality

The frame is constant near the evaluation point.  In particular, no
derivatives of eigenvectors or of a point-dependent diagonalization occur.
-/

set_option autoImplicit false
noncomputable section

open Matrix Filter
open scoped BigOperators ComplexOrder ContDiff Topology

namespace CHS.Pogorelov

open CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {n : ℕ}

theorem matrix_conjugate_mul (A B : Matrix ι ι ℂ) :
    (A * B).map star = A.map star * B.map star :=
  Matrix.map_mul (f := starRingEnd ℂ)

theorem matrix_conjugate_one : (1 : Matrix ι ι ℂ).map star = 1 := by
  ext i j
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem matrix_conjugate_adjoint (Q : Matrix ι ι ℂ) :
    Q.conjTranspose.map star = Q.transpose := by
  ext i j
  simp

theorem matrix_conjugate_transpose (Q : Matrix ι ι ℂ) :
    Q.transpose.map star = Q.conjTranspose := rfl

theorem matrix_adjoint_conjugate (Q : Matrix ι ι ℂ) :
    (Q.map star).conjTranspose = Q.transpose := by
  ext i j
  simp

theorem conjugate_unitary (Q : Matrix ι ι ℂ)
    (hQ : Q.conjTranspose * Q = 1) (hQ' : Q * Q.conjTranspose = 1) :
    (Q.map star).conjTranspose * Q.map star = 1 ∧
      Q.map star * (Q.map star).conjTranspose = 1 := by
  constructor
  · have h := congrArg (fun M : Matrix ι ι ℂ => M.map star) hQ
    simpa only [matrix_conjugate_mul, matrix_conjugate_adjoint,
      matrix_conjugate_one, matrix_adjoint_conjugate] using h
  · have h := congrArg (fun M : Matrix ι ι ℂ => M.map star) hQ'
    simpa only [matrix_conjugate_mul, matrix_conjugate_adjoint,
      matrix_conjugate_one, matrix_adjoint_conjugate] using h

theorem unitary_schur_correction (Q A B : Matrix ι ι ℂ)
    (hQ : Q.conjTranspose * Q = 1) (hQ' : Q * Q.conjTranspose = 1)
    (hA : IsUnit (A.map star).det) :
    (Q * B * Q.transpose) * ((Q * A * Q.conjTranspose).map star)⁻¹ *
        (Q * B * Q.transpose).map star =
      Q * (B * (A.map star)⁻¹ * B.map star) * Q.conjTranspose := by
  obtain ⟨hR, hR'⟩ := conjugate_unitary Q hQ hQ'
  have hmapA : (Q * A * Q.conjTranspose).map star =
      Q.map star * A.map star * (Q.map star).conjTranspose := by
    rw [matrix_conjugate_mul, matrix_conjugate_mul,
      matrix_conjugate_adjoint, matrix_adjoint_conjugate]
  have hmapB : (Q * B * Q.transpose).map star =
      Q.map star * B.map star * Q.conjTranspose := by
    rw [matrix_conjugate_mul, matrix_conjugate_mul, matrix_conjugate_transpose]
  have hcancel : Q.transpose * Q.map star = 1 := by
    simpa only [matrix_adjoint_conjugate] using hR
  rw [hmapA, unitary_conjugate_inverse (Q.map star) (A.map star) hR hR' hA,
    hmapB, matrix_adjoint_conjugate]
  calc
    _ = Q * (B * (Q.transpose * Q.map star) * (A.map star)⁻¹ *
      (Q.transpose * Q.map star) * B.map star) * Q.conjTranspose := by noncomm_ring
    _ = _ := by simp only [hcancel, Matrix.mul_one, Matrix.one_mul]

theorem conjugate_complexHessian_isUnit {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (a b : ι → E)
    (hdet : (complexHessian a b u x).det = 1) :
    IsUnit ((complexHessian a b u x).map star).det := by
  have hT : (complexHessian a b u x).map star = (complexHessian a b u x).transpose := by
    ext i j
    exact (complexHessian_isHermitian hu a b).apply j i
  rw [hT, Matrix.det_transpose, hdet]
  exact isUnit_one

theorem correctionTrace_unitary_frame {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (Q : Matrix ι ι ℂ) (a b : ι → E)
    (hdet : (complexHessian a b u x).det = 1)
    (hQ : Q.conjTranspose * Q = 1) (hQ' : Q * Q.conjTranspose = 1) :
    correctionTrace (complexFrameReal Q a b) (complexFrameImag Q a b) u x =
      correctionTrace a b u x := by
  simp only [correctionTrace_eq, complexHessian_complexFrame hu, pureHessian_complexFrame hu]
  rw [
    unitary_schur_correction Q _ _ hQ hQ' (conjugate_complexHessian_isUnit hu a b hdet),
    unitary_conjugate_trace Q _ hQ]

theorem traceCombination_unitary_frame {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (Q : Matrix ι ι ℂ) (a b : ι → E)
    (hdet : (complexHessian a b u x).det = 1)
    (hQ : Q.conjTranspose * Q = 1) (hQ' : Q * Q.conjTranspose = 1) (c : ℝ) :
    traceCombination (complexFrameReal Q a b) (complexFrameImag Q a b) u c x =
      traceCombination a b u c x := by
  unfold traceCombination
  rw [complexHessian_complexFrame hu, unitary_conjugate_trace Q _ hQ,
    correctionTrace_unitary_frame hu Q a b hdet hQ hQ']

theorem schur_bound_unitary_frame {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (Q : Matrix ι ι ℂ) (a b : ι → E)
    (hdet : (complexHessian a b u x).det = 1)
    (hQ : Q.conjTranspose * Q = 1) (hQ' : Q * Q.conjTranspose = 1)
    (κ : ℝ) (hmat : (κ • complexHessian a b u x -
      pureHessian a b u x * ((complexHessian a b u x).map star)⁻¹ *
        (pureHessian a b u x).map star).PosSemidef) :
    let a' := complexFrameReal Q a b
    let b' := complexFrameImag Q a b
    (κ • complexHessian a' b' u x -
      pureHessian a' b' u x * ((complexHessian a' b' u x).map star)⁻¹ *
        (pureHessian a' b' u x).map star).PosSemidef := by
  dsimp only
  simp only [complexHessian_complexFrame hu, pureHessian_complexFrame hu]
  rw [
    unitary_schur_correction Q _ _ hQ hQ' (conjugate_complexHessian_isUnit hu a b hdet)]
  have h := hmat.mul_mul_conjTranspose_same Q
  simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul] using h

theorem wirtingerGradient_complexFrame {f : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (Q : Matrix ι ι ℂ) (a b : ι → E) :
    wirtingerGradient (complexFrameReal Q a b) (complexFrameImag Q a b) f x =
      Q.mulVec (wirtingerGradient a b f x) := by
  funext i
  simp only [wirtingerGradient_eq_dz hf, dz_complexFrame, Matrix.mulVec, dotProduct]

/-- Spectral diagonalization expressed in the precise convention used by
`complexFrameReal` and `complexFrameImag`. -/
theorem exists_unitary_diagonal_squares {A : Matrix ι ι ℂ} (hA : A.PosDef) :
    ∃ (Q : Matrix ι ι ℂ) (r : ι → ℝ),
      Q.conjTranspose * Q = 1 ∧ Q * Q.conjTranspose = 1 ∧
      (∀ i, 0 < r i) ∧ Q * A * Q.conjTranspose = diagonal (fun i => (r i : ℂ) ^ 2) := by
  let V := hA.isHermitian.eigenvectorUnitary
  let P : Matrix ι ι ℂ := V
  let D := diagonal (fun i => (hA.isHermitian.eigenvalues i : ℂ))
  let r : ι → ℝ := fun i => Real.sqrt (hA.isHermitian.eigenvalues i)
  have hP : P.conjTranspose * P = 1 := by
    change star (↑V : Matrix ι ι ℂ) * (↑V : Matrix ι ι ℂ) = 1
    exact Unitary.coe_star_mul_self V
  have hP' : P * P.conjTranspose = 1 := by
    change (↑V : Matrix ι ι ℂ) * star (↑V : Matrix ι ι ℂ) = 1
    simpa only [Unitary.coe_star] using Unitary.coe_mul_star_self V
  have hspec : A = P * D * P.conjTranspose := by
    simpa only [Unitary.conjStarAlgAut_apply, P, D, V, Function.comp_def,
      star_eq_conjTranspose, RCLike.ofReal_eq_complex_ofReal] using
      hA.isHermitian.spectral_theorem
  refine ⟨P.conjTranspose, r, ?_, ?_, ?_, ?_⟩
  · simpa only [Matrix.conjTranspose_conjTranspose] using hP'
  · simpa only [Matrix.conjTranspose_conjTranspose] using hP
  · intro i
    exact Real.sqrt_pos.mpr (hA.eigenvalues_pos i)
  · rw [Matrix.conjTranspose_conjTranspose, hspec]
    calc
      _ = (P.conjTranspose * P) * D * (P.conjTranspose * P) := by noncomm_ring
      _ = D := by simp only [hP, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by
        dsimp only [D]
        congr 1
        funext i
        dsimp only [r]
        rw [← Complex.ofReal_pow, Real.sq_sqrt (hA.eigenvalues_pos i).le]

/-- Equation (2.28) in the original frame.  The diagonalizing unitary is
chosen at `x` and is then kept constant throughout all differentiations. -/
theorem traceCombination_log_bound {u : E → ℝ} {U : Set E}
    (hn : 2 ≤ n) (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : Fin n → E)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = 1)
    {x : E} (hx : x ∈ U) (hpos : (complexHessian a b u x).PosDef)
    {κ : ℝ} (hκ : 1 ≤ κ)
    (hmat : (κ • complexHessian a b u x -
      pureHessian a b u x * ((complexHessian a b u x).map star)⁻¹ *
        (pureHessian a b u x).map star).PosSemidef) :
    let S := traceCombination a b u (cChoice n κ)
    let W := (complexHessian a b u x)⁻¹
    let g := wirtingerGradient a b (fun y => Real.log (S y)) x
    (1 / (beta n κ - 1)) * (star g ⬝ᵥ W.mulVec g).re ≤
      (linearizedScalar a b W (fun y => (Real.log (S y) : ℂ)) x).re := by
  obtain ⟨Q, r, hQ, hQ', hr, hdiag⟩ := exists_unitary_diagonal_squares hpos
  let a' := complexFrameReal Q a b
  let b' := complexFrameImag Q a b
  let S := traceCombination a b u (cChoice n κ)
  let S' := traceCombination a' b' u (cChoice n κ)
  let W := (complexHessian a b u x)⁻¹
  have hu2 (y : E) (hy : y ∈ U) : ContDiffAt ℝ 2 u y :=
    (hu.contDiffAt (hU.mem_nhds hy)).of_le (by norm_num)
  have hdet' (y : E) (hy : y ∈ U) : (complexHessian a' b' u y).det = 1 := by
    rw [complexHessian_complexFrame (hu2 y hy), unitary_conjugate_determinant Q _ hQ']
    exact hdet y hy
  have hdiag' : complexHessian a' b' u x = diagonal (fun i => (r i : ℂ) ^ 2) := by
    rw [complexHessian_complexFrame (hu2 x hx)]
    exact hdiag
  have hpos' : (complexHessian a' b' u x).PosDef := by
    rw [hdiag']
    apply Matrix.PosDef.diagonal
    intro i
    rw [← Complex.ofReal_pow]
    exact_mod_cast (sq_pos_of_pos (hr i))
  have hmat' := schur_bound_unitary_frame (hu2 x hx) Q a b (hdet x hx) hQ hQ' κ hmat
  have hW' : (complexHessian a' b' u x)⁻¹ = Q * W * Q.conjTranspose := by
    rw [complexHessian_complexFrame (hu2 x hx)]
    exact unitary_conjugate_inverse Q _ hQ hQ' (hdet x hx ▸ isUnit_one)
  have hSS : Set.EqOn S' S U := by
    intro y hy
    exact traceCombination_unitary_frame (hu2 y hy) Q a b (hdet y hy) hQ hQ' _
  have hreg : ContDiffAt ℝ 2 S x :=
    (traceCombination_contDiffOn hU hu a b hdet _).contDiffAt (hU.mem_nhds hx)
  have hSpos : 0 < S x := by
    letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    have htr : 0 < (complexHessian a b u x).trace.re := by
      have h := hpos.trace_pos
      rw [← ofReal_trace_re_of_isHermitian hpos.isHermitian] at h
      exact_mod_cast h
    have hm : (κ • complexHessian a b u x -
        (complexHessian a b u x - schurHessian a b u x)).PosSemidef := by
      change (κ • complexHessian a b u x - (_ - (_ - _))).PosSemidef
      rw [sub_sub_cancel]
      exact hmat
    have hd := (schur_correction_trace_bounds (hu2 x hx) a b hpos κ hm).1
    exact add_pos_of_pos_of_nonneg (mul_pos (cChoice_pos hn hκ) htr) hd
  have hlogreg : ContDiffAt ℝ 2 (fun y => Real.log (S y)) x := hreg.log hSpos.ne'
  have hlog : Set.EqOn (fun y => Real.log (S' y)) (fun y => Real.log (S y)) U :=
    fun y hy => congrArg Real.log (hSS hy)
  have hgrad : wirtingerGradient a' b' (fun y => Real.log (S' y)) x =
      wirtingerGradient a' b' (fun y => Real.log (S y)) x := by
    have hnear : (fun y => Real.log (S' y)) =ᶠ[𝓝 x] fun y => Real.log (S y) :=
      Filter.eventually_of_mem (hU.mem_nhds hx) (fun y hy => hlog hy)
    unfold wirtingerGradient
    rw [hnear.fderiv_eq]
  have hscalar : linearizedScalar a' b' (complexHessian a' b' u x)⁻¹
      (fun y => (Real.log (S' y) : ℂ)) x =
      linearizedScalar a b W (fun y => (Real.log (S y) : ℂ)) x := by
    rw [linearizedScalar_congr_on hU (fun y hy => congrArg Complex.ofReal (hlog hy)) hx,
      hW', linearizedScalar_unitary_frame hlogreg Q W a b hQ]
  have h := diagonal_traceCombination_log_bound hn hU hu a' b' hdet' hx hpos' r hr
    hdiag' hκ hmat'
  change (1 / (beta n κ - 1)) *
    (star (wirtingerGradient a' b' (fun y => Real.log (S' y)) x) ⬝ᵥ
      (complexHessian a' b' u x)⁻¹.mulVec
        (wirtingerGradient a' b' (fun y => Real.log (S' y)) x)).re ≤
    (linearizedScalar a' b' (complexHessian a' b' u x)⁻¹
      (fun y => (Real.log (S' y) : ℂ)) x).re at h
  rw [hscalar, hgrad, hW',
    wirtingerGradient_complexFrame (hlogreg.differentiableAt (by norm_num)),
    unitary_covector_pairing Q W _ hQ] at h
  exact h

end CHS.Pogorelov
