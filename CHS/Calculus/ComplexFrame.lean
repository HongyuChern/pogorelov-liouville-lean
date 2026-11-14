import CHS.Pogorelov.TraceField

/-!
# Constant complex changes of the real directional frame

The two real blocks are transformed separately.  If the new Wirtinger
directions are `∂'_i = ∑ j, Q i j ∂_j`, then the actual mixed Hessian
transforms by `Q A Q*`, while the pure Hessian transforms by `Q B Qᵀ`.
-/

set_option autoImplicit false
noncomputable section

open Matrix Filter
open scoped BigOperators ContDiff Topology

namespace CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def complexFrameReal (Q : Matrix ι ι ℂ) (a b : ι → E) (i : ι) : E :=
  ∑ j, ((Q i j).re • a j + (Q i j).im • b j)

def complexFrameImag (Q : Matrix ι ι ℂ) (a b : ι → E) (i : ι) : E :=
  ∑ j, ((Q i j).re • b j - (Q i j).im • a j)

private theorem complex_frame_scalar (z v w : ℂ) :
    (2 : ℂ)⁻¹ * ((z.re : ℂ) * v + (z.im : ℂ) * w -
      Complex.I * ((z.re : ℂ) * w - (z.im : ℂ) * v)) =
      z * ((2 : ℂ)⁻¹ * (v - Complex.I * w)) := by
  conv_rhs => rw [← Complex.re_add_im z]
  ring_nf
  simp only [Complex.I_sq]
  <;> ring

/-- The first derivative transformation is unconditional: even the total
Fréchet derivative used in the definitions is linear in its direction. -/
theorem dz_complexFrame (Q : Matrix ι ι ℂ) (a b : ι → E)
    (f : E → ℂ) (x : E) (i : ι) :
    dz (complexFrameReal Q a b i) (complexFrameImag Q a b i) f x =
      ∑ j, Q i j * dz (a j) (b j) f x := by
  simp only [complexFrameReal, complexFrameImag, dz, rd, map_sum, map_add,
    map_sub, map_smul, Complex.real_smul]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact complex_frame_scalar (Q i j) (fderiv ℝ f x (a j)) (fderiv ℝ f x (b j))

theorem complexFrameReal_conjugate (Q : Matrix ι ι ℂ) (a b : ι → E) :
    complexFrameReal (Q.map star) a (fun j => -b j) = complexFrameReal Q a b := by
  funext i
  simp [complexFrameReal, Complex.star_def, Complex.conj_re, Complex.conj_im]

theorem complexFrameImag_conjugate (Q : Matrix ι ι ℂ) (a b : ι → E) :
    complexFrameImag (Q.map star) a (fun j => -b j) =
      fun i => -complexFrameImag Q a b i := by
  funext i
  simp only [complexFrameImag, Matrix.map_apply, Complex.star_def,
    Complex.conj_re, Complex.conj_im, smul_neg, neg_smul, sub_neg_eq_add,
    ← Finset.sum_neg_distrib, neg_sub]
  apply Finset.sum_congr rfl
  intro j _
  abel

theorem dz_conjugate_complexFrame (Q : Matrix ι ι ℂ) (a b : ι → E)
    (f : E → ℂ) (x : E) (i : ι) :
    dz (complexFrameReal Q a b i) (-complexFrameImag Q a b i) f x =
      ∑ j, star (Q i j) * dz (a j) (-b j) f x := by
  simpa only [complexFrameReal_conjugate, complexFrameImag_conjugate,
    Matrix.map_apply] using dz_complexFrame (Q.map star) a (fun j => -b j) f x i

/-- Covariance of the actual pure Hessian; the right factor is a transpose. -/
theorem pureHessian_complexFrame {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (Q : Matrix ι ι ℂ) (a b : ι → E) :
    pureHessian (complexFrameReal Q a b) (complexFrameImag Q a b) u x =
      Q * pureHessian a b u x * Q.transpose := by
  have huc : ContDiffAt ℝ 2 (fun y => (u y : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hu
  ext i j
  have hinner : dz (complexFrameReal Q a b j) (complexFrameImag Q a b j)
      (fun y => (u y : ℂ)) =
      fun y => ∑ k, Q j k * dz (a k) (b k) (fun z => (u z : ℂ)) y := by
    funext y
    exact dz_complexFrame Q a b _ y j
  change dz (complexFrameReal Q a b i) (complexFrameImag Q a b i)
    (dz (complexFrameReal Q a b j) (complexFrameImag Q a b j)
      (fun y => (u y : ℂ))) x = _
  rw [hinner, dz_sum_at]
  · simp only [Matrix.mul_apply, Matrix.transpose_apply]
    apply Finset.sum_congr rfl
    intro k _
    rw [CHS.Pogorelov.dz_const_mul_at
      ((dz_contDiffAt_one huc (a k) (b k)).differentiableAt (by norm_num)),
      dz_complexFrame, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l _
    change Q j k * (Q i l * pureHessian a b u x l k) =
      Q i l * pureHessian a b u x l k * Q j k
    ring
  · intro k
    exact ((dz_contDiffAt_one huc (a k) (b k)).differentiableAt
      (by norm_num)).const_mul _

/-- Covariance of the actual mixed Hessian. -/
theorem complexHessian_complexFrame {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (Q : Matrix ι ι ℂ) (a b : ι → E) :
    complexHessian (complexFrameReal Q a b) (complexFrameImag Q a b) u x =
      Q * complexHessian a b u x * Q.conjTranspose := by
  have huc : ContDiffAt ℝ 2 (fun y => (u y : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hu
  ext i j
  have hinner : dz (complexFrameReal Q a b j) (-complexFrameImag Q a b j)
      (fun y => (u y : ℂ)) =
      fun y => ∑ k, star (Q j k) * dz (a k) (-b k) (fun z => (u z : ℂ)) y := by
    funext y
    exact dz_conjugate_complexFrame Q a b _ y j
  change dz (complexFrameReal Q a b i) (complexFrameImag Q a b i)
    (dz (complexFrameReal Q a b j) (-complexFrameImag Q a b j)
      (fun y => (u y : ℂ))) x = _
  rw [hinner, dz_sum_at]
  · simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    apply Finset.sum_congr rfl
    intro k _
    rw [CHS.Pogorelov.dz_const_mul_at
      ((dz_contDiffAt_one huc (a k) (-b k)).differentiableAt (by norm_num)),
      dz_complexFrame, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l _
    change star (Q j k) * (Q i l * complexHessian a b u x l k) =
      Q i l * complexHessian a b u x l k * star (Q j k)
    ring
  · intro k
    exact ((dz_contDiffAt_one huc (a k) (-b k)).differentiableAt
      (by norm_num)).const_mul _

end CHS.Calculus

namespace CHS.Pogorelov

open CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem unitary_conjugate_trace (Q M : Matrix ι ι ℂ)
    (hQ : Q.conjTranspose * Q = 1) : (Q * M * Q.conjTranspose).trace = M.trace := by
  rw [Matrix.trace_mul_comm (Q * M), ← Matrix.mul_assoc, hQ, Matrix.one_mul]

theorem unitary_conjugate_mul (Q X Y : Matrix ι ι ℂ)
    (hQ : Q.conjTranspose * Q = 1) :
    (Q * X * Q.conjTranspose) * (Q * Y * Q.conjTranspose) =
      Q * (X * Y) * Q.conjTranspose := by
  calc
    _ = Q * (X * (Q.conjTranspose * Q) * Y) * Q.conjTranspose := by noncomm_ring
    _ = _ := by rw [hQ, Matrix.mul_one]

theorem unitary_conjugate_inverse (Q A : Matrix ι ι ℂ)
    (hQ : Q.conjTranspose * Q = 1) (hQ' : Q * Q.conjTranspose = 1)
    (hA : IsUnit A.det) :
    (Q * A * Q.conjTranspose)⁻¹ = Q * A⁻¹ * Q.conjTranspose := by
  apply Matrix.inv_eq_right_inv
  rw [unitary_conjugate_mul Q A A⁻¹ hQ, Matrix.mul_nonsing_inv A hA,
    Matrix.mul_one, hQ']

theorem unitary_conjugate_determinant (Q A : Matrix ι ι ℂ)
    (hQ' : Q * Q.conjTranspose = 1) :
    (Q * A * Q.conjTranspose).det = A.det := by
  have hdet : Q.det * Q.conjTranspose.det = 1 := by
    rw [← Matrix.det_mul, hQ', Matrix.det_one]
  rw [Matrix.det_mul, Matrix.det_mul, mul_right_comm, hdet, one_mul]

/-- The inverse metric and covector must be transformed together. -/
theorem unitary_covector_pairing (Q W : Matrix ι ι ℂ) (v : ι → ℂ)
    (hQ : Q.conjTranspose * Q = 1) :
    star (Q.mulVec v) ⬝ᵥ (Q * W * Q.conjTranspose).mulVec (Q.mulVec v) =
      star v ⬝ᵥ W.mulVec v := by
  rw [CHS.WeightedSquares.pairing_product]
  have hv : Q.conjTranspose.mulVec (Q.mulVec v) = v := by
    rw [Matrix.mulVec_mulVec, hQ, Matrix.one_mulVec]
  rw [hv]

/-- Invariance of the real scalar linearization in a constant unitary frame. -/
theorem linearizedScalar_unitary_frame {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (Q W : Matrix ι ι ℂ) (a b : ι → E)
    (hQ : Q.conjTranspose * Q = 1) :
    linearizedScalar (complexFrameReal Q a b) (complexFrameImag Q a b)
      (Q * W * Q.conjTranspose) (fun y => (f y : ℂ)) x =
      linearizedScalar a b W (fun y => (f y : ℂ)) x := by
  rw [linearizedScalar_ofReal_eq_trace hf, complexHessian_complexFrame hf,
    unitary_conjugate_mul Q W _ hQ, unitary_conjugate_trace Q _ hQ,
    linearizedScalar_ofReal_eq_trace hf]

end CHS.Pogorelov
