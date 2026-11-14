import CHS.Pogorelov.UnitaryTrace

/-!
# The actual squared Euclidean Wirtinger gradient

This file starts the next interface, equation (2.30).  The derivative formula
and regularity are proved here.  The contracted second derivative `L G = a+d`
is not assumed and is not an endpoint of this file.
-/

set_option autoImplicit false
noncomputable section

open Matrix Filter
open scoped BigOperators ComplexOrder ContDiff Topology

namespace CHS.Pogorelov

open CHS.Calculus CHS.Algebra

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : ℕ}

def gradientNormSq (a b : Fin n → E) (u : E → ℝ) (x : E) : ℝ :=
  ∑ i, Complex.normSq (dz (a i) (b i) (fun y => (u y : ℂ)) x)

theorem gradientNormSq_nonneg (a b : Fin n → E) (u : E → ℝ) (x : E) :
    0 ≤ gradientNormSq a b u x :=
  Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _

theorem gradientNormSq_complex (a b : Fin n → E) (u : E → ℝ) (x : E) :
    (gradientNormSq a b u x : ℂ) =
      ∑ i, dz (a i) (b i) (fun y => (u y : ℂ)) x *
        star (dz (a i) (b i) (fun y => (u y : ℂ)) x) := by
  simp only [gradientNormSq, Complex.ofReal_sum, Complex.star_def, Complex.mul_conj]

theorem gradientNormSq_eq_wirtinger {u : E → ℝ} {x : E}
    (hu : DifferentiableAt ℝ u x) (a b : Fin n → E) :
    gradientNormSq a b u x = vecSq (wirtingerGradient a b u x) := by
  simp only [gradientNormSq, vecSq, wirtingerGradient_eq_dz hu]

theorem gradientNormSq_contDiffAt_two {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 3 u x) (a b : Fin n → E) :
    ContDiffAt ℝ 2 (gradientNormSq a b u) x := by
  have huc : ContDiffAt ℝ 3 (fun y => (u y : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hu
  let g (i : Fin n) := dz (a i) (b i) (fun y => (u y : ℂ))
  have hg (i : Fin n) : ContDiffAt ℝ 2 (g i) x := dz_contDiffAt_two huc (a i) (b i)
  have hsum : ContDiffAt ℝ 2 (fun y => ∑ i, g i y * star (g i y)) x := by
    apply ContDiffAt.sum
    intro i _
    exact (hg i).mul (Complex.conjCLE.contDiff.contDiffAt.comp x (hg i))
  have heq : gradientNormSq a b u = fun y => (∑ i, g i y * star (g i y)).re := by
    funext y
    simp only [gradientNormSq, g, Complex.re_sum, Complex.star_def,
      Complex.mul_conj, Complex.ofReal_re]
  rw [heq]
  exact Complex.reCLM.contDiff.contDiffAt.comp x hsum

theorem potential_dz_star (a b : Fin n → E) (u : E → ℝ) (x : E) (i : Fin n) :
    star (dz (a i) (b i) (fun y => (u y : ℂ)) x) =
      dz (a i) (-b i) (fun y => (u y : ℂ)) x := by
  simpa only [Complex.star_def, Complex.conj_ofReal] using
    (dz_star_flip (a i) (b i) (fun y => (u y : ℂ)) x).symm

/-- The first-derivative identity in (2.30), with the manuscript's factor
`1/2` in every Wirtinger derivative. -/
theorem gradientNormSq_first_derivative {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (a b : Fin n → E) (p : Fin n) :
    dz (a p) (b p) (fun y => (gradientNormSq a b u y : ℂ)) x =
      (complexHessian a b u x).mulVec (wirtingerGradient a b u x) p +
        (pureHessian a b u x).mulVec (star (wirtingerGradient a b u x)) p := by
  have huc : ContDiffAt ℝ 2 (fun y => (u y : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hu
  let g (i : Fin n) := dz (a i) (b i) (fun y => (u y : ℂ))
  have hg (i : Fin n) : DifferentiableAt ℝ (g i) x :=
    (dz_contDiffAt_one huc (a i) (b i)).differentiableAt (by norm_num)
  have hgs (i : Fin n) : DifferentiableAt ℝ (fun y => star (g i y)) x :=
    Complex.conjCLE.differentiableAt.comp x (hg i)
  have hstar (i : Fin n) : (fun y => star (g i y)) =
      dz (a i) (-b i) (fun y => (u y : ℂ)) := by
    funext y
    exact potential_dz_star a b u y i
  have heq : (fun y => (gradientNormSq a b u y : ℂ)) =
      fun y => ∑ i, g i y * star (g i y) := by
    funext y
    exact gradientNormSq_complex a b u y
  rw [heq, dz_sum_at (f := fun i y => g i y * star (g i y))
    (fun i => (hg i).mul (hgs i))]
  simp only [Matrix.mulVec, dotProduct, Pi.star_apply,
    wirtingerGradient_eq_dz (hu.differentiableAt (by norm_num)),
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [dz_mul_at (hg i) (hgs i), hstar]
  change pureHessian a b u x p i * star (g i x) +
      g i x * complexHessian a b u x p i =
    complexHessian a b u x p i * g i x + pureHessian a b u x p i * star (g i x)
  ring

theorem vecSq_add_le_two (v w : CVector n) :
    vecSq (fun i => v i + w i) ≤ 2 * vecSq v + 2 * vecSq w := by
  have h := vecSq_add_le_sqrt v w
  have hv := Real.sq_sqrt (vecSq_nonneg v)
  have hw := Real.sq_sqrt (vecSq_nonneg w)
  nlinarith [sq_nonneg (Real.sqrt (vecSq v) - Real.sqrt (vecSq w))]

theorem vecSq_unitary (Q : CMatrix n) (v : CVector n)
    (hQ : Q.conjTranspose * Q = 1) : vecSq (Q.mulVec v) = vecSq v := by
  have hp (w : CVector n) : (star w ⬝ᵥ w).re = vecSq w := by
    simp only [dotProduct, Complex.re_sum, Pi.star_apply, vecSq]
    apply Finset.sum_congr rfl
    intro i _
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
  have hpair : star (Q.mulVec v) ⬝ᵥ Q.mulVec v = star v ⬝ᵥ v := by
    rw [Matrix.dotProduct_mulVec, Matrix.star_mulVec]
    rw [Matrix.vecMul_vecMul, hQ, Matrix.vecMul_one]
  rw [← hp (Q.mulVec v), hpair, hp v]

/-- Equality of the two functions, so that their first and second derivatives
can be compared without differentiating a variable frame. -/
theorem gradientNormSq_unitary_frame_eq (Q : CMatrix n) (a b : Fin n → E)
    (u : E → ℝ) (hQ : Q.conjTranspose * Q = 1) :
    gradientNormSq (complexFrameReal Q a b) (complexFrameImag Q a b) u =
      gradientNormSq a b u := by
  funext x
  change vecSq (fun i => dz (complexFrameReal Q a b i) (complexFrameImag Q a b i)
      (fun y => (u y : ℂ)) x) =
    vecSq (fun i => dz (a i) (b i) (fun y => (u y : ℂ)) x)
  have hvec : (fun i => dz (complexFrameReal Q a b i) (complexFrameImag Q a b i)
      (fun y => (u y : ℂ)) x) =
      Q.mulVec (fun i => dz (a i) (b i) (fun y => (u y : ℂ)) x) := by
    funext i
    exact dz_complexFrame Q a b _ x i
  rw [hvec, vecSq_unitary Q _ hQ]

theorem gradientNormSq_unitary_frame {u : E → ℝ} {x : E}
    (hu : DifferentiableAt ℝ u x) (Q : CMatrix n) (a b : Fin n → E)
    (hQ : Q.conjTranspose * Q = 1) :
    gradientNormSq (complexFrameReal Q a b) (complexFrameImag Q a b) u x =
      gradientNormSq a b u x := by
  exact congrFun (gradientNormSq_unitary_frame_eq Q a b u hQ) x

end CHS.Pogorelov
