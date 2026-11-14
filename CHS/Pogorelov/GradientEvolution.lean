import CHS.Pogorelov.GradientBound

/-!
# The contracted second derivative of the gradient square

Equation (2.30), `L G = a+d`, is obtained from the actual third derivatives
and the first derivative of `det A = 1`.  This identity needs C3 on the
open set, so it introduces no extra regularity into Theorem 1.1.
-/

set_option autoImplicit false
noncomputable section

open Matrix Filter
open scoped BigOperators ComplexOrder ContDiff Topology

namespace CHS.Pogorelov

open CHS.Calculus CHS.Algebra

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : ℕ}

private theorem third_reverse_ends {f : E → ℂ} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 3 f U) {x : E} (hx : x ∈ U)
    (a b c d e k : E) :
    dz a b (dz c d (dz e k f)) x = dz e k (dz c d (dz a b f)) x := by
  rw [third_inner_comm_on hU hf a b c d e k hx,
    third_outer_comm_at (hf.contDiffAt (hU.mem_nhds hx)) a b e k c d,
    third_inner_comm_on hU hf e k a b c d hx]

theorem gradient_trace_contraction (A B W : CMatrix n)
    (hB : ∀ i j, B i j = B j i) :
    (∑ i, ∑ p, ∑ q, W q p * (A i q * A p i + B p i * star (B q i))) =
      (A * W * A).trace + (B * W.transpose * B.conjTranspose).trace := by
  simp only [mul_add, Finset.sum_add_distrib]
  congr 1
  · simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    ring
  · simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    rw [hB i p, hB i q]
    ring

/-- The second identity in (2.30), in any of the constant real frames. -/
theorem gradientNormSq_evolution {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 3 u U) (a b : Fin n → E)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = 1)
    {x : E} (hx : x ∈ U) :
    linearizedScalar a b (complexHessian a b u x)⁻¹
      (fun y => (gradientNormSq a b u y : ℂ)) x =
      (complexHessian a b u x).trace + correctionTrace a b u x := by
  let f : E → ℂ := fun y => (u y : ℂ)
  let A := complexHessian a b u
  let B := pureHessian a b u
  let W := (A x)⁻¹
  let g (i : Fin n) := dz (a i) (b i) f
  have huc : ContDiffOn ℝ 3 f U := Complex.ofRealCLM.contDiff.comp_contDiffOn hu
  have hu3 := hu.contDiffAt (hU.mem_nhds hx)
  have hc3 := huc.contDiffAt (hU.mem_nhds hx)
  have hu2 : ContDiffAt ℝ 2 u x := hu3.of_le (by norm_num)
  have hc2 : ContDiffAt ℝ 2 f x := hc3.of_le (by norm_num)
  have hAreg : MatrixDifferentiableAt A x := complexHessian_differentiableAt hu3 a b
  have hBreg : MatrixDifferentiableAt B x := by
    intro i j
    exact (dz_contDiffAt_one (dz_contDiffAt_two hc3 (a j) (b j))
      (a i) (b i)).differentiableAt (by norm_num)
  have hg (i : Fin n) : DifferentiableAt ℝ (g i) x :=
    (dz_contDiffAt_two hc3 (a i) (b i)).differentiableAt (by norm_num)
  have hgs (i : Fin n) : DifferentiableAt ℝ (fun y => star (g i y)) x :=
    Complex.conjCLE.differentiableAt.comp x (hg i)
  have hdetnear : (fun y => (A y).det) =ᶠ[𝓝 x] fun _ => (1 : ℂ) :=
    Filter.eventually_of_mem (hU.mem_nhds hx) (fun y hy => hdet y hy)
  have hzero (i : Fin n) (s : E) :
      (∑ p, ∑ q, W q p * dz (a q) (-b q) (dz (a p) (b p) (dz (a i) s f)) x) = 0 := by
    calc
      _ = ∑ p, ∑ q, W q p * dz (a i) s (fun y => A y p q) x := by
        apply Finset.sum_congr rfl
        intro p _
        apply Finset.sum_congr rfl
        intro q _
        congr 1
        exact third_reverse_ends hU huc hx (a q) (-b q) (a p) (b p) (a i) s
      _ = 0 := complexHessian_det_one_first hu3 a b hdetnear (a i) s
  have hzeroA (i : Fin n) :
      (∑ p, ∑ q, W q p * dz (a q) (-b q) (fun y => A y p i) x) = 0 :=
    hzero i (-b i)
  have hzeroB (i : Fin n) :
      (∑ p, ∑ q, W q p * dz (a q) (-b q) (fun y => B y p i) x) = 0 :=
    hzero i (b i)
  have hfirst (p : Fin n) :
      dz (a p) (b p) (fun y => (gradientNormSq a b u y : ℂ)) =ᶠ[𝓝 x]
        fun y => ∑ i, (A y p i * g i y + B y p i * star (g i y)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    have hy2 : ContDiffAt ℝ 2 u y := (hu.contDiffAt (hU.mem_nhds hy)).of_le (by norm_num)
    have h := gradientNormSq_first_derivative hy2 a b p
    simpa only [Matrix.mulVec, dotProduct, Pi.star_apply,
      wirtingerGradient_eq_dz (hy2.differentiableAt (by norm_num)),
      Finset.sum_add_distrib, A, B, g, f] using h
  have hbar (i q : Fin n) : dz (a q) (-b q) (g i) x = A x i q := by
    exact dz_comm_at hc2 (a q) (-b q) (a i) (b i)
  have hbarstar (i q : Fin n) :
      dz (a q) (-b q) (fun y => star (g i y)) x = star (B x q i) :=
    dz_star_flip (a q) (b q) (g i) x
  have hsecond (p q : Fin n) :
      dz (a q) (-b q) (dz (a p) (b p)
          (fun y => (gradientNormSq a b u y : ℂ))) x =
        ∑ i, ((dz (a q) (-b q) (fun y => A y p i) x * g i x + A x p i * A x i q) +
          (dz (a q) (-b q) (fun y => B y p i) x * star (g i x) +
            B x p i * star (B x q i))) := by
    rw [dz_congr_nhds (hfirst p), dz_sum_at
      (f := fun i y => A y p i * g i y + B y p i * star (g i y))
      (fun i => ((hAreg p i).mul (hg i)).add ((hBreg p i).mul (hgs i)))]
    apply Finset.sum_congr rfl
    intro i _
    rw [dz_add_at (f := fun y => A y p i * g i y)
      (g := fun y => B y p i * star (g i y))
      ((hAreg p i).mul (hg i)) ((hBreg p i).mul (hgs i)),
      dz_mul_at (hAreg p i) (hg i), dz_mul_at (hBreg p i) (hgs i),
      hbar, hbarstar]
  have hthirdcancel (i : Fin n) :
      (∑ p, ∑ q, W q p *
        ((dz (a q) (-b q) (fun y => A y p i) x * g i x + A x p i * A x i q) +
          (dz (a q) (-b q) (fun y => B y p i) x * star (g i x) + B x p i * star (B x q i)))) =
      ∑ p, ∑ q, W q p * (A x i q * A x p i + B x p i * star (B x q i)) := by
    have hterm (p q : Fin n) : W q p *
        ((dz (a q) (-b q) (fun y => A y p i) x * g i x + A x p i * A x i q) +
          (dz (a q) (-b q) (fun y => B y p i) x * star (g i x) + B x p i * star (B x q i))) =
        (W q p * dz (a q) (-b q) (fun y => A y p i) x) * g i x +
        (W q p * dz (a q) (-b q) (fun y => B y p i) x) * star (g i x) +
        W q p * (A x i q * A x p i + B x p i * star (B x q i)) := by ring
    simp_rw [hterm]
    simp only [Finset.sum_add_distrib, ← Finset.sum_mul,
      hzeroA i, hzeroB i, zero_mul, zero_add]
  have hBsym (i j : Fin n) : B x i j = B x j i :=
    dz_comm_at hc2 (a i) (b i) (a j) (b j)
  have hAbar : (A x).map star = (A x).transpose := by
    ext i j
    exact (complexHessian_isHermitian hu2 a b).apply j i
  change linearizedScalar a b W (fun y => (gradientNormSq a b u y : ℂ)) x = _
  calc
    _ = ∑ p, ∑ q, ∑ i, W q p *
        ((dz (a q) (-b q) (fun y => A y p i) x * g i x + A x p i * A x i q) +
          (dz (a q) (-b q) (fun y => B y p i) x * star (g i x) + B x p i * star (B x q i))) := by
      simp only [linearizedScalar, hsecond, Finset.mul_sum]
    _ = ∑ i, ∑ p, ∑ q, W q p *
        ((dz (a q) (-b q) (fun y => A y p i) x * g i x + A x p i * A x i q) +
          (dz (a q) (-b q) (fun y => B y p i) x * star (g i x) + B x p i * star (B x q i))) := by
      calc
        _ = ∑ p, ∑ i, ∑ q, W q p *
            ((dz (a q) (-b q) (fun y => A y p i) x * g i x + A x p i * A x i q) +
              (dz (a q) (-b q) (fun y => B y p i) x * star (g i x) + B x p i * star (B x q i))) := by
          apply Finset.sum_congr rfl
          intro p _
          rw [Finset.sum_comm]
        _ = _ := by rw [Finset.sum_comm]
    _ = ∑ i, ∑ p, ∑ q, W q p * (A x i q * A x p i + B x p i * star (B x q i)) := by
      simp_rw [hthirdcancel]
    _ = (A x * W * A x).trace + (B x * W.transpose * (B x).conjTranspose).trace :=
      gradient_trace_contraction (A x) (B x) W hBsym
    _ = (A x).trace + correctionTrace a b u x := by
      rw [show A x * W = 1 from self_mul_inverse_of_det_one (A x) (hdet x hx), Matrix.one_mul,
        correctionTrace_eq, hAbar, Matrix.transpose_nonsing_inv,
        pureHessian_conjTranspose hu2 a b]

end CHS.Pogorelov
