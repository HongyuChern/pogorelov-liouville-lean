import CHS.Calculus.MatrixCalculusRules

/-!
# Finite regularity of the actual inverse on the constant determinant locus

The inverse regularity used below is proved through the polynomial adjugate.
In particular, C2 of the Schur field is a consequence of C4 of the potential,
not a separately assumed field in the PDE data. S002 UNCOMPILED candidates.
-/
set_option autoImplicit false
open scoped BigOperators ContDiff Topology Matrix.Norms.Elementwise
namespace CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual determinant as a continuous multilinear map in its rows. -/
noncomputable def determinantPolynomial :
    ContinuousMultilinearMap ℂ (fun _ : ι => ι → ℂ) ℂ where
  toMultilinearMap := Matrix.detRowAlternating.toMultilinearMap
  cont := continuous_id.matrix_det

@[simp] lemma determinantPolynomial_apply (A : Matrix ι ι ℂ) :
    determinantPolynomial A = A.det := rfl

lemma complex_det_contDiff {k : WithTop ℕ∞} :
    ContDiff ℝ k (Matrix.det : Matrix ι ι ℂ → ℂ) := by
  have entry (i j : ι) : ContDiff ℝ k (fun A : Matrix ι ι ℂ => A i j) :=
    (contDiff_pi.mp (contDiff_pi.mp contDiff_id i)) j
  change ContDiff ℝ k (fun A : Matrix ι ι ℂ => A.det)
  simp only [Matrix.det_apply']
  refine ContDiff.sum (fun σ _ => contDiff_const.mul ?_)
  exact contDiff_prod (fun i _ => entry (σ i) i)

lemma field_det_contDiffAt {k : WithTop ℕ∞} {G : E → Matrix ι ι ℂ} {x : E}
    (hG : ∀ i j, ContDiffAt ℝ k (fun y => G y i j) x) :
    ContDiffAt ℝ k (fun y => (G y).det) x := by
  exact complex_det_contDiff.contDiffAt.comp x
    (contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr (hG i))

lemma field_adjugate_contDiffAt {k : WithTop ℕ∞} {G : E → Matrix ι ι ℂ} {x : E}
    (hG : ∀ i j, ContDiffAt ℝ k (fun y => G y i j) x) (i j : ι) :
    ContDiffAt ℝ k (fun y => (G y).adjugate i j) x := by
  simp_rw [Matrix.adjugate_apply]
  apply field_det_contDiffAt
  intro r s
  by_cases hr : r = j
  · subst r
    simp only [Matrix.updateRow_self]
    exact contDiffAt_const
  · simpa only [Matrix.updateRow_ne hr] using hG r s

lemma field_inverse_contDiffAt_of_det_one {k : WithTop ℕ∞}
    {G : E → Matrix ι ι ℂ} {x : E}
    (hG : ∀ i j, ContDiffAt ℝ k (fun y => G y i j) x)
    (hdet : (fun y => (G y).det) =ᶠ[𝓝 x] (fun _ => (1 : ℂ))) (i j : ι) :
    ContDiffAt ℝ k (fun y => (G y)⁻¹ i j) x := by
  apply (field_adjugate_contDiffAt hG i j).congr_of_eventuallyEq
  exact hdet.mono fun y hy => by
    simp only [inv_eq_adjugate_of_det_one (G y) hy]

lemma matrix_product_contDiffAt {k : WithTop ℕ∞}
    {G H : E → Matrix ι ι ℂ} {x : E}
    (hG : ∀ i j, ContDiffAt ℝ k (fun y => G y i j) x)
    (hH : ∀ i j, ContDiffAt ℝ k (fun y => H y i j) x) (i j : ι) :
    ContDiffAt ℝ k (fun y => (G y * H y) i j) x := by
  change ContDiffAt ℝ k (fun y => ∑ s, G y i s * H y s j) x
  exact ContDiffAt.sum (fun s _ => (hG i s).mul (hH s j))


/- The C1 versions below are reconstructed in S004. They are consequences
of the actual determinant polynomial; they do not assume C1 of the inverse. -/
lemma field_det_differentiableAt {G : E → Matrix ι ι ℂ} {x : E}
    (hG : MatrixDifferentiableAt G x) :
    DifferentiableAt ℝ (fun y => (G y).det) x := by
  have hdet : DifferentiableAt ℝ (Matrix.det : Matrix ι ι ℂ → ℂ) (G x) :=
    (complex_det_contDiff (k := 1)).contDiffAt.differentiableAt (by norm_num)
  exact hdet.comp x (differentiableAt_pi.mpr fun i => differentiableAt_pi.mpr (hG i))

lemma field_adjugate_differentiableAt {G : E → Matrix ι ι ℂ} {x : E}
    (hG : MatrixDifferentiableAt G x) (i j : ι) :
    DifferentiableAt ℝ (fun y => (G y).adjugate i j) x := by
  simp_rw [Matrix.adjugate_apply]
  apply field_det_differentiableAt
  intro r s
  by_cases hr : r = j
  · subst r
    simp only [Matrix.updateRow_self]
    exact differentiableAt_const _
  · simpa only [Matrix.updateRow_ne hr] using hG r s

/-- Public derivative interface consumed by the preserved S002 graph proof.
Local determinant one is sufficient; global invertibility is not assumed. -/
lemma inverse_matrix_differentiableAt_of_det_one
    {G : E → Matrix ι ι ℂ} {x : E}
    (hG : MatrixDifferentiableAt G x)
    (hdet : (fun y => (G y).det) =ᶠ[𝓝 x] (fun _ => (1 : ℂ))) :
    MatrixDifferentiableAt (fun y => (G y)⁻¹) x := by
  intro i j
  apply (field_adjugate_differentiableAt hG i j).congr_of_eventuallyEq
  exact hdet.mono fun y hy => by
    simp only [inv_eq_adjugate_of_det_one (G y) hy]

end CHS.Calculus
