import CHS.Calculus.CofactorDivergence

/-!
# Actual mixed and pure complex Hessians

The derivatives use the same constant real directions and normalization as
`FiniteWirtinger`. The mixed Hessian's inverse divergence follows at local
`C³` regularity from row commutation and the determinant-one equation.
-/

set_option autoImplicit false
open scoped BigOperators ContDiff Topology

namespace CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*}

noncomputable def complexHessian (a b : ι → E) (u : E → ℝ) (x : E) :
    Matrix ι ι ℂ :=
  fun i j => dz (a i) (b i) (dz (a j) (-b j) (fun y => (u y : ℂ))) x

noncomputable def pureHessian (a b : ι → E) (u : E → ℝ) (x : E) :
    Matrix ι ι ℂ :=
  fun i j => dz (a i) (b i) (dz (a j) (b j) (fun y => (u y : ℂ))) x

theorem complexHessian_differentiableAt {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 3 u x) (a b : ι → E) :
    MatrixDifferentiableAt (complexHessian a b u) x := by
  intro i j
  have huc : ContDiffAt ℝ 3 (fun y => (u y : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hu
  exact (dz_contDiffAt_one (dz_contDiffAt_two huc (a j) (-b j))
    (a i) (b i)).differentiableAt (by norm_num)

theorem complexHessian_contDiffAt_two {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 4 u x) (a b : ι → E) (i j : ι) :
    ContDiffAt ℝ 2 (fun y => complexHessian a b u y i j) x := by
  have huc : ContDiffAt ℝ 4 (fun y => (u y : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hu
  exact dz_contDiffAt_two (dz_contDiffAt_three huc (a j) (-b j)) (a i) (b i)

theorem pureHessian_contDiffAt_two {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 4 u x) (a b : ι → E) (i j : ι) :
    ContDiffAt ℝ 2 (fun y => pureHessian a b u y i j) x := by
  have huc : ContDiffAt ℝ 4 (fun y => (u y : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hu
  exact dz_contDiffAt_two (dz_contDiffAt_three huc (a j) (b j)) (a i) (b i)

theorem complexHessian_row_comm {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 3 u x) (a b : ι → E) (i r k : ι) :
    dz (a i) (b i) (fun y => complexHessian a b u y r k) x =
      dz (a r) (b r) (fun y => complexHessian a b u y i k) x := by
  have huc : ContDiffAt ℝ 3 (fun y => (u y : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hu
  exact third_outer_comm_at huc (a i) (b i) (a r) (b r) (a k) (-b k)

/-- The determinant-one equation differentiated in any constant Wirtinger direction. -/
theorem complexHessian_det_one_first [Fintype ι] [DecidableEq ι]
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 3 u x) (a b : ι → E)
    (hdet : (fun y => (complexHessian a b u y).det) =ᶠ[𝓝 x] (fun _ => (1 : ℂ)))
    (v w : E) :
    (∑ i, ∑ j, (complexHessian a b u x)⁻¹ j i *
      dz v w (fun y => complexHessian a b u y i j) x) = 0 := by
  have hx : (complexHessian a b u x).det = 1 := hdet.eq_of_nhds
  rw [inv_eq_adjugate_of_det_one _ hx,
    ← dz_det_field (complexHessian_differentiableAt hu a b) v w,
    dz_congr_nhds hdet v w, dz_const]

theorem complexHessian_inverse_divergence [Fintype ι] [DecidableEq ι]
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 3 u x) (a b : ι → E)
    (hdet : (fun y => (complexHessian a b u y).det) =ᶠ[𝓝 x] (fun _ => (1 : ℂ)))
    (j : ι) :
    (∑ i, dz (a i) (b i) (fun y => (complexHessian a b u y)⁻¹ j i) x) = 0 :=
  inverse_divergence_of_commuting_rows a b (complexHessian_differentiableAt hu a b)
    (complexHessian_row_comm hu a b) hdet j

end CHS.Calculus
