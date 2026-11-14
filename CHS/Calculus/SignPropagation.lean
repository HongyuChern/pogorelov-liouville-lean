import CHS.Algebra.PositiveCone
import CHS.Calculus.PotentialNegation

/-!
# Propagation of the actual complex Hessian branch

The domain is explicitly preconnected.  A definite Hessian at one point
propagates because the actual Hessian is continuous and nonsingular.
The existence and rank properties of a perturbed extremum are separate.
-/

set_option autoImplicit false
noncomputable section

open Set Matrix
open scoped ContDiff ComplexOrder

namespace CHS.Calculus

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [Fintype ι] [DecidableEq ι]

theorem complexHessian_posSemidef_of_realBlockHessian {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (a b : ι → E)
    (hR : (realBlockHessian a b u x).PosSemidef) :
    (complexHessian a b u x).PosSemidef := by
  have hC := (actual_block_posSemidef_iff_complexification hu a b).mpr
    ((real_matrix_posSemidef_iff_complexification (realBlockHessian_isHermitian hu a b)).mp hR)
  exact hC.submatrix (Sum.inl : ι → ι ⊕ ι)

theorem complexHessian_posDef_of_realBlockHessian_det_ne_zero {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (a b : ι → E)
    (hR : (realBlockHessian a b u x).PosSemidef)
    (hdet : (complexHessian a b u x).det ≠ 0) :
    (complexHessian a b u x).PosDef :=
  (complexHessian_posSemidef_of_realBlockHessian hu a b hR).posDef_iff_det_ne_zero.mpr hdet

theorem complexHessian_posDef_on_of_at {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hconn : IsPreconnected U) (hu : ContDiffOn ℝ 4 u U)
    (a b : ι → E) (hdet : ∀ x ∈ U, (complexHessian a b u x).det ≠ 0)
    {x₀ : E} (hx₀ : x₀ ∈ U) (hpos : (complexHessian a b u x₀).PosDef) :
    ∀ x ∈ U, (complexHessian a b u x).PosDef := by
  letI : PreconnectedSpace U := Subtype.preconnectedSpace hconn
  have hA : Continuous (fun x : U => complexHessian a b u x) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    apply continuousOn_iff_continuous_restrict.mp
    intro x hx
    exact (complexHessian_contDiffAt_two (hu.contDiffAt (hU.mem_nhds hx))
      a b i j).continuousAt.continuousWithinAt
  have hherm (x : U) : (complexHessian a b u x).IsHermitian :=
    complexHessian_isHermitian ((hu.contDiffAt (hU.mem_nhds x.property)).of_le
      (by norm_num)) a b
  have hall := CHS.Algebra.posDef_everywhere_of_preconnected hA hherm
    (fun x => hdet x x.property) (x₀ := ⟨x₀, hx₀⟩) hpos
  intro x hx
  exact hall ⟨x, hx⟩

theorem complexHessian_neg_posDef_on_of_at {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hconn : IsPreconnected U) (hu : ContDiffOn ℝ 4 u U)
    (a b : ι → E) (hdet : ∀ x ∈ U, (complexHessian a b u x).det ≠ 0)
    {x₀ : E} (hx₀ : x₀ ∈ U) (hneg : (-complexHessian a b u x₀).PosDef) :
    ∀ x ∈ U, (-complexHessian a b u x).PosDef := by
  have hdetneg (x : E) (hx : x ∈ U) :
      (complexHessian a b (fun y => -u y) x).det ≠ 0 := by
    rw [complexHessian_neg, Matrix.det_neg]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (hdet x hx)
  have hpos : (complexHessian a b (fun y => -u y) x₀).PosDef := by
    rwa [complexHessian_neg]
  simpa only [complexHessian_neg] using
    complexHessian_posDef_on_of_at hU hconn hu.neg a b hdetneg hx₀ hpos

end CHS.Calculus
