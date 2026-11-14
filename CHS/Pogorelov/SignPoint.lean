import CHS.Algebra.SignBranch
import CHS.Calculus.SignPropagation
import CHS.Calculus.HessianQuadraticForm

/-!
# The negative-branch matrix sandwich at a real seminegative point

The original upper bound changes direction when the potential is negated.
At a point with nonnegative real Hessian for `-u`, Lemma 2.2 supplies the
opposite bound.  The resulting sandwich forces κ = 1 and zero Schur
complement at that point.
-/

set_option autoImplicit false
noncomputable section

open Set Matrix Filter
open scoped ContDiff ComplexOrder Topology

namespace CHS.Pogorelov

open CHS.Calculus CHS.Algebra

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem complexHessian_conjugate_det_isUnit
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) (a b : ι → E)
    (hdet : (complexHessian a b u x).det = 1) :
    IsUnit ((complexHessian a b u x).map star).det := by
  have hT : (complexHessian a b u x).map star = (complexHessian a b u x).transpose := by
    ext i j
    exact (complexHessian_isHermitian hu a b).apply j i
  rw [hT, Matrix.det_transpose, hdet]
  exact isUnit_one

theorem negative_branch_sandwich_at_point
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) (a b : ι → E)
    (hdet : (complexHessian a b u x).det = 1)
    (hR : (realBlockHessian a b (fun y => -u y) x).PosSemidef)
    {κ : ℝ} (hκ : 1 ≤ κ)
    (hmat : (κ • complexHessian a b u x -
      pureHessian a b u x * ((complexHessian a b u x).map star)⁻¹ *
        (pureHessian a b u x).map star).PosSemidef) :
    κ = 1 ∧ (complexHessian a b (fun y => -u y) x).PosDef ∧
      schurHessian a b (fun y => -u y) x = 0 := by
  have hdetw : (complexHessian a b (fun y => -u y) x).det ≠ 0 := by
    rw [complexHessian_neg, Matrix.det_neg, hdet, mul_one]
    exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have hA := complexHessian_posDef_of_realBlockHessian_det_ne_zero hu.neg a b hR hdetw
  let A := complexHessian a b (fun y => -u y) x
  let M := schurHessian a b (fun y => -u y) x
  let C := A - M
  have hbar := complexHessian_conjugate_det_isUnit hu a b hdet
  have hlo : (C - κ • A).PosSemidef := by
    have heq : C - κ • A = κ • complexHessian a b u x -
        pureHessian a b u x * ((complexHessian a b u x).map star)⁻¹ *
          (pureHessian a b u x).map star := by
      dsimp only [C, M, A]
      rw [complexHessian_neg, schurHessian_neg a b u x hbar, smul_neg]
      unfold schurHessian schurField
      abel
    rwa [heq]
  have hM : M.PosSemidef := by
    have heq := realBlockHessian_posSemidef_equivalences hu.neg a b hA
    exact heq.2.mp (heq.1.mp hR)
  have hhi : (A - C).PosSemidef := by simpa only [C, sub_sub_cancel] using hM
  obtain ⟨hk, hCA⟩ := schur_sandwich_forces_kappa_one hA hκ hlo hhi
  refine ⟨hk, hA, ?_⟩
  change M = 0
  have hcancel : A - C = 0 := sub_eq_zero.mpr hCA.symm
  simpa only [C, sub_sub_cancel] using hcancel

theorem exists_value_ne_zero_of_complex_det_one
    {U : Set E} (hU : IsOpen U) (hne : U.Nonempty) {u : E → ℝ}
    (hu : ContDiffOn ℝ 2 u U) (a b : ι → E)
    (hdet : ∀ x ∈ U, (complexHessian a b u x).det = 1) :
    ∃ x ∈ U, u x ≠ 0 := by
  by_contra! hz
  obtain ⟨x, hx⟩ := hne
  have heq : u =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) :=
    Filter.eventually_of_mem (hU.mem_nhds hx) (fun y hy => hz y hy)
  have hH : realHessian u x = 0 := by
    unfold realHessian
    rw [heq.fderiv.fderiv_eq]
    simp
  have hA : complexHessian a b u x = 0 := by
    ext i j
    rw [complexHessian_real_entry (hu.contDiffAt (hU.mem_nhds hx)), hH]
    simp
  have hd := hdet x hx
  rw [hA, Matrix.det_zero] at hd
  exact zero_ne_one hd

end CHS.Pogorelov
