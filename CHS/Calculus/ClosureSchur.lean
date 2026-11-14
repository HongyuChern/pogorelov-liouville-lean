import CHS.Calculus.ClosureHessian
import CHS.Pogorelov.BoundaryExtension
import CHS.Calculus.QuadraticPerturbation

/-!
# Schur algebra for genuine C2 boundary jets

The second derivative jet is symmetric on the closure by density.  At
each closure point a concrete quadratic realizes exactly that bilinear
form. This transfers the existing real/complex Schur equivalence without
assuming an ambient smooth extension of the original potential.
-/

set_option autoImplicit false
noncomputable section

open Set Matrix
open scoped ContDiff ComplexOrder

namespace CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def bilinearQuadratic (H : E →L[ℝ] E →L[ℝ] ℝ) (x : E) : ℝ :=
  (1 / 2 : ℝ) * H x x

theorem contDiff_bilinearQuadratic (H : E →L[ℝ] E →L[ℝ] ℝ) (k : ℕ∞ω) :
    ContDiff ℝ k (bilinearQuadratic H) := by
  exact contDiff_const.mul (H.contDiff.clm_apply contDiff_id)

theorem realHessian_bilinearQuadratic (H : E →L[ℝ] E →L[ℝ] ℝ)
    (hsym : ∀ v w, H v w = H w v) (x : E) :
    realHessian (bilinearQuadratic H) x = H := by
  have hD : fderiv ℝ (fun y => H y y) = ⇑((2 : ℝ) • H) := by
    funext y
    have hd := H.hasFDerivAt.clm_apply (hasFDerivAt_id y)
    simp only [id_eq] at hd
    rw [hd.fderiv]
    ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      _root_.add_apply, _root_.smul_apply, smul_eq_mul]
    change H y v + H v y = 2 * H y v
    rw [hsym v y]
    ring
  change realHessian (fun y => (1 / 2 : ℝ) * H y y) x = H
  rw [realHessian_const_mul]
  unfold realHessian
  rw [hD, ((2 : ℝ) • H).fderiv, smul_smul]
  norm_num

namespace ClosureC2Jet

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {u : E → ℝ} {U : Set E}

theorem hessian_symmetric_on_closure (J : ClosureC2Jet u U)
    (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U) {x : E} (hx : x ∈ closure U) :
    ∀ v w : E, J.hessian x v w = J.hessian x w v := by
  intro v w
  have heq : EqOn (fun y => J.hessian y v w) (fun y => J.hessian y w v) U := by
    intro y hy
    change J.hessian y v w = J.hessian y w v
    rw [J.hessian_eq hy]
    exact realHessian_symm (hu.contDiffAt (hU.mem_nhds hy)) v w
  exact heq.of_subset_closure
    ((J.continuous_hessian.clm_apply continuousOn_const).clm_apply continuousOn_const)
    ((J.continuous_hessian.clm_apply continuousOn_const).clm_apply continuousOn_const)
    subset_closure Subset.rfl hx

def schurField (J : ClosureC2Jet u U) (a b : ι → E) (x : E) : Matrix ι ι ℂ :=
  J.complexField a b x - J.pureField a b x *
    ((J.complexField a b x).map star).adjugate * (J.pureField a b x).map star

theorem continuousOn_schurField (J : ClosureC2Jet u U) (a b : ι → E) :
    ContinuousOn (J.schurField a b) (closure U) := by
  have hA := J.continuousOn_complexField a b
  have hB := J.continuousOn_pureField a b
  unfold schurField
  fun_prop

theorem schurField_eq (J : ClosureC2Jet u U) (a b : ι → E)
    {x : E} (hx : x ∈ U) (hu : ContDiffAt ℝ 2 u x)
    (hdet : (complexHessian a b u x).det = 1) :
    J.schurField a b x = schurHessian a b u x := by
  have hT : (complexHessian a b u x).map star = (complexHessian a b u x).transpose := by
    ext i j
    exact (complexHessian_isHermitian hu a b).apply j i
  have hD : ((complexHessian a b u x).map star).det = 1 := by
    rw [hT, Matrix.det_transpose, hdet]
  simp only [schurField, J.complexField_eq hx hu a b, J.pureField_eq hx hu a b]
  change _ = complexHessian a b u x - pureHessian a b u x *
    ((complexHessian a b u x).map star)⁻¹ * (pureHessian a b u x).map star
  rw [inv_eq_adjugate_of_det_one _ hD]

theorem fields_eq_quadratic (J : ClosureC2Jet u U)
    (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U) (a b : ι → E)
    {x : E} (hx : x ∈ closure U) :
    J.realField a b x = realBlockHessian a b (bilinearQuadratic (J.hessian x)) 0 ∧
      J.complexField a b x = complexHessian a b (bilinearQuadratic (J.hessian x)) 0 ∧
      J.pureField a b x = pureHessian a b (bilinearQuadratic (J.hessian x)) 0 := by
  have hH := realHessian_bilinearQuadratic (J.hessian x)
    (J.hessian_symmetric_on_closure hU hu hx) (0 : E)
  have hq := (contDiff_bilinearQuadratic (J.hessian x) 2).contDiffAt (x := (0 : E))
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    change J.hessian x _ _ = realHessian _ 0 _ _
    rw [hH]
  · ext i j
    rw [complexHessian_real_entry hq, hH]
    rfl
  · ext i j
    rw [pureHessian_real_entry hq, hH]
    rfl

theorem realField_posSemidef_iff_schurField (J : ClosureC2Jet u U)
    (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U) (a b : ι → E)
    {x : E} (hx : x ∈ closure U) (hA : (J.complexField a b x).PosDef)
    (hdet : (J.complexField a b x).det = 1) :
    (J.realField a b x).PosSemidef ↔ (J.schurField a b x).PosSemidef := by
  obtain ⟨hR, hAc, hB⟩ := J.fields_eq_quadratic hU hu a b hx
  let q := bilinearQuadratic (J.hessian x)
  have hq : ContDiffAt ℝ 2 q (0 : E) := (contDiff_bilinearQuadratic _ 2).contDiffAt
  have hAq : (complexHessian a b q 0).PosDef := hAc ▸ hA
  have hT : (complexHessian a b q 0).map star = (complexHessian a b q 0).transpose := by
    ext i j
    exact (complexHessian_isHermitian hq a b).apply j i
  have hD : ((complexHessian a b q 0).map star).det = 1 := by
    rw [hT, Matrix.det_transpose, ← hAc]
    exact hdet
  have hM : J.schurField a b x = schurHessian a b q 0 := by
    simp only [schurField, hAc, hB]
    change _ = complexHessian a b q 0 - pureHessian a b q 0 *
      ((complexHessian a b q 0).map star)⁻¹ * (pureHessian a b q 0).map star
    rw [inv_eq_adjugate_of_det_one _ hD]
  rw [hR, hM]
  obtain ⟨h₁, h₂⟩ := realBlockHessian_posSemidef_equivalences hq a b hAq
  exact h₁.trans h₂

end ClosureC2Jet
end CHS.Calculus
