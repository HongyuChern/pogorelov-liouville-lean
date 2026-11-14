import CHS.Calculus.CommonKernelDomination
import CHS.Calculus.QuadraticPerturbation
import CHS.Calculus.HessianQuadraticForm
import CHS.Calculus.SignPropagation
import CHS.Calculus.PotentialScalars

/-! # Quantitative real Hessian domination and complex positivity -/

set_option autoImplicit false
noncomputable section

open scoped ContDiff ComplexOrder

namespace CHS.Calculus

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem complexHessian_add {u v : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x) (a b : ι → E) :
    complexHessian a b (fun y => u y + v y) x =
      complexHessian a b u x + complexHessian a b v x := by
  ext i j
  rw [Matrix.add_apply, complexHessian_real_entry (hu.add hv),
    complexHessian_real_entry hu, complexHessian_real_entry hv]
  simp only [realHessian_add hu hv, add_apply, Complex.ofReal_add]
  ring

theorem complexHessian_domination_of_realHessian_domination [Fintype ι] [DecidableEq ι]
    {u q : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) (hq : ContDiffAt ℝ 2 q x)
    (a b : ι → E) (ε : ℝ)
    (hdom : ∀ v : E, ε * realHessian u x v v ≤ realHessian q x v v) :
    (complexHessian a b q x - ε • complexHessian a b u x).PosSemidef := by
  let f := fun y => q y + (-ε) * u y
  have hf : ContDiffAt ℝ 2 f x := hq.add (contDiffAt_const.mul hu)
  have hH : realHessian f x = realHessian q x + (-ε) • realHessian u x := by
    rw [realHessian_add hq (contDiffAt_const.mul hu), realHessian_const_mul]
  have hQ : ∀ v : E, 0 ≤ realHessian f x v v := by
    intro v
    rw [hH]
    change 0 ≤ realHessian q x v v + -ε * realHessian u x v v
    linarith [hdom v]
  have hR := realBlockHessian_posSemidef_of_quadratic_nonneg hf a b hQ
  have hA := complexHessian_posSemidef_of_realBlockHessian hf a b hR
  have heq : complexHessian a b f x = complexHessian a b q x - ε • complexHessian a b u x := by
    rw [complexHessian_add hq (contDiffAt_const.mul hu), complexHessian_const_mul,
      neg_smul, sub_eq_add_neg]
  rwa [heq] at hA

end CHS.Calculus

namespace CHS.Calculus

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] [Fintype ι] [DecidableEq ι]

theorem complexHessian_posDef_of_real_kernel_inclusion
    {u q : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) (hq : ContDiffAt ℝ 2 q x)
    (a b : ι → E) (hA : (complexHessian a b u x).PosDef)
    (hQ : ∀ v : E, 0 ≤ realHessian q x v v)
    (hker : (realHessian q x).ker ≤ (realHessian u x).ker) :
    ∃ ε : ℝ, 0 < ε ∧
      (complexHessian a b q x - ε • complexHessian a b u x).PosSemidef ∧
      (complexHessian a b q x).PosDef := by
  obtain ⟨ε, hε, hdom⟩ := exists_pos_realHessian_domination_of_kernel_inclusion
    hu hq hQ (realHessian q x).ker rfl hker
  have hdiff := complexHessian_domination_of_realHessian_domination hu hq a b ε hdom
  have hpos := (hA.smul hε).add_posSemidef hdiff
  have heq : ε • complexHessian a b u x +
      (complexHessian a b q x - ε • complexHessian a b u x) = complexHessian a b q x := by abel
  rw [heq] at hpos
  exact ⟨ε, hε, hdiff, hpos⟩

end CHS.Calculus
