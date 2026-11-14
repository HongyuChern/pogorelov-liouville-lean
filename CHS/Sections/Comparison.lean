import CHS.Algebra.DeterminantBounds
import CHS.Calculus.HessianExtrema

/-!
# Strict comparison for the complex Hessian determinant on a bounded domain
-/

set_option autoImplicit false

open Set
open scoped ComplexOrder ContDiff

namespace CHS.Sections

open CHS.Calculus CHS.Algebra

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A strict determinant supersolution that lies below the solution on the
boundary remains below it on the compact closure. -/
theorem le_on_closure_of_det_lt_of_compact_representatives
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ closure U)
    (a b : ι → E) {f g : E → ℝ}
    (hf : ContinuousOn f (closure U)) (hg : ContinuousOn g (closure U))
    (hf₂ : ContDiffOn ℝ 2 f U) (hg₂ : ContDiffOn ℝ 2 g U)
    (hpos : ∀ x ∈ U, (complexHessian a b f x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian a b g x).det < (complexHessian a b f x).det)
    (hbd : ∀ x ∈ frontier U, f x ≤ g x)
    (hrep : ∀ x ∈ closure U, ∃ y ∈ K, f x - g x = f y - g y) :
    ∀ x ∈ closure U, f x ≤ g x := by
  intro x hx
  by_contra! h
  let d (y : E) := f y - g y
  have hd : ContinuousOn d (closure U) := hf.sub hg
  obtain ⟨y, hy, hxy⟩ := hrep x hx
  obtain ⟨p, hpK, hpMaxK⟩ := hK.exists_isMaxOn ⟨y, hy⟩ (hd.mono hKU)
  have hp : p ∈ closure U := hKU hpK
  have hpMax : IsMaxOn d (closure U) p := by
    intro z hz
    obtain ⟨w, hw, hzw⟩ := hrep z hz
    exact hzw.le.trans (hpMaxK hw)
  have hpPos : 0 < d p := (sub_pos.mpr h).trans_le (hpMax hx)
  have hpU : p ∈ U := by
    by_contra hpU
    exact hpPos.not_ge (sub_nonpos.mpr (hbd p (hU.frontier_eq ▸ ⟨hp, hpU⟩)))
  have hpLocal : IsLocalMax d p :=
    hpMax.isLocalMax (Filter.mem_of_superset (hU.mem_nhds hpU) subset_closure)
  have hF := hf₂.contDiffAt (hU.mem_nhds hpU)
  have hG := hg₂.contDiffAt (hU.mem_nhds hpU)
  exact (hdet p hpU).not_ge
    (det_le_of_posDef_of_posSemidef_sub (hpos p hpU)
      (complexHessian_sub_posSemidef_of_isLocalMax hF hG hpLocal a b))


theorem le_on_closure_of_det_lt
    {U : Set E} (hU : IsOpen U) (hK : IsCompact (closure U))
    (a b : ι → E) {f g : E → ℝ}
    (hf : ContinuousOn f (closure U)) (hg : ContinuousOn g (closure U))
    (hf₂ : ContDiffOn ℝ 2 f U) (hg₂ : ContDiffOn ℝ 2 g U)
    (hpos : ∀ x ∈ U, (complexHessian a b f x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian a b g x).det < (complexHessian a b f x).det)
    (hbd : ∀ x ∈ frontier U, f x ≤ g x) : ∀ x ∈ closure U, f x ≤ g x :=
  le_on_closure_of_det_lt_of_compact_representatives hU hK Subset.rfl a b hf hg hf₂ hg₂
    hpos hdet hbd (fun x hx => ⟨x, hx, rfl⟩)

end CHS.Sections
