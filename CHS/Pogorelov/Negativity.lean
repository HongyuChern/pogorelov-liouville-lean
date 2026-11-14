import CHS.Calculus.HessianExtrema
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Strict negativity in the positive definite branch

The proof uses the actual real Hessian at an interior maximum.  Compact
representatives suffice, so the same argument applies to a bounded domain
and to a compact real-translation quotient.  No strict negativity or
maximum-principle conclusion is assumed as input.
-/

set_option autoImplicit false
noncomputable section

open Set Filter
open scoped ComplexOrder ContDiff Topology

namespace CHS.Pogorelov

open CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem not_isLocalMax_of_complexHessian_posDef {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (a b : ι → E)
    (hA : (complexHessian a b u x).PosDef) : ¬ IsLocalMax u x := by
  intro hmax
  let i : ι := Classical.choice inferInstance
  have ha := realHessian_nonpos_of_isLocalMax hu hmax (a i)
  have hb := realHessian_nonpos_of_isLocalMax hu hmax (b i)
  have hpos : 0 < (complexHessian a b u x i i).re :=
    (Complex.pos_iff.mp (hA.diag_pos (i := i))).1
  rw [complexHessian_real_entry hu] at hpos
  norm_num [Complex.mul_re, Complex.mul_im] at hpos
  linarith

theorem nonpos_on_closure_of_compact_representatives {u : E → ℝ} {U K : Set E}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ closure U)
    (hu : ContinuousOn u (closure U)) (hu₂ : ContDiffOn ℝ 2 u U)
    (a b : ι → E) (hA : ∀ x ∈ U, (complexHessian a b u x).PosDef)
    (hbd : ∀ x ∈ frontier U, u x = 0)
    (hrep : ∀ x ∈ closure U, ∃ y ∈ K, u x = u y) :
    ∀ x ∈ closure U, u x ≤ 0 := by
  intro x hx
  by_contra! hpos
  obtain ⟨z, hz, _⟩ := hrep x hx
  obtain ⟨p, hpK, hmaxK⟩ := hK.exists_isMaxOn ⟨z, hz⟩ (hu.mono hKU)
  have hp : p ∈ closure U := hKU hpK
  have hmax : IsMaxOn u (closure U) p := by
    intro y hy
    obtain ⟨q, hq, hyq⟩ := hrep y hy
    exact hyq.le.trans (hmaxK hq)
  have hpPos : 0 < u p := hpos.trans_le (hmax hx)
  have hpU : p ∈ U := by
    by_contra hpU
    rw [hbd p (hU.frontier_eq ▸ ⟨hp, hpU⟩)] at hpPos
    exact lt_irrefl _ hpPos
  exact not_isLocalMax_of_complexHessian_posDef
    (hu₂.contDiffAt (hU.mem_nhds hpU)) a b (hA p hpU)
    (hmax.isLocalMax (mem_of_superset (hU.mem_nhds hpU) subset_closure))

theorem neg_on_of_compact_representatives {u : E → ℝ} {U K : Set E}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ closure U)
    (hu : ContinuousOn u (closure U)) (hu₂ : ContDiffOn ℝ 2 u U)
    (a b : ι → E) (hA : ∀ x ∈ U, (complexHessian a b u x).PosDef)
    (hbd : ∀ x ∈ frontier U, u x = 0)
    (hrep : ∀ x ∈ closure U, ∃ y ∈ K, u x = u y) :
    ∀ x ∈ U, u x < 0 := by
  have hnonpos := nonpos_on_closure_of_compact_representatives
    hU hK hKU hu hu₂ a b hA hbd hrep
  intro x hx
  by_contra! hxzero
  have hzero : u x = 0 := le_antisymm (hnonpos x (subset_closure hx)) hxzero
  have hmax : IsMaxOn u U x := by
    intro y hy
    rw [hzero]
    exact hnonpos y (subset_closure hy)
  exact not_isLocalMax_of_complexHessian_posDef
    (hu₂.contDiffAt (hU.mem_nhds hx)) a b (hA x hx)
    (hmax.isLocalMax (hU.mem_nhds hx))

theorem neg_on_of_compact_closure {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hK : IsCompact (closure U))
    (hu : ContinuousOn u (closure U)) (hu₂ : ContDiffOn ℝ 2 u U)
    (a b : ι → E) (hA : ∀ x ∈ U, (complexHessian a b u x).PosDef)
    (hbd : ∀ x ∈ frontier U, u x = 0) : ∀ x ∈ U, u x < 0 :=
  neg_on_of_compact_representatives hU hK Subset.rfl hu hu₂ a b hA hbd
    (fun x hx => ⟨x, hx, rfl⟩)

end CHS.Pogorelov
