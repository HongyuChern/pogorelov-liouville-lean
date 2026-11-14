import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Interior extrema after a strict quadratic perturbation

Compact representatives of the pair `(u,q)` suffice.  In the bounded case
one takes `q(x) = ‖x‖²`; in the cylindrical case one takes the squared norm
of the orthogonal projection.  The size of the perturbation is produced
from the positive value of `u` and compactness, rather than assumed.
-/

set_option autoImplicit false
noncomputable section

open Set Filter
open scoped Topology

namespace CHS.Pogorelov

variable {E : Type*} [TopologicalSpace E]

theorem exists_pos_perturbation_interior_max
    {U C : Set E} (hU : IsOpen U) (hC : IsCompact C) (hCU : C ⊆ closure U)
    {u q : E → ℝ} (hu : ContinuousOn u (closure U)) (hq : ContinuousOn q (closure U))
    (hq0 : ∀ x ∈ closure U, 0 ≤ q x)
    (hbd : ∀ x ∈ frontier U, u x = 0)
    (hrep : ∀ x ∈ closure U, ∃ y ∈ C, u x = u y ∧ q x = q y)
    {x₀ : E} (hx₀ : x₀ ∈ U) (hu₀ : 0 < u x₀) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ p ∈ U,
      IsMaxOn (fun x => u x + ε * q x) (closure U) p ∧
      IsLocalMax (fun x => u x + ε * q x) p := by
  obtain ⟨y₀, hy₀, _, _⟩ := hrep x₀ (subset_closure hx₀)
  obtain ⟨M, hM⟩ := hC.bddAbove_image (hq.mono hCU)
  have hM0 : 0 ≤ M := (hq0 y₀ (hCU hy₀)).trans (hM (mem_image_of_mem q hy₀))
  let ε := u x₀ / (2 * (M + 1))
  have hε : 0 < ε := div_pos hu₀ (by positivity)
  have hεeq : ε * (2 * (M + 1)) = u x₀ :=
    div_mul_cancel₀ _ (by positivity : (2 : ℝ) * (M + 1) ≠ 0)
  have hgap : ε * M < u x₀ := by nlinarith
  let F := fun x => u x + ε * q x
  have hF : ContinuousOn F (closure U) := hu.add (continuousOn_const.mul hq)
  obtain ⟨p, hpC, hpMax⟩ := hC.exists_isMaxOn ⟨y₀, hy₀⟩ (hF.mono hCU)
  have hmax : IsMaxOn F (closure U) p := by
    intro x hx
    obtain ⟨y, hy, huy, hqy⟩ := hrep x hx
    change u x + ε * q x ≤ u p + ε * q p
    rw [huy, hqy]
    exact hpMax hy
  have hbase : u x₀ ≤ F x₀ := by
    dsimp [F]
    exact le_add_of_nonneg_right (mul_nonneg hε.le (hq0 x₀ (subset_closure hx₀)))
  have hpU : p ∈ U := by
    by_contra hpU
    have hpbd : p ∈ frontier U := hU.frontier_eq ▸ ⟨hCU hpC, hpU⟩
    have hpq : q p ≤ M := hM (mem_image_of_mem q hpC)
    have hplow : u x₀ ≤ F p := hbase.trans (hmax (subset_closure hx₀))
    change u x₀ ≤ u p + ε * q p at hplow
    rw [hbd p hpbd, zero_add] at hplow
    exact (not_lt_of_ge (hplow.trans (mul_le_mul_of_nonneg_left hpq hε.le))) hgap
  exact ⟨ε, hε, p, hpU, hmax,
    hmax.isLocalMax (mem_of_superset (hU.mem_nhds hpU) subset_closure)⟩

theorem exists_neg_perturbation_interior_min
    {U C : Set E} (hU : IsOpen U) (hC : IsCompact C) (hCU : C ⊆ closure U)
    {u q : E → ℝ} (hu : ContinuousOn u (closure U)) (hq : ContinuousOn q (closure U))
    (hq0 : ∀ x ∈ closure U, 0 ≤ q x)
    (hbd : ∀ x ∈ frontier U, u x = 0)
    (hrep : ∀ x ∈ closure U, ∃ y ∈ C, u x = u y ∧ q x = q y)
    {x₀ : E} (hx₀ : x₀ ∈ U) (hu₀ : u x₀ < 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ p ∈ U,
      IsMinOn (fun x => u x - ε * q x) (closure U) p ∧
      IsLocalMin (fun x => u x - ε * q x) p := by
  obtain ⟨ε, hε, p, hp, hmax, hlocal⟩ := exists_pos_perturbation_interior_max
    hU hC hCU (u := fun x => -u x) hu.neg hq hq0
    (fun x hx => by change -u x = 0; rw [hbd x hx, neg_zero])
    (fun x hx => by
      obtain ⟨y, hy, huy, hqy⟩ := hrep x hx
      exact ⟨y, hy, congrArg Neg.neg huy, hqy⟩) hx₀ (neg_pos.mpr hu₀)
  refine ⟨ε, hε, p, hp, ?_, ?_⟩
  · intro x hx
    have h := hmax hx
    change -u x + ε * q x ≤ -u p + ε * q p at h
    change u p - ε * q p ≤ u x - ε * q x
    linarith
  · filter_upwards [hlocal] with x hx
    change -u x + ε * q x ≤ -u p + ε * q p at hx
    change u p - ε * q p ≤ u x - ε * q x
    linarith

end CHS.Pogorelov
