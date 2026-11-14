import CHS.Pogorelov.WeightedMaximum

/-!
# Topological attainment for a continuous boundary extension

The compact-representative interface covers the topology needed both on a
compact closure and on a compact translation quotient.  This file does not
construct the continuous extension from C2 boundary jets, nor the compact
representatives from the quotient assumption.  Those analytic/geometric
obligations remain explicit.
-/

set_option autoImplicit false
noncomputable section

open Set Filter
open scoped Topology

namespace CHS.Pogorelov

variable {E : Type*} [TopologicalSpace E]

theorem exists_positive_interior_maximum_of_compact_representatives
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ closure U)
    {f : E → ℝ} (hf : ContinuousOn f (closure U))
    (hbd : ∀ x ∈ frontier U, f x = 0)
    (hrep : ∀ x ∈ closure U, ∃ y ∈ K, f x = f y)
    (hpositive : ∃ y ∈ U, 0 < f y) :
    ∃ x ∈ U, 0 < f x ∧ IsMaxOn f (closure U) x ∧ IsLocalMax f x := by
  obtain ⟨y, hy, hfy⟩ := hpositive
  obtain ⟨z, hz, _⟩ := hrep y (subset_closure hy)
  obtain ⟨x, hxK, hmaxK⟩ := hK.exists_isMaxOn ⟨z, hz⟩ (hf.mono hKU)
  have hx : x ∈ closure U := hKU hxK
  have hmax : IsMaxOn f (closure U) x := by
    intro w hw
    obtain ⟨v, hv, hwv⟩ := hrep w hw
    exact hwv.le.trans (hmaxK hv)
  have hfx : 0 < f x := hfy.trans_le (hmax (subset_closure hy))
  have hxU : x ∈ U := by
    by_contra hxU
    have hfront : x ∈ frontier U := hU.frontier_eq ▸ ⟨hx, hxU⟩
    rw [hbd x hfront] at hfx
    exact lt_irrefl _ hfx
  exact ⟨x, hxU, hfx, hmax,
    hmax.isLocalMax (Filter.mem_of_superset (hU.mem_nhds hxU) subset_closure)⟩

theorem exists_positive_interior_maximum_of_compact_closure
    {U : Set E} (hU : IsOpen U) (hK : IsCompact (closure U))
    {f : E → ℝ} (hf : ContinuousOn f (closure U))
    (hbd : ∀ x ∈ frontier U, f x = 0) (hpositive : ∃ y ∈ U, 0 < f y) :
    ∃ x ∈ U, 0 < f x ∧ IsMaxOn f (closure U) x ∧ IsLocalMax f x :=
  exists_positive_interior_maximum_of_compact_representatives hU hK Subset.rfl hf
    hbd (fun x hx => ⟨x, hx, rfl⟩) hpositive

/-- The extension need only agree with the test function on the open domain;
no derivatives of an arbitrary extension outside the closure are used. -/
theorem exists_interior_maximum_of_compact_extension
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ closure U)
    {f F : E → ℝ} (hF : ContinuousOn F (closure U)) (hmatch : Set.EqOn F f U)
    (hbd : ∀ x ∈ frontier U, F x = 0)
    (hrep : ∀ x ∈ closure U, ∃ y ∈ K, F x = F y)
    (hpositive : ∃ y ∈ U, 0 < f y) :
    ∃ x ∈ U, 0 < f x ∧ IsMaxOn f U x ∧ IsLocalMax f x := by
  have hposF : ∃ y ∈ U, 0 < F y := by
    obtain ⟨y, hy, hfy⟩ := hpositive
    exact ⟨y, hy, by rwa [hmatch hy]⟩
  obtain ⟨x, hx, hFx, hmaxF, _⟩ :=
    exists_positive_interior_maximum_of_compact_representatives hU hK hKU hF hbd hrep hposF
  have hmax : IsMaxOn f U x := by
    intro y hy
    change f y ≤ f x
    rw [← hmatch hy, ← hmatch hx]
    exact hmaxF (subset_closure hy)
  refine ⟨x, hx, ?_, hmax, hmax.isLocalMax (hU.mem_nhds hx)⟩
  rwa [hmatch hx] at hFx

end CHS.Pogorelov
