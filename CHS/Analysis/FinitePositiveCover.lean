import CHS.Analysis.CompactCommonZero

/-! # A finite positive family on a compact set -/

set_option autoImplicit false
noncomputable section

open Set
open scoped BigOperators

namespace CHS.Analysis

theorem finite_positive_sum_lower_bound_on_compact
    {X I : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    (f : I → X → ℝ) (hf : ∀ i, Continuous (f i))
    (hpos : ∀ x ∈ K, ∃ i, 0 < f i x) :
    ∃ t : Finset I, ∃ c : ℝ, 0 < c ∧
      ∀ x ∈ K, c ≤ ∑ i ∈ t, max (f i x) 0 := by
  classical
  by_cases hne : K.Nonempty
  · obtain ⟨t, ht⟩ := hK.elim_finite_subcover
      (fun i => {x | 0 < f i x}) (fun i => isOpen_lt continuous_const (hf i)) (by
        intro x hx
        obtain ⟨i, hi⟩ := hpos x hx
        exact mem_iUnion.mpr ⟨i, hi⟩)
    let g : X → ℝ := fun x => ∑ i ∈ t, max (f i x) 0
    have hg : Continuous g := by
      apply continuous_finset_sum
      intro i _
      exact (hf i).max continuous_const
    have hgpos (x : X) (hx : x ∈ K) : 0 < g x := by
      obtain ⟨i, hit, hi⟩ := mem_iUnion₂.mp (ht hx)
      exact lt_of_lt_of_le (hi.trans_le (le_max_left _ _))
        (Finset.single_le_sum (fun j _ => le_max_right _ _) hit)
    obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hne hg.continuousOn
    exact ⟨t, g x, hgpos x hx, fun y hy => hmin hy⟩
  · exact ⟨∅, 1, zero_lt_one, fun x hx => False.elim (hne ⟨x, hx⟩)⟩

end CHS.Analysis
