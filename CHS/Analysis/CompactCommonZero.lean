import CHS.Analysis.SimultaneousNearMinima

/-!
# A common zero in a compact range closure

This compactness step converts simultaneous finite approximation into a
single common zero for an arbitrary family of nonnegative continuous
observables.  In the Liouville argument the observables are directional
Hessian deficits on the compact closure of the actual Hessian range.
-/

set_option autoImplicit false
noncomputable section

open Set
open scoped BigOperators

namespace CHS.Analysis

theorem common_zero_of_compact_finite_approximation
    {X ι : Type*} [TopologicalSpace X] {S : Set X}
    (hS : IsCompact S) (hne : S.Nonempty) (f : ι → X → ℝ)
    (hf : ∀ i, Continuous (f i)) (hnonneg : ∀ i x, x ∈ S → 0 ≤ f i x)
    (happrox : ∀ s : Finset ι, ∀ ε : ℝ, 0 < ε →
      ∃ x ∈ S, ∑ i ∈ s, f i x < ε) :
    ∃ x ∈ S, ∀ i, f i x = 0 := by
  classical
  obtain ⟨x, hxS, hx⟩ := hS.inter_iInter_nonempty (fun i => {x | f i x = 0})
    (fun i => isClosed_eq (hf i) continuous_const) (by
      intro s
      have hc : Continuous (fun x => ∑ i ∈ s, f i x) :=
        continuous_finset_sum _ fun i _ => hf i
      obtain ⟨y, hyS, hymin⟩ := hS.exists_isMinOn hne hc.continuousOn
      have hsum0 : (∑ i ∈ s, f i y) = 0 := by
        apply le_antisymm
        · by_contra! hpos
          obtain ⟨z, hzS, hz⟩ := happrox s _ hpos
          exact (not_lt_of_ge (hymin hzS)) hz
        · exact Finset.sum_nonneg fun i _ => hnonneg i y hyS
      refine ⟨y, hyS, ?_⟩
      simp only [mem_iInter, mem_setOf_eq]
      intro i hi
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnonneg j y hyS)).mp hsum0 i hi)
  exact ⟨x, hxS, by simpa only [mem_iInter, mem_setOf_eq] using hx⟩

end CHS.Analysis
