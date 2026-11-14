import CHS.Pogorelov.GeneralEstimate

/-! # Compact real-translation quotient geometry passes to invariant subdomains -/

set_option autoImplicit false
noncomputable section

open Set

namespace CHS.Pogorelov

open CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

theorem compact_real_quotient_of_invariant_subdomain
    (K : Submodule ℝ E) {U V : Set E} (hVU : V ⊆ U)
    (hUinv : ∀ x ∈ U, ∀ v ∈ K, x + v ∈ U)
    (hVinv : ∀ x ∈ V, ∀ v ∈ K, x + v ∈ V)
    (hquot : IsCompact ((Submodule.Quotient.mk : E → E ⧸ K) '' closure U)) :
    IsCompact ((Submodule.Quotient.mk : E → E ⧸ K) '' closure V) := by
  obtain ⟨C, hC, _, hrep⟩ := compact_representatives_of_compact_real_quotient K hUinv hquot
  have heq : (Submodule.Quotient.mk : E → E ⧸ K) '' closure V =
      (Submodule.Quotient.mk : E → E ⧸ K) '' (C ∩ closure V) := by
    ext q
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hdiff⟩ := hrep x (closure_mono hVU hx)
      have hyv := translation_maps_closure K hVinv hdiff hx
      change x + (y - x) ∈ closure V at hyv
      have heqyx : x + (y - x) = y := by abel
      rw [heqyx] at hyv
      exact ⟨y, ⟨hy, hyv⟩, (Submodule.Quotient.eq K).mpr hdiff⟩
    · rintro ⟨y, hy, hq⟩
      exact ⟨y, hy.2, hq⟩
  rw [heq]
  exact (hC.inter_right isClosed_closure).image K.mkQL.continuous

end CHS.Pogorelov

namespace CHS

open Pogorelov

variable {n : ℕ}
local notation "E₀" => DeGiorgi.AmbientSpace (n + n)

theorem PogorelovCompactGeometry.lower_sublevel
    {u : E₀ → ℝ} {c d : ℝ} (hcd : c ≤ d)
    (hgeometry : PogorelovCompactGeometry {x | u x < d} u) :
    PogorelovCompactGeometry {x | u x < c} u := by
  have hsub : {x | u x < c} ⊆ {x | u x < d} := fun x hx => lt_of_lt_of_le hx hcd
  rcases hgeometry with hbounded | ⟨K, hUinv, huinv, hquot⟩
  · exact Or.inl (hbounded.subset hsub)
  · have hVinv : ∀ x ∈ {x | u x < c}, ∀ v ∈ K, x + v ∈ {x | u x < c} := by
      intro x hx v hv
      change u (x + v) < c
      rw [huinv x (hsub hx) v hv]
      exact hx
    exact Or.inr ⟨K, hVinv, fun x hx v hv => huinv x (hsub hx) v hv,
      compact_real_quotient_of_invariant_subdomain K hsub hUinv hVinv hquot⟩

end CHS
