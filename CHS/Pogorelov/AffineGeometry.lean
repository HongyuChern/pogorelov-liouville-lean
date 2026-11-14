import CHS.Pogorelov.GeneralEstimate

/-!
# Bounded and compact real-quotient geometry under affine equivalences

Compactness is transported using actual compact representatives and the
actual quotient map.  The transformed translation space is the inverse
image of the original real subspace under the linear equivalence.
-/

set_option autoImplicit false
noncomputable section

open Set

namespace CHS.Pogorelov

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

theorem compact_real_quotient_affine_preimage
    (T : E ≃L[ℝ] E) (c : E) (K : Submodule ℝ E) {U : Set E}
    (hUinv : ∀ x ∈ U, ∀ v ∈ K, x + v ∈ U)
    (hquot : IsCompact ((Submodule.Quotient.mk : E → E ⧸ K) '' closure U)) :
    IsCompact ((Submodule.Quotient.mk : E → E ⧸ (K.comap T.toLinearMap)) ''
      closure {x | c + T x ∈ U}) := by
  let V : Set E := {x | c + T x ∈ U}
  let ψ : E → E := fun y => T.symm (y - c)
  have hψ : Continuous ψ := T.symm.continuous.comp (continuous_id.sub continuous_const)
  have hpψ (y : E) : c + T (ψ y) = y := by simp [ψ]
  have hforward : MapsTo (fun x => c + T x) V U := fun x hx => hx
  have hforwardC := hforward.closure (continuous_const.add T.continuous)
  have hback : MapsTo ψ U V := by
    intro y hy
    change c + T (ψ y) ∈ U
    rwa [hpψ]
  have hbackC := hback.closure hψ
  obtain ⟨C, hC, hCU, hrep⟩ := compact_representatives_of_compact_real_quotient K hUinv hquot
  let C' := ψ '' C
  have hC' : IsCompact C' := hC.image hψ
  have hCV : C' ⊆ closure V := by
    rintro y ⟨z, hz, rfl⟩
    exact hbackC (hCU hz)
  have hrep' : ∀ x ∈ closure V, ∃ y ∈ C', y - x ∈ K.comap T.toLinearMap := by
    intro x hx
    obtain ⟨y, hy, hdiff⟩ := hrep (c + T x) (hforwardC hx)
    refine ⟨ψ y, mem_image_of_mem ψ hy, ?_⟩
    change T (ψ y - x) ∈ K
    dsimp only [ψ]
    rw [map_sub, T.apply_symm_apply, sub_sub]
    exact hdiff
  let q : E → E ⧸ (K.comap T.toLinearMap) := Submodule.Quotient.mk
  have heq : q '' closure V = q '' C' := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hdiff⟩ := hrep' x hx
      exact ⟨y, hy, (Submodule.Quotient.eq _).mpr hdiff⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hCV hy, rfl⟩
  change IsCompact (q '' closure V)
  rw [heq]
  exact hC'.image (K.comap T.toLinearMap).mkQL.continuous

end CHS.Pogorelov

namespace CHS

open Pogorelov

variable {n : ℕ}
local notation "E₀" => DeGiorgi.AmbientSpace (n + n)

theorem PogorelovCompactGeometry.comp_affine
    {U : Set E₀} {u : E₀ → ℝ} (hgeometry : PogorelovCompactGeometry U u)
    (T : E₀ ≃L[ℝ] E₀) (c : E₀) :
    PogorelovCompactGeometry {x | c + T x ∈ U} (fun x => u (c + T x)) := by
  rcases hgeometry with hbounded | ⟨K, hUinv, huinv, hquot⟩
  · let ψ : E₀ → E₀ := fun y => T.symm (y - c)
    have hC : IsCompact (ψ '' closure U) := hbounded.isCompact_closure.image
      (T.symm.continuous.comp (continuous_id.sub continuous_const))
    apply Or.inl
    apply hC.isBounded.subset
    intro x hx
    exact ⟨c + T x, subset_closure hx, by simp [ψ]⟩
  · refine Or.inr ⟨K.comap T.toLinearMap, ?_, ?_,
      compact_real_quotient_affine_preimage T c K hUinv hquot⟩
    · intro x hx v hv
      change c + T (x + v) ∈ U
      simpa only [map_add, add_assoc] using hUinv (c + T x) hx (T v) hv
    · intro x hx v hv
      change u (c + T (x + v)) = u (c + T x)
      simpa only [map_add, add_assoc] using huinv (c + T x) hx (T v) hv

end CHS
