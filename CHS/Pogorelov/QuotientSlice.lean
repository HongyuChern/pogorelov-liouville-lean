import CHS.Pogorelov.CompactQuotient

/-! # Actual compact quotient closure implies compact orthogonal slice closure -/

set_option autoImplicit false
noncomputable section

open Set

namespace CHS.Pogorelov

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

theorem compact_orthogonal_slice_of_compact_real_quotient
    (K : Submodule ℝ E) {U : Set E}
    (hUinv : ∀ x ∈ U, ∀ v ∈ K, x + v ∈ U)
    (hquot : IsCompact ((Submodule.Quotient.mk : E → E ⧸ K) '' closure U)) :
    IsCompact (closure (Kᗮ.subtypeL ⁻¹' U)) := by
  let P := Kᗮ.orthogonalProjectionOnto
  let S : Set Kᗮ := Kᗮ.subtypeL ⁻¹' U
  have hP : MapsTo P U S := by
    intro x hx
    change (Kᗮ.orthogonalProjectionOnto x : E) ∈ U
    rw [Submodule.orthogonalProjectionOnto_orthogonal]
    change x - K.starProjection x ∈ U
    simpa only [sub_eq_add_neg] using hUinv x hx (-K.starProjection x)
      (K.neg_mem (K.starProjection_apply_mem x))
  have hPc := hP.closure P.continuous
  have hi : MapsTo Kᗮ.subtypeL S U := fun x hx => hx
  have hic := hi.closure Kᗮ.subtypeL.continuous
  obtain ⟨C, hC, hCU, hrep⟩ := compact_representatives_of_compact_real_quotient K hUinv hquot
  have heq : closure S = P '' C := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, hdiff⟩ := hrep (x : E) (hic hx)
      have hz : P (y - (x : E)) = 0 :=
        Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal
          (K.le_orthogonal_orthogonal hdiff)
      have hself : P (x : E) = x := Submodule.orthogonalProjectionOnto_mem_subspace_eq_self x
      rw [map_sub, hself] at hz
      exact ⟨y, hy, sub_eq_zero.mp hz⟩
    · rintro ⟨y, hy, rfl⟩
      exact hPc (hCU hy)
  change IsCompact (closure S)
  rw [heq]
  exact hC.image P.continuous

end CHS.Pogorelov
