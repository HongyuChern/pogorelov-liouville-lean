import CHS.Pogorelov.PerturbedExtrema
import CHS.Pogorelov.CompactQuotient
import CHS.Calculus.QuadraticPerturbation
import CHS.Calculus.TranslationKernel

/-!
# Strict perturbations on an actual compact real-translation quotient

The squared projection norm has compact representatives together with the
potential.  Consequently the extremum is a local extremum in the full
ambient space, with a strict Hessian bound in every transverse direction.
-/

set_option autoImplicit false
noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace CHS.Pogorelov

open CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

theorem compact_value_projection_representatives
    (K : Submodule ℝ E) {U : Set E} {u : E → ℝ}
    (hu : ContinuousOn u (closure U))
    (hUinv : ∀ x ∈ U, ∀ v ∈ K, x + v ∈ U)
    (huinv : ∀ x ∈ U, ∀ v ∈ K, u (x + v) = u x)
    (hquot : IsCompact ((Submodule.Quotient.mk : E → E ⧸ K) '' closure U)) :
    ∃ C : Set E, IsCompact C ∧ C ⊆ closure U ∧
      ∀ x ∈ closure U, ∃ y ∈ C,
        u x = u y ∧ ‖Kᗮ.orthogonalProjectionOnto x‖ ^ 2 =
          ‖Kᗮ.orthogonalProjectionOnto y‖ ^ 2 := by
  obtain ⟨C, hC, hCU, hrep⟩ := compact_representatives_of_compact_real_quotient K hUinv hquot
  refine ⟨C, hC, hCU, ?_⟩
  intro x hx
  obtain ⟨y, hy, hdiff⟩ := hrep x hx
  have huEq := translation_invariant_on_closure K hUinv hu huinv x hx (y - x) hdiff
  have hyx : x + (y - x) = y := by abel
  rw [hyx] at huEq
  have hproj : Kᗮ.orthogonalProjectionOnto (y - x) = 0 :=
    Kᗮ.orthogonalProjectionOnto_eq_zero_iff.mpr (K.le_orthogonal_orthogonal hdiff)
  rw [map_sub, sub_eq_zero] at hproj
  exact ⟨y, hy, huEq.symm, by rw [hproj]⟩

theorem exists_strict_projected_maximum
    (K : Submodule ℝ E) {U : Set E} {u : E → ℝ} (hU : IsOpen U)
    (hu : ContDiffOn ℝ 2 u U) (huC : ContinuousOn u (closure U))
    (hUinv : ∀ x ∈ U, ∀ v ∈ K, x + v ∈ U)
    (huinv : ∀ x ∈ U, ∀ v ∈ K, u (x + v) = u x)
    (hquot : IsCompact ((Submodule.Quotient.mk : E → E ⧸ K) '' closure U))
    (hbd : ∀ x ∈ frontier U, u x = 0)
    {x₀ : E} (hx₀ : x₀ ∈ U) (hu₀ : 0 < u x₀) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ p ∈ U, ∀ v : E,
      realHessian u p v v ≤ -2 * ε * ‖Kᗮ.orthogonalProjectionOnto v‖ ^ 2 := by
  obtain ⟨C, hC, hCU, hrep⟩ := compact_value_projection_representatives K huC hUinv huinv hquot
  have hq : ContinuousOn (fun x : E => ‖Kᗮ.orthogonalProjectionOnto x‖ ^ 2) (closure U) :=
    (Kᗮ.orthogonalProjectionOnto.continuous.norm.pow 2).continuousOn
  obtain ⟨ε, hε, p, hp, _, hlocal⟩ := exists_pos_perturbation_interior_max hU hC hCU
    huC hq (fun _ _ => sq_nonneg _) hbd hrep hx₀ hu₀
  exact ⟨ε, hε, p, hp, realHessian_le_neg_quadratic_of_isLocalMax
    (hu.contDiffAt (hU.mem_nhds hp)) Kᗮ.orthogonalProjectionOnto ε hlocal⟩

end CHS.Pogorelov
