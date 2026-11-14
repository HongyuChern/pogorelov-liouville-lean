import CHS.Pogorelov.SignPoint
import CHS.Pogorelov.SignNorms
import CHS.Pogorelov.QuotientPerturbation
import CHS.Analysis.HessianKernelRank

/-!
# Branch classification for the independent Theorem 1.1

Connectedness is explicit.  Compact quotient geometry produces a strict
projected extremum.  The negative branch forces κ = 1; its fixed
translation kernel and the actual block rank identity force the Schur
complement of `-u` to vanish everywhere.
-/

set_option autoImplicit false
noncomputable section

open Set Matrix
open scoped ContDiff ComplexOrder

namespace CHS

open Calculus Analysis Pogorelov

variable {n : ℕ}
local notation "E₀" => DeGiorgi.AmbientSpace (n + n)

theorem PogorelovCompactGeometry.exists_translation_subspace
    {U : Set E₀} {u : E₀ → ℝ} (h : PogorelovCompactGeometry U u) :
    ∃ K : Submodule ℝ E₀,
      (∀ x ∈ U, ∀ v ∈ K, x + v ∈ U) ∧
      (∀ x ∈ U, ∀ v ∈ K, u (x + v) = u x) ∧
      IsCompact ((Submodule.Quotient.mk : E₀ → E₀ ⧸ K) '' closure U) := by
  rcases h with hbounded | hquot
  · refine ⟨⊥, ?_, ?_, hbounded.isCompact_closure.image (⊥ : Submodule ℝ E₀).mkQL.continuous⟩
    · intro x hx v hv
      have hv0 : v = 0 := hv
      simpa only [hv0, add_zero] using hx
    · intro x hx v hv
      have hv0 : v = 0 := hv
      simp only [hv0, add_zero]
  · exact hquot

theorem pogorelov_positive_branch_of_negative_value
    (hn : 2 ≤ n) {U : Set E₀} (hU : IsOpen U) (hconn : IsPreconnected U)
    {u : E₀ → ℝ} (hu : ContDiffOn ℝ 4 u U) (huC : ContinuousOn u (closure U))
    (hdet : ∀ x ∈ U, (complexHessian realDirections imagDirections u x).det = 1)
    (hbd : ∀ x ∈ frontier U, u x = 0) (hgeometry : PogorelovCompactGeometry U u)
    {x₀ : E₀} (hx₀ : x₀ ∈ U) (hu₀ : u x₀ < 0) :
    ∀ x ∈ U, (complexHessian realDirections imagDirections u x).PosDef := by
  obtain ⟨K, hUinv, huinv, hquot⟩ := hgeometry.exists_translation_subspace
  have hwInv : ∀ x ∈ U, ∀ v ∈ K, (-u (x + v)) = -u x :=
    fun x hx v hv => congrArg Neg.neg (huinv x hx v hv)
  have hwbd : ∀ x ∈ frontier U, (-u x) = 0 := fun x hx => by rw [hbd x hx, neg_zero]
  obtain ⟨ε, hε, p, hp, hbound⟩ := exists_strict_projected_maximum K hU
    (u := fun x => -u x) (hu.neg.of_le (by norm_num)) huC.neg
      hUinv hwInv hquot hwbd hx₀ (neg_pos.mpr hu₀)
  have hu₂ : ContDiffAt ℝ 2 u p := (hu.contDiffAt (hU.mem_nhds hp)).of_le (by norm_num)
  have hquad (v : E₀) : 0 ≤ realHessian u p v v := by
    have h := hbound v
    rw [realHessian_neg] at h
    change -realHessian u p v v ≤ -2 * ε * ‖Kᗮ.orthogonalProjectionOnto v‖ ^ 2 at h
    nlinarith [sq_nonneg ‖Kᗮ.orthogonalProjectionOnto v‖]
  have hR := realBlockHessian_posSemidef_of_quadratic_nonneg hu₂
    realDirections imagDirections hquad
  have hA := complexHessian_posDef_of_realBlockHessian hu₂ realDirections imagDirections hR (hdet p hp)
  exact complexHessian_posDef_on_of_at hU hconn hu realDirections imagDirections
    (fun x hx => hdet x hx ▸ one_ne_zero) hp hA

theorem pogorelov_negative_branch_of_positive_value
    (hn : 2 ≤ n) {κ : ℝ} (hκ : 1 ≤ κ) {U : Set E₀}
    (hU : IsOpen U) (hconn : IsPreconnected U)
    {u : E₀ → ℝ} (hu : ContDiffOn ℝ 4 u U) (huC : ContinuousOn u (closure U))
    (hdet : ∀ x ∈ U, (complexHessian realDirections imagDirections u x).det = 1)
    (hbd : ∀ x ∈ frontier U, u x = 0)
    (hmat : ∀ x ∈ U, (κ • complexHessian realDirections imagDirections u x -
      pureHessian realDirections imagDirections u x *
        ((complexHessian realDirections imagDirections u x).map star)⁻¹ *
          (pureHessian realDirections imagDirections u x).map star).PosSemidef)
    (hgeometry : PogorelovCompactGeometry U u)
    {x₀ : E₀} (hx₀ : x₀ ∈ U) (hu₀ : 0 < u x₀) :
    κ = 1 ∧
      (∀ x ∈ U, (complexHessian realDirections imagDirections (fun y => -u y) x).PosDef) ∧
      (∀ x ∈ U, (complexHessian realDirections imagDirections (fun y => -u y) x).det = 1) ∧
      (∀ x ∈ U, schurHessian realDirections imagDirections (fun y => -u y) x = 0) := by
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨K, hUinv, huinv, hquot⟩ := hgeometry.exists_translation_subspace
  obtain ⟨ε, hε, p, hp, hbound⟩ := exists_strict_projected_maximum K hU
    (hu.of_le (by norm_num)) huC hUinv huinv hquot hbd hx₀ hu₀
  have hu₂ (x : E₀) (hx : x ∈ U) : ContDiffAt ℝ 2 u x :=
    (hu.contDiffAt (hU.mem_nhds hx)).of_le (by norm_num)
  have hquad (v : E₀) : 2 * ε * ‖Kᗮ.orthogonalProjectionOnto v‖ ^ 2 ≤
      realHessian (fun y => -u y) p v v := by
    rw [realHessian_neg]
    change _ ≤ -realHessian u p v v
    linarith [hbound v]
  have hR := realBlockHessian_posSemidef_of_quadratic_nonneg (hu₂ p hp).neg
    realDirections imagDirections (fun v => (by positivity :
      0 ≤ 2 * ε * ‖Kᗮ.orthogonalProjectionOnto v‖ ^ 2).trans (hquad v))
  obtain ⟨hk, hAp, hMp⟩ := negative_branch_sandwich_at_point (hu₂ p hp)
    realDirections imagDirections (hdet p hp) hR hκ (hmat p hp)
  have hAw : ∀ x ∈ U,
      (complexHessian realDirections imagDirections (fun y => -u y) x).PosDef := by
    have hpneg : (-complexHessian realDirections imagDirections u p).PosDef := by
      rwa [complexHessian_neg] at hAp
    simpa only [complexHessian_neg] using complexHessian_neg_posDef_on_of_at hU hconn hu
      realDirections imagDirections (fun x hx => hdet x hx ▸ one_ne_zero) hp hpneg
  have hdetw (x : E₀) (hx : x ∈ U) :
      (complexHessian realDirections imagDirections (fun y => -u y) x).det = 1 := by
    apply Algebra.det_eq_one_of_posDef_det_neg_eq_one (hAw x hx)
    simpa only [complexHessian_neg, neg_neg] using hdet x hx
  have hwInv : ∀ x ∈ U, ∀ v ∈ K, (-u (x + v)) = -u x :=
    fun x hx v hv => congrArg Neg.neg (huinv x hx v hv)
  have hK (x : E₀) (hx : x ∈ U) : K ≤ (realHessian (fun y => -u y) x).ker :=
    translation_subspace_le_realHessian_ker hU K hUinv (hu.neg.of_le (by norm_num)) hwInv hx
  have hker := realHessian_ker_eq_of_strict_projected_bound K (hK p hp)
    (by positivity : 0 < 2 * ε) hquad
  have hM := schurHessian_eq_zero_of_fixed_subspace_and_one_kernel hU
    (hu.neg.of_le (by norm_num)) hAw K hK hp hker hMp
  exact ⟨hk, hAw, hdetw, hM⟩

end CHS
