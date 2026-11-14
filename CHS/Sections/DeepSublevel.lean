import CHS.Pogorelov.GeneralEstimate
import CHS.Calculus.PotentialConstants
import CHS.Analysis.LinfBounds
import CHS.Pogorelov.SubdomainGeometry

/-!
# Proposition 3.2: the normalized deep-sublevel estimate (3.8)

Apply the exact positive κ = 1 estimate to `v + 1/4` on `{v < -1/4}`.
The lower bound `v ≥ -1` supplies the C⁰ bound; the explicit gradient bound
is the input furnished by Lemma 3.1.  The conclusion is a pointwise real
Hessian bound and an actual finite entrywise L∞ bound on `{v ≤ -1/2}`.
The normalization and exhaustion required for Proposition 3.2 are separate.
-/

set_option autoImplicit false
noncomputable section

open Set Matrix
open scoped ContDiff ComplexOrder ENNReal

namespace CHS

open Calculus Analysis Pogorelov

variable {n : ℕ}
local notation "E₀" => DeGiorgi.AmbientSpace (n + n)

theorem PogorelovCompactGeometry.add_const {U : Set E₀} {u : E₀ → ℝ}
    (h : PogorelovCompactGeometry U u) (c : ℝ) :
    PogorelovCompactGeometry U (fun x => u x + c) := by
  rcases h with hbounded | ⟨L, hUinv, huinv, hquot⟩
  · exact Or.inl hbounded
  · exact Or.inr ⟨L, hUinv, fun x hx v hv => congrArg (fun r => r + c) (huinv x hx v hv), hquot⟩

namespace Sections

def deepSublevelHessianConstant (n : ℕ) (K : ℝ) : ℝ :=
  256 * (n : ℝ) ^ 2 * Real.exp (1 / 8) * (1 + K ^ 2) * (4 : ℝ) ^ (4 * n)

theorem deepSublevelHessianConstant_nonneg (n : ℕ) (K : ℝ) :
    0 ≤ deepSublevelHessianConstant n K := by
  unfold deepSublevelHessianConstant
  positivity

theorem abs_le_of_quarter_weighted_bound {s h C : ℝ} (m : ℕ)
    (hs : (1 : ℝ) / 4 ≤ s) (hbound : |s ^ m * h| ≤ C) : |h| ≤ C * (4 : ℝ) ^ m := by
  have hs0 : 0 ≤ s := by linarith
  rw [abs_mul, abs_of_nonneg (pow_nonneg hs0 _)] at hbound
  have hsmall : ((1 : ℝ) / 4) ^ m * |h| ≤ C :=
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hs m) (abs_nonneg h)).trans hbound
  have hscaled := mul_le_mul_of_nonneg_right hsmall (pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) m)
  have heq : (((1 : ℝ) / 4) ^ m * |h|) * 4 ^ m = |h| := by
    rw [mul_right_comm, ← mul_pow]
    norm_num
  rwa [heq] at hscaled

theorem normalized_deep_sublevel_hessian_pointwise
    (hn : 2 ≤ n) {v : E₀ → ℝ} (hv : ContDiff ℝ 4 v)
    (hdet : ∀ x, (complexHessian realDirections imagDirections v x).det = 1)
    (hR : ∀ x, (realBlockHessian realDirections imagDirections v x).PosSemidef)
    (hlower : ∀ x, -1 ≤ v x) (K : ℝ)
    (hK : ∀ x, v x < -1 / 4 → gradientNormSq realDirections imagDirections v x ≤ K ^ 2)
    (hgeometry : PogorelovCompactGeometry {x | v x < -1 / 4} v) :
    ∀ x, v x ≤ -1 / 2 → ∀ i j : Fin (n + n),
      |euclideanHessian v x i j| ≤ deepSublevelHessianConstant n K := by
  let U : Set E₀ := {x | v x < -1 / 4}
  let f : E₀ → ℝ := fun x => v x + 1 / 4
  have hU : IsOpen U := isOpen_lt hv.continuous continuous_const
  have hf : ContDiff ℝ 4 f := hv.add contDiff_const
  have hfBoundary : C2OnClosure f U := c2OnClosure_of_neighborhood isOpen_univ
    (subset_univ _) ((hf.of_le (by norm_num)).contDiffOn)
  have hbd : ∀ x ∈ frontier U, f x = 0 := by
    intro x hx
    have heq : v x = -1 / 4 := frontier_lt_subset_eq hv.continuous continuous_const hx
    dsimp [f]
    rw [heq]
    ring
  have hfd (x : E₀) (hx : x ∈ U) :
      (complexHessian realDirections imagDirections f x).det = 1 := by
    simpa only [f, complexHessian_add_const] using hdet x
  have hfR (x : E₀) : (realBlockHessian realDirections imagDirections f x).PosSemidef := by
    simpa only [f, realBlockHessian_add_const] using hR x
  have hf₂ (x : E₀) : ContDiffAt ℝ 2 f x := hf.contDiffAt.of_le (by norm_num)
  have hA (x : E₀) (hx : x ∈ U) := complexHessian_posDef_of_realBlockHessian
    (hf₂ x) realDirections imagDirections (hfR x) (hfd x hx)
  have hmat (x : E₀) (hx : x ∈ U) :
      ((1 : ℝ) • complexHessian realDirections imagDirections f x -
        pureHessian realDirections imagDirections f x *
          ((complexHessian realDirections imagDirections f x).map star)⁻¹ *
            (pureHessian realDirections imagDirections f x).map star).PosSemidef := by
    rw [one_smul]
    change (schurHessian realDirections imagDirections f x).PosSemidef
    have heq := realBlockHessian_posSemidef_equivalences (hf₂ x)
      realDirections imagDirections (hA x hx)
    exact heq.2.mp (heq.1.mp (hfR x))
  have hgrad : ∀ x ∈ U, gradientNormSq realDirections imagDirections f x ≤ K ^ 2 := by
    intro x hx
    simpa only [f, gradientNormSq_add_const] using hK x hx
  have hvalue : ∀ x ∈ U, -f x ≤ (1 : ℝ) := by
    intro x hx
    dsimp [f]
    linarith [hlower x]
  obtain ⟨C, hC, hCU, hrep⟩ := (hgeometry.add_const (1 / 4)).compact_jet_representatives
    hU (hf.contDiffOn.of_le (by norm_num)) hfBoundary.jet
  have hpoint := positive_branch_estimate_of_compact_jet_representatives hn hU hC hCU
    hf.contDiffOn hfBoundary.jet realDirections imagDirections hfd hA
      (by norm_num : (1 : ℝ) ≤ 1) hmat hbd hrep K 1 hgrad hvalue
  intro x hx i j
  have hxU : x ∈ U := by change v x < -1 / 4; linarith
  have hb := hpoint x hxU (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)
  rw [convex_coefficient, Real.one_rpow, mul_one, beta_one,
    show 4 * (n : ℝ) = ((4 * n : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast, realBlockHessian_add_const] at hb
  have hcoord := congrArg (fun M : Matrix (Fin (n + n)) (Fin (n + n)) ℝ => M i j)
    (realBlockHessian_reindex v x)
  change realBlockHessian realDirections imagDirections v x
    (finSumFinEquiv.symm i) (finSumFinEquiv.symm j) = euclideanHessian v x i j at hcoord
  rw [hcoord] at hb
  apply abs_le_of_quarter_weighted_bound (4 * n) _ hb
  dsimp [f]
  linarith

theorem normalized_deep_sublevel_hessian_linf
    (hn : 2 ≤ n) {v : E₀ → ℝ} (hv : ContDiff ℝ 4 v)
    (hdet : ∀ x, (complexHessian realDirections imagDirections v x).det = 1)
    (hR : ∀ x, (realBlockHessian realDirections imagDirections v x).PosSemidef)
    (hlower : ∀ x, -1 ≤ v x) (K : ℝ)
    (hK : ∀ x, v x < -1 / 4 → gradientNormSq realDirections imagDirections v x ≤ K ^ 2)
    (hgeometry : PogorelovCompactGeometry {x | v x < -1 / 4} v) :
    entryLinfNormOn MeasureTheory.volume {x | v x ≤ -1 / 2} (euclideanHessian v) ≤
        deepSublevelHessianConstant n K ∧
      ∀ i j, MeasureTheory.eLpNorm (fun x => euclideanHessian v x i j) (∞ : ℝ≥0∞)
        (MeasureTheory.volume.restrict {x | v x ≤ -1 / 2}) ≠ (∞ : ℝ≥0∞) := by
  have hbound := normalized_deep_sublevel_hessian_pointwise hn hv hdet hR hlower K hK hgeometry
  have hset : MeasurableSet {x : E₀ | v x ≤ -1 / 2} :=
    (isClosed_le hv.continuous continuous_const).measurableSet
  exact ⟨entryLinfNormOn_le_of_pointwise_bound MeasureTheory.volume hset
    (deepSublevelHessianConstant_nonneg n K) hbound,
    entrywise_eLpNorm_top_ne_top_of_pointwise_bound MeasureTheory.volume hset hbound⟩

end Sections
end CHS
