import CHS.Sections.Depth
import CHS.Pogorelov.QuotientSlice
import CHS.Calculus.HessianLocality

/-!
# Lemma 3.1 with invariance only on the original domain

The actual quotient image of the closure supplies the compact slice.
Composing with the orthogonal projection produces globally invariant
representatives, which agree with the original functions and all actual
derivatives inside the domain.  Values of the original functions outside
the closure are unrestricted.
-/

set_option autoImplicit false
noncomputable section

open DeGiorgi Set Metric Filter
open scoped ContDiff ComplexOrder Topology BigOperators

namespace CHS.Sections

open CHS.Calculus CHS.Analysis CHS.Pogorelov

variable {n : ℕ} [NeZero (n + n)]
local notation "E" => AmbientSpace (n + n)

theorem cylindrical_section_estimates_of_local_invariance
    (hn : 0 < n) (K : Submodule ℝ E) {U : Set E}
    (hU : IsOpen U) (hconv : Convex ℝ U)
    (hquot : IsCompact ((Submodule.Quotient.mk : E → E ⧸ K) '' closure U))
    (hUinv : ∀ x ∈ U, ∀ w ∈ K, x + w ∈ U)
    {u q : E → ℝ}
    (huInv : ∀ x ∈ U, ∀ w ∈ K, u (x + w) = u x)
    (hqInv : ∀ x ∈ U, ∀ w ∈ K, q (x + w) = q x)
    (hu : ContinuousOn u (closure U)) (hu₂ : ContDiffOn ℝ 2 u U)
    (hR : ∀ x ∈ U, (realBlockHessian realDirections imagDirections u x).PosSemidef)
    (hq : ContinuousOn q (closure U)) (hq₂ : ContDiffOn ℝ 2 q U)
    (hqConvex : ConvexOn ℝ univ q)
    (hqBounds : ∀ x ∈ closure U, 0 ≤ q x ∧ q x ≤ 4 * (n : ℝ) ^ 2)
    (hQ : ∀ x ∈ U, (complexHessian realDirections imagDirections q x - 1).PosSemidef)
    (huLower : ∀ x ∈ closure U, -1 ≤ u x)
    (huUpper : ∀ x ∈ U, u x ≤ 0)
    (huBoundary : ∀ x ∈ frontier U, u x = 0)
    (huDet : ∀ x ∈ U, (complexHessian realDirections imagDirections u x).det = 1)
    {x : E} (hx : x ∈ U) (hxDeep : u x ≤ -1 / 4) :
    let c := Real.sqrt ((32 * (n : ℝ) ^ 2)⁻¹ ^ (n - 1) / 2) / 16
    c ≤ infDist x (frontier U) ∧
      Real.sqrt (∑ i, ‖affineWirtinger realDirections imagDirections (fderiv ℝ u x) i‖ ^ 2) ≤ c⁻¹ := by
  let P : E →L[ℝ] E := Kᗮ.starProjection
  let v : E → ℝ := u ∘ P
  let p : E → ℝ := q ∘ P
  have hP (y : E) : P y = y - K.starProjection y := K.starProjection_orthogonal_val y
  have hmap : MapsTo P U U := by
    intro y hy
    rw [hP]
    simpa only [sub_eq_add_neg] using hUinv y hy (-K.starProjection y)
      (K.neg_mem (K.starProjection_apply_mem y))
  have hmapc : MapsTo P (closure U) (closure U) := hmap.closure P.continuous
  have hvcont : ContinuousOn v (closure U) := hu.comp P.continuous.continuousOn hmapc
  have hpcont : ContinuousOn p (closure U) := hq.comp P.continuous.continuousOn hmapc
  have hv2 : ContDiffOn ℝ 2 v U := hu₂.comp P.contDiff.contDiffOn hmap
  have hp2 : ContDiffOn ℝ 2 p U := hq₂.comp P.contDiff.contDiffOn hmap
  have hveq : EqOn v u U := by
    intro y hy
    change u (P y) = u y
    rw [hP]
    simpa only [sub_eq_add_neg] using huInv y hy (-K.starProjection y)
      (K.neg_mem (K.starProjection_apply_mem y))
  have hpeq : EqOn p q U := by
    intro y hy
    change q (P y) = q y
    rw [hP]
    simpa only [sub_eq_add_neg] using hqInv y hy (-K.starProjection y)
      (K.neg_mem (K.starProjection_apply_mem y))
  have hveqc : EqOn v u (closure U) := hveq.of_subset_closure hvcont hu subset_closure Subset.rfl
  have hpeqc : EqOn p q (closure U) := hpeq.of_subset_closure hpcont hq subset_closure Subset.rfl
  have hvnear (y : E) (hy : y ∈ U) : v =ᶠ[𝓝 y] u :=
    Filter.eventually_of_mem (hU.mem_nhds hy) (fun z hz => hveq hz)
  have hpnear (y : E) (hy : y ∈ U) : p =ᶠ[𝓝 y] q :=
    Filter.eventually_of_mem (hU.mem_nhds hy) (fun z hz => hpeq hz)
  have hvA (y : E) (hy : y ∈ U) : complexHessian realDirections imagDirections v y =
      complexHessian realDirections imagDirections u y :=
    complexHessian_eq_of_eventuallyEq _ _ (hvnear y hy)
      (hv2.contDiffAt (hU.mem_nhds hy)) (hu₂.contDiffAt (hU.mem_nhds hy))
  have hpA (y : E) (hy : y ∈ U) : complexHessian realDirections imagDirections p y =
      complexHessian realDirections imagDirections q y :=
    complexHessian_eq_of_eventuallyEq _ _ (hpnear y hy)
      (hp2.contDiffAt (hU.mem_nhds hy)) (hq₂.contDiffAt (hU.mem_nhds hy))
  have hvinv (y w : E) (hw : w ∈ K) : v (y + w) = v y := by
    change u (P (y + w)) = u (P y)
    rw [map_add, show P w = 0 from K.starProjection_orthogonal_apply_eq_zero hw, add_zero]
  have hpinv (y w : E) (hw : w ∈ K) : p (y + w) = p y := by
    change q (P (y + w)) = q (P y)
    rw [map_add, show P w = 0 from K.starProjection_orthogonal_apply_eq_zero hw, add_zero]
  have hpconv : ConvexOn ℝ univ p := by
    refine ⟨convex_univ, ?_⟩
    intro y _ z _ a b ha hb hab
    change q (P (a • y + b • z)) ≤ a • q (P y) + b • q (P z)
    rw [map_add, map_smul, map_smul]
    exact hqConvex.2 (mem_univ _) (mem_univ _) ha hb hab
  have hvR (y : E) (hy : y ∈ U) :
      (realBlockHessian realDirections imagDirections v y).PosSemidef := by
    rw [realBlockHessian_eq_of_eventuallyEq _ _ (hvnear y hy)]
    exact hR y hy
  have hpBounds (y : E) (hy : y ∈ closure U) : 0 ≤ p y ∧ p y ≤ 4 * (n : ℝ) ^ 2 := by
    rw [hpeqc hy]
    exact hqBounds y hy
  have hpQ (y : E) (hy : y ∈ U) :
      (complexHessian realDirections imagDirections p y - 1).PosSemidef := by
    rw [hpA y hy]
    exact hQ y hy
  have hvLower (y : E) (hy : y ∈ closure U) : -1 ≤ v y := by rw [hveqc hy]; exact huLower y hy
  have hvUpper (y : E) (hy : y ∈ U) : v y ≤ 0 := by rw [hveq hy]; exact huUpper y hy
  have hvbd (y : E) (hy : y ∈ frontier U) : v y = 0 := by
    rw [hveqc (frontier_subset_closure hy)]
    exact huBoundary y hy
  have hvdet (y : E) (hy : y ∈ U) : (complexHessian realDirections imagDirections v y).det = 1 := by
    rw [hvA y hy]
    exact huDet y hy
  have hdeep : v x ≤ -1 / 4 := by rwa [hveq hx]
  have h := cylindrical_section_estimates hn K hU hconv
    (compact_orthogonal_slice_of_compact_real_quotient K hUinv hquot) hUinv
    hvinv hpinv hvcont hv2 hvR hpcont hp2 hpconv hpBounds hpQ hvLower hvUpper hvbd hvdet hx hdeep
  rwa [(hvnear x hx).fderiv_eq] at h

end CHS.Sections
