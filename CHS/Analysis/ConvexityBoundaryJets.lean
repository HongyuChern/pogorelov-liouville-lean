import CHS.Analysis.ConvexityMinimum
import CHS.Calculus.ClosureSchur

/-!
# Boundary convexity with C4 interior and actual C2 boundary jets

This version of Proposition 2.4 does not assume a C4 extension across the
boundary.  The closure Hessian is the unique continuous extension of the
actual interior Frechet Hessian, and the equation is imposed on that jet.
-/

set_option autoImplicit false
noncomputable section

open DeGiorgi Filter Metric Set Matrix MeasureTheory
open scoped ContDiff ComplexOrder Topology

namespace CHS.Analysis

open CHS.Calculus

variable {n : ℕ} [NeZero (n + n)]
local notation "E" => AmbientSpace (n + n)

theorem closure_realHessian_posSemidef_of_boundary
    (hd : 2 < ((n + n : ℕ) : ℝ))
    {u : E → ℝ} {U : Set E} (hU : IsOpen U) (hconn : IsPreconnected U)
    (hK : IsCompact (closure U)) (hu : ContDiffOn ℝ 4 u U)
    (J : ClosureC2Jet u U)
    (hA : ∀ x ∈ closure U, (J.complexField realDirections imagDirections x).PosDef)
    (hdet : ∀ x ∈ closure U, (J.complexField realDirections imagDirections x).det = 1)
    (hbd : ∀ x ∈ frontier U, (J.realField realDirections imagDirections x).PosSemidef) :
    ∀ x ∈ closure U, (J.realField realDirections imagDirections x).PosSemidef := by
  have hu2 : ContDiffOn ℝ 2 u U := hu.of_le (by norm_num)
  have hux (x : E) (hx : x ∈ U) : ContDiffAt ℝ 2 u x := hu2.contDiffAt (hU.mem_nhds hx)
  have hactualA (x : E) (hx : x ∈ U) :
      (complexHessian realDirections imagDirections u x).PosDef := by
    rw [← J.complexField_eq hx (hux x hx)]
    exact hA x (subset_closure hx)
  have hactualDet (x : E) (hx : x ∈ U) :
      (complexHessian realDirections imagDirections u x).det = 1 := by
    rw [← J.complexField_eq hx (hux x hx)]
    exact hdet x (subset_closure hx)
  let M := J.schurField realDirections imagDirections
  have hMc : ContinuousOn M (closure U) := J.continuousOn_schurField _ _
  have hMeq (x : E) (hx : x ∈ U) : M x = schurHessian realDirections imagDirections u x :=
    J.schurField_eq _ _ hx (hux x hx) (hactualDet x hx)
  have hHerm (x : E) (hx : x ∈ closure U) : (M x).IsHermitian := by
    ext i j
    have heq : EqOn (fun y => star (M y j i)) (fun y => M y i j) U := by
      intro y hy
      change star (M y j i) = M y i j
      rw [hMeq y hy]
      exact (schurHessian_isHermitian (hux y hy) realDirections imagDirections).apply i j
    exact heq.of_subset_closure (by fun_prop) (by fun_prop) subset_closure Subset.rfl hx
  have hproper : U ≠ univ := by
    intro heq
    have hb : Bornology.IsBounded (univ : Set E) := by simpa [heq] using hK.isBounded
    exact (Filter.neBot_iff.mp (inferInstance : Filter.NeBot (Bornology.cobounded E)))
      (Bornology.cobounded_eq_bot_iff.mpr (Bornology.isBounded_univ.mp hb))
  have hpair (ξ : Fin n → ℂ) :
      ∀ x ∈ closure U, 0 ≤ (star ξ ⬝ᵥ (M x).mulVec ξ).re := by
    apply nonneg_on_closure_of_local_supersolutions hd hU hconn hK hproper
    · fun_prop
    · intro x hx
      have hM : (M x).PosSemidef :=
        (J.realField_posSemidef_iff_schurField hU hu2 _ _ (frontier_subset_closure hx)
          (hA x (frontier_subset_closure hx)) (hdet x (frontier_subset_closure hx))).mp (hbd x hx)
      exact (Complex.nonneg_iff.mp (hM.dotProduct_mulVec_nonneg ξ)).1
    · intro x hx
      obtain ⟨r, hr, B, hsub, hs⟩ := schurPair_local_supersolutions hU hu hactualDet hactualA ξ x hx
      refine ⟨r, hr, B, hsub, IsSupersolution.congr_ae ?_ hs⟩
      filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
      change (star ξ ⬝ᵥ (schurHessian realDirections imagDirections u y).mulVec ξ).re =
        (star ξ ⬝ᵥ (M y).mulVec ξ).re
      rw [hMeq y (hsub hy)]
  intro x hx
  apply (J.realField_posSemidef_iff_schurField hU hu2 _ _ hx (hA x hx) (hdet x hx)).mpr
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hHerm x hx)
  intro ξ
  exact Complex.nonneg_iff.mpr ⟨hpair ξ x hx, (hHerm x hx).im_star_dotProduct_mulVec_self ξ |>.symm⟩

end CHS.Analysis
