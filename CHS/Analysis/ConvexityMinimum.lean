import CHS.Analysis.SchurMinimum
import DifferentialGeometry.External.DeGiorgi.Localization

/-!
# The boundary convexity principle

Each scalar Schur pairing has a classical minimum on the compact closure.
A negative minimum would be interior, so the shifted supersolution would
vanish on the connected domain and hence also on its boundary.
-/

set_option autoImplicit false
noncomputable section

open DeGiorgi Filter Metric Set
open scoped BigOperators ComplexOrder ContDiff Topology

namespace CHS.Analysis

open Calculus

variable {n : ℕ} [NeZero (n + n)]
local notation "E" => AmbientSpace (n + n)

private theorem schurPair_continuousOn_closure
    {u : E → ℝ} {V U : Set E} (hV : IsOpen V) (hsub : closure U ⊆ V)
    (hu : ContDiffOn ℝ 4 u V)
    (hdet : ∀ y ∈ closure U, (complexHessian realDirections imagDirections u y).det = 1)
    (ξ : Fin n → ℂ) :
    ContinuousOn (fun y => (matrixPair (schurHessian realDirections imagDirections u) ξ y).re)
      (closure U) := by
  let A := complexHessian realDirections imagDirections u
  let B := pureHessian realDirections imagDirections u
  let C (x : E) := (B x).map star
  let H (x : E) := (A x).map star
  let M (x : E) := A x - B x * (H x).adjugate * C x
  have hM_eq : EqOn M (schurHessian realDirections imagDirections u) (closure U) := by
    intro y hy
    have hu2 : ContDiffAt ℝ 2 u y := (hu.contDiffAt (hV.mem_nhds (hsub hy))).of_le (by norm_num)
    have hT : H y = (A y).transpose := by
      ext i j
      exact (complexHessian_isHermitian hu2 _ _).apply j i
    have hHdet : (H y).det = 1 := by rw [hT, Matrix.det_transpose]; exact hdet y hy
    change A y - B y * (H y).adjugate * C y = A y - B y * (H y)⁻¹ * C y
    rw [inv_eq_adjugate_of_det_one _ hHdet]
  have hMC : ContinuousOn (fun y => (matrixPair M ξ y).re) (closure U) := by
    intro y hy
    have hu4 := hu.contDiffAt (hV.mem_nhds (hsub hy))
    have hA (i j : Fin n) : ContDiffAt ℝ 2 (fun z => A z i j) y :=
      complexHessian_contDiffAt_two hu4 _ _ i j
    have hB (i j : Fin n) : ContDiffAt ℝ 2 (fun z => B z i j) y :=
      pureHessian_contDiffAt_two hu4 _ _ i j
    have hC (i j : Fin n) : ContDiffAt ℝ 2 (fun z => C z i j) y :=
      Complex.conjCLE.contDiff.contDiffAt.comp y (hB i j)
    have hH (i j : Fin n) : ContDiffAt ℝ 2 (fun z => H z i j) y :=
      Complex.conjCLE.contDiff.contDiffAt.comp y (hA i j)
    have hM (i j : Fin n) : ContDiffAt ℝ 2 (fun z => M z i j) y :=
      (hA i j).sub (matrix_product_contDiffAt
        (matrix_product_contDiffAt hB (field_adjugate_contDiffAt hH)) hC i j)
    have hPair : ContDiffAt ℝ 2 (fun z => (matrixPair M ξ z).re) y :=
      Complex.reCLM.contDiff.contDiffAt.comp y (matrixPair_contDiffAt hM ξ)
    exact hPair.continuousAt.continuousWithinAt
  apply hMC.congr
  intro y hy
  exact congrArg (fun T : Matrix (Fin n) (Fin n) ℂ => (star ξ ⬝ᵥ T.mulVec ξ).re)
    (hM_eq hy).symm

theorem nonneg_on_closure_of_local_supersolutions
    (hd : 2 < ((n + n : ℕ) : ℝ))
    {U : Set E} (hU : IsOpen U) (hconn : IsPreconnected U) (hK : IsCompact (closure U))
    (hproper : U ≠ univ) {v : E → ℝ}
    (hv : ContinuousOn v (closure U)) (hbd : ∀ x ∈ frontier U, 0 ≤ v x)
    (hlocal : ∀ x ∈ U, ∃ r : ℝ, 0 < r ∧ ∃ B : NormalizedEllipticCoeff (n + n) (ball x r),
      ball x r ⊆ U ∧ IsSupersolution B.1 v) :
    ∀ x ∈ closure U, 0 ≤ v x := by
  intro z hz
  by_contra! hneg
  obtain ⟨p, hp, hmin⟩ := hK.exists_isMinOn ⟨z, hz⟩ hv
  have hpNeg : v p < 0 := lt_of_le_of_lt (hmin hz) hneg
  have hpU : p ∈ U := by
    by_contra hpU
    exact hpNeg.not_ge (hbd p (hU.frontier_eq ▸ ⟨hp, hpU⟩))
  have hfront : (frontier U).Nonempty := by
    by_contra hf
    have hclopen := isClopen_iff_frontier_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp hf)
    exact hproper (hclopen.eq_univ ⟨p, hpU⟩)
  let w (x : E) := v x - v p
  have hw : ContinuousOn w (closure U) := hv.sub continuousOn_const
  have hEq : EqOn w (fun _ => 0) U :=
    eq_zero_on_connected_of_local_supersolutions hd hU hconn (hw.mono subset_closure)
      (fun x hx => sub_nonneg.mpr (hmin (subset_closure hx)))
      (fun x hx => by
        obtain ⟨r, hr, B, hsub, hsup⟩ := hlocal x hx
        exact ⟨r, hr, B, hsub, hsup.sub_const_ball hr (v p)⟩) hpU (sub_self _)
  have hmaps : MapsTo w U ({0} : Set ℝ) := fun x hx => Set.mem_singleton_iff.mpr (hEq hx)
  obtain ⟨q, hq⟩ := hfront
  have hq0 : w q ∈ closure ({0} : Set ℝ) :=
    hmaps.closure_of_continuousOn hw (frontier_subset_closure hq)
  have hqEq : v q - v p = 0 := by simpa [w] using hq0
  linarith [hbd q hq]


/-- Proposition 2.4 on a relatively compact connected domain. A (C^4)
extension to an open neighbourhood of the closure suffices. -/
theorem realBlockHessian_posSemidef_on_closure
    (hd : 2 < ((n + n : ℕ) : ℝ))
    {u : E → ℝ} {U V : Set E} (hU : IsOpen U) (hconn : IsPreconnected U)
    (hK : IsCompact (closure U)) (hV : IsOpen V) (hsub : closure U ⊆ V)
    (hu : ContDiffOn ℝ 4 u V)
    (hA : ∀ y ∈ closure U, (complexHessian realDirections imagDirections u y).PosDef)
    (hdet : ∀ y ∈ closure U, (complexHessian realDirections imagDirections u y).det = 1)
    (hbd : ∀ y ∈ frontier U, (realBlockHessian realDirections imagDirections u y).PosSemidef) :
    ∀ y ∈ closure U, (realBlockHessian realDirections imagDirections u y).PosSemidef := by
  have hproper : U ≠ univ := by
    intro hEq
    have hbounded : Bornology.IsBounded (univ : Set E) := by
      simpa [hEq] using hK.isBounded
    exact (Filter.neBot_iff.mp (inferInstance : Filter.NeBot (Bornology.cobounded E)))
      (Bornology.cobounded_eq_bot_iff.mpr (Bornology.isBounded_univ.mp hbounded))
  have hdiff (y : E) (hy : y ∈ closure U) : ContDiffAt ℝ 2 u y :=
    (hu.contDiffAt (hV.mem_nhds (hsub hy))).of_le (by norm_num)
  have hequiv (y : E) (hy : y ∈ closure U) :
      (realBlockHessian realDirections imagDirections u y).PosSemidef ↔
        (schurHessian realDirections imagDirections u y).PosSemidef := by
    obtain ⟨hRC, hCM⟩ := realBlockHessian_posSemidef_equivalences
      (hdiff y hy) realDirections imagDirections (hA y hy)
    exact hRC.trans hCM
  intro y hy
  apply (hequiv y hy).mpr
  have hMherm := schurHessian_isHermitian (hdiff y hy) realDirections imagDirections
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hMherm
  intro ξ
  apply Complex.nonneg_iff.mpr
  refine ⟨?_, (hMherm.im_star_dotProduct_mulVec_self ξ).symm⟩
  exact nonneg_on_closure_of_local_supersolutions hd hU hconn hK hproper
    (schurPair_continuousOn_closure hV hsub hu hdet ξ)
    (fun z hz => schurPair_nonneg realDirections imagDirections ξ
      ((hequiv z (frontier_subset_closure hz)).mp (hbd z hz)))
    (schurPair_local_supersolutions hU (hu.mono (subset_closure.trans hsub))
      (fun z hz => hdet z (subset_closure hz)) (fun z hz => hA z (subset_closure hz)) ξ) y hy

end CHS.Analysis
