import CHS.Sections.Barrier
import CHS.Analysis.LinearizedFlux
import CHS.Analysis.ConvexGradient
import Mathlib.Analysis.LocallyConvex.Separation

/-!
# A supporting affine coordinate from a nearest point of the complement
-/

set_option autoImplicit false
noncomputable section

open DeGiorgi Metric Set
open scoped BigOperators ComplexOrder ContDiff InnerProductSpace

namespace CHS.Sections

open CHS.Analysis CHS.Calculus

variable {n : ℕ} [NeZero (n + n)]
local notation "E" => AmbientSpace (n + n)

theorem affineWirtinger_norm_sq (L : E →L[ℝ] ℝ) :
    (∑ i, ‖affineWirtinger realDirections imagDirections L i‖ ^ 2) = ‖L‖ ^ 2 / 4 := by
  let v := (InnerProductSpace.toDual ℝ E).symm L
  have hv : ‖v‖ = ‖L‖ := (InnerProductSpace.toDual ℝ E).symm.norm_map L
  have hvcoord (i : Fin (n + n)) : L (EuclideanSpace.single i 1) = v i := by
    calc
      L (EuclideanSpace.single i 1) = ⟪v, EuclideanSpace.single i 1⟫_ℝ :=
        InnerProductSpace.toDual_symm_apply.symm
      _ = v i := by rw [real_inner_comm]; simp [EuclideanSpace.inner_single_left]
  rw [← hv, EuclideanSpace.real_norm_sq_eq, ← Equiv.sum_comp finSumFinEquiv,
    Fintype.sum_sum_type, ← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.sq_norm]
  simp only [affineWirtinger, realDirections, imagDirections, hvcoord, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re,
    Complex.sub_im, Complex.I_re, Complex.I_im, Complex.inv_re, Complex.inv_im,
    Complex.normSq_ofNat]
  norm_num
  ring

theorem exists_normalized_support_at_infDist_compl
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U)
    (hproper : U ≠ univ) {x : E} (hx : x ∈ U) :
    ∃ (L : E →L[ℝ] ℝ) (k : ℝ), ‖L‖ = 1 ∧
      (∀ z ∈ U, 0 < L z + k) ∧ L x + k ≤ infDist x Uᶜ := by
  have hne : Uᶜ.Nonempty := Set.nonempty_compl.mpr hproper
  obtain ⟨y, hy, hd⟩ := hU.isClosed_compl.exists_infDist_eq_dist hne x
  obtain ⟨P, hP⟩ := geometric_hahn_banach_point_open hconv hU (show y ∉ U from hy)
  have hPne : P ≠ 0 := by
    intro he
    have h := hP x hx
    rw [he, zero_apply, zero_apply] at h
    exact (lt_irrefl _ h)
  have hn : 0 < ‖P‖ := (norm_pos_iff (a := P)).mpr hPne
  let L := ‖P‖⁻¹ • P
  refine ⟨L, -L y, ?_, ?_, ?_⟩
  · simp [L, norm_smul, hn.ne']
  · intro z hz
    change 0 < ‖P‖⁻¹ * P z + -(‖P‖⁻¹ * P y)
    rw [← sub_eq_add_neg, ← mul_sub]
    exact mul_pos (inv_pos.mpr hn) (sub_pos.mpr (hP z hz))
  · rw [hd, dist_eq_norm, ← sub_eq_add_neg, ← map_sub]
    change ‖P‖⁻¹ * P (x - y) ≤ ‖x - y‖
    have h := (le_abs_self (P (x - y))).trans (P.le_opNorm (x - y))
    have hm := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hn.le)
    simpa only [← mul_assoc, inv_mul_cancel₀ hn.ne', one_mul] using hm


private theorem section_gradient_bound_of_depth {U : Set E} {u : E → ℝ}
    {x : E} (hx : x ∈ U) (hconv : ConvexOn ℝ U u) (hdiff : DifferentiableAt ℝ u x)
    (huLower : -1 ≤ u x) (huUpper : ∀ y ∈ U, u y ≤ 0)
    {c : ℝ} (hc : 0 < c) (hdepth : c ≤ infDist x Uᶜ) :
    Real.sqrt (∑ i, ‖affineWirtinger realDirections imagDirections (fderiv ℝ u x) i‖ ^ 2) ≤ c⁻¹ := by
  have hball : ball x c ⊆ U :=
    (ball_subset_ball hdepth).trans ball_infDist_compl_subset
  let r := c / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrlt : r < c := by dsimp [r]; linarith
  have hbound (e : E) (he : ‖e‖ = 1) : fderiv ℝ u x e ≤ r⁻¹ := by
    have heU : x + r • e ∈ U := by
      apply hball
      rw [mem_ball_iff_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hr,
        he, mul_one]
      exact hrlt
    have h := supporting_fderiv_of_convexOn hconv hx heU hdiff
    rw [add_sub_cancel_left, map_smul, smul_eq_mul] at h
    have hprod : fderiv ℝ u x e * r ≤ 1 := by
      rw [mul_comm]
      linarith [huLower, huUpper _ heU]
    simpa only [one_div] using (le_div_iff₀ hr).mpr hprod
  have hnorm : ‖fderiv ℝ u x‖ ≤ r⁻¹ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hr.le)
    intro v
    by_cases hv : v = 0
    · simp [hv]
    have hn' : 0 < ‖v‖ := norm_pos_iff.mpr hv
    let e := ‖v‖⁻¹ • v
    have he : ‖e‖ = 1 := by simp [e, norm_smul, hn'.ne']
    have hneg : ‖-e‖ = 1 := by simpa using he
    have hplus := hbound e he
    have hminus := hbound (-e) hneg
    rw [map_neg] at hminus
    have habs : ‖fderiv ℝ u x e‖ ≤ r⁻¹ := by
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨neg_le.mp hminus, hplus⟩
    have hvEq : ‖v‖ • e = v := by simp [e, smul_smul, hn'.ne']
    calc
      ‖fderiv ℝ u x v‖ = ‖fderiv ℝ u x (‖v‖ • e)‖ := by rw [hvEq]
      _ = ‖v‖ * ‖fderiv ℝ u x e‖ := by
        rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg v)]
      _ ≤ r⁻¹ * ‖v‖ := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right habs (norm_nonneg v)
  rw [affineWirtinger_norm_sq]
  have hs : Real.sqrt (‖fderiv ℝ u x‖ ^ 2 / 4) = ‖fderiv ℝ u x‖ / 2 := by
    rw [show ‖fderiv ℝ u x‖ ^ 2 / 4 = (‖fderiv ℝ u x‖ / 2) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  rw [hs]
  have hrInv : r⁻¹ = 2 * c⁻¹ := by
    dsimp only [r]
    rw [inv_div, div_eq_mul_inv]
  rw [hrInv] at hnorm
  linarith

/-- Lemma 3.1 on a bounded convex domain, with the explicit constant in
the proof. The distance is computed to the closed complement. -/
theorem bounded_section_depth_and_gradient
    (hn : 0 < n) {U : Set E} (hU : IsOpen U) (hK : IsCompact (closure U))
    {u q : E → ℝ} (hconv : ConvexOn ℝ U u)
    (hu : ContinuousOn u (closure U)) (hu₂ : ContDiffOn ℝ 2 u U)
    (hq : ContinuousOn q (closure U)) (hq₂ : ContDiffOn ℝ 2 q U)
    (hqBounds : ∀ y ∈ closure U, 0 ≤ q y ∧ q y ≤ 4 * (n : ℝ) ^ 2)
    (hQ : ∀ y ∈ U, (complexHessian realDirections imagDirections q y - 1).PosSemidef)
    (huLower : ∀ y ∈ closure U, -1 ≤ u y)
    (huUpper : ∀ y ∈ U, u y ≤ 0)
    (huBoundary : ∀ y ∈ frontier U, u y = 0)
    (huDet : ∀ y ∈ U, (complexHessian realDirections imagDirections u y).det = 1)
    {x : E} (hx : x ∈ U) (hxDeep : u x ≤ -1 / 4) :
    let c := Real.sqrt ((32 * (n : ℝ) ^ 2)⁻¹ ^ (n - 1) / 2) / 16
    c ≤ infDist x Uᶜ ∧
      Real.sqrt (∑ i, ‖affineWirtinger realDirections imagDirections (fderiv ℝ u x) i‖ ^ 2) ≤ c⁻¹ := by
  let c := Real.sqrt ((32 * (n : ℝ) ^ 2)⁻¹ ^ (n - 1) / 2) / 16
  change c ≤ infDist x Uᶜ ∧ _
  have hc : 0 < c := by
    dsimp [c]
    exact div_pos (Real.sqrt_pos.mpr (by positivity)) (by norm_num)
  have hproper : U ≠ univ := by
    intro hEq
    have hbounded : Bornology.IsBounded (univ : Set E) := by
      simpa [hEq] using hK.isBounded
    exact (Filter.neBot_iff.mp (inferInstance : Filter.NeBot (Bornology.cobounded E)))
      (Bornology.cobounded_eq_bot_iff.mpr (Bornology.isBounded_univ.mp hbounded))
  obtain ⟨L, k, hL, hlevel, hdist⟩ := exists_normalized_support_at_infDist_compl
    hU hconv.1 hproper hx
  have hLnorm : (∑ i, ‖affineWirtinger realDirections imagDirections L i‖ ^ 2) = 1 / 4 := by
    rw [affineWirtinger_norm_sq, hL, one_pow]
  have hdepth : c ≤ infDist x Uᶜ := (section_depth_lower_bound_of_compact_representatives hn realDirections imagDirections
    hU hK Subset.rfl L k hu hu₂ hq hq₂ hlevel hqBounds hQ hLnorm huLower huBoundary huDet
    (fun _ z hz => ⟨z, ⟨closure_mono inter_subset_left hz, hz⟩, rfl, rfl, rfl⟩) hx hxDeep).trans hdist
  refine ⟨hdepth, ?_⟩
  exact section_gradient_bound_of_depth hx hconv
    ((hu₂.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num))
    (huLower x (subset_closure hx)) huUpper hc hdepth

private theorem projection_norm_comp_eq
    (V : Submodule ℝ E) (P : V →L[ℝ] ℝ) :
    ‖P.comp V.orthogonalProjectionOnto‖ = ‖P‖ := by
  apply le_antisymm
  · exact (P.opNorm_comp_le _).trans (mul_le_of_le_one_right (norm_nonneg P)
      V.orthogonalProjectionOnto_norm_le)
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro z
    have h := (P.comp V.orthogonalProjectionOnto).le_opNorm (z : E)
    simpa only [ContinuousLinearMap.comp_apply,
      V.orthogonalProjectionOnto_mem_subspace_eq_self, Submodule.coe_norm] using h

set_option backward.isDefEq.respectTransparency false in
theorem exists_normalized_support_at_infDist_cylinder
    (V : Submodule ℝ E) {S : Set V} (hS : IsOpen S) (hc : Convex ℝ S)
    (hproper : S ≠ univ) {x : E} (hx : V.orthogonalProjectionOnto x ∈ S) :
    ∃ (P : V →L[ℝ] ℝ) (k : ℝ), ‖P.comp V.orthogonalProjectionOnto‖ = 1 ∧
      (∀ z, V.orthogonalProjectionOnto z ∈ S → 0 < P (V.orthogonalProjectionOnto z) + k) ∧
      P (V.orthogonalProjectionOnto x) + k ≤
        infDist x (V.orthogonalProjectionOnto ⁻¹' S)ᶜ := by
  let U := V.orthogonalProjectionOnto ⁻¹' S
  have hU : IsOpen U := hS.preimage V.orthogonalProjectionOnto.continuous
  have hne : Uᶜ.Nonempty := by
    obtain ⟨z, hz⟩ := Set.nonempty_compl.mpr hproper
    refine ⟨(z : E), ?_⟩
    simpa only [U, mem_compl_iff, mem_preimage,
      V.orthogonalProjectionOnto_mem_subspace_eq_self] using hz
  obtain ⟨y, hy, hd⟩ := hU.isClosed_compl.exists_infDist_eq_dist hne x
  obtain ⟨P, hP⟩ := geometric_hahn_banach_point_open hc hS
    (show V.orthogonalProjectionOnto y ∉ S from hy)
  have hPne : P ≠ 0 := by
    intro h
    have hlt := hP _ hx
    rw [h, zero_apply, zero_apply] at hlt
    exact lt_irrefl _ hlt
  have hnP : 0 < ‖P‖ := (norm_pos_iff (a := P)).mpr hPne
  let Q := ‖P‖⁻¹ • P
  have hQnorm : ‖Q‖ = 1 := by
    change ‖‖P‖⁻¹ • P‖ = 1
    apply le_antisymm
    · simpa only [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnP), inv_mul_cancel₀ hnP.ne'] using
        ContinuousLinearMap.opNorm_smul_le (‖P‖⁻¹) P
    · have h := ContinuousLinearMap.opNorm_smul_le ‖P‖ Q
      have hPQ : ‖P‖ • Q = P := by
        simp only [Q, smul_smul, mul_inv_cancel₀ hnP.ne', one_smul]
      rw [hPQ, Real.norm_eq_abs, abs_of_pos hnP] at h
      exact (le_mul_iff_one_le_right hnP).mp h
  refine ⟨Q, -Q (V.orthogonalProjectionOnto y), ?_, ?_, ?_⟩
  · rw [projection_norm_comp_eq, hQnorm]
  · intro z hz
    change 0 < ‖P‖⁻¹ * P (V.orthogonalProjectionOnto z) +
      -(‖P‖⁻¹ * P (V.orthogonalProjectionOnto y))
    rw [← sub_eq_add_neg, ← mul_sub]
    exact mul_pos (inv_pos.mpr hnP) (sub_pos.mpr (hP _ hz))
  · change Q (V.orthogonalProjectionOnto x) + -Q (V.orthogonalProjectionOnto y) ≤ infDist x Uᶜ
    rw [hd, dist_eq_norm, ← sub_eq_add_neg, ← map_sub, ← map_sub]
    have h := (le_abs_self (Q (V.orthogonalProjectionOnto (x - y)))).trans
      ((Q.comp V.orthogonalProjectionOnto).le_opNorm (x - y))
    rw [projection_norm_comp_eq, hQnorm, one_mul] at h
    exact h


/-- Lemma 3.1 on the inverse image of a relatively compact convex domain
under orthogonal projection. The invariant functions are represented by
their values on the orthogonal slice. -/
theorem cylindrical_section_depth_and_gradient
    (hn : 0 < n) (V : Submodule ℝ E) {S : Set V}
    (hS : IsOpen S) (hK : IsCompact (closure S))
    (hproper : S ≠ univ) {u q : E → ℝ}
    (huInv : ∀ y : E, u y = u (V.orthogonalProjectionOnto y : E))
    (hqInv : ∀ y : E, q y = q (V.orthogonalProjectionOnto y : E))
    (hconv : ConvexOn ℝ (V.orthogonalProjectionOnto ⁻¹' S) u)
    (hu : ContinuousOn u (closure (V.orthogonalProjectionOnto ⁻¹' S)))
    (hu₂ : ContDiffOn ℝ 2 u (V.orthogonalProjectionOnto ⁻¹' S))
    (hq : ContinuousOn q (closure (V.orthogonalProjectionOnto ⁻¹' S)))
    (hq₂ : ContDiffOn ℝ 2 q (V.orthogonalProjectionOnto ⁻¹' S))
    (hqBounds : ∀ y ∈ closure (V.orthogonalProjectionOnto ⁻¹' S),
      0 ≤ q y ∧ q y ≤ 4 * (n : ℝ) ^ 2)
    (hQ : ∀ y, V.orthogonalProjectionOnto y ∈ S →
      (complexHessian realDirections imagDirections q y - 1).PosSemidef)
    (huLower : ∀ y ∈ closure (V.orthogonalProjectionOnto ⁻¹' S), -1 ≤ u y)
    (huUpper : ∀ y, V.orthogonalProjectionOnto y ∈ S → u y ≤ 0)
    (huBoundary : ∀ y ∈ frontier (V.orthogonalProjectionOnto ⁻¹' S), u y = 0)
    (huDet : ∀ y, V.orthogonalProjectionOnto y ∈ S →
      (complexHessian realDirections imagDirections u y).det = 1)
    {x : E} (hx : V.orthogonalProjectionOnto x ∈ S) (hxDeep : u x ≤ -1 / 4) :
    let c := Real.sqrt ((32 * (n : ℝ) ^ 2)⁻¹ ^ (n - 1) / 2) / 16
    c ≤ infDist x (V.orthogonalProjectionOnto ⁻¹' S)ᶜ ∧
      Real.sqrt (∑ i, ‖affineWirtinger realDirections imagDirections (fderiv ℝ u x) i‖ ^ 2) ≤ c⁻¹ := by
  let c := Real.sqrt ((32 * (n : ℝ) ^ 2)⁻¹ ^ (n - 1) / 2) / 16
  let π := V.orthogonalProjectionOnto
  let U : Set E := π ⁻¹' S
  let K : Set E := V.subtypeL '' closure S
  have hU : IsOpen U := hS.preimage π.continuous
  have hπ : IsOpenMap π := π.isOpenMap
    (fun z => ⟨z, V.orthogonalProjectionOnto_mem_subspace_eq_self z⟩)
  have hK' : IsCompact K := hK.image V.subtypeL.continuous
  have hKU : K ⊆ closure U := by
    rintro _ ⟨z, hz, rfl⟩
    change (z : E) ∈ closure (π ⁻¹' S)
    rw [← hπ.preimage_closure_eq_closure_preimage π.continuous]
    simpa only [mem_preimage, π, V.orthogonalProjectionOnto_mem_subspace_eq_self] using hz
  have hconvS : Convex ℝ S := by
    have hEq : V.subtypeL ⁻¹' U = S := by
      ext z
      change π (z : E) ∈ S ↔ z ∈ S
      rw [V.orthogonalProjectionOnto_mem_subspace_eq_self]
    rw [← hEq]
    exact hconv.1.linear_preimage V.subtypeL.toLinearMap
  obtain ⟨P, k, hnorm, hlevel, hdist⟩ :=
    exists_normalized_support_at_infDist_cylinder V hS hconvS hproper hx
  let L := P.comp π
  have hLnorm : (∑ i, ‖affineWirtinger realDirections imagDirections L i‖ ^ 2) = 1 / 4 := by
    rw [affineWirtinger_norm_sq, hnorm, one_pow]
  have hrep (δ : ℝ) (z : E) (hz : z ∈ closure (U ∩ {y | L y + k < δ})) :
      ∃ y ∈ K ∩ closure (U ∩ {w | L w + k < δ}),
        u z = u y ∧ q z = q y ∧ L z + k = L y + k := by
    let Sδ := S ∩ {y : V | P y + k < δ}
    have heq : U ∩ {y | L y + k < δ} = π ⁻¹' Sδ := rfl
    rw [heq, ← hπ.preimage_closure_eq_closure_preimage π.continuous] at hz
    have hzS : π z ∈ closure S := closure_mono inter_subset_left hz
    refine ⟨(π z : E), ⟨⟨π z, hzS, rfl⟩, ?_⟩, huInv z, hqInv z, ?_⟩
    · rw [heq, ← hπ.preimage_closure_eq_closure_preimage π.continuous]
      change π ((π z : V) : E) ∈ closure Sδ
      simpa only [mem_preimage, π, V.orthogonalProjectionOnto_mem_subspace_eq_self] using hz
    · change P (π z) + k = P (π ((π z : V) : E)) + k
      rw [V.orthogonalProjectionOnto_mem_subspace_eq_self]
  have hdepth : c ≤ infDist x Uᶜ := (section_depth_lower_bound_of_compact_representatives
    hn realDirections imagDirections hU hK' hKU L k hu hu₂ hq hq₂ hlevel hqBounds hQ hLnorm
    huLower huBoundary huDet hrep hx hxDeep).trans hdist
  have hc : 0 < c := by
    dsimp [c]
    exact div_pos (Real.sqrt_pos.mpr (by positivity)) (by norm_num)
  refine ⟨hdepth, section_gradient_bound_of_depth hx hconv ?_ (huLower x (subset_closure hx))
    huUpper hc hdepth⟩
  exact (hu₂.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)


theorem convexOn_of_realBlockHessian_posSemidef {U : Set E} (hU : IsOpen U)
    (hconv : Convex ℝ U) {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (hR : ∀ x ∈ U, (realBlockHessian realDirections imagDirections u x).PosSemidef) :
    ConvexOn ℝ U u := by
  apply convexOn_of_realHessian_nonneg hU hconv hu
  intro x hx v
  let B := (EuclideanSpace.basisFun (Fin (n + n)) ℝ).toBasis
  let z (i : Fin n ⊕ Fin n) := B.repr v (finSumFinEquiv i)
  let e := Sum.elim (realDirections (n := n)) imagDirections
  have he (i : Fin n ⊕ Fin n) : e i = B (finSumFinEquiv i) := by
    rw [show B (finSumFinEquiv i) = EuclideanSpace.single (finSumFinEquiv i) 1 from
      EuclideanSpace.basisFun_apply (Fin (n + n)) ℝ _]
    cases i <;> rfl
  have hsum : (∑ i, z i • e i) = v := by
    simp only [he, z]
    exact (Equiv.sum_comp finSumFinEquiv (fun j => B.repr v j • B j)).trans (B.sum_repr v)
  have hquad : realHessian u x v v = z ⬝ᵥ (realBlockHessian realDirections imagDirections u x).mulVec z := by
    conv_lhs => rw [← hsum]
    simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, dotProduct,
      Matrix.mulVec, Finset.mul_sum, realBlockHessian, e]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [realHessian_symm (hu.contDiffAt (hU.mem_nhds hx)) _ _]
    ring
  rw [hquad]
  simpa only [star_trivial] using (hR x hx).dotProduct_mulVec_nonneg z

theorem infDist_compl_eq_infDist_frontier_of_open {U : Set E}
    (hU : IsOpen U) (hproper : U ≠ univ) {x : E} (hx : x ∈ U) :
    infDist x Uᶜ = infDist x (frontier U) := by
  obtain ⟨y, hy, h⟩ := exists_mem_frontier_infDist_compl_eq_dist hx hproper
  apply le_antisymm
  · exact infDist_le_infDist_of_subset
      (fun z hz => show z ∉ U from ((hU.frontier_eq ▸ hz) : z ∈ closure U \ U).2) ⟨y, hy⟩
  · exact (infDist_le_dist_of_mem hy).trans_eq h.symm


/-- The bounded-domain statement with the manuscript's Hessian hypothesis
and distance to the boundary. -/
theorem bounded_section_estimates
    (hn : 0 < n) {U : Set E} (hU : IsOpen U) (hK : IsCompact (closure U))
    (hconv : Convex ℝ U) {u q : E → ℝ}
    (hu : ContinuousOn u (closure U)) (hu₂ : ContDiffOn ℝ 2 u U)
    (hR : ∀ y ∈ U, (realBlockHessian realDirections imagDirections u y).PosSemidef)
    (hq : ContinuousOn q (closure U)) (hq₂ : ContDiffOn ℝ 2 q U)
    (hqBounds : ∀ y ∈ closure U, 0 ≤ q y ∧ q y ≤ 4 * (n : ℝ) ^ 2)
    (hQ : ∀ y ∈ U, (complexHessian realDirections imagDirections q y - 1).PosSemidef)
    (huLower : ∀ y ∈ closure U, -1 ≤ u y)
    (huUpper : ∀ y ∈ U, u y ≤ 0)
    (huBoundary : ∀ y ∈ frontier U, u y = 0)
    (huDet : ∀ y ∈ U, (complexHessian realDirections imagDirections u y).det = 1)
    {x : E} (hx : x ∈ U) (hxDeep : u x ≤ -1 / 4) :
    let c := Real.sqrt ((32 * (n : ℝ) ^ 2)⁻¹ ^ (n - 1) / 2) / 16
    c ≤ infDist x (frontier U) ∧
      Real.sqrt (∑ i, ‖affineWirtinger realDirections imagDirections (fderiv ℝ u x) i‖ ^ 2) ≤ c⁻¹ := by
  have hproper : U ≠ univ := by
    intro hEq
    have hbounded : Bornology.IsBounded (univ : Set E) := by
      simpa [hEq] using hK.isBounded
    exact (Filter.neBot_iff.mp (inferInstance : Filter.NeBot (Bornology.cobounded E)))
      (Bornology.cobounded_eq_bot_iff.mpr (Bornology.isBounded_univ.mp hbounded))
  rw [← infDist_compl_eq_infDist_frontier_of_open hU hproper hx]
  exact bounded_section_depth_and_gradient hn hU hK
    (convexOn_of_realBlockHessian_posSemidef hU hconv hu₂ hR)
    hu hu₂ hq hq₂ hqBounds hQ huLower huUpper huBoundary huDet hx hxDeep

/-- A translation-invariant set is the full preimage of its orthogonal
slice, and translation-invariant functions factor through the same slice. -/
theorem factors_through_orthogonal_slice
    (K : Submodule ℝ E) {U : Set E} {u : E → ℝ}
    (hU : ∀ x ∈ U, ∀ v ∈ K, x + v ∈ U)
    (hu : ∀ x, ∀ v ∈ K, u (x + v) = u x) :
    U = Kᗮ.orthogonalProjectionOnto ⁻¹' (Kᗮ.subtypeL ⁻¹' U) ∧
      ∀ x, u x = u (Kᗮ.orthogonalProjectionOnto x : E) := by
  have hP (x : E) : (Kᗮ.orthogonalProjectionOnto x : E) = x - K.starProjection x := by
    rw [K.orthogonalProjectionOnto_orthogonal]
  have hK (x : E) : K.starProjection x ∈ K := (K.orthogonalProjectionOnto x).prop
  constructor
  · ext x
    change x ∈ U ↔ (Kᗮ.orthogonalProjectionOnto x : E) ∈ U
    rw [hP]
    constructor
    · intro hx
      simpa only [sub_eq_add_neg] using hU x hx (-K.starProjection x) (K.neg_mem (hK x))
    · intro hx
      simpa only [sub_add_cancel] using hU _ hx (K.starProjection x) (hK x)
  · intro x
    rw [hP]
    simpa only [sub_add_cancel] using hu (x - K.starProjection x) (K.starProjection x) (hK x)


/-- The translation-invariant case of Lemma 3.1, using the orthogonal
real slice as the quotient. -/
theorem cylindrical_section_estimates
    (hn : 0 < n) (K : Submodule ℝ E) {U : Set E}
    (hU : IsOpen U) (hconv : Convex ℝ U)
    (hK : IsCompact (closure (Kᗮ.subtypeL ⁻¹' U)))
    (hUinv : ∀ y ∈ U, ∀ v ∈ K, y + v ∈ U)
    {u q : E → ℝ}
    (huInv : ∀ y, ∀ v ∈ K, u (y + v) = u y)
    (hqInv : ∀ y, ∀ v ∈ K, q (y + v) = q y)
    (hu : ContinuousOn u (closure U)) (hu₂ : ContDiffOn ℝ 2 u U)
    (hR : ∀ y ∈ U, (realBlockHessian realDirections imagDirections u y).PosSemidef)
    (hq : ContinuousOn q (closure U)) (hq₂ : ContDiffOn ℝ 2 q U)
    (hqConvex : ConvexOn ℝ univ q)
    (hqBounds : ∀ y ∈ closure U, 0 ≤ q y ∧ q y ≤ 4 * (n : ℝ) ^ 2)
    (hQ : ∀ y ∈ U, (complexHessian realDirections imagDirections q y - 1).PosSemidef)
    (huLower : ∀ y ∈ closure U, -1 ≤ u y)
    (huUpper : ∀ y ∈ U, u y ≤ 0)
    (huBoundary : ∀ y ∈ frontier U, u y = 0)
    (huDet : ∀ y ∈ U, (complexHessian realDirections imagDirections u y).det = 1)
    {x : E} (hx : x ∈ U) (hxDeep : u x ≤ -1 / 4) :
    let c := Real.sqrt ((32 * (n : ℝ) ^ 2)⁻¹ ^ (n - 1) / 2) / 16
    c ≤ infDist x (frontier U) ∧
      Real.sqrt (∑ i, ‖affineWirtinger realDirections imagDirections (fderiv ℝ u x) i‖ ^ 2) ≤ c⁻¹ := by
  let S : Set Kᗮ := Kᗮ.subtypeL ⁻¹' U
  obtain ⟨hEq, huProj⟩ := factors_through_orthogonal_slice K hUinv huInv
  have hqProj := (factors_through_orthogonal_slice K hUinv hqInv).2
  have hS : IsOpen S := hU.preimage Kᗮ.subtypeL.continuous
  have hproper : U ≠ univ := by
    intro hEqU
    have hqUpper : ∀ y : E, q y ≤ 4 * (n : ℝ) ^ 2 :=
      fun y => (hqBounds y (by simp [hEqU])).2
    have hqConst : ∀ y : E, q y = q 0 := by
      intro y
      have hcompare (a b : E) : q b ≤ q a := by
        by_contra! hlt
        let t := (4 * (n : ℝ) ^ 2 - q a) / (q b - q a) + 2
        have ht : 1 < t := by
          dsimp [t]
          have := div_nonneg (sub_nonneg.mpr (hqUpper a)) (sub_nonneg.mpr hlt.le)
          linarith
        let z := a + t • (b - a)
        have hb : (1 - t⁻¹) • a + t⁻¹ • z = b := by
          dsimp [z]
          rw [sub_smul, one_smul, smul_add, smul_smul, inv_mul_cancel₀ (by linarith : t ≠ 0),
            one_smul]
          abel
        have hcv := hqConvex.2 (mem_univ a) (mem_univ z)
          (sub_nonneg.mpr ((inv_le_one₀ (by linarith : 0 < t)).mpr ht.le))
          (inv_nonneg.mpr (by linarith : 0 ≤ t)) (sub_add_cancel 1 t⁻¹)
        rw [hb] at hcv
        simp only [smul_eq_mul] at hcv
        have hquot : q b - q a ≤ (q z - q a) / t := by
          rw [div_eq_mul_inv, mul_comm]
          linarith
        have hmul := (le_div_iff₀ (by linarith : 0 < t)).mp hquot
        have hprod : t * (q b - q a) =
            4 * (n : ℝ) ^ 2 - q a + 2 * (q b - q a) := by
          dsimp [t]
          rw [add_mul, div_mul_cancel₀ _ (sub_ne_zero.mpr hlt.ne')]
        linarith [hqUpper z]
      exact le_antisymm (hcompare 0 y) (hcompare y 0)
    have hqEq : q = fun _ => q 0 := funext hqConst
    have h := hQ x hx
    rw [hqEq] at h
    have hZero : complexHessian realDirections imagDirections (fun _ : E => q 0) x = 0 := by
      ext i j
      change dz (realDirections i) (imagDirections i)
        (dz (realDirections j) (-imagDirections j) (fun _ : E => (q 0 : ℂ))) x = 0
      have hinner : dz (realDirections j) (-imagDirections j) (fun _ : E => (q 0 : ℂ)) =
          fun _ : E => (0 : ℂ) := funext fun y => dz_const _ _ _ y
      rw [hinner, dz_const]
    rw [hZero, zero_sub] at h
    let i : Fin n := ⟨0, hn⟩
    have hbad := h.diag_nonneg (i := i)
    exact (not_le_of_gt zero_lt_one) (by simpa [Matrix.neg_apply] using hbad)
  have hSproper : S ≠ univ := by
    intro h
    apply hproper
    exact hEq.trans (by rw [show (Kᗮ.subtypeL ⁻¹' U) = (univ : Set Kᗮ) from h, preimage_univ])
  rw [← infDist_compl_eq_infDist_frontier_of_open hU hproper hx]
  have hConvU := convexOn_of_realBlockHessian_posSemidef hU hconv hu₂ hR
  rw [hEq] at hu hu₂ hq hq₂ hqBounds hQ huLower huUpper huBoundary huDet hx hConvU ⊢
  exact cylindrical_section_depth_and_gradient hn Kᗮ hS hK hSproper huProj hqProj
    hConvU hu hu₂ hq hq₂ hqBounds hQ huLower huUpper huBoundary huDet hx hxDeep

end CHS.Sections
