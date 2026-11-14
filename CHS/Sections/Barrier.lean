import CHS.Sections.Comparison

/-!
# Strip comparison for a normalized convex section
-/

set_option autoImplicit false
noncomputable section

open Filter Metric Set
open scoped BigOperators ComplexOrder ContDiff Topology

namespace CHS.Sections

open CHS.Calculus CHS.Algebra

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def sectionBarrier (ε δ C : ℝ) (q l : E → ℝ) (x : E) : ℝ :=
  ε * (q x - C) - 2 * l x / δ + (l x / δ) ^ 2

theorem contDiffOn_sectionBarrier {ε δ C : ℝ} {q l : E → ℝ} {U : Set E}
    (hq : ContDiffOn ℝ 2 q U) (hl : ContDiffOn ℝ 2 l U) :
    ContDiffOn ℝ 2 (sectionBarrier ε δ C q l) U := by
  unfold sectionBarrier
  exact ((contDiffOn_const.mul (hq.sub contDiffOn_const)).sub
    ((contDiffOn_const.mul hl).div_const δ)).add ((hl.div_const δ).pow 2)

theorem sectionBarrier_le_on_strip_of_det_gt_of_compact_representatives
    {n : ℕ} (a b : Fin n → E)
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ closure U)
    {u q l : E → ℝ} {ε δ C : ℝ} (hε : 0 ≤ ε) (hδ : 0 < δ)
    (hu : ContinuousOn u (closure U)) (hu₂ : ContDiffOn ℝ 2 u U)
    (hq : ContinuousOn q (closure U)) (hq₂ : ContDiffOn ℝ 2 q U)
    (hl : Continuous l) (hl₂ : ContDiffOn ℝ 2 l U)
    (hlevel : ∀ x ∈ U, 0 < l x) (hbound : ∀ x ∈ closure U, q x ≤ C)
    (huLower : ∀ x ∈ closure U, -1 ≤ u x)
    (huBoundary : ∀ x ∈ frontier U, u x = 0)
    (huDet : ∀ x ∈ U, (complexHessian a b u x).det = 1)
    (hpos : ∀ x ∈ U, (complexHessian a b (sectionBarrier ε δ C q l) x).PosDef)
    (hdet : ∀ x ∈ U, 1 < (complexHessian a b (sectionBarrier ε δ C q l) x).det)
    (hrep : ∀ x ∈ closure (U ∩ {y | l y < δ}),
      ∃ y ∈ K ∩ closure (U ∩ {z | l z < δ}), u x = u y ∧ q x = q y ∧ l x = l y) :
    ∀ x ∈ U, l x < δ → sectionBarrier ε δ C q l x ≤ u x := by
  let W := U ∩ {x | l x < δ}
  let f := sectionBarrier ε δ C q l
  have hW : IsOpen W := hU.inter (isOpen_lt hl continuous_const)
  have hWC : closure W ⊆ closure U := closure_mono inter_subset_left
  have hWK : IsCompact (K ∩ closure W) := hK.inter_right isClosed_closure
  have hWsub : W ⊆ U := inter_subset_left
  have hfC : ContinuousOn f (closure U) := by
    unfold f sectionBarrier
    exact ((continuousOn_const.mul (hq.sub continuousOn_const)).sub
      ((continuousOn_const.mul hl.continuousOn).div_const δ)).add
      ((hl.continuousOn.div_const δ).pow 2)
  have hlev : ∀ x ∈ closure W, 0 ≤ l x ∧ l x ≤ δ := by
    have hsubset : closure W ⊆ l ⁻¹' Icc 0 δ := by
      apply closure_minimal _ (isClosed_Icc.preimage hl)
      exact fun x hx => ⟨(hlevel x hx.1).le, hx.2.le⟩
    exact fun x hx => hsubset hx
  have hbd : ∀ x ∈ frontier W, f x ≤ u x := by
    intro x hx
    have hxC : x ∈ closure W := frontier_subset_closure hx
    have hxU := hWC hxC
    have hxW : x ∉ W := ((hW.frontier_eq ▸ hx) : x ∈ closure W \ W).2
    have hq0 : ε * (q x - C) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hε (sub_nonpos.mpr (hbound x hxU))
    by_cases hmem : x ∈ U
    · have hδx : l x = δ := le_antisymm (hlev x hxC).2
        (le_of_not_gt fun hlt => hxW ⟨hmem, hlt⟩)
      unfold f sectionBarrier
      rw [hδx, div_self hδ.ne']
      have h2 : 2 * δ / δ = 2 := by field_simp
      rw [h2]
      nlinarith [huLower x hxU]
    · have hux := huBoundary x (hU.frontier_eq ▸ ⟨hxU, hmem⟩)
      have hL0 : 0 ≤ l x / δ := div_nonneg (hlev x hxC).1 hδ.le
      have hL1 : l x / δ ≤ 1 := (div_le_iff₀ hδ).mpr (by simpa using (hlev x hxC).2)
      unfold f sectionBarrier
      rw [hux, mul_div_assoc]
      nlinarith [mul_nonneg hL0 (sub_nonneg.mpr hL1)]
  intro x hx hxδ
  apply le_on_closure_of_det_lt_of_compact_representatives hW hWK inter_subset_right a b
    (hfC.mono hWC) (hu.mono hWC) ((contDiffOn_sectionBarrier hq₂ hl₂).mono hWsub)
    (hu₂.mono hWsub) (fun y hy => hpos y hy.1)
    (fun y hy => by rw [huDet y hy.1]; exact hdet y hy.1) hbd
  · intro z hz
    obtain ⟨y, hy, heu, heq, hel⟩ := hrep z hz
    exact ⟨y, hy, by simp [f, sectionBarrier, heu, heq, hel]⟩
  · exact subset_closure ⟨hx, hxδ⟩


def affineWirtinger {ι : Type*} (a b : ι → E) (L : E →L[ℝ] ℝ) (i : ι) : ℂ :=
  (2 : ℂ)⁻¹ * ((L (a i) : ℂ) - Complex.I * (L (b i) : ℂ))

/-- The actual mixed Hessian of the normalized quadratic strip barrier. -/
theorem complexHessian_sectionBarrier {ι : Type*} (a b : ι → E)
    {q : E → ℝ} {x : E} (hq : ContDiffAt ℝ 2 q x)
    (L : E →L[ℝ] ℝ) (k ε δ C : ℝ) (hδ : δ ≠ 0) :
    complexHessian a b (sectionBarrier ε δ C q (fun y => L y + k)) x =
      (ε : ℂ) • complexHessian a b q x +
        ((2 / δ ^ 2 : ℝ) : ℂ) • Matrix.vecMulVec (affineWirtinger a b L)
          (star (affineWirtinger a b L)) := by
  let l (y : E) := L y + k
  let f := sectionBarrier ε δ C q l
  have hl : ContDiff ℝ 2 l := L.contDiff.add contDiff_const
  have hf : ContDiffAt ℝ 2 f x := by
    unfold f sectionBarrier
    exact ((contDiffAt_const.mul (hq.sub contDiffAt_const)).sub
      ((contDiffAt_const.mul hl.contDiffAt).div_const δ)).add
      ((hl.contDiffAt.div_const δ).pow 2)
  have hderivL (y : E) : HasFDerivAt l L y := L.hasFDerivAt.add_const k
  have hderiv (v w : E) : realHessian f x v w =
      ε * realHessian q x v w + (2 / δ ^ 2) * (L v * L w) := by
    let c : ℝ := 2 / δ ^ 2
    let R (y : E) := (c * l y - 2 / δ) • L
    have hFirst : fderiv ℝ f =ᶠ[𝓝 x] fun y => ε • fderiv ℝ q y + R y := by
      filter_upwards [hq.eventually (by simp)] with y hy
      have hqD := (hy.differentiableAt (by norm_num)).hasFDerivAt
      have hdL := hderivL y
      have hDdiv : HasFDerivAt (fun z => l z / δ) (δ⁻¹ • L) y := by
        simpa only [div_eq_mul_inv, mul_comm] using hdL.const_mul δ⁻¹
      have hTwo : HasFDerivAt (fun z => 2 * l z / δ) (δ⁻¹ • ((2 : ℝ) • L)) y := by
        simpa only [div_eq_mul_inv, mul_comm (δ⁻¹)] using (hdL.const_mul 2).const_mul δ⁻¹
      have h0 := ((hqD.sub_const C).const_mul ε).sub hTwo
      have h1 := hDdiv.pow 2
      have hsum := h0.add h1
      change HasFDerivAt f _ y at hsum
      rw [hsum.fderiv]
      ext z
      simp only [R, sub_apply, add_apply, smul_apply, smul_eq_mul, pow_one, show (2 - 1 : ℕ) = 1 by decide, nsmul_eq_mul, Nat.cast_ofNat, c]
      field_simp
      <;> ring
    have hD := (hq.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have hR : HasFDerivAt R ((c • L).smulRight L) x := by
      have h := ((hderivL x).const_mul c).sub_const (2 / δ)
      exact h.smul_const L
    have hs := (hD.hasFDerivAt.const_smul ε).add hR
    change HasFDerivAt (fun y => ε • fderiv ℝ q y + R y) _ x at hs
    unfold realHessian
    rw [hFirst.fderiv_eq, hs.fderiv]
    simp [c, mul_assoc]
  change complexHessian a b f x = _
  ext i j
  rw [complexHessian_real_entry hf, Matrix.add_apply, Matrix.smul_apply,
    complexHessian_real_entry hq, Matrix.smul_apply, Matrix.vecMulVec_apply]
  simp only [hderiv, Complex.ofReal_add, Complex.ofReal_mul, smul_eq_mul,
    affineWirtinger, Pi.star_apply, star_mul, star_sub, star_inv₀, star_ofNat,
    Complex.star_def, Complex.conj_ofReal, Complex.conj_I]
  ring_nf
  simp [Complex.I_sq]
  ring


theorem section_depth_lower_bound_of_compact_representatives
    {n : ℕ} (hn : 0 < n) (a b : Fin n → E)
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ closure U)
    {u q : E → ℝ} (L : E →L[ℝ] ℝ) (k : ℝ)
    (hu : ContinuousOn u (closure U)) (hu₂ : ContDiffOn ℝ 2 u U)
    (hq : ContinuousOn q (closure U)) (hq₂ : ContDiffOn ℝ 2 q U)
    (hlevel : ∀ y ∈ U, 0 < L y + k)
    (hqBounds : ∀ y ∈ closure U, 0 ≤ q y ∧ q y ≤ 4 * (n : ℝ) ^ 2)
    (hQ : ∀ y ∈ U, (complexHessian a b q y - 1).PosSemidef)
    (hL : (∑ i, ‖affineWirtinger a b L i‖ ^ 2) = 1 / 4)
    (huLower : ∀ y ∈ closure U, -1 ≤ u y)
    (huBoundary : ∀ y ∈ frontier U, u y = 0)
    (huDet : ∀ y ∈ U, (complexHessian a b u y).det = 1)
    (hrep : ∀ (δ : ℝ) (z : E), z ∈ closure (U ∩ {y | L y + k < δ}) →
      ∃ y ∈ K ∩ closure (U ∩ {w | L w + k < δ}),
        u z = u y ∧ q z = q y ∧ L z + k = L y + k)
    {x : E} (hx : x ∈ U) (hxDeep : u x ≤ -1 / 4) :
    Real.sqrt ((32 * (n : ℝ) ^ 2)⁻¹ ^ (n - 1) / 2) / 16 ≤ L x + k := by
  let ε := (32 * (n : ℝ) ^ 2)⁻¹
  let δ := Real.sqrt (ε ^ (n - 1) / 2)
  let C := 4 * (n : ℝ) ^ 2
  let l (y : E) := L y + k
  let f := sectionBarrier ε δ C q l
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hδ : 0 < δ := Real.sqrt_pos.mpr (by positivity)
  have hscale : δ ^ 2 = ε ^ (n - 1) / 2 := Real.sq_sqrt (by positivity)
  have hεC : ε * C = 1 / 8 := by
    dsimp [ε, C]
    have hn' : (n : ℝ) ≠ 0 := by positivity
    field_simp
    <;> ring
  have hH (y : E) (hy : y ∈ U) : complexHessian a b f y =
      (ε : ℂ) • complexHessian a b q y +
        ((2 / δ ^ 2 : ℝ) : ℂ) • Matrix.vecMulVec (affineWirtinger a b L)
          (star (affineWirtinger a b L)) :=
    complexHessian_sectionBarrier a b (hq₂.contDiffAt (hU.mem_nhds hy)) L k ε δ C hδ.ne'
  have hPos (y : E) (hy : y ∈ U) : (complexHessian a b f y).PosDef := by
    rw [hH y hy]
    have hQpos : (complexHessian a b q y).PosDef := by
      have h := Matrix.PosDef.one.add_posSemidef (hQ y hy)
      rwa [add_comm (1 : Matrix (Fin n) (Fin n) ℂ), sub_add_cancel] at h
    change (ε • complexHessian a b q y + (2 / δ ^ 2 : ℝ) •
      Matrix.vecMulVec (affineWirtinger a b L) (star (affineWirtinger a b L))).PosDef
    exact (hQpos.smul hε).add_posSemidef
      ((Matrix.posSemidef_vecMulVec_self_star _).smul (by positivity))
  have hGt (y : E) (hy : y ∈ U) : 1 < (complexHessian a b f y).det := by
    rw [hH y hy]
    exact section_barrier_det_gt_one hn (hQ y hy) (affineWirtinger a b L) hL hε hδ hscale
  change δ / 16 ≤ l x
  by_cases hxδ : l x < δ
  · have hle : f x ≤ u x :=
      sectionBarrier_le_on_strip_of_det_gt_of_compact_representatives a b hU hK hKU hε.le hδ
        hu hu₂ hq hq₂ (L.continuous.add continuous_const) (L.contDiff.add contDiff_const).contDiffOn
        hlevel (fun y hy => (hqBounds y hy).2) huLower huBoundary huDet hPos hGt (hrep δ) x hx hxδ
    have h0 : 0 ≤ ε * q x := mul_nonneg hε.le (hqBounds x (subset_closure hx)).1
    have hfLower : -(1 / 8 : ℝ) - 2 * l x / δ ≤ f x := by
      unfold f sectionBarrier
      nlinarith only [h0, hεC, sq_nonneg (l x / δ)]
    have hquot : 1 / 8 ≤ 2 * l x / δ := by linarith
    have hmul := (le_div_iff₀ hδ).mp hquot
    linarith
  · have hxδ' := le_of_not_gt hxδ
    linarith

end CHS.Sections
