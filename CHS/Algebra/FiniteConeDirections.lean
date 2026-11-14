import CHS.Algebra.TraceDetConcavity
import CHS.Algebra.ComplexProjection
import CHS.Analysis.FinitePositiveCover
import Mathlib.Analysis.Matrix.Normed

/-!
# A fixed finite family of real directions detects an elliptic half-cone

The directions and the constant depend only on a compact family of positive
Hermitian weights. They work for every real symmetric matrix H whose
weighted complex projection has nonnegative trace. No directional
decomposition or oscillation estimate is assumed.
-/

set_option autoImplicit false
noncomputable section

open Matrix Set Metric
open scoped BigOperators ComplexOrder Matrix.Norms.Elementwise

namespace CHS.Algebra

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "J" => ι ⊕ ι
local notation "V" => Matrix J J ℝ
local notation "W" => Matrix ι ι ℂ

def realMatrixQuadratic (H : V) (z : J → ℝ) : ℝ := z ⬝ᵥ H.mulVec z

theorem realMatrixQuadratic_smul (c : ℝ) (H : V) (z : J → ℝ) :
    realMatrixQuadratic (c • H) z = c * realMatrixQuadratic H z := by
  simp only [realMatrixQuadratic, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

theorem realMatrixQuadratic_sub (H K : V) (z : J → ℝ) :
    realMatrixQuadratic (H - K) z = realMatrixQuadratic H z - realMatrixQuadratic K z := by
  simp only [realMatrixQuadratic, Matrix.sub_mulVec, dotProduct_sub]

theorem continuous_realMatrixQuadratic (z : J → ℝ) :
    Continuous (fun H : V => realMatrixQuadratic H z) := by
  unfold realMatrixQuadratic dotProduct Matrix.mulVec
  fun_prop

def realMatrixQuadraticWeight (z : J → ℝ) : ℝ := (∑ i, |z i|) ^ 2

theorem abs_realMatrixQuadratic_le (H : V) (z : J → ℝ) :
    |realMatrixQuadratic H z| ≤ realMatrixQuadraticWeight z * ‖H‖ := by
  have he (i j : J) : |H i j| ≤ ‖H‖ := by
    simpa only [Real.norm_eq_abs] using Matrix.norm_entry_le_entrywise_sup_norm H (i := i) (j := j)
  calc
    |realMatrixQuadratic H z| = |∑ i, z i * ∑ j, H i j * z j| := rfl
    _ ≤ ∑ i, |z i * ∑ j, H i j * z j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |z i| * |∑ j, H i j * z j| := by simp only [abs_mul]
    _ ≤ ∑ i, |z i| * ∑ j, |H i j * z j| := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _)
    _ ≤ ∑ i, |z i| * ∑ j, (‖H‖ * |z j|) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (he i j) (abs_nonneg _)
    _ = realMatrixQuadraticWeight z * ‖H‖ := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul, realMatrixQuadraticWeight]
      ring

theorem exists_positive_quadratic_of_weighted_projection_nonneg
    {A : W} (hA : A.PosDef) {H : V} (hH : H.IsHermitian) (hne : H ≠ 0)
    (ht : 0 ≤ (A * complexProjection H).trace.re) :
    ∃ z : J → ℝ, 0 < realMatrixQuadratic H z := by
  by_contra! hq
  have hneg : (-H).PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH.neg
    intro z
    rw [star_trivial, Matrix.neg_mulVec, dotProduct_neg, neg_nonneg]
    exact hq z
  have hP := complexProjection_posSemidef hneg
  have htrace : (A * complexProjection (-H)).trace.re = 0 := by
    apply le_antisymm
    · simpa only [complexProjection_neg, Matrix.mul_neg, Matrix.trace_neg, Complex.neg_re]
        using neg_nonpos.mpr ht
    · exact trace_product_posSemidef_nonneg hA.posSemidef hP
  have hPzero := eq_zero_of_posDef_trace_product_re_zero hA hP htrace
  exact hne (neg_eq_zero.mp (eq_zero_of_posSemidef_complexProjection_zero hneg hPzero))

theorem exists_finite_directions_detecting_elliptic_half_cone
    {S : Set W} (hS : IsCompact S) (hpos : ∀ A ∈ S, A.PosDef) :
    ∃ t : Finset (J → ℝ), ∃ C : ℝ, 0 < C ∧
      ∀ A ∈ S, ∀ H : V, H.IsHermitian →
        0 ≤ (A * complexProjection H).trace.re →
        ‖H‖ ≤ C * ∑ z ∈ t, max (realMatrixQuadratic H z) 0 := by
  classical
  let K : Set (W × V) := (S ×ˢ sphere (0 : V) 1) ∩
    {p | p.2.IsHermitian} ∩ {p | 0 ≤ (p.1 * complexProjection p.2).trace.re}
  have htr : Continuous (fun p : W × V => (p.1 * complexProjection p.2).trace.re) :=
    Complex.continuous_re.comp
      (continuous_fst.mul (continuous_complexProjection.comp continuous_snd)).matrix_trace
  have hK : IsCompact K :=
    ((hS.prod (isCompact_sphere (0 : V) 1)).inter_right
      (isClosed_eq continuous_snd.matrix_conjTranspose continuous_snd)).inter_right
      (isClosed_le continuous_const htr)
  obtain ⟨t, c, hc, hlower⟩ := CHS.Analysis.finite_positive_sum_lower_bound_on_compact hK
    (fun z p => realMatrixQuadratic p.2 z)
    (fun z => (continuous_realMatrixQuadratic z).comp continuous_snd) (by
      intro p hp
      have hn : ‖p.2‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hp.1.1.2
      have hnz : p.2 ≠ 0 := by intro hz; simp only [hz, norm_zero] at hn; norm_num at hn
      exact exists_positive_quadratic_of_weighted_projection_nonneg
        (hpos p.1 hp.1.1.1) hp.1.2 hnz hp.2)
  refine ⟨t, c⁻¹, inv_pos.mpr hc, ?_⟩
  intro A hA H hH ht
  by_cases hz : H = 0
  · simp [hz, realMatrixQuadratic]
  have hn : 0 < ‖H‖ := norm_pos_iff.mpr hz
  let N : V := ‖H‖⁻¹ • H
  have hNnorm : N ∈ sphere (0 : V) 1 := by
    simp only [N, mem_sphere, dist_zero_right, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hn.le), inv_mul_cancel₀ hn.ne']
  have hNherm : N.IsHermitian := hH.smul (by rfl : IsSelfAdjoint (‖H‖⁻¹ : ℝ))
  have hNtrace : 0 ≤ (A * complexProjection N).trace.re := by
    simp only [N, complexProjection_smul, Matrix.mul_smul, Matrix.trace_smul,
      Complex.smul_re, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr hn.le) ht
  have h := hlower (A, N) ⟨⟨⟨hA, hNnorm⟩, hNherm⟩, hNtrace⟩
  have hsum : (∑ z ∈ t, max (realMatrixQuadratic N z) 0) =
      ‖H‖⁻¹ * ∑ z ∈ t, max (realMatrixQuadratic H z) 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    simp only [N, realMatrixQuadratic_smul,
      mul_max_of_nonneg _ _ (inv_nonneg.mpr hn.le), mul_zero]
  rw [hsum] at h
  have hmul := mul_le_mul_of_nonneg_left h hn.le
  simp only [← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul] at hmul
  apply (mul_le_mul_iff_of_pos_left hc).mp
  rw [← mul_assoc c c⁻¹, mul_inv_cancel₀ hc.ne', one_mul]
  simpa only [mul_comm] using hmul

/-- A single family applies to every pair in a determinant-one matrix field.
The estimate is asymmetric only in the deficits on the right. -/
theorem norm_sub_le_directional_deficits
    {X : Type*} {S : Set W} {t : Finset (J → ℝ)} {C : ℝ} (hC : 0 ≤ C)
    (hdetect : ∀ A ∈ S, ∀ H : V, H.IsHermitian →
      0 ≤ (A * complexProjection H).trace.re →
      ‖H‖ ≤ C * ∑ z ∈ t, max (realMatrixQuadratic H z) 0)
    {U : Set X} {H : X → V}
    (hH : ∀ x ∈ U, (H x).IsHermitian)
    (hA : ∀ x ∈ U, (complexProjection (H x)).PosDef)
    (hdet : ∀ x ∈ U, (complexProjection (H x)).det = 1)
    (hweight : ∀ x ∈ U, (complexProjection (H x))⁻¹ ∈ S)
    {M : (J → ℝ) → ℝ}
    (hM : ∀ z ∈ t, ∀ x ∈ U, realMatrixQuadratic (H x) z ≤ M z)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    ‖H x - H y‖ ≤ C * ∑ z ∈ t, (M z - realMatrixQuadratic (H y) z) := by
  have htrace : 0 ≤ ((complexProjection (H y))⁻¹ * complexProjection (H x - H y)).trace.re := by
    rw [complexProjection_sub]
    exact trace_inv_mul_sub_nonneg_of_det_eq (hA y hy) (hA x hx)
      ((hdet x hx).trans (hdet y hy).symm)
  apply (hdetect _ (hweight y hy) _ ((hH x hx).sub (hH y hy)) htrace).trans
  apply mul_le_mul_of_nonneg_left _ hC
  apply Finset.sum_le_sum
  intro z hz
  rw [realMatrixQuadratic_sub]
  exact max_le (sub_le_sub_right (hM z hz x hx) _)
    (sub_nonneg.mpr (hM z hz y hy))

end CHS.Algebra
