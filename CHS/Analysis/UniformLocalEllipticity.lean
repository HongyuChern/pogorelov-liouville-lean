import CHS.Analysis.CompactEllipticity

/-! # Uniform local coefficients from one compact positive matrix family -/

set_option autoImplicit false
noncomputable section

open DeGiorgi Set Metric MeasureTheory
open scoped BigOperators RealInnerProductSpace Matrix.Norms.Elementwise

namespace CHS.Analysis

variable {d : ℕ} [NeZero d]
local notation "E" => AmbientSpace d

theorem uniform_local_normalization_of_compact_family
    {S : Set (Matrix (Fin d) (Fin d) ℝ)} (hS : IsCompact S) (hne : S.Nonempty)
    (hpos : ∀ M ∈ S, M.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∃ L : ℝ, 1 ≤ L ∧
      ∀ U : Set E, MeasurableSet U →
      ∀ A : E → Matrix (Fin d) (Fin d) ℝ, ContinuousOn A U →
      (∀ x ∈ U, A x ∈ S) →
      ∃ B : NormalizedEllipticCoeff d U, B.1.Λ = L ∧
        ∀ x ∈ U, B.1.a x = c⁻¹ • A x := by
  classical
  obtain ⟨c, hc, hlow⟩ := uniform_coercivity_of_compact_matrix_family hS hne hpos
  obtain ⟨b, hb, hinv⟩ := uniform_coercivity_of_compact_matrix_family
    (compact_inverse_matrix_family hS hpos) (hne.image _)
    (by rintro _ ⟨M, hM, rfl⟩; exact (hpos M hM).inv)
  let L : ℝ := max 1 (c * b)⁻¹
  have hL : 1 ≤ L := le_max_left _ _
  refine ⟨c, hc, L, hL, ?_⟩
  intro U hU A hA hrange
  let A' : E → Matrix (Fin d) (Fin d) ℝ := U.piecewise A (fun _ => 1)
  have hA' (i j : Fin d) : Measurable (fun x => A' x i j) := by
    have hfun : (fun x => A' x i j) =
        U.piecewise (fun x => A x i j) (fun _ => (1 : Matrix (Fin d) (Fin d) ℝ) i j) := by
      funext x
      by_cases hx : x ∈ U <;> simp [A', hx]
    rw [hfun]
    exact ContinuousOn.measurable_piecewise
      ((continuous_apply j).comp_continuousOn ((continuous_apply i).comp_continuousOn hA))
      continuousOn_const hU
  have heq (x : E) (hx : x ∈ U) : A' x = A x := piecewise_eq_of_mem U A (fun _ => 1) hx
  let B : EllipticCoeff d U := {
    a := fun x => c⁻¹ • A' x
    lam := 1
    Λ := L
    measurable_comp := by
      intro i j
      exact (hA' i j).const_mul c⁻¹
    hlam := zero_lt_one
    hΛ := hL
    coercive := by
      filter_upwards [ae_restrict_mem hU] with x hx
      intro v
      rw [heq x hx, matMulE_smul_matrix, real_inner_smul_right]
      simpa only [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] using
        mul_le_mul_of_nonneg_left (hlow (A x) (hrange x hx) v) (inv_nonneg.mpr hc.le)
    coercive_inv := by
      filter_upwards [ae_restrict_mem hU] with x hx
      intro v
      rw [heq x hx]
      have hdet := isUnit_iff_ne_zero.mpr (hpos (A x) (hrange x hx)).det_pos.ne'
      let k : ℝˣ := Units.mk0 c⁻¹ (inv_ne_zero hc.ne')
      have hscale : (c⁻¹ • A x)⁻¹ = c • (A x)⁻¹ := by
        simpa only [Units.smul_def, Units.val_inv_eq_inv_val, k, Units.val_mk0, inv_inv] using
          Matrix.inv_smul' (A x) k hdet
      rw [hscale, matMulE_smul_matrix, real_inner_smul_right]
      have hLb : L⁻¹ ≤ c * b := by
        simpa only [inv_inv] using (inv_le_inv₀ (lt_of_lt_of_le zero_lt_one hL)
          (inv_pos.mpr (mul_pos hc hb))).mpr (le_max_right 1 (c * b)⁻¹)
      have hix := hinv (A x)⁻¹ (mem_image_of_mem _ (hrange x hx)) v
      exact (mul_le_mul_of_nonneg_right hLb (sq_nonneg _)).trans
        (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hix hc.le) }
  exact ⟨⟨B, rfl⟩, rfl, fun x hx => congrArg (fun M => c⁻¹ • M) (heq x hx)⟩

end CHS.Analysis
