import CHS.Analysis.LocalEllipticity
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# One ellipticity normalization for a whole compact positive matrix family

The two coercivity constants are chosen over a compact family of matrices
and its inverse image, once and for all.  The resulting actual global
coefficient field can be restricted to any ball without changing its
ellipticity ratio.  This avoids radius-dependent local constants.
-/

set_option autoImplicit false
noncomputable section

open DeGiorgi Set Metric MeasureTheory
open scoped BigOperators RealInnerProductSpace Matrix.Norms.Elementwise

namespace CHS.Analysis

variable {d : ℕ} [NeZero d]
local notation "E" => AmbientSpace d

theorem uniform_coercivity_of_compact_matrix_family
    {S : Set (Matrix (Fin d) (Fin d) ℝ)} (hS : IsCompact S) (hne : S.Nonempty)
    (hpos : ∀ A ∈ S, A.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ A ∈ S, ∀ v : E,
      c * ‖v‖ ^ 2 ≤ ⟪v, matMulE A v⟫ := by
  let V : Set E := sphere 0 1
  have hV : V.Nonempty := by
    let i : Fin d := ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩
    exact ⟨EuclideanSpace.single i 1, by simp [V]⟩
  let q : Matrix (Fin d) (Fin d) ℝ × E → ℝ := fun p => ⟪p.2, matMulE p.1 p.2⟫
  have hq : Continuous q := by
    simp only [q, EuclideanSpace.inner_eq_star_dotProduct, matMulE_ofLp,
      dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial]
    fun_prop
  obtain ⟨p, hp, hmin⟩ := (hS.prod (isCompact_sphere (0 : E) 1)).exists_isMinOn
    (hne.prod hV) hq.continuousOn
  have hpNorm : ‖p.2‖ = 1 := by simpa only [V, mem_sphere, dist_zero_right] using hp.2
  have hpNe : p.2 ≠ 0 := by intro hz; simp only [hz, norm_zero] at hpNorm; norm_num at hpNorm
  have hc : 0 < q p := by
    change 0 < ⟪p.2, matMulE p.1 p.2⟫
    rw [EuclideanSpace.inner_eq_star_dotProduct, matMulE_ofLp, dotProduct_comm]
    exact (hpos p.1 hp.1).dotProduct_mulVec_pos
      (fun hz => hpNe (WithLp.ofLp_injective 2 (by simpa using hz)))
  refine ⟨q p, hc, ?_⟩
  intro A hA v
  by_cases hv : v = 0
  · simp [hv, matMulE]
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let w : E := ‖v‖⁻¹ • v
  have hw : w ∈ V := by simp [V, w, mem_sphere, dist_zero_right, norm_smul, hn.ne']
  have hle : q p ≤ ⟪w, matMulE A w⟫ := hmin (show (A, w) ∈ S ×ˢ V from ⟨hA, hw⟩)
  have hscale : matMulE A (‖v‖ • w) = ‖v‖ • matMulE A w := by
    ext i
    simp [matMulE_apply, Matrix.mulVec_smul]
  have hvw : ‖v‖ • w = v := by simp only [w, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  calc
    q p * ‖v‖ ^ 2 ≤ ⟪w, matMulE A w⟫ * ‖v‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hle (sq_nonneg _)
    _ = ⟪‖v‖ • w, matMulE A (‖v‖ • w)⟫ := by
      rw [hscale, real_inner_smul_right (‖v‖ • w) (matMulE A w) ‖v‖,
        real_inner_smul_left w (matMulE A w) ‖v‖]
      ring
    _ = _ := by rw [hvw]

theorem compact_inverse_matrix_family
    {S : Set (Matrix (Fin d) (Fin d) ℝ)} (hS : IsCompact S)
    (hpos : ∀ A ∈ S, A.PosDef) :
    IsCompact ((fun A : Matrix (Fin d) (Fin d) ℝ => A⁻¹) '' S) := by
  apply hS.image_of_continuousOn
  intro A hA
  apply (continuousAt_matrix_inv A _).continuousWithinAt
  simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ (hpos A hA).det_pos.ne'

theorem exists_global_normalizedEllipticCoeff_of_compact_range
    {A : E → Matrix (Fin d) (Fin d) ℝ} (hA : Continuous A)
    {S : Set (Matrix (Fin d) (Fin d) ℝ)} (hS : IsCompact S)
    (hrange : ∀ x, A x ∈ S) (hpos : ∀ M ∈ S, M.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∃ B : NormalizedEllipticCoeff d univ,
      ∀ x, B.1.a x = c⁻¹ • A x := by
  have hne : S.Nonempty := ⟨A 0, hrange 0⟩
  obtain ⟨c, hc, hlow⟩ := uniform_coercivity_of_compact_matrix_family hS hne hpos
  obtain ⟨b, hb, hinv⟩ := uniform_coercivity_of_compact_matrix_family
    (compact_inverse_matrix_family hS hpos) (hne.image _)
    (by rintro _ ⟨M, hM, rfl⟩; exact (hpos M hM).inv)
  let L : ℝ := max 1 (c * b)⁻¹
  have hL : 1 ≤ L := le_max_left _ _
  let B : EllipticCoeff d univ := {
    a := fun x => c⁻¹ • A x
    lam := 1
    Λ := L
    measurable_comp := by
      intro i j
      exact (((continuous_apply j).comp ((continuous_apply i).comp hA)).const_mul c⁻¹).measurable
    hlam := zero_lt_one
    hΛ := hL
    coercive := Filter.Eventually.of_forall (fun x v => by
      rw [matMulE_smul_matrix, real_inner_smul_right]
      simpa only [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] using
        mul_le_mul_of_nonneg_left (hlow (A x) (hrange x) v) (inv_nonneg.mpr hc.le))
    coercive_inv := Filter.Eventually.of_forall (fun x v => by
      have hdet := isUnit_iff_ne_zero.mpr (hpos (A x) (hrange x)).det_pos.ne'
      let k : ℝˣ := Units.mk0 c⁻¹ (inv_ne_zero hc.ne')
      have hscale : (c⁻¹ • A x)⁻¹ = c • (A x)⁻¹ := by
        simpa only [Units.smul_def, Units.val_inv_eq_inv_val, k, Units.val_mk0, inv_inv] using
          Matrix.inv_smul' (A x) k hdet
      rw [hscale, matMulE_smul_matrix, real_inner_smul_right]
      have hLb : L⁻¹ ≤ c * b := by
        simpa only [inv_inv] using (inv_le_inv₀ (lt_of_lt_of_le zero_lt_one hL)
          (inv_pos.mpr (mul_pos hc hb))).mpr (le_max_right 1 (c * b)⁻¹)
      have hix := hinv (A x)⁻¹ (mem_image_of_mem _ (hrange x)) v
      exact (mul_le_mul_of_nonneg_right hLb (sq_nonneg _)).trans
        (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hix hc.le)) }
  exact ⟨c, hc, ⟨B, rfl⟩, fun _ => rfl⟩

end CHS.Analysis
