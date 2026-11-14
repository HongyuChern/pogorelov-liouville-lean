import CHS.Analysis.LinearizedFlux

/-!
# Normalized elliptic coefficients on a compact ball

A continuous positive definite coefficient matrix and its inverse have
uniform lower bounds on the ball. The normalization is by a positive
constant, so it preserves the sign of the divergence.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open DeGiorgi Metric MeasureTheory Set
open scoped BigOperators InnerProductSpace

namespace CHS.Analysis

variable {d : ℕ}
local notation "E" => AmbientSpace d

theorem matMulE_smul_matrix (A : Matrix (Fin d) (Fin d) ℝ) (c : ℝ) (v : E) :
    matMulE (c • A) v = c • matMulE A v := by
  ext i
  simp [matMulE_apply, Matrix.smul_mulVec, PiLp.smul_apply]

private theorem matMulE_smul_vector (A : Matrix (Fin d) (Fin d) ℝ) (c : ℝ) (v : E) :
    matMulE A (c • v) = c • matMulE A v := by
  ext i
  simp [matMulE_apply, Matrix.mulVec_smul]

private theorem matMulE_inner_pos {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.PosDef)
    {v : E} (hv : v ≠ 0) : 0 < ⟪v, matMulE A v⟫_ℝ := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, matMulE_ofLp, dotProduct_comm]
  exact hA.dotProduct_mulVec_pos (fun h => hv (WithLp.ofLp_injective 2 (by simpa using h)))

private theorem matMulE_inner_continuousOn
    {A : E → Matrix (Fin d) (Fin d) ℝ} {K : Set E}
    (hA : ∀ i j, ContinuousOn (fun x => A x i j) K) :
    ContinuousOn (fun p : E × E => ⟪p.2, matMulE (A p.1) p.2⟫_ℝ) (K ×ˢ univ) := by
  apply continuous_snd.continuousOn.inner
  apply (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).comp_continuousOn
  apply continuousOn_pi.mpr
  intro i
  change ContinuousOn (fun p : E × E => ∑ j, A p.1 i j * p.2 j) (K ×ˢ univ)
  apply continuousOn_finsetSum
  intro j _
  exact ((hA i j).comp continuous_fst.continuousOn (fun _ hx => hx.1)).mul
    (((EuclideanSpace.proj j).continuous.comp continuous_snd).continuousOn)

private theorem compact_coercivity [NeZero d]
    {A : E → Matrix (Fin d) (Fin d) ℝ} {K : Set E}
    (hK : IsCompact K) (hne : K.Nonempty)
    (hA : ∀ i j, ContinuousOn (fun x => A x i j) K)
    (hpos : ∀ x ∈ K, (A x).PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, ∀ v : E, c * ‖v‖ ^ 2 ≤ ⟪v, matMulE (A x) v⟫_ℝ := by
  let S : Set E := sphere 0 1
  have hS : S.Nonempty := by
    let i : Fin d := ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩
    exact ⟨EuclideanSpace.single i 1, by simp [S]⟩
  let q (p : E × E) := ⟪p.2, matMulE (A p.1) p.2⟫_ℝ
  have hC : IsCompact (K ×ˢ S) := hK.prod (isCompact_sphere _ _)
  have hq : ContinuousOn q (K ×ˢ S) :=
    (matMulE_inner_continuousOn hA).mono (Set.prod_mono_right (subset_univ S))
  obtain ⟨p, hp, hmin⟩ := hC.exists_isMinOn (hne.prod hS) hq
  let c := ⟪p.2, matMulE (A p.1) p.2⟫_ℝ
  have hpNorm : ‖p.2‖ = 1 := by simpa [S, mem_sphere] using hp.2
  have hpNe : p.2 ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hpNorm
    exact zero_ne_one hpNorm
  have hc : 0 < c := matMulE_inner_pos (hpos p.1 hp.1) hpNe
  have hbound (x : E) (hx : x ∈ K) (v : E) :
      c * ‖v‖ ^ 2 ≤ ⟪v, matMulE (A x) v⟫_ℝ := by
    by_cases hv : v = 0
    · simp [hv, matMulE]
    have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    let w : E := ‖v‖⁻¹ • v
    have hw : w ∈ S := by
      change dist w 0 = 1
      rw [dist_zero_right]
      simp [w, norm_smul, hn.ne']
    have hpw : (x, w) ∈ K ×ˢ S := ⟨hx, hw⟩
    have hle : c ≤ q (x, w) := hmin hpw
    change c ≤ ⟪w, matMulE (A x) w⟫_ℝ at hle
    have hvw : ‖v‖ • w = v := by
      simp [w, smul_smul, hn.ne']
    calc
      c * ‖v‖ ^ 2 ≤ ⟪w, matMulE (A x) w⟫_ℝ * ‖v‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hle (sq_nonneg _)
      _ = ⟪‖v‖ • w, matMulE (A x) (‖v‖ • w)⟫_ℝ := by
        rw [matMulE_smul_vector (A x) ‖v‖ w,
          real_inner_smul_right (‖v‖ • w) (matMulE (A x) w) ‖v‖,
          real_inner_smul_left w (matMulE (A x) w) ‖v‖]
        ring
      _ = ⟪v, matMulE (A x) v⟫_ℝ := by rw [hvw]
  exact Exists.intro c (And.intro hc hbound)

private theorem continuousOn_matrixInverse
    {A : E → Matrix (Fin d) (Fin d) ℝ} {K : Set E}
    (hA : ∀ i j, ContinuousOn (fun x => A x i j) K)
    (hpos : ∀ x ∈ K, (A x).PosDef) (i j : Fin d) :
    ContinuousOn (fun x => (A x)⁻¹ i j) K := by
  have hmat : ContinuousOn A K :=
    continuousOn_pi.mpr fun i => continuousOn_pi.mpr (hA i)
  intro x hx
  have hinv : ContinuousAt Inv.inv (A x) := by
    apply continuousAt_matrix_inv
    rw [Ring.inverse_eq_inv']
    exact continuousAt_id.inv₀ (ne_of_gt (hpos x hx).det_pos)
  exact ((continuous_apply j).continuousAt.comp_continuousWithinAt
    ((continuous_apply i).continuousAt.comp_continuousWithinAt (hinv.comp_continuousWithinAt (hmat x hx))))

/-- Local continuity and pointwise positivity give the exact normalized
coefficient interface on an open ball. The globally measurable
representative agrees pointwise with the scaled matrix on the ball. -/
theorem exists_normalizedEllipticCoeff_on_ball [NeZero d]
    {A : E → Matrix (Fin d) (Fin d) ℝ} {x : E} {r : ℝ} (hr : 0 < r)
    (hA : ∀ i j, ContinuousOn (fun y => A y i j) (closedBall x r))
    (hpos : ∀ y ∈ closedBall x r, (A y).PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∃ B : NormalizedEllipticCoeff d (ball x r),
      ∀ y ∈ ball x r, B.1.a y = c⁻¹ • A y := by
  classical
  have hne : (closedBall x r).Nonempty := ⟨x, mem_closedBall_self hr.le⟩
  obtain ⟨c, hc, hlow⟩ := compact_coercivity (isCompact_closedBall x r) hne hA hpos
  obtain ⟨b, hb, hinv⟩ := compact_coercivity (isCompact_closedBall x r) hne
    (continuousOn_matrixInverse hA hpos) (fun y hy => (hpos y hy).inv)
  let M : E → Matrix (Fin d) (Fin d) ℝ :=
    (ball x r).piecewise (fun y => c⁻¹ • A y) (fun _ => 1)
  have hM (y : E) (hy : y ∈ ball x r) : M y = c⁻¹ • A y :=
    by simp [M, hy]
  have hMeas (i j : Fin d) : Measurable (fun y => M y i j) := by
    have heq : (fun y => M y i j) =
        (ball x r).piecewise (fun y => c⁻¹ * A y i j) (fun _ => (1 : Matrix (Fin d) (Fin d) ℝ) i j) := by
      funext y
      by_cases hy : y ∈ ball x r <;> simp [M, hy, Matrix.smul_apply, smul_eq_mul]
    rw [heq]
    exact ContinuousOn.measurable_piecewise
      (continuousOn_const.mul ((hA i j).mono ball_subset_closedBall)) continuousOn_const
      measurableSet_ball
  let L : ℝ := max 1 (c * b)⁻¹
  have hL : 1 ≤ L := le_max_left _ _
  let B : EllipticCoeff d (ball x r) := {
    a := M
    lam := 1
    Λ := L
    measurable_comp := hMeas
    hlam := zero_lt_one
    hΛ := hL
    coercive := by
      filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_ball (x := x) (ε := r))]
        with y hy
      intro v
      rw [hM y hy, matMulE_smul_matrix, real_inner_smul_right]
      simpa only [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] using
        mul_le_mul_of_nonneg_left (hlow y (ball_subset_closedBall hy) v)
          (inv_nonneg.mpr hc.le)
    coercive_inv := by
      filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_ball (x := x) (ε := r))]
        with y hy
      intro v
      have hdet := isUnit_iff_ne_zero.mpr (ne_of_gt (hpos y (ball_subset_closedBall hy)).det_pos)
      let k : ℝˣ := Units.mk0 c⁻¹ (inv_ne_zero hc.ne')
      have hscale : (c⁻¹ • A y)⁻¹ = c • (A y)⁻¹ := by
        simpa only [Units.smul_def, Units.val_inv_eq_inv_val, k, Units.val_mk0, inv_inv] using
          Matrix.inv_smul' (A y) k hdet
      rw [hM y hy, hscale, matMulE_smul_matrix, real_inner_smul_right]
      have hΛ : L⁻¹ ≤ c * b := by
        simpa only [inv_inv] using (inv_le_inv₀ (lt_of_lt_of_le zero_lt_one hL)
          (inv_pos.mpr (mul_pos hc hb))).mpr (le_max_right (1 : ℝ) (c * b)⁻¹)
      exact (mul_le_mul_of_nonneg_right hΛ (sq_nonneg _)).trans
        (by simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_left (hinv y (ball_subset_closedBall hy) v) hc.le) }
  exact ⟨c, hc, ⟨B, rfl⟩, hM⟩

end CHS.Analysis
