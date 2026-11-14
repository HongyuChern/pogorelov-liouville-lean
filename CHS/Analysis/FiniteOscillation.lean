import CHS.Analysis.CompactOscillation

/-!
# Geometric oscillation contraction from finitely many weak supersolutions

The hypotheses expose the precise finite-direction comparison needed from
the nonlinear equation. All extrema are actual extrema on closed balls.
The contraction factor depends only on dimension, ellipticity, the number
of directions and their comparison constant; it is independent of radius.
-/

set_option autoImplicit false
noncomputable section

open DeGiorgi Set Metric MeasureTheory
open scoped BigOperators

namespace CHS.Analysis

variable {d : ℕ} [NeZero d]
local notation "E" => AmbientSpace d

def finiteOscillationConstant (d : ℕ) [NeZero d] (hd : 2 < (d : ℝ))
    (Λ C : ℝ) (N : ℕ) : ℝ :=
  max 1 ((N : ℝ) * (2 * C * weakHarnackMeanConstant d hd Λ /
    volume.real (ball (0 : AmbientSpace d) (1 / 4 : ℝ))))

def finiteOscillationFactor (d : ℕ) [NeZero d] (hd : 2 < (d : ℝ))
    (Λ C : ℝ) (N : ℕ) : ℝ :=
  finiteOscillationConstant d hd Λ C N / (finiteOscillationConstant d hd Λ C N + 1)

theorem finiteOscillationFactor_pos_lt_one (hd : 2 < (d : ℝ)) (Λ C : ℝ) (N : ℕ) :
    0 < finiteOscillationFactor d hd Λ C N ∧ finiteOscillationFactor d hd Λ C N < 1 := by
  have hD : 0 < finiteOscillationConstant d hd Λ C N :=
    zero_lt_one.trans_le (le_max_left _ _)
  exact ⟨div_pos hD (by positivity), (div_lt_one (by positivity)).mpr (by linarith)⟩

theorem finite_supersolution_oscillation_contraction
    {I : Type*} [Fintype I] (hd : 2 < (d : ℝ))
    {x₀ : E} {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    (A : NormalizedEllipticCoeff d (ball x₀ R))
    (f : I → E → ℝ) (hf : ∀ i, Continuous (f i))
    (hsuper : ∀ i, IsSupersolution A.1
      (fun x => compactSup (f i) (closedBall x₀ R) - f i x))
    (hpair : ∀ i, ∀ x ∈ closedBall x₀ R, ∀ y ∈ closedBall x₀ R,
      |f i x - f i y| ≤ C * ∑ j, (compactSup (f j) (closedBall x₀ R) - f j y)) :
    (∑ i, compactOsc (f i) (closedBall x₀ (R / 8))) ≤
      finiteOscillationFactor d hd A.1.Λ C (Fintype.card I) *
        ∑ i, compactOsc (f i) (closedBall x₀ R) := by
  classical
  let K := closedBall x₀ R
  let L := closedBall x₀ (R / 8)
  let Q : Set E := ball 0 (1 / 4 : ℝ)
  let T : E → E := fun z => x₀ + R • z
  let M (i : I) := compactSup (f i) K
  let S (i : I) := compactSup (f i) L
  let δ : ℝ := ∑ i, (M i - S i)
  let V : ℝ := volume.real Q
  let W := weakHarnackMeanConstant d hd A.1.Λ
  let D := finiteOscillationConstant d hd A.1.Λ C (Fintype.card I)
  have hV : 0 < V := ENNReal.toReal_pos
    (measure_ball_pos (μ := volume) (0 : E) (by norm_num : (0 : ℝ) < 1 / 4)).ne'
    measure_ball_lt_top.ne
  have hW : 0 ≤ W := (weakHarnackMeanConstant_pos hd _).le
  have hD : 0 < D := zero_lt_one.trans_le (le_max_left _ _)
  have hK : IsCompact K := isCompact_closedBall _ _
  have hL : IsCompact L := isCompact_closedBall _ _
  have hLne : L.Nonempty := ⟨x₀, mem_closedBall_self (by positivity)⟩
  have hLK : L ⊆ K := closedBall_subset_closedBall (by linarith)
  have hLquarter : L ⊆ ball x₀ (R / 4) := closedBall_subset_ball (by linarith)
  have hTK (z : E) (hz : z ∈ Q) : T z ∈ K := by
    have hpre := congrArg (fun s : Set E => z ∈ s)
      (affine_preimage_ball_mul (d := d) (x₀ := x₀) (R := R) (ρ := 1 / 4) hR)
    have hsmall : T z ∈ ball x₀ (R / 4) := by
      simpa only [mem_preimage, T, div_eq_mul_inv, one_mul] using hpre.mpr hz
    exact ball_subset_closedBall ((ball_subset_ball (by linarith : R / 4 ≤ R)) hsmall)
  have hupper (i : I) (x : E) (hx : x ∈ K) : f i x ≤ M i :=
    le_compactSup hK (hf i).continuousOn hx
  have hδ : 0 ≤ δ := Finset.sum_nonneg fun i _ => sub_nonneg.mpr
    (compactSup_mono hK hLne (hf i).continuousOn hLK)
  letI : IsFiniteMeasure (volume.restrict Q) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact measure_ball_lt_top
  have hI (i : I) : Integrable (fun z => M i - f i (T z)) (volume.restrict Q) :=
    (continuous_memLp_ball (continuous_const.sub ((hf i).comp (by fun_prop)))
      0 (1 / 4 : ℝ) 1).integrable le_rfl
  have hmean (i : I) : (∫ z in Q, M i - f i (T z)) ≤ W * (M i - S i) := by
    obtain ⟨p, hp, hmax⟩ := compactSup_attained hL hLne (hf i).continuousOn
    have h := weak_harnack_rescaled_mean_le hd hR A (continuous_const.sub (hf i))
      (fun x hx => sub_nonneg.mpr (hupper i x (ball_subset_closedBall hx)))
      (hsuper i) (hLquarter hp)
    change (∫ z in Q, M i - f i (T z)) ≤ W * (M i - f i p) at h
    rw [← hmax] at h
    exact h
  have hsummean : (∑ i, ∫ z in Q, M i - f i (T z)) ≤ W * δ := by
    rw [show W * δ = ∑ i, W * (M i - S i) by exact Finset.mul_sum ..]
    exact Finset.sum_le_sum fun i _ => hmean i
  have hpoint (i : I) (x : E) (hx : x ∈ L) (y : E) (hy : y ∈ L)
      (z : E) (hz : z ∈ Q) :
      f i x - f i y ≤ 2 * C * ∑ j, (M j - f j (T z)) := by
    have h1 := hpair i x (hLK hx) (T z) (hTK z hz)
    have h2 := hpair i y (hLK hy) (T z) (hTK z hz)
    have h1' := le_abs_self (f i x - f i (T z))
    have h2' := neg_le_abs (f i y - f i (T z))
    change |f i x - f i (T z)| ≤ C * ∑ j, (M j - f j (T z)) at h1
    change |f i y - f i (T z)| ≤ C * ∑ j, (M j - f j (T z)) at h2
    linarith
  have hosc (i : I) : compactOsc (f i) L ≤ (2 * C * W / V) * δ := by
    apply compactOsc_le_of_sub_le hL hLne (hf i).continuousOn
    intro x hx y hy
    have hint := integral_mono_ae (integrable_const (f i x - f i y))
      ((integrable_finset_sum _ (fun j _ => hI j)).const_mul (2 * C)) (by
        filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
        exact hpoint i x hx y hy z hz)
    have hprod : V * (f i x - f i y) ≤ (2 * C * W) * δ := by
      calc
        V * (f i x - f i y) ≤ 2 * C * ∑ j, ∫ z in Q, M j - f j (T z) := by
          simpa only [V, Measure.real, integral_const, Measure.restrict_apply_univ,
            smul_eq_mul, integral_const_mul, integral_finset_sum _ (fun j _ => hI j)] using hint
        _ ≤ 2 * C * (W * δ) := mul_le_mul_of_nonneg_left hsummean (by positivity)
        _ = _ := by ring
    have hdiv : f i x - f i y ≤ ((2 * C * W) * δ) / V :=
      (le_div_iff₀ hV).mpr (by simpa only [mul_comm V] using hprod)
    simpa only [div_mul_eq_mul_div] using hdiv
  have hsumosc : (∑ i, compactOsc (f i) L) ≤ D * δ := by
    calc
      _ ≤ ∑ _i : I, (2 * C * W / V) * δ := Finset.sum_le_sum fun i _ => hosc i
      _ = ((Fintype.card I : ℝ) * (2 * C * W / V)) * δ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]
      _ ≤ D * δ := mul_le_mul_of_nonneg_right (le_max_right _ _) hδ
  have hdrop : δ ≤ (∑ i, compactOsc (f i) K) - ∑ i, compactOsc (f i) L := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro i _
    have hm := compactInf_mono hK hLne (hf i).continuousOn hLK
    dsimp only [compactOsc, M, S]
    linarith
  have hmain := hsumosc.trans (mul_le_mul_of_nonneg_left hdrop hD.le)
  change (∑ i, compactOsc (f i) L) ≤ D / (D + 1) * ∑ i, compactOsc (f i) K
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by linarith : 0 < D + 1)).mpr
  nlinarith

end CHS.Analysis
