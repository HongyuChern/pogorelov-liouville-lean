import CHS.Analysis.WeakHarnackMean

/-!
# Finite simultaneous approximation of the infima of supersolutions

For one globally normalized coefficient field, finitely many continuous
nonnegative entire supersolutions with infimum zero become simultaneously
small at some point.  The proof sums the scale-independent weak Harnack
mean bounds on one sufficiently large ball.
-/

set_option autoImplicit false
noncomputable section

open DeGiorgi MeasureTheory Set Metric
open scoped BigOperators

namespace CHS.Analysis

variable {d : ℕ} [NeZero d]
local notation "E" => AmbientSpace d

theorem finite_supersolutions_simultaneously_small
    {ι : Type*} [Fintype ι] (hd : 2 < (d : ℝ))
    (B : NormalizedEllipticCoeff d univ) (g : ι → E → ℝ)
    (hg : ∀ i, Continuous (g i)) (hnonneg : ∀ i x, 0 ≤ g i x)
    (hsuper : ∀ i R, 0 < R →
      IsSupersolution (B.restrict (subset_univ (ball (0 : E) R))).1 (g i))
    (hinf : ∀ i, ∀ δ : ℝ, 0 < δ → ∃ x, g i x < δ)
    {ε : ℝ} (hε : 0 < ε) : ∃ x : E, ∀ i, g i x < ε := by
  classical
  let Q : Set E := ball 0 (1 / 4 : ℝ)
  let V : ℝ := volume.real Q
  have hV : 0 < V := ENNReal.toReal_pos
    (measure_ball_pos (μ := volume) (0 : E) (by norm_num : (0 : ℝ) < 1 / 4)).ne'
    measure_ball_lt_top.ne
  let K := weakHarnackMeanConstant d hd B.1.Λ
  have hK : 0 < K := weakHarnackMeanConstant_pos hd _
  let δ := V * ε / (K * (Fintype.card ι + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  choose y hy using fun i => hinf i δ hδ
  let C := ∑ i, ‖y i‖
  let R := 4 * (C + 1)
  have hC : 0 ≤ C := Finset.sum_nonneg fun i _ => norm_nonneg _
  have hR : 0 < R := by dsimp [R]; linarith
  have hyR (i : ι) : ‖y i‖ < R / 4 := by
    have hle : ‖y i‖ ≤ C := Finset.single_le_sum
      (fun j _ => norm_nonneg (y j)) (Finset.mem_univ i)
    dsimp [R]
    linarith
  letI : IsFiniteMeasure (volume.restrict Q) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact measure_ball_lt_top
  have hI (i : ι) : Integrable (fun z : E => g i (R • z)) (volume.restrict Q) :=
    (continuous_memLp_ball ((hg i).comp
      (show Continuous (fun z : E => R • z) from by fun_prop)) 0 (1 / 4 : ℝ) 1).integrable le_rfl
  have hmean (i : ι) : (∫ z in Q, g i (R • z)) ≤ K * δ :=
    (global_weak_harnack_rescaled_mean_le hd B (hg i) (hnonneg i) (hsuper i) hR (hyR i)).trans
      (mul_le_mul_of_nonneg_left (hy i).le hK.le)
  have hsum : (∫ z in Q, ∑ i, g i (R • z)) ≤ (Fintype.card ι : ℝ) * (K * δ) := by
    rw [integral_finset_sum _ (fun i _ => hI i)]
    calc
      _ ≤ ∑ _i : ι, K * δ := Finset.sum_le_sum fun i _ => hmean i
      _ = _ := by simp
  have hδid : K * ((Fintype.card ι : ℝ) + 1) * δ = V * ε := by
    dsimp [δ]
    field_simp
  have hstrict : (Fintype.card ι : ℝ) * (K * δ) < V * ε := by
    nlinarith [mul_pos hK hδ]
  by_contra! hbad
  have hpoint (z : E) : ε ≤ ∑ i, g i (R • z) := by
    obtain ⟨i, hi⟩ := hbad (R • z)
    exact hi.trans (Finset.single_le_sum (fun j _ => hnonneg j _) (Finset.mem_univ i))
  have hlower : V * ε ≤ ∫ z in Q, ∑ i, g i (R • z) := by
    have h := integral_mono_ae (integrable_const ε)
      (integrable_finset_sum _ (fun i _ => hI i)) (Filter.Eventually.of_forall hpoint)
    simpa only [V, integral_const, Measure.restrict_apply_univ, smul_eq_mul, Measure.real] using h
  exact (not_lt_of_ge (hlower.trans hsum)) hstrict

end CHS.Analysis
