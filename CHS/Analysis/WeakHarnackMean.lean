import CHS.Analysis.ClassicalWeakFlux
import DifferentialGeometry.External.DeGiorgi.StrongMinimum
import DifferentialGeometry.External.DeGiorgi.Localization

/-!
# Linear mean form of weak Harnack, with one global coefficient field

Choosing q = (d-2)/d gives exponent one in the established weak Harnack
inequality.  A positive constant perturbation removes strict positivity.
The rescaled form uses a single coefficient field and a radius-independent
constant.  No regularity estimate is assumed in this interface.
-/

set_option autoImplicit false
noncomputable section

open DeGiorgi Filter MeasureTheory Set Metric
open scoped Topology

namespace CHS.Analysis

variable {d : ℕ} [NeZero d]
local notation "E" => AmbientSpace d

theorem essInf_le_apply_of_continuousOn
    {u : E → ℝ} {U : Set E} (hU : IsOpen U) {x : E} (hx : x ∈ U)
    (hu : ContinuousOn u U) (hlow : ∃ c : ℝ, ∀ y ∈ U, c ≤ u y) :
    essInf u (volume.restrict U) ≤ u x := by
  obtain ⟨c, hc⟩ := hlow
  have hlow_ae : ∀ᵐ y ∂volume.restrict U, c ≤ u y := by
    filter_upwards [ae_restrict_mem hU.measurableSet] with y hy
    exact hc y hy
  have hess_ae := ae_essInf_le ⟨c, hlow_ae⟩
  have hzero_ae : (fun y => max (essInf u (volume.restrict U) - u y) 0)
      =ᵐ[volume.restrict U] (fun _ => 0) := by
    filter_upwards [hess_ae] with y hy
    exact max_eq_right (sub_nonpos.mpr hy)
  have hzero := Measure.eqOn_open_of_ae_eq (μ := volume) hzero_ae hU
    ((continuousOn_const.sub hu).sup continuousOn_const) continuousOn_const
  exact sub_nonpos.mp ((le_max_left _ _).trans_eq (hzero hx))

def weakHarnackMeanConstant (d : ℕ) [NeZero d] (hd : 2 < (d : ℝ)) (Λ : ℝ) : ℝ :=
  max 1 ((CWeakHarnack d hd /
    (1 - ((d : ℝ) - 2) / (d : ℝ)) ^ weakHarnackDecayExp d) ^ (Λ ^ ((1 : ℝ) / 2)))

theorem weakHarnackMeanConstant_pos (hd : 2 < (d : ℝ)) (Λ : ℝ) :
    0 < weakHarnackMeanConstant d hd Λ :=
  lt_of_lt_of_le zero_lt_one (le_max_left _ _)

theorem weak_harnack_unit_mean_le
    (hd : 2 < (d : ℝ)) (A : NormalizedEllipticCoeff d (ball (0 : E) 1))
    {u : E → ℝ} (hu : Continuous u)
    (hnonneg : ∀ x ∈ ball (0 : E) 1, 0 ≤ u x)
    (hsuper : IsSupersolution A.1 u) {x : E} (hx : x ∈ ball (0 : E) (1 / 4 : ℝ)) :
    (∫ z in ball (0 : E) (1 / 4 : ℝ), u z) ≤ weakHarnackMeanConstant d hd A.1.Λ * u x := by
  let Q : Set E := ball 0 (1 / 4 : ℝ)
  let μ : Measure E := volume.restrict Q
  let q : ℝ := ((d : ℝ) - 2) / (d : ℝ)
  let K := weakHarnackMeanConstant d hd A.1.Λ
  have hdpos : 0 < (d : ℝ) := by linarith
  have hdm : 0 < (d : ℝ) - 2 := by linarith
  have hq : 0 < q := div_pos hdm hdpos
  have hq1 : q < 1 := (div_lt_one hdpos).mpr (by linarith)
  have hqd : q * (d : ℝ) = (d : ℝ) - 2 := by dsimp [q]; field_simp
  have hp : q * (d : ℝ) / ((d : ℝ) - 2) = 1 := by rw [hqd]; exact div_self hdm.ne'
  have hp' : ((d : ℝ) - 2) / (q * (d : ℝ)) = 1 := by rw [hqd]; exact div_self hdm.ne'
  have hQ : Q ⊆ ball (0 : E) 1 := ball_subset_ball (by norm_num)
  letI : IsFiniteMeasure (volume.restrict (ball (0 : E) (1 / 4 : ℝ))) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact measure_ball_lt_top
  have hint : Integrable u μ := (continuous_memLp_ball hu 0 (1 / 4 : ℝ) 1).integrable le_rfl
  have hbound (ε : ℝ) (hε : 0 < ε) : (∫ z, u z ∂μ) ≤ K * (u x + ε) := by
    let v : E → ℝ := fun y => u y + ε
    have hvpos : ∀ y ∈ ball (0 : E) 1, 0 < v y := by
      intro y hy
      exact add_pos_of_nonneg_of_pos (hnonneg y hy) hε
    have hvsuper : IsSupersolution A.1 v := by
      simpa [v] using hsuper.sub_const_ball (by norm_num : 0 < (1 : ℝ)) (-ε)
    have hwh := weak_harnack hd A hq hq1 hvpos hvsuper
    rw [hp, hp'] at hwh
    simp only [Real.rpow_one] at hwh
    have habs : (fun y => |v y|) =ᵐ[μ] v := by
      filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
      exact abs_of_pos (hvpos y (hQ hy))
    rw [integral_congr_ae habs] at hwh
    have he : essInf v μ ≤ v x :=
      essInf_le_apply_of_continuousOn isOpen_ball hx (hu.add continuous_const).continuousOn
        ⟨0, fun y hy => (hvpos y (hQ hy)).le⟩
    have hK : (CWeakHarnack d hd / (1 - q) ^ weakHarnackDecayExp d) ^
        (A.1.Λ ^ ((1 : ℝ) / 2)) ≤ K := le_max_right _ _
    have hvint : Integrable v μ :=
      (continuous_memLp_ball (hu.add continuous_const) 0 (1 / 4 : ℝ) 1).integrable le_rfl
    have hmono : (∫ y, u y ∂μ) ≤ ∫ y, v y ∂μ :=
      integral_mono_ae hint hvint (Filter.Eventually.of_forall fun y => le_add_of_nonneg_right hε.le)
    have hprod : (CWeakHarnack d hd / (1 - q) ^ weakHarnackDecayExp d) ^
        (A.1.Λ ^ ((1 : ℝ) / 2)) * essInf v μ ≤ K * v x := by
      have hc : 0 ≤ (CWeakHarnack d hd / (1 - q) ^ weakHarnackDecayExp d) ^
          (A.1.Λ ^ ((1 : ℝ) / 2))
          := Real.rpow_nonneg (div_nonneg
            (zero_le_one.trans (one_le_C_weakHarnack hd))
            (Real.rpow_nonneg (sub_nonneg.mpr hq1.le) _)) _
      exact (mul_le_mul_of_nonneg_left he hc).trans
        (mul_le_mul_of_nonneg_right hK (hvpos x (hQ hx)).le)
    exact hmono.trans (hwh.trans hprod)
  have hlim : Tendsto (fun k : ℕ => K * (u x + 1 / ((k : ℝ) + 1))) atTop (𝓝 (K * u x)) := by
    simpa using tendsto_const_nhds.mul
      (tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  exact ge_of_tendsto hlim (Filter.Eventually.of_forall fun k => hbound _ (by positivity))

theorem global_weak_harnack_rescaled_mean_le
    (hd : 2 < (d : ℝ)) (B : NormalizedEllipticCoeff d univ)
    {u : E → ℝ} (hu : Continuous u) (hnonneg : ∀ x, 0 ≤ u x)
    (hsuper : ∀ R : ℝ, 0 < R →
      IsSupersolution (B.restrict (subset_univ (ball (0 : E) R))).1 u)
    {R : ℝ} (hR : 0 < R) {y : E} (hy : ‖y‖ < R / 4) :
    (∫ z in ball (0 : E) (1 / 4 : ℝ), u (R • z)) ≤
      weakHarnackMeanConstant d hd B.1.Λ * u y := by
  let A := B.restrict (subset_univ (ball (0 : E) R))
  let AR := rescaleNormalizedCoeffToUnitBall (x₀ := (0 : E)) hR A
  have hv : Continuous (fun z : E => u (R • z)) :=
    hu.comp (show Continuous (fun z : E => R • z) from by fun_prop)
  have hs : IsSupersolution AR.1 (fun z : E => u (R • z)) := by
    change IsSupersolution
      (rescaleCoeffToUnitBall (x₀ := (0 : E)) (R := R) hR A.1) (fun z => u (R • z))
    have heq : rescaleToUnitBall (d := d) (x₀ := (0 : E)) (R := R) u =
        (fun z : E => u (R • z)) := by
      funext z
      exact congrArg u (zero_add (R • z))
    rw [← heq]
    exact rescaleToUnitBall_isSupersolution (x₀ := (0 : E)) (R := R) hR A.1 (hsuper R hR)
  have hz : R⁻¹ • y ∈ ball (0 : E) (1 / 4 : ℝ) := by
    rw [mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hR.le)]
    exact (inv_mul_lt_iff₀ hR).mpr (by linarith)
  have h := weak_harnack_unit_mean_le hd AR hv (fun z _ => hnonneg _) hs hz
  have hΛ : AR.1.Λ = B.1.Λ := rfl
  rw [hΛ] at h
  simpa only [smul_smul, mul_inv_cancel₀ hR.ne', one_smul] using h

/-- Local scaled mean estimate with the actual center and radius. Positivity
is required only on the ball where the supersolution is given. -/
theorem weak_harnack_rescaled_mean_le
    (hd : 2 < (d : ℝ)) {x₀ : E} {R : ℝ} (hR : 0 < R)
    (A : NormalizedEllipticCoeff d (ball x₀ R))
    {u : E → ℝ} (hu : Continuous u)
    (hnonneg : ∀ x ∈ ball x₀ R, 0 ≤ u x) (hsuper : IsSupersolution A.1 u)
    {y : E} (hy : y ∈ ball x₀ (R / 4)) :
    (∫ z in ball (0 : E) (1 / 4 : ℝ), u (x₀ + R • z)) ≤
      weakHarnackMeanConstant d hd A.1.Λ * u y := by
  let AR := rescaleNormalizedCoeffToUnitBall (x₀ := x₀) hR A
  have hv : Continuous (fun z : E => u (x₀ + R • z)) := hu.comp (by fun_prop)
  have hmap (z : E) (hz : z ∈ ball (0 : E) 1) : x₀ + R • z ∈ ball x₀ R := by
    have h := congrArg (fun s : Set E => z ∈ s)
      (affine_preimage_ball_mul (d := d) (x₀ := x₀) (R := R) (ρ := 1) hR)
    simpa only [mul_one, mem_preimage] using h.mpr hz
  have hs : IsSupersolution AR.1 (fun z : E => u (x₀ + R • z)) :=
    rescaleToUnitBall_isSupersolution hR A.1 hsuper
  have hz : R⁻¹ • (y - x₀) ∈ ball (0 : E) (1 / 4 : ℝ) := by
    rw [mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hR.le)]
    apply (inv_mul_lt_iff₀ hR).mpr
    simpa only [mem_ball, dist_eq_norm, div_eq_mul_inv, one_mul] using hy
  have h := weak_harnack_unit_mean_le hd AR hv (fun z hz => hnonneg _ (hmap z hz)) hs hz
  have hΛ : AR.1.Λ = A.1.Λ := rfl
  rw [hΛ] at h
  simpa only [smul_smul, mul_inv_cancel₀ hR.ne', one_smul, add_sub_cancel] using h

end CHS.Analysis
