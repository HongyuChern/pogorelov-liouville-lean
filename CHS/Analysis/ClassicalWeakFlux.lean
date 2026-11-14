import CHS.Analysis.WeakFlux

/-!
# Classical C1 functions on a ball: actual Sobolev witnesses and weak flux

Only one classical derivative is used.  This file supplies finite-ball L2
membership instead of adding it as an unexplained PDE assumption.  Its public
supersolution theorem reaches the actual all-H01 De Giorgi definition.
Global C1 representatives occur in this module; localization to a relatively
compact ball is handled separately, not silently assumed of a local solution.

S002 candidate: no Lean elaboration has been performed.
-/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped ENNReal BigOperators ContDiff

namespace CHS.Analysis
open DeGiorgi
variable {d : ℕ} [NeZero d]
local notation "E" => AmbientSpace d

/-- Continuous functions are in every finite Lp on a finite Euclidean ball.
The proof is a compact closed-ball bound, not a global bound. -/
theorem continuous_memLp_ball {F : Type*} [NormedAddCommGroup F]
    {f : E → F} (hf : Continuous f) (x₀ : E) (r : ℝ) (p : ℝ≥0∞) :
    MemLp f p (volume.restrict (ball x₀ r)) := by
  letI : IsFiniteMeasure (volume.restrict (ball x₀ r)) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact measure_ball_lt_top
  obtain ⟨C, hC⟩ := ((isCompact_closedBall x₀ r).image_of_continuousOn
    hf.continuousOn).isBounded.exists_norm_le
  have hbound : ∀ᵐ x ∂volume.restrict (ball x₀ r), ‖f x‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact hC _ ⟨x, ball_subset_closedBall hx, rfl⟩
  exact (memLp_top_of_bound (hf.aestronglyMeasurable.restrict (s := ball x₀ r))
    C hbound).mono_exponent le_top

/-- The vendored gradient field is the actual Frechet derivative in the
canonical Euclidean basis, whether or not the function is C-infinity. -/
theorem continuous_classical_gradient {u : E → ℝ} (hu : ContDiff ℝ 1 u) :
    Continuous (smoothGradField u) := by
  unfold smoothGradField
  apply (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).comp
  apply continuous_pi
  intro i
  exact (hu.continuous_fderiv one_ne_zero).clm_apply continuous_const

/-- An explicit W1,2 witness for a C1 function on any finite ball. -/
def classicalBallWitness {u : E → ℝ} (hu : ContDiff ℝ 1 u) (x₀ : E) (r : ℝ) :
    MemW1pWitness 2 u (ball x₀ r) where
  memLp := continuous_memLp_ball hu.continuous x₀ r 2
  weakGrad := smoothGradField u
  weakGrad_component_memLp := by
    intro i
    simpa [smoothGradField, PiLp.toLp_apply] using
      continuous_memLp_ball
        ((hu.continuous_fderiv one_ne_zero).clm_apply
          (continuous_const : Continuous (fun _ : E => EuclideanSpace.single i (1 : ℝ))))
        x₀ r 2
  isWeakGrad := by
    intro i
    simpa [smoothGradField, PiLp.toLp_apply] using
      HasWeakPartialDeriv.of_contDiff (d := d) (Ω := ball x₀ r) (i := i)
        isOpen_ball hu

/-- Coordinate definition of the actual classical divergence. -/
def classicalDivergence (F : E → E) (x : E) : ℝ :=
  ∑ i : Fin d, (fderiv ℝ (fun y => F y i) x) (EuclideanSpace.single i 1)

lemma continuous_of_componentwise {F : E → E}
    (hF : ∀ i : Fin d, Continuous (fun x => F x i)) : Continuous F := by
  have h : Continuous (fun x => WithLp.toLp 2 (fun i : Fin d => F x i)) :=
    (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).comp (continuous_pi hF)
  simpa using h

lemma continuous_classicalDivergence {F : E → E}
    (hF : ∀ i : Fin d, ContDiff ℝ 1 (fun x => F x i)) :
    Continuous (classicalDivergence F) := by
  unfold classicalDivergence
  apply continuous_finsetSum
  intro i _
  exact ((hF i).continuous_fderiv one_ne_zero).clm_apply continuous_const

/-- The classical C1 divergence is the genuine weak divergence on a ball. -/
theorem hasWeakDiv_classical_on_ball {F : E → E}
    (hF : ∀ i : Fin d, ContDiff ℝ 1 (fun x => F x i)) (x₀ : E) (r : ℝ) :
    HasWeakDiv (classicalDivergence F) F (ball x₀ r) := by
  apply hasWeakDiv_sum_of_hasWeakPartialDeriv
  · intro i
    exact (continuous_memLp_ball (hF i).continuous x₀ r 2).locallyIntegrable
      (by norm_num)
  · intro i
    exact (continuous_memLp_ball
      (((hF i).continuous_fderiv one_ne_zero).clm_apply continuous_const)
      x₀ r 2).locallyIntegrable (by norm_num)
  · intro i
    exact HasWeakPartialDeriv.of_contDiff isOpen_ball (hF i)

/-- Classical div(A grad u) <= 0 gives the actual weak supersolution on a
ball, with every H01 test and every Sobolev witness.  No smooth-test-only
replacement predicate is used. -/
theorem supersolution_of_classical_flux_on_ball
    (x₀ : E) (r : ℝ) (A : EllipticCoeff d (ball x₀ r))
    {u : E → ℝ} (hu : ContDiff ℝ 1 u)
    {F : E → E} (hF : ∀ i : Fin d, ContDiff ℝ 1 (fun x => F x i))
    (hflux : ∀ x ∈ ball x₀ r, matMulE (A.a x) (smoothGradField u x) = F x)
    (hdiv : ∀ x ∈ ball x₀ r, classicalDivergence F x ≤ 0) :
    IsSupersolution A u := by
  apply supersolution_of_weak_flux_on isOpen_ball A (classicalBallWitness hu x₀ r)
  · exact continuous_memLp_ball (continuous_of_componentwise (fun i => (hF i).continuous))
      x₀ r 2
  · exact continuous_memLp_ball (continuous_classicalDivergence hF) x₀ r 2
  · exact hasWeakDiv_classical_on_ball hF x₀ r
  · exact hflux
  · exact hdiv

end CHS.Analysis
