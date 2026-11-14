import CHS.Analysis.ClassicalWeakFlux
import DifferentialGeometry.External.DeGiorgi.Localization
import DifferentialGeometry.External.DeGiorgi.UnitBallApproximationCore.Profiles

/-!
# Relatively compact local C1 data, with no global extension assumption

A genuine smooth cutoff gives global C1 representatives, equal to the original
function and flux on the smaller ball.  The resulting supersolution is
transferred back to the original raw function using the actual De Giorgi AE
congruence theorem.  In particular, neither global C1 regularity nor a boundary
extension of the original solution is a hidden premise.

S002 candidate; not yet Lean-compiled.
-/

noncomputable section
open MeasureTheory Filter Set Metric Topology
open scoped ENNReal ContDiff

namespace CHS.Analysis
open DeGiorgi
variable {d : ℕ} [NeZero d]
local notation "E" => AmbientSpace d

/-- Smooth cutoff multiplication is globally Ck if its closed support lies in
an open region where the original scalar function is Ck. -/
theorem contDiff_mul_of_tsupport_subset
    {k : ℕ} {U : Set E} (hU : IsOpen U)
    {η u : E → ℝ} (hη : ContDiff ℝ k η)
    (hu : ContDiffOn ℝ k u U) (hsupp : tsupport η ⊆ U) :
    ContDiff ℝ k (fun x => η x * u x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact hη.contDiffAt.mul (hu.contDiffAt (hU.mem_nhds hx))
  · have hxnot : x ∉ tsupport η := fun h => hx (hsupp h)
    have hzero : (fun y => η y * u y) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      have hopen : IsOpen (tsupport η)ᶜ := (isClosed_tsupport η).isOpen_compl
      filter_upwards [hopen.mem_nhds hxnot] with y hy
      rw [image_eq_zero_of_notMem_tsupport (f := η) hy, zero_mul]
    exact (contDiffAt_const : ContDiffAt ℝ k (fun _ : E => (0 : ℝ)) x).congr_of_eventuallyEq hzero

/-- A concrete Ck representative agreeing on an inner ball. -/
def cutoffRepresentative (x₀ : E) (r R : ℝ) (u : E → ℝ) : E → ℝ :=
  fun x => myCutoff x₀ r R x * u x

lemma cutoffRepresentative_contDiff
    {k : ℕ} {U : Set E} (hU : IsOpen U)
    {x₀ : E} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hclosed : closedBall x₀ R ⊆ U)
    {u : E → ℝ} (hu : ContDiffOn ℝ k u U) :
    ContDiff ℝ k (cutoffRepresentative x₀ r R u) := by
  apply contDiff_mul_of_tsupport_subset hU
  · exact (myCutoff_contDiff hr hrR).of_le (WithTop.coe_le_coe.mpr le_top)
  · exact hu
  · exact (myCutoff_support_subset x₀ hrR).trans hclosed

lemma cutoffRepresentative_eqOn
    {x₀ : E} {r R : ℝ} (hrR : r < R) (u : E → ℝ) :
    EqOn (cutoffRepresentative x₀ r R u) u (ball x₀ r) := by
  intro x hx
  simp only [cutoffRepresentative, myCutoff_eq_one hrR hx, one_mul]

lemma cutoffRepresentative_eventuallyEq
    {x₀ : E} {r R : ℝ} (hrR : r < R) (u : E → ℝ)
    {x : E} (hx : x ∈ ball x₀ r) :
    cutoffRepresentative x₀ r R u =ᶠ[𝓝 x] u := by
  filter_upwards [isOpen_ball.mem_nhds hx] with y hy
  exact cutoffRepresentative_eqOn hrR u hy

/-- No global C1 hypothesis: all raw data need only be C1 on U, with one
closed ball contained in U. The conclusion tests against the complete H01
class in the actual vendored supersolution definition. -/
theorem supersolution_of_local_classical_flux
    {U : Set E} (hU : IsOpen U) {x₀ : E} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hclosed : closedBall x₀ R ⊆ U)
    (A : EllipticCoeff d (ball x₀ r))
    {u : E → ℝ} (hu : ContDiffOn ℝ 1 u U)
    {F : E → E} (hF : ∀ i : Fin d, ContDiffOn ℝ 1 (fun x => F x i) U)
    (hflux : ∀ x ∈ ball x₀ r, matMulE (A.a x) (smoothGradField u x) = F x)
    (hdiv : ∀ x ∈ ball x₀ r, classicalDivergence F x ≤ 0) :
    IsSupersolution A u := by
  let v := cutoffRepresentative x₀ r R u
  let G : E → E := fun x => WithLp.toLp 2
    (fun i => cutoffRepresentative x₀ r R (fun y => F y i) x)
  have hv : ContDiff ℝ 1 v := cutoffRepresentative_contDiff hU hr hrR hclosed hu
  have hG : ∀ i : Fin d, ContDiff ℝ 1 (fun x => G x i) := by
    intro i
    simpa [G, PiLp.toLp_apply] using
      cutoffRepresentative_contDiff hU hr hrR hclosed (hF i)
  have hvEq : ∀ x ∈ ball x₀ r, v =ᶠ[𝓝 x] u := by
    intro x hx
    exact cutoffRepresentative_eventuallyEq hrR u hx
  have hGEq : ∀ i : Fin d, ∀ x ∈ ball x₀ r,
      (fun y => G y i) =ᶠ[𝓝 x] (fun y => F y i) := by
    intro i x hx
    simpa [G, PiLp.toLp_apply] using
      cutoffRepresentative_eventuallyEq hrR (fun y => F y i) hx
  have hsuper : IsSupersolution A v := by
    apply supersolution_of_classical_flux_on_ball x₀ r A hv hG
    · intro x hx
      have hgrad : smoothGradField v x = smoothGradField u x := by
        unfold smoothGradField
        rw [(hvEq x hx).fderiv_eq]
      rw [hgrad, hflux x hx]
      ext i
      exact ((hGEq i x hx).self_of_nhds).symm
    · intro x hx
      have hdivEq : classicalDivergence G x = classicalDivergence F x := by
        unfold classicalDivergence
        apply Finset.sum_congr rfl
        intro i _
        rw [(hGEq i x hx).fderiv_eq]
      rw [hdivEq]
      exact hdiv x hx
  apply DeGiorgi.IsSupersolution.congr_ae (hsuper := hsuper)
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  exact cutoffRepresentative_eqOn hrR u hx

end CHS.Analysis
