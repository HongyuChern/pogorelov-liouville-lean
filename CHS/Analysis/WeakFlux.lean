import DifferentialGeometry.External.DeGiorgi.WeakFormulation.WeakDivergence
import DifferentialGeometry.External.DeGiorgi.WeakFormulation.SolutionInterfaces

/-!
# A genuine all-H01-test supersolution from a weak flux equation

The conclusion is the vendored De Giorgi predicate, not a CHS replacement.
The integration-by-parts theorem used below already extends compactly
supported smooth tests to every H01 test.  The quantified Sobolev witness is
also arbitrary: witness independence is used explicitly.

S002 candidate. This source has not been elaborated by Lean.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped InnerProductSpace ENNReal

namespace CHS.Analysis
open DeGiorgi
variable {d : ℕ} [NeZero d]
local notation "E" => AmbientSpace d

/-- A square-integrable flux with nonpositive weak divergence defines the
actual De Giorgi supersolution, provided it is the actual coefficient flux
of one (and hence every) Sobolev gradient witness. -/
theorem supersolution_of_weak_flux
    {Ω : Set E} (hΩ : IsOpen Ω) (A : EllipticCoeff d Ω)
    {u : E → ℝ} (hu : MemW1pWitness 2 u Ω)
    {F : E → E} {g : E → ℝ}
    (hF : MemLp F 2 (volume.restrict Ω))
    (hg : MemLp g 2 (volume.restrict Ω))
    (hdiv : HasWeakDiv g F Ω)
    (hflux : ∀ᵐ x ∂volume.restrict Ω, matMulE (A.a x) (hu.weakGrad x) = F x)
    (hsign : ∀ᵐ x ∂volume.restrict Ω, g x ≤ 0) :
    IsSupersolution A u := by
  refine ⟨hu.memW1p, ?_⟩
  intro hw φ hφ0 hφ hφnonneg
  rw [bilinFormOfCoeff_eq_left hΩ A hw hu hφ]
  have hpair : bilinFormOfCoeff A hu hφ = -divergenceRHSOfField F hφ := by
    simp only [bilinFormOfCoeff, divergenceRHSOfField, neg_neg]
    apply integral_congr_ae
    filter_upwards [hflux] with x hx
    simp only [bilinFormIntegrandOfCoeff, divergenceRHSIntegrandOfField, hx]
  have hrhs : divergenceRHSOfField F hφ = ∫ x in Ω, g x * φ x := by
    rw [← weakProblemRHSOfField_eq_of_memH01 hΩ hφ0 hφ]
    exact weakProblemRHSOfField_eq_integral hΩ hF hg hdiv hφ0
  have hnonpos : (∫ x in Ω, g x * φ x) ≤ 0 := by
    apply integral_nonpos_of_ae
    filter_upwards [hsign] with x hx
    exact mul_nonpos_of_nonpos_of_nonneg hx (hφnonneg x)
  rw [hpair, hrhs]
  exact neg_nonneg.mpr hnonpos

/-- Pointwise flux equality and sign on an open set are sufficient; there is
no global ellipticity or boundary trace assumption on `u` here. -/
theorem supersolution_of_weak_flux_on
    {Ω : Set E} (hΩ : IsOpen Ω) (A : EllipticCoeff d Ω)
    {u : E → ℝ} (hu : MemW1pWitness 2 u Ω)
    {F : E → E} {g : E → ℝ}
    (hF : MemLp F 2 (volume.restrict Ω))
    (hg : MemLp g 2 (volume.restrict Ω))
    (hdiv : HasWeakDiv g F Ω)
    (hflux : ∀ x ∈ Ω, matMulE (A.a x) (hu.weakGrad x) = F x)
    (hsign : ∀ x ∈ Ω, g x ≤ 0) :
    IsSupersolution A u := by
  apply supersolution_of_weak_flux hΩ A hu hF hg hdiv
  · filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
    exact hflux x hx
  · filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
    exact hsign x hx

end CHS.Analysis
