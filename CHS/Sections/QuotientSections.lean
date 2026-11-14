import CHS.Sections.Coercivity
import CHS.Calculus.HessianKernelPositivity
import CHS.Calculus.HessianQuadraticForm
import CHS.Analysis.FixedRealKernel
import CHS.Sections.Depth
import CHS.Pogorelov.GeneralEstimate

/-!
# Compact quotient sections from the fixed actual real Hessian kernel

The transverse section is bounded by strict positivity of its actual
Hessian.  Its compact closure is then mapped onto the actual quotient
image of the ambient section closure.  No compactness or coercivity is
assumed in the public fixed-kernel conclusion.
-/

set_option autoImplicit false
noncomputable section

open Set
open scoped ContDiff BigOperators

namespace CHS.Sections

open CHS.Calculus CHS.Analysis CHS.Pogorelov

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

theorem invariant_of_fixed_realHessian_kernel
    {u : E → ℝ} (hu : ContDiff ℝ 2 u) (hD0 : fderiv ℝ u 0 = 0)
    (K : Submodule ℝ E) (hker : ∀ x, (realHessian u x).ker = K) :
    ∀ x v : E, v ∈ K → u (x + v) = u x := by
  intro x v hv
  have hz (y : E) : realHessian u y v = 0 := by
    change v ∈ (realHessian u y).ker
    rwa [hker y]
  simpa only [hD0, zero_apply, add_zero] using add_eq_of_common_hessian_kernel hu hz x

theorem factors_through_orthogonal_projection_of_fixed_kernel
    {u : E → ℝ} (hu : ContDiff ℝ 2 u) (hD0 : fderiv ℝ u 0 = 0)
    (K : Submodule ℝ E) (hker : ∀ x, (realHessian u x).ker = K) (x : E) :
    u x = u (Kᗮ.orthogonalProjectionOnto x : E) := by
  have hK (y : E) (v : K) : realHessian u y (v : E) = 0 := by
    change (v : E) ∈ (realHessian u y).ker
    rw [hker y]
    exact v.property
  simpa only [hD0, zero_apply, add_zero] using splits_on_orthogonalComplement hu K hK x

theorem compact_transverse_section_of_fixed_kernel
    {u : E → ℝ} (hu : ContDiff ℝ 2 u) (hu0 : u 0 = 0)
    (hD0 : fderiv ℝ u 0 = 0) (hQ : ∀ x v : E, 0 ≤ realHessian u x v v)
    (K : Submodule ℝ E) (hker : ∀ x, (realHessian u x).ker = K) (h : ℝ) :
    IsCompact (closure {x : Kᗮ | u x < h}) := by
  have hf : ContDiff ℝ 2 (fun x : Kᗮ => u x) := hu.comp Kᗮ.subtypeL.contDiff
  have hdf : fderiv ℝ (fun x : Kᗮ => u x) 0 = 0 := by
    have hd := ((hu.differentiable (by norm_num) (0 : E)).hasFDerivAt.comp
      (0 : Kᗮ) Kᗮ.subtypeL.hasFDerivAt).fderiv
    simpa only [Function.comp_def, Submodule.subtypeL_apply, ZeroMemClass.coe_zero,
      hD0, ContinuousLinearMap.zero_comp] using hd
  exact compact_closure_sublevel_of_strict_realHessian hf hu0 hdf
    (restricted_realHessian_pos_of_fixed_kernel hu hQ K hker) h

theorem compact_quotient_section_of_fixed_kernel
    {u : E → ℝ} (hu : ContDiff ℝ 2 u) (hu0 : u 0 = 0)
    (hD0 : fderiv ℝ u 0 = 0) (hQ : ∀ x v : E, 0 ≤ realHessian u x v v)
    (K : Submodule ℝ E) (hker : ∀ x, (realHessian u x).ker = K) (h : ℝ) :
    IsCompact ((Submodule.Quotient.mk : E → E ⧸ K) '' closure {x | u x < h}) := by
  let P := Kᗮ.orthogonalProjectionOnto
  let q : E → E ⧸ K := Submodule.Quotient.mk
  have hfactor (x : E) : u x = u (P x : E) :=
    factors_through_orthogonal_projection_of_fixed_kernel hu hD0 K hker x
  have hP : MapsTo P {x | u x < h} {y : Kᗮ | u y < h} := by
    intro x hx
    change u (P x : E) < h
    rwa [← hfactor x]
  have hPc := hP.closure P.continuous
  have hi : MapsTo Kᗮ.subtypeL {y : Kᗮ | u y < h} {x | u x < h} :=
    fun x hx => hx
  have hic := hi.closure Kᗮ.subtypeL.continuous
  have hqP (x : E) : q (P x : E) = q x := by
    apply (Submodule.Quotient.eq K).mpr
    change (Kᗮ.orthogonalProjectionOnto x : E) - x ∈ K
    rw [Submodule.orthogonalProjectionOnto_orthogonal]
    change x - K.starProjection x - x ∈ K
    rw [sub_right_comm, sub_self, zero_sub]
    exact K.neg_mem (K.starProjection_apply_mem x)
  have heq : q '' closure {x | u x < h} =
      (fun x : Kᗮ => q x) '' closure {x : Kᗮ | u x < h} := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨P x, hPc hx, hqP x⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hic hx, rfl⟩
  change IsCompact (q '' closure {x | u x < h})
  rw [heq]
  exact (compact_transverse_section_of_fixed_kernel hu hu0 hD0 hQ K hker h).image
    (K.mkQL.continuous.comp Kᗮ.subtypeL.continuous)

end CHS.Sections

namespace CHS.Sections

open CHS.Calculus CHS.Analysis

variable {n : ℕ}
local notation "E₀" => DeGiorgi.AmbientSpace (n + n)

theorem realHessian_quadratic_nonneg_of_realBlockHessian
    {u : E₀ → ℝ} {x : E₀} (hu : ContDiffAt ℝ 2 u x)
    (hR : (realBlockHessian realDirections imagDirections u x).PosSemidef) (v : E₀) :
    0 ≤ realHessian u x v v := by
  let B := (EuclideanSpace.basisFun (Fin (n + n)) ℝ).toBasis
  let z (i : Fin n ⊕ Fin n) := B.repr v (finSumFinEquiv i)
  have hsum : (∑ i, z i • Sum.elim realDirections imagDirections i) = v := by
    simp only [blockDirection_eq_single, z]
    have hB (j : Fin (n + n)) : EuclideanSpace.single j (1 : ℝ) = B j :=
      (EuclideanSpace.basisFun_apply (Fin (n + n)) ℝ j).symm
    simp only [hB]
    exact (Equiv.sum_comp finSumFinEquiv (fun j => B.repr v j • B j)).trans (B.sum_repr v)
  have hquad := realHessian_sum_directions_quadratic hu realDirections imagDirections z
  rw [hsum] at hquad
  rw [hquad]
  simpa only [star_trivial] using hR.dotProduct_mulVec_nonneg z

/-- Section geometry in Proposition 3.2, after subtracting the tangent
affine function.  The fixed kernel itself is supplied by the accepted
constant-rank and splitting theorem. -/
theorem entire_convex_sections_have_compact_real_quotient
    (hn : 2 ≤ n) {u : E₀ → ℝ} (hu : ContDiff ℝ 4 u)
    (hu0 : u 0 = 0) (hD0 : fderiv ℝ u 0 = 0)
    (hdet : ∀ x, (complexHessian realDirections imagDirections u x).det = 1)
    (hR : ∀ x, (realBlockHessian realDirections imagDirections u x).PosSemidef) :
    ∃ K : Submodule ℝ E₀, (∀ x, (realHessian u x).ker = K) ∧
      (∀ x v : E₀, v ∈ K → u (x + v) = u x) ∧
      ∀ h : ℝ, IsCompact
        ((Submodule.Quotient.mk : E₀ → E₀ ⧸ K) '' closure {x | u x < h}) := by
  letI : NeZero (n + n) := ⟨by omega⟩
  have hu2 : ContDiff ℝ 2 u := hu.of_le (by norm_num)
  have hconv : ConvexOn ℝ univ u := convexOn_of_realBlockHessian_posSemidef
    isOpen_univ convex_univ hu2.contDiffOn (fun x _ => hR x)
  have hd : 2 < ((n + n : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 < n + n)
  obtain ⟨K, hker, _⟩ := exists_fixed_realHessian_kernel_and_split hd hu hconv hdet hR
  exact ⟨K, hker, invariant_of_fixed_realHessian_kernel hu2 hD0 K hker,
    fun h => compact_quotient_section_of_fixed_kernel hu2 hu0 hD0
      (fun x v => realHessian_quadratic_nonneg_of_realBlockHessian hu2.contDiffAt (hR x) v)
      K hker h⟩

theorem entire_convex_sections_have_pogorelov_geometry
    (hn : 2 ≤ n) {u : E₀ → ℝ} (hu : ContDiff ℝ 4 u)
    (hu0 : u 0 = 0) (hD0 : fderiv ℝ u 0 = 0)
    (hdet : ∀ x, (complexHessian realDirections imagDirections u x).det = 1)
    (hR : ∀ x, (realBlockHessian realDirections imagDirections u x).PosSemidef) (h : ℝ) :
    CHS.PogorelovCompactGeometry {x | u x < h} u := by
  obtain ⟨K, _, hinv, hcompact⟩ :=
    entire_convex_sections_have_compact_real_quotient hn hu hu0 hD0 hdet hR
  refine Or.inr ⟨K, ?_, fun x _ v hv => hinv x v hv, hcompact h⟩
  intro x hx v hv
  change u (x + v) < h
  rwa [hinv x v hv]

end CHS.Sections
