import CHS.Sections.EllipsoidSandwich
import CHS.Sections.EllipsoidSections

/-!
# The actual cylindrical ellipsoids in (3.4)

The transverse sublevel set is open, convex, and bounded by the proved
fixed-kernel coercivity theorem.  The dimension-factor ellipsoid sandwich
is lifted through the actual orthogonal projection.  Its outer squared
radius is at most `(2 n)² = 4 n²`, with strict inclusion for the open
section.  The zero-dimensional transverse case is also included.
-/

set_option autoImplicit false
noncomputable section

open Set
open scoped ContDiff

namespace CHS.Sections

open CHS.Calculus CHS.Analysis

variable {n : ℕ}
local notation "E₀" => DeGiorgi.AmbientSpace (n + n)

theorem ellipsoid_section_sandwiches_of_fixed_kernel
    (hn : 0 < n) {u : E₀ → ℝ} (hu : ContDiff ℝ 2 u)
    (hu0 : u 0 = 0) (hD0 : fderiv ℝ u 0 = 0)
    (hR : ∀ x, (realBlockHessian realDirections imagDirections u x).PosSemidef)
    (K : Submodule ℝ E₀) (hker : ∀ x, (realHessian u x).ker = K) :
    HasEllipsoidSectionSandwiches u K := by
  letI : NeZero (n + n) := ⟨by omega⟩
  let P := Kᗮ.orthogonalProjectionOnto
  have hfactor (x : E₀) : u x = u (P x : E₀) :=
    factors_through_orthogonal_projection_of_fixed_kernel hu hD0 K hker x
  have hquad (x z : E₀) : 0 ≤ realHessian u x z z :=
    realHessian_quadratic_nonneg_of_realBlockHessian hu.contDiffAt (hR x) z
  intro h hh
  rcases subsingleton_or_nontrivial Kᗮ with htrivial | hnontrivial
  · letI := htrivial
    let T : Kᗮ ≃L[ℝ] Kᗮ := ContinuousLinearEquiv.refl ℝ Kᗮ
    have hqzero (x : E₀) : ellipsoidQuadratic K T 0 x = 0 := by
      unfold ellipsoidQuadratic
      rw [show ellipsoidLinearMap K T (x - 0) = 0 from Subsingleton.elim _ _]
      norm_num
    have huzero (x : E₀) : u x = 0 := by
      rw [hfactor x, show P x = 0 from Subsingleton.elim _ _]
      exact hu0
    refine ⟨0, T, ?_, ?_⟩
    · intro x _
      rwa [huzero]
    · intro x _
      rw [hqzero]
      have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
      positivity
  · letI := hnontrivial
    let V : Set Kᗮ := {x | u x < h}
    have hV : IsOpen V := isOpen_lt (hu.continuous.comp Kᗮ.subtypeL.continuous) continuous_const
    have hcompact : IsCompact (closure V) :=
      compact_transverse_section_of_fixed_kernel hu hu0 hD0 hquad K hker h
    have hconvU : Convex ℝ {x : E₀ | u x < h} := by
      have hc : ConvexOn ℝ univ u := convexOn_of_realBlockHessian_posSemidef
        isOpen_univ convex_univ hu.contDiffOn (fun x _ => hR x)
      simpa only [mem_univ, true_and] using hc.convex_lt h
    have hconvV : Convex ℝ V := hconvU.linear_preimage Kᗮ.subtype
    have hzero : (0 : Kᗮ) ∈ V := by change u 0 < h; rwa [hu0]
    have hd : 0 < (Module.finrank ℝ Kᗮ : ℝ) := by exact_mod_cast Module.finrank_pos (R := ℝ) (M := Kᗮ)
    obtain ⟨a, T, hinner, houter⟩ := exists_open_ellipsoid_sandwich hd hV
      (hcompact.isBounded.subset subset_closure) hconvV hzero
    have hq (x : E₀) : ellipsoidQuadratic K T (a : E₀) x = ‖T (P x - a)‖ ^ 2 := by
      simp only [ellipsoidQuadratic, ellipsoidLinearMap, ContinuousLinearMap.comp_apply,
        ContinuousLinearEquiv.coe_coe, map_sub,
        Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
      rfl
    have hdleN : Module.finrank ℝ Kᗮ ≤ n + n := by
      simpa only [DeGiorgi.AmbientSpace, finrank_euclideanSpace_fin] using Kᗮ.finrank_le
    have hdle : (Module.finrank ℝ Kᗮ : ℝ) ≤ 2 * (n : ℝ) := by
      have hcast : (Module.finrank ℝ Kᗮ : ℝ) ≤ (n : ℝ) + (n : ℝ) := by exact_mod_cast hdleN
      linarith
    refine ⟨(a : E₀), T, ?_, ?_⟩
    · intro x hx
      rw [hq] at hx
      have hnorm : ‖T (P x - a)‖ < 1 := by nlinarith [norm_nonneg (T (P x - a))]
      rw [hfactor x]
      exact hinner (P x) hnorm
    · intro x hx
      have hxP : P x ∈ V := by change u (P x : E₀) < h; rwa [← hfactor x]
      have hnorm := (houter (P x) hxP).trans_le hdle
      rw [hq]
      nlinarith [norm_nonneg (T (P x - a))]

theorem entire_convex_ellipsoid_section_sandwiches
    (hn : 2 ≤ n) {u : E₀ → ℝ} (hu : ContDiff ℝ 4 u)
    (hu0 : u 0 = 0) (hD0 : fderiv ℝ u 0 = 0)
    (hdet : ∀ x, (complexHessian realDirections imagDirections u x).det = 1)
    (hR : ∀ x, (realBlockHessian realDirections imagDirections u x).PosSemidef) :
    HasEllipsoidSectionSandwiches u (realHessian u 0).ker := by
  obtain ⟨K, hker, _, _⟩ := entire_convex_sections_have_compact_real_quotient hn hu hu0 hD0 hdet hR
  have hker0 (x : E₀) : (realHessian u x).ker = (realHessian u 0).ker :=
    (hker x).trans (hker 0).symm
  exact ellipsoid_section_sandwiches_of_fixed_kernel (by omega) (hu.of_le (by norm_num))
    hu0 hD0 hR (realHessian u 0).ker hker0

end CHS.Sections
