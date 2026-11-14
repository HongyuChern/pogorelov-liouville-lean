import CHS.Liouville.Entire
import CHS.Analysis.ConvexityMinimum

/-!
# Real convexity outside a compact set, in every positive complex dimension

An actual sphere outside the compact set gives a positive complex Hessian.
Nonsingular Hermitian branch propagation makes it positive everywhere;
the accepted boundary convexity principle fills the enclosing ball when
n>=2. In dimension one, a direct trace bound and the exact dimension lift
give quadraticity without applying the higher-dimensional minimum principle.
-/

set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ComplexOrder ContDiff Matrix.Norms.Elementwise

namespace CHS

open CHS.Calculus CHS.Analysis

variable {n : ℕ}
local notation "E" => DeGiorgi.AmbientSpace (n + n)

theorem convex_everywhere_of_convex_outside_compact
    (hn : 2 ≤ n) {u : E → ℝ} (hu : ContDiff ℝ 4 u)
    (hdet : ∀ x, (complexHessian realDirections imagDirections u x).det = 1)
    {K : Set E} (hK : IsCompact K)
    (houtside : ∀ x, x ∉ K → (realBlockHessian realDirections imagDirections u x).PosSemidef) :
    ∀ x, (realBlockHessian realDirections imagDirections u x).PosSemidef := by
  letI : NeZero (n + n) := ⟨by omega⟩
  have hd : 2 < ((n + n : ℕ) : ℝ) := by exact_mod_cast (show 2 < n + n by omega)
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.subset_ball_lt 0 (0 : E)
  let i : Fin (n + n) := ⟨0, by omega⟩
  let p : E := R • EuclideanSpace.single i 1
  have hp : ‖p‖ = R := by simp [p, norm_smul, Real.norm_of_nonneg hR.le]
  have hpK : p ∉ K := by
    intro h
    have h' := hKR h
    simpa only [mem_ball, dist_zero_right, hp, lt_self_iff_false] using h'
  have hApos := complexHessian_posDef_of_realBlockHessian
    (hu.of_le (by norm_num)).contDiffAt realDirections imagDirections (houtside p hpK) (hdet p)
  have hA : ∀ x, (complexHessian realDirections imagDirections u x).PosDef :=
    fun x => complexHessian_posDef_on_of_at isOpen_univ isPreconnected_univ hu.contDiffOn
      realDirections imagDirections (fun y _ => by rw [hdet y]; exact one_ne_zero)
      (mem_univ p) hApos x (mem_univ x)
  have hbd (x : E) (hx : x ∈ frontier (ball (0 : E) R)) :
      (realBlockHessian realDirections imagDirections u x).PosSemidef := by
    apply houtside
    intro hxK
    rw [isOpen_ball.frontier_eq] at hx
    exact hx.2 (hKR hxK)
  have hin := realBlockHessian_posSemidef_on_closure hd isOpen_ball
    (convex_ball (0 : E) R).isPreconnected
    (by rw [closure_ball _ hR.ne']; exact isCompact_closedBall _ _)
    isOpen_univ (subset_univ _) hu.contDiffOn (fun x _ => hA x)
    (fun x _ => hdet x) hbd
  intro x
  by_cases hx : x ∈ K
  · exact hin x (subset_closure (hKR hx))
  · exact houtside x hx

theorem quadratic_of_convex_outside_compact_ge_two
    (hn : 2 ≤ n) {u : E → ℝ} (hu : ContDiff ℝ 4 u)
    (hdet : ∀ x, (complexHessian realDirections imagDirections u x).det = 1)
    {K : Set E} (hK : IsCompact K)
    (houtside : ∀ x, x ∉ K → (realBlockHessian realDirections imagDirections u x).PosSemidef) :
    ∀ x, u x = u 0 + fderiv ℝ u 0 x + (1 / 2 : ℝ) * realHessian u 0 x x :=
  entire_convex_quadratic (by omega) hu hdet
    (convex_everywhere_of_convex_outside_compact hn hu hdet hK houtside)

/-- In one complex dimension the equation fixes the real Laplacian to four.
Convexity outside a compact set therefore bounds each actual Hessian entry
there; compactness supplies the remaining bound. -/
theorem hessian_bound_of_convex_outside_compact_one
    {u : DeGiorgi.AmbientSpace 2 → ℝ} (hu : ContDiff ℝ 4 u)
    (hdet : ∀ x, (complexHessian (realDirections (n := 1)) imagDirections u x).det = 1)
    {K : Set (DeGiorgi.AmbientSpace 2)} (hK : IsCompact K)
    (houtside : ∀ x, x ∉ K →
      (realBlockHessian (realDirections (n := 1)) imagDirections u x).PosSemidef) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ∀ i j, |euclideanHessian (n := 1) u x i j| ≤ C := by
  have hH : Continuous (euclideanHessian (n := 1) u) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact continuous_iff_continuousAt.mpr fun x =>
      (realHessian_contDiffAt_two hu.contDiffAt
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)).continuousAt
  obtain ⟨C, hC⟩ := (hK.image hH).isBounded.exists_norm_le
  refine ⟨max 4 C, (by exact le_trans (by norm_num) (le_max_left _ _)), ?_⟩
  intro x i j
  by_cases hx : x ∈ K
  · have hentry := Matrix.norm_entry_le_entrywise_sup_norm (euclideanHessian (n := 1) u x)
      (i := i) (j := j)
    rw [Real.norm_eq_abs] at hentry
    exact hentry.trans ((hC _ (mem_image_of_mem _ hx)).trans (le_max_right _ _))
  · have h11 : complexHessian (realDirections (n := 1)) imagDirections u x 0 0 = 1 := by
      simpa only [Matrix.det_fin_one] using hdet x
    have ht : (complexHessian (realDirections (n := 1)) imagDirections u x).trace.re = 1 := by
      simp only [Matrix.trace, Fin.sum_univ_one, Matrix.diag_apply, h11, Complex.one_re]
    have hb := CHS.Sections.euclideanHessian_entry_le_four_trace_of_convex
      (hu.of_le (by norm_num)).contDiffAt (houtside x hx) (hdet x) i j
    rw [ht, mul_one] at hb
    exact hb.trans (le_max_left _ _)

theorem quadratic_of_convex_outside_compact_one
    {u : DeGiorgi.AmbientSpace 2 → ℝ} (hu : ContDiff ℝ 4 u)
    (hdet : ∀ x, (complexHessian (realDirections (n := 1)) imagDirections u x).det = 1)
    {K : Set (DeGiorgi.AmbientSpace 2)} (hK : IsCompact K)
    (houtside : ∀ x, x ∉ K →
      (realBlockHessian (realDirections (n := 1)) imagDirections u x).PosSemidef) :
    ∀ x, u x = u 0 + fderiv ℝ u 0 x + (1 / 2 : ℝ) * realHessian u 0 x x := by
  obtain ⟨C, hC, hbound⟩ := hessian_bound_of_convex_outside_compact_one hu hdet hK houtside
  let v := dimensionOneExtension u
  have hv : ContDiff ℝ 4 v := dimensionOneExtension_contDiff hu
  have hu2 : ContDiff ℝ 2 u := hu.of_le (by norm_num)
  have hvA (x : DeGiorgi.AmbientSpace 4) :
      complexHessian (realDirections (n := 2)) imagDirections v x = 1 :=
    dimensionOneExtension_complexHessian hu2 hdet x
  have hvdet : ∀ x, (complexHessian (realDirections (n := 2)) imagDirections v x).det = 1 := by
    intro x
    rw [hvA, Matrix.det_one]
  have hvpos : ∀ x, (complexHessian (realDirections (n := 2)) imagDirections v x).PosDef := by
    intro x
    rw [hvA]
    exact Matrix.PosDef.one
  have hconst := bounded_positive_complexMongeAmpere_realHessian_constant_of_oscillation (n := 2)
    (by norm_num) hv hvdet hvpos (by linarith : 0 ≤ C + 2)
      (dimensionOneExtension_hessian_bound hu2 hC hbound)
  have heq : (fun x => v (firstComplexInclusion x)) = u :=
    funext (dimensionOneExtension_restrict u)
  have hp (x a b : DeGiorgi.AmbientSpace 2) :
      realHessian u x a b = realHessian v (firstComplexInclusion x)
        (firstComplexInclusion a) (firstComplexInclusion b) := by
    have h := realHessian_comp_affine firstComplexInclusion 0 (x := x)
      (hv.of_le (by norm_num)).contDiffAt a b
    simpa only [zero_add, heq] using h
  apply eq_quadratic_of_realHessian_constant hu2
  intro x
  ext a b
  rw [hp, hp, hconst (firstComplexInclusion x) (firstComplexInclusion 0)]

theorem quadratic_of_convex_outside_compact
    (hn : 1 ≤ n) {u : E → ℝ} (hu : ContDiff ℝ 4 u)
    (hdet : ∀ x, (complexHessian realDirections imagDirections u x).det = 1)
    {K : Set E} (hK : IsCompact K)
    (houtside : ∀ x, x ∉ K → (realBlockHessian realDirections imagDirections u x).PosSemidef) :
    ∀ x, u x = u 0 + fderiv ℝ u 0 x + (1 / 2 : ℝ) * realHessian u 0 x x := by
  rcases eq_or_lt_of_le hn with h1 | h2
  · subst n
    exact quadratic_of_convex_outside_compact_one hu hdet hK houtside
  · exact quadratic_of_convex_outside_compact_ge_two (by omega) hu hdet hK houtside

/-- The frozen manuscript's smooth exterior-convexity Corollary 1.4. -/
theorem corollary_1_4_exterior_convexity
    (hn : 1 ≤ n) {u : E → ℝ} (hu : ContDiff ℝ ∞ u)
    (hdet : ∀ x, (complexHessian realDirections imagDirections u x).det = 1)
    {K : Set E} (hK : IsCompact K)
    (houtside : ∀ x, x ∉ K → (realBlockHessian realDirections imagDirections u x).PosSemidef) :
    ∀ x, u x = u 0 + fderiv ℝ u 0 x + (1 / 2 : ℝ) * realHessian u 0 x x :=
  quadratic_of_convex_outside_compact hn
    (hu.of_le (WithTop.coe_le_coe.mpr (le_top : (4 : ℕ∞) ≤ ⊤))) hdet hK houtside

end CHS
