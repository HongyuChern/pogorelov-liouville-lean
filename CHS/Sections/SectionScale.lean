import CHS.Sections.EqualDetComparison
import CHS.Algebra.ComplexNormalization
import CHS.Pogorelov.SubdomainGeometry

/-!
# The section scale bound (3.5)

The two equal-determinant comparisons are proved from the ellipsoid
sandwich (3.4), then evaluated at the ellipsoid center and the normalized
minimum.  The common real translation quotient is the actual quotient
of the section closure; the inner comparison domain inherits compactness.
Existence of the sandwich itself is a separate convex-geometric step.
-/

set_option autoImplicit false
noncomputable section

open Set
open scoped ContDiff ComplexOrder

namespace CHS.Sections

open CHS.Calculus CHS.Analysis CHS.Algebra CHS.Pogorelov

variable {n : ℕ}
local notation "E₀" => DeGiorgi.AmbientSpace (n + n)

theorem section_scale_bounds_of_quadratic_sandwich
    (hn : 0 < n) {u q : E₀ → ℝ} (hu : ContDiff ℝ 2 u) (hq : ContDiff ℝ 2 q)
    (hu0 : u 0 = 0) (hunonneg : ∀ x, 0 ≤ u x) (hqnonneg : ∀ x, 0 ≤ q x)
    (hdet : ∀ x, (complexHessian realDirections imagDirections u x).det = 1)
    (hA : ∀ x, (complexHessian realDirections imagDirections u x).PosDef)
    {C : Matrix (Fin n) (Fin n) ℂ} (hC : C.PosDef)
    (hqH : ∀ x, complexHessian realDirections imagDirections q x = C)
    (a : E₀) (hqa : q a = 0) {h : ℝ} (hh : 0 < h)
    (hinner : ∀ x, q x < 1 → u x < h)
    (houter : ∀ x, u x < h → q x < 4 * (n : ℝ) ^ 2)
    (K : Submodule ℝ E₀)
    (huinv : ∀ x v : E₀, v ∈ K → u (x + v) = u x)
    (hqinv : ∀ x v : E₀, v ∈ K → q (x + v) = q x)
    (hquot : IsCompact ((Submodule.Quotient.mk : E₀ → E₀ ⧸ K) '' closure {x | u x < h})) :
    (∀ x ∈ closure {x | q x < 1},
      u x - h ≤ (hermitianDetRoot C)⁻¹ * (q x - 1)) ∧
    (∀ x ∈ closure {x | u x < h},
      (hermitianDetRoot C)⁻¹ * (q x - 4 * (n : ℝ) ^ 2) ≤ u x - h) ∧
    1 ≤ h * hermitianDetRoot C ∧ h * hermitianDetRoot C ≤ 4 * (n : ℝ) ^ 2 := by
  let c := hermitianDetRoot C
  let U : Set E₀ := {x | u x < h}
  let V : Set E₀ := {x | q x < 1}
  let F : E₀ → ℝ := fun x => u x + -h
  let Q (t : ℝ) : E₀ → ℝ := fun x => c⁻¹ * (q x + -t)
  have hc : 0 < c := hermitianDetRoot_pos hC
  have hroot : (c : ℂ) ^ n = C.det := hermitianDetRoot_pow hn hC
  have hU : IsOpen U := isOpen_lt hu.continuous continuous_const
  have hV : IsOpen V := isOpen_lt hq.continuous continuous_const
  have hVU : V ⊆ U := hinner
  have hUinv : ∀ x ∈ U, ∀ v ∈ K, x + v ∈ U := by
    intro x hx v hv
    change u (x + v) < h
    rwa [huinv x v hv]
  have hVinv : ∀ x ∈ V, ∀ v ∈ K, x + v ∈ V := by
    intro x hx v hv
    change q (x + v) < 1
    rwa [hqinv x v hv]
  have hquotV := compact_real_quotient_of_invariant_subdomain K hVU hUinv hVinv hquot
  have hF : ContDiff ℝ 2 F := hu.add contDiff_const
  have hQ (t : ℝ) : ContDiff ℝ 2 (Q t) := contDiff_const.mul (hq.add contDiff_const)
  have hFH (x : E₀) : complexHessian realDirections imagDirections F x =
      complexHessian realDirections imagDirections u x :=
    complexHessian_add_const realDirections imagDirections u (-h) x
  have hQH (t : ℝ) (x : E₀) : complexHessian realDirections imagDirections (Q t) x = c⁻¹ • C := by
    simp only [Q, complexHessian_const_mul, complexHessian_add_const, hqH]
  have hQpos (t : ℝ) (x : E₀) : (complexHessian realDirections imagDirections (Q t) x).PosDef := by
    rw [hQH]
    exact hC.smul (inv_pos.mpr hc)
  have hQdet (t : ℝ) (x : E₀) : (complexHessian realDirections imagDirections (Q t) x).det = 1 := by
    rw [hQH]
    change (((c⁻¹ : ℝ) : ℂ) • C).det = 1
    rw [Matrix.det_smul, Fintype.card_fin, Complex.ofReal_inv, inv_pow, ← hroot,
      inv_mul_cancel₀ (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hc.ne'))]
  have hFinv (x v : E₀) (hv : v ∈ K) : F (x + v) = F x := by
    dsimp only [F]
    rw [huinv x v hv]
  have hQinv (t : ℝ) (x v : E₀) (hv : v ∈ K) : Q t (x + v) = Q t x := by
    dsimp only [Q]
    rw [hqinv x v hv]
  have hUbar : closure U ⊆ {x | u x ≤ h} :=
    closure_minimal (fun x hx => show u x ≤ h from le_of_lt hx)
      (isClosed_le hu.continuous continuous_const)
  have hqbar : closure U ⊆ {x | q x ≤ 4 * (n : ℝ) ^ 2} :=
    closure_minimal (fun x hx => (houter x hx).le) (isClosed_le hq.continuous continuous_const)
  have hinnerCompare : ∀ x ∈ closure V, F x ≤ Q 1 x := by
    apply le_on_closure_of_det_eq_one_of_compact_real_quotient hn K hV hVinv hquotV
      realDirections imagDirections hF.continuous.continuousOn (hQ 1).continuous.continuousOn
      (fun x _ v hv => hFinv x v hv) (fun x _ v hv => hQinv 1 x v hv)
      hF.contDiffOn (hQ 1).contDiffOn
      (fun x _ => by rw [hFH]; exact hA x)
      (fun x _ => by rw [hFH]; exact hdet x) (fun x _ => hQdet 1 x)
    intro x hx
    have heq : q x = 1 := frontier_lt_subset_eq hq.continuous continuous_const hx
    have hux : u x ≤ h := hUbar (closure_mono hVU (frontier_subset_closure hx))
    dsimp only [F, Q]
    rw [heq]
    nlinarith
  have houterCompare : ∀ x ∈ closure U, Q (4 * (n : ℝ) ^ 2) x ≤ F x := by
    apply le_on_closure_of_det_eq_one_of_compact_real_quotient hn K hU hUinv hquot
      realDirections imagDirections (hQ _).continuous.continuousOn hF.continuous.continuousOn
      (fun x _ v hv => hQinv _ x v hv) (fun x _ v hv => hFinv x v hv)
      (hQ _).contDiffOn hF.contDiffOn (fun x _ => hQpos _ x)
      (fun x _ => hQdet _ x) (fun x _ => by rw [hFH]; exact hdet x)
    intro x hx
    have heq : u x = h := frontier_lt_subset_eq hu.continuous continuous_const hx
    have hqx : q x ≤ 4 * (n : ℝ) ^ 2 := hqbar (frontier_subset_closure hx)
    have hp := mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hc.le)
      (sub_nonpos.mpr hqx)
    dsimp only [F, Q]
    rw [heq]
    linarith
  have hlower : 1 ≤ h * c := by
    have haV : a ∈ V := by change q a < 1; rw [hqa]; norm_num
    have hp := mul_le_mul_of_nonneg_right (hinnerCompare a (subset_closure haV)) hc.le
    have hcancel : Q 1 a * c = -1 := by
      dsimp only [Q]
      rw [hqa]
      field_simp
      <;> ring
    rw [hcancel] at hp
    dsimp only [F] at hp
    have hprod := mul_nonneg (hunonneg a) hc.le
    nlinarith
  have hupper : h * c ≤ 4 * (n : ℝ) ^ 2 := by
    have hzU : (0 : E₀) ∈ U := by change u 0 < h; rwa [hu0]
    have hp := mul_le_mul_of_nonneg_right (houterCompare 0 (subset_closure hzU)) hc.le
    have hcancel : Q (4 * (n : ℝ) ^ 2) 0 * c = q 0 - 4 * (n : ℝ) ^ 2 := by
      dsimp only [Q]
      field_simp
      <;> ring
    rw [hcancel] at hp
    dsimp only [F] at hp
    rw [hu0] at hp
    linarith [hqnonneg 0]
  exact ⟨by simpa only [F, Q, c, sub_eq_add_neg] using hinnerCompare,
    by simpa only [F, Q, c, sub_eq_add_neg] using houterCompare, hlower, hupper⟩

end CHS.Sections
