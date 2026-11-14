import CHS.Sections.Comparison
import CHS.Calculus.PotentialScalars
import CHS.Pogorelov.CompactQuotient

/-!
# Comparison for equal Monge–Ampère determinant

A small positive rescaling of `f`, shifted down by its compact upper
bound, has strictly larger determinant and preserves the boundary order.
The strict comparison theorem then rules out any positive gap `f-g`.
This proves the equal-right-hand-side comparison used before (3.5), on
both compact closures and actual compact real-translation quotients.
-/

set_option autoImplicit false
noncomputable section

open Set Matrix
open scoped ContDiff ComplexOrder

namespace CHS.Sections

open CHS.Calculus CHS.Pogorelov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

theorem le_on_closure_of_det_eq_one_of_compact_representatives
    (hn : 0 < n) {U C : Set E} (hU : IsOpen U) (hC : IsCompact C) (hCU : C ⊆ closure U)
    (a b : Fin n → E) {f g : E → ℝ}
    (hf : ContinuousOn f (closure U)) (hg : ContinuousOn g (closure U))
    (hf₂ : ContDiffOn ℝ 2 f U) (hg₂ : ContDiffOn ℝ 2 g U)
    (hpos : ∀ x ∈ U, (complexHessian a b f x).PosDef)
    (hfdet : ∀ x ∈ U, (complexHessian a b f x).det = 1)
    (hgdet : ∀ x ∈ U, (complexHessian a b g x).det = 1)
    (hbd : ∀ x ∈ frontier U, f x ≤ g x)
    (hrep : ∀ x ∈ closure U, ∃ y ∈ C, f x = f y ∧ g x = g y) :
    ∀ x ∈ closure U, f x ≤ g x := by
  intro x hx
  by_contra! hgap
  obtain ⟨M, hM⟩ := hC.bddAbove_image (hf.mono hCU)
  have hupper (y : E) (hy : y ∈ closure U) : f y ≤ M := by
    obtain ⟨z, hz, hfz, _⟩ := hrep y hy
    rw [hfz]
    exact hM (mem_image_of_mem f hz)
  let s := M - f x
  have hs : 0 ≤ s := sub_nonneg.mpr (hupper x hx)
  let ε := (f x - g x) / (2 * (s + 1))
  have hε : 0 < ε := div_pos (sub_pos.mpr hgap) (by positivity)
  have hεeq : ε * (2 * (s + 1)) = f x - g x :=
    div_mul_cancel₀ _ (by positivity : (2 : ℝ) * (s + 1) ≠ 0)
  have hsmall : ε * s < f x - g x := by nlinarith
  let F := fun y => (1 + ε) * f y + -(ε * M)
  have hF : ContinuousOn F (closure U) := (continuousOn_const.mul hf).add continuousOn_const
  have hF₂ : ContDiffOn ℝ 2 F U := (contDiffOn_const.mul hf₂).add contDiffOn_const
  have hFH (y : E) : complexHessian a b F y = (1 + ε) • complexHessian a b f y := by
    dsimp only [F]
    rw [complexHessian_add_const, complexHessian_const_mul]
  have hFpos (y : E) (hy : y ∈ U) : (complexHessian a b F y).PosDef := by
    rw [hFH]
    exact (hpos y hy).smul (by linarith)
  have hFdet (y : E) (hy : y ∈ U) :
      (complexHessian a b g y).det < (complexHessian a b F y).det := by
    rw [hgdet y hy, hFH]
    change (1 : ℂ) < (((1 + ε : ℝ) : ℂ) • complexHessian a b f y).det
    rw [Matrix.det_smul, Fintype.card_fin, hfdet y hy, mul_one]
    exact_mod_cast (one_lt_pow₀ (by linarith : (1 : ℝ) < 1 + ε) hn.ne')
  have hFbd (y : E) (hy : y ∈ frontier U) : F y ≤ g y := by
    have hu := hupper y (frontier_subset_closure hy)
    have hprod := mul_nonneg hε.le (sub_nonneg.mpr hu)
    have hb := hbd y hy
    dsimp [F]
    nlinarith
  have hFrep : ∀ y ∈ closure U, ∃ z ∈ C, F y - g y = F z - g z := by
    intro y hy
    obtain ⟨z, hz, hfz, hgz⟩ := hrep y hy
    exact ⟨z, hz, by dsimp [F]; rw [hfz, hgz]⟩
  have hcompare := le_on_closure_of_det_lt_of_compact_representatives hU hC hCU a b
    hF hg hF₂ hg₂ hFpos hFdet hFbd hFrep x hx
  dsimp [F, s] at hcompare hsmall
  nlinarith

theorem le_on_closure_of_det_eq_one
    (hn : 0 < n) {U : Set E} (hU : IsOpen U) (hC : IsCompact (closure U))
    (a b : Fin n → E) {f g : E → ℝ}
    (hf : ContinuousOn f (closure U)) (hg : ContinuousOn g (closure U))
    (hf₂ : ContDiffOn ℝ 2 f U) (hg₂ : ContDiffOn ℝ 2 g U)
    (hpos : ∀ x ∈ U, (complexHessian a b f x).PosDef)
    (hfdet : ∀ x ∈ U, (complexHessian a b f x).det = 1)
    (hgdet : ∀ x ∈ U, (complexHessian a b g x).det = 1)
    (hbd : ∀ x ∈ frontier U, f x ≤ g x) : ∀ x ∈ closure U, f x ≤ g x :=
  le_on_closure_of_det_eq_one_of_compact_representatives hn hU hC Subset.rfl a b
    hf hg hf₂ hg₂ hpos hfdet hgdet hbd (fun x hx => ⟨x, hx, rfl, rfl⟩)

section Quotient

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem le_on_closure_of_det_eq_one_of_compact_real_quotient
    (hn : 0 < n) (K : Submodule ℝ F) {U : Set F} (hU : IsOpen U)
    (hUinv : ∀ x ∈ U, ∀ v ∈ K, x + v ∈ U)
    (hquot : IsCompact ((Submodule.Quotient.mk : F → F ⧸ K) '' closure U))
    (a b : Fin n → F) {f g : F → ℝ}
    (hf : ContinuousOn f (closure U)) (hg : ContinuousOn g (closure U))
    (hfinv : ∀ x ∈ U, ∀ v ∈ K, f (x + v) = f x)
    (hginv : ∀ x ∈ U, ∀ v ∈ K, g (x + v) = g x)
    (hf₂ : ContDiffOn ℝ 2 f U) (hg₂ : ContDiffOn ℝ 2 g U)
    (hpos : ∀ x ∈ U, (complexHessian a b f x).PosDef)
    (hfdet : ∀ x ∈ U, (complexHessian a b f x).det = 1)
    (hgdet : ∀ x ∈ U, (complexHessian a b g x).det = 1)
    (hbd : ∀ x ∈ frontier U, f x ≤ g x) : ∀ x ∈ closure U, f x ≤ g x := by
  obtain ⟨C, hC, hCU, hrep⟩ := compact_representatives_of_compact_real_quotient K hUinv hquot
  apply le_on_closure_of_det_eq_one_of_compact_representatives hn hU hC hCU a b
    hf hg hf₂ hg₂ hpos hfdet hgdet hbd
  intro x hx
  obtain ⟨y, hy, hdiff⟩ := hrep x hx
  have hfeq := translation_invariant_on_closure K hUinv hf hfinv x hx (y - x) hdiff
  have hgeq := translation_invariant_on_closure K hUinv hg hginv x hx (y - x) hdiff
  have heqyx : x + (y - x) = y := by abel
  rw [heqyx] at hfeq hgeq
  exact ⟨y, hy, hfeq.symm, hgeq.symm⟩

end Quotient
end CHS.Sections
