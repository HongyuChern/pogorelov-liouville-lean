import Mathlib.Analysis.Matrix.Order
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Propagation of a definite branch through a continuous nonsingular field

The positive cone is open among Hermitian matrices: its complement is the
projection of a closed set over the compact unit sphere.  In a nonsingular
Hermitian family it is also closed, since a positive semidefinite limit is
positive definite.  Connectedness therefore propagates definiteness.

This file proves the branch propagation rather than assuming constant
inertia.  It does not establish the existence of a definite extremum.
-/

set_option autoImplicit false
noncomputable section

open Matrix Set
open scoped BigOperators ComplexOrder

namespace CHS.Algebra

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def realQuadratic (A : Matrix ι ι ℂ) (v : ι → ℂ) : ℝ :=
  (star v ⬝ᵥ A.mulVec v).re

theorem realQuadratic_real_smul (A : Matrix ι ι ℂ) (v : ι → ℂ) (r : ℝ) :
    realQuadratic A (r • v) = r ^ 2 * realQuadratic A v := by
  simp only [realQuadratic, star_smul, star_trivial, Matrix.mulVec_smul,
    smul_dotProduct, dotProduct_smul, smul_smul, Complex.real_smul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

theorem posDef_iff_positive_unit_sphere {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    A.PosDef ↔ ∀ v : ι → ℂ, ‖v‖ = 1 → 0 < realQuadratic A v := by
  constructor
  · intro h v hv
    exact h.re_dotProduct_pos (by
      intro heq
      rw [heq, norm_zero] at hv
      exact zero_ne_one hv)
  · intro h
    apply Matrix.PosDef.of_dotProduct_mulVec_pos hA
    intro v hv
    apply Complex.pos_iff.mpr
    refine ⟨?_, (hA.im_star_dotProduct_mulVec_self v).symm⟩
    let w : ι → ℂ := ‖v‖⁻¹ • v
    have hw : ‖w‖ = 1 := by
      dsimp only [w]
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
    have hq := h w hw
    rw [realQuadratic_real_smul] at hq
    by_contra! hnon
    have hle := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg ‖v‖⁻¹) hnon
    exact (not_lt_of_ge hle) hq

variable {X : Type*} [TopologicalSpace X]

theorem isOpen_posDef_preimage {A : X → Matrix ι ι ℂ} (hA : Continuous A)
    (hherm : ∀ x, (A x).IsHermitian) : IsOpen {x | (A x).PosDef} := by
  let S := Metric.sphere (0 : ι → ℂ) 1
  letI : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_sphere (0 : ι → ℂ) 1)
  let C : Set (X × S) := {p | realQuadratic (A p.1) p.2 ≤ 0}
  have hq : Continuous (fun p : X × S => realQuadratic (A p.1) p.2) := by
    have hv (i : ι) : Continuous (fun p : X × S => (p.2 : ι → ℂ) i) :=
      (continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)
    have ha (i j : ι) : Continuous (fun p : X × S => A p.1 i j) :=
      (continuous_apply j).comp ((continuous_apply i).comp (hA.comp continuous_fst))
    simp only [realQuadratic, Matrix.mulVec, dotProduct, Pi.star_apply]
    exact Complex.continuous_re.comp (continuous_finset_sum _ fun i _ =>
      (hv i).star.mul (continuous_finset_sum _ fun j _ => (ha i j).mul (hv j)))
  have hC : IsClosed C := isClosed_le hq continuous_const
  have hproj : IsClosed (Prod.fst '' C) := isClosedMap_fst_of_compactSpace C hC
  have heq : {x | (A x).PosDef} = (Prod.fst '' C)ᶜ := by
    ext x
    rw [mem_setOf_eq, posDef_iff_positive_unit_sphere (hherm x)]
    constructor
    · intro hx hbad
      obtain ⟨⟨y, v⟩, hbad, rfl⟩ := hbad
      have hv : ‖(v : ι → ℂ)‖ = 1 := by
        simpa only [S, Metric.mem_sphere, dist_zero_right] using v.property
      exact (not_le_of_gt (hx v hv)) hbad
    · intro hx v hv
      by_contra! hbad
      apply hx
      refine ⟨(x, ⟨v, ?_⟩), hbad, rfl⟩
      simpa only [S, Metric.mem_sphere, dist_zero_right] using hv
  rw [heq]
  exact hproj.isOpen_compl

theorem isClosed_posDef_preimage_of_nonsingular {A : X → Matrix ι ι ℂ}
    (hA : Continuous A) (hherm : ∀ x, (A x).IsHermitian)
    (hdet : ∀ x, (A x).det ≠ 0) : IsClosed {x | (A x).PosDef} := by
  have heq : {x | (A x).PosDef} = ⋂ v : ι → ℂ, {x | 0 ≤ realQuadratic (A x) v} := by
    ext x
    simp only [mem_setOf_eq, mem_iInter]
    constructor
    · intro hx v
      exact hx.posSemidef.re_dotProduct_nonneg v
    · intro hx
      have hps : (A x).PosSemidef := Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
        (hherm x) (fun v => Complex.nonneg_iff.mpr
          ⟨hx v, ((hherm x).im_star_dotProduct_mulVec_self v).symm⟩)
      exact hps.posDef_iff_det_ne_zero.mpr (hdet x)
  rw [heq]
  apply isClosed_iInter
  intro v
  apply isClosed_le continuous_const
  unfold realQuadratic Matrix.mulVec dotProduct
  fun_prop

theorem posDef_everywhere_of_preconnected [PreconnectedSpace X]
    {A : X → Matrix ι ι ℂ} (hA : Continuous A) (hherm : ∀ x, (A x).IsHermitian)
    (hdet : ∀ x, (A x).det ≠ 0) {x₀ : X} (hpos : (A x₀).PosDef) :
    ∀ x, (A x).PosDef := by
  have hcl : IsClopen {x | (A x).PosDef} :=
    ⟨isClosed_posDef_preimage_of_nonsingular hA hherm hdet,
      isOpen_posDef_preimage hA hherm⟩
  have heq := hcl.eq_univ ⟨x₀, hpos⟩
  intro x
  have hx : x ∈ {x | (A x).PosDef} := heq.symm ▸ mem_univ x
  exact hx

end CHS.Algebra
