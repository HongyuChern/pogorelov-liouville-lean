import CHS.Calculus.QuadraticPerturbation
import CHS.Calculus.PotentialConstants

/-!
# Actual Hessians under affine pullback and section rescaling

All derivatives are Fréchet derivatives of the transformed potential.
The normalization by `1/h` exactly cancels the two factors `sqrt h` in
the real Hessian.  Complex and pure Hessian formulas follow in the same
fixed directional convention.
-/

set_option autoImplicit false
noncomputable section

open Filter
open scoped ContDiff Topology

namespace CHS.Calculus

variable {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem contDiff_normalized_affine {k : ℕ∞ω} {u : F → ℝ}
    (hu : ContDiff ℝ k u) (T : E →L[ℝ] F) (c : F) (h : ℝ) :
    ContDiff ℝ k (fun y => h⁻¹ * u (c + Real.sqrt h • T y) - 1) := by
  have hT : ContDiff ℝ k (fun y => c + Real.sqrt h • T y) := by fun_prop
  exact (contDiff_const.mul (hu.comp hT)).sub contDiff_const

theorem realHessian_comp_affine
    {u : F → ℝ} (T : E →L[ℝ] F) (c : F) {x : E}
    (hu : ContDiffAt ℝ 2 u (c + T x)) (v w : E) :
    realHessian (fun y => u (c + T y)) x v w = realHessian u (c + T x) (T v) (T w) := by
  let C : (F →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ E F ℝ).flip T
  have ha (y : E) : HasFDerivAt (fun z => c + T z) T y := T.hasFDerivAt.const_add c
  have hnear : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 u (c + T y) :=
    (ha x).continuousAt.eventually (hu.eventually (by simp))
  have hDnear : fderiv ℝ (fun y => u (c + T y)) =ᶠ[𝓝 x]
      (fun y => (fderiv ℝ u (c + T y)).comp T) := by
    filter_upwards [hnear] with y hy
    exact ((hy.differentiableAt (by norm_num)).hasFDerivAt.comp y (ha y)).fderiv
  have hdu : HasFDerivAt (fun y => fderiv ℝ u (c + T y))
      ((realHessian u (c + T x)).comp T) x :=
    ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt.comp x (ha x)
  have hD : HasFDerivAt (fun y => (fderiv ℝ u (c + T y)).comp T)
      (C.comp ((realHessian u (c + T x)).comp T)) x := C.hasFDerivAt.comp x hdu
  change fderiv ℝ (fderiv ℝ (fun y => u (c + T y))) x v w = _
  rw [hDnear.fderiv_eq, hD.fderiv]
  rfl

theorem complexHessian_comp_affine
    {u : F → ℝ} (T : E →L[ℝ] F) (c : F) {x : E}
    (hu : ContDiffAt ℝ 2 u (c + T x)) (a b : ι → E) :
    complexHessian a b (fun y => u (c + T y)) x =
      complexHessian (fun i => T (a i)) (fun i => T (b i)) u (c + T x) := by
  have hf : ContDiffAt ℝ 2 (fun y => u (c + T y)) x :=
    hu.comp x (contDiffAt_const.add T.contDiff.contDiffAt)
  ext i j
  rw [complexHessian_real_entry hf, complexHessian_real_entry hu]
  simp only [realHessian_comp_affine T c hu]

theorem pureHessian_comp_affine
    {u : F → ℝ} (T : E →L[ℝ] F) (c : F) {x : E}
    (hu : ContDiffAt ℝ 2 u (c + T x)) (a b : ι → E) :
    pureHessian a b (fun y => u (c + T y)) x =
      pureHessian (fun i => T (a i)) (fun i => T (b i)) u (c + T x) := by
  have hf : ContDiffAt ℝ 2 (fun y => u (c + T y)) x :=
    hu.comp x (contDiffAt_const.add T.contDiff.contDiffAt)
  ext i j
  rw [pureHessian_real_entry hf, pureHessian_real_entry hu]
  simp only [realHessian_comp_affine T c hu]

theorem realHessian_normalized_affine
    {u : F → ℝ} (T : E →L[ℝ] F) (c : F) {h : ℝ} (hh : 0 < h) {x : E}
    (hu : ContDiffAt ℝ 2 u (c + Real.sqrt h • T x)) (v w : E) :
    realHessian (fun y => h⁻¹ * u (c + Real.sqrt h • T y) - 1) x v w =
      realHessian u (c + Real.sqrt h • T x) (T v) (T w) := by
  have hconst := realHessian_add_const
    (fun y => h⁻¹ * u (c + Real.sqrt h • T y)) (-1) x
  change realHessian (fun y => h⁻¹ * u (c + Real.sqrt h • T y) + -1) x v w = _
  rw [hconst, realHessian_const_mul]
  change h⁻¹ * realHessian (fun y => u (c + (Real.sqrt h • T) y)) x v w = _
  rw [realHessian_comp_affine (Real.sqrt h • T) c hu]
  simp only [ContinuousLinearMap.smul_apply, map_smul, smul_apply, smul_eq_mul]
  have hs := Real.sq_sqrt hh.le
  have hh0 : h ≠ 0 := hh.ne'
  calc
    _ = (h⁻¹ * (Real.sqrt h) ^ 2) * realHessian u (c + Real.sqrt h • T x) (T v) (T w) := by ring
    _ = _ := by rw [hs, inv_mul_cancel₀ hh0, one_mul]

theorem complexHessian_normalized_affine
    {u : F → ℝ} (T : E →L[ℝ] F) (c : F) {h : ℝ} (hh : 0 < h) {x : E}
    (hu : ContDiffAt ℝ 2 u (c + Real.sqrt h • T x)) (a b : ι → E) :
    complexHessian a b (fun y => h⁻¹ * u (c + Real.sqrt h • T y) - 1) x =
      complexHessian (fun i => T (a i)) (fun i => T (b i)) u (c + Real.sqrt h • T x) := by
  have hf : ContDiffAt ℝ 2 (fun y => h⁻¹ * u (c + Real.sqrt h • T y) - 1) x :=
    (contDiffAt_const.mul (hu.comp x (contDiffAt_const.add
      (contDiffAt_const.smul T.contDiff.contDiffAt)))).sub contDiffAt_const
  ext i j
  rw [complexHessian_real_entry hf, complexHessian_real_entry hu]
  simp only [realHessian_normalized_affine T c hh hu]

theorem pureHessian_normalized_affine
    {u : F → ℝ} (T : E →L[ℝ] F) (c : F) {h : ℝ} (hh : 0 < h) {x : E}
    (hu : ContDiffAt ℝ 2 u (c + Real.sqrt h • T x)) (a b : ι → E) :
    pureHessian a b (fun y => h⁻¹ * u (c + Real.sqrt h • T y) - 1) x =
      pureHessian (fun i => T (a i)) (fun i => T (b i)) u (c + Real.sqrt h • T x) := by
  have hf : ContDiffAt ℝ 2 (fun y => h⁻¹ * u (c + Real.sqrt h • T y) - 1) x :=
    (contDiffAt_const.mul (hu.comp x (contDiffAt_const.add
      (contDiffAt_const.smul T.contDiff.contDiffAt)))).sub contDiffAt_const
  ext i j
  rw [pureHessian_real_entry hf, pureHessian_real_entry hu]
  simp only [realHessian_normalized_affine T c hh hu]

end CHS.Calculus
