import CHSComparator.MathlibOnly.Statements
import CHSComparator.Statements

/-!
# Equivalence with the published CHS statements

The mixed and pure Hessians are expanded in real coordinates on the smooth
loci. The gradient equality is used almost everywhere for the volume
restricted to the open domain.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped ComplexOrder ContDiff ENNReal

noncomputable section

namespace CHSComparator.MathlibOnly.Bridge

open CHSComparator.MathlibOnly.Statements CHS.Analysis

variable {n : ℕ} {u : Space n → ℝ} {U : Set (Space n)} {x : Space n}

private theorem closure_iff : C2OnClosure u U ↔ CHS.Calculus.C2OnClosure u U := by
  constructor
  · rintro ⟨hu, hvalue, D, H, hD, hH, hDu, hHu⟩
    exact ⟨hu, ⟨⟨D, H, hvalue, hD, hH, hDu, hHu⟩⟩⟩
  · rintro ⟨hu, ⟨J⟩⟩
    exact ⟨hu, J.continuous_value, J.derivative, J.hessian, J.continuous_derivative,
      J.continuous_hessian, J.derivative_eq, J.hessian_eq⟩

private theorem mixed_eq (hu : ContDiffAt ℝ 2 u x) :
    mixedHessian u x = CHS.Calculus.complexHessian realDirections imagDirections u x := by
  ext i j
  exact (CHS.Calculus.complexHessian_real_entry hu realDirections imagDirections i j).symm

private theorem pure_eq (hu : ContDiffAt ℝ 2 u x) :
    pureHessian u x = CHS.Calculus.pureHessian realDirections imagDirections u x := by
  ext i j
  exact (CHS.Calculus.pureHessian_real_entry hu realDirections imagDirections i j).symm

private theorem det_iff (hu : ContDiffAt ℝ 2 u x) :
    (mixedHessian u x).det = 1 ↔
      (CHS.Calculus.complexHessian realDirections imagDirections u x).det = 1 := by
  rw [mixed_eq hu]

private theorem schur_iff (hu : ContDiffAt ℝ 2 u x) (κ : ℝ) :
    (κ • mixedHessian u x - pureHessian u x * ((mixedHessian u x).map star)⁻¹ *
      (pureHessian u x).map star).PosSemidef ↔
    (κ • CHS.Calculus.complexHessian realDirections imagDirections u x -
      CHS.Calculus.pureHessian realDirections imagDirections u x *
        ((CHS.Calculus.complexHessian realDirections imagDirections u x).map star)⁻¹ *
        (CHS.Calculus.pureHessian realDirections imagDirections u x).map star).PosSemidef := by
  rw [mixed_eq hu, pure_eq hu]

private theorem gradient_eq (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) :
    gradientLinf U u = CHS.Pogorelov.gradientLinfNormOn volume realDirections imagDirections u U := by
  unfold gradientLinf CHS.Pogorelov.gradientLinfNormOn scalarLinf CHS.Pogorelov.scalarLinfNormOn
  apply congrArg ENNReal.toReal
  apply eLpNorm_congr_ae
  filter_upwards [ae_restrict_mem (μ := volume) hU.measurableSet] with x hx
  have hd : DifferentiableAt ℝ u x :=
    (hu.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
  change Real.sqrt (∑ i, Complex.normSq
    (CHS.Pogorelov.wirtingerGradient realDirections imagDirections u x i)) = _
  simp only [CHS.Pogorelov.gradientNormSq, CHS.Pogorelov.wirtingerGradient_eq_dz hd]

private theorem smoothAt (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) {x : Space n}
    (hx : x ∈ U) : ContDiffAt ℝ 2 u x :=
  (hu.contDiffAt (hU.mem_nhds hx)).of_le (by norm_num)

private theorem entireSmoothAt (hu : ContDiff ℝ ∞ u) (x : Space n) :
    ContDiffAt ℝ 2 u x :=
  (hu.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))).contDiffAt

theorem theorem_1_1_iff : Statements.theorem_1_1 ↔ CHSComparator.Statements.theorem_1_1 := by
  constructor
  · intro h n hn κ hκ U hU hconn u hu hclosure hdet hbd hschur hgeom
    have hh := h hn hκ hU hconn hu (closure_iff.mpr hclosure)
      (fun _ hx => (det_iff (smoothAt hU hu hx)).mpr (hdet _ hx)) hbd
      (fun _ hx => (schur_iff (smoothAt hU hu hx) κ).mpr (hschur _ hx)) hgeom
    rw [gradient_eq hU hu] at hh
    exact hh
  · intro h n hn κ hκ U hU hconn u hu hclosure hdet hbd hschur hgeom
    have hh := h hn hκ hU hconn hu (closure_iff.mp hclosure)
      (fun _ hx => (det_iff (smoothAt hU hu hx)).mp (hdet _ hx)) hbd
      (fun _ hx => (schur_iff (smoothAt hU hu hx) κ).mp (hschur _ hx)) hgeom
    rw [gradient_eq hU hu]
    exact hh

theorem theorem_1_2_iff : Statements.theorem_1_2 ↔ CHSComparator.Statements.theorem_1_2 := by
  constructor
  · intro h n hn U hU hconv u hu hclosure hdet hR hbd hgeom
    have hh := h hn hU hconv hu (closure_iff.mpr hclosure)
      (fun _ hx => (det_iff (smoothAt hU hu hx)).mpr (hdet _ hx)) hR hbd hgeom
    rw [gradient_eq hU hu] at hh
    exact hh
  · intro h n hn U hU hconv u hu hclosure hdet hR hbd hgeom
    have hh := h hn hU hconv hu (closure_iff.mp hclosure)
      (fun _ hx => (det_iff (smoothAt hU hu hx)).mp (hdet _ hx)) hR hbd hgeom
    rw [gradient_eq hU hu]
    exact hh

theorem theorem_1_3_iff : Statements.theorem_1_3 ↔ CHSComparator.Statements.theorem_1_3 := by
  constructor
  · intro h n hn u hu hdet hR
    exact h hn hu (fun x => (det_iff (entireSmoothAt hu x)).mpr (hdet x)) hR
  · intro h n hn u hu hdet hR
    exact h hn hu (fun x => (det_iff (entireSmoothAt hu x)).mp (hdet x)) hR

theorem corollary_1_4_iff : Statements.corollary_1_4 ↔ CHSComparator.Statements.corollary_1_4 := by
  constructor
  · intro h n hn u hu hdet K hK hR
    exact h hn hu (fun x => (det_iff (entireSmoothAt hu x)).mpr (hdet x)) hK hR
  · intro h n hn u hu hdet K hK hR
    exact h hn hu (fun x => (det_iff (entireSmoothAt hu x)).mp (hdet x)) hK hR

end CHSComparator.MathlibOnly.Bridge
