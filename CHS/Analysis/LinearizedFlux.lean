import CHS.Analysis.LocalClassicalFlux
import CHS.Calculus.SchurScalar

/-!
# Divergence of the linearized flux

The real coefficient field acts on the actual Euclidean gradient. Column
divergence removes its first-order contribution to the divergence of the flux.
-/

set_option autoImplicit false
noncomputable section

open DeGiorgi Filter Set
open scoped BigOperators ComplexOrder ContDiff Topology

namespace CHS.Analysis

variable {d : ℕ} [NeZero d]
local notation "E" => AmbientSpace d

theorem classicalDivergence_matMulE_gradient
    {A : E → Matrix (Fin d) (Fin d) ℝ} {v : E → ℝ} {x : E}
    (hA : ∀ i j, DifferentiableAt ℝ (fun y => A y i j) x)
    (hv : ContDiffAt ℝ 2 v x)
    (hdiv : ∀ j, (∑ i, fderiv ℝ (fun y => A y i j) x (EuclideanSpace.single i 1)) = 0) :
    classicalDivergence (fun y => matMulE (A y) (smoothGradField v y)) x =
      ∑ i, ∑ j, A x i j *
        Calculus.realHessian v x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  let e : Fin d → E := fun i => EuclideanSpace.single i 1
  have hderiv := (hv.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hd (j : Fin d) : DifferentiableAt ℝ (fun y => fderiv ℝ v y (e j)) x :=
    hderiv.clm_apply (differentiableAt_const _)
  have hsecond (i j : Fin d) :
      fderiv ℝ (fun y => fderiv ℝ v y (e j)) x (e i) =
        Calculus.realHessian v x (e i) (e j) := by
    rw [(hderiv.hasFDerivAt.clm_apply (hasFDerivAt_const (e j) x)).fderiv]
    simp [Calculus.realHessian]
  change (∑ i, fderiv ℝ (fun y => ∑ j, A y i j * fderiv ℝ v y (e j)) x (e i)) = _
  have hexpand (i : Fin d) :
      fderiv ℝ (fun y => ∑ j, A y i j * fderiv ℝ v y (e j)) x (e i) =
        ∑ j, (A x i j * Calculus.realHessian v x (e i) (e j) +
          fderiv ℝ v x (e j) * fderiv ℝ (fun y => A y i j) x (e i)) := by
    rw [fderiv_fun_sum (u := Finset.univ)
      (A := fun j y => A y i j * fderiv ℝ v y (e j))
      (fun j _ => (hA i j).mul (hd j)), ContinuousLinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [fderiv_fun_mul (hA i j) (hd j)]
    simp only [ContinuousLinearMap.add_apply, smul_apply, smul_eq_mul, hsecond]
  simp only [hexpand, Finset.sum_add_distrib]
  rw [add_eq_left, Finset.sum_comm]
  simp only [← Finset.mul_sum, e, hdiv, mul_zero, Finset.sum_const_zero]


open Calculus

variable {n : ℕ}

local notation "Eℂ" => AmbientSpace (n + n)

def realDirections (i : Fin n) : Eℂ := EuclideanSpace.single (finSumFinEquiv (Sum.inl i)) 1

def imagDirections (i : Fin n) : Eℂ := EuclideanSpace.single (finSumFinEquiv (Sum.inr i)) 1

private theorem euclideanDirection_sum (i : Fin n ⊕ Fin n) :
    EuclideanSpace.single (finSumFinEquiv i) (1 : ℝ) =
      Sum.elim realDirections imagDirections i := by
  cases i <;> rfl

/-- The actual real linearized coefficients in the Euclidean coordinate order. -/
def complexLinearizedCoeff (u : Eℂ → ℝ) (x : Eℂ) :
    Matrix (Fin (n + n)) (Fin (n + n)) ℝ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (realLinearizationMatrix (complexHessian realDirections imagDirections u x)⁻¹)

theorem complexLinearizedCoeff_contDiffAt {u : Eℂ → ℝ} {x : Eℂ}
    (hu : ContDiffAt ℝ 4 u x)
    (hdet : (fun y => (complexHessian realDirections imagDirections u y).det) =ᶠ[𝓝 x]
      (fun _ => (1 : ℂ))) (i j : Fin (n + n)) :
    ContDiffAt ℝ 2 (fun y => complexLinearizedCoeff u y i j) x :=
  realLinearizationMatrix_contDiffAt
    (field_inverse_contDiffAt_of_det_one
      (complexHessian_contDiffAt_two hu realDirections imagDirections) hdet)
    (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)

theorem complexLinearizedCoeff_divergence {u : Eℂ → ℝ} {x : Eℂ}
    (hu : ContDiffAt ℝ 3 u x)
    (hdet : (fun y => (complexHessian realDirections imagDirections u y).det) =ᶠ[𝓝 x]
      (fun _ => (1 : ℂ))) (j : Fin (n + n)) :
    (∑ i, fderiv ℝ (fun y => complexLinearizedCoeff u y i j) x
      (EuclideanSpace.single i 1)) = 0 := by
  rw [← Equiv.sum_comp finSumFinEquiv]
  simp only [complexLinearizedCoeff, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, euclideanDirection_sum]
  exact complexHessian_realLinearization_divergence hu realDirections imagDirections hdet
    (finSumFinEquiv.symm j)

theorem schurPair_flux_divergence_nonpos [NeZero (n + n)]
    {u : Eℂ → ℝ} {U : Set Eℂ} (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U)
    (hdet : ∀ y ∈ U, (complexHessian realDirections imagDirections u y).det = 1)
    {x : Eℂ} (hx : x ∈ U)
    (hA : (complexHessian realDirections imagDirections u x).PosDef) (ξ : Fin n → ℂ) :
    classicalDivergence (fun y => matMulE (complexLinearizedCoeff u y)
      (smoothGradField (fun z => (matrixPair (schurHessian realDirections imagDirections u) ξ z).re) y))
      x ≤ 0 := by
  let g := matrixPair (schurHessian realDirections imagDirections u) ξ
  have hg : ContDiffAt ℝ 2 g x :=
    matrixPair_contDiffAt (schurHessian_contDiffAt_two hU hu _ _ hdet hx) ξ
  have hv : ContDiffAt ℝ 2 (fun y => (g y).re) x :=
    Complex.reCLM.contDiff.contDiffAt.comp x hg
  have hu4 := hu.contDiffAt (hU.mem_nhds hx)
  have hdetAt : (fun y => (complexHessian realDirections imagDirections u y).det) =ᶠ[𝓝 x]
      (fun _ => (1 : ℂ)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hdet y hy
  rw [classicalDivergence_matMulE_gradient
    (fun i j => (complexLinearizedCoeff_contDiffAt hu4 hdetAt i j).differentiableAt
      (by norm_num)) hv (complexLinearizedCoeff_divergence (hu4.of_le (by norm_num)) hdetAt),
    ← Equiv.sum_comp finSumFinEquiv]
  simp_rw [← Equiv.sum_comp finSumFinEquiv]
  simp only [complexLinearizedCoeff, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, euclideanDirection_sum]
  exact schurPair_realHessian_nonpos hU hu realDirections imagDirections hdet hx hA ξ

end CHS.Analysis
