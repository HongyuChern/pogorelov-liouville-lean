import CHS.Analysis.HessianHolderGlobal
import CHS.Calculus.HessianLocality

/-!
# Local Holder control of the actual real Hessian

No global regularity or global equation is assumed. A concrete smooth cutoff
agrees with u on B(0,3/2); locality of the actual Frechet Hessian transfers
the uniform estimate back. All constants depend only on n and M, where M
is the given entrywise Hessian bound on B(0,2).
-/

set_option autoImplicit false
noncomputable section

open DeGiorgi Set Metric Matrix
open scoped BigOperators ComplexOrder ContDiff Matrix.Norms.Elementwise

namespace CHS.Analysis

open CHS.Calculus

variable {n : ℕ}
local notation "E" => AmbientSpace (n + n)

theorem exists_local_complexMongeAmpere_hessian_holder
    (hn : 2 ≤ n) {M : ℝ} (hM : 0 ≤ M) :
    ∃ α C : ℝ, 0 < α ∧ α < 1 ∧ 0 < C ∧
      ∀ u : E → ℝ, ContDiffOn ℝ 4 u (ball (0 : E) 2) →
      (∀ x ∈ ball (0 : E) 2, (complexHessian realDirections imagDirections u x).det = 1) →
      (∀ x ∈ ball (0 : E) 2, (complexHessian realDirections imagDirections u x).PosDef) →
      (∀ x ∈ ball (0 : E) 2, ∀ i j, |euclideanHessian u x i j| ≤ M) →
      ∀ x ∈ ball (0 : E) 1, ∀ y ∈ ball (0 : E) 1,
        ‖realBlockHessian realDirections imagDirections u x -
          realBlockHessian realDirections imagDirections u y‖ ≤ C * ‖x - y‖ ^ α := by
  letI : NeZero (n + n) := ⟨by omega⟩
  obtain ⟨α, C, hα, hα1, hC, hglobal⟩ := exists_uniform_hessian_holder_global_representative hn hM
  refine ⟨α, C, hα, hα1, hC, ?_⟩
  intro u hu hdet hA hentry
  let v : E → ℝ := cutoffRepresentative 0 (3 / 2) (7 / 4) u
  have hv : ContDiff ℝ 4 v := cutoffRepresentative_contDiff (k := 4) isOpen_ball
    (by norm_num : (0 : ℝ) < 3 / 2) (by norm_num : (3 / 2 : ℝ) < 7 / 4)
    (closedBall_subset_ball (by norm_num : (7 / 4 : ℝ) < 2)) hu
  have hsmall : ball (0 : E) (3 / 2 : ℝ) ⊆ ball (0 : E) 2 := ball_subset_ball (by norm_num)
  have heq (x : E) (hx : x ∈ ball (0 : E) (3 / 2 : ℝ)) : v =ᶠ[nhds x] u :=
    cutoffRepresentative_eventuallyEq (by norm_num : (3 / 2 : ℝ) < 7 / 4) u hx
  have hH (x : E) (hx : x ∈ ball (0 : E) (3 / 2 : ℝ)) : realHessian v x = realHessian u x :=
    realHessian_eq_of_eventuallyEq (heq x hx)
  have hcomplex (x : E) (hx : x ∈ ball (0 : E) (3 / 2 : ℝ)) :
      complexHessian realDirections imagDirections v x = complexHessian realDirections imagDirections u x :=
    complexHessian_eq_of_eventuallyEq realDirections imagDirections (heq x hx)
      (hv.of_le (by norm_num)).contDiffAt
      ((hu.contDiffAt (isOpen_ball.mem_nhds (hsmall hx))).of_le (by norm_num))
  have hvdet (x : E) (hx : x ∈ ball (0 : E) (3 / 2 : ℝ)) :
      (complexHessian realDirections imagDirections v x).det = 1 := by
    rw [hcomplex x hx]
    exact hdet x (hsmall hx)
  have hvpos (x : E) (hx : x ∈ ball (0 : E) (3 / 2 : ℝ)) :
      (complexHessian realDirections imagDirections v x).PosDef := by
    rw [hcomplex x hx]
    exact hA x (hsmall hx)
  have hventry (x : E) (hx : x ∈ ball (0 : E) (3 / 2 : ℝ)) (i j : Fin (n + n)) :
      |euclideanHessian v x i j| ≤ M := by
    simp only [euclideanHessian, hH x hx]
    exact hentry x (hsmall hx) i j
  intro x hx y hy
  have hinner : ball (0 : E) 1 ⊆ ball (0 : E) (3 / 2 : ℝ) := ball_subset_ball (by norm_num)
  have h := hglobal v hv hvdet hvpos hventry x hx y hy
  rw [realBlockHessian_eq_of_eventuallyEq realDirections imagDirections (heq x (hinner hx)),
    realBlockHessian_eq_of_eventuallyEq realDirections imagDirections (heq y (hinner hy))] at h
  exact h

theorem abs_euclideanHessian_sub_le_block_norm (u : E → ℝ) (x y : E) (i j : Fin (n + n)) :
    |euclideanHessian u x i j - euclideanHessian u y i j| ≤
      ‖realBlockHessian realDirections imagDirections u x -
        realBlockHessian realDirections imagDirections u y‖ := by
  have heq (z : E) : realBlockHessian realDirections imagDirections u z
      (finSumFinEquiv.symm i) (finSumFinEquiv.symm j) = euclideanHessian u z i j :=
    congrArg (fun A => A i j) (realBlockHessian_reindex u z)
  have h := Matrix.norm_entry_le_entrywise_sup_norm
    (realBlockHessian realDirections imagDirections u x -
      realBlockHessian realDirections imagDirections u y)
    (i := finSumFinEquiv.symm i) (j := finSumFinEquiv.symm j)
  simpa only [Matrix.sub_apply, heq, Real.norm_eq_abs] using h

theorem exists_local_complexMongeAmpere_hessian_holder_entry
    (hn : 2 ≤ n) {M : ℝ} (hM : 0 ≤ M) :
    ∃ α C : ℝ, 0 < α ∧ α < 1 ∧ 0 < C ∧
      ∀ u : E → ℝ, ContDiffOn ℝ 4 u (ball (0 : E) 2) →
      (∀ x ∈ ball (0 : E) 2, (complexHessian realDirections imagDirections u x).det = 1) →
      (∀ x ∈ ball (0 : E) 2, (complexHessian realDirections imagDirections u x).PosDef) →
      (∀ x ∈ ball (0 : E) 2, ∀ i j, |euclideanHessian u x i j| ≤ M) →
      ∀ x ∈ ball (0 : E) 1, ∀ y ∈ ball (0 : E) 1, ∀ i j,
        |euclideanHessian u x i j - euclideanHessian u y i j| ≤ C * ‖x - y‖ ^ α := by
  obtain ⟨α, C, hα, hα1, hC, hbound⟩ := exists_local_complexMongeAmpere_hessian_holder hn hM
  refine ⟨α, C, hα, hα1, hC, ?_⟩
  intro u hu hdet hA hentry x hx y hy i j
  exact (abs_euclideanHessian_sub_le_block_norm u x y i j).trans
    (hbound u hu hdet hA hentry x hx y hy)

end CHS.Analysis
