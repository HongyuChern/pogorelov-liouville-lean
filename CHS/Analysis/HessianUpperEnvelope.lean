import CHS.Analysis.DirectionalSupersolutions
import CHS.Analysis.CommonMaximum

/-!
# A Loewner upper envelope in the actual real Hessian range closure

Every real directional Hessian is a subsolution for the same global
coefficient field.  Compactness and the finite weak-Harnack approximation
therefore produce one matrix in the closure of the actual Hessian range
which dominates every actual Hessian.
-/

set_option autoImplicit false
noncomputable section

open DeGiorgi Set Matrix
open scoped BigOperators ComplexOrder ContDiff Matrix.Norms.Elementwise

namespace CHS.Analysis

open CHS.Calculus

variable {n : ℕ}
local notation "E" => AmbientSpace (n + n)
local notation "J" => Fin n ⊕ Fin n

theorem bounded_positive_complexMongeAmpere_upper_envelope
    (hn : 2 ≤ n) {u : E → ℝ} (hu : ContDiff ℝ 4 u)
    (hdet : ∀ x, (complexHessian realDirections imagDirections u x).det = 1)
    (hA : ∀ x, (complexHessian realDirections imagDirections u x).PosDef)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, ∀ i j, |euclideanHessian u x i j| ≤ C) :
    ∃ Q ∈ closure (range (realBlockHessian realDirections imagDirections u)),
      ∀ x, (Q - realBlockHessian realDirections imagDirections u x).PosSemidef := by
  letI : NeZero (n + n) := ⟨by omega⟩
  have hd : 2 < ((n + n : ℕ) : ℝ) := by exact_mod_cast (show 2 < n + n by omega)
  let H := realBlockHessian realDirections imagDirections u
  have hH : Continuous H := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact continuous_iff_continuousAt.mpr fun x =>
      (realHessian_contDiffAt_two hu.contDiffAt
        (Sum.elim realDirections imagDirections i) (Sum.elim realDirections imagDirections j)).continuousAt
  have hnorm (x : E) : ‖H x‖ ≤ C := by
    rw [Matrix.norm_le_iff hC]
    intro i j
    have h := hbound x (finSumFinEquiv i) (finSumFinEquiv j)
    simpa only [H, realBlockHessian, blockDirection_eq_single, euclideanHessian, Real.norm_eq_abs] using h
  have hrange : range H ⊆ Metric.closedBall 0 C := by
    rintro _ ⟨x, rfl⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm x
  have hcompact : IsCompact (closure (range H)) :=
    (isCompact_closedBall 0 C).of_isClosed_subset isClosed_closure
      (closure_minimal hrange Metric.isClosed_closedBall)
  obtain ⟨c, hc, B, hB⟩ := global_complexLinearizedCoeff_of_hessian_bound hu hdet hA hbound
  let f : (J → ℝ) → Matrix J J ℝ → ℝ := fun z A => z ⬝ᵥ A.mulVec z
  have hf (z : J → ℝ) : Continuous (f z) := by
    unfold f dotProduct Matrix.mulVec
    fun_prop
  have hsuper (z : J → ℝ) (M R : ℝ) (_hRpos : 0 < R) :
      IsSupersolution (B.restrict (subset_univ (Metric.ball (0 : E) R))).1
        (fun x => M - f z (H x)) := by
    let e : E := ∑ i, z i • Sum.elim realDirections imagDirections i
    have heq : (fun x => M - f z (H x)) = fun x => M - realHessian u x e e := by
      funext x
      rw [realHessian_sum_directions_quadratic
        (hu.of_le (by norm_num)).contDiffAt realDirections imagDirections]
    rw [heq]
    exact directionalHessian_deficit_supersolution_on_ball hu hdet hA hc B hB e M 0 R
  obtain ⟨Q, hQ, hupper⟩ := exists_common_maximum_in_range_closure hd B H hH hcompact f hf hsuper
  have hHerm (x : E) : (H x).IsHermitian :=
    realBlockHessian_isHermitian (hu.of_le (by norm_num)).contDiffAt realDirections imagDirections
  have hQherm : Q.IsHermitian :=
    closure_minimal (by rintro _ ⟨x, rfl⟩; exact hHerm x)
      (isClosed_eq continuous_id.matrix_conjTranspose continuous_id) hQ
  refine ⟨Q, hQ, ?_⟩
  intro x
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hQherm.sub (hHerm x))
  intro z
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub]
  exact sub_nonneg.mpr (hupper z x)

theorem entire_convex_realHessian_upper_envelope
    (hn : 2 ≤ n) {u : E → ℝ} (hu : ContDiff ℝ 4 u)
    (hdet : ∀ x, (complexHessian realDirections imagDirections u x).det = 1)
    (hR : ∀ x, (realBlockHessian realDirections imagDirections u x).PosSemidef) :
    ∃ Q ∈ closure (range (realBlockHessian realDirections imagDirections u)),
      ∀ x, (Q - realBlockHessian realDirections imagDirections u x).PosSemidef := by
  obtain ⟨C, hC, hbound, _, _⟩ := CHS.entire_convex_hessian_bound hn hu hdet hR
  exact bounded_positive_complexMongeAmpere_upper_envelope hn hu hdet
    (fun x => complexHessian_posDef_of_realBlockHessian (hu.of_le (by norm_num)).contDiffAt
      realDirections imagDirections (hR x) (hdet x)) hC hbound

end CHS.Analysis
