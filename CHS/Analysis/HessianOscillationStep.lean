import CHS.Algebra.FiniteConeDirections
import CHS.Analysis.FiniteOscillation
import CHS.Analysis.CMAEllipticityFamily
import CHS.Analysis.LocalDirectionalSupersolutions

/-!
# Uniform one-step oscillation decay for actual complex Monge--Ampere Hessians

The finite directions, comparison constant and contraction factor are chosen
from n and the entrywise Hessian bound before choosing the potential, domain,
center or radius. The equation and positive branch are only local hypotheses.
The global C4 representative in this intermediate interface will be removed
by the existing cutoff-representative theorem in the local Holder endpoint.
-/

set_option autoImplicit false
noncomputable section

open DeGiorgi Set Metric Matrix
open scoped BigOperators ComplexOrder ContDiff Matrix.Norms.Elementwise

namespace CHS.Analysis

open CHS.Calculus CHS.Algebra

variable {n : ℕ}
local notation "E" => AmbientSpace (n + n)
local notation "J" => Fin n ⊕ Fin n
local notation "V" => Matrix J J ℝ
local notation "W" => Matrix (Fin n) (Fin n) ℂ

def hessianObservable (u : E → ℝ) (z : J → ℝ) (x : E) : ℝ :=
  realMatrixQuadratic (realBlockHessian realDirections imagDirections u x) z

def hessianDirectionalOscillation (t : Finset (J → ℝ)) (u : E → ℝ) (x₀ : E) (R : ℝ) : ℝ :=
  ∑ z : t, compactOsc (hessianObservable u z.1) (closedBall x₀ R)

theorem hessianObservable_eq_directional {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (z : J → ℝ) :
    hessianObservable u z x = realHessian u x
      (∑ i, z i • Sum.elim realDirections imagDirections i)
      (∑ i, z i • Sum.elim realDirections imagDirections i) :=
  (realHessian_sum_directions_quadratic hu realDirections imagDirections z).symm

theorem hessianObservable_continuous {u : E → ℝ} (hu : ContDiff ℝ 4 u) (z : J → ℝ) :
    Continuous (hessianObservable u z) := by
  have heq : hessianObservable u z = fun x => realHessian u x
      (∑ i, z i • Sum.elim realDirections imagDirections i)
      (∑ i, z i • Sum.elim realDirections imagDirections i) :=
    funext fun x => hessianObservable_eq_directional (hu.of_le (by norm_num)).contDiffAt z
  rw [heq]
  exact continuous_iff_continuousAt.mpr fun x => (realHessian_contDiffAt_two hu.contDiffAt _ _).continuousAt

theorem hessian_norm_sub_le_deficits
    {S : Set W} {t : Finset (J → ℝ)} {C : ℝ} (hC : 0 ≤ C)
    (hdetect : ∀ A ∈ S, ∀ H : V, H.IsHermitian →
      0 ≤ (A * complexProjection H).trace.re →
      ‖H‖ ≤ C * ∑ z ∈ t, max (realMatrixQuadratic H z) 0)
    {K : Set E} {u : E → ℝ} (hu : ContDiff ℝ 2 u)
    (hA : ∀ x ∈ K, (complexHessian realDirections imagDirections u x).PosDef)
    (hdet : ∀ x ∈ K, (complexHessian realDirections imagDirections u x).det = 1)
    (hweight : ∀ x ∈ K, (complexHessian realDirections imagDirections u x)⁻¹ ∈ S)
    {M : (J → ℝ) → ℝ} (hM : ∀ z ∈ t, ∀ x ∈ K, hessianObservable u z x ≤ M z)
    {x y : E} (hx : x ∈ K) (hy : y ∈ K) :
    ‖realBlockHessian realDirections imagDirections u x -
        realBlockHessian realDirections imagDirections u y‖ ≤
      C * ∑ z : t, (M z.1 - hessianObservable u z.1 y) := by
  rw [Finset.sum_coe_sort t (fun z => M z - hessianObservable u z y)]
  apply norm_sub_le_directional_deficits hC hdetect
    (fun x _ => realBlockHessian_isHermitian hu.contDiffAt realDirections imagDirections)
    (fun x hx => ?_) (fun x hx => ?_) (fun x hx => ?_) hM hx hy
  · rw [complexProjection_realBlockHessian hu.contDiffAt]
    exact hA x hx
  · rw [complexProjection_realBlockHessian hu.contDiffAt]
    exact hdet x hx
  · rw [complexProjection_realBlockHessian hu.contDiffAt]
    exact hweight x hx

theorem exists_uniform_hessian_oscillation_step (hn : 2 ≤ n) (M : ℝ) :
    ∃ t : Finset (J → ℝ), ∃ D : ℝ, 0 < D ∧ ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧
      ∀ U : Set E, IsOpen U → ∀ u : E → ℝ, ContDiff ℝ 4 u →
      (∀ x ∈ U, (complexHessian realDirections imagDirections u x).det = 1) →
      (∀ x ∈ U, (complexHessian realDirections imagDirections u x).PosDef) →
      (∀ x ∈ U, ∀ i j, |euclideanHessian u x i j| ≤ M) →
      ∀ x₀ : E, ∀ R : ℝ, 0 < R → closedBall x₀ (2 * R) ⊆ U →
        hessianDirectionalOscillation t u x₀ (R / 8) ≤ θ * hessianDirectionalOscillation t u x₀ R ∧
        ∀ x ∈ closedBall x₀ R, ∀ y ∈ closedBall x₀ R,
          ‖realBlockHessian realDirections imagDirections u x -
            realBlockHessian realDirections imagDirections u y‖ ≤ D * hessianDirectionalOscillation t u x₀ R := by
  classical
  letI : NeZero (n + n) := ⟨by omega⟩
  have hd : 2 < ((n + n : ℕ) : ℝ) := by exact_mod_cast (show 2 < n + n by omega)
  obtain ⟨t, D, hD, hdetect⟩ := exists_finite_directions_detecting_elliptic_half_cone
    (inverseComplexDetOneFamily_compact (n := n) M)
    (fun _ h => inverseComplexDetOneFamily_posDef h)
  let L : ℝ := 1 + ∑ z ∈ t, realMatrixQuadraticWeight z
  have hL : 0 < L := by
    have hsum : 0 ≤ ∑ z ∈ t, realMatrixQuadraticWeight z :=
      Finset.sum_nonneg fun z _ => sq_nonneg _
    dsimp only [L]
    linarith
  have hzL (z : t) : realMatrixQuadraticWeight z.1 ≤ L := by
    have h := Finset.single_le_sum (fun y _ => sq_nonneg (∑ j, |y j|)) z.2
    change realMatrixQuadraticWeight z.1 ≤ ∑ y ∈ t, realMatrixQuadraticWeight y at h
    dsimp only [L]
    linarith
  obtain ⟨c, hc, Λ, hΛ, hcoeff⟩ := exists_uniform_local_complex_coefficients (n := n) M
  let θ := finiteOscillationFactor (n + n) hd Λ (L * D) (Fintype.card t)
  have hθ := finiteOscillationFactor_pos_lt_one hd Λ (L * D) (Fintype.card t)
  refine ⟨t, D, hD, θ, hθ.1, hθ.2, ?_⟩
  intro U hU u hu hdet hA hM x₀ R hR hclosed
  obtain ⟨B, hBΛ, hB⟩ := hcoeff U hU u hu.contDiffOn hdet hA hM
  have hKU : closedBall x₀ R ⊆ U := (closedBall_subset_closedBall (by linarith)).trans hclosed
  have hweight (x : E) (hx : x ∈ U) :
      (complexHessian realDirections imagDirections u x)⁻¹ ∈ inverseComplexDetOneFamily n M :=
    mem_image_of_mem _ (complexHessian_mem_complexDetOneFamily
      (hu.of_le (by norm_num)).contDiffAt (hA x hx) (hdet x hx) (hM x hx))
  let F (z : t) := hessianObservable u z.1
  have hF (z : t) : Continuous (F z) := hessianObservable_continuous hu z.1
  let N (z : J → ℝ) := compactSup (hessianObservable u z) (closedBall x₀ R)
  have hupper (z : J → ℝ) (x : E) (hx : x ∈ closedBall x₀ R) : hessianObservable u z x ≤ N z :=
    le_compactSup (isCompact_closedBall _ _) (hessianObservable_continuous hu z).continuousOn hx
  have hnorm (x : E) (hx : x ∈ closedBall x₀ R) (y : E) (hy : y ∈ closedBall x₀ R) :
      ‖realBlockHessian realDirections imagDirections u x -
          realBlockHessian realDirections imagDirections u y‖ ≤
        D * ∑ z : t, (N z.1 - F z y) :=
    hessian_norm_sub_le_deficits hD.le hdetect (hu.of_le (by norm_num))
      (fun a ha => hA a (hKU ha)) (fun a ha => hdet a (hKU ha))
      (fun a ha => hweight a (hKU ha)) (fun z _ => hupper z) hx hy
  constructor
  · have hsub : ball x₀ R ⊆ U := ball_subset_closedBall.trans hKU
    let A := B.restrict hsub
    have hsuper (z : t) : IsSupersolution A.1 (fun x => N z.1 - F z x) := by
      let e : E := ∑ i, z.1 i • Sum.elim realDirections imagDirections i
      have heq : (fun x => N z.1 - F z x) = fun x => N z.1 - realHessian u x e e := by
        funext x
        rw [show F z x = hessianObservable u z.1 x from rfl,
          hessianObservable_eq_directional (hu.of_le (by norm_num)).contDiffAt]
      rw [heq]
      exact directionalHessian_deficit_local_supersolution_on_ball hU hu.contDiffOn
        hdet hA hc B hB e (N z.1) hR (by linarith : R < 2 * R) hclosed
    have hpair (z : t) (x : E) (hx : x ∈ closedBall x₀ R) (y : E) (hy : y ∈ closedBall x₀ R) :
        |F z x - F z y| ≤ (L * D) * ∑ j : t, (N j.1 - F j y) := by
      have habs := abs_realMatrixQuadratic_le
        (realBlockHessian realDirections imagDirections u x -
          realBlockHessian realDirections imagDirections u y) z.1
      rw [realMatrixQuadratic_sub] at habs
      calc
        _ ≤ realMatrixQuadraticWeight z.1 *
            ‖realBlockHessian realDirections imagDirections u x -
              realBlockHessian realDirections imagDirections u y‖ := habs
        _ ≤ L * ‖realBlockHessian realDirections imagDirections u x -
              realBlockHessian realDirections imagDirections u y‖ :=
          mul_le_mul_of_nonneg_right (hzL z) (norm_nonneg _)
        _ ≤ L * (D * ∑ j : t, (N j.1 - F j y)) := mul_le_mul_of_nonneg_left (hnorm x hx y hy) hL.le
        _ = _ := by ring
    have h := finite_supersolution_oscillation_contraction hd hR (mul_nonneg hL.le hD.le) A F hF hsuper hpair
    have hAΛ : A.1.Λ = Λ := hBΛ
    rw [hAΛ] at h
    exact h
  · intro x hx y hy
    apply (hnorm x hx y hy).trans
    apply mul_le_mul_of_nonneg_left _ hD.le
    apply Finset.sum_le_sum
    intro z _
    exact sub_le_sub_left
      (compactInf_le (isCompact_closedBall _ _) (hF z).continuousOn hy) _

end CHS.Analysis
