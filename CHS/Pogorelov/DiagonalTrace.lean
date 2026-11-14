import CHS.Pogorelov.WeightedGradient
import CHS.Pogorelov.TraceEvolution
import CHS.Pogorelov.TraceField

/-!
# Diagonal formulas for the actual third derivatives of the potential
-/

set_option autoImplicit false
noncomputable section

open Matrix Filter
open scoped BigOperators ComplexOrder ContDiff Topology

namespace CHS.Pogorelov

open CHS.Calculus CHS.Algebra

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : ℕ}

private theorem inv_diagonal_squares (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) :
    (diagonal (fun i => (r i : ℂ) ^ 2))⁻¹ = diagonal (fun i => ((r i : ℂ) ^ 2)⁻¹) := by
  apply inv_eq_right_inv
  rw [diagonal_mul_diagonal']
  have h : (fun i : Fin n => (r i : ℂ) ^ 2 * ((r i : ℂ) ^ 2)⁻¹) = fun _ => 1 := by
    funext i
    exact mul_inv_cancel₀ (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (hr i).ne'))
  rw [h, diagonal_one]

theorem diagonal_det_one_third_derivatives {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 3 u x) (a b : Fin n → E)
    (hdet : (fun y => (complexHessian a b u y).det) =ᶠ[𝓝 x] fun _ => (1 : ℂ))
    (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) (hA : complexHessian a b u x = diagonal (fun i => (r i : ℂ) ^ 2)) :
    let T := fun p => matrixDZ (a p) (b p) (complexHessian a b u) x
    (∀ p i j, T p i j = T i p j) ∧
      ∀ p, (∑ j, T p j j / (r j : ℂ) ^ 2) = 0 := by
  constructor
  · exact complexHessian_row_comm hu a b
  · intro p
    have h := complexHessian_det_one_first hu a b hdet (a p) (b p)
    rw [hA, inv_diagonal_squares r hr] at h
    simp only [diagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
      if_true] at h
    simp_rw [div_eq_mul_inv, mul_comm (matrixDZ _ _ _ _ _ _)]
    exact h

theorem diagonal_scaled_pure_rows
    {A B : CMatrix n} {r : Fin n → ℝ} (hr : ∀ p, 0 < r p)
    (hA : A = diagonal (fun i => (r i : ℂ) ^ 2))
    (hB : B.conjTranspose = B.map star) {κ : ℝ}
    (hκ : (κ • A - B * (A.map star)⁻¹ * B.map star).PosSemidef) :
    ∀ p, (∑ j, Complex.normSq (B p j / ((r p : ℂ) * (r j : ℂ)))) ≤ κ := by
  intro p
  have hAstar : A.map star = A := by
    rw [hA, map_diagonal_star]
    congr 1
    ext i
    simp [star_pow, Complex.conj_ofReal]
  have hp := (Complex.nonneg_iff.mp (hκ.diag_nonneg (i := p))).1
  rw [Matrix.sub_apply, Matrix.smul_apply, Complex.sub_re] at hp
  have hP : ((B * (A.map star)⁻¹ * B.map star) p p).re =
      ∑ j, Complex.normSq (B p j) / r j ^ 2 := by
    rw [hAstar, hA, inv_diagonal_squares r hr, ← hB, Matrix.mul_apply, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_diagonal, Matrix.conjTranspose_apply]
    have hj : (B p j * ((r j : ℂ) ^ 2)⁻¹ * star (B p j)) =
        ((Complex.normSq (B p j) / r j ^ 2 : ℝ) : ℂ) := by
      rw [mul_right_comm, Complex.star_def, Complex.mul_conj, Complex.ofReal_div, Complex.ofReal_pow, div_eq_mul_inv]
    rw [hj, Complex.ofReal_re]
  have hpos : 0 < r p ^ 2 := sq_pos_of_pos (hr p)
  rw [hP] at hp
  have hR : ((κ • A) p p).re = κ * r p ^ 2 := by
    rw [hA, Matrix.smul_apply, diagonal_apply_eq, ← Complex.ofReal_pow]
    change ((κ : ℂ) * (↑(r p ^ 2) : ℂ)).re = _
    rw [← Complex.ofReal_mul, Complex.ofReal_re]
  have hp' : (∑ j, Complex.normSq (B p j) / r j ^ 2) ≤ κ * r p ^ 2 := by
    apply sub_nonneg.mp
    simpa only [← Matrix.smul_apply, hR] using hp
  calc
    _ = (∑ j, Complex.normSq (B p j) / r j ^ 2) / r p ^ 2 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      rw [Complex.normSq_div, Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_ofReal]
      rw [div_div]
      congr 1
      ring
    _ ≤ κ := (div_le_iff₀ hpos).mpr hp'


theorem matrixDZ_conjugate_pure_entries {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 3 u U) (a b : Fin n → E)
    {x : E} (hx : x ∈ U) (i j p : Fin n) :
    matrixDZ (a i) (b i) (fun y => (pureHessian a b u y).map star) x j p =
      star (matrixDZ (a p) (b p) (complexHessian a b u) x j i) := by
  have hc : ContDiffOn ℝ 3 (fun y => (u y : ℂ)) U :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hu
  have hAt := hc.contDiffAt (hU.mem_nhds hx)
  rw [matrixDZ_map_star, Matrix.map_apply]
  congr 1
  change dz (a i) (-b i) (dz (a j) (b j) (dz (a p) (b p) (fun y => (u y : ℂ)))) x =
    dz (a p) (b p) (dz (a j) (b j) (dz (a i) (-b i) (fun y => (u y : ℂ)))) x
  rw [third_inner_comm_on hU hc (a i) (-b i) (a j) (b j) (a p) (b p) hx,
    third_outer_comm_at hAt (a i) (-b i) (a p) (b p) (a j) (b j),
    third_inner_comm_on hU hc (a p) (b p) (a i) (-b i) (a j) (b j) hx]


theorem diagonal_pogorelov_gradient_bound {u : E → ℝ} {U : Set E}
    (hn : 2 ≤ n) (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : Fin n → E)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = 1)
    {x : E} (hx : x ∈ U) (r : Fin n → ℝ) (hr : ∀ p, 0 < r p)
    (hA : complexHessian a b u x = diagonal (fun i => (r i : ℂ) ^ 2))
    (c κ : ℝ) (hc : 0 ≤ c) (hκ : 0 ≤ κ)
    (hmat : (κ • complexHessian a b u x -
      pureHessian a b u x * ((complexHessian a b u x).map star)⁻¹ *
        (pureHessian a b u x).map star).PosSemidef) :
    let A := complexHessian a b u
    let B := pureHessian a b u
    let W := (A x)⁻¹
    let T := fun p => matrixDZ (a p) (b p) A x
    let C (p : Fin n) : CMatrix n :=
      fun j q => T p j q / ((r p : ℂ) * (r j : ℂ) * (r q : ℂ))
    let v (i : Fin n) := (c : ℂ) * dz (a i) (b i) (fun y => (A y).trace) x +
      (B x * ((A x).map star)⁻¹ * matrixDZ (a i) (b i) (fun y => (B y).map star) x).trace
    (star v ⬝ᵥ W.mulVec v).re ≤
      (c ^ 2 + ((n : ℝ) - 1) * κ) * (A x).trace.re * (∑ p, r p ^ 2 * hsSq (C p)) := by
  let A := complexHessian a b u
  let B := pureHessian a b u
  let W := (A x)⁻¹
  let T := fun p => matrixDZ (a p) (b p) A x
  let C (p : Fin n) : CMatrix n :=
    fun j q => T p j q / ((r p : ℂ) * (r j : ℂ) * (r q : ℂ))
  let v (i : Fin n) := (c : ℂ) * dz (a i) (b i) (fun y => (A y).trace) x +
    (B x * ((A x).map star)⁻¹ * matrixDZ (a i) (b i) (fun y => (B y).map star) x).trace
  have hu4 := hu.contDiffAt (hU.mem_nhds hx)
  have hu3 : ContDiffAt ℝ 3 u x := hu4.of_le (by norm_num)
  have hd : (fun y => (A y).det) =ᶠ[𝓝 x] fun _ => (1 : ℂ) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hdet y hy
  obtain ⟨hT, hTrace⟩ := diagonal_det_one_third_derivatives hu3 a b hd r hr hA
  have hRows := diagonal_scaled_pure_rows hr hA
    (pureHessian_conjTranspose (hu4.of_le (by norm_num)) a b) hmat
  have hAstar : (A x).map star = A x := by
    change (complexHessian a b u x).map star = complexHessian a b u x
    rw [hA, map_diagonal_star]
    congr 1
    ext j
    simp [star_pow, Complex.conj_ofReal]
  have hW : W = diagonal (fun i => ((r i : ℂ) ^ 2)⁻¹) := by
    change (complexHessian a b u x)⁻¹ = _
    rw [hA, inv_diagonal_squares r hr]
  have hv (i : Fin n) : v i =
      (c : ℂ) * (∑ p, T i p p) + ∑ p, ∑ j, B x p j * star (T p j i) / (r j : ℂ) ^ 2 := by
    unfold v
    rw [dz_trace (complexHessian_differentiableAt hu3 a b)]
    congr 1
    rw [hAstar]
    change (B x * W * matrixDZ (a i) (b i) (fun y => (B y).map star) x).trace = _
    rw [hW]
    unfold Matrix.trace
    apply Finset.sum_congr rfl
    intro p _
    rw [Matrix.diag_apply, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_diagonal, matrixDZ_conjugate_pure_entries hU (hu.of_le (by norm_num)) a b hx]
    change _ = B x p j * star (matrixDZ (a p) (b p) A x j i) / (r j : ℂ) ^ 2
    rw [div_eq_mul_inv, mul_right_comm]
  have hquad : (star v ⬝ᵥ W.mulVec v).re =
      vecSq (fun i => v i / (r i : ℂ)) := by
    rw [hW]
    simp only [dotProduct, Complex.re_sum, vecSq, Pi.star_apply, mulVec_diagonal]
    apply Finset.sum_congr rfl
    intro i _
    rw [← mul_left_comm, Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
    rw [Complex.normSq_div, Complex.normSq_ofReal, ← Complex.ofReal_pow, ← Complex.ofReal_inv,
      ← Complex.ofReal_mul, Complex.ofReal_re, div_eq_mul_inv, pow_two]
    exact mul_comm _ _
  have htrA : (A x).trace.re = ∑ p, r p ^ 2 := by
    change (complexHessian a b u x).trace.re = _
    rw [hA, Matrix.trace_diagonal, Complex.re_sum]
    simp only [← Complex.ofReal_pow, Complex.ofReal_re]
  change (star v ⬝ᵥ W.mulVec v).re ≤
    (c ^ 2 + ((n : ℝ) - 1) * κ) * (A x).trace.re * (∑ p, r p ^ 2 * hsSq (C p))
  rw [hquad, htrA]
  simp_rw [hv]
  exact diagonal_trace_gradient_bound hn r hr T hT hTrace (B x) c κ hc hκ hRows


theorem diagonal_trace_energy_eq (r : Fin n → ℝ) (hr : ∀ p, 0 < r p)
    (T : Fin n → CMatrix n) (hT : ∀ p j q, T p j q = T j p q) :
    let W := diagonal (fun i => ((r i : ℂ) ^ 2)⁻¹)
    let C (p : Fin n) : CMatrix n :=
      fun j q => T p j q / ((r p : ℂ) * (r j : ℂ) * (r q : ℂ))
    (CHS.WeightedSquares.matrixSquare W W T).trace.re =
      ∑ p, r p ^ 2 * hsSq (C p) := by
  let d (i : Fin n) := ((r i : ℂ) ^ 2)⁻¹
  let W := diagonal d
  let C (p : Fin n) : CMatrix n :=
    fun j q => T p j q / ((r p : ℂ) * (r j : ℂ) * (r q : ℂ))
  have hsum : CHS.WeightedSquares.matrixSquare W W T =
      ∑ p, d p • (T p * W * (T p).conjTranspose) := by
    unfold CHS.WeightedSquares.matrixSquare
    apply Finset.sum_congr rfl
    intro p _
    simp only [W, Matrix.diagonal_apply, ite_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  have hentry (p j q : Fin n) :
      (d p * (T p j q * d q * star (T p j q))).re =
        (r j ^ 2) * Complex.normSq (C j p q) := by
    rw [hT p j q]
    have hprod : d p * (T j p q * d q * star (T j p q)) =
        d p * d q * (T j p q * star (T j p q)) := by ring
    rw [hprod, Complex.star_def, Complex.mul_conj]
    dsimp only [d, C]
    rw [Complex.normSq_div, Complex.normSq_mul, Complex.normSq_mul,
      Complex.normSq_ofReal, Complex.normSq_ofReal, Complex.normSq_ofReal,
      ← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_inv,
      ← Complex.ofReal_inv, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re]
    field_simp [(hr p).ne', (hr j).ne', (hr q).ne']
    <;> ring
  calc
    (CHS.WeightedSquares.matrixSquare W W T).trace.re =
        ∑ p, ∑ j, ∑ q, (d p * (T p j q * d q * star (T p j q))).re := by
      rw [hsum]
      simp only [Matrix.trace_sum, Complex.re_sum, Matrix.trace_smul, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro p _
      simp only [Matrix.trace, Matrix.diag_apply, Finset.mul_sum, Complex.re_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [Matrix.mul_apply, Finset.mul_sum, Complex.re_sum]
      apply Finset.sum_congr rfl
      intro q _
      rw [show (T p * W) j q = T p j q * d q by exact mul_diagonal d _ _ _,
        Matrix.conjTranspose_apply]
    _ = ∑ p, ∑ j, ∑ q, r j ^ 2 * Complex.normSq (C j p q) := by simp_rw [hentry]
    _ = ∑ p, r p ^ 2 * hsSq (C p) := by
      rw [Finset.sum_comm]
      simp only [hsSq, vecSq, Finset.mul_sum]


/-- Equation (2.25) for the actual potential and its trace energy, in a
frame where the mixed Hessian at the point is diagonal. -/
theorem diagonal_pogorelov_trace_gradient_energy_bound {u : E → ℝ} {U : Set E}
    (hn : 2 ≤ n) (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : Fin n → E)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = 1)
    {x : E} (hx : x ∈ U) (r : Fin n → ℝ) (hr : ∀ p, 0 < r p)
    (hA : complexHessian a b u x = diagonal (fun i => (r i : ℂ) ^ 2))
    (c κ : ℝ) (hc : 0 ≤ c) (hκ : 0 ≤ κ)
    (hmat : (κ • complexHessian a b u x -
      pureHessian a b u x * ((complexHessian a b u x).map star)⁻¹ *
        (pureHessian a b u x).map star).PosSemidef) :
    let A := complexHessian a b u
    let B := pureHessian a b u
    let W := (A x)⁻¹
    let T := fun p => matrixDZ (a p) (b p) A x
    let v (i : Fin n) := (c : ℂ) * dz (a i) (b i) (fun y => (A y).trace) x +
      (B x * ((A x).map star)⁻¹ * matrixDZ (a i) (b i) (fun y => (B y).map star) x).trace
    (star v ⬝ᵥ W.mulVec v).re ≤
      (c ^ 2 + ((n : ℝ) - 1) * κ) * (A x).trace.re *
        (CHS.WeightedSquares.matrixSquare W W T).trace.re := by
  have hu3 : ContDiffAt ℝ 3 u x := (hu.contDiffAt (hU.mem_nhds hx)).of_le (by norm_num)
  let A := complexHessian a b u
  let T := fun p => matrixDZ (a p) (b p) A x
  have hT : ∀ p i j, T p i j = T i p j := complexHessian_row_comm hu3 a b
  have heq := diagonal_trace_energy_eq r hr T hT
  have hW : (A x)⁻¹ = diagonal (fun i => ((r i : ℂ) ^ 2)⁻¹) := by
    change (complexHessian a b u x)⁻¹ = _
    rw [hA, inv_diagonal_squares r hr]
  dsimp only at heq ⊢
  have henergy : (CHS.WeightedSquares.matrixSquare (A x)⁻¹ (A x)⁻¹ T).trace.re =
      ∑ p, r p ^ 2 * hsSq (fun j q => T p j q / ((r p : ℂ) * (r j : ℂ) * (r q : ℂ))) := by
    rw [hW]
    exact heq
  have h := diagonal_pogorelov_gradient_bound hn hU hu a b hdet hx r hr hA c κ hc hκ hmat
  dsimp only at h
  dsimp only [A, T] at henergy
  rw [henergy]
  exact h


private theorem normSq_trace_weighted_product_le
    (r : Fin n → ℝ) (P B : CMatrix n) :
    let W := diagonal (fun i => ((r i : ℂ) ^ 2)⁻¹)
    Complex.normSq (P * W * B.conjTranspose).trace ≤
      (P * W * P.conjTranspose).trace.re * (B * W * B.conjTranspose).trace.re := by
  let W := diagonal (fun i => ((r i : ℂ) ^ 2)⁻¹)
  let S := diagonal (fun i => (r i : ℂ)⁻¹)
  have hS : S.conjTranspose = S := by
    dsimp only [S]
    rw [diagonal_conjTranspose]
    congr 1
    ext i
    simp [star_inv₀, Complex.conj_ofReal]
  have hSS : S * S = W := by
    dsimp only [S, W]
    rw [diagonal_mul_diagonal']
    congr 1
    funext i
    rw [pow_two, _root_.mul_inv_rev]
  have hform (X Y : CMatrix n) :
      X * W * Y.conjTranspose = (X * S) * (Y * S).conjTranspose := by
    rw [Matrix.conjTranspose_mul, hS, ← hSS]
    simp only [Matrix.mul_assoc]
  change Complex.normSq (P * W * B.conjTranspose).trace ≤
    (P * W * P.conjTranspose).trace.re * (B * W * B.conjTranspose).trace.re
  rw [hform P B, hform P P, hform B B]
  let X := P * S
  let Y := B * S
  let e := Fintype.equivFin (Fin n × Fin n)
  let vx : CVector (Fintype.card (Fin n × Fin n)) := fun i => X (e.symm i).1 (e.symm i).2
  let vy : CVector (Fintype.card (Fin n × Fin n)) := fun i => Y (e.symm i).1 (e.symm i).2
  have hdot : dot vx vy = (X * Y.conjTranspose).trace := by
    unfold dot
    rw [← Equiv.sum_comp e]
    simp only [vx, vy, Equiv.symm_apply_apply, Fintype.sum_prod_type,
      Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hnorm (M : CMatrix n) :
      vecSq (fun i => M (e.symm i).1 (e.symm i).2) = (M * M.conjTranspose).trace.re := by
    rw [← hsSq_eq_trace_product]
    unfold vecSq
    rw [← Equiv.sum_comp e]
    simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type, hsSq, vecSq]
  have hcs := dot_sq_le vx vy
  rw [hdot, hnorm X, hnorm Y] at hcs
  exact hcs

/-- A public wrapper for the inverse formula used by the diagonal estimates. -/
theorem diagonal_inverse_squares (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) :
    (diagonal (fun i => (r i : ℂ) ^ 2))⁻¹ = diagonal (fun i => ((r i : ℂ) ^ 2)⁻¹) :=
  inv_diagonal_squares r hr

/-- The inverse diagonal metric is the Euclidean square of the rescaled
covector.  This identity also holds when some `r i` vanishes. -/
theorem diagonal_covector_norm_eq (r : Fin n → ℝ) (v : Fin n → ℂ) :
    (star v ⬝ᵥ (diagonal (fun i => ((r i : ℂ) ^ 2)⁻¹)).mulVec v).re =
      vecSq (fun i => v i / (r i : ℂ)) := by
  simp only [dotProduct, Complex.re_sum, vecSq, Pi.star_apply, mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  rw [← mul_left_comm, Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
  rw [Complex.normSq_div, Complex.normSq_ofReal, ← Complex.ofReal_pow,
    ← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.ofReal_re, div_eq_mul_inv, pow_two]
  exact mul_comm _ _

theorem diagonal_matrixSquare_trace (r : Fin n → ℝ) (H : CMatrix n)
    (P : Fin n → CMatrix n) :
    (CHS.WeightedSquares.matrixSquare
      (diagonal (fun i => ((r i : ℂ) ^ 2)⁻¹)) H P).trace.re =
      ∑ p, (r p ^ 2)⁻¹ * (P p * H * (P p).conjTranspose).trace.re := by
  have hweight (i : Fin n) : ((r i : ℂ) ^ 2)⁻¹ = (((r i ^ 2)⁻¹ : ℝ) : ℂ) := by
    simp only [Complex.ofReal_inv, Complex.ofReal_pow]
  simp only [CHS.WeightedSquares.matrixSquare, Matrix.diagonal_apply, ite_smul,
    zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, Complex.re_sum,
    hweight, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]

/-- The finite-dimensional weighted trace inequality in (2.22).
It reuses the private Hilbert--Schmidt estimate above. -/
theorem diagonal_trace_product_bound (r : Fin n → ℝ)
    (P : Fin n → CMatrix n) (B : CMatrix n) :
    let W := diagonal (fun i => ((r i : ℂ) ^ 2)⁻¹)
    let v := fun p => (P p * W * B.conjTranspose).trace
    (star v ⬝ᵥ W.mulVec v).re ≤
      (B * W * B.conjTranspose).trace.re *
        (CHS.WeightedSquares.matrixSquare W W P).trace.re := by
  dsimp only
  rw [diagonal_covector_norm_eq, diagonal_matrixSquare_trace, Finset.mul_sum]
  unfold vecSq
  apply Finset.sum_le_sum
  intro p _
  rw [Complex.normSq_div, Complex.normSq_ofReal]
  have hcs := normSq_trace_weighted_product_le r (P p) B
  dsimp only at hcs
  have hweight : 0 ≤ (r p ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg _)
  have h := mul_le_mul_of_nonneg_left hcs hweight
  simpa only [div_eq_mul_inv, pow_two, mul_comm, mul_left_comm, mul_assoc] using h

/-- Equation (2.22) for the actual compensated third derivative. -/
theorem diagonal_pogorelov_correction_gradient_bound {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (a b : Fin n → E)
    (r : Fin n → ℝ) (hr : ∀ p, 0 < r p)
    (hA : complexHessian a b u x = diagonal (fun i => (r i : ℂ) ^ 2)) :
    let A := complexHessian a b u x
    let B := pureHessian a b u x
    let W := A⁻¹
    let P := fun p => compensatedHessian a b u p x
    let v := fun p => (P p * (A.map star)⁻¹ * B.map star).trace
    (star v ⬝ᵥ W.mulVec v).re ≤
      (correctionTrace a b u x).re *
        (CHS.WeightedSquares.matrixSquare W ((A.map star)⁻¹) P).trace.re := by
  have hAstar : (complexHessian a b u x).map star = complexHessian a b u x := by
    rw [hA, map_diagonal_star]
    congr 1
    ext i
    simp [star_pow, Complex.conj_ofReal]
  have hW : (complexHessian a b u x)⁻¹ = diagonal (fun i => ((r i : ℂ) ^ 2)⁻¹) := by
    rw [hA, inv_diagonal_squares r hr]
  dsimp only
  rw [correctionTrace_eq, hAstar, ← pureHessian_conjTranspose hu a b, hW]
  exact diagonal_trace_product_bound r (fun p => compensatedHessian a b u p x)
    (pureHessian a b u x)

/-- Equation (2.26) for the actual real field `S_c`, in a frame diagonalizing
the mixed Hessian at this one point.  The energies are the actual weighted
matrix squares.  The unitary-frame reduction is a separate obligation. -/
theorem diagonal_traceCombination_gradient_bound {u : E → ℝ} {U : Set E}
    (hn : 2 ≤ n) (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : Fin n → E)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = 1)
    {x : E} (hx : x ∈ U) (hpos : (complexHessian a b u x).PosDef)
    (r : Fin n → ℝ) (hr : ∀ p, 0 < r p)
    (hA : complexHessian a b u x = diagonal (fun i => (r i : ℂ) ^ 2))
    (c κ : ℝ) (hc : 0 ≤ c) (hκ : 0 ≤ κ)
    (hmat : (κ • complexHessian a b u x -
      pureHessian a b u x * ((complexHessian a b u x).map star)⁻¹ *
        (pureHessian a b u x).map star).PosSemidef) :
    let A := complexHessian a b u
    let W := (A x)⁻¹
    let Q := CHS.WeightedSquares.matrixSquare W W (fun p => matrixDZ (a p) (b p) A x)
    let F := CHS.WeightedSquares.matrixSquare W (((A x).map star)⁻¹)
      (fun p => compensatedHessian a b u p x)
    let g := fun i => dz (a i) (b i) (fun y => (traceCombination a b u c y : ℂ)) x
    (star g ⬝ᵥ W.mulVec g).re ≤
      ((c ^ 2 + ((n : ℝ) - 1) * κ) / (c + 1) * (A x).trace.re +
        (correctionTrace a b u x).re) * ((c + 1) * Q.trace.re + F.trace.re) := by
  let A := complexHessian a b u
  let B := pureHessian a b u
  let W := (A x)⁻¹
  let Q := CHS.WeightedSquares.matrixSquare W W (fun p => matrixDZ (a p) (b p) A x)
  let F := CHS.WeightedSquares.matrixSquare W (((A x).map star)⁻¹)
    (fun p => compensatedHessian a b u p x)
  let v (i : Fin n) := (c : ℂ) * dz (a i) (b i) (fun y => (A y).trace) x +
    (B x * ((A x).map star)⁻¹ *
      matrixDZ (a i) (b i) (fun y => (B y).map star) x).trace
  let w (i : Fin n) := (compensatedHessian a b u i x * ((A x).map star)⁻¹ *
    (B x).map star).trace
  have hu2 : ContDiffAt ℝ 2 u x := (hu.contDiffAt (hU.mem_nhds hx)).of_le (by norm_num)
  have hW : W = diagonal (fun i => ((r i : ℂ) ^ 2)⁻¹) := by
    change (complexHessian a b u x)⁻¹ = _
    rw [hA, inv_diagonal_squares r hr]
  have hv := diagonal_pogorelov_trace_gradient_energy_bound
    hn hU hu a b hdet hx r hr hA c κ hc hκ hmat
  change (star v ⬝ᵥ W.mulVec v).re ≤
    (c ^ 2 + ((n : ℝ) - 1) * κ) * (A x).trace.re * Q.trace.re at hv
  rw [hW, diagonal_covector_norm_eq] at hv
  have hw := diagonal_pogorelov_correction_gradient_bound hu2 a b r hr hA
  change (star w ⬝ᵥ W.mulVec w).re ≤ (correctionTrace a b u x).re * F.trace.re at hw
  rw [hW, diagonal_covector_norm_eq] at hw
  obtain ⟨hQ, hF, _, _⟩ := trace_evolution hU hu a b hdet hx hpos
  have hQ0 : 0 ≤ Q.trace.re := (Complex.nonneg_iff.mp hQ).1
  have hF0 : 0 ≤ F.trace.re := (Complex.nonneg_iff.mp hF).1
  have ha0 : 0 ≤ (A x).trace.re := (Complex.nonneg_iff.mp hpos.posSemidef.trace_nonneg).1
  have hmat' : (κ • A x - (A x - schurHessian a b u x)).PosSemidef := by
    change (κ • A x - (A x - (A x - _))).PosSemidef
    rw [sub_sub_cancel]
    exact hmat
  have hd0 : 0 ≤ (correctionTrace a b u x).re :=
    (schur_correction_trace_bounds hu2 a b hpos κ hmat').1
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hcomb := trace_vecSq_combination
    (fun i => v i / (r i : ℂ)) (fun i => w i / (r i : ℂ))
    hnR hκ hc ha0 hd0 hQ0 hF0 hv hw
  have hg (i : Fin n) :
      dz (a i) (b i) (fun y => (traceCombination a b u c y : ℂ)) x = v i + w i :=
    traceCombination_first_derivative hU hu a b hdet hx c i
  dsimp only
  change (star (fun i => dz (a i) (b i)
      (fun y => (traceCombination a b u c y : ℂ)) x) ⬝ᵥ
      W.mulVec (fun i => dz (a i) (b i)
        (fun y => (traceCombination a b u c y : ℂ)) x)).re ≤ _
  rw [hW, diagonal_covector_norm_eq]
  simpa only [hg, add_div] using hcomb

end CHS.Pogorelov
