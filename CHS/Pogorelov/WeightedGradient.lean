import CHS.Algebra.TraceFreeScaled

/-!
# Finite weighted inequalities for the gradient of the Pogorelov trace
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace CHS.Pogorelov

open CHS.Algebra

variable {m n : ℕ}

/-- Weighted Cauchy–Schwarz for a finite family of complex vectors. -/
theorem weighted_vecSq_sum_le (weight : Fin m → ℝ) (hweight : ∀ p, 0 ≤ weight p)
    (v : Fin m → CVector n) :
    vecSq (fun i => ∑ p, (weight p : ℂ) * v p i) ≤
      (∑ p, weight p) * (∑ p, weight p * vecSq (v p)) := by
  have hcoord (i : Fin n) :
      Complex.normSq (∑ p, (weight p : ℂ) * v p i) ≤
        (∑ p, weight p) * (∑ p, weight p * Complex.normSq (v p i)) := by
    let z (p : Fin m) := (Real.sqrt (weight p) : ℂ) * v p i
    let w (p : Fin m) := (Real.sqrt (weight p) : ℂ)
    have h := dot_sq_le z w
    have hdot : dot z w = ∑ p, (weight p : ℂ) * v p i := by
      unfold dot
      apply Finset.sum_congr rfl
      intro p _
      simp only [z, w, Complex.star_def, Complex.conj_ofReal]
      have hsq : (Real.sqrt (weight p) : ℂ) * (Real.sqrt (weight p) : ℂ) = (weight p : ℂ) := by
        exact_mod_cast (Real.mul_self_sqrt (hweight p))
      rw [mul_right_comm, hsq]
    have hz : vecSq z = ∑ p, weight p * Complex.normSq (v p i) := by
      unfold vecSq
      apply Finset.sum_congr rfl
      intro p _
      dsimp only [z]
      rw [complex_sq_real_mul, Real.sq_sqrt (hweight p)]
    have hw : vecSq w = ∑ p, weight p := by
      unfold vecSq
      apply Finset.sum_congr rfl
      intro p _
      dsimp only [w]
      rw [Complex.normSq_ofReal, Real.mul_self_sqrt (hweight p)]
    rw [hdot, hz, hw, mul_comm] at h
    exact h
  unfold vecSq
  calc
    _ ≤ ∑ i, (∑ p, weight p) * (∑ p, weight p * Complex.normSq (v p i)) :=
      Finset.sum_le_sum (fun i _ => hcoord i)
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp_rw [← Finset.mul_sum]


/-- The trace-free part of the gradient estimate, in a diagonal frame. -/
theorem tracefree_weighted_gradient_bound {n : ℕ} (hn : 2 ≤ n)
    (c κ : ℝ) (hc : 0 ≤ c) (hκ : 0 ≤ κ)
    (weight : Fin n → ℝ) (hweight : ∀ p, 0 ≤ weight p)
    (C : Fin n → CMatrix n) (htrace : ∀ p, tr (C p) = 0)
    (e k : Fin n → CVector n) (he : ∀ p, vecSq (e p) = 1)
    (hk : ∀ p, vecSq (k p) ≤ κ) :
    vecSq (fun i => ∑ p, (weight p : ℂ) * action c (C p) (e p) (k p) i) ≤
      (c ^ 2 + ((n : ℝ) - 1) * κ) * (∑ p, weight p) *
        (∑ p, weight p * hsSq (C p)) := by
  let d := c ^ 2 + ((n : ℝ) - 1) * κ
  have hsum : (∑ p, weight p * vecSq (action c (C p) (e p) (k p))) ≤
      ∑ p, weight p * (d * hsSq (C p)) := by
    exact Finset.sum_le_sum fun p _ =>
      mul_le_mul_of_nonneg_left
        (CHS.Algebra.tracefree_matrix_inequality_scaled hn c κ hc hκ (C p) (htrace p) (e p) (k p)
          (he p) (hk p)) (hweight p)
  calc
    _ ≤ (∑ p, weight p) * (∑ p, weight p * vecSq (action c (C p) (e p) (k p))) :=
      weighted_vecSq_sum_le weight hweight _
    _ ≤ (∑ p, weight p) * (∑ p, weight p * (d * hsSq (C p))) :=
      mul_le_mul_of_nonneg_left hsum (Finset.sum_nonneg fun p _ => hweight p)
    _ = _ := by
      have heq : (∑ p, weight p * (d * hsSq (C p))) =
          d * (∑ p, weight p * hsSq (C p)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        ring
      rw [heq]
      change _ = d * (∑ p, weight p) * (∑ p, weight p * hsSq (C p))
      ring


/-- The two summands in (2.24), expressed using square roots of the
eigenvalues and the third derivative tensor in the diagonal frame. -/
theorem diagonal_trace_gradient_expansion
    (r : Fin n → ℝ) (hr : ∀ p, 0 < r p)
    (T : Fin n → CMatrix n) (hT : ∀ p i q, T p i q = T i p q)
    (B : CMatrix n) (c : ℝ) (i : Fin n) :
    let C (p : Fin n) : CMatrix n :=
      fun j q => T p j q / ((r p : ℂ) * (r j : ℂ) * (r q : ℂ))
    let e (p : Fin n) : CVector n := fun j => if j = p then 1 else 0
    let k (p : Fin n) : CVector n := fun j => B p j / ((r p : ℂ) * (r j : ℂ))
    (∑ p, ((r p : ℂ) ^ 2) * action c (C p) (e p) (k p) i) =
      ((c : ℂ) * (∑ p, T i p p) +
        ∑ p, ∑ j, B p j * star (T p j i) / (r j : ℂ) ^ 2) / (r i : ℂ) := by
  let C (p : Fin n) : CMatrix n :=
    fun j q => T p j q / ((r p : ℂ) * (r j : ℂ) * (r q : ℂ))
  let e (p : Fin n) : CVector n := fun j => if j = p then 1 else 0
  let k (p : Fin n) : CVector n := fun j => B p j / ((r p : ℂ) * (r j : ℂ))
  change (∑ p, ((r p : ℂ) ^ 2) * action c (C p) (e p) (k p) i) = _
  rw [add_div, Finset.mul_sum, Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  have hm : mv (C p) (e p) i = C p i p := by
    simp [mv, e, mul_ite]
  have hne (j : Fin n) : (r j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hr j).ne'
  unfold action adjmv
  rw [hm, mul_add]
  congr 1
  · dsimp only [C]
    rw [hT p i p]
    field_simp [hne]
    <;> ring
  · rw [Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [C, k]
    simp only [Complex.star_def, map_div₀, map_mul, Complex.conj_ofReal]
    field_simp [hne]
    <;> ring


/-- Equation (2.25) after the mixed Hessian has been diagonalized and
its positive eigenvalues written as squares. -/
theorem diagonal_trace_gradient_bound {n : ℕ} (hn : 2 ≤ n)
    (r : Fin n → ℝ) (hr : ∀ p, 0 < r p)
    (T : Fin n → CMatrix n) (hT : ∀ p i q, T p i q = T i p q)
    (hDet : ∀ p, (∑ j, T p j j / (r j : ℂ) ^ 2) = 0)
    (B : CMatrix n) (c κ : ℝ) (hc : 0 ≤ c) (hκ : 0 ≤ κ)
    (hB : ∀ p, (∑ j, Complex.normSq (B p j / ((r p : ℂ) * (r j : ℂ)))) ≤ κ) :
    let C (p : Fin n) : CMatrix n :=
      fun j q => T p j q / ((r p : ℂ) * (r j : ℂ) * (r q : ℂ))
    vecSq (fun i => ((c : ℂ) * (∑ p, T i p p) +
      ∑ p, ∑ j, B p j * star (T p j i) / (r j : ℂ) ^ 2) / (r i : ℂ)) ≤
      (c ^ 2 + ((n : ℝ) - 1) * κ) * (∑ p, r p ^ 2) *
        (∑ p, r p ^ 2 * hsSq (C p)) := by
  let C (p : Fin n) : CMatrix n :=
    fun j q => T p j q / ((r p : ℂ) * (r j : ℂ) * (r q : ℂ))
  let e (p : Fin n) : CVector n := fun j => if j = p then 1 else 0
  let k (p : Fin n) : CVector n := fun j => B p j / ((r p : ℂ) * (r j : ℂ))
  have htrace (p : Fin n) : tr (C p) = 0 := by
    have heq : tr (C p) = (∑ j, T p j j / (r j : ℂ) ^ 2) / (r p : ℂ) := by
      unfold tr
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      dsimp only [C]
      rw [div_div, pow_two]
      congr 1
      ring
    rw [heq, hDet p, zero_div]
  have he (p : Fin n) : vecSq (e p) = 1 := by
    simp [vecSq, e, apply_ite Complex.normSq]
  have hsum (i : Fin n) :
      (∑ p, (↑(r p ^ 2) : ℂ) * action c (C p) (e p) (k p) i) =
        ((c : ℂ) * (∑ p, T i p p) +
          ∑ p, ∑ j, B p j * star (T p j i) / (r j : ℂ) ^ 2) / (r i : ℂ) := by
    simpa only [Complex.ofReal_pow] using diagonal_trace_gradient_expansion r hr T hT B c i
  change _ ≤ (c ^ 2 + ((n : ℝ) - 1) * κ) * (∑ p, r p ^ 2) * (∑ p, r p ^ 2 * hsSq (C p))
  simp_rw [← hsum]
  exact tracefree_weighted_gradient_bound hn c κ hc hκ (fun p => r p ^ 2)
    (fun p => sq_nonneg (r p)) C htrace e k he hB

end CHS.Pogorelov
