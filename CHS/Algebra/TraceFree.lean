import CHS.Algebra.TraceFreeScalar
import CHS.CoreImports

/-!
# A coordinate proof of the trace-free matrix inequality (paper Lemma 2.6)

All norms below are defined by actual finite sums of complex squared norms.
The proof uses the unnormalised test vector `v = c C e + C* k` and the
scaled projection `N Q - tr(Q) I`. Thus it needs neither a choice of a
maximising unit vector nor division by its norm.

S001 STATUS: complete candidate proof text; NOT typechecked in this environment.
This status is intentional and applies also to the public theorem at the end.
No field or hypothesis is used to assume the desired matrix inequality.
-/

set_option autoImplicit false
open scoped BigOperators

namespace CHS.Algebra

variable {n : ℕ}

abbrev CVector (n : ℕ) := Fin n → ℂ
abbrev CMatrix (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

noncomputable def vecSq (v : CVector n) : ℝ := ∑ i, Complex.normSq (v i)
noncomputable def hsSq (C : CMatrix n) : ℝ := ∑ i, vecSq (C i)
noncomputable def tr (C : CMatrix n) : ℂ := ∑ i, C i i
noncomputable def dot (v w : CVector n) : ℂ := ∑ i, v i * star (w i)
noncomputable def pair (C Q : CMatrix n) : ℝ :=
  ∑ i, ∑ j, (C i j * star (Q i j)).re
noncomputable def outer (v w : CVector n) : CMatrix n := fun i j => v i * star (w j)
noncomputable def scalar (z : ℂ) : CMatrix n := fun i j => if j = i then z else 0
noncomputable def mv (C : CMatrix n) (e : CVector n) : CVector n :=
  fun i => ∑ j, C i j * e j
noncomputable def adjmv (C : CMatrix n) (k : CVector n) : CVector n :=
  fun i => ∑ j, star (C j i) * k j
noncomputable def action (c : ℝ) (C : CMatrix n) (e k : CVector n) : CVector n :=
  fun i => (c : ℂ) * mv C e i + adjmv C k i
noncomputable def testMatrix (c : ℝ) (e k v : CVector n) : CMatrix n :=
  fun i j => (c : ℂ) * outer v e i j + outer k v i j
noncomputable def projected (Q : CMatrix n) : CMatrix n :=
  fun i j => ((n : ℝ) : ℂ) * Q i j - scalar (tr Q) i j

lemma vecSq_nonneg (v : CVector n) : 0 ≤ vecSq v := by
  exact Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg (v i))

lemma hsSq_nonneg (C : CMatrix n) : 0 ≤ hsSq C := by
  exact Finset.sum_nonneg (fun i _ => vecSq_nonneg (C i))

lemma complex_sq_add (z w : ℂ) : Complex.normSq (z + w) =
    Complex.normSq z + Complex.normSq w + 2 * (z * star w).re := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

lemma complex_sq_sub (z w : ℂ) : Complex.normSq (z - w) =
    Complex.normSq z + Complex.normSq w - 2 * (z * star w).re := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

lemma complex_sq_real_mul (a : ℝ) (z : ℂ) :
    Complex.normSq ((a : ℂ) * z) = a ^ 2 * Complex.normSq z := by
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

lemma complex_pair_sq_le (z w : ℂ) :
    (z * star w).re ^ 2 ≤ Complex.normSq z * Complex.normSq w := by
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.star_def,
    Complex.conj_re, Complex.conj_im]
  nlinarith [sq_nonneg (z.re * w.im - z.im * w.re)]

lemma dot_re_self (v : CVector n) : (dot v v).re = vecSq v := by
  simp only [dot, vecSq, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Complex.mul_re, Complex.star_def, Complex.conj_re,
    Complex.conj_im, Complex.normSq_apply]
  ring

lemma dot_star_swap (v w : CVector n) : star (dot v w) = dot w v := by
  simp only [dot, star_sum, star_mul, star_star]

lemma dot_real_mul_add (a : ℝ) (v w z : CVector n) :
    dot (fun i => (a : ℂ) * v i + w i) z = (a : ℂ) * dot v z + dot w z := by
  simp only [dot, add_mul, Finset.sum_add_distrib, mul_assoc, Finset.mul_sum]

lemma dot_sq_le (v w : CVector n) : Complex.normSq (dot v w) ≤ vecSq v * vecSq w := by
  have htriangle : ‖dot v w‖ ≤ ∑ i, ‖v i‖ * ‖w i‖ := by
    simpa only [dot, norm_mul, norm_star] using
      (norm_sum_le Finset.univ (fun i => v i * star (w i)))
  have hsum0 : 0 ≤ ∑ i, ‖v i‖ * ‖w i‖ :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => ‖v i‖) (fun i => ‖w i‖)
  have hsquared : ‖dot v w‖ ^ 2 ≤ (∑ i, ‖v i‖ * ‖w i‖) ^ 2 := by
    nlinarith [norm_nonneg (dot v w)]
  simpa only [vecSq, Complex.sq_norm] using hsquared.trans hcs

lemma pair_sq_le (C Q : CMatrix n) : pair C Q ^ 2 ≤ hsSq C * hsSq Q := by
  have hrow (i : Fin n) :
      (∑ j, (C i j * star (Q i j)).re) ^ 2 ≤ vecSq (C i) * vecSq (Q i) := by
    exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (fun j _ => Complex.normSq_nonneg (C i j))
      (fun j _ => Complex.normSq_nonneg (Q i j))
      (fun j _ => complex_pair_sq_le (C i j) (Q i j))
  exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun i _ => vecSq_nonneg (C i))
    (fun i _ => vecSq_nonneg (Q i)) (fun i _ => hrow i)

lemma pair_real_left (a : ℝ) (C Q : CMatrix n) :
    pair (fun i j => (a : ℂ) * C i j) Q = a * pair C Q := by
  simp only [pair, mul_assoc, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Finset.mul_sum]

lemma pair_real_right (a : ℝ) (C Q : CMatrix n) :
    pair C (fun i j => (a : ℂ) * Q i j) = a * pair C Q := by
  have h (z w : ℂ) : (z * star ((a : ℂ) * w)).re = a * (z * star w).re := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.star_def,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  simp only [pair, h, Finset.mul_sum]

lemma pair_add_right (C Q R : CMatrix n) :
    pair C (fun i j => Q i j + R i j) = pair C Q + pair C R := by
  simp only [pair, star_add, mul_add, Complex.add_re, Finset.sum_add_distrib]

lemma pair_sub_right (C Q R : CMatrix n) :
    pair C (fun i j => Q i j - R i j) = pair C Q - pair C R := by
  simp only [pair, star_sub, mul_sub, Complex.sub_re, Finset.sum_sub_distrib]

lemma hsSq_real_mul (a : ℝ) (C : CMatrix n) :
    hsSq (fun i j => (a : ℂ) * C i j) = a ^ 2 * hsSq C := by
  simp only [hsSq, vecSq, complex_sq_real_mul, Finset.mul_sum]

lemma hsSq_add (C Q : CMatrix n) :
    hsSq (fun i j => C i j + Q i j) = hsSq C + hsSq Q + 2 * pair C Q := by
  simp only [hsSq, vecSq, pair, complex_sq_add, Finset.sum_add_distrib,
    Finset.mul_sum]

lemma hsSq_sub (C Q : CMatrix n) :
    hsSq (fun i j => C i j - Q i j) = hsSq C + hsSq Q - 2 * pair C Q := by
  simp only [hsSq, vecSq, pair, complex_sq_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.mul_sum]

lemma pair_scalar (C : CMatrix n) (a : ℂ) :
    pair C (scalar a) = (tr C * star a).re := by
  classical
  have h (i j : Fin n) :
      (C i j * star (scalar a i j)).re = if j = i then (C i j * star a).re else 0 := by
    by_cases hij : j = i <;> simp [scalar, hij]
  simp only [pair, h]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [tr, Finset.sum_mul, Complex.re_sum]

lemma hsSq_scalar (a : ℂ) : hsSq (scalar (n := n) a) = (n : ℝ) * Complex.normSq a := by
  classical
  have h (i j : Fin n) :
      Complex.normSq (scalar a i j) = if j = i then Complex.normSq a else 0 := by
    by_cases hij : j = i <;> simp [scalar, hij]
  simp [hsSq, vecSq, h]

lemma pair_self_trace (C : CMatrix n) :
    (tr C * star (tr C)).re = Complex.normSq (tr C) := by
  simp only [Complex.mul_re, Complex.star_def, Complex.conj_re,
    Complex.conj_im, Complex.normSq_apply]
  ring

lemma projected_sq (Q : CMatrix n) :
    hsSq (projected Q) = (n : ℝ) ^ 2 * hsSq Q - (n : ℝ) * Complex.normSq (tr Q) := by
  change hsSq (fun i j => ((n : ℝ) : ℂ) * Q i j - scalar (tr Q) i j) = _
  rw [hsSq_sub (fun i j => ((n : ℝ) : ℂ) * Q i j) (scalar (tr Q)),
    hsSq_real_mul, hsSq_scalar, pair_real_left,
    pair_scalar, pair_self_trace]
  ring

lemma pair_projected_of_trace_zero (C Q : CMatrix n) (htr : tr C = 0) :
    pair C (projected Q) = (n : ℝ) * pair C Q := by
  change pair C (fun i j => ((n : ℝ) : ℂ) * Q i j - scalar (tr Q) i j) = _
  rw [pair_sub_right C (fun i j => ((n : ℝ) : ℂ) * Q i j) (scalar (tr Q)),
    pair_real_right, pair_scalar, htr]
  simp

lemma hsSq_outer (v w : CVector n) : hsSq (outer v w) = vecSq v * vecSq w := by
  simp only [hsSq, vecSq, outer, Complex.normSq_mul, Complex.star_def, Complex.normSq_conj]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl (fun i _ => (Finset.mul_sum ..).symm)

lemma tr_outer (v w : CVector n) : tr (outer v w) = dot v w := rfl

lemma tr_testMatrix (c : ℝ) (e k v : CVector n) :
    tr (testMatrix c e k v) = (c : ℂ) * dot v e + dot k v := by
  simp only [tr, testMatrix, outer, dot, Finset.sum_add_distrib, Finset.mul_sum]

lemma pair_outer_outer (v e k : CVector n) :
    pair (outer v e) (outer k v) = (dot v e * star (dot k v)).re := by
  rw [dot_star_swap]
  simp only [pair, outer, dot, Finset.sum_mul, Finset.mul_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [star_mul, star_star]
  congr 1
  ring

lemma pair_outer_mv (C : CMatrix n) (v e : CVector n) :
    pair C (outer v e) = (dot (mv C e) v).re := by
  unfold pair outer dot mv
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_mul, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [star_mul, star_star]
  congr 1
  ring

lemma pair_outer_adjmv (C : CMatrix n) (k v : CVector n) :
    pair C (outer k v) = (dot (adjmv C k) v).re := by
  unfold pair outer dot adjmv
  rw [Finset.sum_comm, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_mul, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Complex.mul_re, Complex.mul_im, Complex.star_def,
    Complex.conj_re, Complex.conj_im]
  ring

lemma testMatrix_duality (c : ℝ) (C : CMatrix n) (e k v : CVector n) :
    pair C (testMatrix c e k v) = (dot (action c C e k) v).re := by
  change pair C (fun i j => (c : ℂ) * outer v e i j + outer k v i j) = _
  rw [pair_add_right C (fun i j => (c : ℂ) * outer v e i j) (outer k v),
    pair_real_right, pair_outer_mv, pair_outer_adjmv]
  unfold action
  rw [dot_real_mul_add]
  simp

lemma testMatrix_sq (c : ℝ) (e k v : CVector n) (he : vecSq e = 1) :
    hsSq (testMatrix c e k v) =
      (c ^ 2 + vecSq k) * vecSq v +
        2 * c * (dot v e * star (dot k v)).re := by
  change hsSq (fun i j => (c : ℂ) * outer v e i j + outer k v i j) = _
  rw [hsSq_add (fun i j => (c : ℂ) * outer v e i j) (outer k v),
    hsSq_real_mul, pair_real_left,
    hsSq_outer, hsSq_outer, pair_outer_outer, he]
  ring

lemma tr_testMatrix_sq (c : ℝ) (e k v : CVector n) :
    Complex.normSq (tr (testMatrix c e k v)) =
      c ^ 2 * ‖dot v e‖ ^ 2 + ‖dot k v‖ ^ 2 +
        2 * c * (dot v e * star (dot k v)).re := by
  rw [tr_testMatrix, complex_sq_add, complex_sq_real_mul]
  simp only [Complex.sq_norm, mul_assoc, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

lemma projected_testMatrix_sq_bound (hn : 2 ≤ n) (c : ℝ) (hc : 0 ≤ c)
    (e k v : CVector n) (he : vecSq e = 1) (hk : vecSq k ≤ 1) :
    hsSq (projected (testMatrix c e k v)) ≤
      (n : ℝ) ^ 2 * ((c ^ 2 + (n : ℝ) - 1) * vecSq v) := by
  have hN : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : ‖dot k v‖ ^ 2 ≤ vecSq v := by
    rw [Complex.sq_norm]
    exact (dot_sq_le k v).trans (by nlinarith [vecSq_nonneg v])
  have ht : (dot v e * star (dot k v)).re ≤ ‖dot v e‖ * ‖dot k v‖ := by
    calc
      _ ≤ ‖dot v e * star (dot k v)‖ := Complex.re_le_norm _
      _ = _ := by rw [norm_mul, norm_star]
  rw [projected_sq, testMatrix_sq c e k v he, tr_testMatrix_sq]
  exact tracefree_projected_sq_bound (n : ℝ) c (vecSq v) (vecSq k)
    ‖dot v e‖ ‖dot k v‖ (dot v e * star (dot k v)).re
    hN hc (vecSq_nonneg v) hk hs ht

/-- Lemma 2.6, expressed in finite sums of the genuine squared complex norms.
`action` is exactly `c C e + C* k`, not an abstract action. -/
theorem tracefree_matrix_inequality (hn : 2 ≤ n) (c : ℝ) (hc : 0 ≤ c)
    (C : CMatrix n) (htr : tr C = 0) (e k : CVector n)
    (he : vecSq e = 1) (hk : vecSq k ≤ 1) :
    vecSq (action c C e k) ≤ (c ^ 2 + (n : ℝ) - 1) * hsSq C := by
  let w := action c C e k
  let Q := testMatrix c e k w
  have hp : pair C (projected Q) = (n : ℝ) * vecSq w := by
    rw [pair_projected_of_trace_zero C Q htr]
    change (n : ℝ) * pair C (testMatrix c e k w) = _
    rw [testMatrix_duality]
    change (n : ℝ) * (dot w w).re = _
    rw [dot_re_self]
  have hD := projected_testMatrix_sq_bound hn c hc e k w he hk
  have hcs := pair_sq_le C (projected Q)
  rw [hp] at hcs
  have hupper := mul_le_mul_of_nonneg_left hD (hsSq_nonneg C)
  have hcombined :
      (n : ℝ) ^ 2 * (vecSq w) ^ 2 ≤
        (n : ℝ) ^ 2 * (((c ^ 2 + (n : ℝ) - 1) * hsSq C) * vecSq w) := by
    calc
      _ = ((n : ℝ) * vecSq w) ^ 2 := by ring
      _ ≤ hsSq C * hsSq (projected Q) := hcs
      _ ≤ hsSq C * ((n : ℝ) ^ 2 * ((c ^ 2 + (n : ℝ) - 1) * vecSq w)) := hupper
      _ = _ := by ring
  have hN : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hN2 : 0 < (n : ℝ) ^ 2 := sq_pos_of_pos hN
  have hcancel := le_of_mul_le_mul_left hcombined hN2
  have hcoefficient : 0 ≤ c ^ 2 + (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [sq_nonneg c]
  exact square_bound_cancel_nonneg (vecSq w)
    ((c ^ 2 + (n : ℝ) - 1) * hsSq C) (vecSq_nonneg w)
    (mul_nonneg hcoefficient (hsSq_nonneg C)) hcancel

/-- A precise bridge to the matrix trace used in the manuscript. -/
theorem tr_eq_matrix_trace (C : CMatrix n) : tr C = Matrix.trace C := rfl

/-- A precise bridge to ordinary matrix-vector multiplication. -/
theorem mv_eq_matrix_mulVec (C : CMatrix n) (e : CVector n) : mv C e = C.mulVec e := rfl

/-- A precise bridge to the conjugate-transpose action. -/
theorem adjmv_eq_conjTranspose_mulVec (C : CMatrix n) (k : CVector n) :
    adjmv C k = C.conjTranspose.mulVec k := rfl

/-- No sup norm on the function type is being substituted for the L2 norm. -/
theorem vecSq_eq_euclidean_norm_sq (v : CVector n) :
    vecSq v = ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin n))‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [vecSq, Complex.sq_norm]

/-- The finite-sum Hilbert--Schmidt square is the real trace of `C C*`. -/
theorem hsSq_eq_trace_product (C : CMatrix n) :
    hsSq C = (Matrix.trace (C * C.conjTranspose)).re := by
  change (∑ i, ∑ j, Complex.normSq (C i j)) =
    (∑ i, ∑ j, C i j * star (C i j)).re
  simp only [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.star_def,
    Complex.conj_re, Complex.conj_im]
  ring

end CHS.Algebra

namespace CHS

open CHS.Algebra

/-- Paper Lemma 2.6 in actual Euclidean norms and matrix operations.
The section-wide manuscript assumption is `n ≥ 2`.
S001: full proof text only; no successful Lean build has yet occurred. -/
theorem tracefree_matrix_inequality {n : ℕ} (hn : 2 ≤ n)
    (c : ℝ) (hc : 0 ≤ c) (C : Matrix (Fin n) (Fin n) ℂ)
    (htr : Matrix.trace C = 0) (e k : Fin n → ℂ)
    (he : ‖(WithLp.toLp 2 e : EuclideanSpace ℂ (Fin n))‖ = 1)
    (hk : ‖(WithLp.toLp 2 k : EuclideanSpace ℂ (Fin n))‖ ≤ 1) :
    ‖(WithLp.toLp 2 (fun i => (c : ℂ) * C.mulVec e i +
        C.conjTranspose.mulVec k i) : EuclideanSpace ℂ (Fin n))‖ ^ 2 ≤
      (c ^ 2 + (n : ℝ) - 1) * (Matrix.trace (C * C.conjTranspose)).re := by
  have he2 : vecSq e = 1 := by
    rw [vecSq_eq_euclidean_norm_sq, he]
    norm_num
  have hk2 : vecSq k ≤ 1 := by
    rw [vecSq_eq_euclidean_norm_sq]
    nlinarith [norm_nonneg (WithLp.toLp 2 k : EuclideanSpace ℂ (Fin n))]
  have ht : tr C = 0 := by simpa only [tr_eq_matrix_trace] using htr
  have h := Algebra.tracefree_matrix_inequality hn c hc C ht e k he2 hk2
  rw [vecSq_eq_euclidean_norm_sq, hsSq_eq_trace_product] at h
  exact h

end CHS

