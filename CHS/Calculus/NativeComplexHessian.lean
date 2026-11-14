import CHS.Calculus.SchurContraction

/-!
# Actual complex, pure and anti-pure Hessians of a real potential

S006 candidate, not compiled in Chat. All matrices below are obtained from
real Fréchet derivatives; no third- or fourth-order identities are hypotheses.
The constant-direction formulation is specialized at the end to the frozen
interleaved coordinates on real Euclidean 2n-space.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ContDiff Topology

namespace CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def complexify (u : E → ℝ) : E → ℂ := fun x => (u x : ℂ)

lemma complexify_contDiffOn {k : WithTop ℕ∞} {u : E → ℝ} {U : Set E}
    (hu : ContDiffOn ℝ k u U) : ContDiffOn ℝ k (complexify u) U :=
  Complex.ofRealCLM.contDiff.fun_comp_contDiffOn hu

noncomputable def complexHessianIn (a b : ι → E) (u : E → ℝ)
    (x : E) : Matrix ι ι ℂ :=
  fun i j => dz (a i) (b i) (dz (a j) (-b j) (complexify u)) x

noncomputable def pureHessianIn (a b : ι → E) (u : E → ℝ)
    (x : E) : Matrix ι ι ℂ :=
  fun i j => dz (a i) (b i) (dz (a j) (b j) (complexify u)) x

noncomputable def antiHessianIn (a b : ι → E) (u : E → ℝ)
    (x : E) : Matrix ι ι ℂ :=
  fun i j => dz (a i) (-b i) (dz (a j) (-b j) (complexify u)) x

lemma complexHessianIn_contDiffOn (a b : ι → E) {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (i j : ι) :
    ContDiffOn ℝ 2 (fun x => complexHessianIn a b u x i j) U := by
  intro x hx
  have hc := (complexify_contDiffOn hu).contDiffAt (hU.mem_nhds hx)
  exact (dz_contDiffAt_two (dz_contDiffAt_three hc (a j) (-b j))
    (a i) (b i)).contDiffWithinAt

lemma pureHessianIn_contDiffOn (a b : ι → E) {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (i j : ι) :
    ContDiffOn ℝ 2 (fun x => pureHessianIn a b u x i j) U := by
  intro x hx
  have hc := (complexify_contDiffOn hu).contDiffAt (hU.mem_nhds hx)
  exact (dz_contDiffAt_two (dz_contDiffAt_three hc (a j) (b j))
    (a i) (b i)).contDiffWithinAt

lemma antiHessianIn_contDiffOn (a b : ι → E) {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (i j : ι) :
    ContDiffOn ℝ 2 (fun x => antiHessianIn a b u x i j) U := by
  intro x hx
  have hc := (complexify_contDiffOn hu).contDiffAt (hU.mem_nhds hx)
  exact (dz_contDiffAt_two (dz_contDiffAt_three hc (a j) (-b j))
    (a i) (-b i)).contDiffWithinAt

/-- Two conjugations of actual Wirtinger derivatives, including nondifferentiable
points under mathlib's total fderiv convention. -/
lemma star_second_dz (a b c d : E) (f : E → ℂ) (x : E) :
    star (dz a b (dz c d f) x) =
      dz a (-b) (dz c (-d) (fun y => star (f y))) x := by
  rw [← dz_star_flip a b (dz c d f) x]
  have h : (fun y => star (dz c d f y)) = dz c (-d) (fun y => star (f y)) := by
    funext y
    exact (dz_star_flip c d f y).symm
  rw [h]

lemma star_complexify (u : E → ℝ) :
    (fun x => star (complexify u x)) = complexify u := by
  funext x
  simp [complexify, Complex.star_def]

lemma complexHessianIn_star_entry (a b : ι → E) {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (i j : ι) :
    star (complexHessianIn a b u x i j) = complexHessianIn a b u x j i := by
  have hc : ContDiffAt ℝ 2 (complexify u) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hu
  change star (dz (a i) (b i) (dz (a j) (-b j) (complexify u)) x) = _
  rw [star_second_dz, neg_neg, star_complexify]
  exact dz_comm_at hc (a i) (-b i) (a j) (b j)

lemma complexHessianIn_conjTranspose (a b : ι → E) {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) :
    (complexHessianIn a b u x).conjTranspose = complexHessianIn a b u x := by
  ext i j
  exact complexHessianIn_star_entry a b hu j i

/-- Thus the transpose used in the calculus equals the paper's bar(A). -/
lemma complexHessianIn_transpose_eq_bar (a b : ι → E) {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) :
    (complexHessianIn a b u x).transpose =
      (fun i j => star (complexHessianIn a b u x i j)) := by
  ext i j
  exact (complexHessianIn_star_entry a b hu i j).symm

lemma antiHessianIn_eq_bar (a b : ι → E) (u : E → ℝ) (x : E) :
    antiHessianIn a b u x = (fun i j => star (pureHessianIn a b u x i j)) := by
  ext i j
  change dz (a i) (-b i) (dz (a j) (-b j) (complexify u)) x =
    star (dz (a i) (b i) (dz (a j) (b j) (complexify u)) x)
  rw [star_second_dz, star_complexify]

lemma pureHessianIn_symmetric (a b : ι → E) {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (i j : ι) :
    pureHessianIn a b u x i j = pureHessianIn a b u x j i := by
  have hc : ContDiffAt ℝ 2 (complexify u) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hu
  exact dz_comm_at hc (a i) (b i) (a j) (b j)

lemma antiHessianIn_eq_conjTranspose (a b : ι → E) {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) :
    antiHessianIn a b u x = (pureHessianIn a b u x).conjTranspose := by
  rw [antiHessianIn_eq_bar]
  ext i j
  exact congrArg star (pureHessianIn_symmetric a b hu i j)

/-- Cyclically move the last of three derivatives to the front. -/
lemma third_cycle_on {f : E → ℂ} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 3 f U) (a b c d e k : E)
    {x : E} (hx : x ∈ U) :
    dz a b (dz c d (dz e k f)) x = dz e k (dz a b (dz c d f)) x := by
  calc
    _ = dz a b (dz e k (dz c d f)) x := third_inner_comm_on hU hf a b c d e k hx
    _ = _ := third_outer_comm_at (hf.contDiffAt (hU.mem_nhds hx)) a b e k c d

/-- Reverse three derivatives using actual neighbourhood equalities. -/
lemma third_reverse_on {f : E → ℂ} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 3 f U) (a b c d e k : E)
    {x : E} (hx : x ∈ U) :
    dz a b (dz c d (dz e k f)) x = dz e k (dz c d (dz a b f)) x := by
  have hfx := hf.contDiffAt (hU.mem_nhds hx)
  calc
    _ = dz c d (dz a b (dz e k f)) x := third_outer_comm_at hfx a b c d e k
    _ = dz c d (dz e k (dz a b f)) x := third_inner_comm_on hU hf c d a b e k hx
    _ = _ := third_outer_comm_at hfx c d e k a b

/-- Move the last pair to the front with reversed order. All swaps below are
at C4, and the inner swaps are proved on an open neighbourhood first. -/
lemma fourth_contraction_exchange_on {f : E → ℂ} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 4 f U) (a b c d e k p q : E)
    {x : E} (hx : x ∈ U) :
    dz a b (dz c d (dz e k (dz p q f))) x =
      dz p q (dz e k (dz a b (dz c d f))) x := by
  have hfx := hf.contDiffAt (hU.mem_nhds hx)
  calc
    _ = dz a b (dz e k (dz c d (dz p q f))) x :=
      fourth_middle_comm_on hU hf a b c d e k p q hx
    _ = dz a b (dz e k (dz p q (dz c d f))) x :=
      fourth_inner_comm_on hU hf a b e k c d p q hx
    _ = dz e k (dz a b (dz p q (dz c d f))) x :=
      fourth_outer_comm_at hfx a b e k p q c d
    _ = dz e k (dz p q (dz a b (dz c d f))) x :=
      fourth_middle_comm_on hU hf e k a b p q c d hx
    _ = _ := fourth_outer_comm_at hfx e k p q a b c d

lemma complexHessianIn_second_exchange (a b : ι → E) {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) {x : E} (hx : x ∈ U) (i j p q : ι) :
    matrixDZ (a i) (b i) (matrixDZ (a j) (-b j) (complexHessianIn a b u)) x p q =
      matrixDZ (a q) (-b q) (matrixDZ (a p) (b p) (complexHessianIn a b u)) x i j := by
  exact fourth_contraction_exchange_on hU (complexify_contDiffOn hu)
    (a i) (b i) (a j) (-b j) (a p) (b p) (a q) (-b q) hx

lemma pureHessianIn_second_exchange (a b : ι → E) {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) {x : E} (hx : x ∈ U) (i j p q : ι) :
    matrixDZ (a i) (b i) (matrixDZ (a j) (b j) (complexHessianIn a b u)) x p q =
      matrixDZ (a q) (-b q) (matrixDZ (a p) (b p) (pureHessianIn a b u)) x i j := by
  exact fourth_contraction_exchange_on hU (complexify_contDiffOn hu)
    (a i) (b i) (a j) (b j) (a p) (b p) (a q) (-b q) hx

/-- Fixed frozen coordinates: no new domain or complete metric hypothesis. -/
abbrev CMARealSpace (n : ℕ) := EuclideanSpace ℝ (Fin (2 * n))

def cmaRealIndex {n : ℕ} (i : Fin n) : Fin (2 * n) := ⟨2 * i.val, by omega⟩
def cmaImagIndex {n : ℕ} (i : Fin n) : Fin (2 * n) := ⟨2 * i.val + 1, by omega⟩
noncomputable def cmaRealDirection {n : ℕ} (i : Fin n) : CMARealSpace n :=
  EuclideanSpace.single (cmaRealIndex i) 1
noncomputable def cmaImagDirection {n : ℕ} (i : Fin n) : CMARealSpace n :=
  EuclideanSpace.single (cmaImagIndex i) 1
noncomputable def nativeComplexHessian {n : ℕ} (u : CMARealSpace n → ℝ) :=
  complexHessianIn cmaRealDirection cmaImagDirection u
noncomputable def nativePureHessian {n : ℕ} (u : CMARealSpace n → ℝ) :=
  pureHessianIn cmaRealDirection cmaImagDirection u
noncomputable def nativeAntiHessian {n : ℕ} (u : CMARealSpace n → ℝ) :=
  antiHessianIn cmaRealDirection cmaImagDirection u

end CHS.Calculus
