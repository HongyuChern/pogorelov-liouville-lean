import CHS.CoreImports

/-!
# Actual local Wirtinger derivatives with finite regularity

Adapted from the selected S053 `KEBall.LocalWirtinger` proof pattern,
with the unnecessary C-infinity hypotheses removed. No KEBall solution
predicate, domain, metric, or PoincareLib dependency is imported here.

S001 STATUS: source written and manually reviewed, NOT Lean-typechecked.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Topology

namespace CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Actual real Frechet directional derivative, in a constant direction. -/
noncomputable def rd (v : E) (f : E → ℂ) (x : E) : ℂ := fderiv ℝ f x v

/-- The 1/2-normalized Wirtinger derivative; conjugate directions use `-b`. -/
noncomputable def dz (a b : E) (f : E → ℂ) (x : E) : ℂ :=
  (2 : ℂ)⁻¹ * (rd a f x - Complex.I * rd b f x)

lemma rd_contDiffAt_one {f : E → ℂ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (v : E) : ContDiffAt ℝ 1 (rd v f) x := by
  exact (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const

lemma rd_contDiffAt_two {f : E → ℂ} {x : E}
    (hf : ContDiffAt ℝ 3 f x) (v : E) : ContDiffAt ℝ 2 (rd v f) x := by
  exact (hf.fderiv_right (m := 2) (by norm_num)).clm_apply contDiffAt_const

lemma rd_contDiffAt_three {f : E → ℂ} {x : E}
    (hf : ContDiffAt ℝ 4 f x) (v : E) : ContDiffAt ℝ 3 (rd v f) x := by
  exact (hf.fderiv_right (m := 3) (by norm_num)).clm_apply contDiffAt_const

lemma dz_contDiffAt_one {f : E → ℂ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (a b : E) : ContDiffAt ℝ 1 (dz a b f) x := by
  exact contDiffAt_const.mul
    ((rd_contDiffAt_one hf a).sub (contDiffAt_const.mul (rd_contDiffAt_one hf b)))

lemma dz_contDiffAt_two {f : E → ℂ} {x : E}
    (hf : ContDiffAt ℝ 3 f x) (a b : E) : ContDiffAt ℝ 2 (dz a b f) x := by
  exact contDiffAt_const.mul
    ((rd_contDiffAt_two hf a).sub (contDiffAt_const.mul (rd_contDiffAt_two hf b)))

lemma dz_contDiffAt_three {f : E → ℂ} {x : E}
    (hf : ContDiffAt ℝ 4 f x) (a b : E) : ContDiffAt ℝ 3 (dz a b f) x := by
  exact contDiffAt_const.mul
    ((rd_contDiffAt_three hf a).sub (contDiffAt_const.mul (rd_contDiffAt_three hf b)))

lemma rd_const_mul_at {f : E → ℂ} {x : E}
    (hf : DifferentiableAt ℝ f x) (v : E) (c : ℂ) :
    rd v (fun y => c * f y) x = c * rd v f x := by
  simp [rd, fderiv_const_mul hf]

lemma rd_sub_at {f g : E → ℂ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (v : E) :
    rd v (fun y => f y - g y) x = rd v f x - rd v g x := by
  simp [rd, fderiv_fun_sub hf hg]

lemma rd_rd_at {f : E → ℂ} {x : E} (hf : ContDiffAt ℝ 2 f x) (a b : E) :
    rd a (rd b f) x = fderiv ℝ (fderiv ℝ f) x a b := by
  unfold rd
  have hdf : ContDiffAt ℝ 1 (fderiv ℝ f) x :=
    hf.fderiv_right (m := 1) (by norm_num)
  rw [fderiv_clm_apply (hdf.differentiableAt (by norm_num))
    (differentiableAt_const b)]
  simp

/-- C2 at the point is sufficient; no C-infinity hypothesis is used. -/
theorem rd_comm_at {f : E → ℂ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (a b : E) : rd a (rd b f) x = rd b (rd a f) x := by
  rw [rd_rd_at hf, rd_rd_at hf]
  exact (hf.isSymmSndFDerivAt (by simp)).eq a b

lemma rd_dz_at {f : E → ℂ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (v a b : E) :
    rd v (dz a b f) x = (2 : ℂ)⁻¹ *
      (rd v (rd a f) x - Complex.I * rd v (rd b f) x) := by
  have ha := (rd_contDiffAt_one hf a).differentiableAt (by norm_num)
  have hb := (rd_contDiffAt_one hf b).differentiableAt (by norm_num)
  have hI : DifferentiableAt ℝ (fun _ : E => Complex.I) x := differentiableAt_const _
  have hIb : DifferentiableAt ℝ (fun y => Complex.I * rd b f y) x := hI.mul hb
  have hsub : DifferentiableAt ℝ (fun y => rd a f y - Complex.I * rd b f y) x :=
    ha.sub hIb
  unfold dz
  rw [rd_const_mul_at hsub, rd_sub_at ha hIb, rd_const_mul_at hb]

/-- Commutation of any two constant Wirtinger directions at C2 regularity. -/
theorem dz_comm_at {f : E → ℂ} {x : E} (hf : ContDiffAt ℝ 2 f x)
    (a b c d : E) : dz a b (dz c d f) x = dz c d (dz a b f) x := by
  change (2 : ℂ)⁻¹ * (rd a (dz c d f) x - Complex.I * rd b (dz c d f) x) =
    (2 : ℂ)⁻¹ * (rd c (dz a b f) x - Complex.I * rd d (dz a b f) x)
  rw [rd_dz_at hf, rd_dz_at hf, rd_dz_at hf, rd_dz_at hf]
  rw [rd_comm_at hf a c, rd_comm_at hf a d, rd_comm_at hf b c, rd_comm_at hf b d]
  ring

/-- An open-set statement does not require extending the function smoothly
past the boundary. -/
theorem dz_comm_on {f : E → ℂ} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) (a b c d : E) {x : E} (hx : x ∈ U) :
    dz a b (dz c d f) x = dz c d (dz a b f) x := by
  exact dz_comm_at (hf.contDiffAt (hU.mem_nhds hx)) a b c d

/-- The outer two derivatives in a mixed third derivative, at C3. -/
theorem third_outer_comm_at {f : E → ℂ} {x : E}
    (hf : ContDiffAt ℝ 3 f x) (a b c d e k : E) :
    dz a b (dz c d (dz e k f)) x = dz c d (dz a b (dz e k f)) x := by
  exact dz_comm_at (dz_contDiffAt_two hf e k) a b c d

/-- The outer two derivatives in a fourth derivative, at C4. -/
theorem fourth_outer_comm_at {f : E → ℂ} {x : E}
    (hf : ContDiffAt ℝ 4 f x) (a b c d e k p q : E) :
    dz a b (dz c d (dz e k (dz p q f))) x =
      dz c d (dz a b (dz e k (dz p q f))) x := by
  exact dz_comm_at (dz_contDiffAt_two (dz_contDiffAt_three hf p q) e k) a b c d

/-- The actual real Hessian, not an abstract matrix supplied as a hypothesis. -/
noncomputable def realHessian (u : E → ℝ) (x : E) :
    E →L[ℝ] E →L[ℝ] ℝ := fderiv ℝ (fderiv ℝ u) x

theorem realHessian_symm {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) (v w : E) :
    realHessian u x v w = realHessian u x w v :=
  (hu.isSymmSndFDerivAt (by simp)).eq v w

/-- Local equality is sufficient for equality of the actual directional derivatives. -/
lemma rd_congr_nhds {f g : E → ℂ} {x : E}
    (hfg : f =ᶠ[𝓝 x] g) (a : E) : rd a f x = rd a g x := by
  unfold rd
  exact congrArg (fun D : E →L[ℝ] ℂ => D a) (hfg.fderiv_eq (𝕜 := ℝ))

lemma dz_congr_nhds {f g : E → ℂ} {x : E}
    (hfg : f =ᶠ[𝓝 x] g) (a b : E) : dz a b f x = dz a b g x := by
  unfold dz
  rw [rd_congr_nhds hfg a, rd_congr_nhds hfg b]

lemma dz_congr_on {f g : E → ℂ} {U : Set E} (hU : IsOpen U)
    (hfg : Set.EqOn f g U) (a b : E) {x : E} (hx : x ∈ U) :
    dz a b f x = dz a b g x := by
  apply dz_congr_nhds (a := a) (b := b)
  exact Filter.Eventually.mono (hU.mem_nhds hx) (fun y hy => hfg hy)

/-- The inner transposition is proved on a neighbourhood before differentiating;
pointwise equality at x alone would not justify this step. -/
theorem third_inner_comm_on {f : E → ℂ} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 3 f U) (a b c d e k : E)
    {x : E} (hx : x ∈ U) :
    dz a b (dz c d (dz e k f)) x = dz a b (dz e k (dz c d f)) x := by
  apply dz_congr_on hU (a := a) (b := b) (hx := hx)
  intro y hy
  exact dz_comm_at ((hf.contDiffAt (hU.mem_nhds hy)).of_le (by norm_num)) c d e k

/-- Middle adjacent transposition of four constant Wirtinger directions. -/
theorem fourth_middle_comm_on {f : E → ℂ} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 4 f U) (a b c d e k p q : E)
    {x : E} (hx : x ∈ U) :
    dz a b (dz c d (dz e k (dz p q f))) x =
      dz a b (dz e k (dz c d (dz p q f))) x := by
  apply dz_congr_on hU (a := a) (b := b) (hx := hx)
  intro y hy
  have hfy := hf.contDiffAt (hU.mem_nhds hy)
  exact dz_comm_at ((dz_contDiffAt_three hfy p q).of_le (by norm_num)) c d e k

/-- Innermost adjacent transposition of four derivatives, using two genuine
neighbourhood congruences; no extension beyond the open domain is assumed. -/
theorem fourth_inner_comm_on {f : E → ℂ} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 4 f U) (a b c d e k p q : E)
    {x : E} (hx : x ∈ U) :
    dz a b (dz c d (dz e k (dz p q f))) x =
      dz a b (dz c d (dz p q (dz e k f))) x := by
  apply dz_congr_on hU (a := a) (b := b) (hx := hx)
  intro y hy
  apply dz_congr_on hU (a := c) (b := d) (hx := hy)
  intro z hz
  exact dz_comm_at ((hf.contDiffAt (hU.mem_nhds hz)).of_le (by norm_num)) e k p q

end CHS.Calculus
