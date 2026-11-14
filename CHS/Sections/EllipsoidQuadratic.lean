import CHS.Calculus.HessianOrder
import CHS.Calculus.AffinePullback

/-!
# The actual quadratic potential of an ellipsoid on the transverse slice

The ellipsoid is represented by a continuous linear equivalence of the
orthogonal complement of the fixed real kernel.  All properties below
are proved for the actual function, including its Hessian, exact kernel,
translation invariance, and strictly positive complex Hessian.
No assertion of John ellipsoid existence is made in this file.
-/

set_option autoImplicit false
noncomputable section

open scoped ContDiff RealInnerProductSpace ComplexOrder

namespace CHS.Sections

open CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

def ellipsoidLinearMap (K : Submodule ℝ E) (T : Kᗮ ≃L[ℝ] Kᗮ) : E →L[ℝ] Kᗮ :=
  T.toContinuousLinearMap.comp Kᗮ.orthogonalProjectionOnto

def ellipsoidQuadratic (K : Submodule ℝ E) (T : Kᗮ ≃L[ℝ] Kᗮ) (a : E) (x : E) : ℝ :=
  ‖ellipsoidLinearMap K T (x - a)‖ ^ 2

theorem ellipsoidLinearMap_eq_zero_iff
    (K : Submodule ℝ E) (T : Kᗮ ≃L[ℝ] Kᗮ) (v : E) :
    ellipsoidLinearMap K T v = 0 ↔ v ∈ K := by
  constructor
  · intro hv
    have hP : Kᗮ.orthogonalProjectionOnto v = 0 := by
      apply T.injective
      change T (Kᗮ.orthogonalProjectionOnto v) = 0 at hv
      simpa only [map_zero] using hv
    have he := congrArg (fun z : Kᗮ => (z : E)) hP
    rw [Submodule.orthogonalProjectionOnto_orthogonal] at he
    change v - K.starProjection v = 0 at he
    rw [sub_eq_zero.mp he]
    exact K.starProjection_apply_mem v
  · intro hv
    have hP : Kᗮ.orthogonalProjectionOnto v = 0 :=
      Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal (K.le_orthogonal_orthogonal hv)
    change T (Kᗮ.orthogonalProjectionOnto v) = 0
    rw [hP, map_zero]

theorem contDiff_ellipsoidQuadratic
    (K : Submodule ℝ E) (T : Kᗮ ≃L[ℝ] Kᗮ) (a : E) (k : ℕ∞ω) :
    ContDiff ℝ k (ellipsoidQuadratic K T a) :=
  (((ellipsoidLinearMap K T).contDiff).comp (contDiff_id.sub contDiff_const)).norm_sq ℝ

theorem ellipsoidQuadratic_nonneg
    (K : Submodule ℝ E) (T : Kᗮ ≃L[ℝ] Kᗮ) (a x : E) : 0 ≤ ellipsoidQuadratic K T a x :=
  sq_nonneg _

theorem ellipsoidQuadratic_center
    (K : Submodule ℝ E) (T : Kᗮ ≃L[ℝ] Kᗮ) (a : E) : ellipsoidQuadratic K T a a = 0 := by
  simp only [ellipsoidQuadratic, sub_self, map_zero, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]

theorem realHessian_ellipsoidQuadratic
    (K : Submodule ℝ E) (T : Kᗮ ≃L[ℝ] Kᗮ) (a x v w : E) :
    realHessian (ellipsoidQuadratic K T a) x v w =
      2 * ⟪ellipsoidLinearMap K T v, ellipsoidLinearMap K T w⟫ := by
  let L := ellipsoidLinearMap K T
  have heq : ellipsoidQuadratic K T a =
      fun y => ‖L (-a + (ContinuousLinearMap.id ℝ E) y)‖ ^ 2 := by
    funext y
    dsimp only [ellipsoidQuadratic, L, ContinuousLinearMap.id_apply]
    congr 2
    abel
  rw [heq, realHessian_comp_affine (ContinuousLinearMap.id ℝ E) (-a)
    ((L.contDiff.norm_sq ℝ).contDiffAt), realHessian_norm_sq_comp]
  rfl

theorem realHessian_ellipsoidQuadratic_nonneg
    (K : Submodule ℝ E) (T : Kᗮ ≃L[ℝ] Kᗮ) (a x v : E) :
    0 ≤ realHessian (ellipsoidQuadratic K T a) x v v := by
  rw [realHessian_ellipsoidQuadratic, real_inner_self_eq_norm_sq]
  positivity

theorem realHessian_ellipsoidQuadratic_kernel
    (K : Submodule ℝ E) (T : Kᗮ ≃L[ℝ] Kᗮ) (a x : E) :
    (realHessian (ellipsoidQuadratic K T a) x).ker = K := by
  ext v
  change realHessian (ellipsoidQuadratic K T a) x v = 0 ↔ v ∈ K
  constructor
  · intro hv
    have hdiag := congrArg (fun L : E →L[ℝ] ℝ => L v) hv
    rw [realHessian_ellipsoidQuadratic, real_inner_self_eq_norm_sq] at hdiag
    have hn : ‖ellipsoidLinearMap K T v‖ = 0 := by
      have hp := norm_nonneg (ellipsoidLinearMap K T v)
      change 2 * ‖ellipsoidLinearMap K T v‖ ^ 2 = 0 at hdiag
      nlinarith
    exact (ellipsoidLinearMap_eq_zero_iff K T v).mp (norm_eq_zero.mp hn)
  · intro hv
    ext w
    rw [realHessian_ellipsoidQuadratic, (ellipsoidLinearMap_eq_zero_iff K T v).mpr hv]
    simp

theorem ellipsoidQuadratic_translation_invariant
    (K : Submodule ℝ E) (T : Kᗮ ≃L[ℝ] Kᗮ) (a x v : E) (hv : v ∈ K) :
    ellipsoidQuadratic K T a (x + v) = ellipsoidQuadratic K T a x := by
  have heq : x + v - a = (x - a) + v := by abel
  simp only [ellipsoidQuadratic, heq, map_add,
    (ellipsoidLinearMap_eq_zero_iff K T v).mpr hv, add_zero]

variable {ι : Type*}

theorem complexHessian_ellipsoidQuadratic_constant
    (K : Submodule ℝ E) (T : Kᗮ ≃L[ℝ] Kᗮ) (c : E) (a b : ι → E) (x y : E) :
    complexHessian a b (ellipsoidQuadratic K T c) x =
      complexHessian a b (ellipsoidQuadratic K T c) y := by
  have hq := contDiff_ellipsoidQuadratic K T c 2
  ext i j
  rw [complexHessian_real_entry hq.contDiffAt, complexHessian_real_entry hq.contDiffAt]
  simp only [realHessian_ellipsoidQuadratic]

theorem complexHessian_ellipsoidQuadratic_posDef [Fintype ι] [DecidableEq ι]
    (K : Submodule ℝ E) (T : Kᗮ ≃L[ℝ] Kᗮ) (c : E) (a b : ι → E)
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x)
    (hA : (complexHessian a b u x).PosDef) (hK : K ≤ (realHessian u x).ker) (y : E) :
    (complexHessian a b (ellipsoidQuadratic K T c) y).PosDef := by
  rw [complexHessian_ellipsoidQuadratic_constant K T c a b y x]
  have hq := (contDiff_ellipsoidQuadratic K T c 2).contDiffAt (x := x)
  have hker : (realHessian (ellipsoidQuadratic K T c) x).ker ≤ (realHessian u x).ker := by
    rwa [realHessian_ellipsoidQuadratic_kernel]
  exact (complexHessian_posDef_of_real_kernel_inclusion hu hq a b hA
    (realHessian_ellipsoidQuadratic_nonneg K T c x) hker).choose_spec.2.2

end CHS.Sections
