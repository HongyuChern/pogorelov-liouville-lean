import CHS.Pogorelov.ClosureMaximum
import CHS.Pogorelov.CompactQuotient
import CHS.Pogorelov.RealHessianBound

/-!
# Theorem 1.1, positive definite branch: pointwise weighted estimate

Both geometric alternatives are supplied below.  These declarations use
explicit upper bounds `K` and `V`; the supremum-norm endpoint is a separate
wrapper.  The original sign-independent theorem is not identified with
this positive definite branch.
-/

set_option autoImplicit false
noncomputable section

open Matrix Set
open scoped BigOperators ComplexOrder ContDiff

namespace CHS.Pogorelov

open CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : ℕ}

theorem weighted_realBlockHessian_bound_of_trace_bound
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) (a b : Fin n → E)
    (hA : (complexHessian a b u x).PosDef) {κ : ℝ} (hκ : 0 ≤ κ)
    (hmat : (κ • complexHessian a b u x -
      pureHessian a b u x * ((complexHessian a b u x).map star)⁻¹ *
        (pureHessian a b u x).map star).PosSemidef)
    {w c R : ℝ} (hw : 0 ≤ w) (hc : 0 < c)
    (htrace : w * traceCombination a b u c x ≤ c * R) (i j : Fin n ⊕ Fin n) :
    |w * realBlockHessian a b u x i j| ≤ 2 * (1 + Real.sqrt κ) * R := by
  have hm : (κ • complexHessian a b u x -
      (complexHessian a b u x - schurHessian a b u x)).PosSemidef := by
    change (κ • complexHessian a b u x - (_ - (_ - _))).PosSemidef
    rw [sub_sub_cancel]
    exact hmat
  have hd : 0 ≤ (correctionTrace a b u x).re :=
    (schur_correction_trace_bounds hu a b hA κ hm).1
  have ha : w * (complexHessian a b u x).trace.re ≤ R := by
    apply (mul_le_mul_iff_of_pos_left hc).mp
    calc
      c * (w * (complexHessian a b u x).trace.re) ≤
          w * traceCombination a b u c x := by
        unfold traceCombination
        nlinarith [mul_nonneg hw hd]
      _ ≤ c * R := htrace
  have hentry := mul_le_mul_of_nonneg_left
    (realBlockHessian_entry_bound hu a b hA hκ hmat i j) hw
  have hfactor : 0 ≤ 2 * (1 + Real.sqrt κ) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left ha hfactor
  rw [abs_mul, abs_of_nonneg hw]
  nlinarith

theorem positive_branch_estimate_of_compact_jet_representatives
    {u : E → ℝ} {U C : Set E} (hn : 2 ≤ n) (hU : IsOpen U)
    (hC : IsCompact C) (hCU : C ⊆ closure U) (hu : ContDiffOn ℝ 4 u U)
    (J : ClosureC2Jet u U) (a b : Fin n → E)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = 1)
    (hpos : ∀ y ∈ U, (complexHessian a b u y).PosDef)
    {κ : ℝ} (hκ : 1 ≤ κ)
    (hmat : ∀ y ∈ U, (κ • complexHessian a b u y -
      pureHessian a b u y * ((complexHessian a b u y).map star)⁻¹ *
        (pureHessian a b u y).map star).PosSemidef)
    (hbd : ∀ y ∈ frontier U, u y = 0)
    (hrep : ∀ x ∈ closure U, ∃ y ∈ C,
      u x = u y ∧ J.derivative x = J.derivative y ∧ J.hessian x = J.hessian y)
    (K V : ℝ) (hK : ∀ y ∈ U, gradientNormSq a b u y ≤ K ^ 2)
    (hV : ∀ y ∈ U, -u y ≤ V) :
    ∀ y ∈ U, ∀ i j : Fin n ⊕ Fin n,
      |(-u y) ^ beta n κ * realBlockHessian a b u y i j| ≤
        32 * (n : ℝ) * beta n κ * (1 + Real.sqrt κ) * Real.exp (1 / 8) *
          (1 + K ^ 2) * V ^ (beta n κ - 1) := by
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hu₂ : ContDiffOn ℝ 2 u U := hu.of_le (by norm_num)
  have hneg := neg_on_of_compact_representatives hU hC hCU J.continuous_value hu₂
    a b hpos hbd (fun x hx => by
      obtain ⟨y, hy, hxy, _, _⟩ := hrep x hx
      exact ⟨y, hy, hxy⟩)
  have ht := weighted_trace_bound_of_compact_jet_representatives hn hU hC hCU hu J
    a b hdet hpos hκ hmat hbd hrep K V hK hV
  intro y hy i j
  let R := 16 * (n : ℝ) * beta n κ * Real.exp (1 / 8) *
    (1 + K ^ 2) * V ^ (beta n κ - 1)
  have htrace : (-u y) ^ beta n κ * traceCombination a b u (cChoice n κ) y ≤
      cChoice n κ * R := by
    convert ht y hy using 1 <;> dsimp [R] <;> ring
  have h := weighted_realBlockHessian_bound_of_trace_bound
    (hu₂.contDiffAt (hU.mem_nhds hy)) a b (hpos y hy) (by linarith : 0 ≤ κ)
    (hmat y hy) (Real.rpow_nonneg (neg_nonneg.mpr (hneg y hy).le) _)
    (cChoice_pos hn hκ) htrace i j
  calc
    _ ≤ 2 * (1 + Real.sqrt κ) * R := h
    _ = _ := by dsimp [R]; ring

theorem positive_branch_estimate_of_compact_closure
    {u : E → ℝ} {U : Set E} (hn : 2 ≤ n) (hU : IsOpen U)
    (hcompact : IsCompact (closure U)) (hu : ContDiffOn ℝ 4 u U)
    (huBoundary : C2OnClosure u U) (a b : Fin n → E)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = 1)
    (hpos : ∀ y ∈ U, (complexHessian a b u y).PosDef)
    {κ : ℝ} (hκ : 1 ≤ κ)
    (hmat : ∀ y ∈ U, (κ • complexHessian a b u y -
      pureHessian a b u y * ((complexHessian a b u y).map star)⁻¹ *
        (pureHessian a b u y).map star).PosSemidef)
    (hbd : ∀ y ∈ frontier U, u y = 0)
    (K V : ℝ) (hK : ∀ y ∈ U, gradientNormSq a b u y ≤ K ^ 2)
    (hV : ∀ y ∈ U, -u y ≤ V) :
    ∀ y ∈ U, ∀ i j : Fin n ⊕ Fin n,
      |(-u y) ^ beta n κ * realBlockHessian a b u y i j| ≤
        32 * (n : ℝ) * beta n κ * (1 + Real.sqrt κ) * Real.exp (1 / 8) *
          (1 + K ^ 2) * V ^ (beta n κ - 1) :=
  positive_branch_estimate_of_compact_jet_representatives hn hU hcompact Subset.rfl hu
    huBoundary.jet a b hdet hpos hκ hmat hbd
    (fun x hx => ⟨x, hx, rfl, rfl, rfl⟩) K V hK hV

section Quotient

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable [FiniteDimensional ℝ F]

theorem positive_branch_estimate_of_compact_real_quotient
    (L : Submodule ℝ F) {u : F → ℝ} {U : Set F} (hn : 2 ≤ n) (hU : IsOpen U)
    (hquot : IsCompact ((Submodule.Quotient.mk : F → F ⧸ L) '' closure U))
    (hUinv : ∀ x ∈ U, ∀ v ∈ L, x + v ∈ U)
    (huinv : ∀ x ∈ U, ∀ v ∈ L, u (x + v) = u x)
    (hu : ContDiffOn ℝ 4 u U) (huBoundary : C2OnClosure u U) (a b : Fin n → F)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = 1)
    (hpos : ∀ y ∈ U, (complexHessian a b u y).PosDef)
    {κ : ℝ} (hκ : 1 ≤ κ)
    (hmat : ∀ y ∈ U, (κ • complexHessian a b u y -
      pureHessian a b u y * ((complexHessian a b u y).map star)⁻¹ *
        (pureHessian a b u y).map star).PosSemidef)
    (hbd : ∀ y ∈ frontier U, u y = 0)
    (K V : ℝ) (hK : ∀ y ∈ U, gradientNormSq a b u y ≤ K ^ 2)
    (hV : ∀ y ∈ U, -u y ≤ V) :
    ∀ y ∈ U, ∀ i j : Fin n ⊕ Fin n,
      |(-u y) ^ beta n κ * realBlockHessian a b u y i j| ≤
        32 * (n : ℝ) * beta n κ * (1 + Real.sqrt κ) * Real.exp (1 / 8) *
          (1 + K ^ 2) * V ^ (beta n κ - 1) := by
  obtain ⟨C, hC, hCU, hrep⟩ :=
    compact_jet_representatives_of_compact_real_quotient L hU
      (hu.of_le (by norm_num)) huBoundary.jet hUinv huinv hquot
  exact positive_branch_estimate_of_compact_jet_representatives hn hU hC hCU hu
    huBoundary.jet a b hdet hpos hκ hmat hbd hrep K V hK hV

end Quotient
end CHS.Pogorelov
