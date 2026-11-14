import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Data.Matrix.Basic

/-!
# Supremum seminorms used in the pointwise Pogorelov estimate

The scalar seminorm is the supremum of absolute values, with zero inserted
to cover an empty set.  The matrix seminorm takes the supremum over points
and individual entries.  No operator norm is involved.
-/

set_option autoImplicit false
noncomputable section

open Set

namespace CHS.Analysis

variable {E : Type*}

def scalarSupNormOn (U : Set E) (f : E → ℝ) : ℝ :=
  sSup (insert 0 ((fun x => |f x|) '' U))

theorem scalarSupNormOn_nonneg {U : Set E} {f : E → ℝ}
    (hf : BddAbove ((fun x => |f x|) '' U)) : 0 ≤ scalarSupNormOn U f :=
  le_csSup (hf.insert 0) (mem_insert 0 _)

theorem abs_le_scalarSupNormOn {U : Set E} {f : E → ℝ}
    (hf : BddAbove ((fun x => |f x|) '' U)) {x : E} (hx : x ∈ U) :
    |f x| ≤ scalarSupNormOn U f :=
  le_csSup (hf.insert 0) (mem_insert_of_mem 0 (mem_image_of_mem _ hx))

theorem scalarSupNormOn_le {U : Set E} {f : E → ℝ} {R : ℝ}
    (hR : 0 ≤ R) (hf : ∀ x ∈ U, |f x| ≤ R) : scalarSupNormOn U f ≤ R := by
  apply csSup_le ⟨0, mem_insert 0 _⟩
  intro r hr
  rcases mem_insert_iff.mp hr with rfl | hr
  · exact hR
  · obtain ⟨x, hx, rfl⟩ := hr
    exact hf x hx

def entrySupNormOn {ι κ : Type*} (U : Set E) (H : E → Matrix ι κ ℝ) : ℝ :=
  sSup (insert 0 {r | ∃ x ∈ U, ∃ i j, r = |H x i j|})

theorem entrySupNormOn_le {ι κ : Type*} {U : Set E} {H : E → Matrix ι κ ℝ} {R : ℝ}
    (hR : 0 ≤ R) (hH : ∀ x ∈ U, ∀ i j, |H x i j| ≤ R) :
    entrySupNormOn U H ≤ R := by
  apply csSup_le ⟨0, mem_insert 0 _⟩
  intro r hr
  rcases mem_insert_iff.mp hr with rfl | hr
  · exact hR
  · obtain ⟨x, hx, i, j, rfl⟩ := hr
    exact hH x hx i j

theorem abs_entry_le_entrySupNormOn {ι κ : Type*} {U : Set E}
    {H : E → Matrix ι κ ℝ}
    (hH : BddAbove {r | ∃ x ∈ U, ∃ i j, r = |H x i j|})
    {x : E} (hx : x ∈ U) (i : ι) (j : κ) : |H x i j| ≤ entrySupNormOn U H :=
  le_csSup (hH.insert 0) (mem_insert_of_mem 0 ⟨x, hx, i, j, rfl⟩)

/-- A continuous extension on a compact representative set bounds the
actual interior function. -/
theorem bddAbove_abs_image_of_compact_extension [TopologicalSpace E]
    {U C : Set E} (hC : IsCompact C) (hCU : C ⊆ closure U)
    {f F : E → ℝ} (hF : ContinuousOn F (closure U)) (hmatch : EqOn F f U)
    (hrep : ∀ x ∈ closure U, ∃ y ∈ C, F x = F y) :
    BddAbove ((fun x => |f x|) '' U) := by
  have habs : ContinuousOn (fun x => |F x|) C := by
    simpa only [Real.norm_eq_abs] using (hF.mono hCU).norm
  obtain ⟨M, hM⟩ := hC.bddAbove_image habs
  refine ⟨M, ?_⟩
  rintro r ⟨x, hx, rfl⟩
  change |f x| ≤ M
  obtain ⟨y, hy, hxy⟩ := hrep x (subset_closure hx)
  rw [← hmatch hx, hxy]
  exact hM (mem_image_of_mem _ hy)

end CHS.Analysis
