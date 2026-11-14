import CHS.Analysis.EssentialSupremum
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Maximum of the entrywise L∞ seminorms

The matrix endpoint agrees with the manuscript's definition: the maximum
over entries of their scalar L∞ seminorms.  Reindexing by the two-block
coordinate equivalence preserves it exactly.
-/

set_option autoImplicit false
noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace CHS.Analysis

variable {E ι κ : Type*}

theorem entrySupNormOn_eq_sup_scalarSupNormOn [Finite ι] [Finite κ]
    (U : Set E) (H : E → Matrix ι κ ℝ)
    (hbounded : ∀ i j, BddAbove ((fun x => |H x i j|) '' U)) :
    entrySupNormOn U H =
      sSup (insert 0 (range (fun p : ι × κ => scalarSupNormOn U (fun x => H x p.1 p.2)))) := by
  let S := insert 0 (range (fun p : ι × κ => scalarSupNormOn U (fun x => H x p.1 p.2)))
  have hS : BddAbove S := (finite_range _).bddAbove.insert 0
  have hS0 : 0 ≤ sSup S := le_csSup hS (mem_insert 0 _)
  have hentry (x : E) (hx : x ∈ U) (i : ι) (j : κ) : |H x i j| ≤ sSup S :=
    (abs_le_scalarSupNormOn (hbounded i j) hx).trans
      (le_csSup hS (mem_insert_of_mem 0 ⟨(i, j), rfl⟩))
  have hH : BddAbove {r | ∃ x ∈ U, ∃ i j, r = |H x i j|} := by
    refine ⟨sSup S, ?_⟩
    rintro r ⟨x, hx, i, j, rfl⟩
    exact hentry x hx i j
  have hH0 : 0 ≤ entrySupNormOn U H := le_csSup (hH.insert 0) (mem_insert 0 _)
  apply le_antisymm (entrySupNormOn_le hS0 hentry)
  apply csSup_le ⟨0, mem_insert 0 _⟩
  intro r hr
  rcases mem_insert_iff.mp hr with rfl | hr
  · exact hH0
  · obtain ⟨⟨i, j⟩, rfl⟩ := hr
    exact scalarSupNormOn_le hH0 (fun _ hx => abs_entry_le_entrySupNormOn hH hx i j)

theorem entrySupNormOn_reindex {ι' κ' : Type*} (e : ι ≃ ι') (d : κ ≃ κ')
    (U : Set E) (H : E → Matrix ι κ ℝ) :
    entrySupNormOn U (fun x => Matrix.reindex e d (H x)) = entrySupNormOn U H := by
  have hs : {r | ∃ x ∈ U, ∃ i j, r = |Matrix.reindex e d (H x) i j|} =
      {r | ∃ x ∈ U, ∃ i j, r = |H x i j|} := by
    ext r
    constructor
    · rintro ⟨x, hx, i, j, hr⟩
      exact ⟨x, hx, e.symm i, d.symm j, hr⟩
    · rintro ⟨x, hx, i, j, hr⟩
      exact ⟨x, hx, e i, d j, by
        simpa only [Matrix.reindex_apply, Matrix.submatrix_apply,
          Equiv.symm_apply_apply] using hr⟩
  unfold entrySupNormOn
  rw [hs]

section Measure

variable [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
variable {μ : Measure E} [μ.IsOpenPosMeasure]

def entryLinfNormOn (μ : Measure E) (U : Set E) (H : E → Matrix ι κ ℝ) : ℝ :=
  sSup (insert 0 (range (fun p : ι × κ =>
    (eLpNorm (fun x => H x p.1 p.2) ∞ (μ.restrict U)).toReal)))

theorem entryLinfNormOn_reindex {ι' κ' : Type*} (e : ι ≃ ι') (d : κ ≃ κ')
    (U : Set E) (H : E → Matrix ι κ ℝ) :
    entryLinfNormOn μ U (fun x => Matrix.reindex e d (H x)) = entryLinfNormOn μ U H := by
  have hrange :
      range (fun p : ι' × κ' =>
        (eLpNorm (fun x => Matrix.reindex e d (H x) p.1 p.2) ∞ (μ.restrict U)).toReal) =
      range (fun p : ι × κ =>
        (eLpNorm (fun x => H x p.1 p.2) ∞ (μ.restrict U)).toReal) := by
    ext r
    constructor
    · rintro ⟨⟨i, j⟩, hr⟩
      exact ⟨(e.symm i, d.symm j), hr⟩
    · rintro ⟨⟨i, j⟩, hr⟩
      exact ⟨(e i, d j), by
        simpa only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply] using hr⟩
  unfold entryLinfNormOn
  rw [hrange]

theorem entrySupNormOn_eq_entryLinfNormOn [Finite ι] [Finite κ]
    {U : Set E} (hU : IsOpen U) {H : E → Matrix ι κ ℝ}
    (hcont : ∀ i j, ContinuousOn (fun x => H x i j) U)
    (hbounded : ∀ i j, BddAbove ((fun x => |H x i j|) '' U)) :
    entrySupNormOn U H = entryLinfNormOn μ U H := by
  rw [entrySupNormOn_eq_sup_scalarSupNormOn U H hbounded]
  have heq : (fun p : ι × κ => scalarSupNormOn U (fun x => H x p.1 p.2)) =
      (fun p : ι × κ => (eLpNorm (fun x => H x p.1 p.2) ∞ (μ.restrict U)).toReal) := by
    funext p
    exact scalarSupNormOn_eq_eLpNorm_top_toReal hU (hcont p.1 p.2) (hbounded p.1 p.2)
  rw [heq]
  rfl

end Measure
end CHS.Analysis
