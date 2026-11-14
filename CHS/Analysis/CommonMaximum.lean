import CHS.Analysis.CompactCommonZero

/-!
# A common maximizer of subsolution observables in a compact range closure

This is the scale-independent whole-space compactness consequence of weak
Harnack.  It does not assert a local Evans--Krylov oscillation estimate.
-/

set_option autoImplicit false
noncomputable section

open DeGiorgi Set
open scoped BigOperators

namespace CHS.Analysis

variable {d : ℕ} [NeZero d]
local notation "E" => AmbientSpace d

theorem exists_common_maximum_in_range_closure
    {X ι : Type*} [TopologicalSpace X] (hd : 2 < (d : ℝ))
    (B : NormalizedEllipticCoeff d univ) (H : E → X)
    (hH : Continuous H) (hcompact : IsCompact (closure (range H)))
    (f : ι → X → ℝ) (hf : ∀ i, Continuous (f i))
    (hsuper : ∀ i M R, 0 < R →
      IsSupersolution (B.restrict (subset_univ (Metric.ball (0 : E) R))).1
        (fun x => M - f i (H x))) :
    ∃ A ∈ closure (range H), ∀ i x, f i (H x) ≤ f i A := by
  classical
  let S := closure (range H)
  let m : ι → ℝ := fun i => sSup (range (fun x => f i (H x)))
  let g : ι → X → ℝ := fun i A => m i - f i A
  have hmem (x : E) : H x ∈ S := subset_closure (mem_range_self x)
  have hbdd (i : ι) : BddAbove (range (fun x => f i (H x))) :=
    ((hcompact.image (hf i)).bddAbove).mono (by
      rintro _ ⟨x, rfl⟩
      exact mem_image_of_mem _ (hmem x))
  have hupper (i : ι) (x : E) : f i (H x) ≤ m i :=
    le_csSup (hbdd i) (mem_range_self x)
  have hnonneg (i : ι) (A : X) (hA : A ∈ S) : 0 ≤ g i A := by
    apply sub_nonneg.mpr
    exact closure_minimal (by rintro _ ⟨x, rfl⟩; exact hupper i x)
      (isClosed_le (hf i) continuous_const) hA
  have hinf (i : ι) (δ : ℝ) (hδ : 0 < δ) : ∃ x : E, g i (H x) < δ := by
    obtain ⟨a, ⟨x, rfl⟩, hx⟩ := exists_lt_of_lt_csSup
      (range_nonempty (fun x : E => f i (H x))) (sub_lt_self (m i) hδ)
    refine ⟨x, ?_⟩
    dsimp only [g]
    linarith
  obtain ⟨A, hAS, hAzero⟩ := common_zero_of_compact_finite_approximation hcompact
    ⟨H 0, hmem 0⟩ g (fun i => continuous_const.sub (hf i)) hnonneg (by
      intro s ε hε
      let δ : ℝ := ε / (s.card + 1)
      have hδ : 0 < δ := by dsimp [δ]; positivity
      obtain ⟨x, hx⟩ := finite_supersolutions_simultaneously_small hd B
        (fun i : s => fun x => g i (H x))
        (fun i => continuous_const.sub ((hf i).comp hH))
        (fun i x => hnonneg i (H x) (hmem x))
        (fun i => hsuper i (m i)) (fun i => hinf i) hδ
      refine ⟨H x, hmem x, ?_⟩
      have hle : (∑ i ∈ s, g i (H x)) ≤ (s.card : ℝ) * δ := by
        calc
          _ ≤ ∑ _i ∈ s, δ := Finset.sum_le_sum fun i hi => (hx ⟨i, hi⟩).le
          _ = _ := by simp
      have hid : ((s.card : ℝ) + 1) * δ = ε := by dsimp [δ]; field_simp
      exact hle.trans_lt (by nlinarith))
  refine ⟨A, hAS, ?_⟩
  intro i x
  have hm : m i = f i A := sub_eq_zero.mp (hAzero i)
  exact (hupper i x).trans_eq hm

end CHS.Analysis
