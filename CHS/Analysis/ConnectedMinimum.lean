import DifferentialGeometry.External.DeGiorgi.StrongMinimum
import Mathlib.Topology.Connected.Basic

/-!
# From the genuine De Giorgi local minimum theorem to a connected open domain

Only locally normalized coefficient fields are required. There is no common
radius or global ellipticity constant. The local coefficient and supersolution
hypotheses are explicit intermediate inputs, to be constructed for the actual
CHS linearized operator; they are not hidden in the final paper statements.
S004 candidate source, awaiting real compilation.
-/

noncomputable section
open Set Metric Filter Topology

namespace CHS.Analysis
open DeGiorgi
variable {d : ℕ} [NeZero d]
local notation "E" => AmbientSpace d

/-- Zero propagation on an open connected set, with the original all-H01-test
De Giorgi predicate on a separate positive-radius ball around every point. -/
theorem eq_zero_on_connected_of_local_supersolutions
    (hd : 2 < (d : ℝ)) {U : Set E}
    (hU : IsOpen U) (hconn : IsPreconnected U)
    {u : E → ℝ} (hu : ContinuousOn u U)
    (hu_nonneg : ∀ x ∈ U, 0 ≤ u x)
    (hlocal : ∀ x ∈ U, ∃ R : ℝ, 0 < R ∧
      ∃ A : NormalizedEllipticCoeff d (ball x R),
        ball x R ⊆ U ∧ IsSupersolution A.1 u)
    {x₀ : E} (hx₀ : x₀ ∈ U) (hzero : u x₀ = 0) :
    EqOn u (fun _ => 0) U := by
  let Z : Set E := {x | x ∈ U ∧ u x = 0}
  let P : Set E := {x | x ∈ U ∧ u x ≠ 0}
  have hZ : IsOpen Z := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    rcases hlocal x hx.1 with ⟨R, hR, A, hball, hsuper⟩
    have hRq : 0 < R / 4 := div_pos hR (by norm_num)
    have hquarter : ball x (R / 4) ⊆ ball x R :=
      ball_subset_ball (by linarith)
    have hz : EqOn u (fun _ => 0) (ball x (R / 4)) :=
      DeGiorgi.IsSupersolution.eq_zero_on_quarter_ball hd hR A
        (hu.mono hball) (fun y hy => hu_nonneg y (hball hy)) hsuper
        (mem_ball_self hRq) hx.2
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hRq)] with y hy
    exact ⟨hball (hquarter hy), hz hy⟩
  have hP : IsOpen P := by
    have hpre := hu.isOpen_inter_preimage hU
      (isClosed_singleton : IsClosed ({0} : Set ℝ)).isOpen_compl
    simpa only [P, Set.inter_def, Set.mem_preimage, Set.mem_compl_iff,
      Set.mem_singleton_iff] using hpre
  have hdisj : Disjoint Z P := by
    apply Set.disjoint_left.mpr
    intro x hxZ hxP
    exact hxP.2 hxZ.2
  have hcover : U ⊆ Z ∪ P := by
    intro x hx
    by_cases hz : u x = 0
    · exact Or.inl ⟨hx, hz⟩
    · exact Or.inr ⟨hx, hz⟩
  have hnonempty : (U ∩ Z).Nonempty := ⟨x₀, hx₀, hx₀, hzero⟩
  have hsubset : U ⊆ Z :=
    hconn.subset_left_of_subset_union hZ hP hdisj hcover hnonempty
  intro x hx
  exact (hsubset hx).2

end CHS.Analysis
