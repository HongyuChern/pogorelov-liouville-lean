import CHS.Sections.CoordinateConditioning
import CHS.Pogorelov.RealHessianBound

/-! # The actual real Hessian is controlled by four times the complex trace -/

set_option autoImplicit false
noncomputable section

open scoped ContDiff ComplexOrder

namespace CHS.Sections

open CHS.Calculus CHS.Analysis CHS.Pogorelov

variable {n : ℕ}
local notation "E₀" => DeGiorgi.AmbientSpace (n + n)

theorem euclideanHessian_entry_le_four_trace_of_convex
    {u : E₀ → ℝ} {x : E₀} (hu : ContDiffAt ℝ 2 u x)
    (hR : (realBlockHessian realDirections imagDirections u x).PosSemidef)
    (hdet : (complexHessian realDirections imagDirections u x).det = 1)
    (i j : Fin (n + n)) :
    |euclideanHessian u x i j| ≤ 4 * (complexHessian realDirections imagDirections u x).trace.re := by
  have hA := complexHessian_posDef_of_realBlockHessian hu realDirections imagDirections hR hdet
  have hmat : ((1 : ℝ) • complexHessian realDirections imagDirections u x -
      pureHessian realDirections imagDirections u x *
        ((complexHessian realDirections imagDirections u x).map star)⁻¹ *
          (pureHessian realDirections imagDirections u x).map star).PosSemidef := by
    rw [one_smul]
    change (schurHessian realDirections imagDirections u x).PosSemidef
    have heq := realBlockHessian_posSemidef_equivalences hu realDirections imagDirections hA
    exact heq.2.mp (heq.1.mp hR)
  have hb := realBlockHessian_entry_bound hu realDirections imagDirections hA
    (by norm_num : (0 : ℝ) ≤ 1) hmat (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)
  have heq := congrArg (fun M : Matrix (Fin (n + n)) (Fin (n + n)) ℝ => M i j)
    (realBlockHessian_reindex u x)
  change realBlockHessian realDirections imagDirections u x
    (finSumFinEquiv.symm i) (finSumFinEquiv.symm j) = euclideanHessian u x i j at heq
  rw [heq] at hb
  norm_num only [Real.sqrt_one] at hb
  linarith

end CHS.Sections
