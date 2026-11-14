import DifferentialGeometry.External.DeGiorgi.ScaledBallEstimates
import DifferentialGeometry.External.DeGiorgi.StrongMinimum

/-!
CHS dependency probe v2. Only types and transitive axioms are queried.
This file proves no CHS paper theorem. Fresh Lean compilation has not yet run.
The linear Holder theorem is deliberately not a dependency of this core probe.
-/

set_option pp.universes true
set_option pp.explicit true

#check @DeGiorgi.weak_harnack
#check @DeGiorgi.weak_harnack_on_ball
#check @DeGiorgi.IsSupersolution.eq_zero_on_unit_quarter_ball
#check @DeGiorgi.IsSupersolution.eq_zero_on_quarter_ball

#print axioms DeGiorgi.weak_harnack
#print axioms DeGiorgi.weak_harnack_on_ball
#print axioms DeGiorgi.IsSupersolution.eq_zero_on_unit_quarter_ball
#print axioms DeGiorgi.IsSupersolution.eq_zero_on_quarter_ball

#print DeGiorgi.EllipticCoeff
#print DeGiorgi.NormalizedEllipticCoeff
#print DeGiorgi.IsSupersolution
