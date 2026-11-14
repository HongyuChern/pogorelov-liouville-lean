-- CHS modification (2026-11-14): adjust Mathlib imports for the pinned build.
-- Modified 2026-04-28: updated internal import paths for project namespace
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Common Prelude

This module is the shared prelude for the De Giorgi development.

Policy:

- imports come directly from `Mathlib`;
- declarations in this directory live under `DeGiorgi`;
- shared opens and scoped notations live here so the theorem files stay small.
-/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace DeGiorgi

end DeGiorgi
