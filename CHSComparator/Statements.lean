import CHS.Algebra.TraceFree
import CHS.Analysis.BlockCoordinates
import CHS.Calculus.BasisHessian
import CHS.Calculus.ClosureSchur
import CHS.Pogorelov.LinfEstimate
import CHS.Sections.Barrier

/-!
Explicit propositions for the frozen paper targets. Shared coordinate,
jet and norm definitions are imported at the file level.
-/

set_option autoImplicit false

open Set
open scoped BigOperators ComplexOrder ContDiff ENNReal

noncomputable section

namespace CHSComparator.Statements

def depthConstant (n : ℕ) : ℝ :=
  Real.sqrt ((32 * (n : ℝ) ^ 2)⁻¹ ^ (n - 1) / 2) / 16

def theorem_1_1 : Prop :=
  ∀ {n : ℕ},
  2 ≤ n →
    ∀ {κ : ℝ},
      1 ≤ κ →
        ∀ {U : Set (DeGiorgi.AmbientSpace (n + n))},
          IsOpen U →
            IsConnected U →
              ∀ {u : DeGiorgi.AmbientSpace (n + n) → ℝ},
                ContDiffOn ℝ 4 u U →
                  CHS.Calculus.C2OnClosure u U →
                    (∀ x ∈ U,
                        (CHS.Calculus.complexHessian CHS.Analysis.realDirections CHS.Analysis.imagDirections u x).det =
                          1) →
                      (∀ x ∈ frontier U, u x = 0) →
                        (∀ x ∈ U,
                            (κ •
                                  CHS.Calculus.complexHessian CHS.Analysis.realDirections CHS.Analysis.imagDirections u
                                    x -
                                CHS.Calculus.pureHessian CHS.Analysis.realDirections CHS.Analysis.imagDirections u x *
                                    ((CHS.Calculus.complexHessian CHS.Analysis.realDirections
                                            CHS.Analysis.imagDirections u x).map
                                        star)⁻¹ *
                                  (CHS.Calculus.pureHessian CHS.Analysis.realDirections CHS.Analysis.imagDirections u
                                        x).map
                                    star).PosSemidef) →
                          (Bornology.IsBounded U ∨
      ∃ K : Submodule ℝ (DeGiorgi.AmbientSpace (n + n)),
        (∀ x ∈ U, ∀ w ∈ K, x + w ∈ U) ∧
        (∀ x ∈ U, ∀ w ∈ K, u (x + w) = u x) ∧
        IsCompact ((Submodule.Quotient.mk : _ → _ ⧸ K) '' closure U)) →
                            (CHS.Analysis.entryLinfNormOn MeasureTheory.volume U fun x =>
                                (-u x) ^ CHS.Pogorelov.beta n κ • CHS.Analysis.euclideanHessian u x) ≤
                              32 * ↑n * CHS.Pogorelov.beta n κ * (1 + √κ) * Real.exp (1 / 8) *
                                  (1 +
                                    CHS.Pogorelov.gradientLinfNormOn MeasureTheory.volume CHS.Analysis.realDirections
                                        CHS.Analysis.imagDirections u U ^
                                      2) *
                                CHS.Pogorelov.scalarLinfNormOn MeasureTheory.volume U u ^ (CHS.Pogorelov.beta n κ - 1)

def theorem_1_2 : Prop :=
  ∀ {n : ℕ},
  2 ≤ n →
    ∀ {U : Set (DeGiorgi.AmbientSpace (n + n))},
      IsOpen U →
        Convex ℝ U →
          ∀ {u : DeGiorgi.AmbientSpace (n + n) → ℝ},
            ContDiffOn ℝ 4 u U →
              CHS.Calculus.C2OnClosure u U →
                (∀ x ∈ U,
                    (CHS.Calculus.complexHessian CHS.Analysis.realDirections CHS.Analysis.imagDirections u x).det = 1) →
                  (∀ x ∈ U,
                      (CHS.Calculus.realBlockHessian CHS.Analysis.realDirections CHS.Analysis.imagDirections u
                          x).PosSemidef) →
                    (∀ x ∈ frontier U, u x = 0) →
                      (Bornology.IsBounded U ∨
      ∃ K : Submodule ℝ (DeGiorgi.AmbientSpace (n + n)),
        (∀ x ∈ U, ∀ w ∈ K, CHS.Calculus.realHessian u x w = 0) ∧
        (∀ x ∈ U, ∀ w ∈ K, x + w ∈ U) ∧
        (∀ x ∈ U, ∀ w ∈ K, u (x + w) = u x) ∧
        IsCompact ((Submodule.Quotient.mk : _ → _ ⧸ K) '' closure U)) →
                        (CHS.Analysis.entryLinfNormOn MeasureTheory.volume U fun x =>
                            (-u x) ^ (4 * (n : ℝ)) • CHS.Analysis.euclideanHessian u x) ≤
                          256 * ↑n ^ 2 * Real.exp (1 / 8) *
                              (1 +
                                CHS.Pogorelov.gradientLinfNormOn MeasureTheory.volume CHS.Analysis.realDirections
                                    CHS.Analysis.imagDirections u U ^
                                  2) *
                            CHS.Pogorelov.scalarLinfNormOn MeasureTheory.volume U u ^ (4 * (n : ℝ) - 1)

def theorem_1_3 : Prop :=
  ∀ {n : ℕ},
  1 ≤ n →
    ∀ {u : DeGiorgi.AmbientSpace (n + n) → ℝ},
      ContDiff ℝ ∞ u →
        (∀ (x : DeGiorgi.AmbientSpace (n + n)),
            (CHS.Calculus.complexHessian CHS.Analysis.realDirections CHS.Analysis.imagDirections u x).det = 1) →
          (∀ (x : DeGiorgi.AmbientSpace (n + n)),
              (CHS.Calculus.realBlockHessian CHS.Analysis.realDirections CHS.Analysis.imagDirections u x).PosSemidef) →
            ∀ (x : DeGiorgi.AmbientSpace (n + n)),
              u x = u 0 + (fderiv ℝ u 0) x + 1 / 2 * ((CHS.Calculus.realHessian u 0) x) x

def corollary_1_4 : Prop :=
  ∀ {n : ℕ},
  1 ≤ n →
    ∀ {u : DeGiorgi.AmbientSpace (n + n) → ℝ},
      ContDiff ℝ ∞ u →
        (∀ (x : DeGiorgi.AmbientSpace (n + n)),
            (CHS.Calculus.complexHessian CHS.Analysis.realDirections CHS.Analysis.imagDirections u x).det = 1) →
          ∀ {K : Set (DeGiorgi.AmbientSpace (n + n))},
            IsCompact K →
              (∀ x ∉ K,
                  (CHS.Calculus.realBlockHessian CHS.Analysis.realDirections CHS.Analysis.imagDirections u
                      x).PosSemidef) →
                ∀ (x : DeGiorgi.AmbientSpace (n + n)),
                  u x = u 0 + (fderiv ℝ u 0) x + 1 / 2 * ((CHS.Calculus.realHessian u 0) x) x

def lemma_2_1 : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}
  [Fintype ι] [DecidableEq ι] {u : E → ℝ} {U : Set E},
  IsOpen U →
    ContDiffOn ℝ 4 u U →
      ∀ (a b : ι → E),
        (∀ y ∈ U, (CHS.Calculus.complexHessian a b u y).det = 1) →
          ∀ {x : E},
            x ∈ U →
              let A := CHS.Calculus.complexHessian a b u;
              let B := CHS.Calculus.pureHessian a b u;
              let H := fun y => (A y).map star;
              let C := fun y => (B y).map star;
              let W := (A x)⁻¹;
              let L := fun G =>
                CHS.SchurContractionCore.contract W fun p q =>
                  CHS.Calculus.matrixDZ (a q) (-b q) (CHS.Calculus.matrixDZ (a p) (b p) G) x;
              let first := fun G =>
                CHS.SchurContractionCore.contract W fun p q =>
                  CHS.Calculus.matrixDZ (a p) (b p) A x * W * CHS.Calculus.matrixDZ (a q) (-b q) G x;
              let second := fun G =>
                CHS.SchurContractionCore.contract W fun p q =>
                  CHS.Calculus.matrixDZ (a q) (-b q) B x * (H x)⁻¹ * CHS.Calculus.matrixDZ (a p) (b p) G x;
              L A = first A ∧
                L A = second C ∧
                  L B = first B ∧
                    L B = second H ∧
                      (CHS.SchurContractionCore.contract W fun p q =>
                          CHS.Calculus.matrixDZ (a q) (-b q) (CHS.Calculus.inverseDerivativeField a b H C p) x) =
                        0

def lemma_2_2_nonnegative : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {u : E → ℝ} {x : E},
  ContDiffAt ℝ 2 u x →
    ∀ (a b : ι → E),
      (CHS.Calculus.complexHessian a b u x).PosDef →
        ((CHS.Calculus.realBlockHessian a b u x).PosSemidef ↔ (CHS.Calculus.complexBlockHessian a b u x).PosSemidef) ∧
          ((CHS.Calculus.complexBlockHessian a b u x).PosSemidef ↔ (CHS.Calculus.schurHessian a b u x).PosSemidef)

def lemma_2_2_positive : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}
  [Fintype ι] [DecidableEq ι] {u : E → ℝ} {x : E},
  ContDiffAt ℝ 2 u x →
    ∀ (a b : ι → E),
      (CHS.Calculus.complexHessian a b u x).PosDef →
        ((CHS.Calculus.realBlockHessian a b u x).PosDef ↔ (CHS.Calculus.complexBlockHessian a b u x).PosDef) ∧
          ((CHS.Calculus.complexBlockHessian a b u x).PosDef ↔ (CHS.Calculus.schurHessian a b u x).PosDef)

def lemma_2_3_identity : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}
  [Fintype ι] [DecidableEq ι] {u : E → ℝ} {U : Set E},
  IsOpen U →
    ContDiffOn ℝ 4 u U →
      ∀ (a b : ι → E),
        (∀ y ∈ U, (CHS.Calculus.complexHessian a b u y).det = 1) →
          ∀ {x : E},
            x ∈ U →
              (CHS.SchurContractionCore.contract (CHS.Calculus.complexHessian a b u x)⁻¹ fun p q =>
                  CHS.Calculus.matrixDZ (a q) (-b q)
                    (CHS.Calculus.matrixDZ (a p) (b p) (CHS.Calculus.schurHessian a b u)) x) =
                -CHS.SchurContractionCore.contract (CHS.Calculus.complexHessian a b u x)⁻¹ fun p q =>
                    CHS.Calculus.compensatedHessian a b u p x * ((CHS.Calculus.complexHessian a b u x).map star)⁻¹ *
                      (CHS.Calculus.compensatedHessian a b u q x).conjTranspose

def lemma_2_3_nonpositive : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {u : E → ℝ} {U : Set E},
  IsOpen U →
    ContDiffOn ℝ 4 u U →
      ∀ (a b : ι → E),
        (∀ y ∈ U, (CHS.Calculus.complexHessian a b u y).det = 1) →
          ∀ {x : E},
            x ∈ U →
              (CHS.Calculus.complexHessian a b u x).PosDef →
                (-CHS.SchurContractionCore.contract (CHS.Calculus.complexHessian a b u x)⁻¹ fun p q =>
                      CHS.Calculus.matrixDZ (a q) (-b q)
                        (CHS.Calculus.matrixDZ (a p) (b p) (CHS.Calculus.schurHessian a b u)) x).PosSemidef

def proposition_2_4 : Prop :=
  ∀ {n : ℕ} [NeZero (n + n)],
  2 < ((n + n : ℕ) : ℝ) →
    ∀ {u : DeGiorgi.AmbientSpace (n + n) → ℝ} {U : Set (DeGiorgi.AmbientSpace (n + n))},
      IsOpen U →
        IsPreconnected U →
          IsCompact (closure U) →
            ContDiffOn ℝ 4 u U →
              ∀ (J : CHS.Calculus.ClosureC2Jet u U),
                (∀ x ∈ closure U, (J.complexField CHS.Analysis.realDirections CHS.Analysis.imagDirections x).PosDef) →
                  (∀ x ∈ closure U,
                      (J.complexField CHS.Analysis.realDirections CHS.Analysis.imagDirections x).det = 1) →
                    (∀ x ∈ frontier U,
                        (J.realField CHS.Analysis.realDirections CHS.Analysis.imagDirections x).PosSemidef) →
                      ∀ x ∈ closure U,
                        (J.realField CHS.Analysis.realDirections CHS.Analysis.imagDirections x).PosSemidef

def lemma_2_5 : Prop :=
  ∀ {n : ℕ} [NeZero (n + n)],
  2 < ((n + n : ℕ) : ℝ) →
    ∀ {u : DeGiorgi.AmbientSpace (n + n) → ℝ} {U : Set (DeGiorgi.AmbientSpace (n + n))},
      IsOpen U →
        IsPreconnected U →
          ContDiffOn ℝ 4 u U →
            (∀ y ∈ U,
                (CHS.Calculus.complexHessian CHS.Analysis.realDirections CHS.Analysis.imagDirections u y).det = 1) →
              (∀ y ∈ U,
                  (CHS.Calculus.realBlockHessian CHS.Analysis.realDirections CHS.Analysis.imagDirections u
                      y).PosSemidef) →
                ∀ {x y : DeGiorgi.AmbientSpace (n + n)},
                  x ∈ U →
                    y ∈ U →
                      (CHS.Calculus.schurHessian CHS.Analysis.realDirections CHS.Analysis.imagDirections u x).rank =
                          (CHS.Calculus.schurHessian CHS.Analysis.realDirections CHS.Analysis.imagDirections u y).rank ∧
                        (CHS.Calculus.realBlockHessian CHS.Analysis.realDirections CHS.Analysis.imagDirections u
                              x).rank =
                          (CHS.Calculus.realBlockHessian CHS.Analysis.realDirections CHS.Analysis.imagDirections u
                              y).rank

def lemma_2_6 : Prop :=
  ∀ {n : ℕ},
  2 ≤ n →
    ∀ (c : ℝ),
      0 ≤ c →
        ∀ (C : Matrix (Fin n) (Fin n) ℂ),
          C.trace = 0 →
            ∀ (e k : Fin n → ℂ),
              ‖WithLp.toLp 2 e‖ = 1 →
                ‖WithLp.toLp 2 k‖ ≤ 1 →
                  ‖WithLp.toLp 2 fun i => ↑c * C.mulVec e i + C.conjTranspose.mulVec k i‖ ^ 2 ≤
                    (c ^ 2 + ↑n - 1) * (C * C.conjTranspose).trace.re

def lemma_3_1 : Prop :=
  ∀ {n : ℕ},
  0 < n →
    ∀ {U : Set (DeGiorgi.AmbientSpace (n + n))},
      IsOpen U →
        Convex ℝ U →
          ∀ {u q : DeGiorgi.AmbientSpace (n + n) → ℝ},
            CHS.Calculus.C2OnClosure u U →
              (∀ x ∈ U,
                  (CHS.Calculus.realBlockHessian CHS.Analysis.realDirections CHS.Analysis.imagDirections u
                      x).PosSemidef) →
                (∀ x ∈ U, -1 ≤ u x ∧ u x < 0) →
                  (∀ x ∈ frontier U, u x = 0) →
                    (∀ x ∈ U,
                        (CHS.Calculus.complexHessian CHS.Analysis.realDirections CHS.Analysis.imagDirections u x).det =
                          1) →
                      ContinuousOn q (closure U) →
                        ContDiffOn ℝ 2 q U →
                          ConvexOn ℝ Set.univ q →
                            (∀ x ∈ closure U, 0 ≤ q x ∧ q x ≤ 4 * ↑n ^ 2) →
                              (∀ x ∈ U,
                                  (CHS.Calculus.complexHessian CHS.Analysis.realDirections CHS.Analysis.imagDirections q
                                        x -
                                      1).PosSemidef) →
                                (Bornology.IsBounded U ∨
      ∃ K : Submodule ℝ (DeGiorgi.AmbientSpace (n + n)),
        (∀ x ∈ U, ∀ w ∈ K, x + w ∈ U) ∧
        (∀ x ∈ U, ∀ w ∈ K, u (x + w) = u x) ∧
        (∀ x ∈ U, ∀ w ∈ K, q (x + w) = q x) ∧
        IsCompact ((Submodule.Quotient.mk : _ → _ ⧸ K) '' closure U)) →
                                  0 < depthConstant n ∧
                                    ∀ x ∈ U,
                                      u x ≤ -1 / 4 →
                                        depthConstant n ≤ Metric.infDist x (frontier U) ∧
                                          √(∑ i,
                                                ‖CHS.Sections.affineWirtinger CHS.Analysis.realDirections
                                                      CHS.Analysis.imagDirections (fderiv ℝ u x) i‖ ^
                                                  2) ≤
                                            (depthConstant n)⁻¹

def proposition_3_2 : Prop :=
  ∀ {n : ℕ},
  2 ≤ n →
    ∀ {u : DeGiorgi.AmbientSpace (n + n) → ℝ},
      ContDiff ℝ ∞ u →
        (∀ (x : DeGiorgi.AmbientSpace (n + n)),
            (CHS.Calculus.complexHessian CHS.Analysis.realDirections CHS.Analysis.imagDirections u x).det = 1) →
          (∀ (x : DeGiorgi.AmbientSpace (n + n)),
              (CHS.Calculus.realBlockHessian CHS.Analysis.realDirections CHS.Analysis.imagDirections u x).PosSemidef) →
            ∃ C,
              0 ≤ C ∧
                (∀ (x : DeGiorgi.AmbientSpace (n + n)) (i j : Fin (n + n)),
                    |CHS.Analysis.euclideanHessian u x i j| ≤ C) ∧
                  CHS.Analysis.entryLinfNormOn MeasureTheory.volume Set.univ (CHS.Analysis.euclideanHessian u) ≤ C ∧
                    ∀ (i j : Fin (n + n)),
                      MeasureTheory.eLpNorm (fun x => CHS.Analysis.euclideanHessian u x i j) ⊤ MeasureTheory.volume ≠ ⊤

end CHSComparator.Statements
