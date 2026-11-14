import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Independent statements of CHS Theorems 1.1–1.3 and Corollary 1.4

Identify ℂⁿ with Euclidean ℝ²ⁿ in the order (real coordinates, imaginary
coordinates). The matrices below use the usual factors 1/2 in each
Wirtinger derivative. The scalar and entrywise norms use Lebesgue measure.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped BigOperators ComplexOrder ContDiff ENNReal

noncomputable section

namespace CHSComparator.MathlibOnly.Statements

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin (n + n))

variable {n : ℕ}

def realDirection (i : Fin n) : Space n :=
  EuclideanSpace.single (finSumFinEquiv (Sum.inl i)) 1

def imagDirection (i : Fin n) : Space n :=
  EuclideanSpace.single (finSumFinEquiv (Sum.inr i)) 1

/-- The second Fréchet derivative, viewed as a continuous bilinear form. -/
def hessian (u : Space n → ℝ) (x : Space n) :
    Space n →L[ℝ] Space n →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ u) x

/-- The mixed complex Hessian, with entry ∂²u/∂zᵢ∂z̄ⱼ. -/
def mixedHessian (u : Space n → ℝ) (x : Space n) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j =>
    (4 : ℂ)⁻¹ *
      ((hessian u x (realDirection i) (realDirection j) : ℂ) +
        (hessian u x (imagDirection i) (imagDirection j) : ℂ) +
        Complex.I * ((hessian u x (realDirection i) (imagDirection j) : ℂ) -
          (hessian u x (imagDirection i) (realDirection j) : ℂ)))

/-- The pure complex Hessian, with entry ∂²u/∂zᵢ∂zⱼ. -/
def pureHessian (u : Space n → ℝ) (x : Space n) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j =>
    (4 : ℂ)⁻¹ *
      ((hessian u x (realDirection i) (realDirection j) : ℂ) -
        (hessian u x (imagDirection i) (imagDirection j) : ℂ) -
        Complex.I * ((hessian u x (realDirection i) (imagDirection j) : ℂ) +
          (hessian u x (imagDirection i) (realDirection j) : ℂ)))

/-- The real Hessian indexed by the real and imaginary blocks of the basis. -/
def realHessianMatrix (u : Space n → ℝ) (x : Space n) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  fun i j => hessian u x (Sum.elim realDirection imagDirection i)
    (Sum.elim realDirection imagDirection j)

def coordinateHessian (u : Space n → ℝ) (x : Space n) :
    Matrix (Fin (n + n)) (Fin (n + n)) ℝ :=
  fun i j => hessian u x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)

/-- C² up to the boundary. The derivatives on U extend continuously to its closure. -/
def C2OnClosure (u : Space n → ℝ) (U : Set (Space n)) : Prop :=
  ContDiffOn ℝ 2 u U ∧ ContinuousOn u (closure U) ∧
    ∃ (D : Space n → Space n →L[ℝ] ℝ) (H : Space n → Space n →L[ℝ] Space n →L[ℝ] ℝ),
      ContinuousOn D (closure U) ∧ ContinuousOn H (closure U) ∧
        EqOn D (fderiv ℝ u) U ∧ EqOn H (hessian u) U

def scalarLinf (U : Set (Space n)) (f : Space n → ℝ) : ℝ :=
  (eLpNorm f ∞ (volume.restrict U)).toReal

def gradientNormSq (u : Space n → ℝ) (x : Space n) : ℝ :=
  ∑ i : Fin n, Complex.normSq
    ((2 : ℂ)⁻¹ * ((fderiv ℝ u x (realDirection i) : ℂ) -
      Complex.I * (fderiv ℝ u x (imagDirection i) : ℂ)))

def gradientLinf (U : Set (Space n)) (u : Space n → ℝ) : ℝ :=
  scalarLinf U (fun x => Real.sqrt (gradientNormSq u x))

def weightedHessianLinf (U : Set (Space n)) (u : Space n → ℝ) (γ : ℝ) : ℝ :=
  sSup (insert 0 (range fun p : Fin (n + n) × Fin (n + n) =>
    scalarLinf U (fun x => (-u x) ^ γ * coordinateHessian u x p.1 p.2)))

def invariantWithCompactQuotient (U : Set (Space n)) (u : Space n → ℝ)
    (K : Submodule ℝ (Space n)) : Prop :=
  (∀ x ∈ U, ∀ w ∈ K, x + w ∈ U) ∧
  (∀ x ∈ U, ∀ w ∈ K, u (x + w) = u x) ∧
  IsCompact ((Submodule.Quotient.mk : Space n → Space n ⧸ K) '' closure U)

def beta (n : ℕ) (κ : ℝ) : ℝ := (4 * (n : ℝ) - 2) * κ + 2

def theorem_1_1 : Prop :=
  ∀ {n : ℕ}, 2 ≤ n →
  ∀ {κ : ℝ}, 1 ≤ κ →
  ∀ {U : Set (Space n)}, IsOpen U → IsConnected U →
  ∀ {u : Space n → ℝ}, ContDiffOn ℝ 4 u U → C2OnClosure u U →
    (∀ x ∈ U, (mixedHessian u x).det = 1) →
    (∀ x ∈ frontier U, u x = 0) →
    (∀ x ∈ U, (κ • mixedHessian u x -
      pureHessian u x * ((mixedHessian u x).map star)⁻¹ *
        (pureHessian u x).map star).PosSemidef) →
    (Bornology.IsBounded U ∨ ∃ K, invariantWithCompactQuotient U u K) →
    weightedHessianLinf U u (beta n κ) ≤
      32 * (n : ℝ) * beta n κ * (1 + Real.sqrt κ) * Real.exp (1 / 8) *
        (1 + gradientLinf U u ^ 2) * scalarLinf U u ^ (beta n κ - 1)

def theorem_1_2 : Prop :=
  ∀ {n : ℕ}, 2 ≤ n →
  ∀ {U : Set (Space n)}, IsOpen U → Convex ℝ U →
  ∀ {u : Space n → ℝ}, ContDiffOn ℝ 4 u U → C2OnClosure u U →
    (∀ x ∈ U, (mixedHessian u x).det = 1) →
    (∀ x ∈ U, (realHessianMatrix u x).PosSemidef) →
    (∀ x ∈ frontier U, u x = 0) →
    (Bornology.IsBounded U ∨ ∃ K : Submodule ℝ (Space n),
      (∀ x ∈ U, ∀ w ∈ K, hessian u x w = 0) ∧ invariantWithCompactQuotient U u K) →
    weightedHessianLinf U u (4 * (n : ℝ)) ≤
      256 * (n : ℝ) ^ 2 * Real.exp (1 / 8) *
        (1 + gradientLinf U u ^ 2) * scalarLinf U u ^ (4 * (n : ℝ) - 1)

def theorem_1_3 : Prop :=
  ∀ {n : ℕ}, 1 ≤ n →
  ∀ {u : Space n → ℝ}, ContDiff ℝ ∞ u →
    (∀ x, (mixedHessian u x).det = 1) →
    (∀ x, (realHessianMatrix u x).PosSemidef) →
    ∀ x, u x = u 0 + fderiv ℝ u 0 x + 1 / 2 * hessian u 0 x x

def corollary_1_4 : Prop :=
  ∀ {n : ℕ}, 1 ≤ n →
  ∀ {u : Space n → ℝ}, ContDiff ℝ ∞ u →
    (∀ x, (mixedHessian u x).det = 1) →
    ∀ {K : Set (Space n)}, IsCompact K →
      (∀ x ∉ K, (realHessianMatrix u x).PosSemidef) →
      ∀ x, u x = u 0 + fderiv ℝ u 0 x + 1 / 2 * hessian u 0 x x

end CHSComparator.MathlibOnly.Statements
