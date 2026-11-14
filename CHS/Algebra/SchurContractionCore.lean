import CHS.CoreImports

/-!
# Noncommutative contraction algebra for the Schur-Hessian identity

S005 candidate source, not compiled in Chat. This module imports only Mathlib.
It proves algebraic identities and cancellation rules, NOT paper Lemma 2.3.
In the calculus bridge, the arrays below are replaced by actual derivatives;
the differentiated Monge-Ampere identities remain separate proof obligations.
The coefficient order is exactly W q p, not W p q.
-/

set_option autoImplicit false
open scoped BigOperators

namespace CHS.SchurContractionCore

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Matrix-valued contraction with the inverse-Hessian index order. -/
noncomputable def contract (W : Matrix ι ι ℂ)
    (F : ι → ι → Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  ∑ p, ∑ q, W q p • F p q

lemma contract_sub (W : Matrix ι ι ℂ) (F G : ι → ι → Matrix ι ι ℂ) :
    contract W (fun p q => F p q - G p q) = contract W F - contract W G := by
  simp only [contract, smul_sub, Finset.sum_sub_distrib]

lemma contract_mul_right (W : Matrix ι ι ℂ)
    (F : ι → ι → Matrix ι ι ℂ) (R : Matrix ι ι ℂ) :
    contract W (fun p q => F p q * R) = contract W F * R := by
  simp only [contract, Finset.sum_mul, Matrix.smul_mul]

lemma contract_mul_left (W : Matrix ι ι ℂ)
    (B : Matrix ι ι ℂ) (F : ι → ι → Matrix ι ι ℂ) :
    contract W (fun p q => B * F p q) = B * contract W F := by
  simp only [contract, Finset.mul_sum, Matrix.mul_smul]

/-- Derivative of an inverse follows from the differentiated product,
provided K is an actual left inverse. -/
lemma inverse_derivative_of_product_zero
    (H K dH dK : Matrix ι ι ℂ) (hKH : K * H = 1)
    (hproduct : dH * K + H * dK = 0) :
    dK = -(K * dH * K) := by
  have hright : H * dK = -(dH * K) := by
    calc
      H * dK = (dH * K + H * dK) - dH * K := by abel
      _ = -(dH * K) := by rw [hproduct]; simp
  calc
    dK = K * (H * dK) := by rw [← mul_assoc, hKH, one_mul]
    _ = K * (-(dH * K)) := by rw [hright]
    _ = -(K * dH * K) := by simp only [mul_neg, mul_assoc]

/-- The first Schur derivative is a genuine noncommutative polynomial identity. -/
lemma schur_first_derivative_algebra
    (A₁ B C K B₁ C₁ H₁ K₁ : Matrix ι ι ℂ)
    (hK₁ : K₁ = -(K * H₁ * K)) :
    A₁ - ((B₁ * K + B * K₁) * C + (B * K) * C₁) =
      A₁ - ((B₁ - B * K * H₁) * K) * C - B * K * C₁ := by
  rw [hK₁]
  noncomm_ring

/-- The compensated divergence vanishes after two independently stated
contractions cancel. No Schur-Hessian conclusion is assumed here. -/
lemma compensated_contraction_cancel
    (W B : Matrix ι ι ℂ) (dB Q : ι → Matrix ι ι ℂ)
    (d₂B dQ : ι → ι → Matrix ι ι ℂ)
    (hB : contract W d₂B = contract W (fun p q => dB q * Q p))
    (hQ : contract W dQ = 0) :
    contract W (fun p q => d₂B p q - dB q * Q p - B * dQ p q) = 0 := by
  simp only [contract_sub, contract_mul_left, hB, hQ, mul_zero, sub_self, sub_zero]

/-- Algebraic last step of the paper's LM calculation. Each hypothesis is a
separate differential contraction to be proved from the actual PDE upstream. -/
lemma schur_contraction_cancel
    (W B K R : Matrix ι ι ℂ)
    (E dB T dR : ι → Matrix ι ι ℂ)
    (d₂A dE dT : ι → ι → Matrix ι ι ℂ)
    (hA : contract W d₂A = contract W (fun p q => dB q * T p))
    (hE : contract W dE = 0) (hT : contract W dT = 0)
    (hR : ∀ q, dR q = K * (E q).conjTranspose) :
    contract W (fun p q =>
      d₂A p q - dE p q * R - E p * dR q - dB q * T p - B * dT p q) =
      -contract W (fun p q => E p * K * (E q).conjTranspose) := by
  have hreturn : contract W (fun p q => E p * dR q) =
      contract W (fun p q => E p * K * (E q).conjTranspose) := by
    simp only [hR, mul_assoc]
  simp only [contract_sub, contract_mul_right, contract_mul_left,
    hE, hT, zero_mul, mul_zero, sub_zero]
  rw [hA, hreturn]
  abel

end CHS.SchurContractionCore
