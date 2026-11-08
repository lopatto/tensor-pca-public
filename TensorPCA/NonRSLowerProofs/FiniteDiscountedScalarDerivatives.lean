-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteDiscountedPartitionCoefficients
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Scalar derivatives needed by the discounted marked transform. These identities use
Mathlib's real power and logarithm, including their total definitions; the later
composition is evaluated at the positive point1.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteDiscountedScalarDerivatives
open scoped BigOperators
noncomputable section

theorem iteratedDeriv_rpow (a : ℝ) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun y : ℝ => y^a) x =
      (descPochhammer ℝ n).eval a*x^(a-(n : ℝ)) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have H : iteratedDeriv n (fun y : ℝ => y^a) =
        fun y : ℝ => (descPochhammer ℝ n).eval a*y^(a-(n : ℝ)) := funext ih
    rw [H,deriv_const_mul_field,Real.deriv_rpow_const,descPochhammer_succ_eval]
    simp only [Nat.cast_add,Nat.cast_one]
    rw [show a-(n : ℝ)-1=a-((n : ℝ)+1) by ring]
    ring

theorem iteratedDeriv_rpow_one (a : ℝ) (n : ℕ) :
    iteratedDeriv n (fun y : ℝ => y^a) 1 = (descPochhammer ℝ n).eval a := by
  simp [iteratedDeriv_rpow]

theorem descPochhammer_neg_one (n : ℕ) :
    (descPochhammer ℝ n).eval (-1) = (-1 : ℝ)^n*(n.factorial : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [descPochhammer_succ_eval,ih,pow_succ,Nat.factorial_succ]
    simp only [Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    ring

theorem iteratedDeriv_log_one (n : ℕ) :
    iteratedDeriv (n+1) Real.log 1 = (-1 : ℝ)^n*(n.factorial : ℝ) := by
  rw [iteratedDeriv_succ']
  have H : deriv Real.log = fun y : ℝ => y^(-1 : ℝ) := by
    funext y
    rw [Real.deriv_log,Real.rpow_neg_one]
  rw [H,iteratedDeriv_rpow_one,descPochhammer_neg_one]

theorem iteratedDeriv_log_div_one (alpha : ℝ) (n : ℕ) :
    iteratedDeriv (n+1) (fun y : ℝ => Real.log y/alpha) 1 =
      ((-1 : ℝ)^n*(n.factorial : ℝ))/alpha := by
  rw [iteratedDeriv_div_const,iteratedDeriv_log_one]

end
end TensorPCA.NonRSLowerProofs.FiniteDiscountedScalarDerivatives
