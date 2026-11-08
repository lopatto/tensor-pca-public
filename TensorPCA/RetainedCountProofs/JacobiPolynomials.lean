-- SPDX-License-Identifier: Apache-2.0
/- Attributed deterministic Jacobi/Hermite source proof from
   pmaronow/slowequilibration-palomar a28aaa336343c4caf43791ababd8ed0ee5c7b58e,
   Upstream/OAI/MathematicalPhysics/CriticalSK/PathSpectra.lean, originally
   openai/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Only the genuine
   tridiagonal matrix, characteristic polynomial and Hermite identities are
   retained; no random-matrix or asymptotic theorem is assumed. See LICENSE. -/
module
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
@[expose] public section
noncomputable section
open Matrix Polynomial
open scoped BigOperators Topology
namespace TensorPCA.RetainedCountProofs.JacobiMatrix
set_option backward.isDefEq.respectTransparency false
def scaledHermite (a : ℝ) : ℕ → Polynomial ℝ
  | 0 => 1
  | k + 1 => X * scaledHermite a k - C a * derivative (scaledHermite a k)

@[simp] lemma scaledHermite_zero (a : ℝ) : scaledHermite a 0 = 1 := rfl

lemma scaledHermite_succ (a : ℝ) (k : ℕ) :
    scaledHermite a (k + 1) = X * scaledHermite a k - C a * derivative (scaledHermite a k) := rfl

lemma derivative_scaledHermite_succ (a : ℝ) (k : ℕ) :
    derivative (scaledHermite a (k + 1)) = C (k + 1 : ℝ) * scaledHermite a k := by
  induction k with
  | zero => simp [scaledHermite]
  | succ k ih =>
    rw [scaledHermite_succ a (k + 1), derivative_sub, derivative_mul, derivative_X,
      one_mul, ih, derivative_mul, derivative_C, zero_mul, zero_add]
    rw [derivative_mul, derivative_C, zero_mul, zero_add]
    rw [scaledHermite_succ a k]
    simp only [Nat.cast_add, Nat.cast_one, map_add, map_one]
    ring

lemma scaledHermite_three_term (a : ℝ) (k : ℕ) :
    scaledHermite a (k + 2) = X * scaledHermite a (k + 1) -
      C (a * (k + 1)) * scaledHermite a k := by
  rw [show k + 2 = (k + 1) + 1 by omega, scaledHermite_succ,
    derivative_scaledHermite_succ, map_mul, mul_assoc]

lemma scaledHermite_differential (a : ℝ) (k : ℕ) :
    C a * derivative (derivative (scaledHermite a k)) -
      X * derivative (scaledHermite a k) + C (k : ℝ) * scaledHermite a k = 0 := by
  have h := derivative_scaledHermite_succ a k
  rw [scaledHermite_succ, derivative_sub, derivative_mul, derivative_X,
    one_mul, derivative_mul, derivative_C, zero_mul, zero_add] at h
  simp only [map_add, map_one] at h
  linear_combination -h

lemma scaledHermite_degree_gap (a : ℝ) (p : Polynomial ℝ) (hp : p ≠ 0) :
    (C a * derivative p).degree < (X * p).degree := by
  by_cases ha : a = 0
  · simp only [ha, map_zero, zero_mul, degree_zero]
    exact degree_ne_bot.mpr (mul_ne_zero X_ne_zero hp) |>.bot_lt
  · rw [degree_C_mul ha, mul_comm X p]
    exact degree_derivative_le.trans_lt (degree_lt_degree_mul_X hp)

lemma scaledHermite_monic (a : ℝ) (k : ℕ) : (scaledHermite a k).Monic := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [scaledHermite_succ]
    exact (monic_X.mul ih).sub_of_left (scaledHermite_degree_gap a _ ih.ne_zero)

lemma scaledHermite_degree (a : ℝ) (k : ℕ) : (scaledHermite a k).degree = k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [scaledHermite_succ, degree_sub_eq_left_of_degree_lt
      (scaledHermite_degree_gap a _ (scaledHermite_monic a k).ne_zero), mul_comm X _,
      degree_mul_X, ih]
    norm_cast

lemma det_tridiagonal_step {R : Type*} [CommRing R] (k : ℕ)
    (A : Matrix (Fin (k + 2)) (Fin (k + 2)) R)
    (hrow : ∀ j : Fin k, A 0 j.succ.succ = 0)
    (hcol : ∀ i : Fin k, A i.succ.succ 0 = 0) :
    A.det = A 0 0 * (A.submatrix Fin.succ Fin.succ).det -
      A 0 1 * A 1 0 * (A.submatrix (Fin.succ ∘ Fin.succ) (Fin.succ ∘ Fin.succ)).det := by
  have hminor : (A.submatrix Fin.succ (1 : Fin (k + 2)).succAbove).det =
      A 1 0 * (A.submatrix (Fin.succ ∘ Fin.succ) (Fin.succ ∘ Fin.succ)).det := by
    rw [det_succ_column_zero, Fin.sum_univ_succ]
    simp only [Matrix.submatrix_apply, Fin.val_zero, pow_zero, one_mul,
      Fin.succ_zero_eq_one, Fin.one_succAbove_zero, hcol, mul_zero, zero_mul,
      Finset.sum_const_zero, add_zero, submatrix_submatrix, Fin.succAbove_zero]
    congr 2
  rw [det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero, Fin.val_succ,
    Fin.succ_zero_eq_one, hminor, hrow, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero, Fin.val_one, pow_one, neg_one_mul]
  ring

def jacobi (a : ℝ) (k : ℕ) : Matrix (Fin k) (Fin k) ℝ := fun i j =>
  if i.val + 1 = j.val then Real.sqrt (a * ((k : ℝ) - 1 - i.val))
  else if j.val + 1 = i.val then Real.sqrt (a * ((k : ℝ) - 1 - j.val)) else 0

lemma jacobi_diagonal (a : ℝ) (k : ℕ) (i : Fin k) : jacobi a k i i = 0 := by
  simp [jacobi]

lemma jacobi_symmetric (a : ℝ) (k : ℕ) : (jacobi a k).IsSymm := by
  ext i j
  dsimp [jacobi, Matrix.transpose]
  split_ifs with h₁ h₂ h₃ <;> first | rfl | omega

lemma jacobi_tail (a : ℝ) (k : ℕ) :
    (jacobi a (k + 1)).submatrix Fin.succ Fin.succ = jacobi a k := by
  ext i j
  simp only [Matrix.submatrix_apply, jacobi, Fin.val_succ, Nat.add_right_cancel_iff,
    Nat.cast_add, Nat.cast_one]
  split_ifs <;> congr 1 <;> ring

lemma jacobi_row_zero (a : ℝ) (k : ℕ) (j : Fin k) : jacobi a (k + 2) 0 j.succ.succ = 0 := by
  simp [jacobi]

lemma jacobi_col_zero (a : ℝ) (k : ℕ) (i : Fin k) : jacobi a (k + 2) i.succ.succ 0 = 0 := by
  simp [jacobi]

lemma jacobi_first_super (a : ℝ) (k : ℕ) :
    jacobi a (k + 2) 0 1 = Real.sqrt (a * (k + 1)) := by
  simp [jacobi]
  congr 1
  ring

lemma jacobi_first_sub (a : ℝ) (k : ℕ) :
    jacobi a (k + 2) 1 0 = Real.sqrt (a * (k + 1)) := by
  simp [jacobi]
  congr 1
  ring

lemma charmatrix_jacobi_tail (a : ℝ) (k : ℕ) :
    ((jacobi a (k + 1)).charmatrix).submatrix Fin.succ Fin.succ =
      (jacobi a k).charmatrix := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [jacobi_diagonal]
  · simp [hij, charmatrix_apply_ne, ← jacobi_tail a k]

lemma jacobi_charpoly_step {a : ℝ} (ha : 0 ≤ a) (k : ℕ) :
    (jacobi a (k + 2)).charpoly = X * (jacobi a (k + 1)).charpoly -
      C (a * (k + 1)) * (jacobi a k).charpoly := by
  have hr (j : Fin k) : (jacobi a (k + 2)).charmatrix 0 j.succ.succ = 0 := by
    rw [charmatrix_apply_ne _ _ _ (by simp only [ne_eq, Fin.ext_iff, Fin.val_zero, Fin.val_succ]; omega), jacobi_row_zero]
    simp
  have hc (i : Fin k) : (jacobi a (k + 2)).charmatrix i.succ.succ 0 = 0 := by
    rw [charmatrix_apply_ne _ _ _ (by simp only [ne_eq, Fin.ext_iff, Fin.val_zero, Fin.val_succ]; omega), jacobi_col_zero]
    simp
  unfold Matrix.charpoly
  rw [det_tridiagonal_step k _ hr hc, charmatrix_apply_eq, jacobi_diagonal,
    map_zero, sub_zero, charmatrix_jacobi_tail,
    charmatrix_apply_ne _ _ _ (by simp only [ne_eq, Fin.ext_iff, Fin.val_zero, Fin.val_one]; omega : (0 : Fin (k + 2)) ≠ 1),
    charmatrix_apply_ne _ _ _ (by simp only [ne_eq, Fin.ext_iff, Fin.val_zero, Fin.val_one]; omega : (1 : Fin (k + 2)) ≠ 0),
    jacobi_first_super, jacobi_first_sub, neg_mul_neg, ← map_mul,
    ← sq, Real.sq_sqrt (by positivity)]
  congr 2
  rw [← submatrix_submatrix, charmatrix_jacobi_tail, charmatrix_jacobi_tail]

lemma jacobi_charpoly {a : ℝ} (ha : 0 ≤ a) (k : ℕ) :
    (jacobi a k).charpoly = scaledHermite a k := by
  induction k using Nat.twoStepInduction with
  | zero => simp
  | one =>
    have hz : jacobi a 1 = 0 := by ext i j; fin_cases i; fin_cases j; simp [jacobi]
    simp [hz, scaledHermite]
  | more k h0 h1 => rw [jacobi_charpoly_step ha, h0, h1, scaledHermite_three_term]


end TensorPCA.RetainedCountProofs.JacobiMatrix
