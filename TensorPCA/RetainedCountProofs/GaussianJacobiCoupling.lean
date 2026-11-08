-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
/- The two elementary measurability proofs below follow immutable
   pmaronow/slowequilibration-palomar a28aaa336343c4caf43791ababd8ed0ee5c7b58e,
   GaussianMatrices.lean (upstream openai/math
   fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb). The coupling arguments use
   actual Householder matrices and their actual Gaussian marginal laws;
   no empirical spectral limit or comparison premise is assumed. See LICENSE. -/
module
public import TensorPCA.RetainedCountProofs.GaussianTridiagonalGeometry
public import TensorPCA.RetainedCountProofs.JacobiPolynomials
public import Mathlib.Probability.HasLaw
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Module
open scoped BigOperators Topology RealInnerProductSpace
namespace TensorPCA.RetainedCountProofs.OAI.CriticalSK
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
lemma borderMatrix_measurable (n : ℕ) :
    Measurable (fun p : ℝ × (EuclideanSpace ℝ (Fin n) × GaussianMatrix (Fin n)) =>
      borderMatrix p.1 p.2.1 p.2.2) := by
  apply (WithLp.measurable_toLp _ _).comp
  apply Measurable.of_eval
  intro i
  apply (WithLp.measurable_toLp _ _).comp
  apply Measurable.of_eval
  intro j
  change Measurable (fun p : ℝ × (EuclideanSpace ℝ (Fin n) × GaussianMatrix (Fin n)) =>
    borderMatrix p.1 p.2.1 p.2.2 i j)
  cases i using Fin.cases <;> cases j using Fin.cases
  all_goals simp only [borderMatrix_zero_zero, borderMatrix_zero_succ,
    borderMatrix_succ_zero, borderMatrix_succ_succ]
  all_goals fun_prop

lemma triReduce_measurable (n : ℕ) : Measurable (triReduce n) := by
  induction n with
  | zero => exact measurable_id
  | succ n ih =>
    exact (borderMatrix_measurable n).comp
      ((by fun_prop : Measurable fun A : GaussianMatrix (Fin (n+1)) => A 0 0).prodMk
        (((firstColumn_measurable n).norm.smul measurable_const).prodMk
          (ih.comp (reducedTail_measurable n))))

lemma borderMatrix_sub {m : ℕ} (a b : ℝ)
    (v w : EuclideanSpace ℝ (Fin m)) (B C : GaussianMatrix (Fin m)) :
    borderMatrix a v B - borderMatrix b w C = borderMatrix (a-b) (v-w) (B-C) := by
  ext i j
  cases i using Fin.cases <;> cases j using Fin.cases <;> rfl

lemma norm_borderMatrix_sq {m : ℕ} (a : ℝ) (v : EuclideanSpace ℝ (Fin m))
    (B : GaussianMatrix (Fin m)) :
    ‖borderMatrix a v B‖ ^ 2 = a^2 + 2*‖v‖^2 + ‖B‖^2 := by
  simp only [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ, borderMatrix_zero_zero,
    borderMatrix_zero_succ, borderMatrix_succ_zero, borderMatrix_succ_succ,
    Real.norm_eq_abs, sq_abs, Finset.sum_add_distrib]
  ring

lemma firstAxis_norm_le_one (m : ℕ) : ‖firstAxis m‖ ≤ 1 := by
  cases m with
  | zero =>
    have hz : firstAxis 0 = 0 := Subsingleton.elim _ _
    simp only [hz, norm_zero, zero_le_one]
  | succ m => exact (firstAxis_norm_succ m).le

def jacobiGaussian (a : ℝ) (m : ℕ) : GaussianMatrix (Fin m) :=
  GOEAsymptotics.matrixToGaussian (JacobiMatrix.jacobi a m)

lemma jacobiGaussian_border (a : ℝ) (m : ℕ) :
    jacobiGaussian a (m+1) =
      borderMatrix 0 (Real.sqrt (a*(m:ℝ)) • firstAxis m) (jacobiGaussian a m) := by
  have hrow (j : Fin m) : JacobiMatrix.jacobi a (m+1) 0 j.succ =
      Real.sqrt (a*(m:ℝ)) * firstAxis m j := by
    have hz : (1 = j.val+1) ↔ j.val=0 := by omega
    simp only [JacobiMatrix.jacobi, Fin.val_zero, Fin.val_succ, zero_add,
      Nat.cast_add, Nat.cast_one, hz, show ¬(j.val+1+1=0) by omega, ite_false]
    simp only [firstAxis, PiLp.toLp_apply]
    split_ifs <;> simp only [mul_one, mul_zero]
    congr 1
    ring
  ext i j
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => exact JacobiMatrix.jacobi_diagonal a (m+1) 0
    | succ j => exact hrow j
  | succ i =>
    cases j using Fin.cases with
    | zero =>
      change JacobiMatrix.jacobi a (m+1) i.succ 0 = Real.sqrt (a*(m:ℝ)) * firstAxis m i
      have hs := congrArg (fun M : Matrix (Fin (m+1)) (Fin (m+1)) ℝ => M i.succ 0)
        (JacobiMatrix.jacobi_symmetric a (m+1))
      exact hs.symm.trans (hrow i)
    | succ j => exact congrFun (congrFun (JacobiMatrix.jacobi_tail a m) i) j

def jacobiSquaredError (a : ℝ) (m : ℕ) (A : GaussianMatrix (Fin m)) : ℝ :=
  ‖triReduce m A - jacobiGaussian a m‖ ^ 2

lemma jacobiSquaredError_measurable (a : ℝ) (m : ℕ) :
    Measurable (jacobiSquaredError a m) := by
  unfold jacobiSquaredError
  exact ((triReduce_measurable m).sub measurable_const).norm.pow_const 2

lemma jacobiSquaredError_succ_le (a : ℝ) (m : ℕ) (A : GaussianMatrix (Fin (m+1))) :
    jacobiSquaredError a (m+1) A ≤
      (A 0 0)^2 + 2*(‖firstColumn A‖ - Real.sqrt (a*(m:ℝ)))^2 +
        jacobiSquaredError a m (reducedTail A) := by
  have haxis : ‖firstAxis m‖ ^ 2 ≤ 1 := by
    nlinarith [firstAxis_norm_le_one m, norm_nonneg (firstAxis m)]
  have hv : ‖‖firstColumn A‖ • firstAxis m -
      Real.sqrt (a*(m:ℝ)) • firstAxis m‖ ^ 2 ≤
        (‖firstColumn A‖ - Real.sqrt (a*(m:ℝ))) ^ 2 := by
    rw [← sub_smul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    exact (mul_le_mul_of_nonneg_left haxis (sq_nonneg _)).trans_eq (mul_one _)
  unfold jacobiSquaredError
  rw [triReduce, jacobiGaussian_border, borderMatrix_sub, norm_borderMatrix_sq, sub_zero]
  nlinarith

end TensorPCA.RetainedCountProofs.OAI.CriticalSK
