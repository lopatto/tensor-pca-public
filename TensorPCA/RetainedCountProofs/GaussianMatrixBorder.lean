-- SPDX-License-Identifier: Apache-2.0
/- Exact block-conjugation geometry adapted from immutable
   pmaronow/slowequilibration-palomar a28aaa336343c4caf43791ababd8ed0ee5c7b58e,
   Upstream/OAI/MathematicalPhysics/CriticalSK/GaussianMatrices.lean (upstream
   openai/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb). All maps are actual
   finite Euclidean isometries and matrices; no probability or asymptotic
   statement is postulated. See LICENSE. -/
module
public import TensorPCA.RetainedCountProofs.GaussianMatrixConjugation
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Module
open scoped BigOperators Topology RealInnerProductSpace
namespace TensorPCA.RetainedCountProofs.OAI.CriticalSK
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
def extendTailIsometry {n : ℕ}
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) where
  toFun x := WithLp.toLp 2 (Fin.cases (x 0) (U (WithLp.toLp 2 (fun i => x i.succ))))
  invFun x := WithLp.toLp 2 (Fin.cases (x 0) (U.symm (WithLp.toLp 2 (fun i => x i.succ))))
  left_inv x := by
    ext i
    cases i using Fin.cases with
    | zero => rfl
    | succ i => change U.symm (U (WithLp.toLp 2 (fun j => x j.succ))) i = x i.succ; simp
  right_inv x := by
    ext i
    cases i using Fin.cases with
    | zero => rfl
    | succ i => change U (U.symm (WithLp.toLp 2 (fun j => x j.succ))) i = x i.succ; simp
  map_add' x y := by
    ext i
    cases i using Fin.cases with
    | zero => rfl
    | succ i =>
      change U ((WithLp.toLp 2 (fun j => x j.succ)) + (WithLp.toLp 2 (fun j => y j.succ))) i = _
      simp
  map_smul' c x := by
    ext i
    cases i using Fin.cases with
    | zero => rfl
    | succ i =>
      change U (c • WithLp.toLp 2 (fun j => x j.succ)) i = _
      simp
  norm_map' x := by
    change ‖(WithLp.toLp 2 (Fin.cases (x 0) (U (WithLp.toLp 2 (fun i => x i.succ)))) : EuclideanSpace ℝ (Fin (n + 1)))‖ = ‖x‖
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    have h := congrArg (fun r : ℝ => r^2) (U.norm_map (WithLp.toLp 2 (fun j => x j.succ)))
    simp only [PiLp.norm_sq_eq_of_L2] at h ⊢
    simpa only [Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ, PiLp.toLp_apply] using
      congrArg (fun t : ℝ => ‖x 0‖ ^ 2 + t) h

@[simp] lemma extendTailIsometry_zero {n : ℕ}
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin (n + 1))) : extendTailIsometry U x 0 = x 0 := rfl

@[simp] lemma extendTailIsometry_succ {n : ℕ}
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin (n + 1))) (i : Fin n) :
    extendTailIsometry U x i.succ = U (WithLp.toLp 2 (fun j => x j.succ)) i := rfl

@[simp] lemma extendTailIsometry_basis_zero {n : ℕ}
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    extendTailIsometry U (EuclideanSpace.basisFun (Fin (n + 1)) ℝ 0) =
      EuclideanSpace.basisFun (Fin (n + 1)) ℝ 0 := by
  ext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
    simp only [extendTailIsometry_succ, EuclideanSpace.basisFun_apply]
    have h : (WithLp.toLp 2 fun j : Fin n => (EuclideanSpace.single 0 (1 : ℝ)) j.succ) = 0 := by
      ext j; simp
    rw [h, map_zero]
    simp

lemma extendTailIsometry_basis_succ {n : ℕ}
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) (k : Fin n) :
    extendTailIsometry U (EuclideanSpace.basisFun (Fin (n + 1)) ℝ k.succ) =
      WithLp.toLp 2 (Fin.cases 0 (U (EuclideanSpace.basisFun (Fin n) ℝ k))) := by
  ext i
  cases i using Fin.cases with
  | zero => simp
  | succ i =>
    simp only [extendTailIsometry_succ, Fin.cases_succ]
    apply congrArg (fun w : EuclideanSpace ℝ (Fin n) => U w i)
    ext j
    simp

def borderMatrix {n : ℕ} (a : ℝ) (v : EuclideanSpace ℝ (Fin n))
    (B : GaussianMatrix (Fin n)) : GaussianMatrix (Fin (n + 1)) :=
  WithLp.toLp 2 (Fin.cases (WithLp.toLp 2 (Fin.cases a v))
    (fun i => WithLp.toLp 2 (Fin.cases (v i) (B i))))

@[simp] lemma borderMatrix_zero_zero {n : ℕ} (a : ℝ) (v : EuclideanSpace ℝ (Fin n))
    (B : GaussianMatrix (Fin n)) : borderMatrix a v B 0 0 = a := rfl

@[simp] lemma borderMatrix_zero_succ {n : ℕ} (a : ℝ) (v : EuclideanSpace ℝ (Fin n))
    (B : GaussianMatrix (Fin n)) (i : Fin n) : borderMatrix a v B 0 i.succ = v i := rfl

@[simp] lemma borderMatrix_succ_zero {n : ℕ} (a : ℝ) (v : EuclideanSpace ℝ (Fin n))
    (B : GaussianMatrix (Fin n)) (i : Fin n) : borderMatrix a v B i.succ 0 = v i := rfl

@[simp] lemma borderMatrix_succ_succ {n : ℕ} (a : ℝ) (v : EuclideanSpace ℝ (Fin n))
    (B : GaussianMatrix (Fin n)) (i j : Fin n) : borderMatrix a v B i.succ j.succ = B i j := rfl

lemma extendTailIsometry_border {n : ℕ}
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (a : ℝ) (v : EuclideanSpace ℝ (Fin n)) (B : GaussianMatrix (Fin n)) :
    conjugateGaussianMatrix (extendTailIsometry U) (borderMatrix a v B) =
      borderMatrix a (U v) (conjugateGaussianMatrix U B) := by
  classical
  ext i j
  cases i using Fin.cases <;> cases j using Fin.cases
  all_goals simp only [conjugateGaussianMatrix_apply, Fin.sum_univ_succ]
  all_goals simp only [extendTailIsometry_basis_zero, extendTailIsometry_basis_succ]
  all_goals simp only [Fin.cases_zero, Fin.cases_succ,
    EuclideanSpace.basisFun_apply]
  all_goals simp only [PiLp.single_apply, Fin.succ_ne_zero,
    ite_true, ite_false, borderMatrix_zero_zero, borderMatrix_zero_succ,
    borderMatrix_succ_zero, borderMatrix_succ_succ, zero_mul, mul_zero,
    one_mul, mul_one, Finset.sum_const_zero, add_zero, zero_add]
  · simpa only [EuclideanSpace.basisFun_apply] using (euclidean_isometry_apply_eq_sum U v _).symm
  · rw [euclidean_isometry_apply_eq_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [EuclideanSpace.basisFun_apply, mul_comm]
  · simpa only [EuclideanSpace.basisFun_apply] using (conjugateGaussianMatrix_apply U B _ _).symm


end TensorPCA.RetainedCountProofs.OAI.CriticalSK
