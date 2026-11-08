-- SPDX-License-Identifier: Apache-2.0
/- Exact finite Householder tridiagonalization adapted from immutable
   pmaronow/slowequilibration-palomar a28aaa336343c4caf43791ababd8ed0ee5c7b58e,
   Upstream/OAI/MathematicalPhysics/CriticalSK/GaussianMatrices.lean and
   GOESpectrum.lean (upstream openai/math
   fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb). We reuse the existing genuine
   Gaussian-to-Mathlib matrix map and actual self-adjoint eigenvalues.
   No empirical or edge limit is assumed. See LICENSE. -/
module
public import TensorPCA.RetainedCountProofs.GaussianMatrixBlocks
public import TensorPCA.RetainedCountProofs.GaussianMatrixSpectralTools
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Module Matrix Polynomial
open scoped BigOperators Topology RealInnerProductSpace
namespace TensorPCA.RetainedCountProofs.OAI.CriticalSK
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
section
variable {n : ℕ}
def orthoMatrix (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => U (EuclideanSpace.basisFun (Fin n) ℝ j) i

lemma gaussianToMatrix_injective : Function.Injective (GOEAsymptotics.gaussianToMatrix (k := n)) := by
  intro A B h
  ext i j
  exact congrFun (congrFun h i) j

lemma orthoMatrix_trans (U V : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    orthoMatrix (U.trans V) = orthoMatrix V * orthoMatrix U := by
  ext i j
  change V (U (EuclideanSpace.basisFun (Fin n) ℝ j)) i = _
  rw [euclidean_isometry_apply_eq_sum]
  simp only [Matrix.mul_apply, orthoMatrix]
  apply Finset.sum_congr rfl
  intros
  ring

lemma gaussianToMatrix_conjugate (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (A : GaussianMatrix (Fin n)) :
    GOEAsymptotics.gaussianToMatrix (conjugateGaussianMatrix U A) =
      orthoMatrix U * GOEAsymptotics.gaussianToMatrix A * (orthoMatrix U).transpose := by
  ext i j
  simp only [GOEAsymptotics.gaussianToMatrix, conjugateGaussianMatrix_apply, Matrix.mul_apply,
    Matrix.transpose_apply, orthoMatrix, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma conjugateGaussianMatrix_trans (U V : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (A : GaussianMatrix (Fin n)) :
    conjugateGaussianMatrix (U.trans V) A =
      conjugateGaussianMatrix V (conjugateGaussianMatrix U A) := by
  apply gaussianToMatrix_injective
  simp only [gaussianToMatrix_conjugate, orthoMatrix_trans, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

lemma conjugate_symmetric (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (A : GaussianMatrix (Fin n)) (hA : ∀ i j, A i j = A j i) :
    ∀ i j, conjugateGaussianMatrix U A i j = conjugateGaussianMatrix U A j i := by
  have hT : transposeGaussianMatrix A = A := by ext i j; exact hA j i
  have h := conjugateGaussianMatrix_transpose U A
  rw [hT] at h
  intro i j
  exact congrArg (fun B : GaussianMatrix (Fin n) => B i j) h

end

def firstAxis (n : ℕ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => if i.val = 0 then 1 else 0)

lemma firstAxis_succ (n : ℕ) : firstAxis (n+1) = EuclideanSpace.basisFun (Fin (n+1)) ℝ 0 := by
  ext i
  cases i using Fin.cases <;> simp [firstAxis, EuclideanSpace.basisFun_apply]

lemma firstAxis_norm_succ (n : ℕ) : ‖firstAxis (n+1)‖ = 1 := by
  rw [firstAxis_succ]
  exact (EuclideanSpace.basisFun (Fin (n+1)) ℝ).orthonormal.norm_eq_one 0

lemma align_firstAxis (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) :
    alignIsometry (firstAxis n) v v = ‖v‖ • firstAxis n := by
  cases n with
  | zero => exact Subsingleton.elim _ _
  | succ n => exact alignIsometry_align _ _ (firstAxis_norm_succ n)

lemma extendTailIsometry_firstAxis {n : ℕ}
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    extendTailIsometry U (firstAxis (n+1)) = firstAxis (n+1) := by
  rw [firstAxis_succ]
  exact extendTailIsometry_basis_zero U

def firstColumn {n : ℕ} (A : GaussianMatrix (Fin (n+1))) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => A 0 i.succ)

def reducedTail {n : ℕ} (A : GaussianMatrix (Fin (n+1))) : GaussianMatrix (Fin n) :=
  conjugateGaussianMatrix (alignIsometry (firstAxis n) (firstColumn A)) (matrixTail A)

lemma reducedTail_symmetric {n : ℕ} (A : GaussianMatrix (Fin (n+1)))
    (hA : ∀ i j, A i j = A j i) : ∀ i j, reducedTail A i j = reducedTail A j i :=
  conjugate_symmetric _ _ (fun i j => hA i.succ j.succ)

@[fun_prop] lemma firstColumn_measurable (n : ℕ) : Measurable (firstColumn (n := n)) := by
  apply (WithLp.measurable_toLp _ _).comp
  apply Measurable.of_eval
  intro i
  fun_prop [firstColumn]

lemma reducedTail_measurable (n : ℕ) : Measurable (reducedTail (n := n)) := by
  have hm := (exposed_column_tail_law n 1 (firstAxis n)).measurable
  have ht : Measurable (fun p : ℝ × ((Fin n → ℝ) × GaussianMatrix (Fin n)) => p.2.2) :=
    measurable_snd.comp measurable_snd
  exact ht.comp hm

lemma first_step_conjugate {n : ℕ} (A : GaussianMatrix (Fin (n+1)))
    (hA : ∀ i j, A i j = A j i) :
    conjugateGaussianMatrix (extendTailIsometry (alignIsometry (firstAxis n) (firstColumn A))) A =
      borderMatrix (A 0 0) (‖firstColumn A‖ • firstAxis n) (reducedTail A) := by
  conv_lhs => arg 2; rw [← borderMatrix_blocks A hA]
  rw [extendTailIsometry_border]
  dsimp only [goeBlocks]
  change borderMatrix (A 0 0) (alignIsometry (firstAxis n) (firstColumn A) (firstColumn A))
    (reducedTail A) = _
  rw [align_firstAxis]

def triReduce : (n : ℕ) → GaussianMatrix (Fin n) → GaussianMatrix (Fin n)
  | 0, A => A
  | n+1, A => borderMatrix (A 0 0) (‖firstColumn A‖ • firstAxis n) (triReduce n (reducedTail A))

def triIsometry : (n : ℕ) → GaussianMatrix (Fin n) →
    (EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
  | 0, _ => LinearIsometryEquiv.refl _ _
  | n+1, A => (extendTailIsometry (alignIsometry (firstAxis n) (firstColumn A))).trans
      (extendTailIsometry (triIsometry n (reducedTail A)))

lemma triIsometry_firstAxis (n : ℕ) (A : GaussianMatrix (Fin n)) :
    triIsometry n A (firstAxis n) = firstAxis n := by
  cases n with
  | zero => rfl
  | succ n => simp only [triIsometry, LinearIsometryEquiv.trans_apply, extendTailIsometry_firstAxis]

lemma triReduce_conjugate (n : ℕ) (A : GaussianMatrix (Fin n))
    (hA : ∀ i j, A i j = A j i) :
    triReduce n A = conjugateGaussianMatrix (triIsometry n A) A := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    rw [triIsometry, conjugateGaussianMatrix_trans, first_step_conjugate A hA,
      extendTailIsometry_border]
    simp only [map_smul, triIsometry_firstAxis]
    rw [← ih _ (reducedTail_symmetric A hA)]
    rfl


lemma orthoMatrix_transpose {n : ℕ}
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    (orthoMatrix U).transpose = orthoMatrix U.symm := by
  ext i j
  have hh := U.inner_map_eq_flip (EuclideanSpace.basisFun (Fin n) ℝ i)
    (EuclideanSpace.basisFun (Fin n) ℝ j)
  simpa only [EuclideanSpace.inner_basisFun_real,EuclideanSpace.basisFun_inner,
    orthoMatrix,Matrix.transpose_apply] using hh

lemma orthoMatrix_toLpLin {n : ℕ}
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    Matrix.toLpLin 2 2 (orthoMatrix U) = U.toLinearEquiv.toLinearMap := by
  ext x i
  change (∑ j, U (EuclideanSpace.basisFun (Fin n) ℝ j) i * x j) = U x i
  rw [euclidean_isometry_apply_eq_sum]
  apply Finset.sum_congr rfl
  intros
  ring

lemma gaussianMatrixCLM_conjugate {n : ℕ}
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (A : GaussianMatrix (Fin n)) :
    (gaussianMatrixCLM (conjugateGaussianMatrix U A)).toLinearMap =
      U.toLinearEquiv.conj (gaussianMatrixCLM A).toLinearMap := by
  change Matrix.toLpLin 2 2 (GOEAsymptotics.gaussianToMatrix (conjugateGaussianMatrix U A)) = _
  rw [gaussianToMatrix_conjugate,Matrix.toLpLin_mul_same,Matrix.toLpLin_mul_same,
    orthoMatrix_transpose,orthoMatrix_toLpLin,orthoMatrix_toLpLin]
  rfl

lemma matrixOrderedEigenvalues_conjugate {n : ℕ}
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (A : GaussianMatrix (Fin n)) (hA : ∀ i j, A i j = A j i) :
    matrixOrderedEigenvalues (conjugateGaussianMatrix U A) = matrixOrderedEigenvalues A := by
  rw [matrixOrderedEigenvalues_eq _ (conjugate_symmetric U A hA),matrixOrderedEigenvalues_eq _ hA]
  apply (LinearMap.IsSymmetric.eigenvalues_eq_eigenvalues_iff _ _ _ _).mpr
  rw [gaussianMatrixCLM_conjugate,LinearEquiv.charpoly_conj]

lemma matrixOrderedEigenvalues_triReduce {n : ℕ}
    (A : GaussianMatrix (Fin n)) (hA : ∀ i j, A i j = A j i) :
    matrixOrderedEigenvalues (triReduce n A) = matrixOrderedEigenvalues A := by
  rw [triReduce_conjugate n A hA]
  exact matrixOrderedEigenvalues_conjugate _ _ hA


end TensorPCA.RetainedCountProofs.OAI.CriticalSK
