-- SPDX-License-Identifier: Apache-2.0
/- Static symmetric-part/eigenvalue definitions follow immutable
pmaronow/slowequilibration-palomar a28aaa336343c4caf43791ababd8ed0ee5c7b58e,
Upstream/OAI/MathematicalPhysics/CriticalSK/GOESpectrum.lean (credited upstream
openai/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb). The finite Rayleigh
arguments below use Mathlib's genuine eigenbasis; no MinMax/spectral asymptotic
or random-matrix bound is assumed. See the repository LICENSE. -/
module
public import TensorPCA.RetainedCountProofs.GaussianMatrixSymmetry
public import TensorPCA.RetainedCountProofs.GaussianMatrixFeatures
public import TensorPCA.RetainedCountProofs.SymmetricOperatorQuadratic
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Module
open scoped BigOperators Topology RealInnerProductSpace
namespace TensorPCA.RetainedCountProofs.OAI.CriticalSK
open GOEAsymptotics GaussianMatrixFeatures
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma gaussianMatrixCLM_symmetric {n : ℕ} (A : GaussianMatrix (Fin n))
    (hA : ∀ i j, A i j = A j i) : (gaussianMatrixCLM A).toLinearMap.IsSymmetric := by
  apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
  ext i j
  exact hA j i

lemma symmetrize_half_entry {n : ℕ} (A : GaussianMatrix (Fin n)) (i j : Fin n) :
    symmetrizeGaussianMatrix (1/2 : ℝ) A i j = (A i j+A j i)/2 := by
  change (1/2 : ℝ)*(A i j+A j i) = _
  ring

lemma symmetrize_half_symmetric {n : ℕ} (A : GaussianMatrix (Fin n)) :
    ∀ i j, symmetrizeGaussianMatrix (1/2 : ℝ) A i j = symmetrizeGaussianMatrix (1/2 : ℝ) A j i := by
  intro i j
  rw [symmetrize_half_entry,symmetrize_half_entry,add_comm]

lemma symmetrize_half_eq {n : ℕ} (A : GaussianMatrix (Fin n)) (hA : ∀ i j, A i j = A j i) :
    symmetrizeGaussianMatrix (1/2 : ℝ) A = A := by
  ext i j
  rw [symmetrize_half_entry,hA j i]
  ring

/-- Descending eigenvalues of the genuine symmetric part, agreeing with
actual self-adjoint eigenvalues on symmetric matrices. -/
def matrixOrderedEigenvalues {n : ℕ} (A : GaussianMatrix (Fin n)) : Fin n → ℝ :=
  (gaussianMatrixCLM_symmetric _ (symmetrize_half_symmetric A)).eigenvalues
    (by simp : finrank ℝ (EuclideanSpace ℝ (Fin n)) = n)

lemma matrixOrderedEigenvalues_eq {n : ℕ} (A : GaussianMatrix (Fin n))
    (hA : ∀ i j, A i j = A j i) :
    matrixOrderedEigenvalues A = (gaussianMatrixCLM_symmetric A hA).eigenvalues
      (by simp : finrank ℝ (EuclideanSpace ℝ (Fin n)) = n) := by
  unfold matrixOrderedEigenvalues
  congr 2
  exact congrArg gaussianMatrixCLM (symmetrize_half_eq A hA)

lemma rankOneMatrix_norm {n : ℕ} (u : EuclideanSpace ℝ (Fin n)) :
    ‖rankOneMatrix u‖ = ‖u‖^2 := by
  apply (sq_eq_sq₀ (norm_nonneg _) (sq_nonneg _)).mp
  simpa only [← pow_mul] using rankOneMatrix_norm_sq u

lemma quadratic_symmetrize_half {n : ℕ} (A : GaussianMatrix (Fin n))
    (u : EuclideanSpace ℝ (Fin n)) :
    inner ℝ u (gaussianMatrixCLM (symmetrizeGaussianMatrix (1/2 : ℝ) A) u) =
      inner ℝ u (gaussianMatrixCLM A u) := by
  rw [quadratic_eq_rankOne_inner,quadratic_eq_rankOne_inner]
  calc
    _ = inner ℝ (symmetrizeGaussianMatrix (1/2 : ℝ) A) (rankOneMatrix u) := real_inner_comm _ _
    _ = inner ℝ A (rankOneMatrix u) := by
      change inner ℝ (SymmetricGaussianRealization.symmetrize A) (rankOneMatrix u) = _
      exact SymmetricGaussianRealization.symmetrize_inner A (rankOneMatrix u)
        (fun i j ↦ by simp only [rankOneMatrix_apply,mul_comm])
    _ = _ := real_inner_comm _ _

lemma quadratic_le_topEigenvalue {n : ℕ} (A : GaussianMatrix (Fin (n+1)))
    (u : EuclideanSpace ℝ (Fin (n+1))) (hu : ‖u‖ = 1) :
    inner ℝ u (gaussianMatrixCLM A u) ≤ matrixOrderedEigenvalues A 0 := by
  let S := symmetrizeGaussianMatrix (1/2 : ℝ) A
  let hS := gaussianMatrixCLM_symmetric S (symmetrize_half_symmetric A)
  let hn : finrank ℝ (EuclideanSpace ℝ (Fin (n+1))) = n+1 := by simp
  let B := hS.eigenvectorBasis hn
  change _ ≤ hS.eigenvalues hn 0
  calc
    _ = inner ℝ u (gaussianMatrixCLM S u) := (quadratic_symmetrize_half A u).symm
    _ = basisQuadratic B (hS.eigenvalues hn) u := (eigenbasisQuadratic_eq hS hn u).symm
    _ ≤ (hS.eigenvalues hn 0)*(∑ i, (B.repr u i)^2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (hS.eigenvalues_antitone hn (Fin.zero_le i)) (sq_nonneg _)
    _ = _ := by rw [basis_sum_squares B u,hu]; simp

lemma exists_unit_quadratic_eq_top {n : ℕ} (A : GaussianMatrix (Fin (n+1))) :
    ∃ u : EuclideanSpace ℝ (Fin (n+1)), ‖u‖ = 1 ∧
      inner ℝ u (gaussianMatrixCLM A u) = matrixOrderedEigenvalues A 0 := by
  let S := symmetrizeGaussianMatrix (1/2 : ℝ) A
  let hS := gaussianMatrixCLM_symmetric S (symmetrize_half_symmetric A)
  let hn : finrank ℝ (EuclideanSpace ℝ (Fin (n+1))) = n+1 := by simp
  let B := hS.eigenvectorBasis hn
  refine ⟨B 0,B.norm_eq_one 0,?_⟩
  rw [← quadratic_symmetrize_half A (B 0)]
  have he : gaussianMatrixCLM S (B 0) = hS.eigenvalues hn 0 • B 0 := hS.apply_eigenvectorBasis hn 0
  rw [he,real_inner_smul_right,real_inner_self_eq_norm_sq,B.norm_eq_one 0]
  change hS.eigenvalues hn 0*1^2 = hS.eigenvalues hn 0
  simp

lemma topEigenvalue_sub_le {n : ℕ} (A B : GaussianMatrix (Fin (n+1))) :
    matrixOrderedEigenvalues A 0-matrixOrderedEigenvalues B 0 ≤ ‖A-B‖ := by
  obtain ⟨u,hu,hval⟩ := exists_unit_quadratic_eq_top A
  have hb := quadratic_le_topEigenvalue B u hu
  calc
    _ ≤ matrixOrderedEigenvalues A 0-inner ℝ u (gaussianMatrixCLM B u) := sub_le_sub_left hb _
    _ = inner ℝ (rankOneMatrix u) (A-B) := by
      rw [← hval]
      simp only [quadratic_eq_rankOne_inner,inner_sub_right]
    _ ≤ ‖rankOneMatrix u‖*‖A-B‖ := real_inner_le_norm _ _
    _ = _ := by rw [rankOneMatrix_norm,hu]; simp

lemma matrixTopEigenvalue_lipschitz (n : ℕ) :
    LipschitzWith 1 (fun A : GaussianMatrix (Fin (n+1)) ↦ matrixOrderedEigenvalues A 0) := by
  apply LipschitzWith.of_dist_le_mul
  intro A B
  change |matrixOrderedEigenvalues A 0-matrixOrderedEigenvalues B 0| ≤ (1 : ℝ)*‖A-B‖
  rw [one_mul]
  apply abs_le.mpr
  constructor
  · have h := topEigenvalue_sub_le B A
    rw [norm_sub_rev] at h
    linarith
  · exact topEigenvalue_sub_le A B

lemma matrixTopEigenvalue_measurable (n : ℕ) :
    Measurable (fun A : GaussianMatrix (Fin (n+1)) ↦ matrixOrderedEigenvalues A 0) :=
  (matrixTopEigenvalue_lipschitz n).continuous.measurable

end TensorPCA.RetainedCountProofs.OAI.CriticalSK
