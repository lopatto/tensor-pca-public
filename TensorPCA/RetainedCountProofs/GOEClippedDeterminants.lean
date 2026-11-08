-- SPDX-License-Identifier: Apache-2.0
/- Actual finite clipped spectral trace and determinant domination, following
   the exact finite arguments in pmaronow/slowequilibration-palomar
   a28aaa336343c4caf43791ababd8ed0ee5c7b58e,
   SlowEquilibration/GOEClippedDeterminants.lean. The shared functional below
   takes a literal Matrix and its actual dimension. No spectral asymptotic or
   expected trace limit is assumed. See LICENSE. -/
module
public import TensorPCA.RetainedCountProofs.MatrixSpectralTraceLipschitz
public import TensorPCA.RetainedCountProofs.SpectralTraceLipschitz
@[expose] public section
namespace TensorPCA.RetainedCountProofs.GOEClippedDeterminants
noncomputable section
open MeasureTheory ProbabilityTheory
open GOEAsymptotics OAI.CriticalSK SpectralTraceLipschitz
open scoped BigOperators Topology NNReal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Literal clipped logarithmic statistic of the actual symmetric matrix law.
The dimension parameter is the number of rows, including the empty matrix. -/
def matrixClippedTrace (m : ℕ) (k rho : ℝ) (W : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  ∑ i : Fin m, clippedLog k rho (matrixOrderedEigenvalues (matrixToGaussian W) i)

lemma matrixOrderedEigenvalues_symmetrize {m : ℕ} (A : GOEAsymptotics.GaussianMatrix m) :
    matrixOrderedEigenvalues (SymmetricGaussianRealization.symmetrize A) =
      matrixOrderedEigenvalues A := by
  rw [matrixOrderedEigenvalues_eq _ (SymmetricGaussianRealization.symmetrize_symmetric A)]
  rfl

/-- Every scalar Lipschitz test has a genuine total spectral-trace bound on
all inputs, since the shared eigenvalues are those of the symmetric part. -/
lemma spectralTrace_lipschitz (m : ℕ) (f : ℝ → ℝ) {L : ℝ≥0} (hf : LipschitzWith L f) :
    LipschitzWith ⟨Real.sqrt (m : ℝ)*(L : ℝ), by positivity⟩
      (fun A : GOEAsymptotics.GaussianMatrix m => ∑ i, f (matrixOrderedEigenvalues A i)) := by
  apply LipschitzWith.of_dist_le_mul
  intro A B
  change |(∑ i, f (matrixOrderedEigenvalues A i))-
    (∑ i, f (matrixOrderedEigenvalues B i))| ≤
      (Real.sqrt (m : ℝ)*(L : ℝ))*‖A-B‖
  have h := spectral_trace_difference (SymmetricGaussianRealization.symmetrize A)
    (SymmetricGaussianRealization.symmetrize B)
    (SymmetricGaussianRealization.symmetrize_symmetric A)
    (SymmetricGaussianRealization.symmetrize_symmetric B) f hf
  simp only [matrixOrderedEigenvalues_symmetrize] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [map_sub] using SymmetricGaussianRealization.symmetrize_norm_le (A-B)

lemma matrixClippedTrace_gaussian_lipschitz (m : ℕ) (k : ℝ) {rho : ℝ} (hrho : 0 < rho) :
    LipschitzWith ⟨Real.sqrt (m : ℝ)*(1/rho), by positivity⟩
      (fun A : GOEAsymptotics.GaussianMatrix m => matrixClippedTrace m k rho (gaussianToMatrix A)) := by
  have h := spectralTrace_lipschitz m (clippedLog k rho) (clippedLog_lipschitz k hrho)
  change LipschitzWith ⟨Real.sqrt (m : ℝ)*(1/rho), by positivity⟩
    (fun A : GOEAsymptotics.GaussianMatrix m => ∑ i, clippedLog k rho (matrixOrderedEigenvalues A i)) at h
  simpa only [matrixClippedTrace, matrixToGaussian_gaussianToMatrix] using h

lemma matrixClippedTrace_measurable (m : ℕ) (k : ℝ) {rho : ℝ} (hrho : 0 < rho) :
    Measurable (matrixClippedTrace m k rho) := by
  have h := (matrixClippedTrace_gaussian_lipschitz m k hrho).continuous.measurable
  simpa only [Function.comp_def, gaussianToMatrix_matrixToGaussian] using
    h.comp (matrixToGaussian_measurable m)

lemma shifted_det_eq_prod {m : ℕ} (k : ℝ) (B : GOEAsymptotics.GaussianMatrix m)
    (hB : ∀ i j, B i j = B j i) :
    (k • (1 : Matrix (Fin m) (Fin m) ℝ) - gaussianToMatrix B).det =
      ∏ i, (k - matrixOrderedEigenvalues B i) := by
  let hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) = m := by simp
  let hS := gaussianMatrixCLM_symmetric B hB
  have hchar : (gaussianMatrixCLM B).toLinearMap.charpoly = (gaussianToMatrix B).charpoly := by
    exact Matrix.charpoly_toLin (gaussianToMatrix B) (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
  have h := hS.charpoly_eq hn
  rw [hchar] at h
  have he := congrArg (Polynomial.eval k) h
  rw [Matrix.eval_charpoly] at he
  simpa only [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal, Polynomial.eval_prod,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    matrixOrderedEigenvalues_eq B hB, RCLike.ofReal_real_eq_id, id_eq] using he

lemma exp_matrixClippedTrace (m : ℕ) (k : ℝ) {rho : ℝ} (hrho : 0 < rho)
    (W : Matrix (Fin m) (Fin m) ℝ) :
    Real.exp (matrixClippedTrace m k rho W) =
      ∏ i, max |k-matrixOrderedEigenvalues (matrixToGaussian W) i| rho := by
  unfold matrixClippedTrace clippedLog
  rw [Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  exact Real.exp_log (hrho.trans_le (le_max_right _ _))

lemma matrixAbsoluteDet_le_exp_matrixClippedTrace (m : ℕ) (k : ℝ)
    {rho : ℝ} (hrho : 0 < rho) (W : Matrix (Fin m) (Fin m) ℝ)
    (hW : ∀ i j, W i j = W j i) :
    |(k • (1 : Matrix (Fin m) (Fin m) ℝ)-W).det| ≤ Real.exp (matrixClippedTrace m k rho W) := by
  rw [← gaussianToMatrix_matrixToGaussian W, shifted_det_eq_prod k (matrixToGaussian W) hW,
    Finset.abs_prod, exp_matrixClippedTrace m k hrho]
  exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun _ _ => le_max_left _ _)

end
end TensorPCA.RetainedCountProofs.GOEClippedDeterminants
