-- SPDX-License-Identifier: Apache-2.0
/- Narrow attributed Apache-2.0 source port:
https://github.com/pmaronow/slowequilibration-palomar/blob/a28aaa336343c4caf43791ababd8ed0ee5c7b58e/SlowEquilibration/NegativeDefiniteMatrices.lean
Retained static negativity/Borel/coordinate bodies are unchanged apart from
namespace/import prefixes. Unused spectral criteria are omitted, and no
spectral asymptotic premise is substituted. See repository LICENSE. -/
module

public import TensorPCA.RetainedCountProofs.NegativeDefiniteOperators

/-! Matrix and orthonormal-coordinate criteria for quadratic negativity. -/
@[expose] public section
namespace TensorPCA.RetainedCountProofs.NegativeDefiniteOperators
open Set MeasureTheory Matrix
open TensorPCA.RetainedCountProofs.OAI.CriticalSK GOEAsymptotics
open scoped RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma matrix_operator_shift {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (k : ℝ) :
    gaussianMatrixCLM (matrixToGaussian (W - k • 1)) =
      gaussianMatrixCLM (matrixToGaussian W) - k • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
  ext v i
  change ((W-k•1) *ᵥ v.ofLp) i = (W *ᵥ v.ofLp) i - k*v i
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

lemma matrix_operator_toMatrix_apply {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {n : ℕ}
    (B : OrthonormalBasis (Fin n) ℝ E) (T : E →L[ℝ] E) (v : EuclideanSpace ℝ (Fin n)) :
    gaussianMatrixCLM (matrixToGaussian (LinearMap.toMatrix B.toBasis B.toBasis T.toLinearMap)) v =
      B.repr (T (B.repr.symm v)) := by
  have h := T.toLinearMap.toMatrix_mulVec_repr B.toBasis B.toBasis (B.repr.symm v)
  apply PiLp.ext
  intro i
  have hi := congrFun h i
  change ((LinearMap.toMatrix B.toBasis B.toBasis T.toLinearMap) *ᵥ
    (fun j => B.repr (B.repr.symm v) j)) i = B.repr (T (B.repr.symm v)) i at hi
  rw [B.repr.apply_symm_apply] at hi
  exact hi

lemma negativeDefinite_toMatrix_iff {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {n : ℕ}
    (B : OrthonormalBasis (Fin n) ℝ E) (T : E →L[ℝ] E) :
    NegativeDefinite (gaussianMatrixCLM (matrixToGaussian (LinearMap.toMatrix B.toBasis B.toBasis T.toLinearMap))) ↔
      NegativeDefinite T := by
  have he (v : EuclideanSpace ℝ (Fin n)) :
      inner ℝ v (gaussianMatrixCLM (matrixToGaussian
        (LinearMap.toMatrix B.toBasis B.toBasis T.toLinearMap)) v) =
        inner ℝ (B.repr.symm v) (T (B.repr.symm v)) := by
    rw [matrix_operator_toMatrix_apply]
    exact (B.repr.inner_map_map (B.repr.symm v) (T (B.repr.symm v))).symm.trans
      (by rw [B.repr.apply_symm_apply]) |>.symm
  constructor
  · intro h v hv
    have hh := h (B.repr v) (by intro h0; apply hv; exact B.repr.injective (h0.trans (map_zero _).symm))
    rw [he, B.repr.symm_apply_apply] at hh
    exact hh
  · intro h v hv
    rw [he]
    exact h (B.repr.symm v) (by intro h0; apply hv; simpa using congrArg B.repr h0)

end
end TensorPCA.RetainedCountProofs.NegativeDefiniteOperators
