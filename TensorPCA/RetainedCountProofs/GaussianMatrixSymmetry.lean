-- SPDX-License-Identifier: Apache-2.0
/- Narrow finite symmetric-matrix projection port from immutable
pmaronow/slowequilibration-palomar a28aaa336343c4caf43791ababd8ed0ee5c7b58e,
GaussianMatrices.lean and SymmetricGaussianRealization.lean. The upstream
GaussianMatrices attributes openai/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Only exact transpose/projection maps and norm identities are retained, using
shared matrix aliases; no new GOE law or spectral conclusion is introduced.
See the repository LICENSE. -/
module
public import TensorPCA.RetainedCountProofs.GaussianMatrixOperators
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology RealInnerProductSpace
namespace TensorPCA.RetainedCountProofs.OAI.CriticalSK
variable {ι : Type*} [Fintype ι]
def transposeGaussianMatrix : GaussianMatrix ι ≃ₗᵢ[ℝ] GaussianMatrix ι where
  toFun A := WithLp.toLp 2 (fun i => WithLp.toLp 2 (fun j => A j i))
  invFun A := WithLp.toLp 2 (fun i => WithLp.toLp 2 (fun j => A j i))
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' A := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [PiLp.norm_sq_eq_of_L2]
    exact Finset.sum_comm

@[simp] lemma transposeGaussianMatrix_apply (A : GaussianMatrix ι) (i j : ι) :
    transposeGaussianMatrix A i j = A j i := rfl

def symmetrizeGaussianMatrix (s : ℝ) (A : GaussianMatrix ι) : GaussianMatrix ι :=
  s • (A + transposeGaussianMatrix A)

lemma symmetrizeGaussianMatrix_continuous (s : ℝ) :
    Continuous (symmetrizeGaussianMatrix (ι := ι) s) := by
  unfold symmetrizeGaussianMatrix
  fun_prop


end TensorPCA.RetainedCountProofs.OAI.CriticalSK
namespace TensorPCA.RetainedCountProofs.SymmetricGaussianRealization
open GOEAsymptotics OAI.CriticalSK
variable {m : ℕ}

def symmetrizeLinear : GOEAsymptotics.GaussianMatrix m →ₗ[ℝ] GOEAsymptotics.GaussianMatrix m where
  toFun A := (1/2 : ℝ) • (A + transposeGaussianMatrix A)
  map_add' A B := by ext i j; change (1/2 : ℝ)*((A i j+B i j)+(A j i+B j i)) = _; change _ = (1/2 : ℝ)*(A i j+A j i)+(1/2 : ℝ)*(B i j+B j i); ring
  map_smul' r A := by ext i j; change (1/2 : ℝ)*(r*A i j+r*A j i) = r*((1/2 : ℝ)*(A i j+A j i)); ring

def symmetrize : GOEAsymptotics.GaussianMatrix m →L[ℝ] GOEAsymptotics.GaussianMatrix m where
  toLinearMap := symmetrizeLinear
  cont := symmetrizeGaussianMatrix_continuous (ι := Fin m) (1/2)

@[simp] lemma symmetrize_apply (A : GOEAsymptotics.GaussianMatrix m) (i j : Fin m) :
    symmetrize A i j = (A i j + A j i)/2 := by
  change (1/2 : ℝ) * (A i j + A j i) = _
  ring

lemma symmetrize_symmetric (A : GOEAsymptotics.GaussianMatrix m) :
    ∀ i j, symmetrize A i j = symmetrize A j i := by
  intro i j
  simp only [symmetrize_apply, add_comm]

lemma symmetrize_eq_self (A : GOEAsymptotics.GaussianMatrix m)
    (hA : ∀ i j, A i j = A j i) : symmetrize A = A := by
  ext i j
  simp only [symmetrize_apply, hA i j]
  ring

lemma symmetrize_norm_le (A : GOEAsymptotics.GaussianMatrix m) : ‖symmetrize A‖ ≤ ‖A‖ := by
  change ‖(1/2 : ℝ) • (A + transposeGaussianMatrix A)‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)]
  calc
    _ ≤ (1/2 : ℝ) * (‖A‖ + ‖transposeGaussianMatrix A‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ = _ := by rw [LinearIsometryEquiv.norm_map]; ring

lemma symmetrize_inner (M A : GOEAsymptotics.GaussianMatrix m)
    (hA : ∀ i j, A i j = A j i) : inner ℝ (symmetrize M) A = inner ℝ M A := by
  have ht : transposeGaussianMatrix A = A := by ext i j; exact hA j i
  have hi := (transposeGaussianMatrix (ι := Fin m)).inner_map_map M A
  rw [ht] at hi
  change inner ℝ ((1/2 : ℝ) • (M + transposeGaussianMatrix M)) A = _
  rw [inner_smul_left, conj_trivial, inner_add_left, hi]
  ring


end TensorPCA.RetainedCountProofs.SymmetricGaussianRealization
