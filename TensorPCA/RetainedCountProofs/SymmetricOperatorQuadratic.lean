-- SPDX-License-Identifier: Apache-2.0
/- Narrow finite operator source port:
https://github.com/pmaronow/slowequilibration-palomar/blob/a28aaa336343c4caf43791ababd8ed0ee5c7b58e/SlowEquilibration/Upstream/OAI/MathematicalPhysics/CriticalSK/MinMax.lean
The upstream source credits openai/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Only literal finite eigenbasis quadratic identities are retained, with bodies
unchanged. No random matrix/spectral asymptotic is asserted. See LICENSE. -/
module
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Tactic.Ring
@[expose] public section
namespace TensorPCA.RetainedCountProofs.OAI.CriticalSK
noncomputable section
open Module
open scoped BigOperators RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
def basisQuadratic {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) (a : Fin n → ℝ) (x : E) : ℝ :=
  ∑ i, a i * (b.repr x i) ^ 2

omit [FiniteDimensional ℝ E] in
lemma basis_sum_squares {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) (x : E) :
    ∑ i, (b.repr x i) ^ 2 = ‖x‖ ^ 2 := by
  simp only [b.repr_apply_apply]
  exact b.sum_sq_inner_right x

lemma eigenbasisQuadratic_eq {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    {n : ℕ} (hn : finrank ℝ E = n) (x : E) :
    basisQuadratic (hT.eigenvectorBasis hn) (hT.eigenvalues hn) x = inner ℝ x (T x) := by
  rw [basisQuadratic, ← (hT.eigenvectorBasis hn).sum_inner_mul_inner x (T x)]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_comm ((hT.eigenvectorBasis hn) i) x, ← (hT.eigenvectorBasis hn).repr_apply_apply,
    ← (hT.eigenvectorBasis hn).repr_apply_apply, hT.eigenvectorBasis_apply_self_apply]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  ring


end
end TensorPCA.RetainedCountProofs.OAI.CriticalSK
