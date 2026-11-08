-- SPDX-License-Identifier: Apache-2.0
/- Narrow finite spectral-criterion source port:
https://github.com/pmaronow/slowequilibration-palomar/blob/a28aaa336343c4caf43791ababd8ed0ee5c7b58e/SlowEquilibration/NegativeDefiniteOperators.lean
Exact shifted symmetric-operator criterion, with unchanged mathematical body.
No random-matrix spectral estimate is imported or assumed. See LICENSE. -/
module
public import TensorPCA.RetainedCountProofs.NegativeDefiniteOperators
public import TensorPCA.RetainedCountProofs.SymmetricOperatorQuadratic
@[expose] public section
namespace TensorPCA.RetainedCountProofs.NegativeDefiniteOperators
noncomputable section
open TensorPCA.RetainedCountProofs.OAI.CriticalSK
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
/-- Strict negativity of a shifted symmetric operator is equivalent to
every genuine eigenvalue lying below the shift. -/
lemma negativeDefinite_shift_iff (T : E →L[ℝ] E) (hT : T.toLinearMap.IsSymmetric)
    {m : ℕ} (hm : Module.finrank ℝ E = m) (k : ℝ) :
    NegativeDefinite (T - k • ContinuousLinearMap.id ℝ E) ↔ ∀ i : Fin m, hT.eigenvalues hm i < k := by
  let B := hT.eigenvectorBasis hm
  constructor
  · intro h i
    have hh := h (B i) (B.orthonormal.ne_zero i)
    have hv : ‖B i‖ = 1 := B.norm_eq_one i
    have he : T (B i) = hT.eigenvalues hm i • B i := hT.apply_eigenvectorBasis hm i
    change inner ℝ (B i) (T (B i) - k • B i) < 0 at hh
    rw [he, inner_sub_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hv] at hh
    norm_num at hh
    linarith
  · intro h v hv
    have hv' : B.repr v ≠ 0 := by intro hh; apply hv; exact B.repr.injective (hh.trans (map_zero _).symm)
    have hi : ∃ i : Fin m, B.repr v i ≠ 0 := by
      by_contra! hh
      apply hv'
      ext i
      exact hh i
    obtain ⟨i,hi⟩ := hi
    change inner ℝ v (T v - k • v) < 0
    have hq : basisQuadratic B (hT.eigenvalues hm) v = inner ℝ v (T v) :=
      eigenbasisQuadratic_eq hT hm v
    rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
      ← hq, ← basis_sum_squares B v]
    change (∑ j, hT.eigenvalues hm j * (B.repr v j)^2) - k*(∑ j, (B.repr v j)^2) < 0
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_neg'
    · intro j _
      nlinarith [sq_nonneg (B.repr v j), h j]
    · exact ⟨i, Finset.mem_univ i, by nlinarith [sq_pos_of_ne_zero hi, h i]⟩

end
end TensorPCA.RetainedCountProofs.NegativeDefiniteOperators
