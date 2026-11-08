-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Pinned representation probe for finite real unit-Gram matrices.
No continuous selection of matrix square roots is required. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteUnitGramRealization
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
noncomputable section

/-- Rows of the standard nonnegative matrix square root. -/
def realization {K : ℕ} (A : Matrix (Fin K) (Fin K) ℝ) (i : Fin K) :
    EuclideanSpace ℝ (Fin K) := WithLp.toLp 2 (fun j ↦ CFC.sqrt A i j)

theorem realization_inner {K : ℕ} (A : Matrix (Fin K) (Fin K) ℝ) (hA : A.PosSemidef)
    (i j : Fin K) : inner ℝ (realization A i) (realization A j)=A i j := by
  have hR : (CFC.sqrt A).IsHermitian := (CFC.sqrt_nonneg A).posSemidef.isHermitian
  have hsymm (a b : Fin K) : CFC.sqrt A a b=CFC.sqrt A b a := by
    simpa only [star_trivial] using (hR.apply a b).symm
  have hroot := congrArg (fun B : Matrix (Fin K) (Fin K) ℝ ↦ B i j)
    (CFC.sqrt_mul_sqrt_self A hA.nonneg)
  rw [Matrix.mul_apply] at hroot
  simp only [realization,EuclideanSpace.inner_toLp_toLp,star_trivial,dotProduct]
  calc
    _ = ∑ l, CFC.sqrt A i l*CFC.sqrt A l j := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [hsymm j l]
      ring
    _ = A i j := hroot

theorem realization_norm {K : ℕ} (A : Matrix (Fin K) (Fin K) ℝ) (hA : A.PosSemidef)
    (hdiag : ∀ i, A i i=1) (i : Fin K) : ‖realization A i‖=1 := by
  have H := realization_inner A hA i i
  rw [real_inner_self_eq_norm_sq,hdiag i] at H
  nlinarith [norm_nonneg (realization A i)]

theorem exists_unit_realization {K : ℕ} (A : Matrix (Fin K) (Fin K) ℝ) (hA : A.PosSemidef)
    (hdiag : ∀ i, A i i=1) :
    ∃ v : Fin K → EuclideanSpace ℝ (Fin K), (∀ i, ‖v i‖=1) ∧ ∀ i j, inner ℝ (v i) (v j)=A i j :=
  ⟨realization A,realization_norm A hA hdiag,realization_inner A hA⟩

theorem entry_abs_le_one {K : ℕ} (A : Matrix (Fin K) (Fin K) ℝ) (hA : A.PosSemidef)
    (hdiag : ∀ i, A i i=1) (i j : Fin K) : |A i j|≤1 := by
  rw [← realization_inner A hA i j]
  simpa only [realization_norm A hA hdiag,mul_one] using
    abs_real_inner_le_norm (realization A i) (realization A j)

/-- The standard finite real positive-semidefinite matrices with unit diagonal. -/
def unitGramSet (K : ℕ) : Set (Matrix (Fin K) (Fin K) ℝ) :=
  {A | A.PosSemidef ∧ ∀ i, A i i=1}

theorem unitGramSet_isClosed (K : ℕ) : IsClosed (unitGramSet K) := by
  have hd : IsClosed {A : Matrix (Fin K) (Fin K) ℝ | ∀ i, A i i=1} := by
    have H : IsClosed (⋂ i : Fin K, {A : Matrix (Fin K) (Fin K) ℝ | A i i=1}) :=
      isClosed_iInter (fun i ↦ isClosed_eq (by fun_prop) continuous_const)
    simpa only [Set.setOf_forall] using H
  exact Matrix.posSemidef_is_closed.inter hd

theorem unitGramSet_isCompact (K : ℕ) : IsCompact (unitGramSet K) := by
  have hbox : IsCompact {A : Matrix (Fin K) (Fin K) ℝ | ∀ i j, A i j∈Set.Icc (-1 : ℝ) 1} :=
    isCompact_pi_infinite (fun i : Fin K ↦ isCompact_pi_infinite (fun j : Fin K ↦ isCompact_Icc))
  apply hbox.of_isClosed_subset (unitGramSet_isClosed K)
  intro A hA i j
  exact abs_le.mp (entry_abs_le_one A hA.1 hA.2 i j)

end
end TensorPCA.NonRSLowerProofs.FiniteUnitGramRealization
