-- SPDX-License-Identifier: Apache-2.0
/- Jacobi row/support proofs adapt PathSpectra.lean at immutable
   pmaronow/slowequilibration-palomar a28aaa336343c4caf43791ababd8ed0ee5c7b58e
   (upstream openai/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb).
   The generic row estimate below is proved directly by a largest coordinate
   of a genuine eigenvector, avoiding an additional spectral-library import.
   No asymptotic or random-matrix hypothesis is used. See LICENSE. -/
module
public import TensorPCA.RetainedCountProofs.JacobiPolynomials
public import Mathlib.Tactic.Linarith
@[expose] public section
noncomputable section
open Matrix Polynomial
open scoped BigOperators Topology
namespace TensorPCA.RetainedCountProofs.JacobiMatrix
set_option backward.isDefEq.respectTransparency false
lemma finset_sum_indicator_le_one {ι : Type*} [Fintype ι] (p : ι → Prop)
    [DecidablePred p] (hp : ∀ i j, p i → p j → i = j) :
    (∑ i, if p i then (1 : ℝ) else 0) ≤ 1 := by
  classical
  by_cases hex : ∃ i, p i
  · obtain ⟨i, hi⟩ := hex
    have heq : ∀ j, p j ↔ j = i := fun j => ⟨fun hj => hp j i hj hi, fun h => h ▸ hi⟩
    simp_rw [heq]
    simp
  · simp [not_exists.mp hex]

lemma jacobi_row_norm_bound (n : ℕ) (i : Fin n) :
    ∑ j : Fin n, ‖jacobi (n : ℝ)⁻¹ n i j‖ ≤ 2 := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.zero_lt_of_lt i.isLt)
  have hentry (k : Fin n) : Real.sqrt ((n : ℝ)⁻¹ * ((n : ℝ) - 1 - k.val)) ≤ 1 := by
    apply Real.sqrt_le_one.mpr
    have hk : (0 : ℝ) ≤ k.val := Nat.cast_nonneg _
    apply (inv_mul_le_iff₀ hn).mpr
    linarith
  have hpoint (j : Fin n) : ‖jacobi (n : ℝ)⁻¹ n i j‖ ≤
      (if i.val + 1 = j.val then 1 else 0) + (if j.val + 1 = i.val then 1 else 0) := by
    unfold jacobi
    split_ifs <;> simp only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      norm_zero] <;> linarith [hentry i, hentry j]
  have h₁ := finset_sum_indicator_le_one (fun j : Fin n => i.val + 1 = j.val)
    (fun j k hj hk => Fin.ext (by omega))
  have h₂ := finset_sum_indicator_le_one (fun j : Fin n => j.val + 1 = i.val)
    (fun j k hj hk => Fin.ext (by omega))
  have hb := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => hpoint j)
  rw [Finset.sum_add_distrib] at hb
  linarith

lemma jacobi_hermitian (a : ℝ) (n : ℕ) : (jacobi a n).IsHermitian :=
  Matrix.isHermitian_iff_isSymm.mpr (jacobi_symmetric a n)

lemma hermitian_eigenvalue_abs_le_of_row_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (C : ℝ)
    (hR : ∀ j, ∑ k, |A j k| ≤ C) (i : ι) : |hA.eigenvalues i| ≤ C := by
  classical
  let : Nonempty ι := ⟨i⟩
  let v := hA.eigenvectorBasis i
  obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ (fun k => |v k|)
    Finset.univ_nonempty
  have hmax (k : ι) : |v k| ≤ |v j| := hj k (Finset.mem_univ k)
  have hpos : 0 < |v j| := by
    by_contra h
    have hz : |v j| = 0 := le_antisymm (le_of_not_gt h) (abs_nonneg _)
    have hv : v = 0 := by
      ext k
      exact abs_eq_zero.mp (le_antisymm ((hmax k).trans_eq hz) (abs_nonneg _))
    have hn : ‖v‖ = 1 := hA.eigenvectorBasis.norm_eq_one i
    rw [hv, norm_zero] at hn
    norm_num at hn
  have he : (∑ k, A j k * v k) = hA.eigenvalues i * v j := by
    exact congrFun (hA.mulVec_eigenvectorBasis i) j
  have hprod : |hA.eigenvalues i| * |v j| ≤ C * |v j| := by
    calc
      _ = |∑ k, A j k * v k| := by rw [← abs_mul, he]
      _ ≤ ∑ k, |A j k * v k| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k, |A j k| * |v k| := by simp only [abs_mul]
      _ ≤ ∑ k, |A j k| * |v j| := Finset.sum_le_sum
        (fun k _ => mul_le_mul_of_nonneg_left (hmax k) (abs_nonneg _))
      _ = (∑ k, |A j k|) * |v j| := (Finset.sum_mul _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (hR j) (abs_nonneg _)
  exact (mul_le_mul_iff_left₀ hpos).mp hprod

lemma jacobi_eigenvalue_bound (n : ℕ) (i : Fin n) :
    |(jacobi_hermitian (n : ℝ)⁻¹ n).eigenvalues i| ≤ 2 := by
  apply hermitian_eigenvalue_abs_le_of_row_sum
  intro j
  simpa only [Real.norm_eq_abs] using jacobi_row_norm_bound n j

end TensorPCA.RetainedCountProofs.JacobiMatrix
