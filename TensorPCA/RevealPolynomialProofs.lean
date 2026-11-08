-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-! The exact finite Bernoulli reveal polynomial, with endpoint-safe product
weights and derivatives. -/
@[expose] public section
namespace TensorPCA.RevealPolynomialProofs
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {ι : Type*} [DecidableEq ι]

def weight (I A : Finset ι) (theta : ℝ) : ℝ :=
  ∏ i ∈ I, if i ∈ A then theta else 1-theta

def average (I : Finset ι) (h : Finset ι → ℝ) (theta : ℝ) : ℝ :=
  ∑ A ∈ I.powerset, weight I A theta*h A

theorem weight_insert_argument (I A : Finset ι) (i : ι) (hi : i ∉ I) (theta : ℝ) :
    weight I (insert i A) theta = weight I A theta := by
  unfold weight
  apply Finset.prod_congr rfl
  intro j hj
  have hji : j ≠ i := fun h ↦ hi (h ▸ hj)
  simp only [Finset.mem_insert, hji, false_or]

theorem weight_insert_not_mem (I A : Finset ι) (i : ι) (hi : i ∉ I) (hA : i ∉ A) (theta : ℝ) :
    weight (insert i I) A theta = (1-theta)*weight I A theta := by
  simp only [weight, Finset.prod_insert hi, hA, ite_false]

theorem weight_insert_insert (I A : Finset ι) (i : ι) (hi : i ∉ I) (theta : ℝ) :
    weight (insert i I) (insert i A) theta = theta*weight I A theta := by
  rw [weight, Finset.prod_insert hi]
  simp only [Finset.mem_insert_self, ite_true]
  rw [← weight, weight_insert_argument I A i hi]

theorem average_insert (I : Finset ι) (h : Finset ι → ℝ) (i : ι) (hi : i ∉ I) (theta : ℝ) :
    average (insert i I) h theta = (1-theta)*average I h theta+
      theta*average I (fun A ↦ h (insert i A)) theta := by
  rw [average, Finset.sum_powerset_insert hi]
  unfold average
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro A hA
    have hiA : i ∉ A := fun ha ↦ hi ((Finset.mem_powerset.mp hA) ha)
    rw [weight_insert_not_mem I A i hi hiA]
    ring
  · apply Finset.sum_congr rfl
    intro A _
    rw [weight_insert_insert I A i hi]
    ring

theorem average_one (I : Finset ι) (theta : ℝ) : average I (fun _ ↦ 1) theta = 1 := by
  induction I using Finset.induction_on with
  | empty => simp [average, weight]
  | @insert i I hi ih =>
    rw [average_insert I (fun _ ↦ 1) i hi, ih]
    ring

theorem weight_nonneg (I A : Finset ι) {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta ≤ 1) :
    0 ≤ weight I A theta := by
  apply Finset.prod_nonneg
  intro i _
  split_ifs <;> linarith

theorem average_nonneg (I : Finset ι) (h : Finset ι → ℝ) {theta : ℝ}
    (h0 : 0 ≤ theta) (h1 : theta ≤ 1) (hh : ∀ A ⊆ I, 0 ≤ h A) : 0 ≤ average I h theta := by
  apply Finset.sum_nonneg
  intro A hA
  exact mul_nonneg (weight_nonneg I A h0 h1) (hh A (Finset.mem_powerset.mp hA))

theorem average_le_const (I : Finset ι) (h : Finset ι → ℝ) {theta C : ℝ}
    (h0 : 0 ≤ theta) (h1 : theta ≤ 1) (hh : ∀ A ⊆ I, h A ≤ C) : average I h theta ≤ C := by
  calc
    _ ≤ ∑ A ∈ I.powerset, weight I A theta*C := by
      apply Finset.sum_le_sum
      intro A hA
      exact mul_le_mul_of_nonneg_left (hh A (Finset.mem_powerset.mp hA)) (weight_nonneg I A h0 h1)
    _ = C := by
      rw [← Finset.sum_mul]
      have hsum : (∑ A ∈ I.powerset, weight I A theta) = 1 := by
        simpa only [average, mul_one] using average_one I theta
      rw [hsum, one_mul]

theorem weight_hasDerivAt (I A : Finset ι) (theta : ℝ) :
    HasDerivAt (weight I A)
      (∑ i ∈ I, weight (I.erase i) A theta*(if i ∈ A then 1 else -1)) theta := by
  have h (i : ι) : HasDerivAt (fun t : ℝ ↦ if i ∈ A then t else 1-t)
      (if i ∈ A then 1 else -1) theta := by
    split_ifs
    · exact hasDerivAt_id theta
    · convert! (hasDerivAt_const theta (1 : ℝ)).sub (hasDerivAt_id theta) using 1
      simp
  convert! HasDerivAt.fun_finsetProd (fun i (_ : i ∈ I) ↦ h i) using 1

theorem signed_average_eq (I : Finset ι) (h : Finset ι → ℝ) (i : ι) (hi : i ∈ I) (theta : ℝ) :
    (∑ A ∈ I.powerset, weight (I.erase i) A theta*(if i ∈ A then 1 else -1)*h A) =
      average (I.erase i) (fun A ↦ h (insert i A)-h A) theta := by
  have hI : I.powerset = (insert i (I.erase i)).powerset :=
    congrArg Finset.powerset (Finset.insert_erase hi).symm
  rw [hI, Finset.sum_powerset_insert (Finset.notMem_erase i I), ← Finset.sum_add_distrib]
  unfold average
  apply Finset.sum_congr rfl
  intro A hA
  have hiA : i ∉ A := fun ha ↦ (Finset.notMem_erase i I) ((Finset.mem_powerset.mp hA) ha)
  rw [weight_insert_argument (I.erase i) A i (Finset.notMem_erase i I)]
  simp only [hiA, ite_false, Finset.mem_insert_self, ite_true]
  ring

/-- The genuine derivative for every real theta, including0 and1. Each
coordinate contributes its actual erased-mask average of the discrete increment. -/
theorem average_hasDerivAt (I : Finset ι) (h : Finset ι → ℝ) (theta : ℝ) :
    HasDerivAt (average I h)
      (∑ i ∈ I, average (I.erase i) (fun A ↦ h (insert i A)-h A) theta) theta := by
  have hd := HasDerivAt.fun_sum (fun A (_ : A ∈ I.powerset) ↦
    (weight_hasDerivAt I A theta).mul_const (h A))
  have he : (∑ A ∈ I.powerset,
      (∑ i ∈ I, weight (I.erase i) A theta*(if i ∈ A then 1 else -1))*h A) =
      ∑ i ∈ I, average (I.erase i) (fun A ↦ h (insert i A)-h A) theta := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    exact signed_average_eq I h i hi theta
  rw [he] at hd
  convert! hd using 1

theorem average_continuous (I : Finset ι) (h : Finset ι → ℝ) : Continuous (average I h) :=
  continuous_iff_continuousAt.mpr fun theta ↦ (average_hasDerivAt I h theta).continuousAt

end
end TensorPCA.RevealPolynomialProofs
