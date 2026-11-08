-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteNestedLawComparison

/-! A strict cofinal height vector and its exact finite-law comparison.
Original weak heights remain recurrence coefficients; the only PMF is the
already normalized literal strict-height nested partition law. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteNestedStrictSurrogate
open FiniteNestedPartition FiniteNestedDiscountedPartitionLaw FiniteNestedLawComparison
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def interiorGrid (depth : ℕ) (j : Fin depth) : ℝ :=
  (((j : ℕ)+1 : ℕ) : ℝ)/((depth+1 : ℕ) : ℝ)

def strictHeightApprox (depth : ℕ) (x : Fin depth→ℝ) (t : ℝ) (j : Fin depth) : ℝ :=
  (1-t)*x j+t*interiorGrid depth j

theorem interiorGrid_pos (depth : ℕ) (j : Fin depth) : 0 < interiorGrid depth j := by
  unfold interiorGrid
  positivity

theorem interiorGrid_lt_one (depth : ℕ) (j : Fin depth) : interiorGrid depth j<1 := by
  have hd : (0 : ℝ)<((depth+1 : ℕ) : ℝ) := by positivity
  rw [interiorGrid,div_lt_one hd]
  exact_mod_cast Nat.succ_lt_succ j.isLt

theorem interiorGrid_strictMono (depth : ℕ) : StrictMono (interiorGrid depth) := by
  intro i j hij
  have hd : (0 : ℝ)<((depth+1 : ℕ) : ℝ) := by positivity
  unfold interiorGrid
  apply (div_lt_div_iff_of_pos_right hd).2
  exact_mod_cast Nat.succ_lt_succ hij

theorem strictHeightApprox_pos (depth : ℕ) (x : Fin depth→ℝ) (t : ℝ)
    (hx0 : ∀j,0≤x j) (ht : 0<t) (ht1 : t≤1) :
    ∀j,0<strictHeightApprox depth x t j := by
  intro j
  have H0 := mul_nonneg (sub_nonneg.mpr ht1) (hx0 j)
  have H1 := mul_pos ht (interiorGrid_pos depth j)
  unfold strictHeightApprox
  linarith only [H0,H1]

theorem strictHeightApprox_lt_one (depth : ℕ) (x : Fin depth→ℝ) (t : ℝ)
    (hx1 : ∀j,x j≤1) (ht : 0<t) (ht1 : t≤1) :
    ∀j,strictHeightApprox depth x t j<1 := by
  intro j
  have H0 := mul_le_mul_of_nonneg_left (hx1 j) (sub_nonneg.mpr ht1)
  have H1 := mul_lt_mul_of_pos_left (interiorGrid_lt_one depth j) ht
  unfold strictHeightApprox
  linarith only [H0,H1]

theorem strictHeightApprox_strictMono (depth : ℕ) (x : Fin depth→ℝ) (t : ℝ)
    (hxm : Monotone x) (ht : 0<t) (ht1 : t≤1) :
    StrictMono (strictHeightApprox depth x t) := by
  intro i j hij
  have H0 := mul_le_mul_of_nonneg_left (hxm hij.le) (sub_nonneg.mpr ht1)
  have H1 := mul_lt_mul_of_pos_left (interiorGrid_strictMono depth hij) ht
  unfold strictHeightApprox
  linarith only [H0,H1]

theorem strictHeightApprox_sub_abs_le (depth : ℕ) (x : Fin depth→ℝ) (t : ℝ)
    (hx0 : ∀j,0≤x j) (hx1 : ∀j,x j≤1) (ht : 0≤t) :
    ∀j,|strictHeightApprox depth x t j-x j|≤t := by
  intro j
  have Hgrid : |interiorGrid depth j-x j|≤1 := by
    exact abs_le.mpr ⟨by linarith [interiorGrid_pos depth j,hx1 j],
      by linarith [interiorGrid_lt_one depth j,hx0 j]⟩
  rw [show strictHeightApprox depth x t j-x j=t*(interiorGrid depth j-x j) by
    unfold strictHeightApprox; ring,abs_mul,abs_of_nonneg ht]
  exact (mul_le_mul_of_nonneg_left Hgrid ht).trans_eq (mul_one t)

theorem strictHeightApprox_joint_continuous (depth : ℕ) :
    Continuous (fun p : (Fin depth→ℝ)×ℝ ↦ strictHeightApprox depth p.1 p.2) := by
  apply continuous_pi
  intro j
  exact ((continuous_const.sub continuous_snd).mul
    ((continuous_apply j).comp continuous_fst)).add (continuous_snd.mul continuous_const)

theorem strictHeightApprox_joint_measurable (depth : ℕ) :
    Measurable (fun p : (Fin depth→ℝ)×ℝ ↦ strictHeightApprox depth p.1 p.2) :=
  (strictHeightApprox_joint_continuous depth).measurable

/-- Replace the original weak coefficients by an exact strict reference law.
Every physical recurrence error remains in the displayed residual sum. -/
theorem surrogate_l1Distance_family_le (depth N : ℕ) (x : Fin depth→ℝ) (t : ℝ)
    (hx0 : ∀j,0≤x j) (hxm : Monotone x) (hx1 : ∀j,x j≤1)
    (ht : 0<t) (ht1 : t≤1)
    (P : (n : ℕ)→PMF (NestedPartition depth n)) (hN : 0<N) :
    l1Distance (P N)
      (partitionPMF depth N (strictHeightApprox depth x t) 0 (le_refl 0)
        (strictHeightApprox_pos depth x t hx0 ht ht1)
        (strictHeightApprox_strictMono depth x t hxm ht ht1)
        (fun j ↦ (strictHeightApprox_lt_one depth x t hx1 ht ht1 j).le))≤
      ∑n ∈ Finset.Ico 1 N,
        (recurrenceResidual depth n x (P n) (P (n+1))+
          ((n*depth+1 : ℕ) : ℝ)*(((n : ℝ)+1)*t/(n : ℝ))) := by
  exact l1Distance_family_le depth N (strictHeightApprox depth x t) x t
    (strictHeightApprox_pos depth x t hx0 ht ht1)
    (strictHeightApprox_strictMono depth x t hxm ht ht1)
    (fun j ↦ (strictHeightApprox_lt_one depth x t hx1 ht ht1 j).le)
    ht.le (strictHeightApprox_sub_abs_le depth x t hx0 hx1 ht.le) P hN


end
end TensorPCA.NonRSLowerProofs.FiniteNestedStrictSurrogate
