-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticUniformBounds
public import TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticLogSteps

/-! Depth-free coefficient estimates for the normalized quadratic root. Positive
precision margins and scalar range bounds are hypotheses; constants are independent
of hierarchy depth.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticCoefficientBounds
open Set FiniteCSGaussianDepthPrecision FiniteGaussianQuadraticUniformBounds
open FiniteGaussianQuadraticLogSteps
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem log_precision_ratio_div_nonneg {d : ℕ} {x Delta : Fin d→ℝ} {B : ℝ}
    (hx : ∀j,0<x j) (hDelta : ∀j,0≤Delta j)
    (hB : tail (fun j ↦ x j*Delta j) 0<B) (j : Fin d) :
    0≤Real.log (precision x Delta B ((j : ℕ)+1)/precision x Delta B j)/x j := by
  have hP := precision_pos hx hDelta hB
  have hnext := precision_succ x Delta B j
  have hratio : 1≤precision x Delta B ((j : ℕ)+1)/precision x Delta B j := by
    apply (le_div_iff₀ (hP j)).mpr
    have H := mul_nonneg (hx j).le (hDelta j)
    nlinarith only [hnext,H]
  exact div_nonneg (Real.log_nonneg hratio) (hx j).le

theorem log_precision_ratio_div_le {d : ℕ} {x Delta : Fin d→ℝ} {B : ℝ}
    (hx : ∀j,0<x j) (hDelta : ∀j,0≤Delta j)
    (hB : tail (fun j ↦ x j*Delta j) 0<B) (j : Fin d) :
    Real.log (precision x Delta B ((j : ℕ)+1)/precision x Delta B j)/x j≤
      Delta j/precision x Delta B j := by
  have hP := precision_pos hx hDelta hB
  have hnext := precision_succ x Delta B j
  have hlog := Real.log_le_sub_one_of_pos (div_pos (hP ((j : ℕ)+1)) (hP j))
  have heq : precision x Delta B ((j : ℕ)+1)/precision x Delta B j-1=
      x j*Delta j/precision x Delta B j := by
    field_simp [(hP j).ne']
    linarith only [hnext]
  rw [heq] at hlog
  have H := div_le_div_of_nonneg_right hlog (hx j).le
  have hcancel : (x j*Delta j/precision x Delta B j)/x j=Delta j/precision x Delta B j := by
    field_simp [(hx j).ne',(hP j).ne']
  rwa [hcancel] at H

theorem log_precision_ratio_div_le_uniform {d : ℕ} {x Delta : Fin d→ℝ} {B Dmin : ℝ}
    (hx : ∀j,0<x j) (hDelta : ∀j,0≤Delta j)
    (hB : tail (fun j ↦ x j*Delta j) 0<B) (hDmin : 0<Dmin)
    (hLower : Dmin≤precision x Delta B 0) (j : Fin d) :
    Real.log (precision x Delta B ((j : ℕ)+1)/precision x Delta B j)/x j≤Delta j/Dmin := by
  refine (log_precision_ratio_div_le hx hDelta hB j).trans ?_
  exact div_le_div_of_nonneg_left (hDelta j) hDmin
    (hLower.trans (precision_zero_le (fun j ↦ (hx j).le) hDelta j))

theorem abs_profileConstant_one_le {d : ℕ} {x Delta : Fin d→ℝ} {B Bmax Dmin Y : ℝ}
    (hx : ∀j,0<x j) (hDelta : ∀j,0≤Delta j)
    (hB : tail (fun j ↦ x j*Delta j) 0<B) (hDmin : 0<Dmin)
    (hLower : Dmin≤precision x Delta B 0) (hB1 : 1≤B) (hMax : B≤Bmax)
    (hSum : (∑j : Fin d,Delta j)≤Y) :
    |profileConstant 1 x Delta B 0|≤Real.log Bmax/2+Y/(2*Dmin) := by
  let S := ∑j : Fin d,Real.log (precision x Delta B ((j : ℕ)+1)/precision x Delta B j)/(2*x j)
  have hHalf (j : Fin d) : Real.log (precision x Delta B ((j : ℕ)+1)/precision x Delta B j)/(2*x j)=
      (Real.log (precision x Delta B ((j : ℕ)+1)/precision x Delta B j)/x j)/2 := by
    field_simp [(hx j).ne']
  have hS0 : 0≤S := by
    apply Finset.sum_nonneg
    intro j _
    rw [hHalf j]
    exact div_nonneg (log_precision_ratio_div_nonneg hx hDelta hB j) (by norm_num)
  have hS : S≤Y/(2*Dmin) := by
    calc
      S≤∑j : Fin d,(Delta j/Dmin)/2 := by
        apply Finset.sum_le_sum
        intro j _
        rw [hHalf j]
        exact div_le_div_of_nonneg_right (log_precision_ratio_div_le_uniform hx hDelta hB hDmin hLower j)
          (by norm_num)
      _=(∑j : Fin d,Delta j)/(2*Dmin) := by
        simp only [div_eq_mul_inv,mul_inv_rev,mul_assoc,Finset.sum_mul]
      _≤Y/(2*Dmin) := div_le_div_of_nonneg_right hSum (by positivity)
  have hLog : 0≤Real.log B := Real.log_nonneg hB1
  have hLogMax : Real.log B≤Real.log Bmax := Real.log_le_log (zero_lt_one.trans_le hB1) hMax
  have hAbs : |(-Real.log B/2+S)|≤Real.log B/2+S := by
    have H := abs_add_le (-Real.log B/2) S
    rw [abs_div,abs_neg,abs_of_nonneg hLog,abs_of_nonneg hS0] at H
    norm_num at H
    exact H
  have H := hAbs.trans (show Real.log B/2+S≤Real.log Bmax/2+Y/(2*Dmin) by linarith only [hLogMax,hS])
  simpa only [profileConstant,tail_zero,Nat.cast_one,one_mul,neg_one_mul,S] using H

theorem quadraticRootSlope_mem_Icc {d : ℕ} (x Delta : Fin d→ℝ) (B : ℝ) {Dmin y0 Y : ℝ}
    (hDmin : 0<Dmin) (hLower : Dmin≤precision x Delta B 0)
    (hy : 0≤y0) (hY : y0≤Y) :
    y0/(2*precision x Delta B 0)∈Icc (0 : ℝ) (Y/(2*Dmin)) := by
  have hD : 0<precision x Delta B 0 := hDmin.trans_le hLower
  refine ⟨div_nonneg hy (by positivity),?_⟩
  calc
    y0/(2*precision x Delta B 0)≤y0/(2*Dmin) :=
      div_le_div_of_nonneg_left hy (by positivity) (by linarith only [hLower])
    _≤Y/(2*Dmin) := div_le_div_of_nonneg_right hY (by positivity)

theorem abs_quadraticRootSlope_le {d : ℕ} (x Delta : Fin d→ℝ) (B : ℝ) {Dmin y0 Y : ℝ}
    (hDmin : 0<Dmin) (hLower : Dmin≤precision x Delta B 0)
    (hy : 0≤y0) (hY : y0≤Y) :
    |y0/(2*precision x Delta B 0)|≤Y/(2*Dmin) := by
  have H := quadraticRootSlope_mem_Icc x Delta B hDmin hLower hy hY
  rw [abs_of_nonneg H.1]
  exact H.2

end
end TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticCoefficientBounds
