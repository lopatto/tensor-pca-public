-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticUniformThreshold
public import TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticUniformBounds

/-! Precision-root equations give fixed compact scalar bounds, and the Gaussian root
value has the ordinary depth-cost normalization.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticCompactParameters
open FiniteCSGaussianDepthPrecision FiniteGaussianQuadraticLogSteps
open FiniteGaussianQuadraticUniformBounds
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem root_compact_bounds {d : ℕ} {x Delta : Fin d→ℝ} {B y0 ymin Y : ℝ}
    (hx : ∀j,0< x j) (hx1 : ∀j,x j≤1) (hDelta : ∀j,0≤ Delta j)
    (hB : tail (fun j => x j*Delta j) 0< B) (hymin : 0< ymin) (hy0 : ymin≤y0)
    (hY : y0+∑j : Fin d,Delta j≤Y)
    (hroot : y0/(precision x Delta B 0)^2+
      (∑j : Fin d,Delta j/(precision x Delta B j*precision x Delta B ((j : ℕ)+1)))=1-1/B) :
    0≤y0 ∧ 0≤Y ∧ 1≤B ∧ B≤2+3*Y ∧ Real.sqrt ymin≤precision x Delta B 0 ∧
      (∑j : Fin d,Delta j)≤Y ∧ y0≤Y := by
  have hy : 0≤y0 := hymin.le.trans hy0
  have hSum : 0≤∑j : Fin d,Delta j := Finset.sum_nonneg (fun j _ => hDelta j)
  have hY0 : 0≤Y := by linarith only [hy,hSum,hY]
  have hP := precision_pos hx hDelta hB
  have hBp : 0< B := by simpa only [precision_end] using hP d
  have hRatios : 0≤∑j : Fin d,Delta j/(precision x Delta B j*precision x Delta B ((j : ℕ)+1)) :=
    Finset.sum_nonneg (fun j _ => div_nonneg (hDelta j) (mul_pos (hP j) (hP ((j : ℕ)+1))).le)
  have hRoot0 := div_nonneg hy (sq_nonneg (precision x Delta B 0))
  have hInv : 1/B≤1 := by linarith only [hroot,hRatios,hRoot0]
  have hBone : 1≤B := (div_le_one hBp).mp hInv
  have hBupper : B≤2+3*Y := by
    have H := root_precision_upper hx hx1 hDelta hB hy hroot
    linarith only [H,hY]
  have hDlower := (Real.sqrt_le_sqrt hy0).trans (root_precision_lower hx hDelta hB hy hroot)
  exact ⟨hy,hY0,hBone,hBupper,hDlower,by linarith only [hY,hy],by linarith only [hY,hSum]⟩

theorem gaussian_root_value_eq_half_depthCost {d : ℕ} {x Delta : Fin d→ℝ} {B : ℝ}
    (hx : ∀j,0< x j) (hDelta : ∀j,0≤ Delta j)
    (hB : tail (fun j => x j*Delta j) 0< B) (y0 : ℝ) :
    profileConstant 1 x Delta B 0+y0/(2*precision x Delta B 0)+(B-1)/2=
      depthCost x Delta y0 B/2 := by
  have hP := precision_pos hx hDelta hB
  have HS : (∑j : Fin d,Real.log (precision x Delta B ((j : ℕ)+1)/precision x Delta B j)/(2*x j))=
      (∑j : Fin d,(Real.log (precision x Delta B ((j : ℕ)+1))-Real.log (precision x Delta B j))/x j)/2 := by
    conv_rhs => rw [div_eq_mul_inv,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [Real.log_div (hP ((j : ℕ)+1)).ne' (hP j).ne']
    ring
  rw [profileConstant,tail_zero,depthCost_eq]
  simp only [Nat.cast_one,one_mul]
  rw [HS]
  ring

end
end TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticCompactParameters
