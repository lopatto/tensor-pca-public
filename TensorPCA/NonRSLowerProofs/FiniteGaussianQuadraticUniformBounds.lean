-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCSGaussianDepthPrecision

/-! Dimension-independent scalar bounds for finite Gaussian spines. These estimates use
the proved precision-root equation, not a shell assumption.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticUniformBounds
open FiniteCSGaussianDepthPrecision
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem precision_zero_le {d : ℕ} {x Delta : Fin d→ℝ} {B : ℝ}
    (hx : ∀j,0≤ x j) (hDelta : ∀j,0≤ Delta j) (i : ℕ) :
    precision x Delta B 0≤precision x Delta B i := by
  have H := tail_le_zero (fun j => mul_nonneg (hx j) (hDelta j)) i
  simpa only [precision] using (show B-tail (fun j => x j*Delta j) 0≤
    B-tail (fun j => x j*Delta j) i by linarith only [H])

theorem precision_le_B {d : ℕ} {x Delta : Fin d→ℝ} {B : ℝ}
    (hx : ∀j,0≤ x j) (hDelta : ∀j,0≤ Delta j) (i : ℕ) :
    precision x Delta B i≤B := by
  exact sub_le_self _ (tail_nonneg (fun j => mul_nonneg (hx j) (hDelta j)) i)

theorem root_precision_lower {d : ℕ} {x Delta : Fin d→ℝ} {B y0 : ℝ}
    (hx : ∀j,0< x j) (hDelta : ∀j,0≤ Delta j)
    (hB : tail (fun j => x j*Delta j) 0< B) (hy : 0≤ y0)
    (hroot : y0/(precision x Delta B 0)^2+
      (∑j : Fin d,Delta j/(precision x Delta B j*precision x Delta B ((j : ℕ)+1)))=1-1/B) :
    Real.sqrt y0≤precision x Delta B 0 := by
  have hP := precision_pos hx hDelta hB
  have hBp : 0< B := by simpa only [precision_end] using hP d
  have hs : 0≤∑j : Fin d,Delta j/(precision x Delta B j*precision x Delta B ((j : ℕ)+1)) := by
    exact Finset.sum_nonneg (fun j _ => div_nonneg (hDelta j) (mul_pos (hP j) (hP ((j : ℕ)+1))).le)
  have hratio : y0/(precision x Delta B 0)^2≤1 := by
    have hInv := one_div_nonneg.mpr hBp.le
    linarith only [hroot,hs,hInv]
  have hsq : y0≤(precision x Delta B 0)^2 := (div_le_one (sq_pos_of_pos (hP 0))).mp hratio
  exact (Real.sqrt_le_iff).mpr ⟨(hP 0).le,hsq⟩

theorem root_precision_upper {d : ℕ} {x Delta : Fin d→ℝ} {B y0 : ℝ}
    (hx : ∀j,0< x j) (hx1 : ∀j,x j≤1) (hDelta : ∀j,0≤ Delta j)
    (hB : tail (fun j => x j*Delta j) 0< B) (hy : 0≤ y0)
    (hroot : y0/(precision x Delta B 0)^2+
      (∑j : Fin d,Delta j/(precision x Delta B j*precision x Delta B ((j : ℕ)+1)))=1-1/B) :
    B≤2+3*(y0+∑j : Fin d,Delta j) := by
  let Y := y0+∑j : Fin d,Delta j
  have hY : 0≤Y := add_nonneg hy (Finset.sum_nonneg (fun j _ => hDelta j))
  have hP := precision_pos hx hDelta hB
  have hBp : 0< B := by simpa only [precision_end] using hP d
  have htail : tail (fun j => x j*Delta j) 0≤Y := by
    rw [tail_zero]
    have H : (∑j : Fin d,x j*Delta j)≤∑j : Fin d,Delta j :=
      Finset.sum_le_sum (fun j _ => by nlinarith only [hx1 j,hDelta j])
    dsimp only [Y]
    linarith only [H,hy]
  have hs : (∑j : Fin d,Delta j/(precision x Delta B j*precision x Delta B ((j : ℕ)+1)))≤
      (∑j : Fin d,Delta j)/(precision x Delta B 0)^2 := by
    conv_rhs => rw [div_eq_mul_inv,Finset.sum_mul]
    simp only [← div_eq_mul_inv]
    apply Finset.sum_le_sum
    intro j _
    have h0j := precision_zero_le (B := B) (fun j => (hx j).le) hDelta j
    have h0next := precision_zero_le (B := B) (fun j => (hx j).le) hDelta ((j : ℕ)+1)
    apply div_le_div_of_nonneg_left (hDelta j) (sq_pos_of_pos (hP 0))
    nlinarith only [h0j,h0next,hP 0,hP j,hP ((j : ℕ)+1)]
  by_contra H
  have hLarge : 2+3*Y< B := lt_of_not_ge H
  have hDlarge : 2+2*Y< precision x Delta B 0 := by
    dsimp only [precision]
    linarith only [hLarge,htail]
  have hBtwo : 2< B := by linarith only [hLarge,hY]
  have hDtwo : 2< precision x Delta B 0 := by linarith only [hDlarge,hY]
  have hSquare : 2*Y<(precision x Delta B 0)^2 := by nlinarith only [hDlarge,hDtwo,hY]
  have hInv : 1/B< (1:ℝ)/2 := by
    apply (div_lt_div_iff₀ hBp (by norm_num : (0:ℝ)<2)).mpr
    linarith only [hBtwo]
  have hRatio : Y/(precision x Delta B 0)^2< (1:ℝ)/2 := by
    apply (div_lt_div_iff₀ (sq_pos_of_pos (hP 0)) (by norm_num : (0:ℝ)<2)).mpr
    nlinarith only [hSquare]
  have hsum : y0/(precision x Delta B 0)^2+
      (∑j : Fin d,Delta j)/(precision x Delta B 0)^2=Y/(precision x Delta B 0)^2 := by
    rw [← add_div]
  linarith only [hroot,hs,hRatio,hInv,hsum]

def prefixVariance {d : ℕ} (x Delta : Fin d→ℝ) (B y0 : ℝ) (i : ℕ) : ℝ :=
  y0/(precision x Delta B 0)^2+
    prefixSum (fun j => Delta j/(precision x Delta B j*precision x Delta B ((j : ℕ)+1))) i

theorem prefixVariance_mem_Icc {d : ℕ} {x Delta : Fin d→ℝ} {B y0 : ℝ}
    (hx : ∀j,0< x j) (hDelta : ∀j,0≤ Delta j)
    (hB : tail (fun j => x j*Delta j) 0< B) (hy : 0≤ y0)
    (hroot : y0/(precision x Delta B 0)^2+
      (∑j : Fin d,Delta j/(precision x Delta B j*precision x Delta B ((j : ℕ)+1)))=1-1/B)
    (i : ℕ) : prefixVariance x Delta B y0 i∈Set.Icc (0:ℝ) 1 := by
  have hP := precision_pos hx hDelta hB
  have hBp : 0< B := by simpa only [precision_end] using hP d
  have hg (j : Fin d) : 0≤Delta j/(precision x Delta B j*precision x Delta B ((j : ℕ)+1)) :=
    div_nonneg (hDelta j) (mul_pos (hP j) (hP ((j : ℕ)+1))).le
  have hpre : 0≤prefixSum (fun j => Delta j/(precision x Delta B j*precision x Delta B ((j : ℕ)+1))) i := by
    apply Finset.sum_nonneg
    intro j _
    split_ifs
    · exact hg j
    · exact le_rfl
  have H := prefix_add_tail (fun j => Delta j/
    (precision x Delta B j*precision x Delta B ((j : ℕ)+1))) i
  have htail := tail_nonneg hg i
  have hInv := one_div_nonneg.mpr hBp.le
  constructor
  · exact add_nonneg (div_nonneg hy (sq_nonneg _)) hpre
  · unfold prefixVariance
    linarith only [H,htail,hroot,hInv]

theorem scaledPrefixVariance_le {d : ℕ} {x Delta : Fin d→ℝ} {B y0 : ℝ}
    (hx : ∀j,0< x j) (hDelta : ∀j,0≤ Delta j)
    (hB : tail (fun j => x j*Delta j) 0< B) (hy : 0≤ y0)
    (hroot : y0/(precision x Delta B 0)^2+
      (∑j : Fin d,Delta j/(precision x Delta B j*precision x Delta B ((j : ℕ)+1)))=1-1/B)
    (i : ℕ) : (precision x Delta B i)^2*prefixVariance x Delta B y0 i≤B^2 := by
  have hP := precision_pos hx hDelta hB i
  have hPB := precision_le_B (B := B) (fun j => (hx j).le) hDelta i
  have hV := prefixVariance_mem_Icc hx hDelta hB hy hroot i
  calc
    _≤(precision x Delta B i)^2*1 := mul_le_mul_of_nonneg_left hV.2 (sq_nonneg _)
    _≤B^2 := by nlinarith only [hP,hPB]

end
end TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticUniformBounds
