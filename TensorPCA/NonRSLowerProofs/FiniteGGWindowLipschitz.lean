-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGGWindowScalar
public import Mathlib.Algebra.Order.Group.MinMax

/-! An explicit global Lipschitz constant for the fixed continuous window. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGGWindowScalar
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem clip_abs_sub_le (a b : ℝ) :
    |max 0 (min 1 a)-max 0 (min 1 b)|≤|a-b| := by
  have h1 := abs_max_sub_max_le_max (0 : ℝ) (min 1 a) 0 (min 1 b)
  have h2 := abs_min_sub_min_le_max (1 : ℝ) a 1 b
  simp only [sub_self,abs_zero] at h1 h2
  rw [max_eq_right (abs_nonneg (min (1 : ℝ) a-min 1 b))] at h1
  rw [max_eq_right (abs_nonneg (a-b))] at h2
  exact h1.trans h2

 theorem window_abs_sub_le {kappa : ℝ} (hK : 0<kappa) (x y : ℝ) :
    |window kappa x-window kappa y|≤(2/kappa+8)*|x-y| := by
  let U := fun w : ℝ ↦ max 0 (min 1 (2*w/kappa-1))
  let V := fun w : ℝ ↦ max 0 (min 1 (7-8*w))
  have hClip (r : ℝ) : 0≤max 0 (min 1 r) ∧ max 0 (min 1 r)≤1 :=
    ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩
  have hUx : 0≤U x ∧ U x≤1 := hClip _
  have hVy : 0≤V y ∧ V y≤1 := hClip _
  have hU : |U x-U y|≤(2/kappa)*|x-y| := by
    have H := clip_abs_sub_le (2*x/kappa-1) (2*y/kappa-1)
    have he : (2*x/kappa-1)-(2*y/kappa-1)=(2/kappa)*(x-y) := by ring
    rw [he,abs_mul,abs_of_pos (div_pos (by norm_num) hK)] at H
    exact H
  have hV : |V x-V y|≤8*|x-y| := by
    have H := clip_abs_sub_le (7-8*x) (7-8*y)
    have he : (7-8*x)-(7-8*y)=(-8 : ℝ)*(x-y) := by ring
    rw [he,abs_mul] at H
    norm_num at H
    exact H
  change |U x*V x-U y*V y|≤_
  calc
    _=|U x*(V x-V y)+(U x-U y)*V y| := by congr 1; ring
    _≤|U x*(V x-V y)|+|(U x-U y)*V y| := abs_add_le _ _
    _=U x*|V x-V y|+|U x-U y| *V y := by
      rw [abs_mul,abs_mul,abs_of_nonneg hUx.1,abs_of_nonneg hVy.1]
    _≤1*(8*|x-y|)+((2/kappa)*|x-y|)*1 := add_le_add
      (mul_le_mul hUx.2 hV (abs_nonneg _) (by norm_num))
      (mul_le_mul hU hVy.2 hVy.1 (by positivity))
    _=_ := by ring

end
end TensorPCA.NonRSLowerProofs.FiniteGGWindowScalar
