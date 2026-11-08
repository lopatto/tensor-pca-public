-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.DerivativeTest
public import Mathlib.Topology.Order.IntermediateValue

/-! Scalar Gaussian precision minimization, before constructing a pushed
Crisanti--Sommers trial. No minimization over the original atom nodes is used. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCSGaussianBMinimization
open Set Filter
open scoped Topology BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {ι : Type*} [Fintype ι]

def cost (d y : ℝ) (a s t : ι → ℝ) (B : ℝ) : ℝ :=
  B-1-Real.log B+y/(B-d)+∑ i, a i*(Real.log (B-t i)-Real.log (B-s i))

def slope (d y : ℝ) (a s t : ι → ℝ) (B : ℝ) : ℝ :=
  1-1/B-y/(B-d)^2-∑ i, a i*(s i-t i)/((B-s i)*(B-t i))

theorem slope_continuousOn {d y : ℝ} (a s t : ι → ℝ) (hd : 0 ≤ d)
    (hst : ∀ i, t i ≤ s i ∧ s i ≤ d) : ContinuousOn (slope d y a s t) (Ioi d) := by
  intro B hB
  have hB0 : B ≠ 0 := ne_of_gt (hd.trans_lt hB)
  have hBd : B-d ≠ 0 := ne_of_gt (sub_pos.mpr hB)
  have hs (i) : B-s i ≠ 0 := ne_of_gt (sub_pos.mpr ((hst i).2.trans_lt hB))
  have ht (i) : B-t i ≠ 0 := ne_of_gt (sub_pos.mpr (((hst i).1.trans (hst i).2).trans_lt hB))
  unfold slope
  fun_prop (disch := aesop)

theorem cost_hasDerivAt {d y : ℝ} (a s t : ι → ℝ) (hd : 0 ≤ d)
    (hst : ∀ i, t i ≤ s i ∧ s i ≤ d) {B : ℝ} (hB : d < B) :
    HasDerivAt (cost d y a s t) (slope d y a s t B) B := by
  have hB0 : B ≠ 0 := ne_of_gt (hd.trans_lt hB)
  have hBd : B-d ≠ 0 := ne_of_gt (sub_pos.mpr hB)
  have hs (i) : B-s i ≠ 0 := ne_of_gt (sub_pos.mpr ((hst i).2.trans_lt hB))
  have ht (i) : B-t i ≠ 0 := ne_of_gt (sub_pos.mpr (((hst i).1.trans (hst i).2).trans_lt hB))
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun i (_ : i ∈ Finset.univ) ↦
    (((hasDerivAt_id B).sub_const (t i)).log (ht i)).sub
      (((hasDerivAt_id B).sub_const (s i)).log (hs i)) |>.const_mul (a i))
  have h := (((hasDerivAt_id B).sub_const 1).sub ((hasDerivAt_id B).log hB0)).add
    ((hasDerivAt_const B y).div ((hasDerivAt_id B).sub_const d) hBd)
  convert h.add hsum using 1
  · rfl
  · unfold slope
    simp only [id_eq, zero_mul, sub_zero, one_mul]
    have heq : (∑ i, a i*(1/(B-t i)-1/(B-s i))) =
        -(∑ i, a i*(s i-t i)/((B-s i)*(B-t i))) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      field_simp [hs i, ht i]
      ring
    rw [heq]
    ring

theorem slope_monotoneOn {d y : ℝ} (a s t : ι → ℝ) (hd : 0 ≤ d) (hy : 0 ≤ y)
    (ha : ∀ i, 0 ≤ a i) (hst : ∀ i, t i ≤ s i ∧ s i ≤ d) :
    MonotoneOn (slope d y a s t) (Ioi d) := by
  intro B hB C hC hBC
  have hB0 : 0 < B := hd.trans_lt hB
  have hBd : 0 < B-d := sub_pos.mpr hB
  have hsq : y/(C-d)^2 ≤ y/(B-d)^2 :=
    div_le_div_of_nonneg_left hy (sq_pos_of_pos hBd)
      (pow_le_pow_left₀ hBd.le (sub_le_sub_right hBC d) 2)
  have hsum : (∑ i, a i*(s i-t i)/((C-s i)*(C-t i))) ≤
      ∑ i, a i*(s i-t i)/((B-s i)*(B-t i)) := by
    apply Finset.sum_le_sum
    intro i _
    have hBs : 0 < B-s i := sub_pos.mpr ((hst i).2.trans_lt hB)
    have hBt : 0 < B-t i := sub_pos.mpr (((hst i).1.trans (hst i).2).trans_lt hB)
    exact div_le_div_of_nonneg_left (mul_nonneg (ha i) (sub_nonneg.mpr (hst i).1))
      (mul_pos hBs hBt) (mul_le_mul (sub_le_sub_right hBC (s i))
        (sub_le_sub_right hBC (t i)) hBt.le (hBs.le.trans (sub_le_sub_right hBC (s i))))
  have hi := one_div_le_one_div_of_le hB0 hBC
  unfold slope
  linarith

theorem slope_tendsto_one (d y : ℝ) (a s t : ι → ℝ) :
    Tendsto (slope d y a s t) atTop (𝓝 1) := by
  have hi (c : ℝ) : Tendsto (fun B : ℝ ↦ (B-c)⁻¹) atTop (𝓝 0) := by
    simpa only [sub_eq_add_neg, Function.comp_def, id_eq] using tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop (-c) tendsto_id)
  have hi0 : Tendsto (fun B : ℝ ↦ 1/B) atTop (𝓝 0) := by simpa using hi 0
  have hy : Tendsto (fun B : ℝ ↦ y/(B-d)^2) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, inv_pow, mul_zero, zero_pow (by decide : 2 ≠ 0)] using
      (hi d).pow 2 |>.const_mul y
  have hs : Tendsto (fun B : ℝ ↦ ∑ i, a i*(s i-t i)/((B-s i)*(B-t i))) atTop (𝓝 0) := by
    convert tendsto_finset_sum Finset.univ (fun i _ ↦ ((hi (s i)).mul (hi (t i))).const_mul
      (a i*(s i-t i))) using 1
    · funext B
      apply Finset.sum_congr rfl
      intro i _
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    · simp
  unfold slope
  simpa only [sub_zero] using ((tendsto_const_nhds.sub hi0).sub hy).sub hs

theorem exists_minimizing_root {d y : ℝ} (a s t : ι → ℝ) (hd : 0 ≤ d) (hy : 0 < y)
    (ha : ∀ i, 0 ≤ a i) (hst : ∀ i, t i ≤ s i ∧ s i ≤ d) :
    ∃ B : ℝ, d < B ∧ slope d y a s t B = 0 ∧
      ∀ C : ℝ, d < C → cost d y a s t B ≤ cost d y a s t C := by
  let e := min y 1
  have he : 0 < e := lt_min hy zero_lt_one
  have he1 : e ≤ 1 := min_le_right _ _
  have hey : e ≤ y := min_le_left _ _
  have hesq : e^2 ≤ y := (by nlinarith : e^2 ≤ e).trans hey
  have hleft : slope d y a s t (d+e) < 0 := by
    have hcoef : 1 ≤ y/e^2 := (le_div_iff₀ (sq_pos_of_pos he)).mpr (by simpa using hesq)
    have hsum : 0 ≤ ∑ i, a i*(s i-t i)/(((d+e)-s i)*((d+e)-t i)) := by
      apply Finset.sum_nonneg
      intro i _
      exact div_nonneg (mul_nonneg (ha i) (sub_nonneg.mpr (hst i).1))
        (mul_nonneg (by linarith [(hst i).2]) (by linarith [(hst i).1, (hst i).2]))
    have hi : 0 < 1/(d+e) := one_div_pos.mpr (by linarith)
    unfold slope
    simp only [add_sub_cancel_left]
    linarith
  obtain ⟨C, hC, hpos⟩ := ((eventually_gt_atTop (d+e)).and
    ((slope_tendsto_one d y a s t).eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < 1)))).exists
  obtain ⟨B, hB, hzero⟩ := intermediate_value_Icc hC.le
    ((slope_continuousOn a s t hd hst).mono (by intro z hz; change d < z; linarith [hz.1]))
    ⟨hleft.le, hpos.le⟩
  have hBd : d < B := by linarith [hB.1]
  have hmono := slope_monotoneOn a s t hd hy.le ha hst
  refine ⟨B, hBd, hzero, ?_⟩
  have hmin : IsMinOn (cost d y a s t) (Ioi d) B := by
    apply isMinOn_Ioi_of_deriv (cost_hasDerivAt a s t hd hst hBd).continuousAt
    · intro x hx
      exact (cost_hasDerivAt a s t hd hst hx.1).differentiableAt.differentiableWithinAt
    · intro x hx
      exact (cost_hasDerivAt a s t hd hst (hBd.trans hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(cost_hasDerivAt a s t hd hst hx.1).deriv, ← hzero]
      exact hmono hx.1 hBd hx.2.le
    · intro x hx
      rw [(cost_hasDerivAt a s t hd hst (hBd.trans hx)).deriv, ← hzero]
      exact hmono hBd (hBd.trans hx) hx.le
  exact fun C hC ↦ hmin hC

end
end TensorPCA.NonRSLowerProofs.FiniteCSGaussianBMinimization
