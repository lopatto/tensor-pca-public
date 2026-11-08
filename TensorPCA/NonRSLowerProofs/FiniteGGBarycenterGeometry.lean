-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! Deterministic barycenter geometry used after finite replica duplication.
No probabilistic identity or duplication assertion is a premise of this lemma. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGGBarycenterGeometry
open scoped BigOperators RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

 theorem mean_inner (m : ℕ) (Y Z : Fin m→E) :
    inner ℝ ((m : ℝ)⁻¹ • ∑i : Fin m,Y i) ((m : ℝ)⁻¹ • ∑j : Fin m,Z j)=
      ((m : ℝ)⁻¹)^2*(∑i : Fin m,∑j : Fin m,inner ℝ (Y i) (Z j)) := by
  rw [real_inner_smul_left,real_inner_smul_right,sum_inner]
  simp_rw [inner_sum]
  ring

 theorem mean_norm_sq_le {m : ℕ} (hm : 0<m) (Y : Fin m→E)
    (hY : ∀i,‖Y i‖=1) {d : ℝ} (hYY : ∀i j,i≠j→inner ℝ (Y i) (Y j)≤d) :
    ‖(m : ℝ)⁻¹ • ∑i : Fin m,Y i‖^2≤1/(m : ℝ)+(1-1/(m : ℝ))*d := by
  have hm0 : (m : ℝ)≠0 := by exact_mod_cast hm.ne'
  have hPair (i j : Fin m) : inner ℝ (Y i) (Y j)≤d+(if j=i then 1-d else 0) := by
    by_cases hji : j=i
    · subst j
      rw [real_inner_self_eq_norm_sq,hY i]
      simp
    · simpa only [if_neg hji,add_zero] using hYY i j (Ne.symm hji)
  have hSum : (∑i : Fin m,∑j : Fin m,inner ℝ (Y i) (Y j))≤
      (m : ℝ)*((m : ℝ)*d+(1-d)) := by
    calc
      _≤∑i : Fin m,∑j : Fin m,(d+(if j=i then 1-d else 0)) :=
        Finset.sum_le_sum (fun i _ ↦ Finset.sum_le_sum (fun j _ ↦ hPair i j))
      _=_ := by simp [Finset.sum_add_distrib]; ring
  rw [←real_inner_self_eq_norm_sq,mean_inner]
  apply (mul_le_mul_of_nonneg_left hSum (sq_nonneg ((m : ℝ)⁻¹))).trans_eq
  field_simp
  ring

 theorem mean_cross_ge {m : ℕ} (hm : 0<m) (Y Z : Fin m→E) {d : ℝ}
    (hYZ : ∀i j,d≤ inner ℝ (Y i) (Z j)) :
    d≤ inner ℝ ((m : ℝ)⁻¹ • ∑i : Fin m,Y i) ((m : ℝ)⁻¹ • ∑j : Fin m,Z j) := by
  have hm0 : (m : ℝ)≠0 := by exact_mod_cast hm.ne'
  have hSum : (m : ℝ)^2*d≤∑i : Fin m,∑j : Fin m,inner ℝ (Y i) (Z j) := by
    calc
      _=∑_i : Fin m,∑_j : Fin m,d := by simp; ring
      _≤_ := Finset.sum_le_sum (fun i _ ↦ Finset.sum_le_sum (fun j _ ↦ hYZ i j))
  rw [mean_inner]
  have H := mul_le_mul_of_nonneg_left hSum (sq_nonneg ((m : ℝ)⁻¹))
  convert H using 1 <;> field_simp <;> ring

 theorem scalar_mean_abs_le {m : ℕ} (hm : 0<m) (z : Fin m→ℝ) {a eps : ℝ}
    (hz : ∀i,|z i-a|≤eps) : |(∑i : Fin m,z i)/(m : ℝ)-a|≤eps := by
  have hmR : (0 : ℝ)<m := by exact_mod_cast hm
  have hLo := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ (abs_le.mp (hz i)).1)
  have hHi := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ (abs_le.mp (hz i)).2)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Finset.sum_sub_distrib] at hLo hHi
  rw [abs_le]
  constructor
  · have H : a-eps≤(∑i : Fin m,z i)/(m : ℝ) := by
      apply (le_div_iff₀ hmR).mpr
      nlinarith only [hLo]
    linarith only [H]
  · have H : (∑i : Fin m,z i)/(m : ℝ)≤a+eps := by
      apply (div_le_iff₀ hmR).mpr
      nlinarith only [hHi]
    linarith only [H]

 theorem separated_overlap_bound {m : ℕ} (hm : 0<m) {eps c a b : ℝ}
    (heps : 0≤eps) (hc : -1≤c) (x : E) (Y Z : Fin m→E)
    (hx : ‖x‖=1) (hY : ∀i,‖Y i‖=1) (hZ : ∀i,‖Z i‖=1)
    (hxY : ∀i,|inner ℝ x (Y i)-a|≤eps) (hxZ : ∀i,|inner ℝ x (Z i)-b|≤eps)
    (hYZ : ∀i j,|inner ℝ (Y i) (Z j)-c|≤eps)
    (hYY : ∀i j,i≠j→inner ℝ (Y i) (Y j)≤c+eps)
    (hZZ : ∀i j,i≠j→inner ℝ (Z i) (Z j)≤c+eps) :
    |a-b|≤2*eps+Real.sqrt (4/(m : ℝ)+4*eps) := by
  let y := (m : ℝ)⁻¹ • ∑i : Fin m,Y i
  let z := (m : ℝ)⁻¹ • ∑i : Fin m,Z i
  have hyy : ‖y‖^2≤1/(m : ℝ)+(1-1/(m : ℝ))*(c+eps) := mean_norm_sq_le hm Y hY hYY
  have hzz : ‖z‖^2≤1/(m : ℝ)+(1-1/(m : ℝ))*(c+eps) := mean_norm_sq_le hm Z hZ hZZ
  have hyz : c-eps≤ inner ℝ y z := mean_cross_ge hm Y Z (fun i j ↦ by linarith [(abs_le.mp (hYZ i j)).1])
  have hDistSq : ‖y-z‖^2≤4/(m : ℝ)+4*eps := by
    rw [norm_sub_sq_real]
    have hInv : 0≤1/(m : ℝ) := by positivity
    have h1 := mul_nonneg hInv (by linarith : 0≤c+1)
    have h2 := mul_nonneg hInv heps
    simp only [div_eq_mul_inv,one_mul] at hyy hzz h1 h2 ⊢
    nlinarith only [hyy,hzz,hyz,h1,h2]
  have hDist := Real.le_sqrt_of_sq_le hDistSq
  have hxDiff : |inner ℝ x y-inner ℝ x z|≤Real.sqrt (4/(m : ℝ)+4*eps) := by
    rw [←inner_sub_right]
    have H := abs_real_inner_le_norm x (y-z)
    rw [hx,one_mul] at H
    exact H.trans hDist
  have hxMean (W : Fin m→E) (q : ℝ) (hW : ∀i,|inner ℝ x (W i)-q|≤eps) :
      |inner ℝ x ((m : ℝ)⁻¹ • ∑i : Fin m,W i)-q|≤eps := by
    rw [real_inner_smul_right,inner_sum]
    have H := scalar_mean_abs_le hm (fun i ↦ inner ℝ x (W i)) hW
    simpa only [div_eq_mul_inv,mul_comm] using H
  have hxym : |inner ℝ x y-a|≤eps := hxMean Y a hxY
  have hxzm : |inner ℝ x z-b|≤eps := hxMean Z b hxZ
  calc
    |a-b|≤|a-inner ℝ x y|+|inner ℝ x y-b| := abs_sub_le _ _ _
    _≤|a-inner ℝ x y|+(|inner ℝ x y-inner ℝ x z|+|inner ℝ x z-b|) :=
      add_le_add le_rfl (abs_sub_le _ _ _)
    _≤eps+(Real.sqrt (4/(m : ℝ)+4*eps)+eps) :=
      add_le_add (by rwa [abs_sub_comm]) (add_le_add hxDiff hxzm)
    _=_ := by ring

end TensorPCA.NonRSLowerProofs.FiniteGGBarycenterGeometry
