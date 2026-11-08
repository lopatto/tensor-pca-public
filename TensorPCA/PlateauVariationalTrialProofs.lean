-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.VariationalProofs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Tactic.FieldSimp

/-! Exact evaluation of a positive constant-then-affine trial profile.
The derivative-at-zero boundary term of the Parisi functional is retained. -/
@[expose] public section
namespace TensorPCA.PlateauVariationalTrialProofs
open Set MeasureTheory
noncomputable section

theorem parisiFunctional_plateau (xi : ℝ → ℝ)
    (hxi : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt xi (deriv xi t) t)
    (hxi' : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (deriv xi) (deriv (deriv xi) t) t)
    (hcont : ContinuousOn (deriv (deriv xi)) (Icc (0 : ℝ) 1))
    {delta b s : ℝ} (hd : 0 < delta) (hb : 0 < b) (hs : s ∈ Icc (0 : ℝ) 1) :
    Scalar.parisiFunctional xi 0 (Scalar.fourParameterProfile delta 0 b s) =
      deriv xi 1 * delta + b * (xi 1 - xi s) + s / (delta + b * (1 - s)) +
        Real.log ((delta + b * (1 - s)) / delta) / b := by
  let p := Scalar.fourParameterProfile delta 0 b s
  let c := delta + b * (1 - s)
  have hc : 0 < c := add_pos_of_pos_of_nonneg hd (mul_nonneg hb.le (sub_nonneg.mpr hs.2))
  have hp := VariationalProofs.fourParameterProfile_admissible delta 0 b s
    ⟨hd, le_rfl, hb.le, hs⟩
  have hpc : ContinuousOn p (Icc (0 : ℝ) 1) := hp.1
  have hpp : ∀ t ∈ Icc (0 : ℝ) 1, 0 < p t := hp.2.2.2
  have hInt : IntervalIntegrable (fun t ↦ deriv (deriv xi) t * p t + 1 / p t)
      volume 0 1 :=
    ((hcont.mul hpc).add (continuousOn_const.div hpc
      (fun t ht ↦ (hpp t ht).ne'))).intervalIntegrable_of_Icc zero_le_one
  have hHeadSet : uIcc (0 : ℝ) s ⊆ Icc (0 : ℝ) 1 := by
    rw [uIcc_of_le hs.1]
    exact Icc_subset_Icc le_rfl hs.2
  have hTailSet : uIcc s (1 : ℝ) ⊆ Icc (0 : ℝ) 1 := by
    rw [uIcc_of_le hs.2]
    exact Icc_subset_Icc hs.1 le_rfl
  have hHeadInt := hInt.mono_set (by simpa [uIcc_of_le zero_le_one] using hHeadSet)
  have hTailInt := hInt.mono_set (by simpa [uIcc_of_le zero_le_one] using hTailSet)
  have hHead : (∫ t in (0 : ℝ)..s, deriv (deriv xi) t * p t + 1 / p t) =
      deriv xi s * c + s / c - deriv xi 0 * c := by
    have hderiv : ∀ t ∈ uIcc (0 : ℝ) s,
        HasDerivAt (fun t ↦ deriv xi t * c + t / c)
          (deriv (deriv xi) t * p t + 1 / p t) t := by
      intro t ht
      have hts : t ≤ s := (uIcc_of_le hs.1 ▸ ht).2
      have heq : p t = c := by simp [p, c, Scalar.fourParameterProfile, max_eq_right hts]
      rw [heq]
      convert ((hxi' t (hHeadSet ht)).mul_const c).add ((hasDerivAt_id t).div_const c) using 1 <;>
        (try funext u) <;> simp only [Pi.add_apply, id_eq] <;> ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hHeadInt]
    simp
  have hTail : (∫ t in s..(1 : ℝ), deriv (deriv xi) t * p t + 1 / p t) =
      deriv xi 1 * delta + b * xi 1 - Real.log delta / b -
        (deriv xi s * c + b * xi s - Real.log c / b) := by
    have hderiv : ∀ t ∈ uIcc s (1 : ℝ),
        HasDerivAt (fun t ↦ deriv xi t * (delta + b * (1 - t)) + b * xi t -
          Real.log (delta + b * (1 - t)) / b)
          (deriv (deriv xi) t * p t + 1 / p t) t := by
      intro t ht
      have hst : s ≤ t := (uIcc_of_le hs.2 ▸ ht).1
      have ht1 : t ≤ 1 := (hTailSet ht).2
      have hpos : 0 < delta + b * (1 - t) := by positivity
      have heq : p t = delta + b * (1 - t) := by
        simp [p, Scalar.fourParameterProfile, max_eq_left hst]
      have hA : HasDerivAt (fun t : ℝ ↦ delta + b * (1 - t)) (-b) t := by
        convert (((hasDerivAt_id t).const_sub 1).const_mul b).const_add delta using 1 <;>
          (try funext u) <;> (try simp only [id_eq]) <;> ring
      rw [heq]
      convert (((hxi' t (hTailSet ht)).mul hA).add
        ((hxi t (hTailSet ht)).const_mul b)).sub ((hA.log hpos.ne').div_const b) using 1 <;>
        field_simp [hb.ne', hpos.ne'] <;> ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hTailInt]
    simp [c]
  have hp0 : p 0 = c := by simp [p, c, Scalar.fourParameterProfile, max_eq_right hs.1]
  change (∫ t in (0 : ℝ)..1, deriv (deriv xi) t * p t + 1 / p t) +
      (0 ^ 2 + deriv xi 0) * p 0 = _
  rw [← intervalIntegral.integral_add_adjacent_intervals hHeadInt hTailInt, hHead, hTail,
    hp0, Real.log_div hc.ne' hd.ne']
  dsimp [c]
  ring

theorem parisiFunctional_xiSlice_plateau (k : ℕ) (hk : 1 ≤ k) (m : ℝ)
    {delta b s : ℝ} (hd : 0 < delta) (hb : 0 < b) (hs : s ∈ Icc (0 : ℝ) 1) :
    Scalar.parisiFunctional (Scalar.xiSlice k m) 0 (Scalar.fourParameterProfile delta 0 b s) =
      deriv (Scalar.xiSlice k m) 1 * delta +
        b * (Scalar.xiSlice k m 1 - Scalar.xiSlice k m s) + s / (delta + b * (1 - s)) +
        Real.log ((delta + b * (1 - s)) / delta) / b := by
  apply parisiFunctional_plateau _
    (fun t _ ↦ (VariationalProofs.hasDerivAt_xiSlice k m t).differentiableAt.hasDerivAt)
    (fun t _ ↦ (VariationalProofs.hasDerivAt_deriv_xiSlice hk m t).differentiableAt.hasDerivAt)
    ?_ hd hb hs
  have heq : deriv (deriv (Scalar.xiSlice k m)) = fun t ↦
      (k : ℝ) * ((k : ℝ) - 1) * (1 - m ^ 2) ^ 2 *
        (m ^ 2 + (1 - m ^ 2) * t) ^ (k - 2) := by
    funext t
    exact (VariationalProofs.hasDerivAt_deriv_xiSlice hk m t).deriv
  rw [heq]
  fun_prop


end
end TensorPCA.PlateauVariationalTrialProofs
