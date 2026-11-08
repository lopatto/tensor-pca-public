-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
/- Scalar formulas adapted from pmaronow/slowequilibration-palomar,
   immutable pin a28aaa336343c4caf43791ababd8ed0ee5c7b58e,
   SlowEquilibration/SemicirclePotential.lean. The explicit whole-line formula
   is used as an internal representation. Its identification with the actual
   semicircle logarithmic integral remains required before transferring a
   physical GOE theorem stated using that integral. See LICENSE. -/
module
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! The standard explicit semicircle logarithmic potential. The `max` makes
its interior branch and continuity at both spectral edges fully explicit. -/
@[expose] public section
namespace TensorPCA.RetainedCountProofs.SemicirclePotential
open Set
noncomputable section
set_option backward.isDefEq.respectTransparency false

def potential (u : ℝ) : ℝ :=
  u^2/4-1/2-|u| * Real.sqrt (u^2-4)/4+
    Real.log ((max 2 |u|+Real.sqrt (u^2-4))/2)

theorem potential_even (u : ℝ) : potential (-u) = potential u := by
  simp only [potential, neg_sq, abs_neg]

theorem potential_abs (u : ℝ) : potential |u| = potential u := by
  simp only [potential, sq_abs, abs_abs]

theorem potential_eq_inside (u : ℝ) (hu : |u| ≤ 2) : potential u = u^2/4-1/2 := by
  have hsq : u^2-4 ≤ 0 := by have h := abs_le.mp hu; nlinarith
  simp only [potential, Real.sqrt_eq_zero_of_nonpos hsq, mul_zero, zero_div,
    sub_zero, max_eq_left hu, add_zero, div_self (by norm_num : (2 : ℝ) ≠ 0), Real.log_one]

theorem potential_explicit {u : ℝ} (hu : 2 < u) :
    potential u = u^2/4-1/2-u*Real.sqrt (u^2-4)/4+
      Real.log ((u+Real.sqrt (u^2-4))/2) := by
  simp only [potential, abs_of_pos (by linarith : 0 < u), max_eq_right hu.le]

theorem potential_two : potential 2 = (1/2 : ℝ) := by
  rw [potential_eq_inside 2 (by norm_num)]
  norm_num

theorem potential_continuous : Continuous potential := by
  unfold potential
  apply Continuous.add
  · fun_prop
  · apply Continuous.log
    · fun_prop
    · intro u
      have hm := le_max_left (2 : ℝ) |u|
      have hs := Real.sqrt_nonneg (u^2-4)
      positivity

theorem potential_hasDerivAt_explicit {u : ℝ} (hu : 2 < u) :
    HasDerivAt potential ((u-Real.sqrt (u^2-4))/2) u := by
  have hs : 0 < Real.sqrt (u^2-4) := Real.sqrt_pos.mpr (by nlinarith)
  have ha : 0 < (u+Real.sqrt (u^2-4))/2 := by positivity
  have hroot := (((hasDerivAt_id u).pow 2).sub_const 4).sqrt (by dsimp; nlinarith : (id^2) u-4 ≠ 0)
  have hp := (((hasDerivAt_id u).pow 2).div_const 4).sub_const (1/2 : ℝ)
  have hm := ((hasDerivAt_id u).mul hroot).div_const 4
  have hl := (((hasDerivAt_id u).add hroot).div_const 2).log ha.ne'
  have hd := (hp.sub hm).add hl
  have he : potential =ᶠ[nhds u] (fun v : ℝ ↦ v^2/4-1/2-v*Real.sqrt (v^2-4)/4+
      Real.log ((v+Real.sqrt (v^2-4))/2)) := by
    filter_upwards [Ioi_mem_nhds hu] with v hv
    exact potential_explicit hv
  apply (hd.congr_of_eventuallyEq he).congr_deriv
  have hsq := Real.sq_sqrt (show 0 ≤ u^2-4 by nlinarith)
  simp only [Pi.pow_apply, Pi.add_apply, Pi.mul_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one, one_mul]
  have hsum : u+Real.sqrt (u^2-4) ≠ 0 := by positivity
  field_simp [hs.ne', hsum]
  nlinarith

theorem potential_le_abs_add_two (u : ℝ) : potential u ≤ |u|+2 := by
  rw [← potential_abs u]
  by_cases hu : |u| ≤ 2
  · rw [potential_eq_inside |u| (by simpa only [abs_abs] using hu)]
    have hsq : |u|^2 ≤ 4 := by nlinarith [abs_nonneg u]
    nlinarith [abs_nonneg u]
  · have h2 : 2 < |u| := lt_of_not_ge hu
    rw [potential_explicit h2]
    have hs := Real.sqrt_nonneg (|u|^2-4)
    have hsq := Real.sq_sqrt (show 0 ≤ |u|^2-4 by nlinarith)
    have hle : Real.sqrt (|u|^2-4) ≤ |u| := by nlinarith [abs_nonneg u]
    have hprod := mul_nonneg hs (sub_nonneg.mpr hle)
    have hlog := Real.log_le_self (show 0 ≤ (|u|+Real.sqrt (|u|^2-4))/2 by positivity)
    nlinarith

end
end TensorPCA.RetainedCountProofs.SemicirclePotential
