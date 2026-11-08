-- SPDX-License-Identifier: Apache-2.0
/- Attributed scalar source adaptation from pmaronow/slowequilibration-palomar,
   pin a28aaa336343c4caf43791ababd8ed0ee5c7b58e,
   SlowEquilibration/StrongFieldWholeLine.lean (Apache-2.0). The same explicit Ω is
   represented by the local SemicirclePotential formula; actual density-integral
   identification is a separate required physical bridge. See LICENSE. -/
module

public import TensorPCA.RetainedCountProofs.StrongFieldComplexity

@[expose] public section

/-!
# Symmetry and edge extension of the strong-field exponent

This module uses the proved explicit-potential continuity and evenness. It extends the outside-edge scalar theorem through both edges.
The inner semicircle formula is treated by the subsequent integral bridge.
-/

namespace TensorPCA.RetainedCountProofs.StrongFieldComplexity

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter
open scoped Topology

theorem potential_two : SemicirclePotential.potential 2 = (1/2 : ℝ) :=
  SemicirclePotential.potential_two

theorem radial_even (t u : ℝ) : radial t (-u) = radial t u := by
  simp only [radial, SemicirclePotential.potential_even, neg_sq]

theorem radial_abs (t u : ℝ) : radial t |u| = radial t u := by
  rcases le_or_gt 0 u with hu | hu
  · rw [abs_of_nonneg hu]
  · rw [abs_of_neg hu, radial_even]

theorem radial_edge_lt_zero {t : ℝ} (ht : 1 < t) : radial t 2 < 0 := by
  have h := innerQuadraticRadial_lt_zero (u := (2 : ℝ)) ht (by norm_num)
  convert h using 1
  norm_num [radial, potential_two]

theorem radial_lt_zero_of_abs_ge_two_of_ne {t u : ℝ} (ht : 1 < t)
    (hu : 2 ≤ |u|) (hne : |u| ≠ endpoint t) : radial t u < 0 := by
  rw [← radial_abs t u]
  rcases hu.eq_or_lt with h | h
  · rw [← h]
    exact radial_edge_lt_zero ht
  · exact radial_lt_zero_of_ne_endpoint ht h hne

theorem radial_nonpos_of_abs_ge_two {t u : ℝ} (ht : 1 < t) (hu : 2 ≤ |u|) :
    radial t u ≤ 0 := by
  by_cases he : |u| = endpoint t
  · rw [← radial_abs t u, he, radial_endpoint ht]
  · exact (radial_lt_zero_of_abs_ge_two_of_ne ht hu he).le

theorem radial_eq_zero_iff_of_abs_ge_two {t u : ℝ} (ht : 1 < t) (hu : 2 ≤ |u|) :
    radial t u = 0 ↔ |u| = endpoint t := by
  constructor
  · intro hz
    by_contra he
    have hn := radial_lt_zero_of_abs_ge_two_of_ne ht hu he
    linarith
  · intro he
    rw [← radial_abs t u, he, radial_endpoint ht]

theorem exponent_continuous (a b variance : ℝ) :
    Continuous (fun z : ℝ × ℝ => exponent a b variance z.1 z.2) := by
  have hp : Continuous (fun z : ℝ × ℝ =>
      SemicirclePotential.potential (z.2/Real.sqrt b)) :=
    SemicirclePotential.potential_continuous.comp (continuous_snd.div_const _)
  unfold exponent
  fun_prop

theorem exponent_simultaneous_neg (a b variance h k : ℝ) :
    exponent a b variance (-h) (-k) = exponent a b variance h k := by
  unfold exponent
  rw [neg_div, SemicirclePotential.potential_even, neg_sq]
  have heq : -h-a*(-k)/(a+b) = -(h-a*k/(a+b)) := by ring
  rw [heq, neg_sq]

theorem exponent_nonpos_of_abs_ge_edge {a b variance h k : ℝ}
    (hb : 0 < b) (hab : b < a) (hvariance : 0 < variance)
    (hk : 2*Real.sqrt b ≤ |k|) : exponent a b variance h k ≤ 0 := by
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hu : 2 ≤ |k/Real.sqrt b| := by
    rw [abs_div, abs_of_pos hs]
    exact (le_div_iff₀ hs).mpr hk
  have hg := radial_nonpos_of_abs_ge_two (ratio_gt_one hb hab) hu
  rw [radial_physical hb hab] at hg
  have ht : 0 ≤ (h-a*k/(a+b))^2/(2*variance) := by positivity
  unfold exponent
  linarith

/-- The literal BCNS exponent has exactly two zero pairs in the two closed
outside-edge regions. -/
theorem exponent_eq_zero_iff_of_abs_ge_edge {a b variance h k : ℝ}
    (hb : 0 < b) (hab : b < a) (hvariance : 0 < variance)
    (hk : 2*Real.sqrt b ≤ |k|) :
    exponent a b variance h k = 0 ↔
      (h = Real.sqrt a ∧ k = radialEndpoint a b) ∨
      (h = -Real.sqrt a ∧ k = -radialEndpoint a b) := by
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hu : 2 ≤ |k/Real.sqrt b| := by
    rw [abs_div, abs_of_pos hs]
    exact (le_div_iff₀ hs).mpr hk
  have ht := ratio_gt_one hb hab
  have hg := radial_nonpos_of_abs_ge_two ht hu
  have htail : 0 ≤ (h-a*k/(a+b))^2/(2*variance) := by positivity
  have heq : exponent a b variance h k =
      radial (a/b) (k/Real.sqrt b) - (h-a*k/(a+b))^2/(2*variance) := by
    rw [radial_physical hb hab]
    rfl
  constructor
  · intro hz
    rw [heq] at hz
    have hg0 : radial (a/b) (k/Real.sqrt b) = 0 := by linarith
    have hk0 := (radial_eq_zero_iff_of_abs_ge_two ht hu).mp hg0
    rw [abs_div, abs_of_pos hs, ← radialEndpoint_normalized hb hab] at hk0
    have hke : |k| = radialEndpoint a b := (div_left_inj' hs.ne').mp hk0
    have hzero : (h-a*k/(a+b))^2 = 0 := by
      have htail0 : (h-a*k/(a+b))^2/(2*variance) = 0 := by linarith
      exact (div_eq_zero_iff).mp htail0 |>.resolve_right (by positivity)
    have hm : h = a*k/(a+b) := by nlinarith [sq_nonneg (h-a*k/(a+b))]
    rcases eq_or_eq_neg_of_abs_eq hke with hpos | hneg
    · left
      refine ⟨?_, hpos⟩
      rw [hpos, endpoint_height hb hab] at hm
      exact hm
    · right
      refine ⟨?_, hneg⟩
      rw [hneg, mul_neg, neg_div, endpoint_height hb hab] at hm
      exact hm
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rw [heq, endpoint_height hb hab, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
        zero_div, sub_zero, radialEndpoint_normalized hb hab, radial_endpoint ht]
    · rw [exponent_simultaneous_neg]
      rw [exponent, endpoint_height hb hab, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
        zero_div, sub_zero, ← radial_physical hb hab,
        radialEndpoint_normalized hb hab, radial_endpoint ht]

/-- Actual strict compact gaps away from the two endpoint heights, in
the two closed exterior spectral regions, including the edges themselves. -/
theorem exists_uniform_exponent_gap_of_abs_ge_edge {a b variance : ℝ}
    (hb : 0 < b) (hab : b < a) (hvariance : 0 < variance)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hregion : ∀ z ∈ K, 2*Real.sqrt b ≤ |z.2|)
    (hheight : ∀ z ∈ K, |z.1| ≠ Real.sqrt a) :
    ∃ η : ℝ, 0 < η ∧ ∀ z ∈ K, exponent a b variance z.1 z.2 ≤ -η := by
  by_cases hne : K.Nonempty
  · obtain ⟨z, hz, hmax⟩ := hK.exists_isMaxOn hne
      (exponent_continuous a b variance).continuousOn
    have hle := exponent_nonpos_of_abs_ge_edge (h := z.1) hb hab hvariance (hregion z hz)
    have hstrict : exponent a b variance z.1 z.2 < 0 := by
      apply lt_of_le_of_ne hle
      intro heq
      have he := (exponent_eq_zero_iff_of_abs_ge_edge hb hab hvariance (hregion z hz)).mp heq
      have ha : 0 < a := hb.trans hab
      apply hheight z hz
      rcases he with he | he
      · rw [he.1, abs_of_pos (Real.sqrt_pos.mpr ha)]
      · rw [he.1, abs_neg, abs_of_pos (Real.sqrt_pos.mpr ha)]
    refine ⟨-exponent a b variance z.1 z.2/2, by linarith, ?_⟩
    intro w hw
    have hm : exponent a b variance w.1 w.2 ≤ exponent a b variance z.1 z.2 := hmax hw
    linarith
  · refine ⟨1, by norm_num, ?_⟩
    intro z hz
    exact (hne ⟨z, hz⟩).elim

end
end TensorPCA.RetainedCountProofs.StrongFieldComplexity

