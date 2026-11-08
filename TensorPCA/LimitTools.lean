-- Copyright (c) 2026 Patrick Lopatto. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Topology.Order.LiminfLimsup
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Tactic.Ring
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import Mathlib.MeasureTheory.Measure.Basic

@[expose] public section

/-! Small mathematical limit-composition lemmas used by the parameterized paper
reduction. These statements do not refer to the tensor experiment or its targets.
The final secant derivative criterion is proved from the derivative slope limit. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace TensorPCA.LimitTools

open Filter MeasureTheory
open scoped Topology ENNReal

/-- Add back a vanishing discrepancy after the deterministic part converges. -/
theorem tendsto_of_vanishing_error {f a : ℕ → ℝ} {l : ℝ}
    (herr : Tendsto (fun n => f n - a n) atTop (𝓝 0))
    (ha : Tendsto a atTop (𝓝 l)) : Tendsto f atTop (𝓝 l) := by
  simpa only [sub_add_cancel, zero_add] using herr.add ha

/-- A bounded-below sequence dominated eventually by arbitrarily close upper
limits has limsup at most the limiting upper bound. Every `g` is an actual real
sequence, not an assumed limsup inequality. -/
theorem limsup_le_of_eventual_upper_envelopes {f : ℕ → ℝ} {L m : ℝ}
    (hlower : ∀ n : ℕ, m ≤ f n)
    (henvelope : ∀ eps : ℝ, 0 < eps → ∃ g : ℕ → ℝ,
      (∀ᶠ n in atTop, f n ≤ g n) ∧ Tendsto g atTop (𝓝 (L + eps))) :
    limsup f atTop ≤ L := by
  apply le_of_forall_pos_le_add
  intro eps heps
  obtain ⟨g, hfg, hg⟩ := henvelope eps heps
  calc
    limsup f atTop ≤ limsup g atTop :=
      limsup_le_limsup hfg (isCoboundedUnder_le_of_le atTop hlower)
        hg.isBoundedUnder_le
    _ = L + eps := hg.limsup_eq

/-- Countably many lower and upper envelopes, whose limits approach the same
value, force the enclosed sequence to converge. This is the logical squeeze
behind the fixed-parameter secant argument. -/
theorem tendsto_of_eventual_envelopes
    {d : ℕ → ℝ} {lo hi : ℕ → ℕ → ℝ} {a b : ℕ → ℝ} {D : ℝ}
    (hlo : ∀ j : ℕ, Tendsto (lo j) atTop (𝓝 (a j)))
    (hhi : ∀ j : ℕ, Tendsto (hi j) atTop (𝓝 (b j)))
    (hbounds : ∀ j : ℕ, ∀ᶠ n in atTop, lo j n ≤ d n ∧ d n ≤ hi j n)
    (ha : Tendsto a atTop (𝓝 D)) (hb : Tendsto b atTop (𝓝 D)) :
    Tendsto d atTop (𝓝 D) := by
  apply tendsto_order.mpr
  constructor
  · intro c hc
    obtain ⟨j, hj⟩ := ((tendsto_order.mp ha).1 c hc).exists
    filter_upwards [(tendsto_order.mp (hlo j)).1 c hj, hbounds j] with n hn hbound
    exact hn.trans_le hbound.1
  · intro c hc
    obtain ⟨j, hj⟩ := ((tendsto_order.mp hb).2 c hc).exists
    filter_upwards [(tendsto_order.mp (hhi j)).2 c hj, hbounds j] with n hn hbound
    exact hbound.2.trans_lt hn

/-- Positive, countable secant increments at a positive base parameter. -/
noncomputable def secantStep (a : ℝ) (j : ℕ) : ℝ :=
  a / ((j : ℝ) + 2)

/-- Exact generic derivative-stability criterion. Its hypotheses supply only
nearby function values, two-sided secant bounds, and differentiability of the
limiting function. No derivative convergence is assumed. The interval points
`a ± a/(j+2)` remain positive when `a>0`. The theorem below proves this criterion; it is not a tensor-specific conclusion. -/
def SecantDerivativeStability : Prop :=
  ∀ (f : ℕ → ℝ → ℝ) (l : ℝ → ℝ) (d : ℕ → ℝ) (a D : ℝ),
    0 < a →
    Tendsto (fun n => f n a) atTop (𝓝 (l a)) →
    (∀ j : ℕ, Tendsto (fun n => f n (a - secantStep a j)) atTop
      (𝓝 (l (a - secantStep a j)))) →
    (∀ j : ℕ, Tendsto (fun n => f n (a + secantStep a j)) atTop
      (𝓝 (l (a + secantStep a j)))) →
    (∀ j : ℕ, ∀ᶠ n in atTop,
      (f n a - f n (a - secantStep a j)) / secantStep a j ≤ d n ∧
      d n ≤ (f n (a + secantStep a j) - f n a) / secantStep a j) →
    HasDerivAt l D a → Tendsto d atTop (𝓝 D)

/-- The secant derivative criterion follows from the actual derivative slope
limit and the generic countable-envelope squeeze. -/
theorem secantDerivativeStability : SecantDerivativeStability := by
  intro f l d a D ha hcenter hleft hright hbounds hderiv
  have hpos (j : ℕ) : 0 < secantStep a j :=
    div_pos ha (add_pos_of_nonneg_of_pos (Nat.cast_nonneg j) zero_lt_two)
  have hdenom : Tendsto (fun j : ℕ => (j : ℝ) + 2) atTop atTop :=
    tendsto_atTop_mono (fun j : ℕ => le_add_of_nonneg_right (le_of_lt zero_lt_two))
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hzero : Tendsto (secantStep a) atTop (𝓝 0) := hdenom.const_div_atTop a
  have hgt : Tendsto (secantStep a) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzero, Eventually.of_forall hpos⟩
  have hlt : Tendsto (fun j => -secantStep a j) atTop (𝓝[<] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨by simpa only [neg_zero] using hzero.neg,
        Eventually.of_forall (fun j => neg_lt_zero.mpr (hpos j))⟩
  have hrightLimit : Tendsto
      (fun j => (l (a + secantStep a j) - l a) / secantStep a j)
      atTop (𝓝 D) := by
    simpa only [Function.comp_def, smul_eq_mul, div_eq_mul_inv, mul_comm] using
      hderiv.tendsto_slope_zero_right.comp hgt
  have hleftLimit : Tendsto
      (fun j => (l a - l (a - secantStep a j)) / secantStep a j)
      atTop (𝓝 D) := by
    convert hderiv.tendsto_slope_zero_left.comp hlt using 1
    funext j
    simp only [Function.comp_def, smul_eq_mul, sub_eq_add_neg,
      div_eq_mul_inv]
    ring
  exact tendsto_of_eventual_envelopes
    (fun j => (hcenter.sub (hleft j)).div_const (secantStep a j))
    (fun j => ((hright j).sub hcenter).div_const (secantStep a j))
    hbounds hleftLimit hrightLimit

/-- Recover convergence from a positive integer power on the nonnegative half
line by continuity of the real `k`th root, including the zero limit. -/
theorem nonnegative_power_limit {f : ℕ → ℝ} {r : ℝ} {k : ℕ}
    (hk : 0 < k) (hf : ∀ n : ℕ, 0 ≤ f n) (hr : 0 ≤ r)
    (hpow : Tendsto (fun n => f n ^ k) atTop (𝓝 (r ^ k))) :
    Tendsto f atTop (𝓝 r) := by
  have hroot := ((Real.continuous_rpow_const (q := (k : ℝ)⁻¹)
    (inv_nonneg.mpr (Nat.cast_nonneg k))).continuousAt.tendsto).comp hpow
  have hfun : (fun n => Real.rpow (f n ^ k) (k : ℝ)⁻¹) = f := by
    funext n
    exact Real.pow_rpow_inv_natCast (hf n) (Nat.ne_of_gt hk)
  change Tendsto (fun n => Real.rpow (f n ^ k) (k : ℝ)⁻¹) atTop
    (𝓝 (Real.rpow (r ^ k) (k : ℝ)⁻¹)) at hroot
  have hrfun : Real.rpow (r ^ k) (k : ℝ)⁻¹ = r :=
    Real.pow_rpow_inv_natCast hr (Nat.ne_of_gt hk)
  rw [hfun, hrfun] at hroot
  exact hroot

/-- A positive-to-negative derivative sign change gives a strict local maximum.
Continuity is imposed on the closed interval so the mean-value monotonicity
lemmas apply up to the central point. -/
theorem strict_local_max_of_deriv_sign_change {f : ℝ → ℝ} {a eps : ℝ}
    (heps : 0 < eps)
    (hf : ContinuousOn f (Set.Icc (a - eps) (a + eps)))
    (hpos : ∀ x ∈ Set.Ioo (a - eps) a, 0 < deriv f x)
    (hneg : ∀ x ∈ Set.Ioo a (a + eps), deriv f x < 0) :
    ∀ y : ℝ, y ≠ a → |y - a| < eps → f y < f a := by
  have hmono : StrictMonoOn f (Set.Icc (a - eps) a) :=
    strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (hf.mono (by
        intro x hx
        exact ⟨hx.1, hx.2.trans (le_add_of_nonneg_right heps.le)⟩))
      (by simpa only [interior_Icc] using hpos)
  have hanti : StrictAntiOn f (Set.Icc a (a + eps)) :=
    strictAntiOn_of_deriv_neg (convex_Icc _ _)
      (hf.mono (by
        intro x hx
        exact ⟨(sub_le_self a heps.le).trans hx.1, hx.2⟩))
      (by simpa only [interior_Icc] using hneg)
  intro y hyne hy
  have hylo : a - eps < y := by
    simpa only [sub_eq_add_neg, add_comm] using
      (lt_sub_iff_add_lt.mp (abs_lt.mp hy).1)
  have hyhi : y < a + eps := by
    simpa only [add_comm] using (sub_lt_iff_lt_add.mp (abs_lt.mp hy).2)
  rcases lt_or_gt_of_ne hyne with hya | hay
  · exact hmono ⟨hylo.le, hya.le⟩ ⟨sub_le_self a heps.le, le_rfl⟩ hya
  · exact hanti ⟨le_rfl, le_add_of_nonneg_right heps.le⟩ ⟨hay.le, hyhi.le⟩ hay

/-- First Borel--Cantelli for a nonnegative real triangular sequence on any
measure space. Finite sums of every fixed positive tail suffice; no independence
between dimensions is assumed. The proof uses only countably many thresholds. -/
theorem ae_tendsto_zero_of_summable_tails {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (f : ℕ → Ω → ℝ)
    (hnonneg : ∀ n : ℕ, ∀ w : Ω, 0 ≤ f n w)
    (hsum : ∀ eps : ℝ, 0 < eps →
      (∑' n : ℕ, μ {w : Ω | eps ≤ f n w}) ≠ ∞) :
    ∀ᵐ w ∂μ, Tendsto (fun n => f n w) atTop (𝓝 0) := by
  let v : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hvpos (j : ℕ) : 0 < v j :=
    div_pos zero_lt_one (add_pos_of_nonneg_of_pos (Nat.cast_nonneg j) zero_lt_one)
  have hdenom : Tendsto (fun j : ℕ => (j : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun j : ℕ => le_add_of_nonneg_right (le_of_lt zero_lt_one))
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hvzero : Tendsto v atTop (𝓝 0) := hdenom.const_div_atTop 1
  have hAE : ∀ j : ℕ, ∀ᵐ w ∂μ, ∀ᶠ n in atTop, f n w < v j := by
    intro j
    simpa only [Set.mem_ofPred_eq, not_le] using
      MeasureTheory.ae_eventually_notMem (hsum (v j) (hvpos j))
  filter_upwards [MeasureTheory.ae_all_iff.mpr hAE] with w hw
  apply tendsto_order.mpr
  constructor
  · intro c hc
    exact Eventually.of_forall (fun n => hc.trans_le (hnonneg n w))
  · intro c hc
    obtain ⟨j, hj⟩ := ((tendsto_order.mp hvzero).2 c hc).exists
    exact (hw j).mono (fun n hn => hn.trans hj)





end TensorPCA.LimitTools
