-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.PureGroundLowerFromBayesianProofs

/-! A large-strength planted anchor gives the mean-maximum lower bound
at every fixed nonnegative strength. Reverse Fatou is applied directly on the
relevant interval; no subtraction of two limsup bounds or physical ground-state
formula is used. -/
@[expose] public section
namespace TensorPCA.MaximumExpectedLowerProofs
open MeasureTheory ProbabilityTheory Set Filter
open MaximumDerivativeProofs MaximumIntegralProofs MaximumIntegralLimitProofs
open PureGroundLowerFromBayesianProofs
open scoped Topology RealInnerProductSpace
noncomputable section

/-- The reviewed scalar slope is integrable on every finite interval,
including intervals crossing the critical selection jump. -/
theorem scalar_rootPower_intervalIntegrable (k : ℕ) (hk : 3 ≤ k) (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ ↦ (Real.sqrt (Scalar.qStar k t))^k) volume a b := by
  apply (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ ↦ (1 : ℝ)) volume a b).mono_fun
  · exact (((qStar_measurable k hk).sqrt).pow_const k).aestronglyMeasurable
  · exact Eventually.of_forall fun t ↦ by
      simpa only [Real.norm_eq_abs,abs_one] using qStar_rootPower_abs_le_one k hk t

theorem scalar_value_difference_integral (k : ℕ) (hk : 3 ≤ k)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∫ t in a..b, (Real.sqrt (Scalar.qStar k t))^k) =
      Scalar.mleValue k b-Scalar.mleValue k a := by
  have H := intervalIntegral.integral_add_adjacent_intervals
    (scalar_rootPower_intervalIntegrable k hk 0 a) (scalar_rootPower_intervalIntegrable k hk a b)
  have hA : Scalar.mleValue k a = Scalar.gs k+
      ∫ t in (0 : ℝ)..a, (Real.sqrt (Scalar.qStar k t))^k := ScalarValueProofs.valueIdentity k hk ha
  have hB : Scalar.mleValue k b = Scalar.gs k+
      ∫ t in (0 : ℝ)..b, (Real.sqrt (Scalar.qStar k t))^k := ScalarValueProofs.valueIdentity k hk hb
  linarith only [H,hA,hB]

/-- Direct bounded reverse Fatou on `[a,b]`. The single critical strength is
removed only on a Lebesgue-null singleton, as in the original zero-endpoint
integral lemma. Bayesian values are the sole asymptotic proof parameter. -/
theorem integrated_selectedSlope_limsup_le_interval_of_values (k : ℕ) (hk : 3 ≤ k)
    (hvalues : CheckedReduction.BayesianValueConvergence k) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    limsup (fun n : ℕ ↦ ∫ t in a..b, selectedSlope (n+1) (k-1) (Nat.succ_pos n) t) atTop ≤
      ∫ t in a..b, (Real.sqrt (Scalar.qStar k t))^k := by
  have hkeq : k-1+1 = k := by omega
  have hAE : ∀ᵐ t : ℝ ∂volume.restrict (Ioc a b),
      limsup (fun n ↦ selectedSlope (n+1) (k-1) (Nat.succ_pos n) t) atTop ≤
        (Real.sqrt (Scalar.qStar k t))^k := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      (ae_restrict_of_ae (show ∀ᵐ t : ℝ ∂volume, t ≠ Scalar.lambdaC k from by simp [ae_iff]))]
      with t ht hne
    have H := selectedSlope_limsup_le_of_values (k-1) (by omega)
      (by simpa only [hkeq] using hvalues) (ha.trans ht.1.le)
      (by simpa only [hkeq] using hne)
    simpa only [hkeq] using H
  have H := limsup_integral_le_of_unit_bound (volume.restrict (Ioc a b))
    (fun n : ℕ ↦ selectedSlope (n+1) (k-1) (Nat.succ_pos n))
    (fun t ↦ (Real.sqrt (Scalar.qStar k t))^k)
    (fun n ↦ selectedSlope_measurable (n+1) (k-1) (Nat.succ_pos n))
    (((qStar_measurable k hk).sqrt).pow_const k)
    (fun n t ↦ selectedSlope_abs_le_one (n+1) (k-1) (Nat.succ_pos n) t)
    (qStar_rootPower_abs_le_one k hk) hAE
  simpa only [intervalIntegral.integral_of_le hab] using H

/-- The lower mean bound at every strength, including
zero and the critical value. No physical pure/RS/mixed ground-state limit or
critical-count estimate is assumed. -/
theorem eventually_expectedMaximum_lower_of_values (k : ℕ) (hk : 3 ≤ k)
    (hvalues : CheckedReduction.BayesianValueConvergence k) {lam eps : ℝ}
    (hlam : 0 ≤ lam) (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop, Scalar.mleValue k lam-eps ≤ Model.expectedMaximum (n+1) k lam := by
  have hkeq : k-1+1 = k := by omega
  obtain ⟨B,hsmall,hB⟩ := ((mleValue_sub_strength_eventually_lt k hk (half_pos heps)).and
    (eventually_ge_atTop lam)).exists
  let I := fun n : ℕ ↦ ∫ t in lam..B, selectedSlope (n+1) (k-1) (Nat.succ_pos n) t
  have hIbound (n : ℕ) : |I n| ≤ |B-lam| := by
    have H := intervalIntegral.norm_integral_le_of_norm_le_const (a := lam) (b := B)
      (C := (1 : ℝ)) (f := selectedSlope (n+1) (k-1) (Nat.succ_pos n)) (fun t _ ↦ by
        simpa only [Real.norm_eq_abs] using selectedSlope_abs_le_one (n+1) (k-1) (Nat.succ_pos n) t)
    simpa only [I,Real.norm_eq_abs,one_mul] using H
  have hIupper : atTop.IsBoundedUnder (· ≤ ·) I :=
    isBoundedUnder_of ⟨|B-lam|,fun n ↦ (abs_le.mp (hIbound n)).2⟩
  have hIntegral : limsup I atTop ≤ Scalar.mleValue k B-Scalar.mleValue k lam := by
    have H := integrated_selectedSlope_limsup_le_interval_of_values k hk hvalues hlam hB
    exact H.trans_eq (scalar_value_difference_integral k hk hlam (hlam.trans hB))
  have hEvent := eventually_lt_add_pos_of_limsup_le hIupper hIntegral (half_pos heps)
  filter_upwards [hEvent] with n hn
  have hFinite := expectedMaximum_integral_identity (n+1) (k-1) (Nat.succ_pos n) lam B
  rw [hkeq] at hFinite
  have hPlant := strength_le_expectedMaximum (k := k) (Nat.succ_pos n) B
  dsimp only [I] at hn
  linarith only [hn,hFinite,hPlant,hsmall]

end
end TensorPCA.MaximumExpectedLowerProofs
