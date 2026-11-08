-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.MaximumExpectedLowerProofs
public import TensorPCA.MaximumSecantProofs
public import TensorPCA.ZeroSignalProofs

/-! Reduction from Bayesian values and the one-sided pure null upper bound. The independently proved Bayesian values are combined in the final assembly. No RS slice-ground or critical-count lower hypothesis is used.
These are parameterized reductions, not final principal exports. -/
@[expose] public section
namespace TensorPCA.MaximumFromPureUpperProofs
open MeasureTheory ProbabilityTheory Set Filter
open MaximumExpectedUpperProofs MaximumDerivativeProofs
open scoped Topology RealInnerProductSpace
noncomputable section
universe u v

private theorem centeredTails : CheckedReduction.CenteredMaximumTails.{u} := by
  intro k _hk lam _hlam Omega _ mu _ E eps heps
  exact MaximumProofs.centeredMaximum_summable_tails E lam eps heps

/-- The Bayesian anchor lower bound and a one-sided null upper bound give the physical pure baseline limit. -/
theorem expectedMaximum_zero_tendsto_of_pure_upper
    (hvalues : ∀ k : ℕ, 3 ≤ k → CheckedReduction.BayesianValueConvergence k)
    (hUpper : ∀ k : ℕ, 3 ≤ k → ∀ eps : ℝ, 0 < eps →
      ∀ᶠ n : ℕ in atTop, Model.expectedMaximum (n+1) k 0 ≤ Scalar.gs k+eps)
    (k : ℕ) (hk : 3 ≤ k) :
    Tendsto (fun n : ℕ ↦ Model.expectedMaximum (n+1) k 0) atTop (𝓝 (Scalar.gs k)) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have he : 0 < (Scalar.gs k-a)/2 := by linarith
    filter_upwards [PureGroundLowerFromBayesianProofs.eventually_expectedMaximum_zero_lower_of_values
      k hk (hvalues k hk) he] with n hn
    linarith
  · intro b hb
    have he : 0 < (b-Scalar.gs k)/2 := by linarith
    filter_upwards [hUpper k hk ((b-Scalar.gs k)/2) he] with n hn
    linarith

/-- Every fixed strength, including the critical value, follows from the
pure upper input alone; the lower is the proved large-strength anchor route. -/
theorem expectedMaximum_tendsto_of_pure_upper
    (hvalues : ∀ k : ℕ, 3 ≤ k → CheckedReduction.BayesianValueConvergence k)
    (hUpper : ∀ k : ℕ, 3 ≤ k → ∀ eps : ℝ, 0 < eps →
      ∀ᶠ n : ℕ in atTop, Model.expectedMaximum (n+1) k 0 ≤ Scalar.gs k+eps)
    (k : ℕ) (hk : 3 ≤ k) {lam : ℝ} (hlam : 0 ≤ lam) :
    Tendsto (fun n : ℕ ↦ Model.expectedMaximum (n+1) k lam) atTop (𝓝 (Scalar.mleValue k lam)) := by
  have hkeq : k-1+1=k := by omega
  have hbase:=expectedMaximum_zero_tendsto_of_pure_upper hvalues hUpper k hk
  have hupper : limsup (fun n : ℕ ↦ Model.expectedMaximum (n+1) k lam) atTop ≤ Scalar.mleValue k lam := by
    have H:=expectedMaximum_limsup_upper_of_values_and_baseline (k-1) (by omega)
      (by simpa only [hkeq] using hvalues k hk)
      (by simpa only [hkeq] using hbase) hlam
    simpa only [hkeq] using H
  have hpoint (n : ℕ) : Model.expectedMaximum (n+1) k lam ≤ Model.expectedMaximum (n+1) k 0+lam := by
    have H:=(expectedMaximum_lipschitz (k:=k) (Nat.succ_pos n)).le_add_mul lam 0
    simpa only [NNReal.coe_one,one_mul,Real.dist_eq,sub_zero,abs_of_nonneg hlam] using H
  have hbounded : atTop.IsBoundedUnder (· ≤ ·) (fun n : ℕ ↦ Model.expectedMaximum (n+1) k lam) :=
    (isBoundedUnder_le_add hbase.isBoundedUnder_le
      (isBoundedUnder_const : atTop.IsBoundedUnder (· ≤ ·) (fun _n : ℕ ↦ lam))).mono_le
        (Eventually.of_forall hpoint)
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have he : 0 < (Scalar.mleValue k lam-a)/2 := by linarith
    filter_upwards [MaximumExpectedLowerProofs.eventually_expectedMaximum_lower_of_values
      k hk (hvalues k hk) hlam he] with n hn
    linarith
  · intro b hb
    exact eventually_lt_of_limsup_lt (hupper.trans_lt hb) hbounded

theorem meanMaximumLimit_of_pure_upper
    (hvalues : ∀ k : ℕ, 3 ≤ k → CheckedReduction.BayesianValueConvergence k)
    (hUpper : ∀ k : ℕ, 3 ≤ k → ∀ eps : ℝ, 0 < eps →
      ∀ᶠ n : ℕ in atTop, Model.expectedMaximum (n+1) k 0 ≤ Scalar.gs k+eps) :
    CheckedReduction.MeanMaximumLimit := by
  intro k hk lam hlam
  exact expectedMaximum_tendsto_of_pure_upper hvalues hUpper k hk hlam

/-- Core conditional principal value reduction. Binding the already proved
Bayesian values leaves just the actual pure null upper input. -/
theorem mleValue_of_pure_upper
    (hvalues : ∀ k : ℕ, 3 ≤ k → CheckedReduction.BayesianValueConvergence k)
    (hUpper : ∀ k : ℕ, 3 ≤ k → ∀ eps : ℝ, 0 < eps →
      ∀ᶠ n : ℕ in atTop, Model.expectedMaximum (n+1) k 0 ≤ Scalar.gs k+eps) :
    Statements.MLEValue.{u} :=
  CheckedReduction.mleValue (meanMaximumLimit_of_pure_upper hvalues hUpper)
    centeredTails

/-- Conditional arbitrary-randomization MLE overlap reduction from the same one-sided pure upper input, retaining the zero-strength branch. -/
theorem mleOverlap_of_pure_upper
    (hvalues : ∀ k : ℕ, 3 ≤ k → CheckedReduction.BayesianValueConvergence k)
    (hUpper : ∀ k : ℕ, 3 ≤ k → ∀ eps : ℝ, 0 < eps →
      ∀ᶠ n : ℕ in atTop, Model.expectedMaximum (n+1) k 0 ≤ Scalar.gs k+eps) :
    Statements.MLEOverlap.{u,v} := by
  apply CheckedReduction.mleOverlap (meanMaximumLimit_of_pure_upper hvalues hUpper)
    centeredTails MaximumSecantProofs.maximumEnvelopeSecants
  · intro k _hk Omega _ mu _ E A _ nu _ R _hMLE eps heps
    exact ZeroSignalProofs.zeroSignal_overlap_summable_tails R eps heps
  · exact ScalarSelectionProofs.selectionLaws
  · exact ScalarValueProofs.valueDerivative

end
end TensorPCA.MaximumFromPureUpperProofs
