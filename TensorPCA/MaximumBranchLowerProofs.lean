-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.MaximumExpectedLowerProofs
public import TensorPCA.EnergyBranchProofs
public import TensorPCA.PureMaximumBridgeProofs

/-! The paper's secondary-branch lower bound (local Lemma 5.4) follows from the Bayesian-value maximum lower reduction and scalar branch.
No physical slice-ground limit or replica-symmetric lower bound is assumed. -/
@[expose] public section
namespace TensorPCA.MaximumBranchLowerProofs
open MeasureTheory ProbabilityTheory Set Filter
open EnergyBranchProofs
open scoped Topology
noncomputable section

/-- The secondary branch is bounded by the reviewed selected scalar value,
including the interval between the spinodal and static thresholds. -/
theorem secondaryBranch_le_mleValue (k : ℕ) (hk : 3 ≤ k) {lam : ℝ}
    (hlam : Scalar.lambdaS k < lam) :
    Scalar.energy k lam (Real.sqrt (Scalar.qS k lam)) ≤ Scalar.mleValue k lam := by
  by_cases habove : Scalar.lambdaC k ≤ lam
  · exact (secondaryBranch_matches_mleValue k hk hlam habove).ge
  · have hbelow : lam < Scalar.lambdaC k := lt_of_not_ge habove
    rw [Scalar.mleValue,ite_eq_left hbelow.le]
    exact (secondaryBranch_below_gs k hk hlam hbelow).le

/-- Finite-dimensional upper boundedness of the original expected
maximum, used only to give its real liminf its ordinary order meaning. -/
theorem expectedMaximum_le_sqrt_add {N k : ℕ} (hN : 0 < N) {lam : ℝ}
    (hlam : 0 ≤ lam) : Model.expectedMaximum N k lam ≤ Real.sqrt (k : ℝ)+lam := by
  have hbase : Model.expectedMaximum N k 0 ≤ Real.sqrt (k : ℝ) := by
    rw [PureMaximumBridgeProofs.expectedMaximum_zero_eq_expectedSliceGround hN]
    simpa only [zero_pow two_ne_zero,sub_zero,mul_one] using
      GroundUpperProofs.expectedSliceGround_le (k := k) hN (m := 0) (by norm_num)
  have hshift := (MaximumDerivativeProofs.expectedMaximum_lipschitz (k := k) hN).le_add_mul lam 0
  have hle : Model.expectedMaximum N k lam ≤ Model.expectedMaximum N k 0+lam := by
    simpa only [NNReal.coe_one,one_mul,Real.dist_eq,sub_zero,abs_of_nonneg hlam] using hshift
  linarith

/-- Every sufficiently large dimension satisfies the secondary-branch
lower bound with arbitrary positive tolerance from the Bayesian values. -/
theorem eventually_expectedMaximum_secondaryBranch_lower_of_values (k : ℕ) (hk : 3 ≤ k)
    (hvalues : CheckedReduction.BayesianValueConvergence k) {lam eps : ℝ} (hlam : Scalar.lambdaS k < lam) (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop,
      Scalar.energy k lam (Real.sqrt (Scalar.qS k lam))-eps ≤
        Model.expectedMaximum (n+1) k lam := by
  have hlam0 : 0 ≤ lam := ((ScalarStationaryProofs.lambdaS_pos k hk).trans hlam).le
  filter_upwards [MaximumExpectedLowerProofs.eventually_expectedMaximum_lower_of_values k hk hvalues hlam0 heps] with n hn
  exact (sub_le_sub_right (secondaryBranch_le_mleValue k hk hlam) eps).trans hn

/-- Lemma 5.4 for the actual scalar secondary-branch energy. The upper bound
required for real-valued liminf is proved uniformly in dimension. -/
theorem secondaryBranch_le_liminf_expectedMaximum_of_values (k : ℕ) (hk : 3 ≤ k)
    (hvalues : CheckedReduction.BayesianValueConvergence k) {lam : ℝ} (hlam : Scalar.lambdaS k < lam) :
    Scalar.energy k lam (Real.sqrt (Scalar.qS k lam)) ≤
      liminf (fun n : ℕ ↦ Model.expectedMaximum (n+1) k lam) atTop := by
  have hlam0 : 0 ≤ lam := ((ScalarStationaryProofs.lambdaS_pos k hk).trans hlam).le
  have hco : atTop.IsCoboundedUnder (· ≥ ·)
      (fun n : ℕ ↦ Model.expectedMaximum (n+1) k lam) :=
    isCoboundedUnder_ge_of_le atTop (fun n ↦ expectedMaximum_le_sqrt_add (Nat.succ_pos n) hlam0)
  apply le_of_forall_pos_le_add
  intro eps heps
  have H := le_liminf_of_le hco
    (eventually_expectedMaximum_secondaryBranch_lower_of_values k hk hvalues hlam heps)
  linarith

/-- Literal displayed conclusion of the paper's Lemma 5.4, valid for every
k≥3 and λ>λs, with the original qS and actual expected likelihood maximum. -/
theorem lemma54_of_values (k : ℕ) (hk : 3 ≤ k)
    (hvalues : CheckedReduction.BayesianValueConvergence k) {lam : ℝ}
    (hlam : Scalar.lambdaS k < lam) :
    Real.sqrt (k : ℝ)*(1+lam^2*(Scalar.qS k lam)^(k-1)) /
      Real.sqrt (1+lam^2*(k : ℝ)*(Scalar.qS k lam)^(k-1)) ≤
      liminf (fun n : ℕ ↦ Model.expectedMaximum (n+1) k lam) atTop := by
  rw [← ScalarValueProofs.branchEnergy_eq_explicit k hk hlam,
    ← energy_at_qS_eq_branchEnergy k hk hlam]
  exact secondaryBranch_le_liminf_expectedMaximum_of_values k hk hvalues hlam

end
end TensorPCA.MaximumBranchLowerProofs
