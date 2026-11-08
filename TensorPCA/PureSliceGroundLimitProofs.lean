-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.PureMaximumUpperProofs
public import TensorPCA.PureMaximumBridgeProofs
public import TensorPCA.MaximumFromPureUpperProofs
public import TensorPCA.BayesianValueProofs

/-! The pure (zero-overlap) slice-ground limit. Bayesian values give
the lower bound; the determinant/Kac--Rice chain gives the
upper bound. Exact finite Gaussian normalization transports the result to
the slice process and its independently proved variational value. -/
@[expose] public section
namespace TensorPCA.PureSliceGroundLimitProofs
noncomputable section
open Filter
open scoped Topology

/-- The actual pure-null mean converges to its reviewed scalar ground value. -/
theorem expectedMaximum_zero_tendsto (k : ℕ) (hk : 3 ≤ k) :
    Tendsto (fun n : ℕ => Model.expectedMaximum (n+1) k 0) atTop (𝓝 (Scalar.gs k)) :=
  MaximumFromPureUpperProofs.expectedMaximum_zero_tendsto_of_pure_upper
    BayesianValueProofs.bayesianValueConvergence
    PureMaximumUpperProofs.eventually_expectedMaximum_zero_upper k hk

/-- Genuine zero-overlap physical ground-state identification, for every
natural k>=3, with no ground-state or matrix-asymptotic proof parameter. -/
theorem sliceGroundLimit_zero (k : ℕ) (hk : 3 ≤ k) : GroundState.SliceGroundLimit k 0 := by
  unfold GroundState.SliceGroundLimit
  rw [PureVariationalProofs.pure_variationalValue_xiSlice_zero k hk]
  apply (expectedMaximum_zero_tendsto k hk).congr'
  exact Eventually.of_forall (fun n =>
    PureMaximumBridgeProofs.expectedMaximum_zero_eq_expectedSliceGround (k := k) (Nat.succ_pos n))

end
end TensorPCA.PureSliceGroundLimitProofs
