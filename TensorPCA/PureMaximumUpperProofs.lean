-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.PureGroundUpperFromDeterminantProofs
public import TensorPCA.RetainedCountProofs.GOEFirstMeanTheorems

/-! The pure-null maximum upper bound. The ordinary matrix determinant
estimate, finite Kac--Rice identity, maximum witness and Gaussian
concentration are all proved prerequisites; no physical limit is assumed. -/
@[expose] public section
namespace TensorPCA.PureMaximumUpperProofs
noncomputable section
open Filter
open RetainedCountProofs GOEPhysicalPotential
open scoped Topology

/-- The genuine one-sided pure-null expectation input, for every k>=3. -/
theorem eventually_expectedMaximum_zero_upper (k : ℕ) (hk : 3 ≤ k)
    (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop, Model.expectedMaximum (n+1) k 0 ≤ Scalar.gs k+eps := by
  have hkreal : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hb : 0 < (k : ℝ)*((k : ℝ)-1) := mul_pos (by linarith) (by linarith)
  apply PureGroundUpperFromDeterminantProofs.eventually_expectedMaximum_zero_upper_of_detMean_upper
    k hk ((1+|Real.log ((k : ℝ)*((k : ℝ)-1))|)/2) _ eps heps
  intro Z hZ eta heta
  simpa only [Nat.add_assoc,show 1+1=2 from rfl,Nat.cast_one,one_mul] using
    GOEFirstMeanTheorems.physical_mean_leading_upper_uniform 1 hb hZ heta

end
end TensorPCA.PureMaximumUpperProofs
