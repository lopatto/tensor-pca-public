-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.TensorOrbitAggregationProofs
public import TensorPCA.GaussianRSNormalizationProofs
public import TensorPCA.CheckedReduction

/-!
# Transfer of the product-prior value limit

This file is a conditional reduction from the explicit nonlinear unordered
Gaussian product-prior RS limit, taken as a proof parameter. Every radial,
ordered-index, k-factorial and scalar normalization step after that input is
proved. No principal theorem is exported here.
-/
@[expose] public section

namespace TensorPCA.BayesianValueTransferProofs

open Filter Set SphericalGaussianTransferProofs OrderedTensorComparisonProofs
  TensorOrbitAggregationProofs GaussianRSNormalizationProofs
open scoped Topology

theorem spherical_value_of_productPrior_limit (k : ℕ) (hk : 3 ≤ k) {gamma : ℝ} (hgamma : 0 < gamma)
    (hRS : Tendsto (fun n : ℕ ↦ unorderedPriorFreeEnergy (n+1) k gamma) atTop
      (𝓝 (sSup (gaussianRSPotential k gamma '' Ici (0 : ℝ))))) :
    Tendsto (fun n : ℕ ↦ Statistical.sphericalBayesFreeEnergy (n+1) k gamma) atTop
      (𝓝 (Statistical.bayesianLimit k gamma)) := by
  rw [sSup_gaussianRSPotential_eq_bayesianLimit k hk hgamma] at hRS
  have hOrdered := full_sub_distinct_tendsto k (by omega : 0 < k) hgamma.le
  have hFullDiff : Tendsto (fun n : ℕ ↦ gaussianPriorFreeEnergy (n+1) k gamma-
      unorderedPriorFreeEnergy (n+1) k gamma) atTop (𝓝 0) := by
    convert hOrdered using 1
    funext n
    rw [distinct_freeEnergy_eq_unordered (Nat.succ_pos n) gamma]
  have hFull := hFullDiff.add hRS
  simp only [sub_add_cancel, zero_add] at hFull
  have hSphere := hFull.sub (gaussianPriorFreeEnergy_sub_spherical_tendsto k hgamma.le)
  simpa only [sub_sub_cancel, sub_zero] using hSphere

theorem bayesianValueConvergence_of_productPrior_limit (k : ℕ) (hk : 3 ≤ k)
    (hRS : ∀ gamma : ℝ, 0 < gamma →
      Tendsto (fun n : ℕ ↦ unorderedPriorFreeEnergy (n+1) k gamma) atTop
        (𝓝 (sSup (gaussianRSPotential k gamma '' Ici (0 : ℝ))))) :
    CheckedReduction.BayesianValueConvergence k := by
  intro gamma hgamma
  exact spherical_value_of_productPrior_limit k hk hgamma (hRS gamma hgamma)


end TensorPCA.BayesianValueTransferProofs
