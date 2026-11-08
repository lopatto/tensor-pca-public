-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.RetainedCountProofs.GOEExpectedTraceProofs
public import TensorPCA.RetainedCountProofs.GOEFirstMeanUpperProofs
public import TensorPCA.RetainedCountProofs.GOEPhysicalFirstMeanUpperProofs
/-! Ordinary GOE first-mean bounds and their spectral estimates. -/
@[expose] public section
namespace TensorPCA.RetainedCountProofs.GOEFirstMeanTheorems
noncomputable section
open MeasureTheory Set Filter
open GOEPhysicalPotential SemicirclePotential SemicircleClipping GOEFirstMeanUpperProofs
open scoped Topology

theorem standard_mean_upper_uniform {S : Set ℝ} (hS : IsCompact S) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop, ∀ k ∈ S,
      physicalMean n (n+1) 1 k ≤ Real.exp (((n+1 : ℕ) : ℝ)*(potential k+eps)) := by
  apply standard_mean_upper_uniform_of_clippedTrace_tendsto _ hS heps
  intro k rho hrho
  simpa only [normalizedExpectedClippedTrace, clippedPotential, Nat.cast_add, Nat.cast_one] using
    GOEExpectedTraceProofs.normalized_expected_clippedTrace_tendsto k hrho

theorem physical_mean_leading_upper_uniform (j : ℕ) {b Z eps : ℝ}
    (hb : 0 < b) (hZ : 0 ≤ Z) (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℝ, |k| ≤ Z →
      physicalMean n (n+1+j) b k ≤ Real.exp
        (((n+1+j : ℕ) : ℝ)*(Real.log b/2+potential (k/Real.sqrt b)+eps)+
          (j : ℝ)*(1+|Real.log b|)/2) :=
  GOEPhysicalFirstMeanUpperProofs.physical_mean_leading_upper_uniform_of_standard
    standard_mean_upper_uniform j hb hZ heps

end
end TensorPCA.RetainedCountProofs.GOEFirstMeanTheorems
